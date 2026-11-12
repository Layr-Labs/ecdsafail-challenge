// Bit-sliced replay of a trace (64 shots per word), mirroring the official simulator's semantics.
use crate::common::*;

pub const F_EXEC: u8 = 1;   // executed in some shot
pub const F_COND0: u8 = 2;  // skipped by a classical condition in some shot
pub const F_FIRE: u8 = 4;   // both controls 1 in some executed shot
pub const F_TPRE: u8 = 8;   // target 1 before the gate in some executed shot
pub const F_TPOST: u8 = 16; // target 1 after the gate in some executed shot
pub const F_A0: u8 = 32;    // first control 0 in some executed shot
pub const F_B0: u8 = 64;    // second control 0 in some executed shot

pub struct Shots { pub n: usize, pub data: Vec<u8> } // per shot: tx,ty,ox,oy,ex,ey (32 bytes LE each)

pub fn load_shots(path: &str) -> Shots {
    let data = std::fs::read(path).expect("inputs");
    assert!(data.len() % 192 == 0);
    Shots { n: data.len() / 192, data }
}

impl Shots {
    #[inline] pub fn bit(&self, shot: usize, field: usize, i: usize) -> bool {
        (self.data[shot * 192 + field * 32 + i / 8] >> (i % 8)) & 1 != 0
    }
}

pub struct Sim { pub q: Vec<u64>, pub b: Vec<u64>, pub phase: u64, rng: u64, pub tof: u64, pub hmr: u64 }

pub struct Rec<'a> { pub flags: &'a mut [u8], pub exec: &'a mut [u16], pub first: &'a mut [u16], pub local_batch: usize }

impl Sim {
    pub fn new(nq: usize, nb: usize, seed: u64) -> Self {
        Sim { q: vec![0; nq + 1], b: vec![0; nb + 1], phase: 0, rng: seed | 1, tof: 0, hmr: 0 }
    }
    #[inline(always)] fn next(&mut self) -> u64 {
        // splitmix64
        self.rng = self.rng.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.rng;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    pub fn load(&mut self, lay: &Layout, shots: &Shots, batch: usize) {
        for x in self.q.iter_mut() { *x = 0; }
        for x in self.b.iter_mut() { *x = 0; }
        self.phase = 0;
        for s in 0..64 {
            let shot = batch * 64 + s;
            for r in 0..4 {
                for (i, &(is_bit, id)) in lay.regs[r].iter().enumerate() {
                    if shots.bit(shot, r, i) { if is_bit { self.b[id] |= 1 << s; } else { self.q[id] |= 1 << s; } }
                }
            }
        }
    }
    /// Returns a description of the first failure, or None if all 64 shots are right.
    pub fn check(&self, lay: &Layout, shots: &Shots, batch: usize) -> Option<String> {
        if self.phase != 0 { return Some(format!("batch {} phase {:#x}", batch, self.phase)); }
        let mut isreg = vec![false; self.q.len()];
        for r in 0..2 {
            for (i, &(_, id)) in lay.regs[r].iter().enumerate() {
                isreg[id] = true;
                let mut want = 0u64;
                for s in 0..64 { if shots.bit(batch * 64 + s, 4 + r, i) { want |= 1 << s; } }
                if self.q[id] != want { return Some(format!("batch {} reg {} bit {} mismatch {:#x}", batch, r, i, self.q[id] ^ want)); }
            }
        }
        for (i, &v) in self.q.iter().enumerate() {
            if !isreg[i] && v != 0 { return Some(format!("batch {} ancilla {} dirty {:#x}", batch, i, v)); }
        }
        None
    }
    /// Mask of shots that fail any check (phase, outputs, dirty ancilla).
    pub fn fail_mask(&self, lay: &Layout, shots: &Shots, batch: usize) -> u64 {
        let mut bad = self.phase;
        let mut isreg = vec![false; self.q.len()];
        for r in 0..2 {
            for (i, &(_, id)) in lay.regs[r].iter().enumerate() {
                isreg[id] = true;
                let mut want = 0u64;
                for s in 0..64 { if shots.bit(batch * 64 + s, 4 + r, i) { want |= 1 << s; } }
                bad |= self.q[id] ^ want;
            }
        }
        for (i, &v) in self.q.iter().enumerate() { if !isreg[i] { bad |= v; } }
        bad
    }
    pub fn run(&mut self, t: &[u64], mut rec: Option<Rec>) {
        let mut base = !0u64;
        let mut stack: Vec<u64> = Vec::with_capacity(16);
        let mut j = 0usize; // CCX ordinal
        for &r in t {
            let k = kind(r);
            if k == K_CCX {
                let (a, b, c) = (fa(r), fb(r), fc(r));
                let (va, vb, t0) = (self.q[a], self.q[b], self.q[c]);
                let v = base & va & vb;
                self.q[c] = t0 ^ v;
                let ex = base.count_ones();
                self.tof += ex as u64;
                if let Some(rc) = rec.as_mut() {
                    let mut f = 0u8;
                    if base != 0 { f |= F_EXEC; }
                    if base != !0 { f |= F_COND0; }
                    if v != 0 { f |= F_FIRE; }
                    if base & t0 != 0 { f |= F_TPRE; }
                    if base & (t0 ^ v) != 0 { f |= F_TPOST; }
                    if base & !va != 0 { f |= F_A0; }
                    if base & !vb != 0 { f |= F_B0; }
                    rc.flags[j] |= f;
                    rc.exec[j] += ex as u16;
                    if v != 0 && rc.first[j] == 0xFFFF { rc.first[j] = (rc.local_batch * 64 + v.trailing_zeros() as usize) as u16; }
                }
                j += 1;
                continue;
            }
            let (a, b, c) = (fa(r), fb(r), fc(r));
            match k {
                K_CX => { let cond = if c == NONE { base } else { base & self.b[c] }; self.q[b] ^= cond & self.q[a]; }
                K_CZ => { let cond = if c == NONE { base } else { base & self.b[c] }; self.phase ^= cond & self.q[a] & self.q[b]; }
                K_X => { let cond = if b == NONE { base } else { base & self.b[b] }; self.q[a] ^= cond; }
                K_Z => { let cond = if b == NONE { base } else { base & self.b[b] }; self.phase ^= cond & self.q[a]; }
                K_HMR => {
                    let rv = self.next();
                    self.hmr += 1;
                    self.b[b] = (self.b[b] & !base) ^ (rv & base);
                    self.phase ^= self.q[a] & rv & base;
                    self.q[a] &= !base;
                }
                K_BINV => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] ^= cond; }
                K_BST0 => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] &= !cond; }
                K_BST1 => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] |= cond; }
                K_PUSH => { stack.push(base); base &= self.b[a]; }
                K_POP => { if let Some(v) = stack.pop() { base = v; } }
                K_REG | K_APPQ | K_APPB => {}
                _ => panic!("kind {}", k),
            }
        }
    }
    /// Replay with hooks: `f(p, qubits)` is called before the op at index pts[p] executes (pts sorted; index n = after the end).
    pub fn run_hooked(&mut self, t: &[u64], pts: &[u64], mut f: impl FnMut(usize, &[u64])) {
        let mut base = !0u64;
        let mut stack: Vec<u64> = Vec::with_capacity(16);
        let mut p = 0usize;
        for (i, &r) in t.iter().enumerate() {
            while p < pts.len() && pts[p] as usize == i { f(p, &self.q); p += 1; }
            let (k, a, b, c) = (kind(r), fa(r), fb(r), fc(r));
            match k {
                K_CCX => { let v = base & self.q[a] & self.q[b]; self.q[c] ^= v; }
                K_CX => { let cond = if c == NONE { base } else { base & self.b[c] }; self.q[b] ^= cond & self.q[a]; }
                K_CZ => { let cond = if c == NONE { base } else { base & self.b[c] }; self.phase ^= cond & self.q[a] & self.q[b]; }
                K_X => { let cond = if b == NONE { base } else { base & self.b[b] }; self.q[a] ^= cond; }
                K_Z => { let cond = if b == NONE { base } else { base & self.b[b] }; self.phase ^= cond & self.q[a]; }
                K_HMR => {
                    let rv = self.next();
                    self.hmr += 1;
                    self.b[b] = (self.b[b] & !base) ^ (rv & base);
                    self.phase ^= self.q[a] & rv & base;
                    self.q[a] &= !base;
                }
                K_BINV => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] ^= cond; }
                K_BST0 => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] &= !cond; }
                K_BST1 => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] |= cond; }
                K_PUSH => { stack.push(base); base &= self.b[a]; }
                K_POP => { if let Some(v) = stack.pop() { base = v; } }
                K_REG | K_APPQ | K_APPB => {}
                _ => panic!("kind {}", k),
            }
        }
        while p < pts.len() { f(p, &self.q); p += 1; }
    }
    /// Replay calling `f(i, op, qubits)` after every op.
    pub fn run_each(&mut self, t: &[u64], mut f: impl FnMut(usize, u64, &[u64])) {
        let mut base = !0u64;
        let mut stack: Vec<u64> = Vec::with_capacity(16);
        for (i, &r) in t.iter().enumerate() {
            let (k, a, b, c) = (kind(r), fa(r), fb(r), fc(r));
            match k {
                K_CCX => { let v = base & self.q[a] & self.q[b]; self.q[c] ^= v; }
                K_CX => { let cond = if c == NONE { base } else { base & self.b[c] }; self.q[b] ^= cond & self.q[a]; }
                K_CZ => { let cond = if c == NONE { base } else { base & self.b[c] }; self.phase ^= cond & self.q[a] & self.q[b]; }
                K_X => { let cond = if b == NONE { base } else { base & self.b[b] }; self.q[a] ^= cond; }
                K_Z => { let cond = if b == NONE { base } else { base & self.b[b] }; self.phase ^= cond & self.q[a]; }
                K_HMR => {
                    let rv = self.next();
                    self.hmr += 1;
                    self.b[b] = (self.b[b] & !base) ^ (rv & base);
                    self.phase ^= self.q[a] & rv & base;
                    self.q[a] &= !base;
                }
                K_BINV => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] ^= cond; }
                K_BST0 => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] &= !cond; }
                K_BST1 => { let cond = if b == NONE { base } else { base & self.b[b] }; self.b[a] |= cond; }
                K_PUSH => { stack.push(base); base &= self.b[a]; }
                K_POP => { if let Some(v) = stack.pop() { base = v; } }
                K_REG | K_APPQ | K_APPB => {}
                _ => panic!("kind {}", k),
            }
            f(i, r, &self.q);
        }
    }
}
