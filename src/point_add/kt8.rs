//! KT8 start machine (KT7 step 3, WIDE machine experiment): x untouched, both Euclid values implicit, quotients from
//! short window products of x with the two cofactors. Spec and register-level reference: notes v3/KT8.md,
//! v3/g2/kt8_ref.py (the constants below must match it). Gates are X / CX / CCX only, everything garbage-free.
use super::*;
use std::collections::BTreeMap;

pub(super) const CAP: usize = 10; // quotient bits of a common slot
pub(super) const GUARD: usize = 12;
pub(super) const ACCG: usize = 8; // accumulator guard lanes
pub(super) const ECAP8: usize = 27; // quotient bits of a tier block
pub(super) const TIER: i32 = 16;
pub(super) const ENV: usize = 27; // public envelope: no cofactor is longer than m + ENV at a slot of length m
pub(super) const WT: usize = 72; // lanes of each cofactor register
pub(super) const WU_C: usize = 2 * CAP + GUARD + 4;
pub(super) const WA_C: usize = WU_C + ACCG;
pub(super) const TAU_HI: i32 = 512;
pub(super) const TAU_LO: i32 = 448;
pub(super) const NX: usize = 255; // lanes of x (bit 255 is the PAR lane, the value is below 2^255)

pub(super) fn m_of(tau: i32) -> usize {
    (257 - (tau + 1) / 2) as usize
}

/// Gate list builder with a pool of clean scratch lanes (stack discipline is not required; every lane given back
/// must be clean).
pub(super) struct Kt {
    pub(super) g: GL,
    pub(super) base: u32,
    pub(super) nalloc: u32,
    free: Vec<u32>,
    live: usize,
    pub(super) hw: usize,
    pub(super) marks: Vec<(String, usize, usize)>,
}

impl Kt {
    pub(super) fn new(base: u32) -> Kt {
        Kt { g: Vec::new(), base, nalloc: 0, free: Vec::new(), live: 0, hw: 0, marks: Vec::new() }
    }
    pub(super) fn take1(&mut self) -> u32 {
        self.live += 1;
        if self.live > self.hw {
            self.hw = self.live;
        }
        if let Some(q0) = self.free.pop() {
            q0
        } else {
            self.nalloc += 1;
            self.base + self.nalloc - 1
        }
    }
    pub(super) fn take(&mut self, n: usize) -> Vec<u32> {
        (0..n).map(|_| self.take1()).collect()
    }
    pub(super) fn give(&mut self, v: &[u32]) {
        for &q0 in v.iter().rev() {
            self.free.push(q0);
        }
        self.live -= v.len();
    }
    pub(super) fn mark(&mut self, name: &str) {
        self.marks.push((name.to_string(), self.g.len(), self.live));
    }
    /// append the inverse of g[s..e]
    pub(super) fn undo(&mut self, s: usize, e: usize) {
        let seg: Vec<G> = self.g[s..e].iter().rev().cloned().collect();
        self.g.extend(seg);
    }
    fn maj(&mut self, c: u32, b: u32, a: u32) {
        self.g.push(gc(a, b));
        self.g.push(gc(a, c));
        self.g.push(gt(c, b, a));
    }
    fn uma(&mut self, ctrl: Option<u32>, c: u32, b: u32, a: u32) {
        self.g.push(gt(c, b, a));
        match ctrl {
            None => {
                self.g.push(gc(a, c));
                self.g.push(gc(c, b));
            }
            Some(k) => {
                self.g.push(gt(k, c, b));
                self.g.push(gc(a, c));
                self.g.push(gc(a, b));
            }
        }
    }
    /// b += ctrl * a (mod 2^len(b)); a.len() <= b.len(), a zero-extended. One clean carry lane for the low part
    /// (2 CCX per lane, 3 controlled), an AND chain on clean lanes for the lanes above a (2 per lane).
    pub(super) fn add(&mut self, ctrl: Option<u32>, a: &[u32], b: &[u32]) {
        let (n, nb) = (a.len(), b.len());
        assert!(n <= nb);
        if n == 0 {
            return;
        }
        let c0 = self.take1();
        let full = if nb == n { n - 1 } else { n };
        for i in 0..full {
            let c = if i == 0 { c0 } else { a[i - 1] };
            self.maj(c, b[i], a[i]);
        }
        if nb == n {
            let i = n - 1;
            let c = if i == 0 { c0 } else { a[i - 1] };
            match ctrl {
                None => {
                    self.g.push(gc(a[i], b[i]));
                    self.g.push(gc(c, b[i]));
                }
                Some(k) => {
                    self.g.push(gt(k, a[i], b[i]));
                    self.g.push(gt(k, c, b[i]));
                }
            }
        } else {
            let kn = a[n - 1];
            let mut chain: Vec<u32> = Vec::with_capacity(nb - n);
            let kc = match ctrl {
                None => {
                    chain.push(kn);
                    None
                }
                Some(k) => {
                    let t = self.take1();
                    self.g.push(gt(k, kn, t));
                    chain.push(t);
                    Some((k, t))
                }
            };
            for j in n..nb - 1 {
                let t = self.take1();
                self.g.push(gt(chain[j - n], b[j], t));
                chain.push(t);
            }
            for j in (n..nb).rev() {
                self.g.push(gc(chain[j - n], b[j]));
                if j > n {
                    self.g.push(gt(chain[j - n - 1], b[j - 1], chain[j - n]));
                }
            }
            let tail: Vec<u32> = chain[1..].to_vec();
            self.give(&tail);
            if let Some((k, t)) = kc {
                self.g.push(gt(k, kn, t));
                self.give(&[t]);
            }
        }
        for i in (0..full).rev() {
            let c = if i == 0 { c0 } else { a[i - 1] };
            self.uma(ctrl, c, b[i], a[i]);
        }
        self.give(&[c0]);
    }
    /// b -= ctrl * a
    pub(super) fn sub(&mut self, ctrl: Option<u32>, a: &[u32], b: &[u32]) {
        let s = self.g.len();
        self.add(ctrl, a, b);
        self.g[s..].reverse();
    }
    /// restoring row: dig (clean) <- [r >= d], r -= dig * d. d.len() <= r.len(), d zero-extended. 3 CCX per lane.
    pub(super) fn rrow(&mut self, r: &[u32], d: &[u32], dig: u32) {
        let (n, nr) = (d.len(), r.len());
        assert!(n >= 1 && n <= nr);
        for &q0 in r {
            self.g.push(gx(q0));
        }
        let c0 = self.take1();
        for i in 0..n {
            let c = if i == 0 { c0 } else { d[i - 1] };
            self.maj(c, r[i], d[i]);
        }
        let mut chain = vec![d[n - 1]];
        for j in n..nr {
            let t = self.take1();
            self.g.push(gt(chain[j - n], r[j], t));
            chain.push(t);
        }
        let top = chain[nr - n];
        self.g.push(gc(top, dig));
        self.g.push(gx(dig));
        for j in (n..nr).rev() {
            self.g.push(gt(chain[j - n], r[j], chain[j - n + 1]));
            self.g.push(gt(dig, chain[j - n], r[j]));
        }
        let tail: Vec<u32> = chain[1..].to_vec();
        self.give(&tail);
        for i in (0..n).rev() {
            let c = if i == 0 { c0 } else { d[i - 1] };
            self.uma(Some(dig), c, r[i], d[i]);
        }
        self.give(&[c0]);
        for &q0 in r {
            self.g.push(gx(q0));
        }
    }
    /// tgt ^= AND of the literals (distinct lanes, tgt not among them). Ladder on clean lanes: 2k - 3 CCX.
    pub(super) fn and_into(&mut self, lits: &[Lit], tgt: u32) {
        let neg: Vec<u32> = lits.iter().filter(|l| !l.1).map(|l| l.0).collect();
        for &q0 in &neg {
            self.g.push(gx(q0));
        }
        let k = lits.len();
        match k {
            0 => self.g.push(gx(tgt)),
            1 => self.g.push(gc(lits[0].0, tgt)),
            2 => self.g.push(gt(lits[0].0, lits[1].0, tgt)),
            _ => {
                let t = self.take(k - 2);
                let s = self.g.len();
                self.g.push(gt(lits[0].0, lits[1].0, t[0]));
                for i in 2..k - 1 {
                    self.g.push(gt(t[i - 2], lits[i].0, t[i - 1]));
                }
                let e = self.g.len();
                self.g.push(gt(t[k - 3], lits[k - 1].0, tgt));
                self.undo(s, e);
                self.give(&t);
            }
        }
        for &q0 in &neg {
            self.g.push(gx(q0));
        }
    }
    pub(super) fn cswap_reg(&mut self, c: u32, a: &[u32], b: &[u32]) {
        for i in 0..a.len() {
            cswap(c, a[i], b[i], &mut self.g);
        }
    }
}

/// The start machine: registers and slots.
pub(super) struct K8 {
    pub(super) kt: Kt,
    pub(super) x: Vec<u32>,  // NX lanes
    pub(super) ta: Vec<u32>, // WT lanes
    pub(super) tb: Vec<u32>,
    pub(super) sp: u32,      // steps parity
    pub(super) f: u32,       // act flag (clean between slots)
    pub(super) qc: Vec<u32>, // quotient copy (clean between slots)
}

impl K8 {
    pub(super) fn new(base: u32, xl: &[u32]) -> K8 {
        let mut kt = Kt::new(base);
        let ta = kt.take(WT);
        let tb = kt.take(WT);
        let sp = kt.take1();
        let f = kt.take1();
        let qc = kt.take(ECAP8);
        let mut k = K8 { kt, x: xl[..NX].to_vec(), ta, tb, sp, f, qc };
        k.kt.g.push(gx(k.tb[0])); // tB = 1
        k
    }
    /// accumulate the window products: acc_b += sum over set bits i of tb of (x >> (lo0 - i)), same for ta.
    fn products(&mut self, nrows: usize, lo0: usize, acc_a: &[u32], acc_b: &[u32]) {
        let wa = acc_a.len();
        for i in 0..nrows {
            let lo = lo0 - i;
            let win: Vec<u32> = (lo..lo + wa).filter(|&b| b < NX).map(|b| self.x[b]).collect();
            self.kt.add(Some(self.tb[i]), &win, acc_b);
            self.kt.add(Some(self.ta[i]), &win, acc_a);
        }
    }
    /// One common slot (quotients up to CAP bits).
    pub(super) fn common_slot(&mut self, tau: i32) {
        let m = m_of(tau);
        let odd = tau & 1 == 1;
        let (ta, tb, sp, f) = (self.ta.clone(), self.tb.clone(), self.sp, self.f);
        let qc = self.qc.clone();
        self.kt.mark(&format!("c{tau} U"));
        let acc_a = self.kt.take(WA_C);
        let acc_b = self.kt.take(WA_C);
        let dig = self.kt.take(CAP + 1);
        let pad = self.kt.take(CAP);
        let z = self.kt.take1();
        let start = self.kt.g.len();
        self.products(m, 213 - m, &acc_a, &acc_b);
        let ua: Vec<u32> = acc_a[ACCG..].to_vec();
        let ub: Vec<u32> = acc_b[ACCG..].to_vec();
        for &l in &ub {
            self.kt.g.push(gc(sp, l));
        }
        for &l in &ua {
            self.kt.g.push(gx(l));
            self.kt.g.push(gc(sp, l));
        }
        let mid0 = self.kt.g.len();
        for i in (0..=CAP).rev() {
            let mut r: Vec<u32> = ua[i..].to_vec();
            r.extend_from_slice(&pad[..i]);
            self.kt.rrow(&r, &ub, dig[i]);
        }
        // stop rule: bl(B) from the leading zeros of U_B
        let thr = 2 * m as i32 - 31;
        let mut lits: Vec<Lit> = vec![(tb[m - 1], true), (ta[m - 1], odd), (dig[CAP], false)];
        for j in m..m + ENV {
            lits.push((tb[j], false));
        }
        if thr > 0 {
            let zl: Vec<Lit> = (thr as usize..WU_C).map(|j| (ub[j], false)).collect();
            self.kt.and_into(&zl, z);
            lits.push((z, false));
        }
        let mid = self.kt.g.len();
        self.kt.and_into(&lits, f);
        for j in 0..CAP {
            self.kt.g.push(gt(f, dig[j], qc[j]));
        }
        let m2 = self.kt.g.len();
        self.kt.undo(start, mid);
        // re-tag the two halves for the census: [start, mid0) and its mirror are products, [mid0, mid) rows
        self.kt.marks.push((format!("c{tau} Q"), mid0, 0));
        self.kt.marks.push((format!("c{tau} F"), mid, 0));
        self.kt.marks.push((format!("c{tau} Q"), m2, 0));
        self.kt.marks.push((format!("c{tau} U"), m2 + (mid - mid0), 0));
        self.kt.give(&[z]);
        self.kt.give(&pad);
        self.kt.give(&dig);
        self.kt.give(&acc_b);
        self.kt.give(&acc_a);
        // cofactor rows, role swap, parity
        self.kt.mark(&format!("c{tau} C"));
        for j in 0..CAP {
            self.kt.add(Some(qc[j]), &tb[..m], &ta[j..m + CAP]);
        }
        self.kt.cswap_reg(f, &ta[..m + CAP], &tb[..m + CAP]);
        self.kt.g.push(gc(f, sp));
        // erase the quotient copy and the act flag from the post-state
        self.kt.mark(&format!("c{tau} E"));
        let dig2 = self.kt.take(CAP + 1);
        let fp = self.kt.take1();
        let s2 = self.kt.g.len();
        for i in (0..=CAP).rev() {
            self.kt.rrow(&tb[i..i + m + 1], &ta[..m], dig2[i]);
        }
        let mut l2: Vec<Lit> = vec![(ta[m - 1], true), (tb[m - 1], odd), (dig2[CAP], false)];
        for j in m..m + ENV {
            l2.push((ta[j], false));
        }
        for j in m + CAP + 1..m + ENV {
            l2.push((tb[j], false));
        }
        self.kt.and_into(&l2, fp);
        let e2 = self.kt.g.len();
        self.kt.g.push(gc(fp, f));
        for j in 0..CAP {
            self.kt.g.push(gt(fp, dig2[j], qc[j]));
        }
        self.kt.undo(s2, e2);
        self.kt.give(&[fp]);
        self.kt.give(&dig2);
        self.kt.mark("end");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// test harness (generated crate, g2tools/kt8.sh): bit-parallel simulation of the gate lists on 64 shots per batch
// ---------------------------------------------------------------------------------------------------------------
pub(super) fn sim(gates: &[G], lane: &mut [u64], macs: &[Mac]) {
    for &g in gates {
        if g.0 == MAC {
            let m = &macs[g.1 as usize];
            let mut v = u64::MAX;
            for &(q0, pol) in &m.lits {
                v &= if pol { lane[q0 as usize] } else { !lane[q0 as usize] };
            }
            lane[m.tgt as usize] ^= v;
        } else if g.2 != NONE {
            lane[g.2 as usize] ^= lane[g.0 as usize] & lane[g.1 as usize];
        } else if g.1 != NONE {
            lane[g.1 as usize] ^= lane[g.0 as usize];
        } else {
            lane[g.0 as usize] ^= u64::MAX;
        }
    }
}
pub(super) fn ccx_count(g: &[G]) -> usize {
    g.iter().filter(|x| x.0 != MAC && x.2 != NONE).count()
}
fn env_u64(name: &str, d: u64) -> u64 {
    std::env::var(name).ok().and_then(|v| v.trim().parse().ok()).unwrap_or(d)
}
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}
fn load(lane: &mut [u64], reg: &[u32], vals: &[u128; 64]) {
    for (i, &q0) in reg.iter().enumerate() {
        let mut w = 0u64;
        for s in 0..64 {
            if (vals[s] >> i) & 1 == 1 {
                w |= 1u64 << s;
            }
        }
        lane[q0 as usize] = w;
    }
}
fn read(lane: &[u64], reg: &[u32], s: usize) -> u128 {
    let mut v = 0u128;
    for (i, &q0) in reg.iter().enumerate() {
        if (lane[q0 as usize] >> s) & 1 == 1 {
            v |= 1u128 << i;
        }
    }
    v
}
fn mask(n: usize) -> u128 {
    if n >= 128 { u128::MAX } else { (1u128 << n) - 1 }
}

/// self-checking test of the primitives against u128 arithmetic
pub fn kt8_prims() {
    let mut rng = Rng(env_u64("KT8_SEED", 7).wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let (mut nt, mut bad) = (0usize, 0usize);
    for case in 0..400usize {
        let nb = 1 + (rng.next() % 100) as usize;
        let n = 1 + (rng.next() % nb as u64) as usize;
        let kind = case % 6;
        // lanes: a = 0..n, b = 200..200+nb, ctrl 400, dig 401, pool from 500
        let a: Vec<u32> = (0..n as u32).collect();
        let b: Vec<u32> = (200..200 + nb as u32).collect();
        let (ctrl, dig) = (400u32, 401u32);
        let mut kt = Kt::new(500);
        let mut lits: Vec<Lit> = vec![];
        match kind {
            0 => kt.add(None, &a, &b),
            1 => kt.add(Some(ctrl), &a, &b),
            2 => kt.sub(None, &a, &b),
            3 => kt.sub(Some(ctrl), &a, &b),
            4 => kt.rrow(&b, &a, dig),
            _ => {
                let k = (rng.next() % 9) as usize;
                for i in 0..k.min(n) {
                    lits.push((a[i], rng.next() & 1 == 1));
                }
                kt.and_into(&lits, dig);
            }
        }
        let mut lane = vec![0u64; 500 + kt.nalloc as usize + 1];
        let mut va = [0u128; 64];
        let mut vb = [0u128; 64];
        for s in 0..64 {
            va[s] = ((rng.next() as u128) << 64 | rng.next() as u128) & mask(n);
            vb[s] = ((rng.next() as u128) << 64 | rng.next() as u128) & mask(nb);
            if s % 5 == 0 {
                vb[s] = va[s] & mask(nb);
            }
            if s % 7 == 0 {
                va[s] = mask(n);
            }
        }
        load(&mut lane, &a, &va);
        load(&mut lane, &b, &vb);
        lane[ctrl as usize] = rng.next();
        let c0 = lane[ctrl as usize];
        sim(&kt.g, &mut lane, &[]);
        for s in 0..64 {
            let (ra, rb) = (read(&lane, &a, s), read(&lane, &b, s));
            let c = ((c0 >> s) & 1) as u128;
            let d = ((lane[dig as usize] >> s) & 1) as u128;
            let (ea, eb, ed) = match kind {
                0 => (va[s], (vb[s] + va[s]) & mask(nb), 0),
                1 => (va[s], (vb[s] + c * va[s]) & mask(nb), 0),
                2 => (va[s], vb[s].wrapping_sub(va[s]) & mask(nb), 0),
                3 => (va[s], vb[s].wrapping_sub(c * va[s]) & mask(nb), 0),
                4 => {
                    let ge = (vb[s] >= va[s]) as u128;
                    (va[s], vb[s] - ge * va[s], ge)
                }
                _ => {
                    let mut v = 1u128;
                    for &(q0, pol) in &lits {
                        let bit = (va[s] >> q0) & 1;
                        v &= if pol { bit } else { 1 - bit };
                    }
                    (va[s], vb[s], v)
                }
            };
            nt += 1;
            let pool_clean = (500..lane.len()).all(|i| (lane[i] >> s) & 1 == 0);
            if ra != ea || rb != eb || d != ed || !pool_clean || ((lane[ctrl as usize] >> s) & 1) as u128 != c {
                bad += 1;
                if bad <= 5 {
                    println!("BAD case {case} kind {kind} n {n} nb {nb} shot {s}: a {ra:x}/{ea:x} b {rb:x}/{eb:x} dig {d}/{ed} pool {pool_clean}");
                }
            }
        }
        if case < 6 {
            println!("kind {kind} n {n} nb {nb}: {} CCX, scratch peak {}", ccx_count(&kt.g), kt.hw);
        }
    }
    println!("kt8_prims: {nt} checks, {bad} bad");
}

/// lanes of the frame machine exactly as f_circuit builds them
pub(super) fn mk_machine() -> Machine {
    let mut b = B { free: vec![], next: 512, gates: Vec::with_capacity(1 << 20) };
    for _ in 0..ZB {
        b.alloc();
    }
    let xl: Vec<u32> = (0..256).collect();
    let pas: Vec<u32> = (256..512).collect();
    let y0 = b.alloc();
    let par = xl[N - 1];
    let y1 = b.alloc();
    let mut y = vec![y0, y1];
    y.extend_from_slice(&xl[..N - 1]);
    let x: Vec<u32> = (0..W).map(|_| b.alloc()).collect();
    let e: Vec<u32> = (0..EB).map(|_| b.alloc()).collect();
    let mut dirty = pas.clone();
    dirty.extend_from_slice(&x);
    dirty.extend_from_slice(&y);
    Machine { b, dirty, pas, x, y, e, par, pg: vec![], wr: W, freed: vec![], w4: NONE, w1: NONE, cv_t2: vec![], cv_freed: vec![], cv_x16: vec![], cv_y16: vec![], cv_pg16: vec![] }
}
/// the reflection of init (x >= 2^255 -> p - x, PAR lane keeps the bit), without the ring X preset
pub(super) fn reflect(mc: &Machine) -> GL {
    let mut g: GL = vec![];
    let xl: Vec<u32> = mc.y[2..].to_vec();
    for &q0 in &xl {
        g.push(gc(mc.par, q0));
    }
    let cl = mc.e[0];
    for &i in &C0M1 {
        g.extend(rev(&inc_long(&xl[i..], mc.par, &mc.dirty, cl)));
    }
    g
}

/// trace of the start region: registers after every slot for 64 shots per batch (checked by v3/g2/kt8_check.py)
pub fn kt8_trace() {
    let mc = mk_machine();
    let xl: Vec<u32> = (0..256).collect();
    let mut k8 = K8::new(mc.b.next, &xl);
    let g0 = reflect(&mc);
    let mut snaps: Vec<(i32, i32, usize)> = vec![];
    let tier_on = env_u64("KT8_TIER", 0) == 1;
    let _ = tier_on;
    for tau in (TAU_LO..=TAU_HI).rev() {
        k8.common_slot(tau);
        snaps.push((tau, 0, k8.kt.g.len()));
    }
    let nl = (k8.kt.base + k8.kt.nalloc) as usize;
    eprintln!("kt8_trace: {} gates, {} CCX, {} lanes, scratch peak {} (persistent {})", k8.kt.g.len(), ccx_count(&k8.kt.g), nl, k8.kt.hw, 2 * WT + 2 + ECAP8);
    census(&k8.kt);
    let nb = env_u64("KT8_NB", 1);
    let mut rng = Rng(env_u64("KT8_SEED", 1).wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut keep: Vec<u32> = k8.ta.clone();
    keep.extend_from_slice(&k8.tb);
    keep.push(k8.sp);
    for batch in 0..nb {
        let mut lane = vec![0u64; nl];
        for s in 0..64usize {
            let limbs = [rng.next(), rng.next(), rng.next(), rng.next()];
            for i in 0..256usize {
                if (limbs[i / 64] >> (i % 64)) & 1 == 1 {
                    lane[i] |= 1u64 << s;
                }
            }
            println!("IN {} {} {:016x}{:016x}{:016x}{:016x}", batch, s, limbs[3], limbs[2], limbs[1], limbs[0]);
        }
        for i in 256..512usize {
            lane[i] = rng.next();
        }
        sim(&g0, &mut lane, &[]);
        let mut gi = 0usize;
        for &(tau, tier, idx) in &snaps {
            sim(&k8.kt.g[gi..idx], &mut lane, &[]);
            gi = idx;
            let mut dirty = 0u64;
            for v in k8.kt.base..k8.kt.base + k8.kt.nalloc {
                if !keep.contains(&v) {
                    dirty |= lane[v as usize];
                }
            }
            for s in 0..64usize {
                println!("K {} {} {} {} {:x} {:x} {} {}", batch, tau, tier, s, read(&lane, &k8.ta, s), read(&lane, &k8.tb, s), (lane[k8.sp as usize] >> s) & 1, (dirty >> s) & 1);
            }
        }
    }
}

/// CCX per stage label (the label is the text after the first space of a mark; "end" closes a stage)
pub(super) fn census(kt: &Kt) {
    let mut marks = kt.marks.clone();
    marks.sort_by_key(|m| m.1);
    let mut tot: BTreeMap<String, usize> = BTreeMap::new();
    let mut per: BTreeMap<String, usize> = BTreeMap::new();
    for (i, m) in marks.iter().enumerate() {
        let e = if i + 1 < marks.len() { marks[i + 1].1 } else { kt.g.len() };
        let n = ccx_count(&kt.g[m.1..e]);
        if m.0 == "end" {
            continue;
        }
        let stage = m.0.split(' ').nth(1).unwrap_or("?").to_string();
        *tot.entry(stage).or_insert(0) += n;
        *per.entry(m.0.split(' ').next().unwrap().to_string()).or_insert(0) += n;
    }
    let all: usize = tot.values().sum();
    println!("CENSUS total CCX {} (gate list {})", all, ccx_count(&kt.g));
    for (k, v) in &tot {
        println!("CENSUS stage {} {}", k, v);
    }
    for (k, v) in &per {
        println!("CENSUS unit {} {}", k, v);
    }
}
