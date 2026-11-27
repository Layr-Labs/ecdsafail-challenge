//! q631 / rp1 (local research, never submitted): bit-sliced shot simulator shared by the rp* tools.  NOT a module of
//! point_add (included with #[path] by src/bin/rp*.rs only).  Semantics = `step` of src/bin/c1census.rs / q2census.rs:
//! computational-basis values of every lane on NS = 64 * NW valid shots (second point = run-time classical input, fresh per
//! shot), HMR outcomes random per shot, conditions and PUSH scopes exact.  Phases are not simulated.
use alloy_primitives::U256;
use quantum_ecc::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
pub type Row = [u16; 4];
pub const NONE: u16 = u16::MAX;
pub struct Rng(pub u64);
impl Rng { #[inline] pub fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } }
pub fn curve() -> WeierstrassEllipticCurve {
    WeierstrassEllipticCurve {
        modulus: U256::from_str_radix("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", 16).unwrap(),
        a: U256::from(0), b: U256::from(7),
        gx: U256::from_str_radix("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798", 16).unwrap(),
        gy: U256::from_str_radix("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8", 16).unwrap(),
        order: U256::from_str_radix("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16).unwrap(),
    }
}
#[inline] pub fn nqu(k: u16) -> usize { match k { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }
/// lanes a record names (qubit fields + the qubit of a register row), deduplicated; returns the count
#[inline] pub fn named(r: &Row, out: &mut [u16; 4]) -> usize {
    let mut c = 0usize;
    for j in 1..=nqu(r[0]) { let l = r[j]; if !out[..c].contains(&l) { out[c] = l; c += 1; } }
    if r[0] == 2 { let l = r[2]; if !out[..c].contains(&l) { out[c] = l; c += 1; } }
    c }
/// the lane whose VALUE a record may change (CCX / CX / X / HMR target), else NONE
#[inline] pub fn target(r: &Row) -> u16 { match r[0] { 13 => r[3], 8 => r[2], 6 | 12 => r[1], _ => NONE } }
pub struct Inputs { pub regq: Vec<Vec<u16>>, pub regb: Vec<Vec<u16>>, pub nq: usize, pub nb: usize, pub reg_rows: Vec<(u64, u16, u16)> }
pub fn inputs(rows: &[Row]) -> Inputs {
    let mut regq: Vec<Vec<u16>> = Vec::new(); let mut regb: Vec<Vec<u16>> = Vec::new(); let (mut nq, mut nb) = (0usize, 0usize); let mut reg_rows = Vec::new();
    for (i, r) in rows.iter().enumerate() {
        let k = r[0];
        for j in 1..=nqu(k) { nq = nq.max(r[j] as usize + 1); }
        match k { 3 | 4 | 5 => { nb = nb.max(r[1] as usize + 1); if r[2] != NONE { nb = nb.max(r[2] as usize + 1); } }
                  6 | 7 => { if r[2] != NONE { nb = nb.max(r[2] as usize + 1); } } 8 | 9 => { if r[3] != NONE { nb = nb.max(r[3] as usize + 1); } }
                  12 => { if r[2] != NONE { nb = nb.max(r[2] as usize + 1); } } 15 => nb = nb.max(r[1] as usize + 1), _ => {} }
        match k { 1 => { let a = r[1] as usize; while regq.len() <= a { regq.push(Vec::new()); regb.push(Vec::new()); } }
                  2 => { regq[r[1] as usize].push(r[2]); nq = nq.max(r[2] as usize + 1); reg_rows.push((i as u64, r[1], r[2])); }
                  18 => { regb[r[1] as usize].push(r[2]); nb = nb.max(r[2] as usize + 1); } _ => {} }
    }
    Inputs { regq, regb, nq, nb, reg_rows }
}
pub struct State<const NW: usize> { pub q: Vec<[u64; NW]>, pub b: Vec<[u64; NW]>, pub base: [u64; NW], pub stack: Vec<[u64; NW]>, pub rng: Rng, pub expect: Vec<(U256, U256)> }
#[inline] pub fn is_zero<const NW: usize>(v: &[u64; NW]) -> bool { v.iter().all(|&x| x == 0) }
impl<const NW: usize> State<NW> {
    pub const NS: usize = 64 * NW;
    /// initial state of NS valid shots drawn from `seed` (xorshift; the census's law) and the expected results
    pub fn new(inp: &Inputs, seed: u64) -> Self {
        let cv = curve(); let mut rng = Rng(seed);
        let mut q = vec![[0u64; NW]; inp.nq]; let mut b = vec![[0u64; NW]; inp.nb]; let mut expect = Vec::new(); let mut shot = 0usize;
        while shot < Self::NS {
            let mut k = [0u64; 4]; for x in k.iter_mut() { *x = rng.next(); } let k1 = U256::from_limbs(k);
            for x in k.iter_mut() { *x = rng.next(); } let k2 = U256::from_limbs(k);
            let t = cv.mul(cv.gx, cv.gy, k1); let o = cv.mul(cv.gx, cv.gy, k2);
            if t.0 == o.0 { continue; }
            let e = cv.add(t.0, t.1, o.0, o.1);
            let (w, m) = (shot / 64, 1u64 << (shot % 64));
            for (i, &l) in inp.regq[0].iter().enumerate() { if t.0.bit(i) { q[l as usize][w] |= m; } }
            for (i, &l) in inp.regq[1].iter().enumerate() { if t.1.bit(i) { q[l as usize][w] |= m; } }
            for (i, &l) in inp.regb[2].iter().enumerate() { if o.0.bit(i) { b[l as usize][w] |= m; } }
            for (i, &l) in inp.regb[3].iter().enumerate() { if o.1.bit(i) { b[l as usize][w] |= m; } }
            expect.push(e); shot += 1;
        }
        State { q, b, base: [u64::MAX; NW], stack: Vec::new(), rng: Rng(seed ^ 0x9E3779B97F4A7C15), expect }
    }
    /// explicit shots (tx, ty, ox, oy) (at most NS; the rest repeat the first), e.g. the failing inputs of an evaluation
    pub fn from_points(inp: &Inputs, pts: &[(U256, U256, U256, U256)], seed: u64) -> Self {
        let cv = curve(); assert!(!pts.is_empty() && pts.len() <= Self::NS);
        let mut q = vec![[0u64; NW]; inp.nq]; let mut b = vec![[0u64; NW]; inp.nb]; let mut expect = Vec::new();
        for shot in 0..Self::NS { let (tx, ty, ox, oy) = pts[if shot < pts.len() { shot } else { 0 }];
            let (w, m) = (shot / 64, 1u64 << (shot % 64));
            for (i, &l) in inp.regq[0].iter().enumerate() { if tx.bit(i) { q[l as usize][w] |= m; } }
            for (i, &l) in inp.regq[1].iter().enumerate() { if ty.bit(i) { q[l as usize][w] |= m; } }
            for (i, &l) in inp.regb[2].iter().enumerate() { if ox.bit(i) { b[l as usize][w] |= m; } }
            for (i, &l) in inp.regb[3].iter().enumerate() { if oy.bit(i) { b[l as usize][w] |= m; } }
            expect.push(cv.add(tx, ty, ox, oy)); }
        State { q, b, base: [u64::MAX; NW], stack: Vec::new(), rng: Rng(seed ^ 0x9E3779B97F4A7C15), expect }
    }
    /// one record
    #[inline] pub fn step(&mut self, r: &Row) {
        let k = r[0];
        let cond_bit = match k { 6 | 7 => r[2], 8 | 9 => r[3], 3 | 4 | 5 => r[2], _ => NONE };
        let mut cond = self.base; if cond_bit != NONE { let c = &self.b[cond_bit as usize]; for i in 0..NW { cond[i] &= c[i]; } }
        match k {
            13 => { let (a, bb, t) = (r[1] as usize, r[2] as usize, r[3] as usize); let mut v = [0u64; NW]; for i in 0..NW { v[i] = cond[i] & self.q[a][i] & self.q[bb][i]; } for i in 0..NW { self.q[t][i] ^= v[i]; } }
            8 => { let (a, t) = (r[1] as usize, r[2] as usize); let mut v = [0u64; NW]; for i in 0..NW { v[i] = cond[i] & self.q[a][i]; } for i in 0..NW { self.q[t][i] ^= v[i]; } }
            6 => { let t = r[1] as usize; for i in 0..NW { self.q[t][i] ^= cond[i]; } }
            12 => { let mut x = [0u64; NW]; for i in 0..NW { x[i] = self.rng.next(); }
                if r[2] != NONE { let bt = r[2] as usize; for i in 0..NW { self.b[bt][i] = (self.b[bt][i] & !cond[i]) ^ (x[i] & cond[i]); } }
                let t = r[1] as usize; for i in 0..NW { self.q[t][i] &= !cond[i]; } }
            3 => { let t = r[1] as usize; for i in 0..NW { self.b[t][i] ^= cond[i]; } }
            4 => { let t = r[1] as usize; for i in 0..NW { self.b[t][i] &= !cond[i]; } }
            5 => { let t = r[1] as usize; for i in 0..NW { self.b[t][i] |= cond[i]; } }
            15 => { self.stack.push(self.base); let c = self.b[r[1] as usize]; for i in 0..NW { self.base[i] &= c[i]; } }
            16 => { if let Some(v) = self.stack.pop() { self.base = v; } }
            _ => {}
        }
    }
    /// shots that end wrong (wrong result or a non-output lane nonzero): bit mask
    pub fn fail_mask(&self, inp: &Inputs) -> [u64; NW] {
        let mut m = [0u64; NW];
        for s in 0..Self::NS { let (w, b) = (s / 64, 1u64 << (s % 64));
            let get = |reg: &Vec<u16>| { let mut v = U256::ZERO; for (i, &l) in reg.iter().enumerate() { if self.q[l as usize][w] & b != 0 { v.set_bit(i, true); } } v };
            if get(&inp.regq[0]) != self.expect[s].0 || get(&inp.regq[1]) != self.expect[s].1 { m[w] |= b; } }
        let outl: std::collections::HashSet<u16> = inp.regq[0].iter().chain(inp.regq[1].iter()).copied().collect();
        for l in 0..self.q.len() { if !outl.contains(&(l as u16)) { for i in 0..NW { m[i] |= self.q[l][i]; } } }
        m }
    /// (wrong results, non-output lanes nonzero, stack depth) at the end
    pub fn verdict(&self, inp: &Inputs) -> (u32, u32, usize) {
        let mut bad = 0u32;
        for s in 0..Self::NS { let (w, m) = (s / 64, 1u64 << (s % 64));
            let get = |reg: &Vec<u16>| { let mut v = U256::ZERO; for (i, &l) in reg.iter().enumerate() { if self.q[l as usize][w] & m != 0 { v.set_bit(i, true); } } v };
            if get(&inp.regq[0]) != self.expect[s].0 || get(&inp.regq[1]) != self.expect[s].1 { bad += 1; } }
        let outl: std::collections::HashSet<u16> = inp.regq[0].iter().chain(inp.regq[1].iter()).copied().collect();
        let dirty = (0..self.q.len()).filter(|&l| !is_zero(&self.q[l]) && !outl.contains(&(l as u16))).count() as u32;
        (bad, dirty, self.stack.len())
    }
}

// ------------------------------------------------------------------ algebraic evaluation (structural zero test)
/// GF(2^64) = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1): carry-less product (4-bit windows) and reduction
#[inline] pub fn gmul(a: u64, b: u64) -> u64 {
    if a == 0 || b == 0 { return 0; } if a == 1 { return b; } if b == 1 { return a; }
    let mut t = [0u128; 16]; for i in 1..16usize { t[i] = t[i & (i - 1)] ^ ((a as u128) << i.trailing_zeros()); }
    let mut r: u128 = 0; for j in (0..16).rev() { r = (r << 4) ^ t[((b >> (4 * j)) & 15) as usize]; }
    let (hi, lo) = ((r >> 64) as u64, r as u64);
    let f = (hi as u128) ^ ((hi as u128) << 1) ^ ((hi as u128) << 3) ^ ((hi as u128) << 4);
    let h2 = (f >> 64) as u64;
    lo ^ (f as u64) ^ h2 ^ (h2 << 1) ^ (h2 << 3) ^ (h2 << 4)
}
/// one random point: every input bit (both coordinates of the quantum point, both of the classical point) and every HMR
/// outcome is an independent random element of GF(2^64); X / CX / CCX / conditions / scopes / bit ops / HMR resets act as
/// polynomials (XOR = +, AND = *, NOT c = 1 + c).  A lane whose value is the ZERO POLYNOMIAL is zero on every input (Boolean
/// points included); a nonzero polynomial vanishes at a random point with tiny probability (heuristically ~2^-64; never
/// claimed as a proof).  Lanes that are zero only through Boolean identities (x^2 = x) evaluate nonzero: conservative.
pub struct Alg { pub q: Vec<u64>, pub b: Vec<u64>, pub base: u64, pub stack: Vec<u64>, pub rng: Rng, pub boolean_classical: bool }
impl Alg {
    /// `boolean_classical`: the classical inputs (the second point: a random VALID point, its bits 0 / 1) and the HMR
    /// outcomes (random 0 / 1) stay Boolean, only the quantum input bits are field elements; else everything is a symbol
    pub fn new(inp: &Inputs, seed: u64, boolean_classical: bool) -> Self {
        let mut rng = Rng(seed); let mut q = vec![0u64; inp.nq]; let mut b = vec![0u64; inp.nb];
        let mut r = || loop { let x = rng.next(); if x > 1 { break x; } };
        for reg in [0usize, 1] { for &l in inp.regq[reg].iter() { q[l as usize] = r(); } }
        if boolean_classical { let cv = curve(); let mut k = [0u64; 4]; for x in k.iter_mut() { *x = r(); } let o = cv.mul(cv.gx, cv.gy, U256::from_limbs(k));
            for (i, &l) in inp.regb[2].iter().enumerate() { b[l as usize] = o.0.bit(i) as u64; }
            for (i, &l) in inp.regb[3].iter().enumerate() { b[l as usize] = o.1.bit(i) as u64; } }
        else { for reg in [2usize, 3] { for &l in inp.regb[reg].iter() { b[l as usize] = r(); } } }
        Alg { q, b, base: 1, stack: Vec::new(), rng: Rng(seed ^ 0x9E3779B97F4A7C15), boolean_classical }
    }
    #[inline] pub fn step(&mut self, r: &Row) {
        let k = r[0];
        let cond_bit = match k { 6 | 7 => r[2], 8 | 9 => r[3], 3 | 4 | 5 => r[2], _ => NONE };
        let cond = if cond_bit != NONE { gmul(self.base, self.b[cond_bit as usize]) } else { self.base };
        match k {
            13 => { let v = gmul(gmul(cond, self.q[r[1] as usize]), self.q[r[2] as usize]); self.q[r[3] as usize] ^= v; }
            8 => { let v = gmul(cond, self.q[r[1] as usize]); self.q[r[2] as usize] ^= v; }
            6 => { self.q[r[1] as usize] ^= cond; }
            12 => { let x = if self.boolean_classical { self.rng.next() & 1 } else { self.rng.next() }; let nc = 1 ^ cond;
                if r[2] != NONE { let bt = r[2] as usize; self.b[bt] = gmul(self.b[bt], nc) ^ gmul(x, cond); }
                let t = r[1] as usize; self.q[t] = gmul(self.q[t], nc); }
            3 => { self.b[r[1] as usize] ^= cond; }
            4 => { let t = r[1] as usize; self.b[t] = gmul(self.b[t], 1 ^ cond); }
            5 => { let t = r[1] as usize; self.b[t] = gmul(self.b[t], 1 ^ cond) ^ cond; }
            15 => { self.stack.push(self.base); self.base = gmul(self.base, self.b[r[1] as usize]); }
            16 => { if let Some(v) = self.stack.pop() { self.base = v; } }
            _ => {}
        }
    }
}
