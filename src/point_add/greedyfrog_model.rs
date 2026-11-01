//! greedyfrog (uniform greedy Euclid): reference models for the traversal circuit in `greedyfrog.rs`.
//!
//! Integer spec (as lv27/greedyfrog/greedyfrog1.py): target (A, tA), source (B, tB), A tB + B tA = p. Step: e = LA - LB,
//! d = [2^e B > A], e' = e - d, A -= 2^e' B, tA += 2^e' tB, z = LA - bl(A), swap when 0 < A < B.
//!
//! Lane model (as greedyfrog2.py, plus a marker): rings X (target) and Y (source) of W lanes, lane W-1 on top. A ring holds
//! its value top-normalised (bit k at lane W - L + k), a marker 1 at lane W - L - 1, and the partner cofactor
//! bit-reversed under the marker (bit i at lane W - L - 2 - i). X = (A, marker, tB), Y = (B, marker, tA). With L = 0
//! (value 0) the marker sits at lane W-1. The forward slot follows the circuit's order step for step:
//!   F1 z0 = [LA == 0]; cnt += z0                      (act = !z0)
//!   F2 d = act & [Y[W-LB..W) > X[W-LB..W)]           (B > A >> e)
//!   F3 rotate X up by d                               (A's MSB wraps into lane 0)
//!   F4 X[W-LB..W) ++ X[0] -= Y[W-LB..W) ++ 0          (borrow chain starts at W - LB)
//!   F5 LA -= d;  Y += X over lanes W-LA-2 down to 0   (Y's significance grows downward; X lane 0 counts
//!                                                      only where d = 0, else it holds A's MSB)
//!   F6 rho = act & min(lz(X from the top), RCAP)     (stops at the marker when A' = 0)
//!   F7 rotate X up by rho;  F8 LA -= rho
//!   F9 sw = act & [LA != 0] & X[W-1] & (LA < LB | LA == LB & Y[W-LB..W) > X[W-LB..W))
//!   F10 swap X <-> Y, LA <-> LB, par ^= sw
//!   F11 ghost d, rho, sw, a1; erase z0 with [LA == 0] & [cnt != 0]
//! F2-F5 run only where a1 = act & X[W-1]: a step whose renormalisation exceeds RCAP lanes leaves X's top lanes zero
//! (lag), and the following slots are stalls that only renormalise (F6-F10) until X is normalised again. LA counts the
//! lag lanes (LA = bl(A) + lag). The inverse slot decodes sw and the rotation since the last step from the post-state
//! (cofactor windows), splits it into this slot's rho and a1 (`rho_of`), and undoes F10..F1.

pub type N = ruint::Uint<384, 6>;
/// G2-01 MARKER-FREE RINGS (Q825 B-MARKERFREE): drop the 1-valued marker lane at W-L-1 (it only restates L, which
/// LA/LB hold): W 258 -> 257. Value bit k at W-L+k, cofactor bit i at CW-1-L-i (numerically the same lanes as with
/// the marker). The finishing step's leading-zero count would run into tB, so the renorm prefix is gated by [LA > i]
/// (rho = min(lz, LA, 7); with the marker lz <= LA already, so the model applies the min in both modes).
pub const MARKER_FREE: bool = true;
/// ring lanes: value + (marker) + partner cofactor <= 257 (+ 1) (A tB < p)
pub const W: usize = if MARKER_FREE { 257 } else { 258 };
/// cofactor frame top: the cofactor's bit i sits at lane CW - 1 - L - i in both modes (A tB < p: L + bl(cof) <= CW)
pub const CW: usize = 257;
/// marker lanes (1 with the marker, 0 marker-free)
pub const MK: usize = W - CW;

pub fn p() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}

pub fn bl(x: &N) -> usize {
    x.bit_len()
}

/// Integer spec state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spec {
    pub a: N,
    pub ta: N,
    pub b: N,
    pub tb: N,
    pub la: usize,
    pub lb: usize,
    pub par: u8,
    pub cnt: usize,
    /// renormalisation lanes still owed by the last step (LA = bl(A) + lag)
    pub lag: usize,
}

/// Renormalisation lanes per slot (a 3-stage barrel).
pub const RCAP: usize = 7;

/// What one slot did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    Done,
    Stall { rho: usize, sw: bool },
    Step { ep: usize, d: usize, z: usize, rho: usize, sw: bool },
}

impl Spec {
    pub fn new(x: N) -> Spec {
        Spec { a: p(), ta: N::ZERO, b: x, tb: N::from(1u64), la: 256, lb: bl(&x), par: 0, cnt: 0, lag: 0 }
    }
    /// One slot.
    pub fn fwd(&mut self) -> Slot {
        if self.la == 0 {
            self.cnt += 1;
            return Slot::Done;
        }
        if self.lag > 0 {
            let rho = self.lag.min(RCAP);
            self.lag -= rho;
            self.la -= rho;
            let sw = self.finish();
            return Slot::Stall { rho, sw };
        }
        let e = self.la - self.lb;
        let d = usize::from((self.b << e) > self.a);
        let ep = e - d;
        self.a -= self.b << ep;
        self.ta += self.tb << ep;
        let z = self.la - bl(&self.a);
        let rho = (z - d).min(RCAP);
        self.lag = z - d - rho;
        self.la -= d + rho;
        let sw = self.finish();
        Slot::Step { ep, d, z, rho, sw }
    }
    /// The swap, once A is normalised (the finishing step never swaps).
    fn finish(&mut self) -> bool {
        let sw = self.lag == 0 && self.a != N::ZERO && self.a < self.b;
        if sw {
            std::mem::swap(&mut self.a, &mut self.b);
            std::mem::swap(&mut self.ta, &mut self.tb);
            std::mem::swap(&mut self.la, &mut self.lb);
            self.par ^= 1;
        }
        sw
    }
}

/// Split the decoded rotation since the last step (r) into this slot's rotation and a1 (the slot was a step):
/// a step rotates min(r, RCAP) <= 7, stall m then rotates up to 7 more, so r >= 8 means a stall, whose own rotation
/// is ((r mod 8) + #{8, 15, 22, 29 <= r}) mod 8.
pub fn rho_of(r: usize) -> (usize, bool) {
    if r < 8 {
        return (r, true);
    }
    let m = [8, 15, 22, 29].iter().filter(|&&c| r >= c).count();
    (((r & 7) + m) & 7, false)
}

/// Lane model state: rings as bit vectors (index = lane).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lanes {
    pub x: Vec<u8>,
    pub y: Vec<u8>,
    pub la: usize,
    pub lb: usize,
    pub cnt: usize,
    pub par: u8,
}

fn put(ring: &mut [u8], val: &N, l: usize, cof: &N) {
    for k in 0..l {
        ring[W - l + k] = u8::from(val.bit(k));
    }
    if MK == 1 {
        ring[W - l - 1] = 1;
    }
    let lc = bl(cof);
    assert!(l + MK + lc <= W, "ring overflow: value {l} + marker + cofactor {lc}");
    for i in 0..lc {
        ring[CW - 1 - l - i] = u8::from(cof.bit(i));
    }
}

fn get(ring: &[u8], l: usize) -> (N, N) {
    let mut v = N::ZERO;
    for k in 0..l {
        if ring[W - l + k] == 1 {
            v |= N::from(1u64) << k;
        }
    }
    if MK == 1 {
        assert_eq!(ring[W - l - 1], 1, "marker missing");
    }
    let mut c = N::ZERO;
    for i in 0..CW - l {
        if ring[CW - 1 - l - i] == 1 {
            c |= N::from(1u64) << i;
        }
    }
    (v, c)
}

/// Value bits of a lane range read as a number, bit 0 = first lane listed.
fn num(ring: &[u8], lanes: &[usize]) -> N {
    let mut v = N::ZERO;
    for (i, &l) in lanes.iter().enumerate() {
        if ring[l] == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}

fn set_num(ring: &mut [u8], lanes: &[usize], v: &N) {
    for (i, &l) in lanes.iter().enumerate() {
        ring[l] = u8::from(v.bit(i));
    }
}

pub fn rot_up(ring: &mut Vec<u8>, k: usize) {
    let k = k % W;
    ring.rotate_right(k); // lane j -> lane j + k
}

pub fn rot_down(ring: &mut Vec<u8>, k: usize) {
    let k = k % W;
    ring.rotate_left(k);
}

/// Lanes of the F4 value chain: W - lb .. W - 1, then 0.
pub fn value_lanes(lb: usize) -> Vec<usize> {
    let mut v: Vec<usize> = (W - lb..W).collect();
    v.push(0);
    v
}

/// Lanes of the F5 cofactor chain: CW - la - 1 down to 0 (la after F5's LA -= d).
pub fn cof_lanes(la: usize) -> Vec<usize> {
    (0..=CW - la - 1).rev().collect()
}

impl Lanes {
    pub fn from_spec(s: &Spec) -> Lanes {
        let mut x = vec![0u8; W];
        let mut y = vec![0u8; W];
        put(&mut x, &s.a, s.la, &s.tb);
        put(&mut y, &s.b, s.lb, &s.ta);
        Lanes { x, y, la: s.la, lb: s.lb, cnt: s.cnt, par: s.par }
    }
    pub fn to_spec(&self) -> Spec {
        let (a, tb) = get(&self.x, self.la);
        let (b, ta) = get(&self.y, self.lb);
        let lag = self.la - bl(&a);
        Spec { a, ta, b, tb, la: self.la, lb: self.lb, par: self.par, cnt: self.cnt, lag }
    }
    /// Leading zeros of a ring from the top lane down.
    pub fn lz_top(ring: &[u8]) -> usize {
        (0..W).take_while(|&k| ring[W - 1 - k] == 0).count()
    }
    /// The forward slot in circuit order. Returns the ghosted (d, rho, sw, a1).
    pub fn fwd(&mut self) -> (usize, usize, bool, bool) {
        let (d, rho, sw, a1, _, _) = self.fwd_ex();
        (d, rho, sw, a1)
    }
    /// `fwd` plus (LA at the renormalisation, the naive leading-zero count exceeded it: the marker-free overshoot that
    /// the LA gate absorbs).
    pub fn fwd_ex(&mut self) -> (usize, usize, bool, bool, usize, bool) {
        // F1
        let act = self.la != 0;
        if !act {
            self.cnt += 1;
            return (0, 0, false, false, 0, false);
        }
        let a1 = self.x[W - 1] == 1;
        let mut d = 0;
        if a1 {
            // F2
            let vl: Vec<usize> = (W - self.lb..W).collect();
            d = usize::from(num(&self.y, &vl) > num(&self.x, &vl));
            // F3
            rot_up(&mut self.x, d);
            // F4
            let lanes = value_lanes(self.lb);
            let xv = num(&self.x, &lanes);
            // the chain's top source is 0 (Y lane 0 may hold tA's MSB)
            let yv = num(&self.y, &lanes[..lanes.len() - 1]);
            assert!(xv >= yv, "F4 borrow out");
            set_num(&mut self.x, &lanes, &(xv - yv));
            // F5
            self.la -= d;
            let cl = cof_lanes(self.la);
            // X lane 0 holds A's MSB where d = 1
            let xs = if d == 1 { num(&self.x, &cl[..cl.len() - 1]) } else { num(&self.x, &cl) };
            let s = num(&self.y, &cl) + xs;
            assert!(!s.bit(cl.len()), "F5 carry out");
            set_num(&mut self.y, &cl, &s);
        }
        // F6, F7, F8 (marker-free: gated by [LA > i]; with the marker lz <= LA)
        let lz = Self::lz_top(&self.x);
        let (la_ren, over) = (self.la, lz > self.la);
        let rho = lz.min(self.la).min(RCAP);
        rot_up(&mut self.x, rho);
        self.la -= rho;
        // F9, F10
        let sw = self.la != 0 && self.x[W - 1] == 1 && (self.la < self.lb || (self.la == self.lb && {
            let vl: Vec<usize> = (W - self.lb..W).collect();
            num(&self.y, &vl) > num(&self.x, &vl)
        }));
        if sw {
            std::mem::swap(&mut self.x, &mut self.y);
            std::mem::swap(&mut self.la, &mut self.lb);
            self.par ^= 1;
        }
        (d, rho, sw, a1, la_ren, over)
    }
}

/// Bottom cofactor window of a ring holding a value of bit length `l`: (slack, the cofactor's top `nb` bits read
/// MSB-first from the slack lane up, lanes from the marker up read as zero).
pub fn window(ring: &[u8], l: usize, nb: usize) -> (usize, N) {
    let m = CW - l; // first lane above the cofactor (the marker lane, or the value's LSB)
    let sl = (0..m).take_while(|&j| ring[j] == 0).count();
    let mut v = N::ZERO;
    for i in 0..nb {
        let j = sl + i;
        v <<= 1;
        if j < m && ring[j] == 1 {
            v |= N::from(1u64);
        }
    }
    (sl, v)
}

/// Decode on the post-state: (sw, r) from the cofactor windows, r = the rotation since the last step (`rho_of`
/// splits it). `nb` window bits, `k` division rows.
/// Returns None when the windows cannot decide (counted as a failure).
pub fn decode(st: &Lanes, nb: usize, k: usize) -> Option<(bool, usize)> {
    // sw: target's own cofactor (in Y) <= source's own cofactor (in X)
    let (sy, wy) = window(&st.y, st.lb, nb);
    let (sx, wx) = window(&st.x, st.la, nb);
    let bly = CW - st.lb - sy; // cofactor bit lengths
    let blx = CW - st.la - sx;
    let sw = bly < blx || (bly == blx && wy <= wx);
    // un-swapped view
    let (la, lb, sxx, syy, wxx, wyy) = if sw { (st.lb, st.la, sy, sx, wy, wx) } else { (st.la, st.lb, sx, sy, wx, wy) };
    // Q = floor(tA / tB): dividend window wyy (Y = target's cofactor after un-swap), divisor wxx; rows j = 0..k-1 at
    // positions kt - j, kt = bl(tA) - bl(tB); r = sX - sY - j_last (derivation in greedyfrog.rs)
    let kt = (CW - lb - syy) as isize - (CW - la - sxx) as isize; // bl(tA) - bl(tB) after un-swap
    if kt < 0 {
        return None;
    }
    let mut rem = wyy;
    let mut jlast = None;
    for j in 0..k.min(kt as usize + 1) {
        let sh = wxx >> j;
        if sh != N::ZERO && rem >= sh {
            rem -= sh;
            jlast = Some(j);
        }
    }
    let jl = jlast?;
    let r = sxx as isize - syy as isize - jl as isize;
    if r < 0 {
        return None;
    }
    Some((sw, r as usize))
}

/// SW-CARRY (R-005a): `decode` plus what the inverse rows leave for the next inverse slot: (sw, r, j_last, q_0,
/// popcount of the quotient bits the rows found). j_last is the sweep's jl before its in-place transform (0 where no
/// row j >= 1 fired), q_0 = !s0 is row 0's quotient bit.
pub fn decode_ext(st: &Lanes, nb: usize, k: usize) -> Option<(bool, usize, usize, bool, u32)> {
    let (sy, wy) = window(&st.y, st.lb, nb);
    let (sx, wx) = window(&st.x, st.la, nb);
    let bly = CW - st.lb - sy;
    let blx = CW - st.la - sx;
    let sw = bly < blx || (bly == blx && wy <= wx);
    let (la, lb, sxx, syy, wxx, wyy) = if sw { (st.lb, st.la, sy, sx, wy, wx) } else { (st.la, st.lb, sx, sy, wx, wy) };
    let kt = (CW - lb - syy) as isize - (CW - la - sxx) as isize;
    if kt < 0 {
        return None;
    }
    let mut rem = wyy;
    let mut jlast = None;
    let mut q0 = false;
    let mut pop = 0u32;
    for j in 0..k.min(kt as usize + 1) {
        let sh = wxx >> j;
        if sh != N::ZERO && rem >= sh {
            rem -= sh;
            jlast = Some(j);
            pop += 1;
            if j == 0 {
                q0 = true;
            }
        }
    }
    let jl = jlast?;
    let r = sxx as isize - syy as isize - jl as isize;
    if r < 0 {
        return None;
    }
    Some((sw, r as usize, jl, q0, pop))
}

/// SW-CARRY single-step flag from the sweep's pre-transform jl and row 0's sign lane s0 = !q_0:
/// single = [jl == 0] | [jl == 1] & s0 (the quotient's top set bit is row 0 or row 1).
pub fn swc_single(jl: usize, q0: bool) -> bool {
    jl == 0 || (jl == 1 && !q0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// SW-CARRY (R-005a) decisive check on the integer walk with the circuit's windows (NB = 28, per-slot rows k from
    /// `windows()`, masked / parked slots included): on every correctly decoded slot t, single(jl, s0) == [run count
    /// == 1] == [popcount(Q) == 1], and c_t = a1_t & single_t == sw_(t-1), the swap the inverse slot t - 1 must undo.
    /// GREEDYFROG_SWC_N walks (default 2000), 8 threads.
    #[test]
    fn greedyfrog_swcarry_single_flag() {
        use super::super::greedyfrog::{windows, NB, NSLOTS};
        let n: usize = std::env::var("GREEDYFROG_SWC_N").ok().and_then(|v| v.parse().ok()).unwrap_or(2000);
        let ws = windows();
        let ks: Vec<usize> = ws.iter().map(|w| w.k).collect();
        let masked: Vec<bool> = ws.iter().map(|w| w.mx < NB + 1).collect();
        let threads = 8usize;
        // per thread: [pairs checked, c != sw_prev, single != [run == 1], single != [pop == 1], decode failures,
        //              pairs on masked slots, walks with a failure, a1 & single count]
        let res: Vec<[u64; 8]> = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..threads).map(|t| {
                let (ks, masked) = (&ks, &masked);
                sc.spawn(move || {
                    let mut rng = Rng(0x5743_4152_5259_0001 ^ (0x9e37_79b9_7f4a_7c15u64.wrapping_mul(t as u64 + 1)));
                    let mut c = [0u64; 8];
                    for _ in 0..(n / threads) {
                        let x = rng.input();
                        let mut sp = Spec::new(x);
                        let mut run = 0usize;
                        let mut prev_sw = false;
                        let mut walk_bad = false;
                        for s in 0..NSLOTS {
                            let rec = sp.fwd();
                            let (a1, sw, rho) = match rec {
                                Slot::Done => (false, false, 0),
                                Slot::Stall { rho, sw } => (false, sw, rho),
                                Slot::Step { rho, sw, .. } => { run += 1; (true, sw, rho) }
                            };
                            let mut cflag = false;
                            let mut ok = true;
                            if !matches!(rec, Slot::Done) {
                                let st = Lanes::from_spec(&sp);
                                match decode_ext(&st, NB, ks[s]) {
                                    Some((dsw, dr, jl, q0, pop)) if dsw == sw && rho_of(dr) == (rho, a1) => {
                                        let single = swc_single(jl, q0);
                                        if a1 {
                                            if single != (run == 1) { c[2] += 1; }
                                            if single != (pop == 1) { c[3] += 1; }
                                        }
                                        cflag = a1 && single;
                                    }
                                    _ => { c[4] += 1; walk_bad = true; ok = false; }
                                }
                            }
                            if s >= 1 && ok {
                                c[0] += 1;
                                if masked[s] { c[5] += 1; }
                                if cflag != prev_sw { c[1] += 1; }
                                if cflag { c[7] += 1; }
                            }
                            if sw {
                                run = 0;
                            }
                            prev_sw = sw;
                        }
                        if walk_bad { c[6] += 1; }
                    }
                    c
                })
            }).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut t = [0u64; 8];
        for r in &res {
            for i in 0..8 {
                t[i] += r[i];
            }
        }
        eprintln!("SWCARRY walks {} pairs {} (masked-slot pairs {}, carried swaps {}): c != sw_prev {}, single != [run==1] {}, \
                   single != [pop==1] {}, decode failures {} (walks {})", n / threads * threads, t[0], t[5], t[7], t[1], t[2],
                  t[3], t[4], t[6]);
        // pairs are counted where slot t decodes (a failing decode is a windows / lambda failure already)
        assert_eq!(t[1], 0);
        assert_eq!(t[2], 0);
        assert_eq!(t[3], 0);
    }

    pub(crate) struct Rng(pub u64);
    impl Rng {
        pub fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        /// x in [1, p/2] as the shell reflects it (GREEDYFROG_NOREFLECT=1: [1, p); x > p/2 makes the first quotient 1 and
        /// breaks the decode at the second level, tA = tB = 1)
        pub fn input(&mut self) -> N {
            let pp = p();
            let refl = std::env::var_os("GREEDYFROG_NOREFLECT").is_none();
            loop {
                let mut v = N::ZERO;
                for i in 0..4 {
                    v |= N::from(self.next()) << (64 * i);
                }
                if v != N::ZERO && v < pp {
                    let w = pp - v;
                    return if refl && w < v { w } else { v };
                }
            }
        }
    }

    /// Per-slot envelope of the quantities the windowed circuit fixes classically (GREEDYFROG_ENV_N walks, GREEDYFROG_ENV_OUT file).
    /// Columns per forward slot s (active shots only): n lb_min lb_max lad_min lad_max cof_min mxp_min mx_min kt_max
    /// rows_max sx_max sy_max. lad = LA - d; cof = lowest lane of tA' after F5; mxp / mx = bit length of X's cofactor
    /// before / after the decode's un-swap; rows = kt - e' + 1; sx, sy = post-state slacks (marker-relative windows).
    #[test]
    fn greedyfrog_envelope() {
        let n: usize = std::env::var("GREEDYFROG_ENV_N").ok().and_then(|v| v.parse().ok()).unwrap_or(2000);
        let seed: u64 = std::env::var("GREEDYFROG_ENV_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0x5eed_e17e);
        let ns = 300usize;
        const C: usize = 14;
        let threads = 4usize;
        let init = |c: usize| -> isize { if [0, 2, 4, 6, 9, 10, 11, 12, 13].contains(&c) { if c == 0 { 0 } else { -1 } } else { isize::MAX } };
        let results: Vec<(Vec<[isize; C]>, Vec<u64>, Vec<u64>, Vec<u64>, Vec<[u64; 3]>)> = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..threads).map(|t| sc.spawn(move || {
                let mut rng = Rng(seed ^ (0x9e37_79b9_7f4a_7c15u64.wrapping_mul(t as u64 + 1)));
                let mut env: Vec<[isize; C]> = (0..ns).map(|_| {
                    let mut a = [0isize; C];
                    for c in 0..C { a[c] = init(c); }
                    a
                }).collect();
                let mut steps_h = vec![0u64; ns + 1];
                let mut rows_h = vec![0u64; 64];
                let mut r_h = vec![0u64; 260];
                let mut st_h = vec![[0u64; 3]; 400];
                for _ in 0..(n / threads) {
                    let mut stl = [0usize; 3];
                    let x = rng.input();
                    let mut sp = Spec::new(x);
                    let mut steps = 0;
                    let mut last_ep = 0usize;
                    for s in 0..ns {
                        if sp.la == 0 { sp.cnt += 1; continue; }
                        let pre = sp.clone();
                        let slot = sp.fwd();
                        steps += 1;
                        let v = &mut env[s];
                        v[0] += 1;
                        let upd_min = |v: &mut [isize; C], c: usize, x: isize| { if x < v[c] { v[c] = x; } };
                        let upd_max = |v: &mut [isize; C], c: usize, x: isize| { if x > v[c] { v[c] = x; } };
                        let sw = match slot {
                            Slot::Step { ep, d, z, sw, .. } => {
                                last_ep = ep;
                                let (la, lb) = (pre.la, pre.lb);
                                // tA' (target cofactor after F5) = pre.ta + 2^ep tb
                                let tap = pre.ta + (pre.tb << ep);
                                let cof_lane = CW as isize - lb as isize - bl(&tap) as isize;
                                upd_min(v, 1, lb as isize); upd_max(v, 2, lb as isize);
                                upd_min(v, 3, (la - d) as isize); upd_max(v, 4, (la - d) as isize);
                                upd_min(v, 5, cof_lane);
                                upd_max(v, 6, z as isize - d as isize);
                                r_h[z - d] += 1;
                                for (ci, cap) in [3usize, 7, 15].iter().enumerate() {
                                    let rr = z - d;
                                    if rr > *cap { stl[ci] += (rr - cap + cap - 1) / cap; }
                                }
                                sw
                            }
                            Slot::Stall { sw, .. } => sw,
                            Slot::Done => unreachable!(),
                        };
                        // decode quantities on the post-state: X = (A, tB), Y = (B, tA)
                        let mxp = bl(&sp.tb) as isize;
                        let sxp = CW as isize - sp.la as isize - mxp; // X slack (cofactor top at CW - LA - 1)
                        let syp = CW as isize - sp.lb as isize - bl(&sp.ta) as isize;
                        let (tau, tbu) = if sw { (sp.tb, sp.ta) } else { (sp.ta, sp.tb) };
                        let mx = bl(&tbu) as isize;
                        let kt = bl(&tau) as isize - mx;
                        let rows = kt - last_ep as isize + 1;
                        upd_min(v, 7, mxp); upd_min(v, 8, mx);
                        upd_max(v, 9, kt); upd_max(v, 10, rows); upd_max(v, 11, sxp.max(syp));
                        upd_max(v, 12, mxp); upd_max(v, 13, mx);
                        if matches!(slot, Slot::Step { .. }) { rows_h[rows.clamp(0, 63) as usize] += 1; }
                    }
                    assert_eq!(sp.la, 0);
                    steps_h[steps.min(ns)] += 1;
                    for ci in 0..3 { st_h[(steps + stl[ci]).min(399)][ci] += 1; }
                }
                (env, steps_h, rows_h, r_h, st_h)
            })).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut env: Vec<[isize; C]> = (0..ns).map(|_| { let mut a = [0isize; C]; for c in 0..C { a[c] = init(c); } a }).collect();
        let mut steps_h = vec![0u64; ns + 1];
        let mut rows_h = vec![0u64; 64];
        let mut r_h = vec![0u64; 260];
        let mut st_h = vec![[0u64; 3]; 400];
        for (e, sh, rh, zh, sth) in results {
            for i in 0..400 { for ci in 0..3 { st_h[i][ci] += sth[i][ci]; } }
            for s in 0..ns {
                env[s][0] += e[s][0];
                for c in 1..C {
                    let mx = [2, 4, 6, 9, 10, 11, 12, 13].contains(&c);
                    if e[s][0] == 0 { continue; }
                    if env[s][0] == e[s][0] { env[s][c] = e[s][c]; continue; }
                    env[s][c] = if mx { env[s][c].max(e[s][c]) } else { env[s][c].min(e[s][c]) };
                }
            }
            for i in 0..sh.len() { steps_h[i] += sh[i]; }
            for i in 0..64 { rows_h[i] += rh[i]; }
            for i in 0..260 { r_h[i] += zh[i]; }
        }
        let mut out = String::new();
        out.push_str("# s n lb_min lb_max lad_min lad_max cof_min r_max mxp_min mx_min kt_max rows_max slack_max mxp_max mx_max\n");
        for s in 0..ns {
            let v = env[s];
            if v[0] == 0 { break; }
            out.push_str(&format!("{s} {}\n", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")));
        }
        let tot: u64 = steps_h.iter().sum();
        let mut tail = String::new();
        let mut acc = 0u64;
        for k in (0..=ns).rev() {
            acc += steps_h[k];
            if steps_h[k] > 0 { tail.push_str(&format!(" {k}:{acc}")); }
            if acc > 2000 { break; }
        }
        out.push_str(&format!("# walks {tot}; steps tail (steps:walks with >= steps):{tail}\n"));
        let rt: u64 = rows_h.iter().sum();
        out.push_str(&format!("# rows needed per step (of {rt}): {}\n",
            (1..64).filter(|&i| rows_h[i] > 0).map(|i| format!("{i}:{}", rows_h[i])).collect::<Vec<_>>().join(" ")));
        out.push_str(&format!("# r per step: {}\n",
            (0..260).filter(|&i| r_h[i] > 0).map(|i| format!("{i}:{}", r_h[i])).collect::<Vec<_>>().join(" ")));
        for (ci, cap) in [3, 7, 15].iter().enumerate() {
            let mut acc = 0u64;
            let mut tail = String::new();
            for k in (0..400).rev() {
                acc += st_h[k][ci];
                if st_h[k][ci] > 0 { tail.push_str(&format!(" {k}:{acc}")); }
                if acc > 2000 { break; }
            }
            out.push_str(&format!("# steps + stalls with a {cap}-lane barrel cap, tail (slots:walks needing >= slots):{tail}\n"));
        }
        let path = std::env::var("GREEDYFROG_ENV_OUT").unwrap_or_else(|_| "greedyfrog_env.txt".into());
        std::fs::write(&path, &out).unwrap();
        eprintln!("greedyfrog envelope: {tot} walks -> {path}");
    }

    /// Lane model == integer spec on every slot, and the decode recovers (sw, r) of every step from its post-state.
    #[test]
    fn greedyfrog_model_lanes_and_decode() {
        let n: usize = std::env::var("GREEDYFROG_N").ok().and_then(|v| v.parse().ok()).unwrap_or(200);
        let mut rng = Rng(0x5eed_1234_abcd_0001);
        let mut bad = 0;
        let mut steps = 0;
        for _ in 0..n {
            let x = rng.input();
            let mut sp = Spec::new(x);
            let mut ln = Lanes::from_spec(&sp);
            for _ in 0..300 {
                let rec = sp.fwd();
                let (d, rho, sw, a1) = ln.fwd();
                assert_eq!(ln.to_spec(), sp, "lane model diverged");
                let want = match rec {
                    Slot::Done => None,
                    Slot::Stall { rho: sr, sw: ssw } => Some((0, sr, ssw, false)),
                    Slot::Step { d: sd, rho: sr, sw: ssw, .. } => Some((sd, sr, ssw, true)),
                };
                if let Some(wv) = want {
                    assert_eq!((d, rho, sw, a1), wv);
                    steps += 1;
                    match decode(&ln, 32, 22) {
                        Some((dsw, dr)) if dsw == sw && rho_of(dr) == (rho, a1) => {}
                        _ => bad += 1,
                    }
                }
            }
            assert_eq!(sp.a, N::ZERO, "walk not finished in 300 slots");
            let t = sp.tb.mul_mod(x, p());
            assert!(t == N::from(1u64) || t == p() - N::from(1u64), "tB is not +-1/x");
        }
        eprintln!("greedyfrog model: {n} walks, {steps} steps, decode failures {bad}");
        assert_eq!(bad, 0);
    }
}
