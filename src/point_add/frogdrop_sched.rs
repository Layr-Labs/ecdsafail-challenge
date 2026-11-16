//! frogdrop schedules: per-column classical envelopes of the lockstep traversal, from a sample of shots plus
//! margins (a graded shot outside an envelope fails; the margins buy that probability down).

pub type N = ruint::Uint<384, 6>;

pub fn p() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}

pub const L0: usize = 128;

/// floor-form NICF in HR (FD_FUSEHR=1): a stepping HR column whose next RCF quotient is 1 (r_{j+1} > r_j / 2) takes
/// that step too and lands on level j + 2 (T = t_{j+1} + t_j, map Z <- (Z T - p)/Y, Q <- T - Q after the map).
pub fn fuse_hr() -> bool {
    static F: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *F.get_or_init(|| std::env::var("FD_FUSEHR").map_or(false, |v| v.trim() != "0"))
}

/// golden-erase window bits (FD_GW, default 20; FIT.md F7 sweep)
pub fn gw() -> usize {
    static W: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *W.get_or_init(|| std::env::var("FD_GW").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(20))
}

/// golden-erase iteration cap (FD_GL, default 14; FIT.md F7 sweep)
pub fn gl() -> usize {
    static W: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *W.get_or_init(|| std::env::var("FD_GL").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(14))
}

/// [x > g y] (g = (sqrt5 - 1)/2) on the top `w` bits of y with x shifted alike (exact when bl(y) <= w):
/// x/y > g  <=>  x^2 + x y > y^2.
pub fn golden_win(x: &N, y: &N, w: usize) -> bool {
    let sh = y.bit_len().saturating_sub(w);
    let (xs, ys) = (*x >> sh, *y >> sh);
    xs * xs + xs * ys > ys * ys
}

/// May this HR state fuse? bl(Z) >= L0 + 2 (the skipped level then stays HR: r_{j+1} > r_j / 2 >= 2^L0, so the
/// landing cofactor fits Q), and in column 0 (j = 1, unreflected x) only x < 2^255 (q_2 >= 2; with q_2 = 1 the
/// golden invariant fails and the fused walk is not injective). The golden erase is gated identically.
pub fn fuse_ok(z: &N, j: usize, col: usize) -> bool {
    fuse_hr() && col < fuse_cf() && bl(z) >= L0 + 2 && (j > 1 || bl(z) <= 255)
}

/// fusing columns: the prefix [0, FD_CF) (classical; every shot there has bl(Z) >= L0 + 2 or is a predicted
/// failure "fzlow"), so the golden erase needs no per-shot gate. Default: unlimited (per-shot bl rule only).
/// built-in fusing prefix (columns 0..33 of sched_frogdrop_fz.txt are all-HR)
pub const FUSE_CF: usize = 33;
pub fn fuse_cf() -> usize {
    static C: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *C.get_or_init(|| std::env::var("FD_CF").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(FUSE_CF))
}

/// The circuit's golden erase (nicf_hr::erase_golden): windows of bits [sy - GW, sy) of x and y (zeros below bit 0),
/// then up to GL steps (x, y) <- (y - x, x) while y/2 < x < y; result parity(steps) ^ [2x > y].
pub fn golden_iter(x: &N, y: &N) -> bool {
    let (gw, gl) = (gw(), gl());
    let sy = y.bit_len();
    let (mut a, mut c) = if sy >= gw { (*x >> (sy - gw), *y >> (sy - gw)) } else { (*x << (gw - sy), *y << (gw - sy)) };
    let mut k = 0usize;
    for _ in 0..gl {
        if a < c && a + a > c { let na = c - a; c = a; a = na; k += 1; } else { break; }
    }
    ((k & 1) == 1) ^ (a + a > c)
}

/// HR fuse decision from P's windows: u = rho - Xh + bq yd in [0, yd) (the windowed r_{j+1}/r_j), o = [2u > yd].
pub fn fuse_win(rho: &N, xh: &N, yd: &N, bq: bool) -> bool {
    let u = if bq { *rho + *yd - *xh } else { *rho - *xh };
    u + u > *yd
}

thread_local! {
    /// accumulated expected misreads of the lean payload e' decision (predict_n adds every fused event)
    pub static EP_ACC: std::cell::Cell<f64> = std::cell::Cell::new(0.0);
}

thread_local! {
    /// payload value d0 of the traversal being predicted (None: e' is only accumulated as an expectation in EP_ACC)
    pub static PL_D: std::cell::Cell<Option<N>> = std::cell::Cell::new(None);
}

/// The lean e' read of the circuit for the payload remainder d (< r_j): [d >> (sz - w) >= ceil(floor(u 2^w / yd) zd / 2^w)].
pub fn ep_lean(u: &N, yd: &N, z: &N, d: &N) -> bool {
    let w = super::nicf_hr::LW;
    let sz = bl(z);
    let one = N::from(1u64);
    let zd = (*z >> (sz - w)) | one;
    let q1 = (*u << w) / *yd;
    let prod = q1 * zd;
    let mut ds = prod >> w;
    if (ds << w) != prod { ds += one; }
    (*d >> (sz - w)) >= ds
}

/// Misread probability of the lean e' decision (nicf_hr::decide) of one fused event, d uniform on [0, r_j): the
/// lockstep bits are the binary digits of the two quotients, so e' = [floor(dw 2^w / zd) >= Q1], Q1 = floor(u 2^w / yd),
/// i.e. [dw >= D*], D* = ceil(Q1 zd / 2^w) (a tie reads 1); the exact e' is [d >= r_{j+1}].
pub fn ep_lean_prob(u: &N, yd: &N, z: &N, zn: &N) -> f64 {
    let w = super::nicf_hr::LW;
    let sz = bl(z);
    let one = N::from(1u64);
    let zd = (*z >> (sz - w)) | one;
    let q1 = (*u << w) / *yd;
    let prod = q1 * zd;
    let mut ds = prod >> w;
    if (ds << w) != prod { ds += one; }
    let a = ds << (sz - w);
    let diff = if a > *zn { a - *zn } else { *zn - a };
    let sh = sz.saturating_sub(60);
    (diff >> sh).as_limbs()[0] as f64 / (*z >> sh).as_limbs()[0] as f64
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Kind { Hr, Ht, Sw, Idle }

/// One shot's record for one column.
#[derive(Clone, Copy, Debug)]
pub struct Rec {
    pub kind: Kind,
    /// bl(bottom), bl(top) at column start; max(bl X_new, bl Y) (the map's pair)
    pub sz: usize,
    pub sy: usize,
    pub mx: usize,
    /// switch cswap lane needs (pre, post)
    pub swl: (usize, usize),
    /// reaches r = 1 at column end
    pub fin: bool,
    /// largest value held in Q during the column
    pub qn: usize,
    /// largest ring-top (middle target) value bits: max(bl X, bl X_new)
    pub xw: usize,
    /// floor-form NICF: this HR column fuses the next (q = 1) RCF step
    pub fz: bool,
}

/// A shot's traversal: its stepping records (columns 0 .. N-2) and the idle data (A0 / B0 sizes).
pub struct Shot {
    pub recs: Vec<Rec>,
    /// bl(t_{N-1}), bl(t_{N-2}), bl(R = r_{N-2})
    pub bt1: usize,
    pub bt2: usize,
    pub br: usize,
}

fn bl(x: &N) -> usize {
    x.bit_len()
}

/// x' = the traversal input (1 <= x' < 2^255).
pub fn shot(xr: N, l0: usize) -> Shot {
    let pp = p();
    let (mut r, mut t) = (vec![pp, xr], vec![N::ZERO, N::from(1u64)]);
    while !r[r.len() - 1].is_zero() {
        let n = r.len();
        let q = r[n - 2] / r[n - 1];
        let rn = r[n - 2] - q * r[n - 1];
        let tn = t[n - 2] + q * t[n - 1];
        r.push(rn);
        t.push(tn);
    }
    let nn = r.len() - 1; // r[nn] = 0, r[nn - 1] = 1
    let mut recs = vec![];
    let (mut ph, mut j) = (0u8, 1usize);
    while !(ph == 1 && j == nn - 1) {
        let rec = if ph == 1 {
            let x_new = r[j + 1];
            // a shot's first HT column starts in the switched layout: Q = Y = r_j, ring top = X = r_{j-1}
            let first = recs.last().map_or(false, |p: &Rec| p.kind == Kind::Sw);
            Rec { kind: Kind::Ht, sz: bl(&t[j]), sy: if first { bl(&r[j - 1]) } else { bl(&r[j]) },
                  mx: bl(&x_new).max(bl(&r[j])), swl: (0, 0), fin: j + 1 == nn - 1,
                  qn: if first { bl(&r[j]) } else { bl(&r[j - 1]) }, xw: bl(&r[j - 1]), fz: false }
        } else if bl(&r[j]) <= l0 {
            // switch: Q t_{j-1} -> r_j (exchange), map t_{j-1} -> r_{j-1}, ring reversal, bottom <-> Q: ends with
            // bottom t_j, Q r_j, ring top r_{j-1}
            Rec { kind: Kind::Sw, sz: bl(&r[j]), sy: bl(&t[j]), mx: bl(&r[j]).max(bl(&t[j])),
                  swl: (bl(&r[j]).max(bl(&t[j - 1])), bl(&r[j]).max(bl(&t[j]))), fin: false,
                  qn: bl(&t[j - 1]).max(bl(&r[j])).max(bl(&t[j])), xw: bl(&t[j - 1]), fz: false }
        } else {
            // floor-form NICF: fuse when the next RCF quotient is 1 (never reaches r = 0: r_{j+2} = r_j - r_{j+1} > 0)
            let fz = fuse_ok(&r[j], j, recs.len()) && j + 2 < nn && r[j + 1] + r[j + 1] > r[j];
            let x_new = if fz { t[j + 2] } else { t[j + 1] };
            Rec { kind: Kind::Hr, sz: bl(&r[j]), sy: bl(&t[j]), mx: bl(&x_new).max(bl(&t[j])), swl: (0, 0),
                  fin: false, qn: bl(&x_new), xw: bl(&x_new), fz }
        };
        recs.push(rec);
        match rec.kind {
            Kind::Hr => j += 1 + rec.fz as usize,
            Kind::Ht => j += 1,
            Kind::Sw => ph = 1,
            Kind::Idle => unreachable!(),
        }
    }
    Shot { recs, bt1: bl(&t[nn - 1]), bt2: bl(&t[nn - 2]), br: bl(&r[nn - 2]) }
}

impl Shot {
    /// record at column c (idle past the end: A0 on even idle counts, B0 on odd)
    pub fn rec(&self, c: usize) -> Rec {
        if c < self.recs.len() {
            return self.recs[c];
        }
        let a0 = (c - self.recs.len()) % 2 == 0;
        let (sz, sy) = if a0 { (self.bt1, 1) } else { (self.bt2, self.br) };
        Rec { kind: Kind::Idle, sz, sy, mx: self.br.max(1), swl: (0, 0), fin: false, qn: self.br, xw: self.br.max(1), fz: false }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ColEnv {
    pub hr: bool,
    pub ht: bool,
    pub sw: bool,
    pub dn: bool,
    pub fin: bool,
    pub sz: (usize, usize),
    pub sy: (usize, usize),
    pub smax: (usize, usize),
    pub swl: (usize, usize),
    /// largest ring-top value bits in the middle
    pub xw: usize,
    /// some HR shot may fuse (floor-form NICF)
    pub fz: bool,
}

impl ColEnv {
    fn empty() -> ColEnv {
        ColEnv { hr: false, ht: false, sw: false, dn: false, fin: false, sz: (999, 0), sy: (999, 0), smax: (999, 0),
                 swl: (0, 0), xw: 0, fz: false }
    }
}

pub struct Sched {
    pub cols: Vec<ColEnv>,
    /// smax envelope of the end map (B0 shots), last-column sz envelope
    pub b0: (usize, usize),
    pub lsz: (usize, usize),
}

fn grow(r: &mut (usize, usize), v: usize) {
    r.0 = r.0.min(v);
    r.1 = r.1.max(v);
}

/// Envelopes over `shots` with margins: size ranges united over the columns within `dw` and widened by `ds` bits,
/// `dc` columns on every kind window, `dcols` extra columns at the end.
pub fn envelope(shots: &[Shot], ds: usize, dc: usize, dcols: usize, dw: usize) -> Sched {
    let ncol = shots.iter().map(|s| s.recs.len()).max().unwrap() + dcols;
    let mut cols = vec![ColEnv::empty(); ncol];
    // kind windows (first, last column seen)
    let mut win = [(usize::MAX, 0usize); 5]; // hr ht sw dn fin
    // raw envelopes per kind per column
    let mut kenv = vec![vec![ColEnv::empty(); ncol]; 4];
    for s in shots {
        for c in 0..ncol {
            let r = s.rec(c);
            let k = match r.kind { Kind::Hr => 0, Kind::Ht => 1, Kind::Sw => 2, Kind::Idle => 3 };
            let e = &mut kenv[k][c];
            grow(&mut e.sz, r.sz);
            grow(&mut e.sy, r.sy);
            grow(&mut e.smax, r.mx);
            e.swl.0 = e.swl.0.max(r.swl.0);
            e.swl.1 = e.swl.1.max(r.swl.1);
            e.xw = e.xw.max(r.xw);
            e.fz |= r.fz;
            win[k] = (win[k].0.min(c), win[k].1.max(c));
            if r.fin {
                win[4] = (win[4].0.min(c), win[4].1.max(c));
            }
        }
    }
    let inw = |k: usize, c: usize, open_end: bool| {
        let (a, b) = win[k];
        a != usize::MAX && c + dc >= a && (open_end || c <= b + dc)
    };
    for (c, e) in cols.iter_mut().enumerate() {
        e.hr = inw(0, c, false);
        e.ht = inw(1, c, true);
        e.sw = inw(2, c, false);
        e.dn = inw(3, c, true);
        e.fin = inw(4, c, true);
        let en = [e.hr, e.ht, e.sw, e.dn];
        for k in 0..4 {
            if !en[k] {
                continue;
            }
            // columns [c - dw, c + dw] clamped into the kind's observed window
            let (a, b) = win[k];
            let lo = c.saturating_sub(dw).max(a).min(b.saturating_sub(dw));
            let hi = (c + dw).min(b).max(a + dw.min(b - a));
            for d in lo..=hi {
                let o = &kenv[k][d];
                if o.sz.1 > 0 {
                    grow(&mut e.sz, o.sz.0); grow(&mut e.sz, o.sz.1);
                    grow(&mut e.sy, o.sy.0); grow(&mut e.sy, o.sy.1);
                    grow(&mut e.smax, o.smax.0); grow(&mut e.smax, o.smax.1);
                    e.swl.0 = e.swl.0.max(o.swl.0);
                    e.swl.1 = e.swl.1.max(o.swl.1);
                    e.xw = e.xw.max(o.xw);
                    e.fz |= o.fz;
                }
            }
        }
        e.sz = (e.sz.0.saturating_sub(ds).max(1), e.sz.1 + ds);
        e.sy = (e.sy.0.saturating_sub(ds).max(1), e.sy.1 + ds);
        e.smax = (e.smax.0.saturating_sub(ds).max(1), e.smax.1 + ds);
        e.xw += ds;
        if e.sw {
            e.swl = (e.swl.0.max(L0) + ds, e.swl.1 + ds);
        }
    }
    let mut b0 = (999, 0);
    let mut lsz = (999, 0);
    for s in shots {
        let r = s.rec(ncol);
        if r.sy != 1 {
            grow(&mut b0, r.mx);
        }
        grow(&mut lsz, s.bt1);
    }
    let b0 = (b0.0.saturating_sub(ds).max(1), b0.1 + ds);
    let lsz = (lsz.0.saturating_sub(ds).max(1), lsz.1 + ds);
    Sched { cols, b0, lsz }
}

/// Does a shot fit the schedule? (None = yes; else the first violation)
pub fn check(s: &Shot, sc: &Sched) -> Option<String> {
    let ncol = sc.cols.len();
    if s.recs.len() > ncol {
        return Some(format!("too long: {} columns", s.recs.len()));
    }
    for c in 0..ncol {
        let r = s.rec(c);
        let e = &sc.cols[c];
        let kind_ok = match r.kind { Kind::Hr => e.hr, Kind::Ht => e.ht, Kind::Sw => e.sw, Kind::Idle => e.dn };
        let inr = |v: usize, rg: (usize, usize)| v >= rg.0 && v <= rg.1;
        if !kind_ok || (r.fin && !e.fin) {
            return Some(format!("col {c}: kind {:?} fin {} not enabled", r.kind, r.fin));
        }
        // the machine's sz holds 255 after column 0 (the column parameters cap the envelope there)
        let esz = if c == 0 { e.sz } else { (e.sz.0, e.sz.1.min(255)) };
        if !inr(r.sz, esz) || !inr(r.sy, e.sy) || !inr(r.mx, e.smax) || r.swl.0 > e.swl.0 || r.swl.1 > e.swl.1
            || r.xw > e.xw {
            return Some(format!("col {c}: {:?} outside {:?}", r, e));
        }
    }
    let r = s.rec(ncol);
    if r.sy != 1 && !(r.mx >= sc.b0.0 && r.mx <= sc.b0.1) {
        return Some("end map".into());
    }
    if !(s.bt1 >= sc.lsz.0 && s.bt1 <= sc.lsz.1) {
        return Some("last column".into());
    }
    None
}

/// Random traversal inputs x' = dx, uniform in [1, p) (frogdrop runs Euclid on dx unreflected).
pub fn sample(n: usize, seed: u64) -> Vec<N> {
    let pp = p();
    let mut s = seed ^ 0x9E3779B97F4A7C15;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let mut out = vec![];
    while out.len() < n {
        let mut v = N::ZERO;
        for i in 0..4 {
            v |= N::from(next()) << (64 * i);
        }
        if v.is_zero() || v >= pp {
            continue;
        }
        out.push(v);
    }
    out
}

pub fn to_text(sc: &Sched) -> String {
    let mut s = String::new();
    for e in &sc.cols {
        let fz = if e.fz { " 1" } else { "" };
        s += &format!("C {} {} {} {} {} {} {} {} {} {} {} {} {} {}{}
", e.hr as u8, e.ht as u8, e.sw as u8, e.dn as u8,
                      e.fin as u8, e.sz.0, e.sz.1, e.sy.0, e.sy.1, e.smax.0, e.smax.1, e.swl.0, e.swl.1, e.xw, fz);
    }
    s += &format!("B {} {}\nL {} {}\n", sc.b0.0, sc.b0.1, sc.lsz.0, sc.lsz.1);
    s
}

pub fn from_text(t: &str) -> Sched {
    let mut cols = vec![];
    let (mut b0, mut lsz) = ((0, 0), (0, 0));
    for line in t.lines() {
        let w: Vec<&str> = line.split_whitespace().collect();
        if w.is_empty() {
            continue;
        }
        let v: Vec<usize> = w[1..].iter().map(|x| x.parse().unwrap()).collect();
        match w[0] {
            "C" => cols.push(ColEnv { hr: v[0] == 1, ht: v[1] == 1, sw: v[2] == 1, dn: v[3] == 1, fin: v[4] == 1,
                                      sz: (v[5], v[6]), sy: (v[7], v[8]), smax: (v[9], v[10]), swl: (v[11], v[12]),
                                      xw: if v.len() > 13 { v[13] } else { v[10] }, fz: v.len() > 14 && v[14] == 1 }),
            "B" => b0 = (v[0], v[1]),
            "L" => lsz = (v[0], v[1]),
            _ => panic!("bad schedule line {line}"),
        }
    }
    Sched { cols, b0, lsz }
}

fn v2(x: &N) -> usize {
    if x.is_zero() { 999 } else { x.trailing_zeros() }
}

/// Classical failure predicate of one traversal input x' (< 2^255) for the built machine: None = every classical
/// assumption of the circuit holds (schedule envelopes, Q capacity, windowed estimate exact with q0 < 2^qb and
/// e <= tot, map operand v2 <= emax). Carry-tail truncations (~2^-40) are not modelled.
pub fn predict(xr: N, sc: &Sched, k: usize, kp: usize, qb: usize, tot: usize, nq: usize, emax: usize)
               -> Option<&'static str> {
    predict_n(xr, sc, k, kp, qb, tot, nq, emax, 288)
}

/// Map region test: Z <- (p - Z X)/Y in place on [0, cut), cut = n - max(bl X, bl Y), needs Z 2^v2(X) and
/// Z' 2^v2(Y) to fit the region.
fn map_fits(z: &N, x: &N, y: &N, zn: &N, n: usize) -> bool {
    let cut = n as isize - x.bit_len().max(y.bit_len()) as isize;
    let need = (z.bit_len() + v2(x)).max(zn.bit_len() + v2(y)) as isize;
    need <= cut
}

pub fn predict_n(xr: N, sc: &Sched, k: usize, kp: usize, qb: usize, tot: usize, nq: usize, emax: usize, nring: usize)
                 -> Option<&'static str> {
    let s = shot(xr, L0);
    if check(&s, sc).is_some() {
        return Some("envelope");
    }
    if s.recs.iter().any(|r| r.qn > nq + r.fz as usize) || s.br > nq {
        return Some("qneed");
    }
    let pp = p();
    let one = N::from(1u64);
    let (mut r, mut t) = (vec![pp, xr], vec![N::ZERO, one]);
    while !r[r.len() - 1].is_zero() {
        let n = r.len();
        let q = r[n - 2] / r[n - 1];
        let rn = r[n - 2] - q * r[n - 1];
        let tn = t[n - 2] + q * t[n - 1];
        r.push(rn);
        t.push(tn);
    }
    let nn = r.len() - 1;
    // decisions: every stepping column + the final no-map middle (Z = t_{N-1}, X = r_N = 0, Y = 1)
    let (mut ph, mut j) = (0u8, 1usize);
    let mut cols: Vec<(u8, usize, bool, usize)> = vec![];
    for (ci, rec) in s.recs.iter().enumerate() {
        if fuse_hr() && ci < fuse_cf() && fuse_cf() != usize::MAX && rec.kind == Kind::Hr && rec.sz < L0 + 2 {
            return Some("fzlow");
        }
        match rec.kind {
            Kind::Hr => { cols.push((0, j, rec.fz, ci)); j += 1 + rec.fz as usize; }
            Kind::Ht => { cols.push((1, j, false, ci)); j += 1; }
            Kind::Sw => {
                if v2(&r[j]) > emax || v2(&t[j]) > emax { return Some("v2"); }

                // switch map: Z = t_{j-1}, X = r_j, Y = t_j -> r_{j-1}
                if !map_fits(&t[j - 1], &r[j], &t[j], &r[j - 1], nring) { return Some("swmap"); }
                ph = 1;
            }
            Kind::Idle => {}
        }
    }
    let _ = ph;
    cols.push((1, nn - 1, false, usize::MAX));
    let mut dpl = PL_D.with(|c| c.get());
    for &(ph, j, fz, ci) in &cols {
        let q = r[j - 1] / r[j];
        // payload digit of an HR level: d <- d mod r_j
        if ph == 0 { if let Some(d) = dpl.as_mut() { *d = *d % r[j]; } }
        let (z, x, y) = if ph == 0 { (r[j], t[j - 1], t[j]) } else { (t[j], r[j + 1], r[j]) };
        if j < nn - 1 {
            // the map's pair (X_new, Y)
            let jn = j + 1 + fz as usize;
            let (xn, yy) = if ph == 0 { (t[jn], t[j]) } else { (r[j + 1], r[j]) };
            if v2(&xn) > emax || v2(&yy) > emax { return Some("v2"); }
            let (zz, zn) = if ph == 0 { (r[j], r[jn]) } else { (t[j], t[j + 1]) };
            if !map_fits(&zz, &xn, &yy, &zn, nring) { return Some("map"); }
        }
        let (sz, sy) = (z.bit_len(), y.bit_len());
        let zh = (z >> (sz - k)) | one;
        let (yh, xh) = if sy >= kp { (y >> (sy - kp), x >> (sy - kp)) } else { (y << (kp - sy), x << (kp - sy)) };
        let e = 256 + k + kp - sz - sy;
        if e > tot { return Some("e"); }
        let fh = ((one << e) - one) / zh;
        // subset-storage P divides by the virtual-odd Yd = Yh | 1
        let yd = if super::frogdrop_col::qsub() > 0 { yh | one } else { yh };
        let (q0, rho) = (fh / yd, fh % yd);
        if q0 >= (one << qb) { return Some("q0"); }
        let b = if rho < xh { one } else { N::ZERO };
        if q0 - b != q { return Some("estimate"); }
        if ph == 0 && fuse_ok(&z, j, ci) {
            if fuse_win(&rho, &xh, &yd, b == one) != fz { return Some("fuse"); }
            if fz {
                let u = if b == one { rho + yd - xh } else { rho - xh };
                if let Some(d) = dpl.as_mut() {
                    let exact = *d >= r[j + 1];
                    if ep_lean(&u, &yd, &z, d) != exact { return Some("eprime"); }
                    if exact { *d = *d - r[j + 1]; }
                } else {
                    let pm = ep_lean_prob(&u, &yd, &z, &r[j + 1]);
                    EP_ACC.with(|c| c.set(c.get() + pm));
                }
            }
            let m = j + 1 + fz as usize;
            // column 0: exact [Q >= 2] (post Q = t_1 = 1 unless fused); later: the golden read-back
            let rd = if j == 1 { t[m - 1] >= N::from(2u64) } else { golden_iter(&t[m - 1], &t[m]) };
            if rd != fz { return Some("golden"); }
        }
    }
    if v2(&r[nn - 2]) > emax { return Some("v2"); }
    // done B0 shots must sit outside the H51 domain (bl(Z) >= 258 - 51)
    if t[nn - 2].bit_len() < 207 { return Some("h51dn"); }
    None
}
