//! frogdrop schedules: per-column classical envelopes of the lockstep traversal, from a sample of shots plus
//! margins (a graded shot outside an envelope fails; the margins buy that probability down).

pub type N = ruint::Uint<384, 6>;

pub fn p() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}

pub const L0: usize = 128;

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
                  qn: if first { bl(&r[j]) } else { bl(&r[j - 1]) }, xw: bl(&r[j - 1]) }
        } else if bl(&r[j]) <= l0 {
            // switch: Q t_{j-1} -> r_j (exchange), map t_{j-1} -> r_{j-1}, ring reversal, bottom <-> Q: ends with
            // bottom t_j, Q r_j, ring top r_{j-1}
            Rec { kind: Kind::Sw, sz: bl(&r[j]), sy: bl(&t[j]), mx: bl(&r[j]).max(bl(&t[j])),
                  swl: (bl(&r[j]).max(bl(&t[j - 1])), bl(&r[j]).max(bl(&t[j]))), fin: false,
                  qn: bl(&t[j - 1]).max(bl(&r[j])).max(bl(&t[j])), xw: bl(&t[j - 1]) }
        } else {
            let x_new = t[j + 1];
            Rec { kind: Kind::Hr, sz: bl(&r[j]), sy: bl(&t[j]), mx: bl(&x_new).max(bl(&t[j])), swl: (0, 0),
                  fin: false, qn: bl(&x_new), xw: bl(&x_new) }
        };
        recs.push(rec);
        match rec.kind {
            Kind::Hr => j += 1,
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
        Rec { kind: Kind::Idle, sz, sy, mx: self.br.max(1), swl: (0, 0), fin: false, qn: self.br, xw: self.br.max(1) }
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
}

impl ColEnv {
    fn empty() -> ColEnv {
        ColEnv { hr: false, ht: false, sw: false, dn: false, fin: false, sz: (999, 0), sy: (999, 0), smax: (999, 0),
                 swl: (0, 0), xw: 0 }
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
        if !inr(r.sz, e.sz) || !inr(r.sy, e.sy) || !inr(r.mx, e.smax) || r.swl.0 > e.swl.0 || r.swl.1 > e.swl.1
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
        s += &format!("C {} {} {} {} {} {} {} {} {} {} {} {} {} {}\n", e.hr as u8, e.ht as u8, e.sw as u8, e.dn as u8,
                      e.fin as u8, e.sz.0, e.sz.1, e.sy.0, e.sy.1, e.smax.0, e.smax.1, e.swl.0, e.swl.1, e.xw);
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
                                      xw: if v.len() > 13 { v[13] } else { v[10] } }),
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
    if s.recs.iter().any(|r| r.qn > nq) || s.br > nq {
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
    let mut cols: Vec<(u8, usize)> = vec![];
    for rec in &s.recs {
        match rec.kind {
            Kind::Hr => { cols.push((0, j)); j += 1; }
            Kind::Ht => { cols.push((1, j)); j += 1; }
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
    cols.push((1, nn - 1));
    for &(ph, j) in &cols {
        let q = r[j - 1] / r[j];
        let (z, x, y) = if ph == 0 { (r[j], t[j - 1], t[j]) } else { (t[j], r[j + 1], r[j]) };
        if j < nn - 1 {
            // the map's pair (X_new, Y)
            let (xn, yy) = if ph == 0 { (t[j + 1], t[j]) } else { (r[j + 1], r[j]) };
            if v2(&xn) > emax || v2(&yy) > emax { return Some("v2"); }
            let (zz, zn) = if ph == 0 { (r[j], r[j + 1]) } else { (t[j], t[j + 1]) };
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
    }
    if v2(&r[nn - 2]) > emax { return Some("v2"); }
    // done B0 shots must sit outside the H51 domain (bl(Z) >= 258 - 51)
    if t[nn - 2].bit_len() < 207 { return Some("h51dn"); }
    None
}
