//! frogdrop schedules: per-column classical envelopes of the lockstep traversal, from a sample of shots plus
//! margins (a graded shot outside an envelope fails; the margins buy that probability down).

pub type N = ruint::Uint<384, 6>;

pub fn p() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}

pub const L0: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Kind { Hr, Ht, Sw, Idle, Dl, Dq }

/// The crossing form choice (arch700). At its first HR state with bl(r_j) <= l0 a shot switches only if
/// bl(r_j) <= bl(t_j); otherwise ("delayed", Dl) it steps HR (q_j) in that column, whose switch map takes it
/// t_{j+1} -> r_{j+1} (mult r_j, div t_j) and whose switch tail leaves (bottom t_j, Q r_j, top r_{j+1}); the next
/// column (Dq) does not step: it skips the stage-2 swap and its map takes t_j -> t_{j+1} (mult r_{j+1}, div r_j),
/// landing in HT j+1.
pub const FORM_CHOICE: bool = true;

pub fn dl_enabled() -> bool {
    FORM_CHOICE
}

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
    /// Dq: bl(Q) = bl(r_j), the column's sy after the stage-2 refill; Dl: bl(r_j); 0 otherwise
    pub mx2: usize,
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
    let mut dq = false;
    while !(ph == 1 && j == nn - 1) {
        let rec = if dq {
            // after a delayed switch: (bottom t_j, Q r_j, top r_{j+1}) skips the stage-2 swap, takes no step and
            // maps t_j -> t_{j+1}
            Rec { kind: Kind::Dq, sz: bl(&t[j]), sy: bl(&r[j + 1]), mx: bl(&r[j + 1]).max(bl(&r[j])), swl: (0, 0),
                  fin: j + 1 == nn - 1, qn: bl(&r[j]).max(bl(&r[j + 1])), xw: bl(&r[j + 1]), mx2: bl(&r[j]) }
        } else if ph == 1 {
            let x_new = r[j + 1];
            // a shot's first HT column starts in the switched layout: Q = Y = r_j, ring top = X = r_{j-1}
            let first = recs.last().map_or(false, |p: &Rec| p.kind == Kind::Sw);
            Rec { kind: Kind::Ht, sz: bl(&t[j]), sy: if first { bl(&r[j - 1]) } else { bl(&r[j]) },
                  mx: bl(&x_new).max(bl(&r[j])), swl: (0, 0), fin: j + 1 == nn - 1,
                  qn: if first { bl(&r[j]) } else { bl(&r[j - 1]) }, xw: bl(&r[j - 1]), mx2: 0 }
        } else if bl(&r[j]) <= l0 && dl_enabled() && bl(&r[j]) > bl(&t[j]) {
            // delayed switch: HR step j (X t_{j-1} -> t_{j+1} in the ring top); stage 9 leaves t_{j+1}'s low 128 bits
            // in Q, its top bits above r_j; stage 10 -> (bottom t_{j+1}, Q r_j, top t_j); switch map -> r_{j+1}; tail
            let tl = bl(&t[j + 1]).min(128);
            Rec { kind: Kind::Dl, sz: bl(&r[j]), sy: bl(&t[j]), mx: bl(&r[j]).max(bl(&t[j])),
                  swl: (bl(&r[j]).max(tl), bl(&r[j]).max(bl(&t[j]))), fin: false,
                  qn: bl(&t[j - 1]).max(bl(&r[j])).max(bl(&t[j])).max(tl), xw: bl(&t[j + 1]), mx2: bl(&r[j]) }
        } else if bl(&r[j]) <= l0 {
            // switch: Q t_{j-1} -> r_j (exchange), map t_{j-1} -> r_{j-1}, ring reversal, bottom <-> Q: ends with
            // bottom t_j, Q r_j, ring top r_{j-1}
            Rec { kind: Kind::Sw, sz: bl(&r[j]), sy: bl(&t[j]), mx: bl(&r[j]).max(bl(&t[j])),
                  swl: (bl(&r[j]).max(bl(&t[j - 1])), bl(&r[j]).max(bl(&t[j]))), fin: false,
                  qn: bl(&t[j - 1]).max(bl(&r[j])).max(bl(&t[j])), xw: bl(&t[j - 1]), mx2: 0 }
        } else {
            let x_new = t[j + 1];
            Rec { kind: Kind::Hr, sz: bl(&r[j]), sy: bl(&t[j]), mx: bl(&x_new).max(bl(&t[j])), swl: (0, 0),
                  fin: false, qn: bl(&x_new), xw: bl(&x_new), mx2: 0 }
        };
        recs.push(rec);
        match rec.kind {
            Kind::Hr => j += 1,
            Kind::Ht => j += 1,
            Kind::Sw => ph = 1,
            Kind::Dl => { ph = 1; dq = true; }
            Kind::Dq => { j += 1; dq = false; }
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
        Rec { kind: Kind::Idle, sz, sy, mx: self.br.max(1), swl: (0, 0), fin: false, qn: self.br, xw: self.br.max(1),
              mx2: 0 }
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
    /// some shot takes the delayed switch (Dl) here, with bl(r_j) >= dlr; some shot is in its no-step column after
    /// one (Dq) here
    pub dl: bool,
    pub dq: bool,
    pub dlr: usize,
}

impl ColEnv {
    fn empty() -> ColEnv {
        ColEnv { hr: false, ht: false, sw: false, dn: false, fin: false, sz: (999, 0), sy: (999, 0), smax: (999, 0),
                 swl: (0, 0), xw: 0, dl: false, dq: false, dlr: 999 }
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
    let mut win = [(usize::MAX, 0usize); 7]; // hr ht sw dn fin dl dq
    // raw envelopes per kind per column
    let mut kenv = vec![vec![ColEnv::empty(); ncol]; 6];
    for s in shots {
        for c in 0..ncol {
            let r = s.rec(c);
            let k = match r.kind { Kind::Hr => 0, Kind::Ht => 1, Kind::Sw => 2, Kind::Idle => 3, Kind::Dl => 4,
                                   Kind::Dq => 5 };
            let e = &mut kenv[k][c];
            grow(&mut e.sz, r.sz);
            grow(&mut e.sy, r.sy);
            grow(&mut e.smax, r.mx);
            e.swl.0 = e.swl.0.max(r.swl.0);
            e.swl.1 = e.swl.1.max(r.swl.1);
            e.xw = e.xw.max(r.xw);
            if r.kind == Kind::Dq { grow(&mut e.sy, r.mx2); }
            if r.kind == Kind::Dl { e.dlr = e.dlr.min(r.mx2); }
            let wk = if k >= 4 { k + 1 } else { k };
            win[wk] = (win[wk].0.min(c), win[wk].1.max(c));
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
        // a delayed shot steps HR and is a switch candidate in its column; the next column holds it as a ph shot
        e.dl = inw(5, c, false);
        e.dq = inw(6, c, false);
        e.hr |= e.dl;
        e.sw |= e.dl;
        e.ht |= e.dq;
        let en = [inw(0, c, false), e.ht, inw(2, c, false), e.dn, e.dl, e.dq];
        for k in 0..6 {
            if !en[k] {
                continue;
            }
            // columns [c - dw, c + dw] clamped into the kind's observed window
            let (a, b) = win[if k >= 4 { k + 1 } else { k }];
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
                    if k == 4 { e.dlr = e.dlr.min(o.dlr); }
                }
            }
        }
        e.sz = (e.sz.0.saturating_sub(ds).max(1), e.sz.1 + ds);
        e.sy = (e.sy.0.saturating_sub(ds).max(1), e.sy.1 + ds);
        e.smax = (e.smax.0.saturating_sub(ds).max(1), e.smax.1 + ds);
        e.xw += ds;
        if e.dl { e.dlr = e.dlr.saturating_sub(ds).max(1); }
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
        let kind_ok = match r.kind { Kind::Hr => e.hr, Kind::Ht => e.ht, Kind::Sw => e.sw, Kind::Idle => e.dn,
                                     Kind::Dl => e.dl, Kind::Dq => e.dq };
        let inr = |v: usize, rg: (usize, usize)| v >= rg.0 && v <= rg.1;
        if !kind_ok || (r.fin && !e.fin) {
            return Some(format!("col {c}: kind {:?} fin {} not enabled", r.kind, r.fin));
        }
        // the machine's sz holds 255 after column 0 (the column parameters cap the envelope there)
        let esz = if c == 0 { e.sz } else { (e.sz.0, e.sz.1.min(255)) };
        if !inr(r.sz, esz) || !inr(r.sy, e.sy) || !inr(r.mx, e.smax) || r.swl.0 > e.swl.0 || r.swl.1 > e.swl.1
            || r.xw > e.xw || (r.kind == Kind::Dq && !inr(r.mx2, e.sy)) || (r.kind == Kind::Dl && r.mx2 < e.dlr) {
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
        s += &format!("C {} {} {} {} {} {} {} {} {} {} {} {} {} {}", e.hr as u8, e.ht as u8, e.sw as u8, e.dn as u8,
                      e.fin as u8, e.sz.0, e.sz.1, e.sy.0, e.sy.1, e.smax.0, e.smax.1, e.swl.0, e.swl.1, e.xw);
        if e.dl || e.dq { s += &format!(" {} {} {}", e.dl as u8, e.dq as u8, if e.dl { e.dlr } else { 0 }); }
        s += "\n";
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
                                      xw: if v.len() > 13 { v[13] } else { v[10] },
                                      dl: v.len() > 16 && v[14] == 1, dq: v.len() > 16 && v[15] == 1,
                                      dlr: if v.len() > 16 && v[14] == 1 { v[16] } else { 999 } }),
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
    // the machine's ring (switch columns extend their map by 2 nq + emax - n lanes); FD_PRED_K / FD_PRED_DN: model a
    // smaller K (with the ring one lane shorter per bit)
    let kk: usize = std::env::var("FD_PRED_K").ok().and_then(|v| v.parse().ok()).unwrap_or(k);
    predict_n(xr, sc, kk, kp, qb, tot, nq, emax, super::pointadd_frogdrop::N + kk - k)
}

/// Map region test: Z <- (p - Z X)/Y in place on [0, cut), cut = n - max(bl X, bl Y), needs Z 2^v2(X) and
/// Z' 2^v2(Y) to fit the region.
fn map_fits(z: &N, x: &N, y: &N, zn: &N, n: usize) -> bool {
    let cut = n as isize - x.bit_len().max(y.bit_len()) as isize;
    // agent_lowq_quot QUOT_MAP_TZ: the 2^e room is the even operand's own zero suffix, no extension
    let tz = super::frogdrop_col::map_tz();
    let need = if tz { z.bit_len().max(zn.bit_len()) } else { (z.bit_len() + v2(x)).max(zn.bit_len() + v2(y)) } as isize;
    need <= cut
}

pub fn predict_n(xr: N, sc: &Sched, k: usize, kp: usize, qb: usize, tot: usize, nq: usize, emax: usize, nring: usize)
                 -> Option<&'static str> {
    let room = if super::frogdrop_col::map_tz() { 0 } else { emax };
    predict_n_geometry(xr, sc, k, kp, qb, tot, nq, emax, nring,
                       super::midg::park_reserve(), (257 + room).saturating_sub(nring))
}

/// Explicit stream geometry for paired censuses. The frozen 699 builder has
/// no ordinary-map extension and a nine-lane crossing reserve.
pub fn predict_n_geometry(xr: N, sc: &Sched, k: usize, kp: usize, qb: usize, tot: usize,
                          nq: usize, emax: usize, nring: usize, reserve: usize,
                          ordinary_extra: usize) -> Option<&'static str> {
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
    // map lanes in column c: the ring, plus the extension of a switch column
    let ext = (2 * nq + if super::frogdrop_col::map_tz() { 0 } else { emax }).saturating_sub(nring);
    let ring_at = |c: usize| nring + if c < sc.cols.len() && sc.cols[c].sw { ext } else { ordinary_extra };
    let mut cols: Vec<(u8, usize, usize)> = vec![];
    for (c, rec) in s.recs.iter().enumerate() {
        match rec.kind {
            Kind::Hr => { cols.push((0, j, c)); j += 1; }
            Kind::Ht => { cols.push((1, j, c)); j += 1; }
            Kind::Sw => {
                if v2(&r[j]) > emax || v2(&t[j]) > emax { return Some("v2"); }

                // switch map: Z = t_{j-1}, X = r_j, Y = t_j -> r_{j-1}
                if !map_fits(&t[j - 1], &r[j], &t[j], &r[j - 1], ring_at(c)) { return Some("swmap"); }
                // agent_lowq_lane QUOT_PRED_SWCHK: the switch tail (stage 14) reverses the ring with a fixed bottom of
                // l0 lanes and probes the new top X = r_{j-1} in the reversed ring's first n - l0 lanes
                // (QUOT_PRED_SWCHK=exact: a cut at the bottom's own size, bl(r_j) + bl(r_{j-1}) <= n)
                let swlim = if std::env::var("QUOT_PRED_SWCHK").as_deref() == Ok("exact") { nring - r[j].bit_len() }
                            else { nring - L0 };
                if std::env::var_os("QUOT_PRED_SWCHK").is_some() && r[j - 1].bit_len() > swlim {
                    return Some("swtop");
                }
                ph = 1;
            }
            Kind::Dl => {
                // delayed switch: HR step j, then the column's switch map Z = t_{j+1}, X = r_j, Y = t_j -> r_{j+1}
                cols.push((2, j, c));
                if v2(&r[j]) > emax || v2(&t[j]) > emax { return Some("v2"); }
                if !map_fits(&t[j + 1], &r[j], &t[j], &r[j + 1], ring_at(c)) { return Some("dlmap1"); }
                // agent_lowq_quot QUOT_PRED_DLCHK: the stage-9 delayed move (lanes n - 1 - l <-> l, l < n / 2) places
                // X_new = t_{j+1}'s bits l0.. only up to bit n - 1 - l0 (QUOT_PRED_DLCHK=half: the old n / 2 probe)
                // (agent_lowq_lane QUOT_PRED_DLCHK=exact: the move's split at bl(r_j) and a cut at the top's t_j:
                // t_{j+1}'s high bits need bl(t_{j+1}) + bl(t_j) <= n and bl(t_{j+1}) + bl(r_j) <= n)
                let dlhalf_lim = match std::env::var("QUOT_PRED_DLCHK").as_deref() {
                    Ok("half") => nring / 2,
                    Ok("exact") => nring - t[j].bit_len().max(r[j].bit_len()),
                    _ => nring - L0,
                };
                if std::env::var_os("QUOT_PRED_DLCHK").is_some() && t[j + 1].bit_len() > dlhalf_lim {
                    return Some("dlhalf");
                }
                ph = 1;
            }
            Kind::Dq => {
                // no step; the column's map Z = t_j, X = r_{j+1}, Y = r_j -> t_{j+1}
                if v2(&r[j + 1]) > emax || v2(&r[j]) > emax { return Some("v2"); }
                if !map_fits(&t[j], &r[j + 1], &r[j], &t[j + 1], ring_at(c)) { return Some("dlmap2"); }
                j += 1;
            }
            Kind::Idle => {}
        }
    }
    let _ = ph;
    cols.push((1, nn - 1, usize::MAX));
    // Scheme G (midg): the crossing step parks q above Y in a cycle of Q + 1 + D lanes
    let gm = super::midg::enabled() && std::env::var("FD_PRED_RHO").is_err();
    if gm {
        let d = reserve as isize;
        for j in 1..nn {
            if r[j].bit_len() <= L0 && r[j - 1].bit_len() > L0 {
                let q = r[j - 1] / r[j];
                // the crossing step parks above Y: Y = r_j in HT form, Y = t_j in the delayed (HR) form
                let hr_form = dl_enabled() && r[j].bit_len() > t[j].bit_len();
                let ybl = if hr_form { t[j].bit_len() } else { r[j].bit_len() };
                // agent_lowq_quot: chunked sessions park one chunk at a time at chunk-relative indices (the HT form
                // also parks all of q for the old stage-5 payload unless G_IP5)
                let qbl = q.bit_len() as isize;
                let qc = super::midg::qch() as isize;
                let chunk_park = super::midg::chunked()
                    && (hr_form || super::midg::G_IP5 || std::env::var_os("QUOT_PRED_CHUNKPARK").is_some());
                let mut need = if chunk_park { qbl.min(qc).max(qbl - qc) } else { qbl };
                // agent_lowq_quot QUOT_CUTS_WIDE=a,b: the chunk cuts of a crossing parked in a wide column
                // (QUOT_CUTS_NARROW: in a narrow one)
                let c = cols.iter().find(|e| e.1 == j).map(|e| e.2);
                let wide = c.is_some_and(|c| c < sc.cols.len()
                    && sc.cols[c].sz.1.min(255) - sc.cols[c].sz.0.min(255) >= 128);
                let cuts_env = if wide { "QUOT_CUTS_WIDE" } else { "QUOT_CUTS_NARROW" };
                // (QUOT_CUTS_CROSS_ONLY: the build's two-chunk default outside switch / delayed / no-step columns and
                // the column after a switch)
                let cross_col = c.is_some_and(|c| c < sc.cols.len() && (sc.cols[c].sw || sc.cols[c].dl || sc.cols[c].dq
                    || (c > 0 && sc.cols[c - 1].sw)));
                let cross_only = std::env::var("QUOT_CUTS_CROSS_ONLY").map(|v| v == "1").unwrap_or(false);
                if cross_only && !cross_col && chunk_park {
                    if std::env::var_os("QUOT_PRED_CROSSDBG").is_some() { eprintln!("CROSSDBG non-crossing column {:?}", c); }
                }
                let cuts_env = if cross_only && !cross_col { "QUOT_CUTS_NONCROSS" } else { cuts_env };
                if let Ok(cuts) = std::env::var(cuts_env) {
                    if chunk_park {
                        let mut bd: Vec<isize> = vec![0];
                        bd.extend(cuts.split(',').filter_map(|x| x.trim().parse::<isize>().ok()));
                        if super::pointadd_frogdrop::K == 0 {
                            if c.is_some_and(|ci| (36..=113).contains(&ci)) { bd = vec![0, 1, 3, 6, 11, 17]; }
                            if c == Some(115) { bd = vec![0, 5, 11, 17]; }
                        }
                        bd.sort_unstable(); bd.dedup();
                        bd.push(isize::MAX);
                        need = bd.windows(2).map(|w| (qbl.min(w[1]) - w[0]).max(0)).max().unwrap_or(qbl);
                    }
                }
                // agent_lowq_quot IP5-split (QUOT_PRED_SPLITK=K, QUOT_PRED_RES_S): the HT payload park holds the bits
                // >= K at 0.. in a cycle with RES_S reserve lanes
                if let Some(kk) = std::env::var("QUOT_PRED_SPLITK").ok().and_then(|v| v.parse::<isize>().ok()) {
                    let rs: isize = std::env::var("QUOT_PRED_RES_S").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
                    if !hr_form && ybl as isize + (qbl - kk).max(0) - 129 > rs { return Some("gpark"); }
                }
                // agent_lowq_quot QUOT_PRED_RES_WIDE: the reserve of a crossing parked in a wide column (sz envelope
                // >= 128 lanes wide: no sz offset, so R takes a park lane there)
                let d = match std::env::var("QUOT_PRED_RES_WIDE").ok().and_then(|v| v.parse::<isize>().ok()) {
                    Some(dw) => {
                        let c = cols.iter().find(|e| e.1 == j).map(|e| e.2);
                        let wide = c.is_some_and(|c| c < sc.cols.len()
                            && sc.cols[c].sz.1.min(255) - sc.cols[c].sz.0.min(255) >= 128);
                        if wide { dw } else { d }
                    }
                    None => d,
                };
                if ybl as isize + need - 129 > d { return Some("gpark"); }
            }
        }
    }
    for &(ph2, j, c) in &cols {
        let dlstep = ph2 == 2;
        let ph = if dlstep { 0 } else { ph2 };
        let q = r[j - 1] / r[j];
        let (z, x, y) = if ph == 0 { (r[j], t[j - 1], t[j]) } else { (t[j], r[j + 1], r[j]) };
        if j < nn - 1 && !dlstep {
            // the map's pair (X_new, Y)
            let (xn, yy) = if ph == 0 { (t[j + 1], t[j]) } else { (r[j + 1], r[j]) };
            if v2(&xn) > emax || v2(&yy) > emax { return Some("v2"); }
            let (zz, zn) = if ph == 0 { (r[j], r[j + 1]) } else { (t[j], t[j + 1]) };
            if !map_fits(&zz, &xn, &yy, &zn, ring_at(c)) { return Some("map"); }
        }
        if gm {
            // Scheme G's stage-1 test (arch700 M13): HR binary search / HT reverse search must reproduce the step
            if j + 1 >= nn { continue; }
            if q >= (one << qb) { return Some("q0"); }
            // lowq-671 QUOT_PRED_KX: the crossing columns' V plays at precision KX with the one-sided threshold and
            // QUOT_PRED_FIXR exact overshoot-repair rounds (q^ - q in [0, FIXR] is repaired)
            // (QUOT_PRED_PSW=1: the column after a switch column too, as the circuit's b8b crossing set)
            // (QUOT_PRED_BIGY=Y: also the columns whose sy envelope reaches past Y, as the circuit's pool9 b8b set)
            let bigy_bound = std::env::var("QUOT_PRED_BIGY").ok().and_then(|v| v.parse::<usize>().ok())
                .or_else(|| (std::env::var("B12A_P1").as_deref() == Ok("1")).then_some(96));
            let bigy = bigy_bound.is_some_and(|y| c < sc.cols.len() && sc.cols[c].sy.1.min(128) > y);
            let cross = c < sc.cols.len() && (sc.cols[c].sw || sc.cols[c].dl || sc.cols[c].dq || bigy
                || super::midg::c63c_fixed_p1_col(c)
                || (std::env::var_os("QUOT_PRED_PSW").is_some() && c > 0 && sc.cols[c - 1].sw));
            // B12A: P1's Y-low catalytic register. On sy < 32 the Q[64..87) swap
            // supplies zeros; otherwise D is exactly Y mod 2^23. Every crossing
            // session uses the same two-sided shifted threshold at K24/TC26.
            if cross && std::env::var("B12A_P1").as_deref() == Ok("1") {
                let y = if ph == 0 { &t[j] } else { &r[j] };
                let d = if y.bit_len() < 32 { 0 } else { y.as_limbs()[0] & ((1u64 << 23) - 1) };
                B12A_D.with(|v| v.set(Some(d)));
                L671_2S.with(|v| v.set(true));
                let ok = if ph == 0 {
                    matches!(g_hr_dq(&r[j], &t[j - 1], y, &t[j + 1], 24, qb), Some(0))
                } else {
                    g_ht_ok(&t[j], y, &r[j - 1], &r[j + 1], &q, 24, qb)
                };
                L671_2S.with(|v| v.set(false));
                B12A_D.with(|v| v.set(None));
                if !ok { return Some(if ph == 0 { "gtest-hr-p1" } else { "gtest-ht-p1" }); }
                continue;
            }
            // lowq-671 QUOT_PRED_HRFIX=1: the circuit's HR repair (crossing, plain HR steps, today's two-sided test):
            // q^ - q in {0, 1} is exact, q^ < q (undershoot) still fails
            if cross && ph == 0 && !dlstep && std::env::var("QUOT_PRED_HRFIX").is_ok()
                && std::env::var("QUOT_PRED_KX").is_err() {
                L671_2S.with(|f| f.set(true));
                let dq = g_hr_dq(&r[j], &t[j - 1], &t[j], &t[j + 1], k, qb);
                L671_2S.with(|f| f.set(false));
                match dq { Some(0) | Some(1) => continue, Some(_) => return Some("gover"), None => return Some("gunder") }
            }
            if let (true, Some(kx0)) = (cross, std::env::var("QUOT_PRED_KX").ok().and_then(|v| v.parse::<usize>().ok())) {
                // QUOT_PRED_TH / QUOT_PRED_KXB: two tiers, precision KXB where the play's sy <= TH (Q room), else KX
                let syp = if ph == 0 { t[j].bit_len() } else { r[j].bit_len() };
                // QUOT_PRED_HT_KX / _HT_TH / _HT_FIXR: the HT plays' own tiers (two-sided, default no repair)
                let ht_own = ph == 1 && std::env::var("QUOT_PRED_HT_KX").is_ok();
                let envk = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<usize>().ok());
                let (kx0, th, kbx) = if ht_own { (envk("QUOT_PRED_HT_KX").unwrap(), envk("QUOT_PRED_HT_TH"), Some(envk("QUOT_PRED_HT_KXB").unwrap_or(24))) }
                                     else { (kx0, envk("QUOT_PRED_TH"), envk("QUOT_PRED_KXB")) };
                let (kx, tier_b) = match (th, kbx) {
                    (Some(th), Some(kb)) if syp <= th => (kb, true),
                    _ => (kx0, false),
                };
                // QUOT_PRED_HT_CONT=R: HT precision min(24, KA + max(0, R - sy)) (room above Y less the parked band)
                let kx = match (ht_own, envk("QUOT_PRED_HT_CONT")) {
                    (true, Some(rt)) => (kx0 + rt.saturating_sub(syp)).min(24),
                    _ => kx,
                };
                // QUOT_PRED_TIERB_2S=1: tier B keeps today's two-sided test (undershoots stay failures)
                L671_2S.with(|f| f.set(ht_own || (tier_b && std::env::var("QUOT_PRED_TIERB_2S").is_ok())));
                // (the circuit's HR repair skips delayed steps: their pre-stage-8 layout breaks the map detour)
                let fixr: usize = if ht_own { envk("QUOT_PRED_HT_FIXR").unwrap_or(0) }
                                  else if dlstep && std::env::var_os("QUOT_PRED_DLFIX").is_none() { 0 }
                                  else { std::env::var("QUOT_PRED_FIXR").ok().and_then(|v| v.parse().ok()).unwrap_or(0) };
                // QUOT_PRED_THS=top,mid,bot (lowq-672): per-session tiers. A session's enter and leave plays share
                // one TH: the top band's bits (kk >= 18) at TH_top, the middle (10..18) at TH_mid, the bottom at TH_bot
                let ths: Option<Vec<usize>> = std::env::var("QUOT_PRED_THS").ok()
                    .map(|v| v.split(',').filter_map(|x| x.trim().parse().ok()).collect());
                // QUOT_PRED_TBOCC=E0 (lowq-672): tier B per session iff the session's parked band leaves Q[E0..) clean:
                // sy + (bits the band can hold below bl(q) <= g + 1) <= E0, bands of the O3 frame tb = min(22, g)
                let occ: Option<usize> = envk("QUOT_PRED_TBOCC");
                let zb = if ph == 0 { r[j].bit_len() } else { t[j].bit_len() };
                let g = 257isize - zb as isize - syp as isize;
                let tbf = g.clamp(0, 22) as usize;
                let (t1s, t2s) = (super::midg::b8b_t1(syp.clamp(1, 128)), super::midg::b8b_t2(syp.clamp(1, 128)));
                let band_occ = |kk: usize| -> usize {
                    // the session of bit kk: top (tbf - t1, tbf], middle (tbf - t2, tbf - t1], bottom [0, tbf - t2]
                    if kk + t1s > tbf { (t1s).min(tbf + 1) }
                    else if kk + t2s > tbf { (tbf + 1).saturating_sub(t1s).min(t2s - t1s) }
                    else { (tbf + 1).saturating_sub(t2s) }
                };
                let dq = if let (Some(e0), Some(kb)) = (occ, kbx) {
                    // (QUOT_PRED_HR2S=1: HR tier A two-sided too, as without the margin and the repair)
                    let hr2s = std::env::var_os("QUOT_PRED_HR2S").is_some();
                    let kf = |kk: usize| if syp + band_occ(kk) <= e0 { (kb, true) } else { (kx0, ht_own || hr2s) };
                    // (key -200 - ph: a crossing step with a tier-A session bit, for the circuit fixture finder)
                    if (0..qb).any(|kk| (kk as isize) <= g && syp + band_occ(kk) > e0) {
                        L671_DQ.with(|d| *d.borrow_mut().entry(-200 - ph as i64).or_insert(0) += 1);
                        // (lowq-671 QUOT_PRED_TA_SYMIN=Y: tier A holds sy in a 16-value window [Y, Y + 16): a tier-A
                        // session below Y has no engine)
                        if envk("QUOT_PRED_TA_SYMIN").is_some_and(|y| syp < y) {
                            L671_2S.with(|f| f.set(false));
                            return Some("tasy");
                        }
                    }
                    let res = if ph == 0 { g_hr_dq_k(&r[j], &t[j - 1], &t[j], &t[j + 1], &kf, qb) }
                    else if g_ht_ok_k(&t[j], &r[j], &r[j - 1], &r[j + 1], &q, &kf, qb) { Some(0) } else { None };
                    // (QUOT_PRED_HIST=1: the failing steps' kind, sy and g, key = 10^6 (1 + ph) + 10^3 sy + g)
                    if std::env::var_os("QUOT_PRED_HIST").is_some() && !matches!(res, Some(0) | Some(1)) {
                        let key = 1_000_000 * (1 + ph as i64) + 1000 * syp as i64 + g.max(0) as i64;
                        L671_DQ.with(|d| *d.borrow_mut().entry(key).or_insert(0) += 1);
                    }
                    res
                } else if let (Some(ths), Some(kb)) = (&ths, kbx) {
                    let thk = |kk: usize| if kk >= 18 { ths[0] } else if kk >= 10 { ths[1] } else { ths[2] };
                    let kf = |kk: usize| if syp <= thk(kk) { (kb, true) } else { (kx0, ht_own) };
                    if ph == 0 { g_hr_dq_k(&r[j], &t[j - 1], &t[j], &t[j + 1], &kf, qb) }
                    else if g_ht_ok_k(&t[j], &r[j], &r[j - 1], &r[j + 1], &q, &kf, qb) { Some(0) } else { None }
                } else if ph == 0 { g_hr_dq(&r[j], &t[j - 1], &t[j], &t[j + 1], kx, qb) }
                  else { g_ht_dq(&t[j], &r[j], &r[j + 1], &q, kx, fixr + 2) };
                L671_2S.with(|f| f.set(false));
                L671_DQ.with(|m| *m.borrow_mut().entry(dq.map(|d| d as i64).unwrap_or(-1)).or_insert(0) += 1);
                match dq { Some(d) if d <= fixr => continue, Some(_) => return Some("gover"), None => return Some("gunder") }
            }
            let ok = if ph == 0 { g_hr_ok(&r[j], &t[j - 1], &t[j], &t[j + 1], k, qb) }
                     else { g_ht_ok(&t[j], &r[j], &r[j - 1], &r[j + 1], &q, k, qb) };
            if !ok { return Some("gtest"); }
            continue;
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

/// Scheme G's stage-1 test (arch700 M13): s = bl(Z) - K, Zh = (Z >> s) | 1, F = floor((2^(256-s) - 1) / Zh),
/// u = max(0, 257 - bl(Z) - TC), over(W) = [(W >> u) > (F >> u)].
fn g_over(w: &N, z: &N, k: usize) -> bool {
    let one = N::from(1u64);
    if let Some(d) = B12A_D.with(|v| v.get()) {
        assert_eq!(k, 24);
        let sz = z.bit_len();
        let s = sz - k;
        let zh = (*z >> s) | one;
        let f = ((one << (256 - s)) - one) / zh;
        let u = 257usize.saturating_sub(sz + super::midg::TC);
        let ra0 = N::from((1u64 << 23) - 1 - d);
        let ra = ((ra0 << super::midg::TC) + ((one << super::midg::TC) - one)) % zh;
        let rb = (N::from(d) << super::midg::TC) % zh;
        let e = N::from(u64::from(ra + rb >= zh));
        return (*w >> u) > (f >> u) - e;
    }
    let sz = z.bit_len();
    let s = sz - k;
    let zh = (*z >> s) | one;
    let f = ((one << (256 - s)) - one) / zh;
    let u = 257usize.saturating_sub(sz + super::midg::TC);
    (*w >> u) > (f >> u)
}

thread_local! {
    static B12A_D: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(None) };
    /// lowq-671: q^ - q of every crossing step the KX test checked (-1: undershoot / not a multiple)
    pub static L671_DQ: std::cell::RefCell<std::collections::BTreeMap<i64, u64>> = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
    pub static L671_2S: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// lowq-671 one-sided test: Zh' = ((Z >> s) - 1) | 1 <= Z >> s and F = floor(2^(256-s) / Zh') >= 2^256 / Z, so the
/// accepted set only grows (q^ >= q)
fn g_over_1s(w: &N, z: &N, k: usize) -> bool {
    if L671_2S.with(|f| f.get()) { return g_over(w, z, k); }
    // QUOT_PRED_MARGIN=M: the circuit's two-sided F with M more units in G (window -= M at position u) instead
    let auto = std::env::var("QUOT_PRED_MARGIN").as_deref() == Ok("auto");
    let mm = if auto { Some((1u64 << (super::midg::TC + 1 - k)) + 1) }
             else { std::env::var("QUOT_PRED_MARGIN").ok().and_then(|v| v.parse::<u64>().ok()) };
    if let Some(m) = mm {
        let one = N::from(1u64);
        let sz = z.bit_len();
        let s = sz - k;
        let zh = (*z >> s) | one;
        let f = ((one << (256 - s)) - one) / zh;
        let u = 257usize.saturating_sub(sz + super::midg::TC);
        // QUOT_PRED_MCOND=1: the margin only where the head x = Z >> s is even (x|1 = x on odd heads is one-sided)
        let even = !((*z >> s).bit(0));
        if std::env::var("QUOT_PRED_MCOND").is_ok() && !even { return (*w >> u) > (f >> u); }
        // lowq-672: the margin's threshold G' = ((F >> u) + 1 + M) << u must stay <= T = 2^(257 - sz) (no V wrap)
        let gp = ((f >> u) + one + N::from(m)) << u;
        if gp > (one << (257 - sz)) { L671_DQ.with(|d| *d.borrow_mut().entry(-100).or_insert(0) += 1); }
        return (*w >> u) > (f >> u) + N::from(m);
    }
    let one = N::from(1u64);
    let sz = z.bit_len();
    let s = sz - k;
    let zh = ((*z >> s) - one) | one;
    let f = (one << (256 - s)) / zh;
    let u = 257usize.saturating_sub(sz + super::midg::TC);
    (*w >> u) > (f >> u)
}

/// HR under the one-sided test: q^ - q from the binary search (None: undershoot or not on the progression)
fn g_hr_dq(z: &N, w0: &N, y: &N, t2: &N, k: usize, qb: usize) -> Option<usize> {
    let bb = 258isize - z.bit_len() as isize - y.bit_len() as isize;
    let mut w = *w0;
    for kk in (0..qb).rev() {
        if kk as isize >= bb { continue; }
        let tr = w + (*y << kk);
        if !g_over_1s(&tr, z, k) { w = tr; }
    }
    if w < *t2 { return None; }
    let d = w - *t2;
    if !(d % *y).is_zero() { return None; }
    let dq = d / *y;
    if dq.bit_len() > 16 { return Some(usize::MAX); }
    Some(dq.as_limbs()[0] as usize)
}

/// g_hr_dq with a per-bit (precision, two-sided) choice (lowq-672 per-session tiers)
fn g_hr_dq_k(z: &N, w0: &N, y: &N, t2: &N, kf: &dyn Fn(usize) -> (usize, bool), qb: usize) -> Option<usize> {
    let bb = 258isize - z.bit_len() as isize - y.bit_len() as isize;
    let mut w = *w0;
    for kk in (0..qb).rev() {
        if kk as isize >= bb { continue; }
        let tr = w + (*y << kk);
        let (k, two) = kf(kk);
        L671_2S.with(|f| f.set(two));
        if !g_over_1s(&tr, z, k) { w = tr; }
    }
    L671_2S.with(|f| f.set(false));
    if w < *t2 { return None; }
    let d = w - *t2;
    if !(d % *y).is_zero() { return None; }
    let dq = d / *y;
    if dq.bit_len() > 16 { return Some(usize::MAX); }
    Some(dq.as_limbs()[0] as usize)
}

/// g_ht_ok with a per-bit precision (two-sided at every bit: HT has no margin)
fn g_ht_ok_k(z: &N, y: &N, r0: &N, r2: &N, q: &N, kf: &dyn Fn(usize) -> (usize, bool), qb: usize) -> bool {
    let bb = 258isize - z.bit_len() as isize - y.bit_len() as isize;
    let _ = r0;
    let mut c = *q;
    let mut x = *r2 + *q * *y;
    for kk in 0..qb {
        if kk as isize >= bb { if c.bit(kk) { return false; } continue; }
        if c.bit(kk) { x -= *y << kk; }
        if !g_over(&(x + (*y << kk)), z, kf(kk).0) { c ^= N::from(1u64) << kk; }
    }
    c.is_zero() && x == *r2
}

/// HT under the one-sided test: q^ = max k with r_{j+1} + k r_j accepted; q^ - q (searched up to `lim`)
fn g_ht_dq(z: &N, y: &N, r2: &N, q: &N, k: usize, lim: usize) -> Option<usize> {
    let base = *r2 + *q * *y;
    if g_over_1s(&base, z, k) { return None; }
    let mut d = 0usize;
    while d < lim && !g_over_1s(&(base + N::from((d + 1) as u64) * *y), z, k) { d += 1; }
    Some(d)
}

/// HR (Z = r_j, W = t_{j-1}, Y = t_j): the top-down binary search ends at t_{j+1}.
fn g_hr_ok(z: &N, w0: &N, y: &N, t2: &N, k: usize, qb: usize) -> bool {
    let bb = 258isize - z.bit_len() as isize - y.bit_len() as isize;
    let mut w = *w0;
    for kk in (0..qb).rev() {
        if kk as isize >= bb { continue; }
        let tr = w + (*y << kk);
        if !g_over(&tr, z, k) { w = tr; }
    }
    w == *t2
}

/// HT (Z = t_j, Y = r_j, X = r_{j-1} after the exact division and X += qY): the bottom-up reverse search erases q.
fn g_ht_ok(z: &N, y: &N, r0: &N, r2: &N, q: &N, k: usize, qb: usize) -> bool {
    let bb = 258isize - z.bit_len() as isize - y.bit_len() as isize;
    let mut c = *q;
    let mut x = *r0;
    for kk in 0..qb {
        if kk as isize >= bb { if c.bit(kk) { return false; } continue; }
        if c.bit(kk) { x -= *y << kk; }
        if !g_over(&(x + (*y << kk)), z, k) { c ^= N::from(1u64) << kk; }
    }
    c.is_zero() && x == *r2
}
