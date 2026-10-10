//! frogtail tests: the walk against a register-level integer model, tick by tick, on 64 shots.

use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::frogtail::*;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

pub const SCHED: &str = include_str!("sched_frogtail.txt");

// ---------------------------------------------------------------- two's complement helpers on N (384 bits)
fn neg(x: N) -> N {
    (!x).wrapping_add(N::from(1u64))
}
fn is_neg(x: N) -> bool {
    x.bit(383)
}
/// signed width (bits needed in two's complement)
fn wid(x: N) -> usize {
    let a = if is_neg(x) { neg(x) } else { x };
    a.bit_len() + 1
}
/// exact two's complement width
fn wid_x(x: N) -> usize {
    if is_neg(x) {
        (!x).bit_len() + 1
    } else {
        x.bit_len() + 1
    }
}
fn sar1(x: N) -> N {
    let s = x >> 1;
    if is_neg(x) {
        s | (N::from(1u64) << 383)
    } else {
        s
    }
}
fn nu(x: N) -> usize {
    if x == N::ZERO {
        1000
    } else {
        x.trailing_zeros()
    }
}
/// two's complement value of `qs` (LSB first) in shot `shot`
fn get_s(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    let l = qs.len();
    if l > 0 && v.bit(l - 1) {
        v |= !((N::from(1u64) << l) - N::from(1u64));
    }
    v
}
fn get_u(w: &[u64], qs: &[QubitId], shot: usize) -> u64 {
    qs.iter()
        .enumerate()
        .map(|(i, &q)| ((w[q.0 as usize] >> shot) & 1) << i)
        .sum()
}
fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: N) {
    for (i, &q) in qs.iter().enumerate() {
        if v.bit(i) {
            w[q.0 as usize] |= 1 << shot
        } else {
            w[q.0 as usize] &= !(1 << shot)
        }
    }
}

fn mul_mod(a: N, b: N, m: N) -> N {
    a.mul_mod(b, m)
}
fn pow_mod(a: N, e: N, m: N) -> N {
    a.pow_mod(e, m)
}

// ---------------------------------------------------------------- register-level model
#[derive(Clone, Debug)]
pub struct M {
    pub av: N,
    pub ac: N,
    pub bv: N,
    pub bc: N,
    pub g: i64,
    pub j: i64,
    pub q: u64,
    pub par: u64,
    /// set when the shot leaves the machine's envelope (cap, window, schedule): not compared afterwards
    pub bad: Option<String>,
}

impl M {
    pub fn new(x: N) -> M {
        M {
            av: p(),
            ac: N::from(1u64),
            bv: x,
            bc: N::ZERO,
            g: 1,
            j: 1,
            q: 0,
            par: 0,
            bad: None,
        }
    }
    pub fn absorbed(&self) -> bool {
        !self.bv.bit(0)
    }
    /// step end (ordinary or absorbing) at the start of tick t
    fn step_end(&mut self, t: usize, sch: &Sched) {
        let e = t >= 2 && self.j < 0 && self.av.bit(0);
        let zl = sch.c[t].min(ZL);
        let f = t >= TABS
            && self.j < 0
            && self.bv.bit(0)
            && (self.av & ((N::from(1u64) << zl) - N::from(1u64))) == N::ZERO;
        if f && self.av != N::ZERO && self.bad.is_none() {
            self.bad = Some(format!("t{t}: absorption flag with A.v != 0"));
        }
        if e || f {
            let sp = nu(self.ac) as i64;
            if sp > (1 << SB) - 1 && self.bad.is_none() {
                self.bad = Some(format!("t{t}: step length {sp}"));
            }
            assert!(
                self.bad.is_some() || self.j == self.g - sp,
                "counter invariant"
            );
            self.g = sp - self.g;
            self.j = self.g;
            if self.g > QB as i64 - 1 && self.bad.is_none() {
                self.bad = Some(format!("t{t}: g {}", self.g));
            }
            self.q = 0;
            self.par ^= 1;
            std::mem::swap(&mut self.av, &mut self.bv);
            std::mem::swap(&mut self.ac, &mut self.bc);
        }
        if f {
            let s = self.av != N::from(1u64);
            self.av = N::ZERO;
            self.ac = N::from(1u64);
            self.bv = if s { neg(N::from(2u64)) } else { N::ZERO };
        }
    }
    pub fn close(&mut self, sch: &Sched) {
        self.step_end(sch.t + 1, sch);
    }
    pub fn tick(&mut self, t: usize, sch: &Sched) {
        self.step_end(t, sch);
        let a = self.av.bit(0) && self.j >= 0;
        let c = sch.c[t];
        let fits = |m: &M, cc: usize| {
            wid(m.av) <= cc
                && wid_x(m.bv) <= cc
                && wid(m.bc) <= sch.wb - cc
                && wid(m.ac) <= sch.wa - cc
        };
        if !fits(self, c) && self.bad.is_none() {
            self.bad = Some(format!("t{t}: pre-add widths"));
        }
        if self.j >= 0 {
            // shift-register digit store
            self.q >>= 1;
            if a {
                self.q |= 1 << (QB - 1);
            }
        }
        if a {
            if self.j == 0 {
                self.av = self.av.wrapping_sub(self.bv);
                self.bc = self.bc.wrapping_add(self.ac);
            } else {
                self.av = self.av.wrapping_add(self.bv);
                self.bc = self.bc.wrapping_sub(self.ac);
            }
        }
        if !fits(self, c) && self.bad.is_none() {
            self.bad = Some(format!("t{t}: post-add widths"));
        }
        assert!(self.bad.is_some() || !self.av.bit(0));
        self.av = sar1(self.av);
        self.ac = self.ac << 1;
        if self.bv.bit(0) {
            self.j -= 1;
        }
        if self.j == -1 && self.bv.bit(0) {
            assert_eq!(t % 2, 0, "digit completion parity");
            self.q = 0;
        }
        if !fits(self, sch.c[t + 1]) && self.bad.is_none() {
            self.bad = Some(format!("t{t}: post-halve widths"));
        }
    }
}

/// Walk registers for a test: B ring = x lanes + fresh.
fn alloc_walk(b: &mut B, sch: &Sched, x: &[QubitId]) -> Walk {
    let mut bb = x.to_vec();
    bb.extend(b.alloc_n(sch.wb - x.len()));
    Walk {
        a: b.alloc_n(sch.wa),
        bb,
        q: b.alloc_n(QB),
        j: b.alloc_n(JB),
        par: b.alloc(),
    }
}

/// Decode the walk's registers at the start of tick t (after tick t - 1's halve).
fn decode(w: &Walk, sch: &Sched, t: usize, st: &[u64], shot: usize) -> M {
    let c = sch.c[t];
    let av: Vec<QubitId> = (0..c).map(|f| w.af(t, f)).collect();
    let ac: Vec<QubitId> = (0..sch.wa - c).map(|s| w.asig(t, s)).collect();
    let bv: Vec<QubitId> = (0..c).map(|f| w.bf(f)).collect();
    let bc: Vec<QubitId> = (0..sch.wb - c).map(|s| w.bsig(s)).collect();
    let j = get_u(st, &w.j, shot) as i64;
    let j = if j >= 1 << (JB - 1) { j - (1 << JB) } else { j };
    M {
        av: get_s(st, &av, shot),
        ac: get_s(st, &ac, shot),
        bv: get_s(st, &bv, shot),
        bc: get_s(st, &bc, shot),
        g: 0,
        j,
        q: 0,
        par: get_u(st, &[w.par], shot),
        bad: None,
    }
}

fn same(a: &M, b: &M) -> bool {
    a.av == b.av && a.ac == b.ac && a.bv == b.bv && a.bc == b.bc && a.j == b.j && a.par == b.par
}

/// Run the walk for `ticks` ticks on 64 random odd x' and compare every tick with the model.
fn walk_check(ticks: usize, seed: u64) {
    let sch = Sched::from_text(SCHED);
    let mut b = B::new();
    let x = b.alloc_n(256);
    let w = alloc_walk(&mut b, &sch, &x);
    let dirty = b.alloc_n(64);
    let sc = Scr::alloc_fwd(&mut b, &dirty, 12);
    init(&mut b, &w);
    let mut bounds = vec![b.ops.len()];
    let mut tof = vec![b.tof];
    for t in 1..=ticks {
        let m = b.fresh_bits(1)[0];
        fwd_tick(&mut b, &w, t, &sch, &sc, m);
        bounds.push(b.ops.len());
        tof.push(b.tof);
    }
    if ticks == sch.t {
        close_fwd(&mut b, &w, &sch, &sc);
    }
    eprintln!(
        "frogtail walk: {} ticks, {} ops, {} Toffoli ({:.0}/tick), peak {}",
        ticks,
        b.ops.len(),
        b.tof,
        b.tof as f64 / ticks as f64,
        b.peak
    );
    let mut rng = Rng::new(seed);
    let xs: Vec<N> = (0..64)
        .map(|_| {
            let mut v = rng.below(256) % p();
            if v == N::ZERO {
                v = N::from(3u64);
            }
            if !v.bit(0) {
                v = p() - v;
            }
            v
        })
        .collect();
    let dv: Vec<N> = (0..64).map(|_| rng.below(64)).collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogtail-test");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(
        (aq as usize).max(b.width() as usize),
        (nb as usize).max(1),
        &mut xof,
    );
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &dirty, k, dv[k]);
    }
    let mut ms: Vec<M> = xs.iter().map(|&x| M::new(x)).collect();
    let scratch: Vec<QubitId> = [sc.e, sc.a, sc.eq, sc.one]
        .iter()
        .cloned()
        .chain(sc.xs.iter().cloned())
        .chain(sc.pool.iter().cloned())
        .chain(sc.tmp.iter().cloned())
        .chain(w.q.iter().cloned())
        .collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let mut bad_shots = 0;
    let mut ends = 0u64;
    let mut adds = 0u64;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for k in 0..64 {
            let par0 = ms[k].par;
            let q0 = ms[k].q;
            ms[k].tick(t, &sch);
            ends += (ms[k].par != par0) as u64;
            adds += (ms[k].q != q0 && ms[k].par == par0) as u64;
            if ms[k].bad.is_some() {
                continue;
            }
            let got = decode(&w, &sch, t + 1, &s.qubits, k);
            assert!(
                same(&got, &ms[k]),
                "tick {t} shot {k}:\n got {:?}\nwant {:?}",
                got,
                ms[k]
            );
            for &q in &scratch {
                assert_eq!(
                    (s.qubits[q.0 as usize] >> k) & 1,
                    0,
                    "tick {t} shot {k}: scratch q{} dirty",
                    q.0
                );
            }
            assert_eq!(
                get_s(&s.qubits, &dirty, k) & ((N::from(1u64) << 64) - N::from(1u64)),
                dv[k],
                "dirty lanes"
            );
        }
        if t % 100 == 0 {
            eprintln!("  tick {t}: ok ({} Toffoli so far)", tof[t]);
        }
    }
    for m in &ms {
        if let Some(r) = &m.bad {
            bad_shots += 1;
            eprintln!("  out-of-envelope shot: {r}");
        }
    }
    eprintln!("walk_check: {ticks} ticks, 64 shots, {bad_shots} outside the envelope, {ends} step ends, {adds} digit ticks");
    if ticks == sch.t {
        s.apply_iter(b.ops[bounds[ticks]..].iter());
        let tc = sch.t + 1;
        let cc = sch.c[tc];
        let pm = p();
        let twoinv_t = pow_mod(N::from(2u64), pm - N::from(2u64) - N::from(0u64), pm); // 2^-1
        let twoinv_t = pow_mod(twoinv_t, N::from(sch.t as u64), pm);
        let mut okn = 0;
        for k in 0..64 {
            if ms[k].bad.is_some() {
                continue;
            }
            ms[k].close(&sch);
            if ms[k].bad.is_some() {
                continue;
            }
            let got = decode(&w, &sch, tc, &s.qubits, k);
            assert!(
                same(&got, &ms[k]),
                "closing step shot {k}: got {:?} want {:?}",
                got,
                ms[k]
            );
            assert!(
                ms[k].absorbed() && ms[k].av == N::ZERO && ms[k].j == 1,
                "shot {k} not absorbed"
            );
            let ac: Vec<QubitId> = (0..sch.wa - cc).map(|s| w.asig(tc, s)).collect();
            let mm = get_s(&s.qubits, &ac, k).trailing_zeros();
            assert_eq!(
                get_s(&s.qubits, &ac, k),
                N::from(1u64) << mm,
                "shot {k}: A.c one-hot"
            );
            let bcl: Vec<QubitId> = (0..sch.wb - cc).map(|s| w.bsig(s)).collect();
            let cval = get_s(&s.qubits, &bcl, k) << mm;
            let sgn = is_neg(ms[k].bv) ^ (ms[k].par == 1) ^ true;
            // C mod p (C signed)
            let cm = if is_neg(cval) {
                pm - (neg(cval) % pm)
            } else {
                cval % pm
            };
            let mut inv = mul_mod(cm, twoinv_t, pm);
            if sgn {
                inv = (pm - inv) % pm;
            }
            assert_eq!(
                mul_mod(inv, xs[k], pm),
                N::from(1u64),
                "shot {k}: end state is not the inverse"
            );
            okn += 1;
        }
        eprintln!("end state: {okn} shots give x'^-1 = (-1)^S C 2^-T");
    }
}

#[test]
fn frogtail_walk_short() {
    walk_check(40, 7);
}

#[test]
#[ignore]
fn frogtail_walk_full() {
    let sch = Sched::from_text(SCHED);
    walk_check(sch.t, 11);
}

/// Forward walk, unabsorb (C_T checked) and its undo, inverse walk: every register back to its start, scratch
/// clean, phase 0.
#[test]
#[ignore]
fn frogtail_walk_roundtrip() {
    let sch = Sched::from_text(SCHED);
    let mut b = B::new();
    let x = b.alloc_n(256);
    let w = alloc_walk(&mut b, &sch, &x);
    let dirty = b.alloc_n(64);
    let mut sc = Scr::alloc(&mut b, &dirty);
    sc.pool = b.alloc_n(83);
    let m = walk_forward(&mut b, &w, &sch, &sc);
    let n_fwd = (b.ops.len(), b.tof);
    let mr = b.alloc_n(MB);
    let tm = b.alloc_n(MB);
    let (r, key, rc) = unabsorb(&mut b, &w, &sch, &mr, &tm, &dirty);
    let n_mid = b.ops.len();
    let t_un = b.tof - n_fwd.1;
    b.play(&rc, true);
    walk_inverse(&mut b, &w, &sch, &sc, &m);
    eprintln!(
        "forward walk {} Toffoli, unabsorb {t_un}, inverse walk {} Toffoli",
        n_fwd.1,
        b.tof - n_fwd.1 - 2 * t_un
    );
    let mut rng = Rng::new(99);
    let xs: Vec<N> = (0..64)
        .map(|_| {
            let mut v = rng.below(256) % p();
            if v == N::ZERO {
                v = N::from(5u64);
            }
            if !v.bit(0) {
                v = p() - v;
            }
            v
        })
        .collect();
    let dv: Vec<N> = (0..64).map(|_| rng.below(64)).collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogtail-rt");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(
        (aq as usize).max(b.width() as usize),
        (nb as usize).max(1),
        &mut xof,
    );
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &dirty, k, dv[k]);
    }
    s.apply_iter(b.ops[..n_mid].iter());
    // after unabsorb: R = C_T (x'^-1 = (-1)^S C_T 2^-T, S = s ^ par ^ 1), key = s, every other A lane, B.v's low
    // lane, j and the temps |0>
    let pm = p();
    let inv2t = N::from(2u64)
        .pow_mod(pm - N::from(2u64), pm)
        .pow_mod(N::from(sch.t as u64), pm);
    let mut ms: Vec<M> = xs.iter().map(|&x| M::new(x)).collect();
    let mut okn = 0;
    for k in 0..64 {
        for t in 1..=sch.t {
            ms[k].tick(t, &sch);
        }
        ms[k].close(&sch);
        if ms[k].bad.is_some() {
            continue;
        }
        let cval = get_s(&s.qubits, &r, k);
        let sgn = is_neg(ms[k].bv) ^ (ms[k].par == 1) ^ true;
        assert_eq!(
            (s.qubits[key.0 as usize] >> k) & 1,
            is_neg(ms[k].bv) as u64,
            "shot {k}: key"
        );
        let cm = if is_neg(cval) {
            pm - (neg(cval) % pm)
        } else {
            cval % pm
        };
        let mut inv = cm.mul_mod(inv2t, pm);
        if sgn {
            inv = (pm - inv) % pm;
        }
        assert_eq!(
            inv.mul_mod(xs[k], pm),
            N::from(1u64),
            "shot {k}: C_T is not the inverse"
        );
        for &q in
            w.a.iter()
                .filter(|q| !r.contains(q))
                .chain(&w.j)
                .chain(&tm)
                .chain(std::iter::once(&w.bb[0]))
        {
            assert_eq!(
                (s.qubits[q.0 as usize] >> k) & 1,
                0,
                "shot {k}: q{} not cleared by unabsorb",
                q.0
            );
        }
        okn += 1;
    }
    eprintln!("unabsorb: {okn} shots give C_T");
    s.apply_iter(b.ops[n_mid..].iter());
    for k in 0..64 {
        assert_eq!(
            get_s(&s.qubits, &x, k) & ((N::from(1u64) << 256) - N::from(1u64)),
            xs[k],
            "shot {k}: x' restored"
        );
        for &q in
            w.a.iter()
                .chain(&w.bb[256..])
                .chain(&w.q)
                .chain(&w.j)
                .chain(std::iter::once(&w.par))
                .chain(&mr)
        {
            assert_eq!(
                (s.qubits[q.0 as usize] >> k) & 1,
                0,
                "shot {k}: walk register not cleared"
            );
        }
        assert_eq!(
            get_s(&s.qubits, &dirty, k) & ((N::from(1u64) << 64) - N::from(1u64)),
            dv[k]
        );
    }
    assert_eq!(s.phase, 0);
    eprintln!(
        "roundtrip ok: {} ops, {} Toffoli, peak {}",
        b.ops.len(),
        b.tof,
        b.peak
    );
}

#[test]
fn frogtail_product_tail() {
    use super::modp_frogdrop::{product, Ms};
    let (m, tt) = (318usize, 556usize);
    let mut b = B::new();
    let c = b.alloc_n(m);
    let y = b.alloc_n(256);
    let ms = Ms::alloc(&mut b);
    let z0 = b.alloc_n(256);
    let mut z = z0.clone();
    let t0 = b.tof;
    product_tail(&mut b, &ms, &mut z, &c, &y, tt);
    let t_tail = b.tof - t0;
    // reference cost: frogdrop's 256-bit product
    let mut b2 = B::new();
    let a2 = b2.alloc_n(256);
    let y2 = b2.alloc_n(256);
    let ms2 = Ms::alloc(&mut b2);
    let mut z2 = b2.alloc_n(256);
    product(&mut b2, &ms2, &mut z2, &a2, &y2);
    eprintln!(
        "product_tail M={m} T={tt}: {t_tail} Toffoli; frogdrop product: {} Toffoli",
        b2.tof
    );
    let mut rng = Rng::new(5);
    let pm = p();
    let cs: Vec<N> = (0..64)
        .map(|_| {
            let v = rng.below(m);
            if v.bit(m - 1) {
                v | !((N::from(1u64) << m) - N::from(1u64))
            } else {
                v
            }
        })
        .collect();
    let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogtail-prod");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(
        (aq as usize).max(b.width() as usize),
        (nb as usize).max(1),
        &mut xof,
    );
    for k in 0..64 {
        put(&mut s.qubits, &c, k, cs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let inv2t = N::from(2u64)
        .pow_mod(pm - N::from(2u64), pm)
        .pow_mod(N::from(tt as u64), pm);
    for k in 0..64 {
        let cm = if is_neg(cs[k]) {
            pm - (neg(cs[k]) % pm)
        } else {
            cs[k] % pm
        };
        let want = ys[k].mul_mod(cm, pm).mul_mod(inv2t, pm);
        let got = get_s(&s.qubits, &z, k) & ((N::from(1u64) << 256) - N::from(1u64));
        assert_eq!(got, want, "shot {k}");
        assert_eq!(
            get_s(&s.qubits, &y, k) & ((N::from(1u64) << 256) - N::from(1u64)),
            ys[k]
        );
    }
    assert_eq!(s.phase, 0);
}

#[test]
fn frogtail_point_add_end_to_end() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    let mut b = B::new();
    let (xq, yq) = super::pointadd_frogtail::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let (nq, _, _, regs) = crate::circuit::analyze_ops(ops.iter());
    eprintln!(
        "ops {} qubits {} peak {} emitted tof {}",
        ops.len(),
        nq,
        b.peak,
        b.tof
    );
    super::tests_chunked::expected_t(&ops);
    // curve
    let pp = super::frogdrop_sched::p();
    let to_u = |v: &N| -> ruint::aliases::U256 {
        ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap())
    };
    type U = ruint::aliases::U256;
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO,
        b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
    let _ = &pp;
    let mut rng = Rng::new(
        std::env::var("FROGTAIL_SEED")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(2024),
    );
    let mut cases = vec![];
    for _ in 0..64 {
        let k1 = to_u(&(rng.below(250) + N::from(1u64)));
        let k2 = to_u(&(rng.below(250) + N::from(1u64)));
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        let e = curve.add(t.0, t.1, o.0, o.1);
        cases.push((t, o, e));
    }
    let mut h = sha3::Shake256::default();
    h.update(b"frogtail-e2e");
    let mut xof = h.finalize_xof();
    let (_, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
    let mut sim = crate::sim::Simulator::new(nq as usize, nb as usize, &mut xof);
    for (k, (t, o, _)) in cases.iter().enumerate() {
        sim.set_register(&regs[0], t.0, k);
        sim.set_register(&regs[1], t.1, k);
        sim.set_register(&regs[2], o.0, k);
        sim.set_register(&regs[3], o.1, k);
    }
    sim.apply_iter(ops.iter());
    let mut bad = 0;
    for (k, (_, _, e)) in cases.iter().enumerate() {
        let gx = sim.get_register(&regs[0], k);
        let gy = sim.get_register(&regs[1], k);
        if gx != e.0 || gy != e.1 {
            bad += 1;
            eprintln!("shot {k} wrong");
        }
    }
    eprintln!("phase {:#x}, bad {bad}", sim.phase);
    assert_eq!(sim.phase, 0, "phase garbage");
    let regq: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    for q in 0..nq {
        if !regq.contains(&q) {
            assert_eq!(sim.qubits[q as usize], 0, "ancilla garbage q{q}");
        }
    }
    assert_eq!(bad, 0, "classical mismatches");
    eprintln!(
        "frogtail end-to-end OK: avg Toffoli {}",
        sim.stats.toffoli_gates / 64
    );
}

/// Toffoli per tick: forward tick and regenerating tick (a mid-walk tick).
#[test]
fn frogtail_tick_breakdown() {
    let sch = Sched::from_text(SCHED);
    let mut b = B::new();
    let x = b.alloc_n(256);
    let w = alloc_walk(&mut b, &sch, &x);
    let dirty = b.alloc_n(64);
    let sc = Scr::alloc(&mut b, &dirty);
    let t = 300;
    let m = b.fresh_bits(1)[0];
    let t0 = b.tof;
    fwd_tick(&mut b, &w, t, &sch, &sc, m);
    let tf = b.tof - t0;
    let (p1, p2, p3) = rec_regen_tick(&mut b, &w, t, &sch, &sc);
    let t1 = b.tof;
    b.play(&p1, false);
    let a = b.tof - t1;
    b.play(&p2, false);
    let bb = b.tof - t1 - a;
    b.play(&p3, false);
    eprintln!(
        "tick {t}: forward {tf} Toffoli; regenerating {} (step end + digit core {a}, store {bb})",
        b.tof - t1
    );
}

#[test]
fn modp_ft_ops() {
    use super::modp_ft::*;
    let pm = p();
    let m256 = (N::from(1u64) << 256) - N::from(1u64);
    let mut rng = Rng::new(123);
    let zs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
    let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
    let cs: Vec<bool> = (0..64).map(|k| k % 3 != 2).collect();
    let sim = |b: &B, z: &[QubitId], y: &[QubitId], ctl: QubitId| {
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"modp-ft");
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new(
            (aq as usize).max(b.width() as usize),
            (nb as usize).max(1),
            &mut xof,
        );
        for k in 0..64 {
            put(&mut s.qubits, z, k, zs[k]);
            put(&mut s.qubits, y, k, ys[k]);
            if cs[k] {
                s.qubits[ctl.0 as usize] |= 1 << k;
            }
        }
        s.apply_iter(b.ops.iter());
        assert_eq!(s.phase, 0);
        s.qubits.clone()
    };
    // ctrl_add_pool: t += ctl a mod 2^n for several widths and pool sizes
    for &(n, pn) in &[
        (2usize, 0usize),
        (2, 1),
        (2, 5),
        (9, 0),
        (9, 3),
        (9, 8),
        (9, 20),
        (40, 17),
    ] {
        let mut b = B::new();
        let (z, y, ctl) = (b.alloc_n(256), b.alloc_n(256), b.alloc());
        let pool = b.alloc_n(pn);
        ctrl_add_pool(&mut b, &y[..n], &z[..n], ctl, &pool);
        let q = sim(&b, &z, &y, ctl);
        let mn = (N::from(1u64) << n) - N::from(1u64);
        for k in 0..64 {
            let want = ((zs[k] & mn) + if cs[k] { ys[k] & mn } else { N::ZERO }) & mn;
            assert_eq!(
                get_s(&q, &z[..n], k) & mn,
                want,
                "ctrl_add_pool n {n} pool {pn} shot {k}"
            );
            assert_eq!(get_s(&q, &y, k) & m256, ys[k], "source restored");
            for &l in &pool {
                assert_eq!((q[l.0 as usize] >> k) & 1, 0, "pool clean");
            }
        }
        eprintln!("ctrl_add_pool n {n} pool {pn}: {} T", b.tof);
    }
    // ctrl_modadd
    {
        let mut b = B::new();
        let (z, y, ctl, d) = (b.alloc_n(256), b.alloc_n(256), b.alloc(), b.alloc());
        let ms = Ms::alloc(&mut b);
        ctrl_modadd(&mut b, &ms, &z, &y, ctl, d);
        let q = sim(&b, &z, &y, ctl);
        for k in 0..64 {
            let want = (zs[k] + if cs[k] { ys[k] } else { N::ZERO }) % pm;
            assert_eq!((get_s(&q, &z, k) & m256) % pm, want, "ctrl_modadd {k}");
        }
        eprintln!("ctrl_modadd {} T", b.tof);
    }
    // mod_double / mod_halve / ctrl_neg
    {
        let mut b = B::new();
        let (z, y, ctl) = (b.alloc_n(256), b.alloc_n(256), b.alloc());
        let ms = Ms::alloc(&mut b);
        let mut zz = z.clone();
        mod_double(&mut b, &ms, &mut zz);
        let t1 = b.tof;
        let q = sim(&b, &z, &y, ctl);
        for k in 0..64 {
            assert_eq!(
                (get_s(&q, &zz, k) & m256) % pm,
                zs[k].mul_mod(N::from(2u64), pm),
                "double {k}"
            );
        }
        let mut b = B::new();
        let (z, y, ctl) = (b.alloc_n(256), b.alloc_n(256), b.alloc());
        let ms = Ms::alloc(&mut b);
        let mut zz = z.clone();
        mod_halve(&mut b, &ms, &mut zz);
        let q = sim(&b, &z, &y, ctl);
        let h = N::from(2u64).pow_mod(pm - N::from(2u64), pm);
        for k in 0..64 {
            assert_eq!(
                (get_s(&q, &zz, k) & m256) % pm,
                zs[k].mul_mod(h, pm),
                "halve {k}"
            );
        }
        let mut b = B::new();
        let (z, y, ctl) = (b.alloc_n(256), b.alloc_n(256), b.alloc());
        let ms = Ms::alloc(&mut b);
        ctrl_neg(&mut b, &ms, &z, Some(ctl));
        let q = sim(&b, &z, &y, ctl);
        for k in 0..64 {
            let want = if cs[k] { (pm - zs[k]) % pm } else { zs[k] };
            assert_eq!((get_s(&q, &z, k) & m256) % pm, want, "neg {k}");
        }
        eprintln!("mod_double {t1} T, ctrl_neg {} T", b.tof);
    }
    // product_tail
    {
        let (m, tt) = (318usize, 556usize);
        let mut b = B::new();
        let c = b.alloc_n(m);
        let y = b.alloc_n(256);
        let ms = Ms::alloc(&mut b);
        let mut z = b.alloc_n(256);
        product_tail(&mut b, &ms, &mut z, &c, &y, tt);
        let cvs: Vec<N> = (0..64)
            .map(|_| {
                let v = rng.below(m);
                if v.bit(m - 1) {
                    v | !((N::from(1u64) << m) - N::from(1u64))
                } else {
                    v
                }
            })
            .collect();
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"modp-ft-pt");
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new(
            (aq as usize).max(b.width() as usize),
            (nb as usize).max(1),
            &mut xof,
        );
        for k in 0..64 {
            put(&mut s.qubits, &c, k, cvs[k]);
            put(&mut s.qubits, &y, k, ys[k]);
        }
        s.apply_iter(b.ops.iter());
        assert_eq!(s.phase, 0);
        let inv2t = N::from(2u64)
            .pow_mod(pm - N::from(2u64), pm)
            .pow_mod(N::from(tt as u64), pm);
        for k in 0..64 {
            let cm = if is_neg(cvs[k]) {
                pm - (neg(cvs[k]) % pm)
            } else {
                cvs[k] % pm
            };
            let want = ys[k].mul_mod(cm, pm).mul_mod(inv2t, pm);
            assert_eq!(
                (get_s(&s.qubits, &z, k) & m256) % pm,
                want,
                "product_tail {k}"
            );
        }
        eprintln!("product_tail {} T", b.tof);
    }
}

/// Walk failure prediction for a division input d (made odd as the circuit does): None if the walk stays in the
/// machine's envelope and finishes by T.
pub fn predict_ft(d: N, sch: &Sched) -> Option<String> {
    let pm = p();
    let x = if d.bit(0) { d } else { pm - d };
    let mut m = M::new(x);
    for t in 1..=sch.t {
        m.tick(t, sch);
        if m.bad.is_some() {
            return m.bad;
        }
    }
    m.close(sch);
    if m.bad.is_some() {
        return m.bad;
    }
    if !m.absorbed() {
        return Some("end: not absorbed".into());
    }
    // C_T = C 2^m must fit the RLEN-lane register, m < 2^MB
    let mm = nu(m.ac);
    if mm >= (1 << MB) || wid(m.bc) + mm > RLEN {
        return Some(format!("end: C_T m {} width {}", mm, wid(m.bc) + mm));
    }
    None
}

#[test]
#[ignore = "tool: FROGTAIL_SCAN=n cargo test --release --bin build_circuit -- frogtail_predict_nonce --ignored --nocapture"]
fn frogtail_predict_nonce() {
    use super::pointadd_frogtail::*;
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    type U = ruint::aliases::U256;
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO,
        b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
    let scan: usize = std::env::var("FROGTAIL_SCAN")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut b = B::new();
    let _ = point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let width = b.width();
    eprintln!("built {} ops, width {width}", ops.len());
    let l = ops.len();
    let mut pre = sha3::Shake256::default();
    pre.update(b"quantum_ecc-fiat-shamir-v2");
    pre.update(&(l as u64).to_le_bytes());
    let upd = |h: &mut sha3::Shake256, op: &crate::circuit::Op| {
        h.update(&[op.kind as u8]);
        h.update(&op.q_control2.0.to_le_bytes());
        h.update(&op.q_control1.0.to_le_bytes());
        h.update(&op.q_target.0.to_le_bytes());
        h.update(&op.c_target.0.to_le_bytes());
        h.update(&op.c_condition.0.to_le_bytes());
        h.update(&op.r_target.0.to_le_bytes());
    };
    for op in &ops[..l - 2] {
        upd(&mut pre, op);
    }
    let tail = ops[l - 2];
    drop(ops);
    let sched = Sched::from_text(SCHED_FROGTAIL);
    let pp = super::frogdrop_sched::p();
    let to_n = |u: U| -> N {
        let mut v = N::ZERO;
        for (i, &w) in u.as_limbs().iter().enumerate() {
            v |= N::from(w) << (64 * i);
        }
        v
    };
    let pred = |x: N| predict_ft(x, &sched);
    let half = std::env::var("FROGTAIL_SHOTS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(9024usize);
    let mut clean = vec![];
    for nonce in 0..(scan.max(1) as u64) {
        let q = if scan == 0 { tail.q_target.0 } else { nonce };
        if q >= width {
            break;
        }
        let mut h = pre.clone();
        let mut op = tail;
        op.q_target = crate::circuit::QubitId(q);
        upd(&mut h, &op);
        upd(&mut h, &op);
        let mut xof = h.finalize_xof();
        let mut fails = std::collections::BTreeMap::<String, usize>::new();
        let mut n = 0;
        for _ in 0..half {
            let mut rb = [[0u8; 32]; 2];
            xof.read(&mut rb[0]);
            xof.read(&mut rb[1]);
            let k1 = U::from_le_bytes(rb[0]);
            let k2 = U::from_le_bytes(rb[1]);
            let t = curve.mul(curve.gx, curve.gy, k1);
            let o = curve.mul(curve.gx, curve.gy, k2);
            if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) {
                continue;
            }
            let e = curve.add(t.0, t.1, o.0, o.1);
            n += 1;
            let (x1, x2, x3) = (to_n(t.0), to_n(o.0), to_n(e.0));
            let d1 = if x1 >= x2 { x1 - x2 } else { x1 + pp - x2 };
            let d2 = if x3 >= x2 { x3 - x2 } else { x3 + pp - x2 };
            if std::env::var("FROGTAIL_DUMP")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                == Some(n - 1)
            {
                eprintln!("DUMP shot {}: x1' {:#x} x2' {:#x}", n - 1, d1, d2);
            }
            for d in [d1, d2] {
                if let Some(why) = pred(d) {
                    *fails
                        .entry(
                            why.split(':')
                                .nth(1)
                                .unwrap_or(&why)
                                .trim()
                                .split(' ')
                                .next()
                                .unwrap_or("")
                                .to_string(),
                        )
                        .or_default() += 1;
                }
            }
        }
        let nf: usize = fails.values().sum();
        eprintln!(
            "nonce qubit {q}: {n} shots, failing divisions {nf} {:?}",
            fails
        );
        if nf == 0 {
            clean.push(q);
        }
    }
    eprintln!("clean nonces: {:?}", clean);
}

/// Forward K ticks then the inverse (closing step + regenerating ticks backwards): phase per K.
#[test]
#[ignore]
fn frogtail_mbu_bisect() {
    let full = Sched::from_text(SCHED);
    for &k in &[556usize] {
        let sch = Sched {
            wa: full.wa,
            wb: full.wb,
            t: k,
            c: full.c[..k + 2].to_vec(),
        };
        let mut b = B::new();
        let x = b.alloc_n(256);
        let w = alloc_walk(&mut b, &sch, &x);
        let dirty = b.alloc_n(64);
        let sc = Scr::alloc(&mut b, &dirty);
        let m = walk_forward(&mut b, &w, &sch, &sc);
        walk_inverse(&mut b, &w, &sch, &sc, &m);
        let mut rng = Rng::new(5);
        let xs: Vec<N> = (0..64)
            .map(|_| {
                let mut v = rng.below(256) % p();
                if v == N::ZERO {
                    v = N::from(5u64);
                }
                if !v.bit(0) {
                    v = p() - v;
                }
                v
            })
            .collect();
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"frogtail-bisect");
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new(
            (aq as usize).max(b.width() as usize),
            (nb as usize).max(1),
            &mut xof,
        );
        for kk in 0..64 {
            put(&mut s.qubits, &x, kk, xs[kk]);
        }
        s.apply_iter(b.ops.iter());
        let mut regs_ok = true;
        for kk in 0..64 {
            if get_s(&s.qubits, &x, kk) & ((N::from(1u64) << 256) - N::from(1u64)) != xs[kk] {
                regs_ok = false;
            }
            for &q in
                w.a.iter()
                    .chain(&w.bb[256..])
                    .chain(&w.q)
                    .chain(&w.j)
                    .chain(std::iter::once(&w.par))
            {
                if (s.qubits[q.0 as usize] >> kk) & 1 != 0 {
                    regs_ok = false;
                }
            }
        }
        eprintln!(
            "K = {k}: registers {} phase {:#x}",
            if regs_ok { "ok" } else { "BAD" },
            s.phase
        );
        for kk in 0..64 {
            let mut md = M::new(xs[kk]);
            for t in 1..=k {
                md.tick(t, &sch);
            }
            if (s.phase >> kk) & 1 == 1 || kk < 3 {
                eprintln!(
                    "   shot {kk} phase {}: j {} g {} nu(ac) {} q {:#x} done {}",
                    (s.phase >> kk) & 1,
                    md.j,
                    md.g,
                    nu(md.ac),
                    md.q,
                    md.av == N::ZERO
                );
            }
        }
    }
}

/// The regenerating walk run forward (digits stored and erased exactly): phase 0 and Q = model digits every tick,
/// then the closing step at T + 1 leaves Q = 0 with phase 0.
#[test]
#[ignore]
fn frogtail_regen_walk() {
    let sch = Sched::from_text(SCHED);
    let mut b = B::new();
    let x = b.alloc_n(256);
    let w = alloc_walk(&mut b, &sch, &x);
    let dirty = b.alloc_n(64);
    let sc = Scr::alloc(&mut b, &dirty);
    init(&mut b, &w);
    let mut bounds = vec![b.ops.len()];
    for t in 1..=sch.t {
        let (p1, p2, p3) = rec_regen_tick(&mut b, &w, t, &sch, &sc);
        b.play(&p1, false);
        b.play(&p2, false);
        b.play(&p3, false);
        bounds.push(b.ops.len());
    }
    let fe = super::frogtail::rec_regen_close(&mut b, &w, &sch, &sc);
    b.play(&fe, false);
    bounds.push(b.ops.len());
    let mut rng = Rng::new(5);
    let xs: Vec<N> = (0..64)
        .map(|_| {
            let mut v = rng.below(256) % p();
            if v == N::ZERO {
                v = N::from(5u64);
            }
            if !v.bit(0) {
                v = p() - v;
            }
            v
        })
        .collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogtail-regen");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(
        (aq as usize).max(b.width() as usize),
        (nb as usize).max(1),
        &mut xof,
    );
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    s.apply_iter(b.ops[..bounds[0]].iter());
    let mut ms: Vec<M> = xs.iter().map(|&x| M::new(x)).collect();
    for t in 1..=sch.t {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for k in 0..64 {
            ms[k].tick(t, &sch);
            let got = get_u(&s.qubits, &w.q, k);
            assert_eq!(got, ms[k].q, "tick {t} shot {k}: Q");
        }
        assert_eq!(s.phase, 0, "tick {t}: phase");
    }
    s.apply_iter(b.ops[bounds[sch.t]..].iter());
    for k in 0..64 {
        assert_eq!(
            get_u(&s.qubits, &w.q, k),
            0,
            "shot {k}: Q after the closing step"
        );
    }
    assert_eq!(s.phase, 0, "closing step phase");
    eprintln!("regen walk ok");
}
