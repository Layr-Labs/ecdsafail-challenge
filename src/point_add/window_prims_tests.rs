//! Tests for window_prims: the tree's 64-shot simulator, every lane random before the gates (dirty content), the
//! registers overwritten with the case; after the gates EVERY lane must equal its expected value (registers that
//! change get their new value, all others - dirty pool, clean lanes at 0, controls, s, untouched words - must be
//! unchanged) and the phase must be 0 on every shot (measured uncomputes).
//!
//! Run: cargo test --release --offline --lib window_prims -- --nocapture --test-threads 4

use super::*;
use crate::point_add::prims_builder::B;
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn bits(&mut self, n: usize) -> u64 { if n >= 64 { self.next() } else { self.next() & ((1u64 << n) - 1) } }
}
fn m(n: usize) -> u64 { if n >= 64 { u64::MAX } else { (1u64 << n) - 1 } }
fn inv(a: u64, n: usize) -> u64 { inv2k(a, n.max(1)) & m(n) }

type Asg = Vec<(Vec<Q>, u64)>;
struct Case { ini: Asg, fin: Asg }

fn put(st: &mut [u64], reg: &[Q], v: u64, s: usize) {
    for (i, q) in reg.iter().enumerate() {
        let bit = 1u64 << s;
        if (v >> i) & 1 == 1 { st[q.0 as usize] |= bit } else { st[q.0 as usize] &= !bit }
    }
}

/// Simulate `b.ops` on the cases (64 per batch). Returns the number of failing cases.
fn run_cases(b: &B, cases: &[Case], rng: &mut Rng, tag: &str) -> u64 {
    let w = b.width() as usize;
    let mut bad = 0;
    for (ci, chunk) in cases.chunks(64).enumerate() {
        let mut h = sha3::Shake256::default();
        h.update(tag.as_bytes());
        h.update(&(ci as u64).to_le_bytes());
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(w, 1, &mut xof);
        for q in 0..w { sim.qubits[q] = rng.next(); }
        for (s, c) in chunk.iter().enumerate() { for (reg, v) in &c.ini { put(&mut sim.qubits, reg, *v, s); } }
        let mut want = sim.qubits.clone();
        for (s, c) in chunk.iter().enumerate() { for (reg, v) in &c.fin { put(&mut want, reg, *v, s); } }
        sim.apply_iter(b.ops.iter());
        for s in 0..chunk.len() {
            let diff = (0..w).any(|q| ((sim.qubits[q] ^ want[q]) >> s) & 1 == 1) || (sim.phase >> s) & 1 == 1;
            if diff {
                bad += 1;
                if bad <= 3 && tag != "mut" && tag != "phase" { eprintln!("FAIL {tag} batch {ci} shot {s}"); }
            }
        }
    }
    bad
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind { Py, Fast, Clean }
const KINDS: [Kind; 3] = [Kind::Py, Kind::Fast, Kind::Clean];

/// Lanes for one build: registers allocated in order, plus `ncl` clean lanes for Cfg::clean.
struct Lay { b: B, cl: Vec<Q> }
impl Lay {
    fn new() -> Self { Lay { b: B::new(), cl: vec![] } }
    fn r(&mut self, n: usize) -> Vec<Q> { self.b.alloc_n(n) }
    fn q(&mut self) -> Q { self.b.alloc() }
    fn clean(&mut self, kind: Kind, n: usize) { if kind == Kind::Clean { self.cl = self.b.alloc_n(n); } }
}
fn cfg_of<'a>(kind: Kind, cl: &'a [Q]) -> Cfg<'a> {
    match kind { Kind::Py => Cfg::PY, Kind::Fast => Cfg::FAST, Kind::Clean => Cfg { clean: cl, fast: true } }
}
fn zero(cl: &[Q]) -> Asg { if cl.is_empty() { vec![] } else { vec![(cl.to_vec(), 0)] } }

fn sizes_ex() -> Vec<usize> { vec![1, 2, 3, 4] }
fn sizes_rnd() -> Vec<usize> { vec![5, 6, 7, 8, 9, 12, 16, 24, 28] }

// ------------------------------------------------------------------ primitives (t_prims.py)
#[test]
fn prims() {
    let mut rng = Rng(1);
    let mut fails = 0;
    let mut total = 0;
    let kc = (P256_LO | 1) as u64;
    for n in sizes_ex().into_iter().chain(sizes_rnd()) {
        let ex = n <= 4;
        let mm = 1u64 << n;
        for kind in KINDS {
            // name, builder, expected (x, y, c, e) -> (new b, new z flip); x = a value, y = b value, e = extra reg
            type Exp = fn(u64, u64, u64, u64, usize, u64) -> Option<(u64, u64)>;
            let prims: Vec<(&str, Exp)> = vec![
                ("add", |x, y, _, _, n, _| Some(((x + y) & m(n), 0))),
                ("addz", |x, y, _, _, n, _| Some(((x + y) & m(n), (x + y) >> n))),
                ("cadd", |x, y, c, _, n, _| Some(((y + c * x) & m(n), 0))),
                ("inc", |_, y, _, _, n, _| Some(((y + 1) & m(n), 0))),
                ("const_add", |_, y, _, _, n, k| Some((y.wrapping_add(k) & m(n), 0))),
                ("c_const_add", |_, y, c, _, n, k| Some((y.wrapping_add(c * k) & m(n), 0))),
                ("neg", |_, y, _, _, n, _| Some((y.wrapping_neg() & m(n), 0))),
                ("mac", |x, y, _, e, n, _| Some((y.wrapping_add(x.wrapping_mul(e)) & m(n), 0))),
                ("add_p", |x, y, _, _, n, _| { if n < 2 { return None; } let a = x & m(n - 1); Some(((y + a) & m(n), (y + a) >> n)) }),
                ("cadd_p", |x, y, c, _, n, _| { if n < 2 { return None; } Some(((y + c * (x & 1)) & m(n), 0)) }),
                ("cc_add_p", |x, y, c, e, n, _| Some(((y + c * (e & 1) * (x & m((n + 1) / 2))) & m(n), 0))),
                ("constmul", |_, y, _, _, n, k| Some((y.wrapping_mul(k) & m(n), 0))),
                ("constmul14", |_, y, _, _, n, k| { let k = if k & 3 == 3 { k.wrapping_neg() } else { k }; Some((y.wrapping_mul(k) & m(n), 0)) }),
                ("mul1p3", |_, y, _, _, n, _| Some((y.wrapping_mul(9) & m(n), 0))),
                ("imul", |x, y, _, _, n, _| if x & 1 == 1 { Some((x.wrapping_mul(y) & m(n), 0)) } else { None }),
                ("idiv", |x, y, _, _, n, _| if x & 1 == 1 { Some((y.wrapping_mul(inv(x, n)) & m(n), 0)) } else { None }),
                ("imul_short", |x, y, _, _, n, _| { let h = (n / 2).max(1); let xs = x & m(h); if xs & 1 == 1 { Some((xs.wrapping_mul(y) & m(n), 0)) } else { None } }),
                ("cimul", |x, y, c, _, n, _| if x & 1 == 1 { Some((if c == 1 { x.wrapping_mul(y) } else { y } & m(n), 0)) } else { None }),
                ("cidiv", |x, y, c, _, n, _| if x & 1 == 1 { Some((if c == 1 { y.wrapping_mul(inv(x, n)) } else { y } & m(n), 0)) } else { None }),
            ];
            for (name, exp) in prims {
                let mut l = Lay::new();
                let a = l.r(n);
                let bb = l.r(n);
                let c = l.q();
                let z = l.q();
                let e = l.r(n);
                let pool = l.r(2 * n + 4);
                l.clean(kind, 2 * n + 2);
                let cl = l.cl.clone();
                let cf = cfg_of(kind, &cl);
                let b = &mut l.b;
                let k = if name == "constmul14" { let k = kc & m(n); if k & 3 == 3 { k.wrapping_neg() & m(n) } else { k } } else { kc & m(n) };
                match name {
                    "add" => add(b, cf, &a, &bb, None),
                    "addz" => add(b, cf, &a, &bb, Some(z)),
                    "cadd" => cadd(b, cf, c, &a, &bb),
                    "inc" => inc(b, cf, &bb, &pool),
                    "const_add" => const_add(b, cf, &bb, k, &pool),
                    "c_const_add" => c_const_add(b, cf, c, &bb, k, &pool),
                    "neg" => neg(b, cf, &bb, &pool),
                    "mac" => mac(b, cf, &bb, &a, &e, &pool),
                    "add_p" => { if n >= 2 { add_p(b, cf, &a[..n - 1], &bb, &pool, Some(z)) } }
                    "cadd_p" => { if n >= 2 { cadd_p(b, cf, c, &a[..1], &bb, &pool) } }
                    "cc_add_p" => cc_add_p(b, cf, c, e[0], &a[..(n + 1) / 2], &bb, &pool),
                    "constmul" => constmul(b, cf, &bb, k, &pool),
                    "constmul14" => constmul14(b, cf, &bb, k, &pool),
                    "mul1p3" => { mul1p(b, cf, &bb, 3, &pool); }
                    "imul" => imul(b, cf, &bb, &a, &pool, 0),
                    "idiv" => idiv(b, cf, &bb, &a, &pool),
                    "imul_short" => imul(b, cf, &bb, &a[..(n / 2).max(1)], &pool, 0),
                    "cimul" => cimul(b, cf, c, &bb, &a, &pool),
                    "cidiv" => cidiv(b, cf, c, &bb, &a, &pool),
                    _ => unreachable!(),
                }
                let tof = b.tof;
                let mut cases = vec![];
                let mut gen = |x: u64, y: u64, cc: u64, ee: u64, zz: u64| {
                    let kk = if name == "constmul14" { k } else { kc & m(n) };
                    let kk = if name == "mul1p3" && n <= 3 { kk } else { kk };
                    if let Some((nb, zf)) = exp(x, y, cc, ee, n, kk) {
                        let mut ini = vec![(a.clone(), x), (bb.clone(), y), (vec![c], cc), (vec![z], zz), (e.clone(), ee)];
                        ini.extend(zero(&cl));
                        let fin = vec![(bb.clone(), nb), (vec![z], zz ^ zf)];
                        cases.push(Case { ini, fin });
                    }
                };
                if ex {
                    for x in 0..mm { for y in 0..mm { for cc in 0..2 { for zz in 0..2 { let ee = rng.bits(n); gen(x, y, cc, ee, zz); } } } }
                } else {
                    for _ in 0..400 { let (x, y, cc, ee, zz) = (rng.bits(n), rng.bits(n), rng.bits(1), rng.bits(n), rng.bits(1)); gen(x | (name.starts_with("imul") || name.starts_with("idiv") || name.starts_with("ci")) as u64, y, cc, ee, zz); }
                }
                // mul1p3 = multiply by 1 + 2^3: expected 9 only when the factor exists (n > 3)
                if name == "mul1p3" && n <= 3 { cases.clear(); }
                let bad = run_cases(&l.b, &cases, &mut rng, name);
                total += cases.len();
                fails += bad;
                if bad > 0 { eprintln!("prim {name} n {n} {kind:?}: {bad} / {} bad", cases.len()); }
                // INV4 prims.log (Python counts, K = P256 | 1 mod 2^n)
                if kind == Kind::Py && (2..=7).contains(&n) {
                    let want: Option<u64> = match name {
                        "add" => Some(2 * n as u64 - 2),
                        "cadd" => Some(3 * n as u64 - 2),
                        "imul" => Some([1, 5, 12, 22, 35, 51][n - 2]),
                        "mac" => Some([5, 12, 22, 35, 51, 70][n - 2]),
                        "constmul" => Some([0, 2, 8, 18, 34, 58][n - 2]),
                        "const_add" => Some([4, 8, 12, 16, 24, 32][n - 2]),
                        _ => None,
                    };
                    if let Some(wv) = want { assert_eq!(tof, wv, "prim {name} n {n} count"); }
                }
            }
        }
    }
    eprintln!("prims: {total} cases, {fails} failures");
    assert_eq!(fails, 0);
}

// ------------------------------------------------------------------ invp (INV4 section 4)
thread_local! { static INVP_CASES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }
fn invp_check(n: usize, p: u64, kind: Kind, glimbs: usize, trials: Option<usize>, rng: &mut Rng) -> (usize, u64, u64) {
    let mut l = Lay::new();
    let x = l.r(n);
    let pool = l.r(2 * n + 8);
    let limbs = l.r(glimbs);
    l.clean(kind, 2 * n + 2);
    let cl = l.cl.clone();
    let cf = cfg_of(kind, &cl);
    invp(&mut l.b, cf, &x, &pool, p, &limbs);
    let tof = l.b.tof;
    let mut cases = vec![];
    let mut mk = |xv: u64| {
        let y = p.wrapping_mul(inv(xv, n)) & m(n);
        let mut ini = vec![(x.clone(), xv), (limbs.clone(), 0)];
        ini.extend(zero(&cl));
        cases.push(Case { ini, fin: vec![(x.clone(), y)] });
    };
    match trials {
        None => { for xv in (1..(1u64 << n)).step_by(2) { mk(xv); } }
        Some(t) => { for _ in 0..t { mk(rng.bits(n) | 1); } }
    }
    let bad = run_cases(&l.b, &cases, rng, "invp");
    INVP_CASES.with(|c| c.set(c.get() + cases.len()));
    (cases.len(), bad, tof)
}

#[test]
fn invp_all() {
    let mut rng = Rng(3);
    let mut fails = 0;
    let mut ps = vec![P256_LO];
    for _ in 0..5 { ps.push(rng.next() | 1); }
    for (pi, &p) in ps.iter().enumerate() {
        for kind in KINDS {
            for n in 2..=13usize {
                let (c, bad, tof) = invp_check(n, p, kind, 0, None, &mut rng);
                fails += bad;
                if bad > 0 { eprintln!("invp n {n} p#{pi} {kind:?}: {bad}/{c}"); }
                if pi == 0 && kind == Kind::Py && [5, 8, 9, 12].contains(&n) {
                    assert_eq!(tof, [96, 282, 388, 706][[5, 8, 9, 12].iter().position(|&v| v == n).unwrap()]);
                }
            }
            for n in [16usize, 20, 24, 25, 28, 32] {
                let (c, bad, tof) = invp_check(n, p, kind, 0, Some(640), &mut rng);
                fails += bad;
                if bad > 0 { eprintln!("invp n {n} p#{pi} {kind:?}: {bad}/{c}"); }
                if pi == 0 && kind == Kind::Py {
                    if let Some(i) = [16, 24, 32].iter().position(|&v| v == n) { assert_eq!(tof, [1308, 3056, 5510][i]); }
                }
            }
            // clean limbs (INV4's g): ceil(n/2) clean lanes
            for n in [4usize, 8, 12, 16, 24] {
                let (c, bad, _) = invp_check(n, p, kind, (n + 1) / 2, if n <= 4 { None } else { Some(320) }, &mut rng);
                fails += bad;
                if bad > 0 { eprintln!("invp limbs n {n} p#{pi} {kind:?}: {bad}/{c}"); }
            }
        }
    }
    eprintln!("invp: {} cases, {fails} failures", INVP_CASES.with(|c| c.get()));
    assert_eq!(fails, 0);
}

// ------------------------------------------------------------------ carry constructions (t_k.py, t_k2.py, t_b.py)
#[derive(Clone, Copy, Debug, PartialEq)]
enum Kc { K0, K1A, K1T, K2, K2g, K4, K1V }

/// One gate list per (construction, D, k, borrow, kind); cases exhaustive (trials None) or random. Returns
/// (cases, failures, Toffoli count).
fn kcheck(kc: Kc, d: usize, k: Option<usize>, borrow: bool, kind: Kind, p: u64, trials: Option<usize>, rng: &mut Rng)
          -> (usize, u64, u64) {
    let mut l = Lay::new();
    let a1 = l.r(d + 1);
    let b1 = l.r(d + 1);
    let t1 = l.r(d + 1);
    let s = l.r(d);
    let h = l.q();
    let ctrl = l.q();
    let t = l.q();
    let wc = l.r(d);
    let pool = l.r(3 * d + 8);
    let glimbs = if kc == Kc::K2g { l.r((d + 1) / 2) } else { vec![] };
    l.clean(kind, 2 * d + 4);
    let cl = l.cl.clone();
    let cf = cfg_of(kind, &cl);
    let pg = Page { a: &a1[..d], bw: &b1[..d], tb: &t1[..d] };
    let pg1 = Page1 { a1: &a1, b1: &b1, t1: &t1, h };
    let view = k.is_some();
    let kk = k.unwrap_or(0);
    let sv: &[Q] = if view { &t1[..d] } else { &s };
    {
        let b = &mut l.b;
        match kc {
            Kc::K0 => k0(b, cf, pg, sv, kk, ctrl, t, &wc, &pool, p, borrow),
            Kc::K1A => k1a(b, cf, pg, sv, kk, ctrl, t, &pool, p, borrow),
            Kc::K1T => k1t(b, cf, pg, &s, ctrl, t, &pool, p, borrow),
            Kc::K2 => k2(b, cf, pg, sv, kk, ctrl, t, &pool, p, borrow, &[]),
            Kc::K2g => k2(b, cf, pg, sv, kk, ctrl, t, &pool, p, borrow, &glimbs),
            Kc::K4 => k4(b, cf, pg1, &s, ctrl, t, &pool, p),
            Kc::K1V => k1v(b, cf, pg1, kk, ctrl, t, &pool, p, borrow),
        }
    }
    let tof = l.b.tof;
    let wide = matches!(kc, Kc::K4 | Kc::K1V);
    let wd = if wide { d + 1 } else { d };
    let mut cases = vec![];
    let mut mk = |av: u64, bv: u64, tv: u64, svv: u64, c: u64, rng: &mut Rng| {
        let (mut av, bv, mut tv) = (av, bv | 1, tv);
        match kc {
            Kc::K1A => tv |= 1,
            Kc::K1T => av |= 1,
            Kc::K1V => { if (av.wrapping_sub(bv << kk)) & 1 == 0 { av ^= 1; } }
            _ => {}
        }
        let q = p.wrapping_sub(av.wrapping_mul(tv)).wrapping_mul(inv(bv, wd)) & m(wd);
        let w = q & m(d);
        let hb = (q >> d) & 1;
        let sval = if view { (tv << kk) & m(d) } else { svv };
        let cbit = if borrow { (w < sval) as u64 } else { (w + sval) >> d };
        let tv0 = rng.bits(1);
        // full words random above the page bits (they must be untouched)
        let hi = |v: u64, r: &mut Rng| if wide { v } else { v | (r.bits(1) << d) };
        let mut ini = vec![(a1.clone(), hi(av, rng)), (b1.clone(), hi(bv, rng)), (t1.clone(), hi(tv, rng)), (s.clone(), svv),
                           (vec![ctrl], c), (vec![t], tv0), (wc.clone(), 0), (glimbs.clone(), 0)];
        if wide { ini.push((vec![h], hb)); }
        ini.extend(zero(&cl));
        cases.push(Case { ini, fin: vec![(vec![t], tv0 ^ (c & cbit))] });
    };
    let mw = 1u64 << wd;
    let ms = 1u64 << d;
    match trials {
        None => {
            for av in 0..mw { for bv in (1..mw).step_by(2) { for tv in 0..mw {
                let srange: Vec<u64> = if view || kc == Kc::K1V { vec![rng.bits(d)] } else { (0..ms).collect() };
                for &svv in &srange { for c in 0..2 {
                    let skip = match kc {
                        Kc::K1A => tv & 1 == 0,
                        Kc::K1T => av & 1 == 0,
                        Kc::K1V => (av.wrapping_sub(bv << kk)) & 1 == 0,
                        _ => false,
                    };
                    if !skip { mk(av, bv, tv, svv, c, rng); }
                } }
            } } }
        }
        Some(tr) => { for _ in 0..tr { let (av, bv, tv, svv, c) = (rng.bits(wd), rng.bits(wd), rng.bits(wd), rng.bits(d), rng.bits(1)); mk(av, bv, tv, svv, c, rng); } }
    }
    let bad = run_cases(&l.b, &cases, rng, "k");
    (cases.len(), bad, tof)
}

/// Every construction x {carry, borrow} x {own s, view 2^k tB for every k} x {PY, FAST, CLEAN}.
fn kmatrix(ds: &[usize], trials: Option<usize>, seed: u64, p: u64) -> u64 {
    let mut rng = Rng(seed);
    let mut fails = 0;
    let mut ncases = 0usize;
    let mut nlists = 0usize;
    for &d in ds {
        for kind in KINDS {
            for kc in [Kc::K0, Kc::K1A, Kc::K1T, Kc::K2, Kc::K2g, Kc::K4, Kc::K1V] {
                for borrow in [false, true] {
                    if borrow && matches!(kc, Kc::K4) { continue; }
                    let mut ks: Vec<Option<usize>> = vec![];
                    match kc {
                        Kc::K1T | Kc::K4 => ks.push(None),
                        Kc::K1V => ks.extend((0..d).map(Some)),
                        _ => { ks.push(None); ks.extend((0..d).map(Some)); }
                    }
                    // random mode: own s + a handful of view shifts (all k at D <= 9)
                    if trials.is_some() && d > 9 { let n = ks.len(); ks = ks.into_iter().enumerate().filter(|(i, _)| *i < 2 || *i == n - 1 || i % 7 == 3).map(|x| x.1).collect(); }
                    for &k in &ks {
                        let tr = trials.map(|t| if k.is_some() { (t / 4).max(64) } else { t });
                        let (c, bad, _) = kcheck(kc, d, k, borrow, kind, p, tr, &mut rng);
                        fails += bad;
                        ncases += c;
                        nlists += 1;
                        if bad > 0 { eprintln!("{kc:?} D {d} k {k:?} borrow {borrow} {kind:?}: {bad}/{c} bad"); }
                    }
                }
            }
        }
    }
    eprintln!("kmatrix D {ds:?} trials {trials:?}: {nlists} gate lists, {ncases} cases, {fails} failures");
    fails
}

#[test]
fn k_exhaustive() {
    let f = kmatrix(&[2, 3, 4], None, 5, P256_LO);
    assert_eq!(f, 0);
}

#[test]
fn k_random() {
    let f = kmatrix(&[5, 8, 9, 12, 16, 24, 28], Some(640), 7, P256_LO);
    assert_eq!(f, 0);
}

#[test]
fn k_other_moduli() {
    let mut rng = Rng(99);
    let mut f = 0;
    for _ in 0..4 {
        let p = rng.next() | 1;
        f += kmatrix(&[3], None, rng.next(), p);
        f += kmatrix(&[7, 12], Some(128), rng.next(), p);
    }
    assert_eq!(f, 0);
}

// ------------------------------------------------------------------ add_implicit, aff_switch
#[test]
fn implicit_and_switch() {
    let mut rng = Rng(11);
    let mut fails = 0;
    let p = P256_LO;
    for d in [2usize, 3, 4, 8, 9, 12, 16, 24, 28] {
        let ex = d <= 3;
        for kind in KINDS {
            // add_implicit: E (len d + 3) += +-ctrl 2^j W
            for car in [Carrier::K1A, Carrier::K2] {
                for (j, sub, ctl) in [(0usize, false, true), (1, true, true), (2, false, false), (3, true, false)] {
                    let mut l = Lay::new();
                    let a = l.r(d); let bw = l.r(d); let tb = l.r(d); let e = l.r(d + 3); let c = l.q();
                    let pool = l.r(3 * d + 8);
                    l.clean(kind, 2 * d + 4);
                    let cl = l.cl.clone();
                    let cf = cfg_of(kind, &cl);
                    add_implicit(&mut l.b, cf, car, Page { a: &a, bw: &bw, tb: &tb }, &e, j, if ctl { Some(c) } else { None }, sub, &pool, p);
                    let mm = 1u64 << d;
                    let mut cases = vec![];
                    let mut mk = |av: u64, bv: u64, tv: u64, ev: u64, cv: u64| {
                        let tv = if car == Carrier::K1A { tv | 1 } else { tv };
                        let w = p.wrapping_sub(av.wrapping_mul(tv)).wrapping_mul(inv(bv | 1, d)) & m(d);
                        let on = if ctl { cv } else { 1 };
                        let delta = (on * w) << j;
                        let en = if sub { ev.wrapping_sub(delta) } else { ev.wrapping_add(delta) } & m(d + 3);
                        let mut ini = vec![(a.clone(), av), (bw.clone(), bv | 1), (tb.clone(), tv), (e.clone(), ev), (vec![c], cv)];
                        ini.extend(zero(&cl));
                        cases.push(Case { ini, fin: vec![(e.clone(), en)] });
                    };
                    if ex {
                        for av in 0..mm { for bv in (1..mm).step_by(2) { for tv in 0..mm { for cv in 0..2 { let ev = rng.bits(d + 3); mk(av, bv, tv, ev, cv); } } } }
                    } else {
                        for _ in 0..256 { let v = (rng.bits(d), rng.bits(d), rng.bits(d), rng.bits(d + 3), rng.bits(1)); mk(v.0, v.1, v.2, v.3, v.4); }
                    }
                    let bad = run_cases(&l.b, &cases, &mut rng, "impl");
                    fails += bad;
                    if bad > 0 { eprintln!("add_implicit {car:?} D {d} j {j} sub {sub} ctl {ctl} {kind:?}: {bad}/{}", cases.len()); }
                }
            }
            // aff_switch Z -> (p - X Z) / Y; and the relation-level check: (a, b, tb) explicit, ta implicit -> tb implicit
            {
                let mut l = Lay::new();
                let z = l.r(d); let x = l.r(d); let y = l.r(d);
                let pool = l.r(2 * d + 6);
                l.clean(kind, 2 * d + 4);
                let cl = l.cl.clone();
                let cf = cfg_of(kind, &cl);
                aff_switch(&mut l.b, cf, &z, &x, &y, &pool, p);
                let mut cases = vec![];
                let mm = 1u64 << d;
                let mut mk = |zv: u64, xv: u64, yv: u64| {
                    let (xv, yv) = (xv | 1, yv | 1);
                    let zn = p.wrapping_sub(xv.wrapping_mul(zv)).wrapping_mul(inv(yv, d)) & m(d);
                    let mut ini = vec![(z.clone(), zv), (x.clone(), xv), (y.clone(), yv)];
                    ini.extend(zero(&cl));
                    cases.push(Case { ini, fin: vec![(z.clone(), zn)] });
                };
                if d <= 4 { for zv in 0..mm { for xv in (1..mm).step_by(2) { for yv in (1..mm).step_by(2) { mk(zv, xv, yv); } } } }
                else { for _ in 0..512 { mk(rng.bits(d), rng.bits(d), rng.bits(d)); } }
                let bad = run_cases(&l.b, &cases, &mut rng, "aff");
                fails += bad;
                if bad > 0 { eprintln!("aff_switch D {d} {kind:?}: {bad}/{}", cases.len()); }
            }
        }
    }
    assert_eq!(fails, 0);
}

// ------------------------------------------------------------------ counts (INV4 tables) and the optimised configs
fn kcount(kc: Kc, d: usize, k: Option<usize>, borrow: bool, kind: Kind) -> u64 {
    let mut rng = Rng(0);
    kcheck(kc, d, k, borrow, kind, P256_LO, Some(0), &mut rng).2
}

#[test]
fn counts() {
    let ds = [5usize, 8, 9, 12, 16, 24, 28];
    // INV4 section 5 (Python gate lists), D = 5, 8, 9, 12, 16, 24
    let inv4: [(Kc, [u64; 6]); 6] = [
        (Kc::K0, [134, 356, 454, 820, 1476, 3364]),
        (Kc::K1A, [108, 344, 452, 856, 1584, 3616]),
        (Kc::K1T, [108, 344, 452, 856, 1584, 3616]),
        (Kc::K1V, [175, 455, 575, 1023, 1799, 3927]),
        (Kc::K4, [293, 717, 897, 1561, 2709, 5869]),
        (Kc::K2, [326, 920, 1230, 2232, 4092, 9476]),
    ];
    for (kc, want) in &inv4 {
        for (i, &d) in ds[..6].iter().enumerate() {
            let k = if *kc == Kc::K1V { Some(0) } else { None };
            assert_eq!(kcount(*kc, d, k, false, Kind::Py), want[i], "{kc:?} D {d}");
        }
    }
    eprintln!("| construction | config | {} | CCX/D^2 at 28 |", ds.iter().map(|d| format!("D={d}")).collect::<Vec<_>>().join(" | "));
    for kc in [Kc::K0, Kc::K1A, Kc::K1T, Kc::K1V, Kc::K4, Kc::K2] {
        for kind in KINDS {
            for borrow in [false, true] {
                if borrow && kc == Kc::K4 { continue; }
                let v: Vec<u64> = ds.iter().map(|&d| kcount(kc, d, if kc == Kc::K1V { Some(0) } else { None }, borrow, kind)).collect();
                eprintln!("| {kc:?}{} | {kind:?} | {} | {:.2} |", if borrow { " borrow" } else { "" },
                          v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" | "), *v.last().unwrap() as f64 / 784.0);
            }
        }
    }
    // primitives at n = D
    eprintln!("| primitive | config | {} |", ds.iter().map(|d| format!("n={d}")).collect::<Vec<_>>().join(" | "));
    for name in ["add", "cadd", "imul", "cimul", "mac", "inc", "const_add p+1", "constmul14 -p", "invp", "aff_switch", "carry_toggle", "add_implicit K1A", "add_implicit K2"] {
        for kind in KINDS {
            let v: Vec<u64> = ds.iter().map(|&n| {
                let mut l = Lay::new();
                let a = l.r(n); let r = l.r(n); let e = l.r(n); let c = l.q(); let t = l.q(); let big = l.r(n + 4);
                let pool = l.r(3 * n + 8);
                l.clean(kind, 2 * n + 4);
                let cl = l.cl.clone();
                let cf = cfg_of(kind, &cl);
                let b = &mut l.b;
                let pg = Page { a: &a, bw: &r, tb: &e };
                match name {
                    "add" => add(b, cf, &a, &r, None),
                    "cadd" => cadd(b, cf, c, &a, &r),
                    "imul" => imul(b, cf, &r, &a, &pool, 0),
                    "cimul" => cimul(b, cf, c, &r, &a, &pool),
                    "mac" => mac(b, cf, &r, &a, &e, &pool),
                    "inc" => inc(b, cf, &r, &pool),
                    "const_add p+1" => const_add(b, cf, &r, P256_LO.wrapping_add(1), &pool),
                    "constmul14 -p" => constmul14(b, cf, &r, P256_LO.wrapping_neg(), &pool),
                    "invp" => invp(b, cf, &r, &pool, P256_LO, &[]),
                    "aff_switch" => aff_switch(b, cf, &r, &a, &e, &pool, P256_LO),
                    "carry_toggle" => carry_toggle(b, cf, &r, &a, 0, c, t, pool[0], false),
                    "add_implicit K1A" => add_implicit(b, cf, Carrier::K1A, pg, &big, 0, Some(c), false, &pool, P256_LO),
                    "add_implicit K2" => add_implicit(b, cf, Carrier::K2, pg, &big, 0, Some(c), false, &pool, P256_LO),
                    _ => unreachable!(),
                }
                b.tof
            }).collect();
            eprintln!("| {name} | {kind:?} | {} |", v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" | "));
        }
    }
}

/// The rig must see faults: drop single gates / flip single lanes of a K2 and a clean-config K1A gate list and expect
/// failures (whole-state check), and a phase fault (CZ added) must fail too.
#[test]
fn rig_detects_faults() {
    use crate::circuit::{Op, OperationType};
    let mut rng = Rng(77);
    for (kc, kind) in [(Kc::K2, Kind::Py), (Kc::K1A, Kind::Clean), (Kc::K1V, Kind::Fast)] {
        let d = 4;
        let mut l = Lay::new();
        let a1 = l.r(d + 1); let b1 = l.r(d + 1); let t1 = l.r(d + 1); let h = l.q(); let ctrl = l.q(); let t = l.q();
        let pool = l.r(3 * d + 8);
        l.clean(kind, 2 * d + 4);
        let cl = l.cl.clone();
        let cf = cfg_of(kind, &cl);
        let pg = Page { a: &a1[..d], bw: &b1[..d], tb: &t1[..d] };
        match kc {
            Kc::K2 => k2(&mut l.b, cf, pg, &t1[..d], 1, ctrl, t, &pool, P256_LO, false, &[]),
            Kc::K1A => k1a(&mut l.b, cf, pg, &t1[..d], 0, ctrl, t, &pool, P256_LO, true),
            _ => k1v(&mut l.b, cf, Page1 { a1: &a1, b1: &b1, t1: &t1, h }, 2, ctrl, t, &pool, P256_LO, false),
        }
        let good = l.b.ops.clone();
        let mk = |rng: &mut Rng| -> Vec<Case> {
            (0..256).map(|_| {
                let wide = kc == Kc::K1V;
                let wd = if wide { d + 1 } else { d };
                let (mut av, bv, mut tv, c) = (rng.bits(wd), rng.bits(wd) | 1, rng.bits(wd), rng.bits(1));
                let k = match kc { Kc::K2 => 1, Kc::K1A => 0, _ => 2 };
                if kc == Kc::K1A { tv |= 1; }
                if kc == Kc::K1V && (av.wrapping_sub(bv << k)) & 1 == 0 { av ^= 1; }
                let q = P256_LO.wrapping_sub(av.wrapping_mul(tv)).wrapping_mul(inv(bv, wd)) & m(wd);
                let w = q & m(d);
                let sval = (tv << k) & m(d);
                let cb = if kc == Kc::K1A { (w < sval) as u64 } else { (w + sval) >> d };
                let tv0 = rng.bits(1);
                let mut ini = vec![(a1[..wd].to_vec(), av), (b1[..wd].to_vec(), bv), (t1[..wd].to_vec(), tv), (vec![ctrl], c), (vec![t], tv0)];
                if wide { ini.push((vec![h], q >> d)); }
                ini.extend(zero(&cl));
                Case { ini, fin: vec![(vec![t], tv0 ^ (c & cb))] }
            }).collect()
        };
        let cases = mk(&mut rng);
        assert_eq!(run_cases(&l.b, &cases, &mut rng, "good"), 0);
        let mut caught = 0;
        let mut tried = 0;
        let n = good.len();
        for trial in 0..40 {
            let i = (rng.next() as usize) % n;
            let mut ops = good.clone();
            let op = ops[i];
            if !matches!(op.kind, OperationType::CCX | OperationType::CX | OperationType::X) { continue; }
            if trial % 2 == 0 { ops.remove(i); } else {
                // retarget onto another lane of the same build
                let mut o = op; o.q_target = pool[(rng.next() as usize) % pool.len()];
                if o.q_target == op.q_control1 || o.q_target == op.q_control2 { continue; }
                ops[i] = o;
            }
            tried += 1;
            l.b.ops = ops;
            if run_cases(&l.b, &cases, &mut rng, "mut") > 0 { caught += 1; }
        }
        // phase fault: a CZ between two lanes that are 1 together on some shots
        let mut ops = good.clone();
        ops.push(Op { kind: OperationType::CZ, q_target: t1[0], q_control1: a1[0], ..Op::empty() });
        l.b.ops = ops;
        let ph = run_cases(&l.b, &cases, &mut rng, "phase");
        eprintln!("rig {kc:?} {kind:?}: {caught}/{tried} single-gate mutations caught, phase fault fails {ph}/256");
        assert!(ph > 0);
        assert!(caught * 10 >= tried * 9, "rig too weak");
    }
}

/// Clean-lane budget sweep: g clean lanes given to the adders (Cfg::clean, fast on) or, for K2, to invp as clean limbs
/// (INV4's g, dirty adders). Counts only (the configs are verified by the matrix tests: their code paths are the
/// same per adder size; the sweep is re-verified at D = 9 and 16 below).
#[test]
fn counts_gsweep() {
    let mut rng = Rng(5);
    let ds = [8usize, 9, 12, 16, 24, 28];
    eprintln!("| construction | g clean | {} |", ds.iter().map(|d| format!("D={d}")).collect::<Vec<_>>().join(" | "));
    for name in ["K1A", "K1V", "K2", "K2 limbs", "invp", "aff_switch", "imul", "cimul"] {
        for gsel in ["0", "1", "2", "4", "8", "D/2", "D", "2D-1"] {
            let mut v = vec![];
            for &d in &ds {
                let g = match gsel { "D/2" => (d + 1) / 2, "D" => d, "2D-1" => 2 * d - 1, s => s.parse().unwrap() };
                if name == "K2 limbs" && g > (d + 1) / 2 * 2 { v.push("-".to_string()); continue; }
                let mut l = Lay::new();
                let a1 = l.r(d + 1); let b1 = l.r(d + 1); let t1 = l.r(d + 1); let h = l.q(); let ctrl = l.q(); let t = l.q();
                let pool = l.r(3 * d + 8);
                let gl = l.r(g);
                let fast = Cfg { clean: if name == "K2 limbs" { &[] } else { &gl }, fast: true };
                let pg = Page { a: &a1[..d], bw: &b1[..d], tb: &t1[..d] };
                let b = &mut l.b;
                match name {
                    "K1A" => k1a(b, fast, pg, &t1[..d], 1, ctrl, t, &pool, P256_LO, false),
                    "K1V" => k1v(b, fast, Page1 { a1: &a1, b1: &b1, t1: &t1, h }, 1, ctrl, t, &pool, P256_LO, false),
                    "K2" => k2(b, fast, pg, &t1[..d], 1, ctrl, t, &pool, P256_LO, false, &[]),
                    "K2 limbs" => k2(b, fast, pg, &t1[..d], 1, ctrl, t, &pool, P256_LO, false, &gl),
                    "invp" => invp(b, fast, &b1[..d], &pool, P256_LO, &[]),
                    "imul" => imul(b, fast, &b1[..d], &a1[..d], &pool, 0),
                    "cimul" => cimul(b, fast, ctrl, &b1[..d], &a1[..d], &pool),
                    _ => aff_switch(b, fast, &a1[..d], &b1[..d], &t1[..d], &pool, P256_LO),
                }
                v.push(b.tof.to_string());
                // re-verify the swept gate lists at two sizes (K constructions, view k = 1)
                if (d == 9 || d == 16) && name.starts_with('K') {
                    let kk = 1;
                    let wide = name == "K1V";
                    let wd = if wide { d + 1 } else { d };
                    let cases: Vec<Case> = (0..192).map(|_| {
                        let (mut av, bv, mut tv, c) = (rng.bits(wd), rng.bits(wd) | 1, rng.bits(wd), rng.bits(1));
                        if name == "K1A" { tv |= 1; }
                        if wide && (av.wrapping_sub(bv << kk)) & 1 == 0 { av ^= 1; }
                        let q = P256_LO.wrapping_sub(av.wrapping_mul(tv)).wrapping_mul(inv(bv, wd)) & m(wd);
                        let w = q & m(d);
                        let cb = (w + ((tv << kk) & m(d))) >> d;
                        let tv0 = rng.bits(1);
                        let mut ini = vec![(a1[..wd].to_vec(), av), (b1[..wd].to_vec(), bv), (t1[..wd].to_vec(), tv), (vec![ctrl], c), (vec![t], tv0)];
                        if wide { ini.push((vec![h], q >> d)); }
                        ini.extend(zero(&gl));
                        Case { ini, fin: vec![(vec![t], tv0 ^ (c & cb))] }
                    }).collect();
                    assert_eq!(run_cases(&l.b, &cases, &mut rng, "sweep"), 0, "{name} D {d} g {g}");
                }
            }
            eprintln!("| {name} | {gsel} | {} |", v.join(" | "));
        }
    }
}
