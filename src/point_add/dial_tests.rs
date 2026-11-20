//! dial768: exhaustive unit tests of the K2-half arithmetic of the sandwich at the page widths the dial builds (D = 3..12).
//! Every block is built exactly as sandwich_x calls it (same functions, same clean / dirty lane roles, HYB on as in the
//! sandwich), simulated on the tree's 64-shot simulator with EVERY lane random before the gates (dirty content), the
//! registers then overwritten with the case. After the gates every lane must equal its expected value (registers that
//! change get the reference value, every other lane - dirty pool, catalyst, clean lanes at 0 - must be unchanged) and the
//! phase must be 0 on every shot (the measured uncomputes of the AND markers are simulated as measurements).
//!
//! Run: cargo test --release --bin build_circuit -- dial_ --show-output
//!
//! dial_k2_hop_ab      hop2::hop_ab (idiv: idiv_sgn2; inverse: invp11 at 11, cat_invp parked elsewhere), all va x all odd vb
//! dial_k2_hop_c       hop2::hop_c (mac_sgn at 11, wp::mac elsewhere), all (va, sc), random vb
//! dial_k2_pconv_cv    hop2::pconv_cv (cv_conj at 11, cimul form elsewhere), c = 1: all odd va x all sc; c = 0: all va x all sc
//! dial_k2_msub        hop2::msub_sgn_g (S4) at every (n, J) the dial reaches, all (g, a, y), random r
//! dial_x1_idiv_sgn2   window_prims::idiv_sgn2 (X1) alone with exactly 2 clean lanes, all (R, odd x), n = 3..12
//! dial_s6a_barrel     s6a_bar (S6a, generalised) against the per-class remap loops, D = 3..12, every class 10..24, both
//!                     class-set spans (E_max 17 and 24), acting and non-acting shots, and rev(bar) = the inverse
//! dial_h1_12          hop2::invp12 (H1 at 12 bits) on all 2,048 odd x, 16 random dirty states each, forward and its gate
//!                     reverse (x -> P / x is an involution, so both must give P / x), plus invp11 the same way at 11 bits
//! dial_h1_lo          hop2::invp_lo (H1 at D = 6..10) the same way: every odd x, 16 dirty states, forward and reverse
//! The Toffoli count of each block per width is printed (DIALTOF lines).

use super::hop2;
use super::prims_builder::B;
use super::window_prims::{self as wp, Cfg, P256_LO};
use crate::circuit::QubitId as Q;
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
fn inv(a: u64, n: usize) -> u64 { wp::inv2k(a, n.max(1)) & m(n) }

type Asg = Vec<(Vec<Q>, u64)>;
struct Case { ini: Asg, fin: Asg }

fn put(st: &mut [u64], reg: &[Q], v: u64, s: usize) {
    for (i, q) in reg.iter().enumerate() {
        let bit = 1u64 << s;
        if (v >> i) & 1 == 1 { st[q.0 as usize] |= bit } else { st[q.0 as usize] &= !bit }
    }
}

/// Simulate `b.ops` on the cases (64 per batch). Returns the number of failing cases (value on any lane, or phase).
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
        // one mask per batch: bit s = shot s differs on some lane or has a phase
        let mut dm = sim.phase;
        for q in 0..w { dm |= sim.qubits[q] ^ want[q]; }
        if chunk.len() < 64 { dm &= (1u64 << chunk.len()) - 1; }
        if dm != 0 {
            if bad < 3 { eprintln!("FAIL {tag} batch {ci} shots mask {dm:#018x}"); }
            bad += dm.count_ones() as u64;
        }
    }
    bad
}

/// streaming form (no case vector for the big widths): cases come from `gen` in blocks of 64 * 1024
fn run_gen(b: &B, total: u64, gen: &mut dyn FnMut(u64) -> Case, rng: &mut Rng, tag: &str) -> u64 {
    let blk = 64 * 1024u64;
    let mut bad = 0;
    let mut i = 0u64;
    let cap: u64 = std::env::var("DIAL_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(u64::MAX);
    let (cnt, samp) = if total > cap { (cap, true) } else { (total, false) };
    if samp { eprintln!("DIALSAMPLE {tag}: {cnt} of {total} cases (uniform + corners)"); }
    let mut rs = Rng(0x5a3e ^ total);
    let mut idx = move |k: u64| -> u64 { if !samp { k } else { match k { 0 => 0, 1 => 1, 2 => total - 2, 3 => total - 1, _ => rs.next() % total } } };
    let total = cnt;
    while i < total {
        let e = (i + blk).min(total);
        let cases: Vec<Case> = (i..e).map(|k| gen(idx(k))).collect();
        bad += run_cases(b, &cases, rng, &format!("{tag}@{i}"));
        i = e;
    }
    bad
}

const WIDTHS_DEF: [usize; 10] = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
/// Ufezuegle: env DIAL_WIDTHS="17,18,19" picks other widths (default the parent's 3..12, exhaustive); env DIAL_CAP = n caps
/// every (test, width) at n cases drawn uniformly from the exhaustive index range plus its corners (0, 1, total - 2, total - 1):
/// SAMPLED, not exhaustive, above the cap. DIAL_MSUB="n:J,n:J" replaces the msub (n, J) list.
fn widths() -> Vec<usize> {
    std::env::var("DIAL_WIDTHS").ok().map(|v| v.split(',').map(|x| x.trim().parse().unwrap()).collect()).unwrap_or(WIDTHS_DEF.to_vec())
}

/// the K2 half's lane roles at page width n: VA, VB, SC (n each), catalyst gd = passenger 1..n (n - 1), pool = passenger
/// n..64 (64 - n, dirty), cfk = the two clean lanes [z, z2]
struct K2 { b: B, va: Vec<Q>, vb: Vec<Q>, sc: Vec<Q>, gd: Vec<Q>, pool: Vec<Q>, pas: Vec<Q>, cl: Vec<Q> }
fn k2(n: usize) -> K2 {
    let mut b = B::new();
    let va = b.alloc_n(n);
    let vb = b.alloc_n(n);
    let sc = b.alloc_n(n);
    let pas = b.alloc_n(64);
    let cl = b.alloc_n(2);
    let gd = pas[1..n].to_vec();
    let pool = pas[n..64].to_vec();
    K2 { b, va, vb, sc, gd, pool, pas, cl }
}

#[test]
fn dial_k2_hop_ab() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a1_0001);
    let mut fails = 0u64;
    for n in widths() {
        let mut k = k2(n);
        let cf = Cfg { clean: &k.cl, fast: false };
        let t0 = k.b.tof;
        hop2::hop_ab(&mut k.b, cf, &k.va, &k.vb, &k.gd, &k.pool, P256_LO, true);
        let tof = k.b.tof - t0;
        // invp11 (H1) leaves the catalyst alone; the parked cat_invp leaves it holding bits 1.. of X * G (G = 1 + 2 gd)
        let h1 = super::GM_INVP11 && (n == 11 || (n == 12 && super::DIAL_H1_12) || ((6..=10).contains(&n) && super::DIAL_H1_LO));
        let (va, vb, gd, cl) = (k.va.clone(), k.vb.clone(), k.gd.clone(), k.cl.clone());
        let total = (1u64 << n) * (1u64 << (n - 1));
        let mut r2 = Rng(0x5eed ^ n as u64);
        let mut gen = |i: u64| -> Case {
            let xv = ((i >> n) << 1) | 1;
            let av = i & m(n);
            let gv = r2.bits(n - 1);
            let ix = inv(xv, n);
            let gd2 = if h1 { gv } else { ((xv.wrapping_mul(1 + 2 * gv)) & m(n)) >> 1 };
            Case {
                ini: vec![(va.clone(), av), (vb.clone(), xv), (gd.clone(), gv), (cl.clone(), 0)],
                fin: vec![(va.clone(), av.wrapping_mul(ix) & m(n)), (vb.clone(), P256_LO.wrapping_mul(ix) & m(n)), (gd.clone(), gd2)],
            }
        };
        let bad = run_gen(&k.b, total, &mut gen, &mut rng, &format!("hop_ab{n}"));
        let inv_name = if !h1 { "cat_invp parked" } else if n == 11 { "invp11" } else if n == 12 { "invp12" } else { "invp_lo" };
        eprintln!("DIALTOF hop_ab n {n}: {total} cases, {bad} bad, tof {tof} (idiv_sgn2 + {inv_name})");
        fails += bad;
    }
    assert_eq!(fails, 0);
}

#[test]
fn dial_k2_hop_c() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a1_0002);
    let mut fails = 0u64;
    for n in widths() {
        let mut k = k2(n);
        let cf = Cfg { clean: &k.cl, fast: false };
        let t0 = k.b.tof;
        hop2::hop_c(&mut k.b, cf, &k.va, &k.vb, &k.sc, &k.pool);
        let tof = k.b.tof - t0;
        let (va, vb, sc, cl) = (k.va.clone(), k.vb.clone(), k.sc.clone(), k.cl.clone());
        let total = 1u64 << (2 * n);
        let mut r2 = Rng(0x5eed ^ n as u64);
        let mut gen = |i: u64| -> Case {
            let (av, sv, bv) = (i & m(n), i >> n, r2.bits(n));
            Case {
                ini: vec![(va.clone(), av), (vb.clone(), bv), (sc.clone(), sv), (cl.clone(), 0)],
                fin: vec![(vb.clone(), bv.wrapping_sub(av.wrapping_mul(sv)) & m(n))],
            }
        };
        let bad = run_gen(&k.b, total, &mut gen, &mut rng, &format!("hop_c{n}"));
        let path = if super::S2_SGN_MAC && (super::DIAL_SGN_ALLW || n == 11) { "mac_sgn (S2)" } else { "wp::mac" };
        eprintln!("DIALTOF hop_c n {n}: {total} cases, {bad} bad, tof {tof} ({path})");
        fails += bad;
    }
    assert_eq!(fails, 0);
}

#[test]
fn dial_k2_pconv_cv() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a1_0003);
    let mut fails = 0u64;
    for n in widths() {
        let mut k = k2(n);
        let c = k.b.alloc();
        let z = [k.cl[0]];
        let cfz = Cfg { clean: &z, fast: false };
        let t0 = k.b.tof;
        hop2::pconv_cv(&mut k.b, cfz, c, &k.va, &k.vb, &k.sc, &k.pas);
        let tof = k.b.tof - t0;
        let (va, vb, sc, zl) = (k.va.clone(), k.vb.clone(), k.sc.clone(), z.to_vec());
        // c = 1: va odd (the flag implies r odd), all (va, sc); c = 0: all (va, sc), SC unchanged
        let n1 = (1u64 << (n - 1)) * (1u64 << n);
        let total = n1 + (1u64 << (2 * n));
        let mut r2 = Rng(0x5eed ^ n as u64);
        let mut gen = |i: u64| -> Case {
            let bv = r2.bits(n);
            let (cv, av, sv) = if i < n1 { (1u64, ((i & m(n - 1)) << 1) | 1, i >> (n - 1)) } else { let j = i - n1; (0, j & m(n), j >> n) };
            let s2 = if cv == 1 { bv.wrapping_sub(av.wrapping_mul(sv)) & m(n) } else { sv };
            Case {
                ini: vec![(va.clone(), av), (vb.clone(), bv), (sc.clone(), sv), (vec![c], cv), (zl.clone(), 0)],
                fin: vec![(sc.clone(), s2)],
            }
        };
        let bad = run_gen(&k.b, total, &mut gen, &mut rng, &format!("pconv_cv{n}"));
        let path = if super::S3_CV_CONJ && (super::DIAL_SGN_ALLW || n == 11) { "cv_conj (S3)" } else { "cimul form" };
        eprintln!("DIALTOF pconv_cv n {n}: {total} cases, {bad} bad, tof {tof} ({path})");
        fails += bad;
    }
    assert_eq!(fails, 0);
}

#[test]
fn dial_k2_msub() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a1_0004);
    let mut fails = 0u64;
    // (n, J): odd11 at D = 3 (q has 2 digits); the big phase at D <= 10 (J = D); D = 11 (J = 10, 11); D = 12 (J = 11)
    let mut cfgs: Vec<(usize, usize)> = vec![(3, 2)];
    cfgs.extend((3..=10).map(|n| (n, n)));
    cfgs.extend([(11, 10), (11, 11), (12, 11)]);
    if let Ok(v) = std::env::var("DIAL_MSUB") { cfgs = v.split(',').map(|p| { let mut it = p.split(':'); (it.next().unwrap().trim().parse().unwrap(), it.next().unwrap().trim().parse().unwrap()) }).collect(); }
    for (n, jj) in cfgs {
        let mut b = B::new();
        let r = b.alloc_n(n);
        let a = b.alloc_n(jj);
        let y = b.alloc_n(n);
        let g = b.alloc();
        let w = b.alloc();
        let t0 = b.tof;
        hop2::msub_sgn_g(&mut b, g, w, &r, &a, &y);
        let tof = b.tof - t0;
        let total = 2u64 << (jj + n);
        let mut r2 = Rng(0x5eed ^ (n * 16 + jj) as u64);
        let mut gen = |i: u64| -> Case {
            let (gv, av, yv, rv) = (i & 1, (i >> 1) & m(jj), i >> (1 + jj), r2.bits(n));
            let r1 = if gv == 1 { rv.wrapping_sub(av.wrapping_mul(yv)) & m(n) } else { rv };
            Case {
                ini: vec![(r.clone(), rv), (a.clone(), av), (y.clone(), yv), (vec![g], gv), (vec![w], 0)],
                fin: vec![(r.clone(), r1)],
            }
        };
        let bad = run_gen(&b, total, &mut gen, &mut rng, &format!("msub{n}_{jj}"));
        eprintln!("DIALTOF msub n {n} J {jj}: {total} cases, {bad} bad, tof {tof}");
        fails += bad;
    }
    assert_eq!(fails, 0);
}

#[test]
fn dial_x1_idiv_sgn2() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a1_0005);
    let mut fails = 0u64;
    for n in widths() {
        let mut b = B::new();
        let x = b.alloc_n(n);
        let r = b.alloc_n(n);
        let cl = b.alloc_n(2);
        let cf = Cfg { clean: &cl, fast: false };
        let t0 = b.tof;
        wp::idiv_sgn2(&mut b, cf, &r, &x);
        let tof = b.tof - t0;
        let (xr, rr, clr) = (x.clone(), r.clone(), cl.clone());
        let total = (1u64 << n) * (1u64 << (n - 1));
        let mut gen = |i: u64| -> Case {
            let (rv, xv) = (i & m(n), ((i >> n) << 1) | 1);
            Case { ini: vec![(xr.clone(), xv), (rr.clone(), rv), (clr.clone(), 0)], fin: vec![(rr.clone(), rv.wrapping_mul(inv(xv, n)) & m(n))] }
        };
        let bad = run_gen(&b, total, &mut gen, &mut rng, &format!("idiv_sgn2_{n}"));
        eprintln!("DIALTOF idiv_sgn2 n {n}: {total} cases, {bad} bad, tof {tof}");
        fails += bad;
    }
    assert_eq!(fails, 0);
}

/// classical bit-sliced evaluation of a frame gate list (64 independent random assignments per lane word)
fn eval_gl(g: &[super::G], st: &mut [u64]) {
    for x in g {
        assert!(x.0 != super::MAC, "eval_gl: MAC macro in a unit-test list");
        if x.2 != super::NONE {
            let t = super::gl_loader::lane_of(x.2) as usize;
            st[t] ^= st[x.0 as usize] & st[x.1 as usize];
        } else if x.1 != super::NONE {
            st[x.1 as usize] ^= st[x.0 as usize];
        } else {
            st[x.0 as usize] = !st[x.0 as usize];
        }
    }
}

#[test]
fn dial_s6a_barrel() {
    let mut rng = Rng(0xd1a1_0006);
    let mut fails = 0u64;
    let mut checks = 0u64;
    for dd in widths() {
        for emax in [17usize, 24] {
            let ll = emax.max(dd);
            // lanes: span 0..ll (span[ll - D + i] = Q[i]), hb0 4, w0, cl 3, d, zb, dirty 64
            let span: Vec<u32> = (0..ll as u32).collect();
            let hb0: Vec<u32> = (ll as u32..ll as u32 + 4).collect();
            let w0 = ll as u32 + 4;
            let cl = [ll as u32 + 5, ll as u32 + 6, ll as u32 + 7];
            let (d, zb) = (ll as u32 + 8, ll as u32 + 9);
            let dirty: Vec<u32> = (ll as u32 + 10..ll as u32 + 74).collect();
            let nl = ll + 74;
            let bar = super::s6a_bar(&span, dd, &hb0, w0, cl, d, zb, &dirty);
            let tof = bar.iter().filter(|g| g.2 != super::NONE).count();
            let f0 = fails;
            for e in 10..=emax {
                for act in [true, false] {
                    let mut st: Vec<u64> = (0..nl).map(|_| rng.next()).collect();
                    for i in 0..4 { st[hb0[i] as usize] = if ((e >> 1) >> i) & 1 == 1 { u64::MAX } else { 0 }; }
                    st[w0 as usize] = if e & 1 == 1 { u64::MAX } else { 0 };
                    for (k, &c) in cl.iter().enumerate() { st[c as usize] = if act || k < 2 { u64::MAX } else { 0 }; }
                    st[d as usize] = 0;
                    st[zb as usize] = 0;
                    let st0 = st.clone();
                    // reference: the per-class remap of big_phase (class e >= D: rotate X[wv-e..wv-1] up by e - D; e < D: the
                    // top D lanes up by e), on a copy
                    let mut rf = st0.clone();
                    let rm = if e >= dd { super::rotate_up(zb, &span[ll - e..], e - dd) } else { super::rotate_up(zb, &span[ll - dd..], e) };
                    rf[zb as usize] = u64::MAX;
                    eval_gl(&rm, &mut rf);
                    let mut sb = st0.clone();
                    eval_gl(&bar, &mut sb);
                    let mut ok = true;
                    for i in 0..e.min(dd) {
                        let q = span[ll - dd + i] as usize;
                        let want = if act { st0[span[ll - e + i] as usize] } else { st0[q] };
                        if sb[q] != want { ok = false; }
                        if act && rf[q] != want { ok = false; }
                    }
                    if !act && sb[..ll] != st0[..ll] { ok = false; }
                    for &l in hb0.iter().chain([w0, d, zb].iter()).chain(cl.iter()).chain(dirty.iter()) {
                        if sb[l as usize] != st0[l as usize] { ok = false; }
                    }
                    // rev(bar) is its inverse on every lane
                    let mut sr = sb.clone();
                    eval_gl(&super::rev(&bar), &mut sr);
                    if sr != st0 { ok = false; }
                    checks += 1;
                    if !ok { fails += 1; if fails <= 5 { eprintln!("FAIL s6a D {dd} E_max {emax} e {e} act {act}"); } }
                }
            }
            eprintln!("DIALTOF s6a n {dd} E_max {emax}: {} cases, {} bad, tof {tof} (barrel, unit-test expansion of the hb0 decrements)", 2 * (emax - 9), fails - f0);
        }
    }
    eprintln!("s6a: {checks} checks, {fails} bad");
    assert_eq!(fails, 0);
}

#[test]
fn dial_h1_12() {
    let mut rng = Rng(0xd1a1_0007);
    let mut fails = 0u64;
    for (n, rev_) in [(11usize, false), (11, true), (12, false), (12, true)] {
        let mut b = B::new();
        let x = b.alloc_n(n);
        let cl = b.alloc_n(2);
        let pool = b.alloc_n(8);
        let t0 = b.tof;
        let f = |b: &mut B| if n == 11 { hop2::invp11(b, &cl, &x, &pool) } else { hop2::invp12(b, &cl, &x, &pool) };
        if rev_ { wp::undo(&mut b, f) } else { f(&mut b) }
        let tof = b.tof - t0;
        let (xr, clr) = (x.clone(), cl.clone());
        let reps = 16u64;
        let total = (1u64 << (n - 1)) * reps;
        let mut gen = |i: u64| -> Case {
            let xv = ((i / reps) << 1) | 1;
            Case { ini: vec![(xr.clone(), xv), (clr.clone(), 0)], fin: vec![(xr.clone(), P256_LO.wrapping_mul(inv(xv, n)) & m(n))] }
        };
        let bad = run_gen(&b, total, &mut gen, &mut rng, &format!("h1_{n}_{rev_}"));
        eprintln!("DIALTOF h1 n {n}{}: {total} cases, {bad} bad, tof {tof}", if rev_ { " reverse" } else { "" });
        fails += bad;
    }
    assert_eq!(fails, 0);
}

#[test]
fn dial_h1_lo() {
    let mut rng = Rng(0xd1a1_0008);
    let mut fails = 0u64;
    for n in 6..=10usize {
        for rev_ in [false, true] {
            let mut b = B::new();
            let x = b.alloc_n(n);
            let cl = b.alloc_n(2);
            let pool = b.alloc_n(8);
            let t0 = b.tof;
            let f = |b: &mut B| hop2::invp_lo(b, &cl, &x, &pool);
            if rev_ { wp::undo(&mut b, f) } else { f(&mut b) }
            let tof = b.tof - t0;
            let (xr, clr) = (x.clone(), cl.clone());
            let reps = 16u64;
            let total = (1u64 << (n - 1)) * reps;
            let mut gen = |i: u64| -> Case {
                let xv = ((i / reps) << 1) | 1;
                Case { ini: vec![(xr.clone(), xv), (clr.clone(), 0)], fin: vec![(xr.clone(), P256_LO.wrapping_mul(inv(xv, n)) & m(n))] }
            };
            let bad = run_gen(&b, total, &mut gen, &mut rng, &format!("h1lo_{n}_{rev_}"));
            eprintln!("DIALTOF h1lo n {n}{}: {total} cases, {bad} bad, tof {tof}", if rev_ { " reverse" } else { "" });
            fails += bad;
        }
    }
    assert_eq!(fails, 0);
}

/// Sechzaehner-Inversli at 18 bits (hop2::invp18): all 131,072 odd x, 16 random dirty states each (pool of 9 lanes, only 9 are used), forward and
/// gate-reversed; value on x, every other lane unchanged (clean lanes back to 0, pool restored), phase 0. Then the Rust gate
/// sequence must equal src/point_add/invp18_gates.json (the model's flat list) gate for gate. Toffoli must be 530.
/// Failure counts are printed separately (DIALTOF h1_18 value / json), so a DEV_INVP18_BREAK control is seen by the value check alone.
#[test]
fn dial_h1_18() {
    use super::prims_builder::G;
    let mut rng = Rng(0xd1a1_0000 + 18);
    let mut fails = 0u64;
    let n = 18usize;
    for rev_ in [false, true] {
        let mut b = B::new();
        let x = b.alloc_n(n);
        let cl = b.alloc_n(2);
        let pool = b.alloc_n(9);
        let t0 = b.tof;
        let f = |b: &mut B| hop2::invp18(b, &cl, &x, &pool);
        if rev_ { wp::undo(&mut b, f) } else { f(&mut b) }
        let tof = b.tof - t0;
        let (xr, clr) = (x.clone(), cl.clone());
        let reps = 16u64;
        let total = (1u64 << (n - 1)) * reps;
        let mut gen = |i: u64| -> Case {
            let xv = ((i / reps) << 1) | 1;
            Case { ini: vec![(xr.clone(), xv), (clr.clone(), 0)], fin: vec![(xr.clone(), P256_LO.wrapping_mul(inv(xv, n)) & m(n))] }
        };
        let bad = run_gen(&b, total, &mut gen, &mut rng, &format!("h1_18_{rev_}"));
        eprintln!("DIALTOF h1_18 value{}: {total} cases, {bad} bad, tof {tof}", if rev_ { " reverse" } else { "" });
        if option_env!("DEV_INVP18_BREAK").is_none() { assert_eq!(tof, 530); }
        fails += bad;
    }
    // gate-for-gate against the JSON
    let js = include_str!("invp18_gates.json");
    let gs = js.split("\"gates\":").nth(1).unwrap();
    let mut want: Vec<Vec<String>> = vec![];
    let mut cur: Option<Vec<String>> = None;
    let mut depth = 0;
    let mut tok = String::new();
    let mut inq = false;
    for ch in gs.chars() {
        if inq { if ch == '"' { inq = false; if let Some(c) = cur.as_mut() { c.push(std::mem::take(&mut tok)); } } else { tok.push(ch); } continue; }
        match ch {
            '"' => inq = true,
            '[' => { depth += 1; if depth == 2 { cur = Some(vec![]); } }
            ']' => { if depth == 2 { want.push(cur.take().unwrap()); } depth -= 1; if depth == 0 { break; } }
            _ => {}
        }
    }
    let mut b = B::new();
    let x = b.alloc_n(n);
    let cl = b.alloc_n(2);
    let pool = b.alloc_n(9);
    let got = wp::rec(&mut b, |b| hop2::invp18(b, &cl, &x, &pool));
    let lane = |s: &str| -> Q {
        let k: usize = s[1..].parse().unwrap();
        match &s[..1] { "x" => x[k], "z" => cl[k], "p" => pool[k], _ => panic!("lane {s}") }
    };
    let mut jbad = 0u64;
    if got.len() != want.len() { jbad += 1; eprintln!("json: length {} vs {}", got.len(), want.len()); }
    for (i, (g, w)) in got.iter().zip(want.iter()).enumerate() {
        let l: Vec<Q> = w[1..].iter().map(|s| lane(s)).collect();
        let e = match w[0].as_str() {
            "x" => G::X(l[0]), "cx" => G::Cx(l[0], l[1]), "ccx" => G::Ccx(l[0], l[1], l[2]),
            "andc" => G::AndC(l[0], l[1], l[2]), "andu" => G::AndU(l[0], l[1], l[2]), o => panic!("op {o}"),
        };
        if *g != e { jbad += 1; if jbad <= 3 { eprintln!("json: gate {i} differs: {:?} vs {:?}", g, e); } }
    }
    eprintln!("DIALTOF h1_18 json: {} gates, {} differ", want.len(), jbad);
    assert_eq!(want.len(), 1749);
    assert_eq!(fails, 0, "value check");
    assert_eq!(jbad, 0, "json check");
}

/// hop_ab at page width 18 (idiv_sgn2 + dispatch to invp18 with the production lane roles: 2 clean, catalyst gd left alone,
/// pool = passenger lanes): 2^20 random (va, odd vb, gd) cases on randomly filled lanes.
#[test]
fn dial_k2_hop_ab18() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let n = 18usize;
    let mut rng = Rng(0xd1a1_1000 + 18);
    let mut k = k2(n);
    let cf = Cfg { clean: &k.cl, fast: false };
    let t0 = k.b.tof;
    hop2::hop_ab(&mut k.b, cf, &k.va, &k.vb, &k.gd, &k.pool, P256_LO, true);
    let tof = k.b.tof - t0;
    let (va, vb, gd, cl) = (k.va.clone(), k.vb.clone(), k.gd.clone(), k.cl.clone());
    let mut r2 = Rng(0x5eed00 + 18);
    let mut gen = |_i: u64| -> Case {
        let xv = (r2.bits(n) & !1) | 1;
        let av = r2.bits(n);
        let gv = r2.bits(n - 1);
        let ix = inv(xv, n);
        Case {
            ini: vec![(va.clone(), av), (vb.clone(), xv), (gd.clone(), gv), (cl.clone(), 0)],
            fin: vec![(va.clone(), av.wrapping_mul(ix) & m(n)), (vb.clone(), P256_LO.wrapping_mul(ix) & m(n)), (gd.clone(), gv)],
        }
    };
    let bad = run_gen(&k.b, 1 << 20, &mut gen, &mut rng, "hop_ab18");
    eprintln!("DIALTOF hop_ab n 18 (sampled 2^20): {bad} bad, tof {tof}");
    assert_eq!(bad, 0);
}
