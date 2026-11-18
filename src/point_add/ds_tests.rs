//! DS (Draeaeschiibe) unit tests on SamrendraS 85db0e93 + the dial code: the K2-half kernels at page widths 3..12 exactly as
//! the sandwich calls them (hop_ab: idiv_sgn2 + invp11 / invp12 / invp_lo / cat_invp; hop_c: mac_sgn / mac; PCONV cv:
//! cv_conj / cimul form), idiv_sgn2 alone, the two Hensel inverses both ways, vb enumerated at n <= 8, the stream's own
//! wrapper (wp::rec -> Machine::pgl_roles -> hmr_roles -> the MarkerWalk emission rule, forward / inverse / block ++ rev_and),
//! and the page-moving edits as index facts. His digit-count blocks (NK_*, DB_F0_SIGN), the page-11 barrel and the other
//! page-11 levers are page-gated (DS_GATE11), not tested here. Every test name contains dial_.
//! Run: cargo test --release --bin build_circuit -- dial_ --show-output

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
    while i < total {
        let e = (i + blk).min(total);
        let cases: Vec<Case> = (i..e).map(|k| gen(k)).collect();
        bad += run_cases(b, &cases, rng, &format!("{tag}@{i}"));
        i = e;
    }
    bad
}

const WIDTHS: [usize; 10] = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

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
    for n in WIDTHS {
        let mut k = k2(n);
        let cf = Cfg { clean: &k.cl, fast: false };
        let t0 = k.b.tof;
        hop2::hop_ab(&mut k.b, cf, &k.va, &k.vb, &k.gd, &k.pool, P256_LO, true);
        let tof = k.b.tof - t0;
        // invp11 (H1) leaves the catalyst alone; the parked cat_invp leaves it holding bits 1.. of X * G (G = 1 + 2 gd)
        let h1 = super::AKK2_H1 && (n == 11 || (n == 12 && super::DS_K2_ALLW) || ((6..=10).contains(&n) && super::DS_K2_ALLW));
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
    for n in WIDTHS {
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
        let path = if super::AKK2_S2 && (super::DS_K2_ALLW || n == 11) { "mac_sgn (S2)" } else { "wp::mac" };
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
    for n in WIDTHS {
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
        let path = if super::AK_PCONV_S3 && (super::DS_K2_ALLW || n == 11) { "cv_conj (S3)" } else { "cimul form" };
        eprintln!("DIALTOF pconv_cv n {n}: {total} cases, {bad} bad, tof {tof} ({path})");
        fails += bad;
    }
    assert_eq!(fails, 0);
}

#[test]
fn dial_x1_idiv_sgn2() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a1_0005);
    let mut fails = 0u64;
    for n in WIDTHS {
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

// ---------------- second batch (review gaps), ported from dial768's dial_tests2.rs
#[test]
fn dial_r2_k2_hop_c_vb() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a2_0001);
    let mut fails = 0u64;
    for n in 3..=8usize {
        let mut k = k2(n);
        let cf = Cfg { clean: &k.cl, fast: false };
        hop2::hop_c(&mut k.b, cf, &k.va, &k.vb, &k.sc, &k.pool);
        let (va, vb, sc, cl) = (k.va.clone(), k.vb.clone(), k.sc.clone(), k.cl.clone());
        let total = 1u64 << (3 * n);
        let mut gen = |i: u64| -> Case {
            let (av, sv, bv) = (i & m(n), (i >> n) & m(n), i >> (2 * n));
            Case { ini: vec![(va.clone(), av), (vb.clone(), bv), (sc.clone(), sv), (cl.clone(), 0)],
                   fin: vec![(vb.clone(), bv.wrapping_sub(av.wrapping_mul(sv)) & m(n))] }
        };
        let bad = run_gen(&k.b, total, &mut gen, &mut rng, &format!("hopc_vb{n}"));
        eprintln!("DIALTOF hop_c_vb n {n}: {total} cases, {bad} bad (every va, sc, vb)");
        fails += bad;
    }
    assert_eq!(fails, 0);
}

#[test]
fn dial_r2_k2_pconv_cv_vb() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a2_0002);
    let mut fails = 0u64;
    for n in 3..=8usize {
        let mut k = k2(n);
        let c = k.b.alloc();
        let z = [k.cl[0]];
        let cfz = Cfg { clean: &z, fast: false };
        hop2::pconv_cv(&mut k.b, cfz, c, &k.va, &k.vb, &k.sc, &k.pas);
        let (va, vb, sc, zl) = (k.va.clone(), k.vb.clone(), k.sc.clone(), z.to_vec());
        let n1 = 1u64 << (3 * n - 1);
        let total = n1 + (1u64 << (3 * n));
        let mut gen = |i: u64| -> Case {
            let (cv, av, sv, bv) = if i < n1 { (1u64, ((i & m(n - 1)) << 1) | 1, (i >> (n - 1)) & m(n), i >> (2 * n - 1)) }
                                   else { let j = i - n1; (0, j & m(n), (j >> n) & m(n), j >> (2 * n)) };
            let s2 = if cv == 1 { bv.wrapping_sub(av.wrapping_mul(sv)) & m(n) } else { sv };
            Case { ini: vec![(va.clone(), av), (vb.clone(), bv), (sc.clone(), sv), (vec![c], cv), (zl.clone(), 0)],
                   fin: vec![(sc.clone(), s2)] }
        };
        let bad = run_gen(&k.b, total, &mut gen, &mut rng, &format!("pcv_vb{n}"));
        eprintln!("DIALTOF pconv_cv_vb n {n}: {total} cases, {bad} bad (every va, sc, vb; c = 1 with va odd, c = 0)");
        fails += bad;
    }
    assert_eq!(fails, 0);
}

/// emit a frame gate list into the builder by the stream's own rules: roles from hmr_roles; a marker emits as AND compute or
/// measured uncompute by MarkerWalk::marker_compute(role, inverse) (MarkerWalk::emit_and: compute -> and_c, else and_u, with
/// OB_HMR_NEG off); a plain gate as CCX / CX / X (MarkerWalk::emit). inverse = the inverse walk: gates in reverse order.
fn emit_walk(b: &mut B, gl: &[super::G], inverse: bool) -> (usize, usize) {
    let fl = vec![false; gl.len()];
    let role = super::hmr_roles(gl, &fl);
    let (mut nc, mut nu) = (0usize, 0usize);
    let l = |v: u32| Q(v as u64);
    let idx: Vec<usize> = if inverse { (0..gl.len()).rev().collect() } else { (0..gl.len()).collect() };
    for i in idx {
        let g = gl[i];
        match role[i] {
            0 => {
                assert!(g.2 == super::NONE || super::gl_loader::flag_of(g.2) == 0);
                if g.2 != super::NONE { b.ccx(l(g.0), l(g.1), l(g.2)); } else if g.1 != super::NONE { b.cx(l(g.0), l(g.1)); } else { b.x(l(g.0)); }
            }
            r @ (3 | 4) => {
                let t = l(super::gl_loader::lane_of(g.2));
                if super::MarkerWalk::marker_compute(r, inverse) { b.and_c(l(g.0), l(g.1), t); nc += 1; } else { b.and_u(l(g.0), l(g.1), t); nu += 1; }
            }
            r => panic!("dial2_wrapper: unexpected role {r} (cc_core AND outside mac_finish)"),
        }
    }
    (nc, nu)
}

#[test]
fn dial_r2_wrapper() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let mut rng = Rng(0xd1a2_0004);
    let mut fails = 0u64;
    for n in 3..=12usize {
        for blk in ["hop_ab", "hop_c", "pconv_cv"] {
            // forms: 0 = forward walk of the block, 1 = inverse walk of the block, 2 = forward walk of block ++ rev_and(block)
            for form in 0..3usize {
                let mut k = k2(n);
                let c = k.b.alloc();
                let cfk = Cfg { clean: &k.cl, fast: false };
                let z = [k.cl[0]];
                let cfz = Cfg { clean: &z, fast: false };
                let rg = match blk {
                    "hop_ab" => wp::rec(&mut k.b, |b| hop2::hop_ab(b, cfk, &k.va, &k.vb, &k.gd, &k.pool, P256_LO, true)),
                    "hop_c" => wp::rec(&mut k.b, |b| hop2::hop_c(b, cfk, &k.va, &k.vb, &k.sc, &k.pool)),
                    _ => wp::rec(&mut k.b, |b| hop2::pconv_cv(b, cfz, c, &k.va, &k.vb, &k.sc, &k.pas)),
                };
                let gl = super::Machine::pgl_roles(rg);
                let markers = gl.iter().filter(|g| g.2 != super::NONE && super::gl_loader::flag_of(g.2) != 0).count();
                let seq: Vec<super::G> = if form == 2 { let mut s = gl.clone(); s.extend(super::rev_and(&gl)); s } else { gl.clone() };
                let (nc, nu) = emit_walk(&mut k.b, &seq, form == 1);
                let (va, vb, sc, gd, cl) = (k.va.clone(), k.vb.clone(), k.sc.clone(), k.gd.clone(), k.cl.clone());
                // the block's map (input -> output), as in dial_tests.rs
                let h1 = super::AKK2_H1 && ((6..=10).contains(&n) && super::DS_K2_ALLW || n == 11 || n == 12 && super::DS_K2_ALLW);
                let exhaust = n <= 6;
                let total: u64 = if exhaust { match blk { "hop_ab" => 1 << (2 * n - 1), "hop_c" => 1 << (3 * n), _ => 3 << (3 * n - 1) } } else { 1 << 16 };
                let mut r2 = Rng(0x5eed ^ (n * 7 + form) as u64);
                let mut gen = |i: u64| -> Case {
                    let gv = r2.bits(n - 1);
                    let (inr, outr): (Asg, Asg) = match blk {
                        "hop_ab" => {
                            let (av, xv) = if exhaust { (i & m(n), ((i >> n) << 1) | 1) } else { (r2.bits(n), r2.bits(n) | 1) };
                            let ix = inv(xv, n);
                            let gd2 = if h1 { gv } else { ((xv.wrapping_mul(1 + 2 * gv)) & m(n)) >> 1 };
                            (vec![(va.clone(), av), (vb.clone(), xv), (gd.clone(), gv)],
                             vec![(va.clone(), av.wrapping_mul(ix) & m(n)), (vb.clone(), P256_LO.wrapping_mul(ix) & m(n)), (gd.clone(), gd2)])
                        }
                        "hop_c" => {
                            let (av, sv, bv) = if exhaust { (i & m(n), (i >> n) & m(n), i >> (2 * n)) } else { (r2.bits(n), r2.bits(n), r2.bits(n)) };
                            (vec![(va.clone(), av), (vb.clone(), bv), (sc.clone(), sv)],
                             vec![(va.clone(), av), (vb.clone(), bv.wrapping_sub(av.wrapping_mul(sv)) & m(n)), (sc.clone(), sv)])
                        }
                        _ => {
                            let n1 = 1u64 << (3 * n - 1);
                            let (cv, av, sv, bv) = if !exhaust { let cv = r2.bits(1); (cv, r2.bits(n) | cv, r2.bits(n), r2.bits(n)) }
                                else if i < n1 { (1, ((i & m(n - 1)) << 1) | 1, (i >> (n - 1)) & m(n), i >> (2 * n - 1)) }
                                else { let j = i - n1; (0, j & m(n), (j >> n) & m(n), j >> (2 * n)) };
                            let s2 = if cv == 1 { bv.wrapping_sub(av.wrapping_mul(sv)) & m(n) } else { sv };
                            (vec![(va.clone(), av), (vb.clone(), bv), (sc.clone(), sv), (vec![c], cv)],
                             vec![(va.clone(), av), (vb.clone(), bv), (sc.clone(), s2), (vec![c], cv)])
                        }
                    };
                    let (mut ini, fin) = match form { 0 => (inr.clone(), outr), 1 => (outr.clone(), inr), _ => (inr.clone(), inr) };
                    ini.push((cl.clone(), 0));
                    Case { ini, fin }
                };
                let bad = run_gen(&k.b, total, &mut gen, &mut rng, &format!("wrap_{blk}_{n}_{form}"));
                let fname = ["forward walk", "inverse walk", "block ++ rev_and(block)"][form];
                eprintln!("DIALTOF wrap_{blk} n {n} form {form}: {total} cases, {bad} bad ({fname}; {markers} AND markers, emitted {nc} AND + {nu} measured uncomputes; {})",
                          if exhaust { "exhaustive" } else { "random" });
                fails += bad;
            }
        }
    }
    assert_eq!(fails, 0);
}

#[test]
fn dial_r2_static_bounds() {
    // conv_fwd: spares = freed[s0 .. s0 + PAGE_DI - D] with s0 = 1 (CAD4); freed = 2 (W - WHI) lanes, the last two of the X
    // half (freed[W-WHI-2], freed[W-WHI-1]) are page_cases_xy's literals x[W-2], x[W-1]. even11: dig = y0, x[wv-1..wv-9].
    let s0 = 1usize;
    let nfreed = 2 * (super::W - super::WHI);
    let mut bad = 0u64;
    for dd in 3..=12usize {
        let nl = super::PAGE_DI - dd;
        let sp: Vec<usize> = (s0..s0 + nl).collect();
        let lit = [super::W - super::WHI - 2, super::W - super::WHI - 1];
        let ok_sp = s0 + nl <= super::W - super::WHI - 2 && sp.iter().all(|&i| i < nfreed && !lit.contains(&i));
        let wv = super::W - 2 * dd;
        let dig: Vec<usize> = (1..10).map(|k| wv - k).collect();
        let ok_dig = dig.iter().all(|&i| i >= 1 && i < wv) && { let mut v = dig.clone(); v.sort(); v.dedup(); v.len() == 9 };
        let extra = (s0 + nl).saturating_sub(6);
        eprintln!("DIALTOF static n {dd}: 2 cases, {} bad (spares freed[{s0}..{}] of {nfreed}, {extra} fresh labels = width {}; ring {wv}, digit lanes x[{}..{}])",
                  (!ok_sp) as u64 + (!ok_dig) as u64, s0 + nl, 765 + extra, wv - 9, wv - 1);
        bad += (!ok_sp) as u64 + (!ok_dig) as u64;
    }
    assert_eq!(bad, 0);
}
