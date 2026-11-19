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


/// Sechzaehner-Inversli at 12 bits (hop2::invp12): all 2,048 odd x, 16 random dirty states each (pool of 8 lanes, only 3 are used), forward and
/// gate-reversed; value on x, every other lane unchanged (clean lanes back to 0, pool restored), phase 0. Then the Rust gate
/// sequence must equal src/point_add/invp12_gates.json (the model's flat list) gate for gate. Toffoli must be 64.
/// Failure counts are printed separately (DIALTOF h1_12 value / json), so a DEV_INVP12_BREAK control is seen by the value check alone.
#[test]
fn dial_h1_12() {
    use super::prims_builder::G;
    let mut rng = Rng(0xd1a1_0000 + 12);
    let mut fails = 0u64;
    let n = 12usize;
    for rev_ in [false, true] {
        let mut b = B::new();
        let x = b.alloc_n(n);
        let cl = b.alloc_n(2);
        let pool = b.alloc_n(8);
        let t0 = b.tof;
        let f = |b: &mut B| hop2::invp12(b, &cl, &x, &pool);
        if rev_ { wp::undo(&mut b, f) } else { f(&mut b) }
        let tof = b.tof - t0;
        let (xr, clr) = (x.clone(), cl.clone());
        let reps = 16u64;
        let total = (1u64 << (n - 1)) * reps;
        let mut gen = |i: u64| -> Case {
            let xv = ((i / reps) << 1) | 1;
            Case { ini: vec![(xr.clone(), xv), (clr.clone(), 0)], fin: vec![(xr.clone(), P256_LO.wrapping_mul(inv(xv, n)) & m(n))] }
        };
        let bad = run_gen(&b, total, &mut gen, &mut rng, &format!("h1_12_{rev_}"));
        eprintln!("DIALTOF h1_12 value{}: {total} cases, {bad} bad, tof {tof}", if rev_ { " reverse" } else { "" });
        if option_env!("DEV_INVP12_BREAK").is_none() { assert_eq!(tof, 64); }
        fails += bad;
    }
    // gate-for-gate against the JSON
    let js = include_str!("invp12_gates.json");
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
    let pool = b.alloc_n(8);
    let got = wp::rec(&mut b, |b| hop2::invp12(b, &cl, &x, &pool));
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
    eprintln!("DIALTOF h1_12 json: {} gates, {} differ", want.len(), jbad);
    assert_eq!(want.len(), 305);
    assert_eq!(fails, 0, "value check");
    assert_eq!(jbad, 0, "json check");
}

/// hop_ab at page width 12 (idiv_sgn2 + dispatch to invp12 with the production lane roles: 2 clean, catalyst gd left alone,
/// pool = passenger lanes): 2^20 random (va, odd vb, gd) cases on randomly filled lanes.
#[test]
fn dial_k2_hop_ab12() {
    wp::HYB.store(true, std::sync::atomic::Ordering::Relaxed);
    let n = 12usize;
    let mut rng = Rng(0xd1a1_1000 + 12);
    let mut k = k2(n);
    let cf = Cfg { clean: &k.cl, fast: false };
    let t0 = k.b.tof;
    hop2::hop_ab(&mut k.b, cf, &k.va, &k.vb, &k.gd, &k.pool, P256_LO, true);
    let tof = k.b.tof - t0;
    let (va, vb, gd, cl) = (k.va.clone(), k.vb.clone(), k.gd.clone(), k.cl.clone());
    let mut r2 = Rng(0x5eed00 + 12);
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
    let bad = run_gen(&k.b, 1 << 20, &mut gen, &mut rng, "hop_ab12");
    eprintln!("DIALTOF hop_ab n 12 (sampled 2^20): {bad} bad, tof {tof}");
    assert_eq!(bad, 0);
}
