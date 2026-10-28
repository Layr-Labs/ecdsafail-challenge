//! Lane G1 tests: measured flags (forward X-measurement, inverse phase repair) on froghop-double.
//!
//! Per slot, from the on-model state of 64 random shots (dirty passenger lanes random):
//! 1. the plain slot is exact (phase 0, scratch clean);
//! 2. the forward (measured) slot leaves every qubit exactly as the plain slot does;
//! 3. forward slot followed by the inverse slot recording played inverted is the identity, phase included
//!    (the receipt written by the forward Hmr is read by the inverse repair in the same run);
//! 4. every forward receipt is read exactly once by its inverse slot.
//! Negative controls drop one repair or one measurement and must be caught.

use super::builder::B;
use super::froghop_double::{FhDouble, Ghost, NRC, WD};
use super::refmodel_double::{self as rmd, N};
use super::tests_double::{lay_double, run, Rng};
use crate::circuit::{BitId, Op, OperationType as OT, QubitId, NO_BIT};

fn put(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) { words[q.0 as usize] |= 1 << shot } else { words[q.0 as usize] &= !(1 << shot) }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mut {
    None,
    /// drop the S8 marker repair (conditioned CCZ; at pool 0 the conditioned Z on p2) from the inverse slot
    DropMarkerRepair,
    /// pool 0 (lane FHD-LEFT): drop the k-th CX of the forward marker move 111 -> 001 (the CX ops right before the
    /// marker's Hmr)
    DropMarkerCx(usize),
    /// drop the conditioned-Z repair of site k (1..NRC) from the inverse slot
    DropZ(usize),
    /// drop the forward measurement of site k (the flag stays in its qubit)
    DropHmr(usize),
    /// drop the forward marker measurement (the flag stays in its qubit)
    DropMarkerHmr,
    /// condition the marker repair on the probe's receipt instead
    SwapReceipts,
    /// site 8: drop the phase oracle's CZ / CCZ inside the condition block
    DropD1Phase,
    /// site 8: drop the measurement in front of the condition block
    DropD1Hmr,
}

/// Returns (slots checked, per-site receipt counts, first failure message).
fn pair_check(seed: u64, m: Mut) -> (usize, [usize; NRC], Option<String>) {
    let lay = lay_double();
    let w = WD;
    let mut b = B::new();
    let d = b.alloc_n(w);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let mut rng = Rng::new(seed);
    let pp = rmd::p();
    let models: Vec<rmd::St> = (0..64).map(|_| {
        let mut x = rng.below(256) % pp;
        if x == N::ZERO { x = N::from(1u64); }
        rmd::St::new(x)
    }).collect();
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let dq = dirty.clone();
    let mut words = run(&b.ops, nq, &|wd| {
        for k in 0..64 { put(wd, &vl, k, &models[k].rv); }
        for (i, &q) in dq.iter().enumerate() {
            wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7 + seed) ^ 0x5bd1e995;
        }
    }).q;
    let mut counts = [0usize; NRC];
    let mut d1n = 0usize;
    let mut fail = None;
    for sigma in 0..lay.s {
        let vmap = f.v.clone();
        let start = b.ops.len();
        // plain
        f.ghost = Ghost::Plain;
        f.slot(&mut b, &lay, sigma);
        let plain: Vec<Op> = b.ops[start..].to_vec();
        let vafter = f.v.clone();
        b.ops.truncate(start);
        f.v = vmap.clone();
        // forward, measured
        f.ghost = Ghost::Fwd;
        f.rc = [None; NRC];
        f.slot(&mut b, &lay, sigma);
        assert_eq!(f.v, vafter, "slot {sigma}: forward lane map");
        let rc = f.rc;
        let mut fwd: Vec<Op> = b.ops[start..].to_vec();
        b.ops.truncate(start);
        f.v = vmap.clone();
        // inverse slot recording, played inverted
        f.ghost = Ghost::Inv;
        f.rc = rc;
        f.rc_used = [false; NRC];
        b.begin();
        f.slot(&mut b, &lay, sigma);
        let rec = b.end();
        for k in 0..NRC {
            assert_eq!(rc[k].is_some(), f.rc_used[k], "slot {sigma}: receipt {k} closure");
            if rc[k].is_some() { counts[k] += 1; }
        }
        f.play_inverse_slot(&mut b, &rec);
        let mut inv: Vec<Op> = b.ops[start..].to_vec();
        d1n += inv.iter().filter(|o| o.kind == OT::PushCondition).count();
        b.ops.truncate(start);
        f.v = vmap.clone();
        f.ghost = Ghost::Plain;
        // receipts are fresh bits read only by their own repair
        for op in &plain {
            assert!(op.kind != OT::Hmr || op.c_target == BitId(0), "plain slot writes a receipt");
        }
        let is_rc = |c: BitId, k: usize| rc[k] == Some(c) && c != NO_BIT;
        match m {
            Mut::None => {}
            Mut::DropMarkerRepair => inv.retain(|o| !(matches!(o.kind, OT::CCZ | OT::Z) && is_rc(o.c_condition, 0))),
            Mut::DropMarkerCx(k) => {
                if let Some(i) = fwd.iter().position(|o| o.kind == OT::Hmr && is_rc(o.c_target, 0)) {
                    let j = i - 2 + k;
                    if fwd[i - 2].kind == OT::CX && fwd[i - 1].kind == OT::CX { fwd.remove(j); }
                }
            }
            Mut::DropZ(k) => inv.retain(|o| !(o.kind == OT::Z && is_rc(o.c_condition, k))),
            Mut::DropHmr(k) => fwd.retain(|o| !(o.kind == OT::Hmr && is_rc(o.c_target, k))),
            Mut::DropMarkerHmr => fwd.retain(|o| !(o.kind == OT::Hmr && is_rc(o.c_target, 0))),
            Mut::DropD1Phase => {
                let mut inside = false;
                inv.retain(|o| {
                    if o.kind == OT::PushCondition { inside = true; }
                    if o.kind == OT::PopCondition { inside = false; }
                    !(inside && matches!(o.kind, OT::CZ | OT::CCZ) && o.c_condition == NO_BIT)
                });
            }
            Mut::DropD1Hmr => {
                if let Some(i) = inv.iter().position(|o| o.kind == OT::PushCondition) {
                    assert_eq!(inv[i - 1].kind, OT::Hmr);
                    inv.remove(i - 1);
                }
            }
            Mut::SwapReceipts => {
                if let (Some(r0), Some(r1)) = (rc[0], rc[1]) {
                    for o in inv.iter_mut() {
                        if o.kind == OT::CCZ && o.c_condition == r0 { o.c_condition = r1; }
                    }
                }
            }
        }
        let wd = words.clone();
        let rp = run(&plain, nq, &move |x| x.copy_from_slice(&wd));
        assert_eq!(rp.phase, 0, "slot {sigma}: plain slot phase");
        let wd = words.clone();
        let rf = run(&fwd, nq, &move |x| x.copy_from_slice(&wd));
        let mut both = fwd.clone();
        both.extend(inv.iter().cloned());
        let wd = words.clone();
        let ri = run(&both, nq, &move |x| x.copy_from_slice(&wd));
        if fail.is_none() && std::env::var_os("G1_DBG").is_some() && (rf.q[..nq] != rp.q[..nq] || ri.phase != 0 || ri.q[..nq] != words[..nq]) {
            let nh = fwd.iter().filter(|o| o.kind == OT::Hmr).count();
            eprintln!("dbg {m:?} slot {sigma}: rf==rp {} ri==w {} ri.phase {:#x} rf.phase {:#x} fwd Hmr {} rc {:?} nq {}", rf.q[..nq] == rp.q[..nq], ri.q[..nq] == words[..nq], ri.phase, rf.phase, nh, rc, nq);
        }
        if fail.is_none() {
            if rf.q[..nq] != rp.q[..nq] {
                let diff: Vec<usize> = (0..nq).filter(|&q| rf.q[q] != rp.q[q]).collect();
                fail = Some(format!("slot {sigma}: measured forward differs from plain on qubits {:?}", &diff[..diff.len().min(8)]));
            } else if ri.q[..nq] != words[..nq] {
                let diff: Vec<usize> = (0..nq).filter(|&q| ri.q[q] != words[q]).collect();
                fail = Some(format!("slot {sigma}: forward + inverse not identity on qubits {:?}", &diff[..diff.len().min(8)]));
            } else if ri.phase != 0 {
                fail = Some(format!("slot {sigma}: forward + inverse phase {:#x}", ri.phase));
            }
        }
        if m == Mut::None {
            if let Some(e) = &fail { panic!("seed {seed}: {e}"); }
        }
        words = rp.q;
        f.v = vafter;
    }
    if std::env::var_os("G1_DBG").is_some() { eprintln!("site 8 cuts: {d1n}"); }
    D1N.with(|c| c.set(d1n));
    (lay.s, counts, fail)
}
thread_local! { static D1N: std::cell::Cell<usize> = std::cell::Cell::new(0); }

#[test]
fn g1_slot_pairs_exact() {
    let seeds: Vec<u64> = match std::env::var("G1_SEEDS") {
        Ok(s) => s.split(',').map(|t| t.trim().parse().unwrap()).collect(),
        Err(_) => vec![5101, 5102, 5103, 5104],
    };
    for &seed in &seeds {
        let (s, counts, fail) = pair_check(seed, Mut::None);
        assert!(fail.is_none());
        assert!(counts[0] > 0, "no measured marker site");
        eprintln!("G1 seed {seed}: {s} slots, measured sites per kind {:?}, site 8 cuts {}, plain == measured forward, pair identity ok", counts, D1N.with(|c| c.get()));
    }
}

#[test]
fn g1_negative_controls() {
    let pool = super::froghop_double::pool_d();
    let mut muts = vec![Mut::DropMarkerRepair, Mut::DropMarkerHmr];
    // sites present at this pool (site 1, the probe, needs dl in its own pool qubit; site 6, dv0, a held z0 form)
    // lane FHD-L19: S4 runs the L19 cube form at every pool (no flag qubit: sites 3, 5, 6 are not used)
    let mut sites = vec![2, 4, 7];
    if pool == 0 {
        // lane FHD-LEFT: at pool 0 only the marker (site 0) is measured; the A4b pool-0 forms hold no flag qubit
        sites.clear();
        muts.push(Mut::DropMarkerCx(0));
        muts.push(Mut::DropMarkerCx(1));
    }
    if pool >= 2 {
        sites.push(1);
        muts.push(Mut::SwapReceipts);
        muts.push(Mut::DropD1Phase);
        muts.push(Mut::DropD1Hmr);
    }
    for k in sites {
        muts.push(Mut::DropZ(k));
        muts.push(Mut::DropHmr(k));
    }
    for m in muts {
        let mut caught = false;
        for seed in [6101u64, 6102] {
            let (_, _, fail) = pair_check(seed, m);
            if let Some(e) = fail {
                eprintln!("G1 mutant {m:?} caught (seed {seed}): {e}");
                caught = true;
                break;
            }
        }
        assert!(caught, "mutant {m:?} not caught");
    }
}

/// Per-step Toffoli of the measured forward slot against the plain slot (expected executed: conditioned
/// gates count one half). Diagnostic only.
#[test]
fn g1_profile() {
    use std::collections::BTreeMap;
    let lay = lay_double();
    let mut tot: [BTreeMap<&'static str, f64>; 2] = [BTreeMap::new(), BTreeMap::new()];
    for (mi, mode) in [Ghost::Plain, Ghost::Fwd].into_iter().enumerate() {
        let mut b = B::new();
        let d = b.alloc_n(WD);
        let v = b.alloc_n(WD);
        let par = b.alloc();
        let dirty = b.alloc_n(256);
        let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
        f.init(&mut b, &lay);
        for sigma in 0..lay.s {
            f.marks.clear();
            f.ghost = mode;
            f.rc = [None; NRC];
            let start = b.ops.len();
            f.slot(&mut b, &lay, sigma);
            let mut mk = vec![("pre", start)];
            mk.extend(f.marks.iter().cloned());
            mk.push(("end", b.ops.len()));
            for i in 0..mk.len() - 1 {
                let c: f64 = b.ops[mk[i].1..mk[i + 1].1].iter().filter(|o| matches!(o.kind, OT::CCX | OT::CCZ))
                    .map(|o| if o.c_condition == NO_BIT { 1.0 } else { 0.5 }).sum();
                *tot[mi].entry(mk[i].0).or_default() += c;
            }
        }
        eprintln!("scratch peak per step ({:?}): {:?}", mode, f.peaks);
    }
    let (mut a0, mut a1) = (0.0, 0.0);
    for (k, v) in &tot[0] {
        let w = tot[1].get(k).copied().unwrap_or(0.0);
        a0 += v;
        a1 += w;
        eprintln!("{:10} plain {:>8.1}/slot  measured fwd {:>8.1}/slot  delta {:>8.1}", k, v / lay.s as f64, w / lay.s as f64, (w - v) / lay.s as f64);
    }
    eprintln!("total plain {:.1}/slot measured fwd {:.1}/slot", a0 / lay.s as f64, a1 / lay.s as f64);
}

/// Classify traversal inputs (env G1_CLASSIFY = file with one hex value per line: the reflected traversal input
/// x' < 2^255). Runs the plain gate-level traversal slot by slot against the integer model and prints per input the
/// first slot where a register leaves the model (or the model's own invariant fails), or "on-model". The measured
/// forward slot equals the plain slot on every qubit (g1_slot_pairs_exact), so the class holds for both builds.
#[test]
fn g1_classify() {
    let Ok(path) = std::env::var("G1_CLASSIFY") else { return };
    let txt = std::fs::read_to_string(&path).unwrap();
    let xs: Vec<N> = txt.lines().map(|l| l.trim()).filter(|l| !l.is_empty())
        .map(|l| N::from_str_radix(l.trim_start_matches("0x"), 16).unwrap()).collect();
    for (ci, chunk) in xs.chunks(64).enumerate() {
        classify_chunk(ci * 64, chunk);
    }
}

fn classify_chunk(base_idx: usize, xs: &[N]) {
    use super::froghop_double::BB;
    use super::refmodel_double::Ph;
    use super::tests_double::expect_lanes;
    let lay = lay_double();
    let w = WD;
    let mut b = B::new();
    let d = b.alloc_n(w);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let pp = rmd::p();
    let mut models: Vec<rmd::St> = (0..64).map(|k| {
        let x = xs[k.min(xs.len() - 1)];
        rmd::St { r: pp, cd: N::from(1u64), rv: x, cv: N::ZERO, pi: 1, ph: Ph::Al, stk: vec![], b: 256, cnt: 0, par: 0, refl: 0 }
    }).collect();
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mods = models.clone();
    let dq = dirty.clone();
    let mut words = run(&b.ops, nq, &|wd| {
        for k in 0..64 { put(wd, &vl, k, &mods[k].rv); }
        for (i, &q) in dq.iter().enumerate() { wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 11); }
    }).q;
    let getb = |wd: &[u64], q: QubitId, k: usize| (wd[q.0 as usize] >> k) & 1;
    let getn = |wd: &[u64], qs: &[QubitId], k: usize| {
        let mut x = N::ZERO;
        for (i, &q) in qs.iter().enumerate() { if (wd[q.0 as usize] >> k) & 1 == 1 { x |= N::from(1u64) << i; } }
        x
    };
    let mut bad: Vec<Option<(usize, String)>> = vec![None; 64];
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    for sigma in 0..lay.s {
        for k in 0..64 {
            if bad[k].is_some() { continue; }
            let m = &models[k];
            let (ed, ev) = expect_lanes(m);
            let mut why = None;
            if (0..w).any(|j| getb(&words, f.d[j], k) as u8 != ed[j]) { why = Some("D lanes".to_string()); }
            else if (0..w).any(|j| getb(&words, f.v[j], k) as u8 != ev[j]) { why = Some("V lanes".to_string()); }
            else if getn(&words, &f.pi, k) != N::from(super::froghop_double::l19_encode((m.pi >> 1) as u64, m.stk.len() as u64).0) { why = Some("pi".to_string()); }
            else {
                let code: Vec<u64> = [f.p0, f.p1, f.p2].iter().map(|&q| getb(&words, q, k)).collect();
                let want = match m.ph { Ph::Al => [1, 0, 0], Ph::Dv => [0, 1, 0], Ph::Co => [1, 1, 0], Ph::Rt => [0, 0, 0], Ph::Dn => [0, 0, 1] };
                if code != want.to_vec() { why = Some(format!("phase code {:?} want {:?}", code, m.ph)); }
                else if getn(&words, &f.bq, k) != N::from(((m.b as i64 - 1 - lay.base[sigma] as i64).rem_euclid(1 << BB)) as u64) { why = Some("b".to_string()); }
                else if getn(&words, &f.dep, k) != N::from(super::froghop_double::l19_encode((m.pi >> 1) as u64, m.stk.len() as u64).1) { why = Some(format!("depth (model {})", m.stk.len())); }
            }
            if let Some(wy) = why { bad[k] = Some((sigma, wy)); }
        }
        let start = b.ops.len();
        f.ghost = Ghost::Plain;
        f.slot(&mut b, &lay, sigma);
        let ops = b.ops[start..].to_vec();
        b.ops.truncate(start);
        let wd = words.clone();
        words = run(&ops, nq, &move |x| x.copy_from_slice(&wd)).q;
        for k in 0..64 {
            if bad[k].is_some() { continue; }
            let mut m2 = models[k].clone();
            let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| m2.fwd(sigma))).is_ok();
            if ok { models[k] = m2; } else { bad[k] = Some((sigma, "model invariant".to_string())); }
        }
    }
    std::panic::set_hook(hook);
    for k in 0..xs.len() {
        let m = &models[k];
        let fin = m.ph == Ph::Dn && m.r == N::from(1u64) && m.rv == N::ZERO;
        match &bad[k] {
            Some((s, wy)) => eprintln!("G1CLASS {} OFF slot {} {}", base_idx + k, s, wy),
            None if fin => eprintln!("G1CLASS {} ON", base_idx + k),
            None => eprintln!("G1CLASS {} OFF end not finished ({:?})", base_idx + k, m.ph),
        }
    }
}
