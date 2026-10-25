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
    /// drop the S8 marker repair (conditioned CCZ) from the inverse slot
    DropMarkerRepair,
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
            Mut::DropMarkerRepair => inv.retain(|o| !(o.kind == OT::CCZ && is_rc(o.c_condition, 0))),
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
    let mut sites = vec![2, 3, 4, 5, 7];
    if pool >= 2 {
        sites.push(1);
        sites.push(6);
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
