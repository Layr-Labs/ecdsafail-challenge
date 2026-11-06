//! Lane GN-EARLY: the lazy product pair with the early-measured forward add at short pools, round-tripped through
//! the simulator against the inherited routine on identical inputs (64 shots per pool).

use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::modp_ft::*;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn rng64(seed: u64) -> N {
    // deterministic per-call value sequence (matches the shelf test's Rng::below(n) draw order)
    static S: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let mut r = Rng::new(seed ^ S.fetch_add(1, std::sync::atomic::Ordering::Relaxed) * 0x9E3779B97F4A7C15);
    r.below(256) % p()
}

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: N) {
    for (i, q) in qs.iter().enumerate() {
        if v.bit(i) {
            w[q.0 as usize] |= 1 << shot;
        }
    }
}
fn get(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}

/// (forward T, bad mid values vs a*y mod p, phase, dirty lanes after the inverse, mid values, receipts, Hmr count)
fn lazy_roundtrip(pool_r: usize, seed: u64) -> (u64, usize, u64, u64, Vec<N>, usize, usize) {
    let pm = p();
    let mut rng = Rng::new(seed);
    let mut b = B::new();
    let (a, y) = (b.alloc_n(256), b.alloc_n(256));
    let k = b.alloc();
    let r = b.alloc_n(pool_r);
    let one = b.alloc();
    b.x(one);
    let ms = Ms { k, r, one };
    let z = b.alloc_n(256);
    let mut zz = z.clone();
    let t0 = b.tof;
    let pair = product_lazy(&mut b, &ms, &mut zz, &a, &y);
    let tf = b.tof - t0;
    let mid = b.ops.len();
    let zmid = zz.clone();
    let receipts = pair.receipts();
    product_inv_lazy(&mut b, &mut zz, &a, &y, pair);
    let hmr = b.ops.iter().filter(|op| matches!(op.kind, crate::circuit::OperationType::Hmr)).count();
    let avs: Vec<N> = (0..64).map(|i| if i < 4 { N::from(i as u64) << (i * 3) } else { rng.below(256) % pm }).collect();
    let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"gn-lazy-rt");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for sh in 0..64 {
        put(&mut s.qubits, &a, sh, avs[sh]);
        put(&mut s.qubits, &y, sh, ys[sh]);
    }
    s.apply_iter(b.ops[..mid].iter());
    let mut badv = 0;
    let mut mids = Vec::new();
    for sh in 0..64 {
        let got = get(&s.qubits, &zmid, sh);
        if got != avs[sh].mul_mod(ys[sh], pm) {
            badv += 1;
        }
        mids.push(got);
    }
    let ph1 = s.phase;
    s.apply_iter(b.ops[mid..].iter());
    let mut dirty = 0u64;
    for q in z.iter().chain(&ms.r).chain([&ms.k]) {
        dirty |= s.qubits[q.0 as usize];
    }
    // the receipts' phases are open between the halves (ph1 is expected nonzero) and repaid by the inverse
    eprintln!("  (mid-way phase {:#x}, final phase {:#x})", ph1, s.phase);
    (tf, badv, s.phase, dirty, mids, receipts, hmr)
}

/// Pools 71 (hand table, inherited add), 69 (generated plan, inherited add), 68 and 67 (generated plan, early add):
/// identical mid values, no bad values, phase 0, all scratch clean. Same T in the forward.
#[test]
fn gn_lazy_roundtrips_early_vs_inherited() {
    let mut ref_mids: Option<Vec<N>> = None;
    for pool_r in [71usize, 69, 68, 67] {
        let (tf, badv, ph, dirty, mids, receipts, hmr) = lazy_roundtrip(pool_r, 11);
        eprintln!("pool r={} (p0={}): fwd {} T, bad values {}, phase {:#x}, dirty {:#x}, receipts {}, Hmr {}", pool_r, pool_r + 1, tf, badv, ph, dirty, receipts, hmr);
        assert_eq!((badv, ph, dirty), (0, 0, 0), "pool r={}", pool_r);
        match &ref_mids {
            None => ref_mids = Some(mids),
            Some(m) => assert_eq!(m, &mids, "mid values differ at pool r={}", pool_r),
        }
    }
}

/// Negative controls: each mutation of the early add must break the round trip on the early path.
#[test]
fn gn_lazy_early_negative_controls() {
    use std::sync::atomic::Ordering::Relaxed;
    for brk in [1u8, 2, 3] {
        GN_EARLY_BREAK.store(brk, Relaxed);
        let r = std::panic::catch_unwind(|| lazy_roundtrip(68, 11));
        GN_EARLY_BREAK.store(0, Relaxed);
        match r {
            Ok((_, badv, ph, dirty, _, _, _)) => {
                eprintln!("break {}: bad values {}, phase {:#x}, dirty {:#x}", brk, badv, ph, dirty);
                assert!((badv, ph, dirty) != (0, 0, 0), "mutation {} not detected", brk);
            }
            Err(_) => eprintln!("break {}: panicked (detected)", brk),
        }
    }
}

/// The pebbled carry chain (GN-PEBBLE) against the direct var_add_pool on identical inputs: random t (n lanes),
/// addend pattern as the lazy fold uses it (a short t2 register sign-extended by repeating its top lane), pools from
/// the pebbled minimum up to one below the single-bridge threshold. Same sums, scratch clean, phase 0.
#[test]
fn gn_pebbled_add_matches_direct() {
    let mut rng = Rng::new(77);
    for (n, t2n) in [(80usize, 29usize), (61, 10), (96, 40), (33, 5)] {
        let need = n - 1;
        let pmin = pebbled_min_pool(need);
        let pmax = (need + 1) / 2; // pool <= loan <=> 2 pool <= need
        for pool_n in [pmin, pmin + 1, pmax.max(pmin)] {
            let mut b = B::new();
            let t = b.alloc_n(n);
            let t2 = b.alloc_n(t2n);
            let big = b.alloc_n(n);
            let small = b.alloc_n(pool_n);
            let add: Vec<Option<QubitId>> = (0..n).map(|i| Some(t2[i.min(t2n - 1)])).collect();
            // direct form on `big`, then the pebbled form (subtracting back) on `small`: t must return to its input
            var_add_pool(&mut b, &t, &add, &big);
            let mid = b.ops.len();
            for &q in &t { b.x(q); }
            var_add_pool(&mut b, &t, &add, &small);
            for &q in &t { b.x(q); }
            let tv: Vec<N> = (0..64).map(|_| rng.below(n)).collect();
            let t2v: Vec<N> = (0..64).map(|_| rng.below(t2n)).collect();
            let (aq, nb, _, _) = analyze_ops(b.ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"gn-pebble");
            let mut xof = h.finalize_xof();
            let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
            for sh in 0..64 {
                put(&mut s.qubits, &t, sh, tv[sh]);
                put(&mut s.qubits, &t2, sh, t2v[sh]);
            }
            s.apply_iter(b.ops[..mid].iter());
            let mask = (N::from(1u64) << n) - N::from(1u64);
            let mut badmid = 0;
            for sh in 0..64 {
                // sign-extended addend: t2 with its top bit repeated up to n lanes
                let mut a = t2v[sh];
                if a.bit(t2n - 1) { a |= (mask >> t2n) << t2n; }
                if get(&s.qubits, &t, sh) != (tv[sh] + a) & mask { badmid += 1; }
            }
            s.apply_iter(b.ops[mid..].iter());
            let mut bad = 0;
            for sh in 0..64 {
                if get(&s.qubits, &t, sh) != tv[sh] { bad += 1; }
            }
            let mut dirty = 0u64;
            for q in big.iter().chain(&small) { dirty |= s.qubits[q.0 as usize]; }
            let used_pebble = pool_n * 2 <= need;
            eprintln!("n {} t2 {} pool {} (pebbled {}): bad mid {}, bad back {}, phase {:#x}, dirty {:#x}", n, t2n, pool_n, used_pebble, badmid, bad, s.phase, dirty);
            assert_eq!((badmid, bad, s.phase, dirty), (0, 0, 0, 0), "n {} pool {}", n, pool_n);
        }
    }
}

/// Early + pebbled: the lazy pair round-trips at every generated plan from p0 = 67 down to the planner's floor, and
/// the plan refuses one below it.
#[test]
fn gn_lazy_roundtrips_pebbled_pools() {
    let mut floor = None;
    for pool_r in (50usize..=66).rev() {
        let r = std::panic::catch_unwind(|| lazy_roundtrip(pool_r, 23));
        match r {
            Ok((tf, badv, ph, dirty, _, receipts, hmr)) => {
                eprintln!("pool r={} (p0={}): fwd {} T, bad values {}, phase {:#x}, dirty {:#x}, receipts {}, Hmr {}", pool_r, pool_r + 1, tf, badv, ph, dirty, receipts, hmr);
                assert_eq!((badv, ph, dirty), (0, 0, 0), "pool r={}", pool_r);
            }
            Err(e) => {
                let msg = e.downcast_ref::<String>().cloned().or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default();
                eprintln!("pool r={} (p0={}) refused: {}", pool_r, pool_r + 1, msg);
                assert!(msg.contains("no feasible lazy block plan"), "pool r={} failed outside the planner: {}", pool_r, msg);
                floor = Some(pool_r + 2); break;
            }
        }
    }
    eprintln!("planner floor p0 = {:?}", floor);
    assert!(floor.is_some(), "no floor found down to p0 = 51");
}

/// Negative controls for the pebbled chain: each mutation must break the direct-vs-pebbled comparison.
#[test]
fn gn_pebbled_negative_controls() {
    use std::sync::atomic::Ordering::Relaxed;
    let mut rng = Rng::new(5);
    for brk in [1u8, 2] {
        GN_PEBBLE_BREAK.store(brk, Relaxed);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (n, t2n, pool_n) = (80usize, 29usize, 18usize);
            let mut b = B::new();
            let t = b.alloc_n(n);
            let t2 = b.alloc_n(t2n);
            let big = b.alloc_n(n);
            let small = b.alloc_n(pool_n);
            let add: Vec<Option<QubitId>> = (0..n).map(|i| Some(t2[i.min(t2n - 1)])).collect();
            var_add_pool(&mut b, &t, &add, &big);
            for &q in &t { b.x(q); }
            var_add_pool(&mut b, &t, &add, &small);
            for &q in &t { b.x(q); }
            let tv: Vec<N> = (0..64).map(|_| rng.below(n)).collect();
            let t2v: Vec<N> = (0..64).map(|_| rng.below(t2n)).collect();
            let (aq, nb, _, _) = analyze_ops(b.ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"gn-pebble-neg");
            let mut xof = h.finalize_xof();
            let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
            for sh in 0..64 { put(&mut s.qubits, &t, sh, tv[sh]); put(&mut s.qubits, &t2, sh, t2v[sh]); }
            s.apply_iter(b.ops.iter());
            let bad = (0..64).filter(|&sh| get(&s.qubits, &t, sh) != tv[sh]).count();
            let mut dirty = 0u64;
            for q in big.iter().chain(&small) { dirty |= s.qubits[q.0 as usize]; }
            (bad, s.phase, dirty)
        }));
        GN_PEBBLE_BREAK.store(0, Relaxed);
        match r {
            Ok((bad, ph, dirty)) => { eprintln!("pebble break {}: bad {}, phase {:#x}, dirty {:#x}", brk, bad, ph, dirty); assert!((bad, ph, dirty) != (0, 0, 0), "pebble mutation {} not detected", brk); }
            Err(_) => eprintln!("pebble break {}: panicked (detected)", brk),
        }
    }
}

/// Negative controls for the cap loan (GN-CAPLOAN) at the walk level: the full G walk count test at cap 878
/// (inverse pool 9 -> the loan fires at every grid cap tick) with each mutation of cap_logic_r8t's loan must
/// fail; the real routine must still pass in the same harness (control).
#[test]
fn gn_caploan_walk_negative_controls() {
    use std::sync::atomic::Ordering::Relaxed;
    std::env::set_var("LILYPAD_CAPQ", "11");
    std::env::set_var("LILYPAD_CAP", "878");
    for brk in [1u8, 2] {
        super::lilypad::GN_CAPLOAN_BREAK.store(brk, Relaxed);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| super::tests_lilypad::lilypad_g_count()));
        super::lilypad::GN_CAPLOAN_BREAK.store(0, Relaxed);
        match r {
            Ok(_) => panic!("cap-loan mutation {brk} not detected"),
            Err(_) => eprintln!("cap-loan break {brk}: detected"),
        }
    }
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| super::tests_lilypad::lilypad_g_count()));
    assert!(r.is_ok(), "cap-loan control run failed");
    eprintln!("cap-loan control (brk 0) at 878: clean");
    // the two-lane loan (short 2) at cap 877: both mutations detected, control clean
    std::env::set_var("LILYPAD_CAP", "877");
    for brk in [1u8, 2, 3, 4] {
        super::lilypad::GN_CAPLOAN_BREAK.store(brk, Relaxed);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| super::tests_lilypad::lilypad_g_count()));
        super::lilypad::GN_CAPLOAN_BREAK.store(0, Relaxed);
        match r {
            Ok(_) => panic!("two-lane cap-loan mutation {brk} not detected"),
            Err(_) => eprintln!("two-lane cap-loan break {brk}: detected"),
        }
    }
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| super::tests_lilypad::lilypad_g_count()));
    assert!(r.is_ok(), "two-lane cap-loan control run failed");
    eprintln!("two-lane cap-loan control (brk 0) at 877: clean");
}

/// Loan-moment census (GN_CAP_CENSUS): which lanes are clean on all 64 shots just before the inverse cap tick's
/// first op (the reversed cap section inside p3) at the grid cap ticks. Prints candidates per tick; the lever's
/// second borrowed lane must come from this set (or a per-parity variant of it).
#[test]
#[ignore]
fn gn_caploan_census() {
    use super::lilypad::{GN_CAP_MARKS, HB, NT, PScr, PWalk};
    use super::lilypad_g::{endpoint_adapter_g, inverse_d_len_g, inverse_sp_len_g, inverse_tmp_len_g, sched_g, walk_forward_g, walk_inverse_g, GN_P3_MARKS, GScr};
    std::env::set_var("GN_CAP_CENSUS", "1");
    let sch = sched_g();
    let qb = 13;
    let cap = 878u64;
    let mut b = B::new();
    let y = b.alloc_n(256);
    let x = b.alloc_n(256);
    let mut a = x.clone();
    a.extend(b.alloc_n(sch.w - 256));
    let mut w = PWalk { a, bb: b.alloc_n(sch.w), q: vec![], h: b.alloc_n(HB), capq: 11, log: b.alloc_n(8) };
    let live_f = b.live + 2 + NT as u64;
    let sc = PScr::alloc_fwd(&mut b, (cap - live_f) as usize);
    let div = b.new_division();
    let m = walk_forward_g(&mut b, &w, &sch, &sc, &GScr, Some(div));
    let adapter = endpoint_adapter_g(&mut b, &w, &sch, &sc);
    b.play(&adapter, false);
    b.play(&adapter, true);
    b.cx(w.h[HB - 2], w.h[HB - 1]);
    b.free(w.h[HB - 1]);
    sc.release(&mut b);
    b.acquire(w.h[HB - 1]);
    b.cx(w.h[HB - 2], w.h[HB - 1]);
    w.q = b.alloc_n(qb);
    let live_i = b.live + 2 + inverse_d_len_g() as u64 + inverse_tmp_len_g() as u64 + inverse_sp_len_g() as u64;
    let sc = PScr::alloc_inv_g(&mut b, (cap - live_i) as usize);
    walk_inverse_g(&mut b, &w, &sch, &sc, &GScr, &m, Some(div));
    b.close_division(div);
    // loan-moment stream index per inverse cap tick:
    // even ticks: the cap flattens directly into p3 at [cs, ce);
    // odd ticks (c50 bit 16 = fused path): the cap is in the hv recording fused into p3 at base + 3 + rel.
    let caps = GN_CAP_MARKS.with(|v| v.borrow().clone());
    let p3s = GN_P3_MARKS.with(|v| v.borrow().clone());
    let mut loan: std::collections::BTreeMap<usize, (usize, bool)> = std::collections::BTreeMap::new();
    for (t, cs, ce, inv) in &caps {
        if !inv { continue; }
        if let Some((_, base, pl, pp)) = p3s.iter().find(|(tt, _, _, _)| tt == t) {
            let (c0, c1) = if t % 2 == 1 { (*base + 3 + *cs, *base + 3 + *ce) } else { (*cs, *ce) };
            assert!(c0 <= *pl && c1 <= *pl && c1 >= c0, "tick {t}: cap section outside p3");
            loan.insert(*t, (*pp + (*pl - c1), t % 2 == 1));
        }
    }
    let mut rng = Rng::new(0x878);
    let xs: Vec<N> = (0..64).map(|_| { let v = rng.below(256) % p(); if v == N::ZERO { N::from(3u64) } else { v } }).collect();
    let ys: Vec<N> = (0..64).map(|_| rng.below(256) % p()).collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"gn-caploan-census");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    let mut applied = 0usize;
    let mut always_clean: Vec<u64> = vec![0u64; 64]; // bit k = shot k clean so far (across all ticks)
    for k in 0..64 { always_clean[k] = u64::MAX; }
    for (&t, &(idx, odd)) in loan.iter().rev() {
        assert!(idx >= applied, "loan indices out of stream order at t={t}");
        s.apply_iter(b.ops[applied..idx].iter());
        applied = idx;
        let qclean: Vec<usize> = w.q.iter().enumerate().filter(|(_, q)| s.qubits[q.0 as usize] == 0).map(|(i, _)| i).collect();
        for k in 0..64 {
            let mut mask = 0u64;
            for f in 0..13 {
                if (s.qubits[w.q[f].0 as usize] >> k) & 1 == 1 { mask |= 1 << f; }
            }
            always_clean[k] &= !mask;
        }
        eprintln!("tick {t} (odd={odd}) loan idx {idx}: clean qfr {qclean:?}");
    }
    let common: Vec<usize> = (0..13).filter(|&f| (0..64).all(|k| (always_clean[k] >> f) & 1 == 1)).collect();
    eprintln!("CENSUS: frames clean on all 64 shots at every grid tick: {common:?}");
}

/// Planner diagnostics for the closing-pool floor: print the greedy plan for p0 = 63 down to the refusal.
#[test]
fn gn_plan63_diag() {
    for p0 in (58usize..=64).rev() {
        for pebbled in [false, true] {
            match super::modp_ft::try_block_plan(p0, true, pebbled) {
                Ok(plan) => eprintln!("p0={p0} pebbled={pebbled}: {} blocks, end pool {} (needs >= 33): {:?}", plan.len(), p0 - 2 * plan.len(), plan),
                Err(placed) => eprintln!("p0={p0} pebbled={pebbled}: REFUSED ({placed} digits)"),
            }
        }
    }
}

/// The pebbled constant fold (GN-PEBBLE const) against const_add_pool on identical inputs (64-lane windows, odd
/// and even constants, pools from the pebbled minimum up to one below the single-bridge threshold): same sums,
/// clean, phase 0. Ported from the shelf (gn/shelf-const-add-pebbled-test.rs).
#[test]
fn gn_pebbled_const_add_matches_direct() {
    for (n, k) in [(64usize, 0x4000_0421u64), (64, 0xC0DE_CAFE_1234_5678u64), (65, 0x0000_0010_0000_0001u64), (64, 0xFFFF_FFFF_FFFF_FFFFu64)] {
        let need = n - 1 - k.trailing_zeros() as usize;
        let pmin = super::modp_ft::pebbled_min_pool(need);
        let pmax = need / 2; // 2 pool <= need
        for pool_n in [pmin, pmin + 1, pmax.max(pmin)] {
            let mut b = B::new();
            let t = b.alloc_n(n);
            let h = b.alloc();
            let big = b.alloc_n(n);
            let small = b.alloc_n(pool_n);
            super::modp_ft::const_add_pool(&mut b, &t, h, k, &big);
            let mid = b.ops.len();
            for &q in &t { b.x(q); }
            super::modp_ft::const_add_pebbled(&mut b, &t, h, k, &small);
            for &q in &t { b.x(q); }
            let mut rng = Rng::new(91);
            let tv: Vec<N> = (0..64).map(|_| rng.below(n)).collect();
            let hv: Vec<bool> = (0..64).map(|i| i % 2 == 1).collect();
            let (aq, nb, _, _) = analyze_ops(b.ops.iter());
            let mut hh = sha3::Shake256::default();
            hh.update(b"gn-cpebble");
            let mut xof = hh.finalize_xof();
            let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
            for sh in 0..64 {
                put(&mut s.qubits, &t, sh, tv[sh]);
                if hv[sh] { s.qubits[h.0 as usize] |= 1 << sh; }
            }
            s.apply_iter(b.ops[..mid].iter());
            let mask = (N::from(1u64) << n) - N::from(1u64);
            let mut badmid = 0;
            for sh in 0..64 {
                let want = if hv[sh] { (tv[sh] + N::from(k)) & mask } else { tv[sh] };
                if get(&s.qubits, &t, sh) != want { badmid += 1; }
            }
            s.apply_iter(b.ops[mid..].iter());
            let mut bad = 0;
            for sh in 0..64 { if get(&s.qubits, &t, sh) != tv[sh] { bad += 1; } }
            let mut dirty = 0u64;
            for q in big.iter().chain(&small) { dirty |= s.qubits[q.0 as usize]; }
            dirty |= s.qubits[h.0 as usize] ^ hv.iter().enumerate().fold(0u64, |a, (i, &v)| a | ((v as u64) << i));
            eprintln!("const n {} k {:#x} pool {}: bad mid {}, bad back {}, phase {:#x}, dirty {:#x}", n, k, pool_n, badmid, bad, s.phase, dirty);
            assert_eq!((badmid, bad, s.phase, dirty), (0, 0, 0, 0), "n {} pool {}", n, pool_n);
        }
    }
}

/// The Cuccaro closing compare fires exactly below the 32-lane window (p0 = 63: end pool 29 -> r 28) and not at
/// 64 (r 33 >= 32); its mutations must break the round trip.
#[test]
fn gn_cuccaro_close_negative_controls() {
    use std::sync::atomic::Ordering::Relaxed;
    let hits_before = super::modp_ft::GN_CUCCARO_HITS.load(Relaxed);
    assert_eq!(lazy_roundtrip(62, 31).1, 0, "p0=63 roundtrip must be clean with the Cuccaro close");
    assert!(super::modp_ft::GN_CUCCARO_HITS.load(Relaxed) > hits_before, "Cuccaro close did not fire at pool r=62");
    for brk in [1u8, 2] {
        super::modp_ft::GN_CUCCARO_BREAK.store(brk, Relaxed);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| lazy_roundtrip(62, 31)));
        super::modp_ft::GN_CUCCARO_BREAK.store(0, Relaxed);
        match r {
            Ok((_, badv, ph, dirty, _, _, _)) => {
                eprintln!("cuccaro break {brk}: bad {}, phase {:#x}, dirty {:#x}", badv, ph, dirty);
                assert!((badv, ph, dirty) != (0, 0, 0), "cuccaro mutation {brk} not detected");
            }
            Err(_) => eprintln!("cuccaro break {brk}: panicked (detected)"),
        }
    }
}
