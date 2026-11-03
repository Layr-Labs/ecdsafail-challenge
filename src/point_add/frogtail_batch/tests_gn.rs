//! Lane GN-EARLY: the lazy product pair with the early-measured forward add at short pools, round-tripped through
//! the simulator against the inherited routine on identical inputs (64 shots per pool).

use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::modp_ft::*;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

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
