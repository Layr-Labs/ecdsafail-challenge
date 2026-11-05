//! rvo1 (adversarial review of O1): probes for paths O1's own tests do not cover.

use super::builder::{B, ONE};
use super::frogdrop_sched::{p, N};
use super::tests_frogdrop::Rng;
use super::tests_o1::{get, mask, put, Fixed, Tape, TAPES};
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;

/// U20 untested branch: const_add_ms with ms.one == ONE and a real control h (not ONE, not ms.k) at a short pool now
/// lends ms.k as a carry lane (the base lent its X'd |1> lane). Exercised through mod_halve, mod_double and
/// ctrl_neg(Some(key)) at pools 56..63, against (a) integer arithmetic and (b) the same op with a real |1> lane
/// (base form): z, phase, flag, pool and key per shot, four forced tapes. Then the precondition probe: the flag preset
/// to 1 on half the shots (a state the base tolerates in these ops) to show the new form's dependence on ms.k == 0.
#[test]
fn c51_u20_msk_lend_folds() {
    use super::modp_ft::{ctrl_neg, mod_double, mod_halve, Ms};
    let pm = p();
    let inv2 = N::from(2u64).pow_mod(pm - N::from(2u64), pm);
    let mut rng = Rng::new(0x5151);
    for pool_len in [56usize, 57, 58, 59, 60, 61, 62, 63] {
        for op in 0..3 {
            // variant 0: sentinel ONE (O1), variant 1: real |1> lane (base form)
            let mut circs = vec![];
            for variant in 0..2 {
                let mut b = B::new();
                let z = b.alloc_n(256);
                let key = b.alloc();
                let flag = b.alloc();
                let r = b.alloc_n(pool_len);
                let one_lane = b.alloc();
                let one = if variant == 0 { ONE } else { b.x(one_lane); one_lane };
                let ms = Ms { k: flag, r: r.clone(), one };
                let mut zz = z.clone();
                let t0 = b.tof;
                match op {
                    0 => mod_halve(&mut b, &ms, &mut zz),
                    1 => mod_double(&mut b, &ms, &mut zz),
                    _ => ctrl_neg(&mut b, &ms, &z, Some(key)),
                }
                if variant == 1 {
                    b.x(one_lane);
                }
                let t = b.tof - t0;
                circs.push((b, z, zz, key, flag, r, t));
            }
            for dirty_flag in [false, true] {
                let mut mismatches = 0usize;
                let mut base_fail = 0usize;
                let mut one_fail = 0usize;
                for tape in TAPES {
                    for round in 0..4 {
                        let zs: Vec<N> = (0..64)
                            .map(|s| match (round, s % 8) {
                                (0, 0) => N::from(1u64),
                                (0, 1) => pm - N::from(1u64),
                                (0, 2) => N::from(1u64) << 255,
                                (0, 3) => pm - N::from(2u64),
                                _ => {
                                    let v = rng.below(256) % pm;
                                    if v.is_zero() { N::from(9u64) } else { v }
                                }
                            })
                            .collect();
                        let keys: Vec<u64> = (0..64).map(|s| ((s / 2 + round) % 2) as u64).collect();
                        let mut res = vec![];
                        for (b, z, zz, key, flag, r, _) in &circs {
                            let (nq, nb, _, _) = analyze_ops(b.ops.iter());
                            let mut xof = Fixed(tape);
                            let mut sim = Simulator::new((nq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
                            for s in 0..64 {
                                put(&mut sim.qubits, z, s, zs[s]);
                                sim.qubits[key.0 as usize] |= keys[s] << s;
                                if dirty_flag && s % 2 == 1 {
                                    sim.qubits[flag.0 as usize] |= 1 << s;
                                }
                            }
                            sim.apply_iter(b.ops.iter());
                            let outz: Vec<N> = (0..64).map(|s| get(&sim.qubits, zz, s)).collect();
                            let pool_clean: Vec<bool> = (0..64).map(|s| get(&sim.qubits, r, s).is_zero()).collect();
                            let flagv = sim.qubits[flag.0 as usize];
                            let keyv = sim.qubits[key.0 as usize];
                            res.push((outz, sim.phase, flagv, keyv, pool_clean));
                        }
                        for s in 0..64 {
                            let want = match op {
                                0 => zs[s].mul_mod(inv2, pm),
                                1 => zs[s].mul_mod(N::from(2u64), pm),
                                _ => if keys[s] == 1 { pm - zs[s] } else { zs[s] },
                            };
                            let flag_in = if dirty_flag && s % 2 == 1 { 1u64 } else { 0 };
                            let mut good = [false; 2];
                            for v in 0..2 {
                                let (o, ph, fl, kv, pc) = &res[v];
                                good[v] = o[s] % pm == want
                                    && (ph >> s) & 1 == 0
                                    && (fl >> s) & 1 == flag_in
                                    && (kv >> s) & 1 == keys[s]
                                    && pc[s];
                            }
                            if !good[1] {
                                base_fail += 1;
                            }
                            if !good[0] {
                                one_fail += 1;
                            }
                            if !dirty_flag {
                                // failure-set inclusion: the ONE form may fail only where the |1>-lane form fails
                                assert!(good[0] || !good[1], "pool {pool_len} op {op} tape {tape:x} shot {s} z {:x}: ONE form fails where base passes", zs[s]);
                                assert_eq!(res[0].0[s], res[1].0[s], "ONE vs |1> lane output, z {:x}", zs[s]);
                                assert_eq!((res[0].1 >> s) & 1, (res[1].1 >> s) & 1, "ONE vs |1> lane phase");
                            } else if good[1] && !good[0] {
                                mismatches += 1;
                            }
                        }
                    }
                }
                if dirty_flag && pool_len<=59 { assert!(mismatches>0, "dirty-ms.k negative control must detect the precondition"); }
                eprintln!(
                    "RVO1 U20 lend-k pool {pool_len} op {op} ({}): T ONE {} vs |1> lane {}; flag preset {}: failing shots ONE {} / |1> lane {} of 1024; ONE-only failures {}",
                    ["mod_halve", "mod_double", "ctrl_neg(key)"][op], circs[0].6, circs[1].6, dirty_flag, one_fail, base_fail, mismatches
                );
            }
        }
    }
}

