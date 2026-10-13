//! E-prod scratch: shell product cost profiling and lazy-fold prototypes (count-only + exactness).
use super::builder::B;
use super::modp_ft::*;
use super::tests_chunked::expected_t;

fn et(b: &B, n0: usize) -> f64 { expected_t(&b.ops[n0..]) }

/// Per-row component costs at several pool sizes.
#[test]
#[ignore]
fn eprod_rowcost() {
    let pools: Vec<usize> = std::env::var("EP_POOLS").unwrap_or("58,64,68,74,77,90,128,167,200,256".into()).split(',').map(|s| s.parse().unwrap()).collect();
    for pl in pools {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let y = b.alloc_n(256);
        let s = b.alloc();
        let ms = Ms { k: b.alloc(), r: b.alloc_n(pl), one: b.alloc() };
        let n0 = b.ops.len();
        add_flag_u(&mut b, &ms, &z, &y);
        let add = et(&b, n0);
        let mut zz = z.clone();
        let n0 = b.ops.len();
        if pl >= SIGNED_TABLE_POOL || pl >= 64 { signed_modadd_halve(&mut b, &ms, &mut zz, &y, Some(s)); }
        let h = if pl >= 64 { et(&b, n0) } else { f64::NAN };
        let n0 = b.ops.len();
        if pl >= 64 { signed_modadd_double(&mut b, &ms, &mut zz, &y, Some(s)); }
        let d = if pl >= 64 { et(&b, n0) } else { f64::NAN };
        eprintln!("ROW pool {pl:4}: add_flag_u {add:6.1}  signed_modadd_halve {h:6.1}  signed_modadd_double {d:6.1}");
    }
}

/// Whole product units at several pools.
#[test]
#[ignore]
fn eprod_unitcost() {
    let pools: Vec<usize> = std::env::var("EP_POOLS").unwrap_or("68,77,128,167,256".into()).split(',').map(|s| s.parse().unwrap()).collect();
    for pl in pools {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let y = b.alloc_n(256);
        let a = b.alloc_n(256);
        let ms = Ms { k: b.alloc(), r: b.alloc_n(pl), one: b.alloc() };
        let mut zz = z.clone();
        let n0 = b.ops.len();
        product(&mut b, &ms, &mut zz, &a, &y);
        let p1 = et(&b, n0);
        let n0 = b.ops.len();
        product_inv(&mut b, &ms, &mut zz, &a, &y);
        let p2 = et(&b, n0);
        let mut zz = z.clone();
        let n0 = b.ops.len();
        product_tail_neg_s(&mut b, &ms, &mut zz, &a, &y, 256, false);
        let t1 = et(&b, n0);
        let n0 = b.ops.len();
        product_tail_neg_s_uncompute(&mut b, &ms, &mut zz, &a, &y, 256, false, 48);
        let t2 = et(&b, n0);
        eprintln!("UNIT pool {pl:4}: product {p1:8.0} product_inv {p2:8.0} tail {t1:8.0} tail_uncompute {t2:8.0}");
    }
}

fn put(w: &mut [u64], qs: &[crate::circuit::QubitId], shot: usize, v: super::frogdrop_sched::N) {
    for (i, q) in qs.iter().enumerate() {
        if v.bit(i) {
            w[q.0 as usize] |= 1 << shot;
        }
    }
}
fn get(w: &[u64], qs: &[crate::circuit::QubitId], shot: usize) -> super::frogdrop_sched::N {
    let mut v = super::frogdrop_sched::N::ZERO;
    for (i, q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= super::frogdrop_sched::N::from(1u64) << i;
        }
    }
    v
}

/// Exactness of the narrow fused rows (signed_modadd_halve / _double) at small pools: value, y restored, every
/// scratch lane and k clean, phase 0, over EP_BATCHES x 64 random shots plus the edge cases of strip_modadd_halve.
#[test]
fn eprod_narrow_rows_exact() {
    use super::frogdrop_sched::{p, N};
    use super::tests_frogdrop::Rng;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    let pm = p();
    let inv2 = (pm + N::from(1u64)) >> 1;
    let batches: usize = std::env::var("EP_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
    let pools: Vec<usize> = std::env::var("EP_XPOOLS").unwrap_or("68,69,70,74,80".into()).split(',').map(|s| s.parse().unwrap()).collect();
    for &pl in &pools {
        for dbl in [false, true] {
            for signed in [false, true] {
                let mut b = B::new();
                let z = b.alloc_n(256);
                let y = b.alloc_n(256);
                let sq = b.alloc();
                let ms = Ms { k: b.alloc(), r: b.alloc_n(pl), one: b.alloc() };
                b.x(ms.one);
                let mut zz = z.clone();
                let n0 = b.ops.len();
                if dbl {
                    signed_modadd_double(&mut b, &ms, &mut zz, &y, if signed { Some(sq) } else { None });
                } else {
                    signed_modadd_halve(&mut b, &ms, &mut zz, &y, if signed { Some(sq) } else { None });
                }
                let et = expected_t(&b.ops[n0..]);
                let (aq, nb, _, _) = analyze_ops(b.ops.iter());
                for bt in 0..batches {
                    let mut h = sha3::Shake256::default();
                    h.update(format!("eprod{pl}{dbl}{signed}{bt}").as_bytes());
                    let mut xof = h.finalize_xof();
                    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
                    let mut rng = Rng::new(4242 + 1000 * bt as u64 + pl as u64 + 2 * signed as u64 + 4 * dbl as u64);
                    let mut zs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
                    let mut ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
                    let ss: Vec<bool> = (0..64).map(|k| signed && (k % 2 == 1)).collect();
                    if bt == 0 {
                        zs[0] = N::ZERO;
                        ys[1] = zs[1];
                        zs[2] = pm - ys[2];
                        ys[3] = zs[3];
                        zs[4] = pm - N::from(1u64);
                        ys[5] = pm - N::from(1u64);
                        zs[6] = pm - N::from(1u64);
                        ys[6] = pm - N::from(1u64);
                        zs[7] = N::from(1u64);
                    }
                    for k in 0..64 {
                        put(&mut s.qubits, &z, k, zs[k]);
                        put(&mut s.qubits, &y, k, ys[k]);
                        if ss[k] {
                            s.qubits[sq.0 as usize] |= 1 << k;
                        }
                    }
                    s.apply_iter(b.ops.iter());
                    for k in 0..64 {
                        let sum = if ss[k] { (zs[k] + pm - ys[k]) % pm } else { (zs[k] + ys[k]) % pm };
                        let want = if dbl { (sum + sum) % pm } else { sum.mul_mod(inv2, pm) };
                        if bt == 0 && k == 2 && !ss[k] {
                            continue; // z + y = p: the known non-canonical trap of the forward add
                        }
                        assert_eq!(get(&s.qubits, &zz, k), want, "pool {pl} dbl {dbl} signed {signed} batch {bt} shot {k}");
                        assert_eq!(get(&s.qubits, &y, k), ys[k]);
                        for &q in ms.r.iter().chain([ms.k].iter()) {
                            assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "pool {pl} shot {k}: scratch dirty");
                        }
                    }
                    if s.phase != 0 { eprintln!("PHASE pool {pl} dbl {dbl} signed {signed} batch {bt}: {:#x}", s.phase); }
                }
                eprintln!("NARROW pool {pl} dbl {dbl} signed {signed}: exact over {} shots, expected T {et:.1}", 64 * batches);
            }
        }
    }
}

/// The division-2 lambda-fix sandwich at a given pool (EP_TPOOLS): z = -y C 2^-256 (unsigned 256-digit C, as
/// rec_product_tail_s on reduce_ct's lo'), value check, Z^m on z, then product_tail_neg_s_uncompute (K0 = 48);
/// z, k and every pool lane must end |0>, inputs restored, phase 0 (m bits are 0 in the simulator, so Z^m is the
/// identity and any phase is the arithmetic's own garbage).
#[test]
#[ignore]
fn eprod_lambda_fix_sandwich() {
    use super::frogdrop_sched::{p, N};
    use super::tests_frogdrop::Rng;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    let pm = p();
    let pools: Vec<usize> = std::env::var("EP_TPOOLS").unwrap_or("48,58,68,77".into()).split(',').map(|s| s.parse().unwrap()).collect();
    let batches: usize = std::env::var("EP_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    for pl in pools {
        let mut b = B::new();
        let (c, y) = (b.alloc_n(256), b.alloc_n(256));
        let ms = Ms { k: b.alloc(), r: b.alloc_n(pl), one: b.alloc() };
        b.x(ms.one);
        let z = b.alloc_n(256);
        let m = b.fresh_bits(256);
        let mut zz = z.clone();
        let n0 = b.ops.len();
        product_tail_neg_s(&mut b, &ms, &mut zz, &c, &y, 256, false);
        let tc = et(&b, n0);
        let mid = b.ops.len();
        let zmid = zz.clone();
        for i in 0..256 {
            b.z_if(zz[i], m[i]);
        }
        let n1 = b.ops.len();
        product_tail_neg_s_uncompute(&mut b, &ms, &mut zz, &c, &y, 256, false, 48);
        let tu = et(&b, n1);
        assert_eq!(zz, z);
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        let inv2 = N::from(2u64).pow_mod(pm - N::from(2u64), pm);
        let sc = inv2.pow_mod(N::from(256u64), pm);
        let (mut badv, mut dirty, mut ph) = (0, 0u64, 0u64);
        for bt in 0..batches {
            let mut rng = Rng::new(777 + pl as u64 + 31 * bt as u64);
            let cs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
            let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
            // twice: the second application cancels the Z^m kick, so a clean run leaves phase 0
            let mut h = sha3::Shake256::default();
            h.update(format!("eprod-sw{pl}{bt}").as_bytes());
            let mut xof = h.finalize_xof();
            let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
            for k in 0..64 {
                put(&mut s.qubits, &c, k, cs[k]);
                put(&mut s.qubits, &y, k, ys[k]);
            }
            s.apply_iter(b.ops[..mid].iter());
            for k in 0..64 {
                let want = (pm - cs[k].mul_mod(ys[k], pm).mul_mod(sc, pm)) % pm;
                if get(&s.qubits, &zmid, k) != want {
                    badv += 1;
                }
            }
            s.apply_iter(b.ops[mid..].iter());
            for q in z.iter().chain(&ms.r).chain([&ms.k]) {
                dirty |= s.qubits[q.0 as usize];
            }
            for k in 0..64 {
                assert_eq!(get(&s.qubits, &c, k), cs[k]);
                assert_eq!(get(&s.qubits, &y, k), ys[k]);
            }
            ph |= s.phase;
        }
        eprintln!("SANDWICH pool {pl}: compute {tc:.0} uncompute {tu:.0} total {:.0}; bad values {badv}, dirty {dirty:#x}, phase {ph:#x} over {} shots", tc + tu, 64 * batches);
        assert_eq!((badv, dirty, ph), (0, 0, 0));
    }
}
