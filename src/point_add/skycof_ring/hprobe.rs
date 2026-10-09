//! Research probe (`SKYCOF_RESEARCH=1 SKYCOF_PROBE=hyb SKYCOF_HYB_T1=<t1>`): the hybrid walk forward and back
//! with a 256-wire passenger at the source cap, simulated on `SKYCOF_RING_BATCHES` x 64 random `d`.
use super::wtest;
use ruint::Uint;

type U = Uint<512, 8>;

fn rng_next(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

pub fn run() {
    let env = super::pointadd::envelope().clone();
    let t1 = super::pointadd::t1();
    assert!(t1 > 0, "set SKYCOF_HYB_T1");
    let t0 = std::time::Instant::now();
    let bt = wtest::build_hyb(&env, 256, t1);
    let (tf, tb) = (super::selftest::expected_ccx(&bt.ops_f), super::selftest::expected_ccx(&bt.ops_b));
    eprintln!("HYBPROBE built t1={t1} cap={:?} peak={} ops_f={} ops_b={} exp_T fwd={tf:.0} back={tb:.0} ({:.1}s)", env.cap, bt.peak,
        bt.ops_f.len(), bt.ops_b.len(), t0.elapsed().as_secs_f64());
    let batches: usize = crate::point_add::skycof::pointadd::knob("SKYCOF_RING_BATCHES").and_then(|v| v.parse().ok()).unwrap_or(4);
    let p = U::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    let mut seed: u64 = 0x5eed_4b1d;
    let mut ds = Vec::new();
    while ds.len() < 64 * batches {
        let mut v = U::ZERO;
        for i in 0..4 {
            v |= U::from(rng_next(&mut seed)) << (64 * i);
        }
        let v = v.reduce_mod(p);
        if !v.is_zero() {
            ds.push(v);
        }
    }
    if let Some(v) = crate::point_add::skycof::pointadd::knob("SKYCOF_PROBE_D") {
        // fixed inputs (hex, comma separated) instead of the random batch
        ds = v.split(',').filter(|s| !s.is_empty()).map(|h| U::from_str_radix(h.trim().trim_start_matches("0x"), 16).unwrap()).collect();
        while ds.len() % 64 != 0 {
            ds.push(U::from(1u64));
        }
    }
    let bad = wtest::simulate(&bt, &env, p, &ds, 77);
    for (i, why) in bad.iter().take(10) {
        eprintln!("HYBPROBE fail d={:#x}: {why}", ds[*i]);
    }
    eprintln!("HYBPROBE walks={} failed={} ({:.1}s)", ds.len(), bad.len(), t0.elapsed().as_secs_f64());
}
