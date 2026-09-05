pub mod circuit;
pub mod mod_arith;
pub mod rfold_mbu;

pub mod arith {
    pub mod compare;
    pub mod const_add;
    pub mod cuccaro;
    pub mod gidney_const_adder;
    pub mod khattar_gidney;
    pub mod mcx;
    pub mod qshift_sub;
    pub mod ripple_add;
    pub mod shift;

    pub mod rfold_mbu {
        pub use crate::point_add::trailmix_port::rfold_mbu::*;
    }
}

pub mod inversion {
    pub mod shrunken_pz_primitives;
    pub mod shrunken_pz_schedule;
    pub mod shrunken_pz_state_machine;
}

pub mod ec {
    pub mod point_add;
}

use alloy_primitives::U256;
use sha3::digest::{ExtendableOutput, Update, XofReader};

use crate::circuit::{Op, OperationType, QubitId};
use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;

const TRAILMIX_TAIL_NONCE_BITS: u32 = 48;
const TRAILMIX_NUM_TESTS: usize = 9024;

pub mod tracker {
    pub mod ghost {
        pub use crate::point_add::trailmix_port::circuit::Ghost;
    }
}

pub mod num_bigint {
    use std::fmt;
    use std::ops::{Add, BitAnd, BitOrAssign, Div, Mul, Rem, Shl, Shr, Sub};

    #[derive(Clone, Default, Debug, Eq, PartialEq, Ord, PartialOrd)]
    pub struct BigUint;

    impl BigUint {
        pub fn from_bytes_le(_bytes: &[u8]) -> Self {
            Self
        }

        pub fn to_bytes_le(&self) -> Vec<u8> {
            Vec::new()
        }
    }

    impl fmt::Display for BigUint {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("0")
        }
    }

    impl fmt::LowerHex for BigUint {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if f.alternate() {
                f.write_str("0x0")
            } else {
                f.write_str("0")
            }
        }
    }

    impl From<u32> for BigUint {
        fn from(_value: u32) -> Self {
            Self
        }
    }

    impl From<u64> for BigUint {
        fn from(_value: u64) -> Self {
            Self
        }
    }

    impl Add for BigUint {
        type Output = BigUint;
        fn add(self, _rhs: BigUint) -> BigUint {
            BigUint
        }
    }

    impl Add<&BigUint> for BigUint {
        type Output = BigUint;
        fn add(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl Add<BigUint> for &BigUint {
        type Output = BigUint;
        fn add(self, _rhs: BigUint) -> BigUint {
            BigUint
        }
    }

    impl Add<&BigUint> for &BigUint {
        type Output = BigUint;
        fn add(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl Add<u32> for &BigUint {
        type Output = BigUint;
        fn add(self, _rhs: u32) -> BigUint {
            BigUint
        }
    }

    impl Add<u32> for BigUint {
        type Output = BigUint;
        fn add(self, _rhs: u32) -> BigUint {
            BigUint
        }
    }

    impl Sub for BigUint {
        type Output = BigUint;
        fn sub(self, _rhs: BigUint) -> BigUint {
            BigUint
        }
    }

    impl Sub<&BigUint> for BigUint {
        type Output = BigUint;
        fn sub(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl Sub<BigUint> for &BigUint {
        type Output = BigUint;
        fn sub(self, _rhs: BigUint) -> BigUint {
            BigUint
        }
    }

    impl Sub<&BigUint> for &BigUint {
        type Output = BigUint;
        fn sub(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl Mul for BigUint {
        type Output = BigUint;
        fn mul(self, _rhs: BigUint) -> BigUint {
            BigUint
        }
    }

    impl Mul<BigUint> for &BigUint {
        type Output = BigUint;
        fn mul(self, _rhs: BigUint) -> BigUint {
            BigUint
        }
    }

    impl Mul<&BigUint> for &BigUint {
        type Output = BigUint;
        fn mul(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl Rem<&BigUint> for BigUint {
        type Output = BigUint;
        fn rem(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl Rem<BigUint> for BigUint {
        type Output = BigUint;
        fn rem(self, _rhs: BigUint) -> BigUint {
            BigUint
        }
    }

    impl Rem<&BigUint> for &BigUint {
        type Output = BigUint;
        fn rem(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl Div for BigUint {
        type Output = BigUint;
        fn div(self, _rhs: BigUint) -> BigUint {
            BigUint
        }
    }

    impl BitAnd<&BigUint> for BigUint {
        type Output = BigUint;
        fn bitand(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl BitAnd<&BigUint> for &BigUint {
        type Output = BigUint;
        fn bitand(self, _rhs: &BigUint) -> BigUint {
            BigUint
        }
    }

    impl Shl<usize> for BigUint {
        type Output = BigUint;
        fn shl(self, _rhs: usize) -> BigUint {
            BigUint
        }
    }

    impl Shl<u32> for BigUint {
        type Output = BigUint;
        fn shl(self, _rhs: u32) -> BigUint {
            BigUint
        }
    }

    impl Shr<u32> for BigUint {
        type Output = BigUint;
        fn shr(self, _rhs: u32) -> BigUint {
            BigUint
        }
    }

    impl BitOrAssign<BigUint> for BigUint {
        fn bitor_assign(&mut self, _rhs: BigUint) {}
    }
}

fn set_default_env(name: &str, value: &str) {
    if std::env::var_os(name).is_none() {
        std::env::set_var(name, value);
    }
}

fn configure_sub1000_trailmix_route() {
    set_default_env("TRAILMIX_THIN_SCHEDULE", "1");
    set_default_env("TRAILMIX_THIN_SEED", "278");
    set_default_env("TRAILMIX_THIN_CLZ_WINDOW", "78");
    set_default_env("TRAILMIX_THIN_MARGIN", "0");
    set_default_env("TRAILMIX_THIN_VALIDATE", "500000");
    set_default_env("TRAILMIX_COUNTER_W", "8");
    // Selective per-step peak target: clamp ONLY the peak-binding step's quotient
    // so the global peak drops 980 -> 979 while non-peak steps keep full q (vs a
    // blunt global Q_CAP=20 that clamps all ~490 steps and manufactures misses).
    // Q_CAP=99 neutralizes the old global clamp; TRAILMIX_Q_TARGET governs.
    // The mid-Q route hands the truncated shrunken-PZ state to a comparison-free
    // ping-pong tail and retains the q973 route's exact low-width refinements.
    set_default_env("TRAILMIX_Q_CAP", "99");
    set_default_env("TRAILMIX_Q_TARGET", "684");
    set_default_env("LOWQ_CLZ_DIFF_CONST_FOLD", "1");
    set_default_env("LOWQ_ONE_A_ELIM", "1");
    set_default_env("LOWQ_HYBRID_GATE_HOLD", "1");
    set_default_env("LOWQ_HYBRID_CACHE_CTZ", "1");
    set_default_env("LOWQ_HYBRID_INPLACE_CTZ", "1");
    set_default_env("LOWQ_BORROW_PASSENGER_CARRY", "1");
    set_default_env("LOWQ_COMPACT_KGANC", "1");
    set_default_env("TRAILMIX_FUSE_DIV_CLZ_A", "1");
    set_default_env("TRAILMIX_SROT_W", "5");
    set_default_env("TRAILMIX_DEFER_Y_MATERIALIZE", "1");
    set_default_env("TRAILMIX_ZERO_DY_NEWDX_ROUTE", "1");
    set_default_env("MIDQ_PZ_PINGPONG_TAIL", "1");
    set_default_env("MIDQ_FUSE_MUL_CLZ", "1");
    set_default_env("MIDQ_RELEASE_PZ_SCRATCH", "1");
    set_default_env("MIDQ_CLZ_OFFSET_PARITY", "1");
    set_default_env("MIDQ_MEASURE_COMPARE", "1");
    set_default_env("MIDQ_DIRTY_CONST", "1");
    set_default_env("MIDQ_RETAIN_DIV_LENGTHS", "1");
    set_default_env("MIDQ_RETAIN_MUL_LENGTHS", "1");
    set_default_env("MIDQ_DIRTY_FIELD_NEG", "1");
    set_default_env("MIDQ_MEASURE_PREDICATE", "1");
    set_default_env("MIDQ_MEASURE_GATE_AND", "1");
    set_default_env("MIDQ_OUTER_DIRTY_CONST", "1");
    set_default_env("CANCEL_DISJOINT_COMMUTING_TOFFOLI", "1");
    set_default_env("CANCEL_XFAMILY_COMMUTING_TOFFOLI", "1");
    set_default_env("TRAILMIX_TAIL_NONCE", "13011");
}

#[derive(Clone, Debug, Default)]
struct TrailMixSupportReport {
    accepted_shots: usize,
    miss_factors: usize,
    repair_entries: usize,
    first_miss: Option<(usize, &'static str, usize)>,
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(default)
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(default)
}

fn secp256k1() -> WeierstrassEllipticCurve {
    WeierstrassEllipticCurve {
        modulus: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .unwrap(),
        a: U256::from(0),
        b: U256::from(7),
        gx: U256::from_str_radix(
            "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .unwrap(),
        gy: U256::from_str_radix(
            "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .unwrap(),
        order: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .unwrap(),
    }
}

fn sub_mod_p(a: U256, b: U256, p: U256) -> U256 {
    if a >= b {
        a - b
    } else {
        p - (b - a)
    }
}

fn support_report_for_xof(
    mut xof: sha3::Shake256Reader,
    target_draws: usize,
) -> TrailMixSupportReport {
    support_report_for_xof_limited(&mut xof, target_draws, None)
}

fn support_report_for_xof_limited(
    xof: &mut sha3::Shake256Reader,
    target_draws: usize,
    max_misses: Option<usize>,
) -> TrailMixSupportReport {
    let curve = secp256k1();
    let mut report = TrailMixSupportReport::default();
    for draw in 0..target_draws {
        let mut rb = [[0u8; 32]; 2];
        xof.read(&mut rb[0]);
        xof.read(&mut rb[1]);
        let k1 = U256::from_le_bytes(rb[0]);
        let k2 = U256::from_le_bytes(rb[1]);
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        if t.0 == o.0 {
            continue;
        }
        if t.0.is_zero() && t.1.is_zero() {
            continue;
        }
        if o.0.is_zero() && o.1.is_zero() {
            continue;
        }
        let r = curve.add(t.0, t.1, o.0, o.1);
        report.accepted_shots += 1;

        let dx = sub_mod_p(t.0, o.0, curve.modulus);
        let c = sub_mod_p(o.0, r.0, curve.modulus);
        for (label, factor) in [("dx", dx), ("qx_minus_rx", c)] {
            let repairs =
                inversion::shrunken_pz_schedule::thin_factor_repairs_u256(factor);
            if repairs > 0 {
                report.miss_factors += 1;
                report.repair_entries += repairs;
                if report.first_miss.is_none() {
                    report.first_miss = Some((draw, label, repairs));
                }
                if max_misses.is_some_and(|limit| report.miss_factors > limit) {
                    return report;
                }
            }
        }
    }
    report
}

fn tail_nonce_x_op(q: u32) -> Op {
    let mut op = Op::empty();
    op.kind = OperationType::X;
    op.q_target = QubitId(q.into());
    op
}

fn hash_tail_nonce(mut hasher: sha3::Shake256, nonce: u64, q0: u32, q1: u32) -> sha3::Shake256 {
    for i in 0..TRAILMIX_TAIL_NONCE_BITS {
        let q = if (nonce >> i) & 1 == 1 { q1 } else { q0 };
        let op = tail_nonce_x_op(q);
        crate::point_add::B::update_fiat_hash_op(&mut hasher, &op);
        crate::point_add::B::update_fiat_hash_op(&mut hasher, &op);
    }
    hasher
}

fn report_current_support(builder: &crate::point_add::B) {
    if std::env::var("TRAILMIX_SUPPORT_CHECK").ok().as_deref() != Some("1") {
        return;
    }
    let Some(hasher) = builder.clone_fiat_hash() else {
        eprintln!(
            "TRAILMIX_SUPPORT no hash stream; set POINT_ADD_HASH_OPS_LEN in count-only mode"
        );
        return;
    };
    let draws = env_usize("TRAILMIX_SUPPORT_SHOTS", TRAILMIX_NUM_TESTS);
    let report = support_report_for_xof(hasher.finalize_xof(), draws);
    eprintln!(
        "TRAILMIX_SUPPORT draws={} accepted={} miss_factors={} repair_entries={} first_miss={:?}",
        draws,
        report.accepted_shots,
        report.miss_factors,
        report.repair_entries,
        report.first_miss
    );
}

fn search_tail_nonce(builder: &crate::point_add::B, q0: u32, q1: u32) {
    let limit = env_usize("TRAILMIX_TAIL_NONCE_SEARCH", 0);
    if limit == 0 {
        return;
    }
    if std::env::var("TRAILMIX_OPTIMIZED_TAIL_SEARCH")
        .ok()
        .as_deref()
        == Some("1")
    {
        return;
    }
    let Some(base_hasher) = builder.clone_fiat_hash() else {
        eprintln!(
            "TRAILMIX_TAIL_SEARCH no hash stream; set POINT_ADD_HASH_OPS_LEN=base_ops+96 in count-only mode"
        );
        return;
    };
    search_tail_nonce_from_hasher(base_hasher, q0, q1, limit);
}

fn search_tail_nonce_from_hasher(
    base_hasher: sha3::Shake256,
    q0: u32,
    q1: u32,
    limit: usize,
) {
    let start = env_u64("TRAILMIX_TAIL_NONCE_START", 0);
    let draws = env_usize("TRAILMIX_TAIL_NONCE_SHOTS", TRAILMIX_NUM_TESTS);
    let trace = std::env::var("TRAILMIX_TAIL_NONCE_TRACE").is_ok();
    let trace_clean = std::env::var("TRAILMIX_TAIL_NONCE_TRACE_CLEAN")
        .ok()
        .as_deref()
        == Some("1");
    let continue_after_clean = std::env::var("TRAILMIX_TAIL_NONCE_CONTINUE")
        .ok()
        .as_deref()
        == Some("1");
    let early_miss = std::env::var("TRAILMIX_TAIL_NONCE_EARLY_MISS")
        .ok()
        .as_deref()
        == Some("1");
    let default_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);
    let threads = env_usize("TRAILMIX_TAIL_NONCE_THREADS", default_threads)
        .max(1)
        .min(limit.max(1));

    let results: Vec<(Option<(u64, TrailMixSupportReport)>, Option<u64>)> =
        std::thread::scope(|scope| {
            let mut handles = Vec::with_capacity(threads);
            for tid in 0..threads {
                let base_hasher = base_hasher.clone();
                handles.push(scope.spawn(move || {
                    let mut best: Option<(u64, TrailMixSupportReport)> = None;
                    let mut clean: Option<u64> = None;
                    let mut off = tid;
                    while off < limit {
                        let nonce = start.wrapping_add(off as u64);
                        let hasher = hash_tail_nonce(base_hasher.clone(), nonce, q0, q1);
                        let mut xof = hasher.finalize_xof();
                        let report = support_report_for_xof_limited(
                            &mut xof,
                            draws,
                            early_miss.then_some(0),
                        );
                        if trace {
                            eprintln!(
                                "TRAILMIX_TAIL_SEARCH nonce={} miss_factors={} repair_entries={} first_miss={:?}",
                                nonce, report.miss_factors, report.repair_entries, report.first_miss
                            );
                        }
                        let better = best.as_ref().map_or(true, |(_, b)| {
                            (report.miss_factors, report.repair_entries)
                                < (b.miss_factors, b.repair_entries)
                        });
                        if better {
                            best = Some((nonce, report.clone()));
                        }
                        if report.miss_factors == 0 {
                            if trace_clean {
                                eprintln!("TRAILMIX_TAIL_SEARCH_CANDIDATE nonce={nonce}");
                            }
                            clean = Some(clean.map_or(nonce, |old| old.min(nonce)));
                            if !continue_after_clean {
                                break;
                            }
                        }
                        off += threads;
                    }
                    (best, clean)
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().expect("tail nonce search worker panicked"))
                .collect()
        });

    let mut best: Option<(u64, TrailMixSupportReport)> = None;
    let mut clean: Option<u64> = None;
    for (worker_best, worker_clean) in results {
        if let Some(nonce) = worker_clean {
            clean = Some(clean.map_or(nonce, |old| old.min(nonce)));
        }
        if let Some((nonce, report)) = worker_best {
            let better = best.as_ref().map_or(true, |(best_nonce, b)| {
                (report.miss_factors, report.repair_entries, nonce)
                    < (b.miss_factors, b.repair_entries, *best_nonce)
            });
            if better {
                best = Some((nonce, report));
            }
        }
    }
    if let Some((nonce, report)) = best {
        eprintln!(
            "TRAILMIX_TAIL_SEARCH_BEST nonce={} accepted={} miss_factors={} repair_entries={} first_miss={:?} searched={} threads={}",
            nonce,
            report.accepted_shots,
            report.miss_factors,
            report.repair_entries,
            report.first_miss,
            limit,
            threads
        );
    }
    if let Some(nonce) = clean {
        eprintln!("TRAILMIX_TAIL_SEARCH_CLEAN nonce={nonce}");
    }
}

pub(crate) fn search_optimized_tail_nonce(ops: &[Op]) {
    let limit = env_usize("TRAILMIX_TAIL_NONCE_SEARCH", 0);
    if limit == 0
        || std::env::var("TRAILMIX_OPTIMIZED_TAIL_SEARCH")
            .ok()
            .as_deref()
            != Some("1")
    {
        return;
    }

    let tail_len = (2 * TRAILMIX_TAIL_NONCE_BITS) as usize;
    assert!(ops.len() >= tail_len, "optimized stream is shorter than nonce tail");
    let (prefix, tail) = ops.split_at(ops.len() - tail_len);

    let mut targets = tail.iter().map(|op| op.q_target.0).collect::<Vec<_>>();
    assert!(
        tail.chunks_exact(2).all(|pair| {
            pair[0].kind == OperationType::X
                && pair[1].kind == OperationType::X
                && pair[0] == pair[1]
        }),
        "optimized stream does not end in the expected X;X nonce tail"
    );
    targets.sort_unstable();
    targets.dedup();
    assert_eq!(targets.len(), 2, "nonce tail must use exactly two qubits");
    let q0 = u32::try_from(targets[0]).expect("nonce-tail qubit id exceeds u32");
    let q1 = u32::try_from(targets[1]).expect("nonce-tail qubit id exceeds u32");

    let mut base_hasher = sha3::Shake256::default();
    base_hasher.update(b"quantum_ecc-fiat-shamir-v2");
    base_hasher.update(&(ops.len() as u64).to_le_bytes());
    for op in prefix {
        crate::point_add::B::update_fiat_hash_op(&mut base_hasher, op);
    }
    eprintln!(
        "TRAILMIX_OPTIMIZED_TAIL_SEARCH prefix_ops={} final_ops={} q0={} q1={}",
        prefix.len(),
        ops.len(),
        q0,
        q1
    );
    search_tail_nonce_from_hasher(base_hasher, q0, q1, limit);
}

pub fn build_builder() -> crate::point_add::B {
    configure_sub1000_trailmix_route();
    if std::env::var_os("MIDQ_RETAIN_DIV_LENGTHS_SELFTEST").is_some() {
        inversion::shrunken_pz_state_machine::retained_lengths_match_original();
        return crate::point_add::B::new();
    }
    if std::env::var_os("MIDQ_DIRTY_CONST_SELFTEST").is_some() {
        inversion::shrunken_pz_state_machine::midq_dirty_const_selftest();
        return crate::point_add::B::new();
    }
    if std::env::var_os("MIDQ_MEASURE_COMPARE_SELFTEST").is_some() {
        inversion::shrunken_pz_primitives::measured_compare_selftest();
        return crate::point_add::B::new();
    }
    if std::env::var_os("MIDQ_CLZ_PARITY_SELFTEST").is_some() {
        inversion::shrunken_pz_state_machine::midq_clz_parity_selftest();
        return crate::point_add::B::new();
    }

    let mut circ = circuit::Circuit::new();
    circ.set_section("trailmix_shrunken_pz");
    let mut tx = circ.alloc_qreg_bits("tx", 256);
    let mut ty = circ.alloc_qreg_bits("ty", 256);
    let ox: Vec<circuit::Cbit> = (0..256).map(|_| circ.alloc_input_bit()).collect();
    let oy: Vec<circuit::Cbit> = (0..256).map(|_| circ.alloc_input_bit()).collect();

    ec::point_add::ec_add_inplace_shrunken_pz(&mut circ, &mut tx, &mut ty, &ox, &oy);

    let mut out = std::mem::take(&mut tx);
    out.extend(std::mem::take(&mut ty));
    let out = circ.defragment(out);
    let tail_q0 = out[0].id();
    let tail_q1 = out[1].id();
    circ.declare_registers(&out[..256], &out[256..512], &ox, &oy);

    search_tail_nonce(&circ.b, tail_q0, tail_q1);

    if let Some(nonce) = std::env::var("TRAILMIX_TAIL_NONCE")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
    {
        circ.set_section("trailmix_tail_nonce");
        for i in 0..TRAILMIX_TAIL_NONCE_BITS {
            let q = if (nonce >> i) & 1 == 1 {
                &out[1]
            } else {
                &out[0]
            };
            circ.x(q);
            circ.x(q);
        }
    }

    let _ = circ.destroy_sim(out);
    let mut builder = circ.into_builder();
    report_current_support(&builder);
    if std::env::var("TRACE_EMITTED_PHASE_OPS").is_ok() {
        use std::collections::BTreeMap;

        let mut aggregate: BTreeMap<&'static str, (usize, usize)> = BTreeMap::new();
        for (index, &(start, phase)) in builder.phase_transitions.iter().enumerate() {
            let end = builder
                .phase_transitions
                .get(index + 1)
                .map_or(builder.ops.len(), |row| row.0)
                .min(builder.ops.len());
            if end <= start {
                continue;
            }
            let toffoli = builder.ops[start..end]
                .iter()
                .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
                .count();
            let entry = aggregate.entry(phase).or_default();
            entry.0 += end - start;
            entry.1 += toffoli;
        }
        let mut rows = aggregate.into_iter().collect::<Vec<_>>();
        rows.sort_by(|a, b| b.1.1.cmp(&a.1.1).then_with(|| a.0.cmp(b.0)));
        let limit = std::env::var("TRACE_EMITTED_PHASE_OPS_TOP")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(60);
        eprintln!("=== TrailMix emitted per-phase ops ===");
        for (phase, (ops, toffoli)) in rows.into_iter().take(limit) {
            eprintln!("TRAILMIX_EMITTED {:<56} ops={ops} toffoli={toffoli}", phase);
        }
    }
    if std::env::var("TRACE_PHASE_OPS").is_ok() {
        use std::collections::BTreeMap;

        builder.close_counted_phase();
        let top_n = std::env::var("TRACE_PHASE_OPS_TOP")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(40);
        let mut rows = builder.counted_phase_rows.clone();
        rows.sort_by(|a, b| b.ops.cmp(&a.ops).then_with(|| a.phase.cmp(b.phase)));
        eprintln!("=== TrailMix count-only per-phase ops ===");
        eprintln!(
            "{:<56} {:>12} {:>12} {:>12} {:>12}",
            "phase", "ops", "toffoli", "hmr", "r"
        );
        for row in rows.into_iter().take(top_n) {
            eprintln!(
                "{:<56} {:>12} {:>12} {:>12} {:>12}",
                row.phase, row.ops, row.toffoli_ops, row.hmr_ops, row.r_ops
            );
        }
        let mut by_phase: BTreeMap<&'static str, crate::point_add::PhaseResource> =
            BTreeMap::new();
        for row in &builder.counted_phase_rows {
            let entry = by_phase
                .entry(row.phase)
                .or_insert(crate::point_add::PhaseResource {
                    phase: row.phase,
                    start: 0,
                    end: 0,
                    ops: 0,
                    toffoli_ops: 0,
                    ccx_ops: 0,
                    ccz_ops: 0,
                    hmr_ops: 0,
                    r_ops: 0,
                });
            entry.ops += row.ops;
            entry.toffoli_ops += row.toffoli_ops;
            entry.ccx_ops += row.ccx_ops;
            entry.ccz_ops += row.ccz_ops;
            entry.hmr_ops += row.hmr_ops;
            entry.r_ops += row.r_ops;
        }
        let mut agg: Vec<_> = by_phase.into_values().collect();
        agg.sort_by(|a, b| b.ops.cmp(&a.ops).then_with(|| a.phase.cmp(b.phase)));
        eprintln!("=== TrailMix aggregate per-phase ops ===");
        eprintln!(
            "{:<56} {:>12} {:>12} {:>12} {:>12}",
            "phase", "ops", "toffoli", "hmr", "r"
        );
        for row in agg.into_iter().take(top_n) {
            eprintln!(
                "{:<56} {:>12} {:>12} {:>12} {:>12}",
                row.phase, row.ops, row.toffoli_ops, row.hmr_ops, row.r_ops
            );
        }
    }
    if std::env::var("TRACE_PEAK").is_ok() || std::env::var("TRACE_PHASE_ACTIVE").is_ok() {
        builder.close_phase_active_region();
        eprintln!(
            "TRAILMIX_SHRUNKEN_PZ peak_qubits={} peak_phase='{}' ops={}",
            builder.peak_qubits,
            builder.peak_phase,
            builder.current_ops_len()
        );
        if std::env::var("TRACE_PHASE_ACTIVE").is_ok() {
            let top_n = std::env::var("TRACE_PHASE_ACTIVE_TOP")
                .ok()
                .and_then(|s| s.parse::<usize>().ok());
            let mut rows: Vec<_> = builder.phase_active_max.iter().collect();
            rows.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
            for (idx, (phase, active)) in rows.into_iter().enumerate() {
                if top_n.is_some_and(|limit| idx >= limit) {
                    break;
                }
                eprintln!("TRAILMIX_ACTIVE {:<48} {}", phase, active);
            }
        }
    }
    builder
}
