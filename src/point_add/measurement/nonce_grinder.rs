//! Exact, unscored nonce search. See `../memory/nonce-grinder.md`.

use super::*;
use crate::circuit::{BitId, NO_BIT};
use crate::sim::SimStats;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Mutex;
use std::thread;
use std::time::Duration;

const TAIL_OPS: usize = 96;
const NONCE_LIMIT: u64 = 1 << 48;
type Point = (U256, U256);

pub(super) fn hash_op(hash: &mut Shake256, op: &Op) {
    hash.update(&[op.kind as u8]);
    for value in [
        op.q_control2.0,
        op.q_control1.0,
        op.q_target.0,
        op.c_target.0,
        op.c_condition.0,
        op.r_target.0,
    ] {
        hash.update(&value.to_le_bytes());
    }
}

pub(super) fn hash_header(count: usize) -> Shake256 {
    let mut hash = Shake256::default();
    hash.update(b"quantum_ecc-fiat-shamir-v2");
    hash.update(&(count as u64).to_le_bytes());
    hash
}

struct NonceStream {
    ops: Vec<Op>,
    prefix: Shake256,
    tail: [Op; TAIL_OPS],
    regs: Vec<Vec<QubitOrBit>>,
    outputs: Vec<bool>,
    qubits: usize,
    bits: usize,
}

impl NonceStream {
    fn new(ops: Vec<Op>) -> Self {
        assert!(ops.len() >= TAIL_OPS, "missing nonce identity tail");
        let start = ops.len() - TAIL_OPS;
        let tail: [Op; TAIL_OPS] = ops[start..].try_into().unwrap();
        let mut prefix = hash_header(ops.len());
        let mut depth = 0usize;
        for op in &ops[..start] {
            op.validate();
            hash_op(&mut prefix, op);
            match op.kind {
                OperationType::PushCondition => depth += 1,
                OperationType::PopCondition => {
                    depth = depth.checked_sub(1).expect("unbalanced condition stack")
                }
                _ => {}
            }
        }
        assert_eq!(depth, 0, "nonce tail is inside a condition stack");
        for pair in tail.chunks_exact(2) {
            let mut expected = Op::empty();
            expected.kind = OperationType::X;
            expected.q_target = pair[0].q_target;
            assert!(expected.q_target.0 < 2, "nonce tail must address q0/q1");
            assert_eq!(pair, [expected, expected], "tail is not an X;X identity");
        }
        let (qubits, bits, _, regs) = analyze_ops(ops.iter());
        assert_eq!(regs.len(), 4);
        let mut outputs = vec![false; qubits as usize];
        let mut seen_qubits = vec![false; qubits as usize];
        let mut seen_bits = vec![false; bits as usize];
        for (index, reg) in regs.iter().enumerate() {
            assert_eq!(reg.len(), 256);
            for &item in reg {
                match item {
                    QubitOrBit::Qubit(q) if index < 2 => {
                        assert!(!seen_qubits[q.0 as usize], "aliased ABI qubit");
                        seen_qubits[q.0 as usize] = true;
                        outputs[q.0 as usize] = true;
                    }
                    QubitOrBit::Bit(b) if index >= 2 => {
                        assert!(!seen_bits[b.0 as usize], "aliased ABI bit");
                        seen_bits[b.0 as usize] = true;
                    }
                    _ => panic!("invalid register {index} type"),
                }
            }
        }
        Self {
            ops,
            prefix,
            tail,
            regs,
            outputs,
            qubits: qubits as usize,
            bits: bits as usize,
        }
    }

    fn tail(&self, nonce: u64) -> [Op; TAIL_OPS] {
        assert!(nonce < NONCE_LIMIT, "only 48 nonce bits are encoded");
        let mut tail = self.tail;
        for (bit, pair) in tail.chunks_exact_mut(2).enumerate() {
            pair[0].q_target = QubitId((nonce >> bit) & 1);
            pair[1].q_target = pair[0].q_target;
        }
        tail
    }

    fn xof(&self, nonce: u64) -> Shake256Reader {
        let mut hash = self.prefix.clone();
        for op in self.tail(nonce) {
            hash_op(&mut hash, &op);
        }
        hash.finalize_xof()
    }

    fn iter<'a>(&'a self, tail: &'a [Op; TAIL_OPS]) -> impl Iterator<Item = &'a Op> {
        self.ops[..self.ops.len() - TAIL_OPS].iter().chain(tail)
    }

    fn baseline_nonce(&self) -> u64 {
        self.tail
            .chunks_exact(2)
            .enumerate()
            .fold(0, |nonce, (bit, pair)| nonce | (pair[0].q_target.0 << bit))
    }
}

// Reassociate the exact reference curve.add operations: 32 byte-table lookups
// replace ~384 affine additions per scalar. No field implementation is replaced.
struct FixedBase {
    table: Vec<[Point; 256]>,
    curve: WeierstrassEllipticCurve,
}

impl FixedBase {
    fn new() -> Self {
        let curve = curve();
        let mut base = (curve.gx, curve.gy);
        let mut table = Vec::with_capacity(32);
        for _ in 0..32 {
            let mut row = [(U256::ZERO, U256::ZERO); 256];
            for digit in 1..256 {
                row[digit] = curve.add(row[digit - 1].0, row[digit - 1].1, base.0, base.1);
            }
            table.push(row);
            for _ in 0..8 {
                base = curve.add(base.0, base.1, base.0, base.1);
            }
        }
        Self { table, curve }
    }

    fn mul(&self, scalar: U256) -> Point {
        let mut result = (U256::ZERO, U256::ZERO);
        for (row, digit) in self.table.iter().zip(scalar.to_le_bytes::<32>()) {
            if digit != 0 {
                let point = row[digit as usize];
                result = self.curve.add(result.0, result.1, point.0, point.1);
            }
        }
        result
    }

    fn batch(&self, xof: &mut impl XofReader, remaining: &mut usize) -> Vec<Shot> {
        let mut shots = Vec::with_capacity(64);
        while *remaining > 0 && shots.len() < 64 {
            *remaining -= 1;
            let mut bytes = [0; 64];
            xof.read(&mut bytes);
            let target = self.mul(U256::from_le_slice(&bytes[..32]));
            let offset = self.mul(U256::from_le_slice(&bytes[32..]));
            if target.0 == offset.0
                || (target.0.is_zero() && target.1.is_zero())
                || (offset.0.is_zero() && offset.1.is_zero())
            {
                continue;
            }
            let expected = self.curve.add(target.0, target.1, offset.0, offset.1);
            shots.push(Shot {
                target,
                offset,
                expected,
            });
        }
        shots
    }
}

fn discard(xof: &mut impl XofReader, mut bytes: usize) {
    let mut scratch = [0; 4096];
    while bytes > 0 {
        let count = bytes.min(scratch.len());
        xof.read(&mut scratch[..count]);
        bytes -= count;
    }
}

fn rng_marker(mut xof: Shake256Reader) -> [u8; 32] {
    let mut result = [0; 32];
    XofReader::read(&mut xof, &mut result);
    result
}

fn load_batch(sim: &mut Simulator<'_, impl XofReader>, regs: &[Vec<QubitOrBit>], shots: &[Shot]) {
    sim.clear_for_shot();
    for (lane, shot) in shots.iter().enumerate() {
        for (reg, value) in
            regs.iter()
                .zip([shot.target.0, shot.target.1, shot.offset.0, shot.offset.1])
        {
            sim.set_register(reg, value, lane);
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Report {
    shots: usize,
    batches: usize,
    failures: [usize; 4],
    stats: SimStats,
    rng: [u8; 32],
}

impl Report {
    fn new(shots: usize, failures: Failures, sim: &Simulator<'_, Shake256Reader>) -> Self {
        Self {
            shots,
            batches: shots.div_ceil(64),
            failures: [
                failures.classical,
                failures.phase,
                failures.ancilla,
                failures.any,
            ],
            stats: sim.stats,
            rng: rng_marker(sim.xof.clone()),
        }
    }

    fn passed(&self) -> bool {
        self.failures[3] == 0
    }
}

fn evaluate(
    stream: &NonceStream,
    table: &FixedBase,
    nonce: u64,
    attempts: usize,
    early_abort: bool,
) -> Report {
    let mut points = stream.xof(nonce);
    let mut randomness = points.clone();
    // The harness consumes ALL attempted scalar pairs before any R/Hmr gate.
    // A separate clone permits lazy EC work without moving that RNG boundary.
    discard(&mut randomness, attempts.checked_mul(64).unwrap());
    let tail = stream.tail(nonce);
    let mut sim = Simulator::new(stream.qubits, stream.bits, &mut randomness);
    let mut remaining = attempts;
    let mut checked = 0;
    let mut failures = Failures::default();
    while remaining > 0 {
        let shots = table.batch(&mut points, &mut remaining);
        if shots.is_empty() {
            break;
        }
        load_batch(&mut sim, &stream.regs, &shots);
        sim.apply_iter(stream.iter(&tail));
        check_batch(&sim, &stream.regs, &shots, &stream.outputs, &mut failures);
        checked += shots.len();
        if early_abort && failures.any != 0 {
            break;
        }
    }
    Report::new(checked, failures, &sim)
}

// Finalists are rechecked with the original E1 sampler (curve.mul) and literal
// evaluator acceptance checks, not with a walk model or the accelerated sampler.
fn certify(stream: &NonceStream, nonce: u64, attempts: usize) -> Report {
    let mut xof = stream.xof(nonce);
    let shots = sample_points(&mut xof, attempts);
    let tail = stream.tail(nonce);
    let mut sim = Simulator::new(stream.qubits, stream.bits, &mut xof);
    let mut failures = Failures::default();
    for batch in shots.chunks(64) {
        load_batch(&mut sim, &stream.regs, batch);
        sim.apply_iter(stream.iter(&tail));
        let mask = live_mask(batch.len());
        let mut classical = 0u64;
        for (lane, shot) in batch.iter().enumerate() {
            if sim.get_register(&stream.regs[0], lane) != shot.expected.0
                || sim.get_register(&stream.regs[1], lane) != shot.expected.1
            {
                classical |= 1 << lane;
            }
        }
        let phase = sim.phase & mask;
        for reg in &stream.regs {
            for item in reg {
                if let QubitOrBit::Qubit(q) = item {
                    *sim.qubit_mut(*q) = 0;
                }
            }
        }
        let ancilla = sim.qubits.iter().fold(0, |acc, &q| acc | q) & mask;
        failures.classical += classical.count_ones() as usize;
        failures.phase += phase.count_ones() as usize;
        failures.ancilla += ancilla.count_ones() as usize;
        failures.any += (classical | phase | ancilla).count_ones() as usize;
    }
    Report::new(shots.len(), failures, &sim)
}

fn prepare() -> (NonceStream, FixedBase) {
    let start = Instant::now();
    // Do not collect the E2 census; this keeps the shared op allocation smaller.
    let ops = super::super::build();
    if let Ok(path) = std::env::var("GRIND_VERIFY_OPS") {
        verify_existing_ops(&ops, &path);
    }
    let stream = NonceStream::new(ops);
    let table = FixedBase::new();
    let digest = rng_marker(stream.xof(stream.baseline_nonce()));
    let fingerprint: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    println!(
        "GRIND_READY pid={} ops={} qubits={} bits={} baseline_nonce={} \
         baseline_xof32={} setup_seconds={:.3}",
        std::process::id(),
        stream.ops.len(),
        stream.qubits,
        stream.bits,
        stream.baseline_nonce(),
        fingerprint,
        start.elapsed().as_secs_f64()
    );
    (stream, table)
}

fn env_u64(key: &str, default: u64) -> u64 {
    std::env::var(key)
        .map(|value| {
            value
                .parse()
                .unwrap_or_else(|_| panic!("{key} must be an unsigned integer"))
        })
        .unwrap_or(default)
}

#[test]
#[ignore = "unscored exact nonce search; see memory/nonce-grinder.md"]
fn search() {
    let start_nonce = env_u64("GRIND_START", 0);
    let end_nonce = env_u64("GRIND_END", NONCE_LIMIT);
    assert!(start_nonce < end_nonce && end_nonce <= NONCE_LIMIT);
    let available = thread::available_parallelism().unwrap().get();
    let threads = usize::try_from(env_u64("GRIND_THREADS", available as u64)).unwrap();
    assert!(
        threads > 0 && threads <= available,
        "GRIND_THREADS exceeds available CPUs"
    );
    let attempts = usize::try_from(env_u64("GRIND_SHOTS", SCORED_SHOTS as u64)).unwrap();
    assert!(
        attempts > 0 && attempts <= SCORED_SHOTS,
        "GRIND_SHOTS must be 1..=9024"
    );
    let stop_on_pass = env_u64("GRIND_STOP_ON_PASS", 1);
    assert!(stop_on_pass <= 1, "GRIND_STOP_ON_PASS must be 0 or 1");
    let seconds = env_u64("GRIND_SECONDS", 0);
    let log_seconds = env_u64("GRIND_LOG_SECONDS", 10);
    assert!(log_seconds > 0);
    let (stream, table) = prepare();
    println!(
        "GRIND_SEARCH start={start_nonce} end_exclusive={end_nonce} threads={threads} \
         available_cpus={available} attempted_shots={attempts} \
         harness_sized={} stop_on_pass={stop_on_pass} limit_seconds={seconds}",
        attempts == SCORED_SHOTS
    );
    let start = Instant::now();
    let next = AtomicU64::new(start_nonce);
    let completed = AtomicU64::new(0);
    let batches = AtomicU64::new(0);
    let checked = AtomicU64::new(0);
    let passes = AtomicU64::new(0);
    let active = AtomicU64::new(threads as u64);
    let stop = AtomicBool::new(false);
    let certification = Mutex::new(());
    thread::scope(|scope| {
        let logger = scope.spawn(|| {
            while active.load(Ordering::SeqCst) > 0 {
                thread::park_timeout(Duration::from_secs(log_seconds));
                if active.load(Ordering::SeqCst) == 0 {
                    break;
                }
                let done = completed.load(Ordering::Relaxed);
                let elapsed = start.elapsed().as_secs_f64();
                println!(
                    "GRIND_PROGRESS elapsed_seconds={elapsed:.3} completed={done} \
                     nonces_per_second={:.3} checked_shots={} batches={} passes={} \
                     next_nonce={} active_workers={}",
                    done as f64 / elapsed,
                    checked.load(Ordering::Relaxed),
                    batches.load(Ordering::Relaxed),
                    passes.load(Ordering::Relaxed),
                    next.load(Ordering::Relaxed).min(end_nonce),
                    active.load(Ordering::SeqCst)
                );
            }
        });
        for worker in 0..threads {
            let logger_thread = logger.thread().clone();
            let stream = &stream;
            let table = &table;
            let next = &next;
            let completed = &completed;
            let batches = &batches;
            let checked = &checked;
            let passes = &passes;
            let active = &active;
            let stop = &stop;
            let certification = &certification;
            scope.spawn(move || {
                struct WorkerDone<'a>(&'a AtomicU64, thread::Thread);
                impl Drop for WorkerDone<'_> {
                    fn drop(&mut self) {
                        if self.0.fetch_sub(1, Ordering::SeqCst) == 1 {
                            self.1.unpark();
                        }
                    }
                }
                let _done = WorkerDone(active, logger_thread);
                while !stop.load(Ordering::Relaxed)
                    && (seconds == 0 || start.elapsed().as_secs() < seconds)
                {
                    let nonce = next.fetch_add(1, Ordering::Relaxed);
                    if nonce >= end_nonce {
                        break;
                    }
                    let result = evaluate(stream, table, nonce, attempts, true);
                    completed.fetch_add(1, Ordering::Relaxed);
                    batches.fetch_add(result.batches as u64, Ordering::Relaxed);
                    checked.fetch_add(result.shots as u64, Ordering::Relaxed);
                    if result.passed() {
                        // Avoid duplicate simultaneous expensive finalist certification.
                        let _guard = certification.lock().unwrap();
                        println!(
                            "GRIND_CANDIDATE nonce={nonce} worker={worker} checked={} \
                             failures={:?} discovery_seconds={:.3}",
                            result.shots,
                            result.failures,
                            start.elapsed().as_secs_f64()
                        );
                        let reference = certify(stream, nonce, attempts);
                        assert_eq!(
                            result, reference,
                            "fast/reference mismatch for nonce {nonce}"
                        );
                        passes.fetch_add(1, Ordering::Relaxed);
                        println!(
                            "GRIND_PASS nonce={nonce} checked={} failures={:?} harness_sized={} \
                             certified_seconds={:.3} mean_toffoli={:.6}",
                            reference.shots,
                            reference.failures,
                            attempts == SCORED_SHOTS,
                            start.elapsed().as_secs_f64(),
                            reference.stats.toffoli_gates as f64 / reference.shots.max(1) as f64
                        );
                        if stop_on_pass != 0 {
                            stop.store(true, Ordering::Relaxed);
                        }
                    }
                }
            });
        }
    });
    let elapsed = start.elapsed().as_secs_f64();
    let done = completed.load(Ordering::Relaxed);
    println!(
        "GRIND_DONE completed={done} passes={} elapsed_seconds={elapsed:.3} \
         nonces_per_second={:.3} next_nonce={} \
         note=next_nonce_is_assignment_cursor_not_safe_crash_resume_point",
        passes.load(Ordering::Relaxed),
        done as f64 / elapsed,
        next.load(Ordering::Relaxed).min(end_nonce)
    );
}

#[test]
fn fixed_base_matches_reference_and_sampler_boundaries() {
    let table = FixedBase::new();
    let curve = &table.curve;
    let mut scalars = vec![
        U256::ZERO,
        U256::from(1),
        U256::from(2),
        curve.order - U256::from(1),
        curve.order,
        curve.order + U256::from(1),
        U256::MAX,
    ];
    for bit in 0..256 {
        scalars.push(U256::from(1) << bit);
    }
    let mut rng = independent_xof(&[67; 32]);
    for _ in 0..128 {
        let mut bytes = [0; 32];
        XofReader::read(&mut rng, &mut bytes);
        scalars.push(U256::from_le_bytes(bytes));
    }
    for scalar in scalars {
        assert_eq!(table.mul(scalar), curve.mul(curve.gx, curve.gy, scalar));
    }
    for attempts in [1, 63, 64, 65, 129] {
        let mut reference_rng = independent_xof(&[attempts as u8; 32]);
        let mut fast_rng = reference_rng.clone();
        let reference = sample_points(&mut reference_rng, attempts);
        let mut remaining = attempts;
        let mut fast = Vec::new();
        while remaining > 0 {
            fast.extend(table.batch(&mut fast_rng, &mut remaining));
        }
        assert_eq!(fast.len(), reference.len());
        for (a, b) in fast.iter().zip(reference) {
            assert_eq!(a.target, b.target);
            assert_eq!(a.offset, b.offset);
            assert_eq!(a.expected, b.expected);
        }
        assert_eq!(rng_marker(fast_rng), rng_marker(reference_rng));
    }
}

#[test]
fn exclusions_consume_attempts_and_preserve_rng_boundary() {
    #[derive(Clone)]
    struct Scalars {
        data: Vec<u8>,
        cursor: usize,
    }
    impl XofReader for Scalars {
        fn read(&mut self, output: &mut [u8]) {
            output.copy_from_slice(&self.data[self.cursor..self.cursor + output.len()]);
            self.cursor += output.len();
        }
    }
    let table = FixedBase::new();
    let order = table.curve.order;
    let mut values = vec![
        (U256::ZERO, U256::from(1)),
        (U256::from(1), U256::ZERO),
        (U256::from(1), U256::from(1)),
        (U256::from(1), order - U256::from(1)),
        (order, U256::from(2)),
    ];
    values.extend((2..=66).map(|k| (U256::from(1), U256::from(k))));
    let data = values
        .iter()
        .flat_map(|(a, b)| {
            a.to_le_bytes::<32>()
                .into_iter()
                .chain(b.to_le_bytes::<32>())
        })
        .collect();
    let mut fast_rng = Scalars { data, cursor: 0 };
    let mut reference_rng = fast_rng.clone();
    let reference = sample_points(&mut reference_rng, values.len());
    let mut remaining = values.len();
    let first = table.batch(&mut fast_rng, &mut remaining);
    let second = table.batch(&mut fast_rng, &mut remaining);
    assert_eq!((first.len(), second.len(), remaining), (64, 1, 0));
    for (fast, reference) in first.iter().chain(&second).zip(reference) {
        assert_eq!(fast.target, reference.target);
        assert_eq!(fast.offset, reference.offset);
        assert_eq!(fast.expected, reference.expected);
    }
    assert_eq!(fast_rng.cursor, reference_rng.cursor);
}

#[test]
fn tail_hash_matches_literal_harness_and_production_encoder() {
    let mut tail_op = Op::empty();
    tail_op.kind = OperationType::X;
    tail_op.q_target = QubitId(0);
    let mut prefix_op = Op::empty();
    prefix_op.kind = OperationType::Hmr;
    prefix_op.q_target = QubitId(7);
    prefix_op.c_target = BitId(9);
    let mut ops = vec![prefix_op];
    ops.extend([tail_op; TAIL_OPS]);
    for nonce in [0, 1, 7_978_492, NONCE_LIMIT - 1] {
        let encoded = super::super::apply_tail_nonce(ops.clone(), nonce);
        let mut literal = hash_header(encoded.len());
        for op in &encoded {
            literal.update(&[op.kind as u8]);
            literal.update(&op.q_control2.0.to_le_bytes());
            literal.update(&op.q_control1.0.to_le_bytes());
            literal.update(&op.q_target.0.to_le_bytes());
            literal.update(&op.c_target.0.to_le_bytes());
            literal.update(&op.c_condition.0.to_le_bytes());
            literal.update(&op.r_target.0.to_le_bytes());
        }
        let mut cached = hash_header(ops.len());
        hash_op(&mut cached, &prefix_op);
        let stream = NonceStream {
            ops: ops.clone(),
            prefix: cached,
            tail: [tail_op; TAIL_OPS],
            regs: Vec::new(),
            outputs: Vec::new(),
            qubits: 8,
            bits: 10,
        };
        assert_eq!(stream.tail(nonce), encoded[1..]);
        assert_eq!(
            rng_marker(stream.xof(nonce)),
            rng_marker(literal.finalize_xof())
        );
        let mut a = stream.xof(nonce);
        let mut b = a.clone();
        for _ in 0..SCORED_SHOTS {
            let mut scalar = [0; 32];
            XofReader::read(&mut a, &mut scalar);
            XofReader::read(&mut a, &mut scalar);
        }
        discard(&mut b, SCORED_SHOTS * 64);
        assert_eq!(rng_marker(a), rng_marker(b));
        let mut rng = stream.xof(nonce);
        let mut sim = Simulator::new(8, 10, &mut rng);
        sim.qubits[0] = 0x12345678;
        sim.qubits[1] = 0x87654321;
        let before = sim.qubits.clone();
        sim.apply_iter(stream.tail(nonce).iter());
        assert_eq!(sim.qubits, before);
        assert_eq!(sim.phase, 0);
        assert!(stream.tail(nonce).iter().all(|op| op.c_condition == NO_BIT));
    }
}

#[test]
#[ignore = "full baseline positive/negative parity; builds but never writes scored artifacts"]
fn baseline_parity() {
    let (stream, table) = prepare();
    // Full literal hash (no cached prefix), as implemented by the trusted harness.
    let mut literal = hash_header(stream.ops.len());
    for op in &stream.ops {
        literal.update(&[op.kind as u8]);
        literal.update(&op.q_control2.0.to_le_bytes());
        literal.update(&op.q_control1.0.to_le_bytes());
        literal.update(&op.q_target.0.to_le_bytes());
        literal.update(&op.c_target.0.to_le_bytes());
        literal.update(&op.c_condition.0.to_le_bytes());
        literal.update(&op.r_target.0.to_le_bytes());
    }
    assert_eq!(
        rng_marker(literal.finalize_xof()),
        rng_marker(stream.xof(stream.baseline_nonce()))
    );
    for nonce in [stream.baseline_nonce(), 0] {
        let start = Instant::now();
        let fast = evaluate(&stream, &table, nonce, SCORED_SHOTS, false);
        let reference = certify(&stream, nonce, SCORED_SHOTS);
        assert_eq!(fast, reference, "full parity for nonce {nonce}");
        println!(
            "GRIND_PARITY nonce={nonce} shots={} failures={:?} seconds={:.3} \
             state_checks=classical,phase,ancilla,counts,rng",
            fast.shots,
            fast.failures,
            start.elapsed().as_secs_f64()
        );
        if nonce == stream.baseline_nonce() {
            assert!(fast.passed(), "current baseline nonce does not pass");
        }
    }
}
