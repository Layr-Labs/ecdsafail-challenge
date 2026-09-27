//! Unscored, test-only laboratory. See `memory/measurement.md` for commands.
//! Nothing in this module is linked into a normal build or writes an artifact.

use std::cell::{Cell, RefCell};
use std::fs::File;
use std::io::{BufReader, Read};
use std::ops::Range;
use std::time::Instant;

use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256, Shake256Reader,
};

use crate::circuit::{analyze_ops, Op, OperationType, QubitId, QubitOrBit, NO_QUBIT};
use crate::sim::Simulator;
use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;

const PHASES: usize = 6;
const SCORED_SHOTS: usize = 9024;

pub(super) mod replay;
pub(super) mod experiments;
mod walk;
mod stages;
mod nonce_grinder;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(super) enum Phase {
    Replay,
    WalkForward,
    WalkBackward,
    Square,
    Coordinates,
    Other,
}

impl Phase {
    const ALL: [Self; PHASES] = [
        Self::Replay,
        Self::WalkForward,
        Self::WalkBackward,
        Self::Square,
        Self::Coordinates,
        Self::Other,
    ];

    fn name(self) -> &'static str {
        match self {
            Self::Replay => "replay/modular-update",
            Self::WalkForward => "GCD-walk-forward",
            Self::WalkBackward => "GCD-walk-backward",
            Self::Square => "square",
            Self::Coordinates => "coordinate-add/sub",
            Self::Other => "other",
        }
    }

    fn from_builder(name: &str) -> Self {
        if name.starts_with("coord_") {
            Self::Coordinates
        } else if name == "square" {
            Self::Square
        } else if name.ends_with("_walkback") {
            Self::WalkBackward
        } else if name.ends_with("_walk") {
            Self::WalkForward
        } else if name.ends_with("_replay") {
            Self::Replay
        } else {
            Self::Other
        }
    }
}

#[derive(Default)]
struct Trace {
    tags: Vec<Phase>,
    peak_live: [u32; PHASES],
    rewrite: Option<RewriteTrace>,
    replay: replay::Trace,
}

struct RewriteTrace {
    input: Vec<Phase>,
    consumed: usize,
}

thread_local! {
    static TRACE: RefCell<Option<Trace>> = const { RefCell::new(None) };
    static OVERRIDE: Cell<Option<Phase>> = const { Cell::new(None) };
}

pub(super) struct Scope(Option<Phase>);

impl Drop for Scope {
    fn drop(&mut self) {
        OVERRIDE.set(self.0);
    }
}

pub(super) fn scope(phase: Phase) -> Scope {
    Scope(OVERRIDE.replace(Some(phase)))
}

pub(super) fn capturing() -> bool {
    TRACE.with_borrow(Option::is_some)
}

fn phase(name: &str) -> Phase {
    OVERRIDE.get().unwrap_or_else(|| Phase::from_builder(name))
}

pub(super) fn record_peak(name: &str, active: u32) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            static LIMIT: std::sync::OnceLock<Option<u32>> = std::sync::OnceLock::new();
            if let Some(limit) = LIMIT.get_or_init(|| match std::env::var("MEASURE_ASSERT_QUBITS") {
                Ok(value) => Some(value.parse().expect("MEASURE_ASSERT_QUBITS must be an integer")),
                Err(std::env::VarError::NotPresent) => None,
                Err(std::env::VarError::NotUnicode(_)) => panic!("MEASURE_ASSERT_QUBITS is not Unicode"),
            }) {
                assert!(active <= *limit, "quantum allocation budget exceeded in {name}: {active} > {limit}");
            }
            let peak = &mut trace.peak_live[phase(name) as usize];
            *peak = (*peak).max(active);
            trace.replay.peak(active);
        }
    });
}

pub(super) fn record_op(name: &str, active: u32, index: usize) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            let phase = phase(name);
            assert_eq!(trace.tags.len(), index);
            trace.tags.push(phase);
            trace.replay.record(active, index);
            let peak = &mut trace.peak_live[phase as usize];
            *peak = (*peak).max(active);
        }
    });
}

pub(super) fn begin_rewrite(input_len: usize) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            assert!(trace.rewrite.is_none());
            assert_eq!(trace.tags.len(), input_len);
            trace.rewrite = Some(RewriteTrace {
                input: std::mem::replace(&mut trace.tags, Vec::with_capacity(input_len)),
                consumed: 0,
            });
            trace.replay.begin_rewrite(input_len);
        }
    });
}

// Each original operation produces zero, one, or two outputs. Expanded product
// rewrites inherit the original label on both their X and CX.
pub(super) fn rewritten_op(output_len: usize) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            let Some(rewrite) = &mut trace.rewrite else {
                return;
            };
            let tag = rewrite.input[rewrite.consumed];
            rewrite.consumed += 1;
            trace.replay.rewritten_op(output_len);
            let added = output_len.checked_sub(trace.tags.len()).unwrap();
            assert!(added <= 2, "rewrite emitted more than two operations");
            trace.tags.extend(std::iter::repeat_n(tag, added));
        }
    });
}

pub(super) fn end_rewrite(output_len: usize) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            let rewrite = trace.rewrite.take().unwrap();
            assert_eq!(rewrite.consumed, rewrite.input.len());
            assert_eq!(trace.tags.len(), output_len);
            trace.replay.end_rewrite(output_len);
        }
    });
}

pub(super) fn append_tail(count: usize) {
    TRACE.with_borrow_mut(|trace| {
        if let Some(trace) = trace {
            trace.tags.extend(std::iter::repeat_n(Phase::Other, count));
            trace.replay.append_tail(count);
        }
    });
}

struct Capture;

impl Capture {
    fn start() -> Self {
        TRACE.with_borrow_mut(|trace| {
            assert!(trace.is_none(), "nested measurement capture");
            *trace = Some(Trace::default());
        });
        Self
    }

    fn finish(self) -> Trace {
        TRACE.with_borrow_mut(|trace| trace.take().unwrap())
    }
}

impl Drop for Capture {
    fn drop(&mut self) {
        TRACE.with_borrow_mut(|trace| *trace = None);
    }
}

struct Span {
    phase: Phase,
    ops: Range<usize>,
}

struct Census {
    spans: Vec<Span>,
    emitted: [u64; PHASES],
    max_wire_width: [u64; PHASES],
    peak_live: [u32; PHASES],
    replay: replay::Census,
}

impl Census {
    fn new(ops: &[Op], trace: Trace) -> Self {
        assert_eq!(ops.len(), trace.tags.len());
        let replay = replay::Census::new(ops, &trace.tags, trace.replay);
        let mut spans: Vec<Span> = Vec::new();
        let mut emitted = [0; PHASES];
        let mut max_wire_width = [0; PHASES];
        let mut condition_depth = 0usize;
        for (index, (op, &phase)) in ops.iter().zip(&trace.tags).enumerate() {
            op.validate();
            if spans.last().is_none_or(|span| span.phase != phase) {
                // Simulator::apply_iter starts a fresh condition stack each call.
                // Never silently split a live PUSH_CONDITION across calls.
                assert_eq!(
                    condition_depth, 0,
                    "phase boundary inside condition at {index}"
                );
                spans.push(Span {
                    phase,
                    ops: index..index,
                });
            }
            spans.last_mut().unwrap().ops.end = index + 1;
            match op.kind {
                OperationType::PushCondition => condition_depth += 1,
                OperationType::PopCondition => {
                    condition_depth = condition_depth.checked_sub(1).expect("unbalanced POP");
                }
                OperationType::CCX | OperationType::CCZ => emitted[phase as usize] += 1,
                _ => {}
            }
            for q in [op.q_control2, op.q_control1, op.q_target] {
                if q != NO_QUBIT {
                    let width = &mut max_wire_width[phase as usize];
                    *width = (*width).max(q.0 + 1);
                }
            }
        }
        assert_eq!(condition_depth, 0);
        Self {
            spans,
            emitted,
            max_wire_width,
            peak_live: trace.peak_live,
            replay,
        }
    }

    fn apply<R: XofReader>(&self, sim: &mut Simulator<'_, R>, ops: &[Op]) -> [u64; PHASES] {
        let before = sim.stats.toffoli_gates;
        let mut counts = [0; PHASES];
        for span in &self.spans {
            let start = sim.stats.toffoli_gates;
            sim.apply_iter(ops[span.ops.clone()].iter());
            counts[span.phase as usize] += sim.stats.toffoli_gates - start;
        }
        assert_eq!(counts.iter().sum::<u64>(), sim.stats.toffoli_gates - before);
        counts
    }

    fn print(&self, executed: Option<(&[u64; PHASES], usize)>) {
        println!("phase\temitted_CCX_CCZ\texecuted_per_shot\tshare_percent\tpeak_live\tmax_wire_id_plus_1");
        let total = executed.map(|(counts, _)| counts.iter().sum::<u64>() as f64);
        for phase in Phase::ALL {
            let p = phase as usize;
            let (avg, share) = executed.map_or((f64::NAN, f64::NAN), |(counts, shots)| {
                (
                    counts[p] as f64 / shots as f64,
                    100.0 * counts[p] as f64 / total.unwrap(),
                )
            });
            println!(
                "{}\t{}\t{avg:.3}\t{share:.4}\t{}\t{}",
                phase.name(),
                self.emitted[p],
                self.peak_live[p],
                self.max_wire_width[p]
            );
        }
        println!(
            "TOTAL emitted={} peak_live={} scored_width={} phase_spans={}",
            self.emitted.iter().sum::<u64>(),
            self.peak_live.iter().max().unwrap(),
            self.max_wire_width.iter().max().unwrap(),
            self.spans.len()
        );
    }
}

fn build_measured() -> (Vec<Op>, Census) {
    experiments::describe();
    let (walk_widths, multiply_rounds) = super::pingpong::measurement_walk_widths();
    let extra = super::pingpong::measurement_exact_tail_start()
        .map_or(0, |start| walk_widths.len() - start);
    println!("ROUNDS native_divide={} native_multiply={} exact_tail={extra} retired_signs={}",
        walk_widths.len()-extra, multiply_rounds-extra, super::pingpong::measurement_retired_signs());
    let start = Instant::now();
    let capture = Capture::start();
    let ops = super::build();
    let trace = capture.finish();
    let census = Census::new(&ops, trace);
    println!(
        "BUILD ops={} seconds={:.3}",
        ops.len(),
        start.elapsed().as_secs_f64()
    );
    if let Ok(path) = std::env::var("MEASURE_VERIFY_OPS") {
        verify_existing_ops(&ops, &path);
    }
    (ops, census)
}

fn op_bytes(op: &Op) -> [u8; 56] {
    let mut record = [0; 56];
    record[..4].copy_from_slice(&(op.kind as u32).to_le_bytes());
    for (slot, value) in record[8..].chunks_exact_mut(8).zip([
        op.q_control2.0,
        op.q_control1.0,
        op.q_target.0,
        op.c_target.0,
        op.c_condition.0,
        op.r_target.0,
    ]) {
        slot.copy_from_slice(&value.to_le_bytes());
    }
    record
}

// Read-only comparison with the existing baseline; never invokes build_circuit's main.
fn verify_existing_ops(ops: &[Op], path: &str) {
    let mut file = File::open(path).expect("open existing operation artifact");
    let mut header = [0; 16];
    file.read_exact(&mut header).unwrap();
    assert_eq!(&header[..8], b"QECCOPSZ");
    assert_eq!(
        u64::from_le_bytes(header[8..].try_into().unwrap()),
        ops.len() as u64
    );
    let mut decoder = zstd::stream::read::Decoder::new(BufReader::new(file)).unwrap();
    decoder.window_log_max(27).unwrap();
    let mut record = [0; 56];
    for (index, op) in ops.iter().enumerate() {
        decoder.read_exact(&mut record).unwrap();
        assert_eq!(
            record,
            op_bytes(op),
            "baseline mismatch at operation {index}"
        );
    }
    assert_eq!(decoder.read(&mut [0]).unwrap(), 0);
    println!(
        "STREAM_IDENTITY all {} records match {path}; file opened read-only",
        ops.len()
    );
}

fn curve() -> WeierstrassEllipticCurve {
    let hex = |text| U256::from_str_radix(text, 16).unwrap();
    WeierstrassEllipticCurve {
        modulus: super::SECP256K1_P,
        a: U256::ZERO,
        b: U256::from(7),
        gx: hex("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hex("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    }
}

fn fresh_seed() -> [u8; 32] {
    let mut seed = [0; 32];
    if let Ok(text) = std::env::var("MEASURE_SEED") {
        assert_eq!(
            text.len(),
            64,
            "MEASURE_SEED must be 64 hexadecimal characters"
        );
        assert!(text.is_ascii());
        for (index, byte) in seed.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&text[2 * index..2 * index + 2], 16)
                .expect("MEASURE_SEED must be hexadecimal");
        }
    } else {
        File::open("/dev/urandom")
            .expect("OS entropy")
            .read_exact(&mut seed)
            .unwrap();
    }
    seed
}

fn independent_xof(seed: &[u8; 32]) -> Shake256Reader {
    let mut hash = Shake256::default();
    hash.update(b"quantum_ecc-independent-measurement-v1");
    hash.update(seed);
    hash.finalize_xof()
}

#[derive(Clone)]
struct Shot {
    target: (U256, U256),
    offset: (U256, U256),
    expected: (U256, U256),
}

// Same scalar distribution, exclusions, reference arithmetic, and RNG ordering as
// eval_circuit::run_tests; only the root seed is independent of the op stream.
fn sample_points(xof: &mut impl XofReader, attempts: usize) -> Vec<Shot> {
    let curve = curve();
    let mut shots = Vec::with_capacity(attempts);
    for _ in 0..attempts {
        let mut rb = [[0; 32]; 2];
        xof.read(&mut rb[0]);
        xof.read(&mut rb[1]);
        let target = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(rb[0]));
        let offset = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(rb[1]));
        if target.0 == offset.0
            || (target.0.is_zero() && target.1.is_zero())
            || (offset.0.is_zero() && offset.1.is_zero())
        {
            continue;
        }
        let expected = curve.add(target.0, target.1, offset.0, offset.1);
        shots.push(Shot {
            target,
            offset,
            expected,
        });
    }
    shots
}

#[derive(Default)]
struct Failures {
    classical: usize,
    phase: usize,
    ancilla: usize,
    any: usize,
    phase_batches: usize,
    ancilla_batches: usize,
}

fn live_mask(shots: usize) -> u64 {
    assert!((1..=64).contains(&shots));
    u64::MAX >> (64 - shots)
}

fn check_batch<R: XofReader>(
    sim: &Simulator<'_, R>,
    regs: &[Vec<QubitOrBit>],
    shots: &[Shot],
    output_qubits: &[bool],
    failures: &mut Failures,
) {
    let mask = live_mask(shots.len());
    let mut classical = 0u64;
    for (lane, shot) in shots.iter().enumerate() {
        if sim.get_register(&regs[0], lane) != shot.expected.0
            || sim.get_register(&regs[1], lane) != shot.expected.1
        {
            classical |= 1 << lane;
        }
    }
    let phase = sim.phase & mask;
    // The evaluator zeroes all register qubits before scanning. Ignoring them
    // here gives the identical decision without destroying the output snapshot.
    let ancilla = sim
        .qubits
        .iter()
        .zip(output_qubits)
        .filter(|(_, output)| !**output)
        .fold(0, |garbage, (&value, _)| garbage | value)
        & mask;
    failures.classical += classical.count_ones() as usize;
    failures.phase += phase.count_ones() as usize;
    failures.ancilla += ancilla.count_ones() as usize;
    failures.any += (classical | phase | ancilla).count_ones() as usize;
    failures.phase_batches += usize::from(phase != 0);
    failures.ancilla_batches += usize::from(ancilla != 0);
}

fn wilson(failures: usize, total: usize) -> (f64, f64) {
    assert!(total > 0 && failures <= total);
    let n = total as f64;
    let p = failures as f64 / n;
    let z2 = 1.959963984540054_f64.powi(2);
    let center = (p + z2 / (2.0 * n)) / (1.0 + z2 / n);
    let radius = (z2 * (p * (1.0 - p) / n + z2 / (4.0 * n * n))).sqrt() / (1.0 + z2 / n);
    ((center - radius).max(0.0), (center + radius).min(1.0))
}

fn print_rate(name: &str, failures: usize, total: usize) {
    let rate = failures as f64 / total as f64;
    let (lo, hi) = wilson(failures, total);
    println!(
        "FAILURE_RATE {name}={failures}/{total} p={rate:.8} Wilson95=[{lo:.8},{hi:.8}] \
         lambda9024={:.4} lambda95=[{:.4},{:.4}]",
        rate * SCORED_SHOTS as f64,
        lo * SCORED_SHOTS as f64,
        hi * SCORED_SHOTS as f64
    );
}

#[test]
#[ignore = "unscored lab: builds the full circuit; see memory/measurement.md"]
fn census() {
    let (_, census) = build_measured();
    census.print(None);
    census.replay.print(census.emitted[Phase::Replay as usize]);
}

#[test]
#[ignore = "unscored fresh-input experiment; see memory/measurement.md"]
fn fresh_sample() {
    let attempts: usize = std::env::var("MEASURE_SHOTS")
        .map(|s| s.parse().expect("MEASURE_SHOTS must be a positive integer"))
        .unwrap_or(1024);
    assert!(attempts > 0);
    let seed = fresh_seed();
    let seed_hex: String = seed.iter().map(|b| format!("{b:02x}")).collect();
    println!("FRESH_SAMPLE seed={seed_hex} requested={attempts} (independent of circuit)");
    let (ops, census) = build_measured();
    let (num_qubits, num_bits, _, regs) = analyze_ops(ops.iter());
    assert_eq!(regs.len(), 4);
    let mut output_qubits = vec![false; num_qubits as usize];
    for (index, reg) in regs.iter().enumerate() {
        assert_eq!(reg.len(), 256);
        for &wire in reg {
            match wire {
                QubitOrBit::Qubit(q) if index < 2 => output_qubits[q.0 as usize] = true,
                QubitOrBit::Bit(_) if index >= 2 => {}
                _ => panic!("invalid register {index} type"),
            }
        }
    }
    let start = Instant::now();
    let mut xof = independent_xof(&seed);
    let shots = sample_points(&mut xof, attempts);
    assert!(!shots.is_empty());
    println!(
        "POINTS accepted={} seconds={:.3}",
        shots.len(),
        start.elapsed().as_secs_f64()
    );
    let start = Instant::now();
    let mut sim = Simulator::new(num_qubits as usize, num_bits as usize, &mut xof);
    let mut failures = Failures::default();
    let mut executed = [0; PHASES];
    for (batch, chunk) in shots.chunks(64).enumerate() {
        sim.clear_for_shot();
        for (lane, shot) in chunk.iter().enumerate() {
            for (reg, value) in
                regs.iter()
                    .zip([shot.target.0, shot.target.1, shot.offset.0, shot.offset.1])
            {
                sim.set_register(reg, value, lane);
            }
        }
        // Independently check that our phase slicing leaves the trusted
        // simulator's state, counters, and random-stream position unchanged.
        let reference = if batch == 0 {
            let mut rng = sim.xof.clone();
            let mut whole = Simulator::new(num_qubits as usize, num_bits as usize, &mut rng);
            whole.qubits.clone_from(&sim.qubits);
            whole.bits.clone_from(&sim.bits);
            whole.apply_iter(ops.iter());
            let snapshot = (whole.qubits, whole.bits, whole.phase, whole.stats);
            Some((snapshot, rng))
        } else {
            None
        };
        let counts = census.apply(&mut sim, &ops);
        if let Some(((qubits, bits, phase, stats), mut rng)) = reference {
            assert_eq!(sim.qubits, qubits, "sliced vs whole qubits");
            assert_eq!(sim.bits, bits, "sliced vs whole classical bits");
            assert_eq!(sim.phase, phase, "sliced vs whole phase");
            assert_eq!(sim.stats, stats, "sliced vs whole counters");
            let mut sliced_rng = sim.xof.clone();
            let (mut a, mut b) = ([0; 32], [0; 32]);
            XofReader::read(&mut sliced_rng, &mut a);
            XofReader::read(&mut rng, &mut b);
            assert_eq!(a, b, "sliced vs whole RNG position");
            println!("SIMULATOR_PARITY first batch: all state, stats and RNG agree");
        }
        if chunk.len() == 64 {
            for (total, value) in executed.iter_mut().zip(counts) {
                *total += value;
            }
        }
        check_batch(&sim, &regs, chunk, &output_qubits, &mut failures);
        if (batch + 1).is_multiple_of(16) || (batch + 1) * 64 >= shots.len() {
            println!(
                "PROGRESS shots={} failures={}",
                ((batch + 1) * 64).min(shots.len()),
                failures.any
            );
        }
    }
    let seconds = start.elapsed().as_secs_f64();
    for (name, count) in [
        ("classical", failures.classical),
        ("phase", failures.phase),
        ("ancilla", failures.ancilla),
        ("any", failures.any),
    ] {
        print_rate(name, count, shots.len());
    }
    println!(
        "BATCH_FAILURES phase={} ancilla={} simulation_seconds={seconds:.3}",
        failures.phase_batches, failures.ancilla_batches
    );
    // apply_iter counts all 64 lanes even in a partial final batch, just like
    // the evaluator. Exclude that batch from per-live-shot census averages.
    let full_shots = shots.len() / 64 * 64;
    if full_shots > 0 {
        census.print(Some((&executed, full_shots)));
        println!(
            "EXECUTED full_batch_shots={full_shots} mean_toffoli={:.3}",
            executed.iter().sum::<u64>() as f64 / full_shots as f64
        );
    } else {
        census.print(None);
    }
    println!(
        "NOTE: measured failures are observations, not test failures; no scored artifacts written"
    );
}

#[test]
fn wilson_and_live_masks() {
    assert_eq!(live_mask(1), 1);
    assert_eq!(live_mask(63), u64::MAX >> 1);
    assert_eq!(live_mask(64), u64::MAX);
    let (lo, hi) = wilson(0, 1024);
    assert!(lo < 1e-15);
    assert!((hi - 0.003737404).abs() < 1e-8);
    let (lo, hi) = wilson(512, 1024);
    assert!((lo + hi - 1.0).abs() < 1e-12);
    let (lo, hi) = wilson(1024, 1024);
    assert!(lo > 0.99 && hi > 1.0 - 1e-15);
}

#[test]
fn rewrite_labels_follow_deleted_weakened_and_expanded_gates() {
    use super::affine_simplify::{rewrite_in_place, Rewrite};
    let capture = Capture::start();
    record_op("square", 9, 0);
    record_op("pp_div_walk", 10, 1);
    record_op("coord_x_sub", 8, 2);
    record_op("square", 9, 3);
    begin_rewrite(4);
    let mut original = Op::empty();
    original.kind = OperationType::CCX;
    original.q_control2 = QubitId(0);
    original.q_control1 = QubitId(1);
    original.q_target = QubitId(2);
    let mut rewrites = [
        Rewrite::Drop,
        Rewrite::Cx(QubitId(1)),
        Rewrite::Keep,
        Rewrite::ComplementedCx(QubitId(1)),
    ]
    .into_iter();
    let result = rewrite_in_place(vec![original; 4], |_| rewrites.next().unwrap());
    end_rewrite(4);
    let trace = capture.finish();
    assert_eq!(
        trace.tags,
        [Phase::WalkForward, Phase::Coordinates, Phase::Square, Phase::Square]
    );
    assert_eq!(result[0].kind, OperationType::CX);
    assert_eq!(result[2].kind, OperationType::X);
    assert_eq!(result[3].kind, OperationType::CX);
    assert_eq!(trace.peak_live[Phase::Square as usize], 9);
}

#[test]
fn scope_restores_parent_and_capture_is_optional() {
    assert!(!capturing());
    record_op("square", 3, 99);
    let capture = Capture::start();
    {
        let _outer = scope(Phase::Replay);
        record_op("pp_mul_walkback", 7, 0);
        {
            let _inner = scope(Phase::WalkBackward);
            record_op("pp_div_replay", 9, 1);
        }
        record_op("pp_mul_walkback", 8, 2);
    }
    record_op("square", 6, 3);
    assert_eq!(
        capture.finish().tags,
        [
            Phase::Replay,
            Phase::WalkBackward,
            Phase::Replay,
            Phase::Square
        ]
    );
    assert!(!capturing());
}

#[test]
fn failures_mask_unused_lanes_and_union_channels() {
    let mut rng = independent_xof(&[1; 32]);
    let mut sim = Simulator::new(3, 0, &mut rng);
    let regs = vec![
        vec![QubitOrBit::Qubit(QubitId(0))],
        vec![QubitOrBit::Qubit(QubitId(1))],
    ];
    let shot = Shot {
        target: (U256::ZERO, U256::ZERO),
        offset: (U256::ZERO, U256::ZERO),
        expected: (U256::ZERO, U256::ZERO),
    };
    let mut failures = Failures::default();
    sim.qubits[0] = 1;
    sim.qubits[2] = 2 | (1 << 63);
    sim.phase = 3 | (1 << 63);
    check_batch(
        &sim,
        &regs,
        &[shot.clone(), shot],
        &[true, true, false],
        &mut failures,
    );
    assert_eq!(
        (
            failures.classical,
            failures.phase,
            failures.ancilla,
            failures.any
        ),
        (1, 2, 1, 2)
    );
    assert_eq!((failures.phase_batches, failures.ancilla_batches), (1, 1));
}

#[test]
fn census_counts_actual_conditions_and_both_toffoli_kinds() {
    use crate::circuit::BitId;
    let mut push = Op::empty();
    push.kind = OperationType::PushCondition;
    push.c_condition = BitId(0);
    let mut ccx = Op::empty();
    ccx.kind = OperationType::CCX;
    ccx.q_control1 = QubitId(0);
    ccx.q_control2 = QubitId(1);
    ccx.q_target = QubitId(2);
    let mut conditional = ccx;
    conditional.c_condition = BitId(1);
    let mut ccz = ccx;
    ccz.kind = OperationType::CCZ;
    let mut pop = Op::empty();
    pop.kind = OperationType::PopCondition;
    let ops = [push, conditional, ccz, pop, ccx];
    let census = Census::new(
        &ops,
        Trace {
            tags: vec![
                Phase::Replay,
                Phase::Replay,
                Phase::Replay,
                Phase::Replay,
                Phase::Square,
            ],
            ..Trace::default()
        },
    );
    let mut rng = independent_xof(&[2; 32]);
    let mut other_rng = rng.clone();
    let mut sliced = Simulator::new(3, 2, &mut rng);
    let mut whole = Simulator::new(3, 2, &mut other_rng);
    sliced.bits[0] = 0x5555_5555_5555_5555;
    sliced.bits[1] = 0x1111_1111_1111_1111;
    whole.bits.clone_from(&sliced.bits);
    let counts = census.apply(&mut sliced, &ops);
    whole.apply_iter(ops.iter());
    assert_eq!(counts[Phase::Replay as usize], 16 + 32);
    assert_eq!(counts[Phase::Square as usize], 64);
    assert_eq!(census.emitted[Phase::Replay as usize], 2);
    assert_eq!(sliced.stats.toffoli_gates, 112);
    assert_eq!(sliced.stats, whole.stats);
    assert_eq!(sliced.qubits, whole.qubits);
    assert_eq!(sliced.bits, whole.bits);
    assert_eq!(sliced.phase, whole.phase);
}

#[test]
#[should_panic(expected = "phase boundary inside condition")]
fn census_rejects_splitting_a_condition_stack() {
    use crate::circuit::BitId;
    let mut push = Op::empty();
    push.kind = OperationType::PushCondition;
    push.c_condition = BitId(0);
    let mut pop = Op::empty();
    pop.kind = OperationType::PopCondition;
    Census::new(
        &[push, pop],
        Trace {
            tags: vec![Phase::Replay, Phase::Square],
            ..Trace::default()
        },
    );
}
