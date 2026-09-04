//! Coherent lowering of Luo et al.'s 835-qubit fixed-schedule EEA.
//!
//! The paper implementation uses measurement-based unary uncomputation and
//! exposes a resource-only placeholder for the inverse EEA.  This backend
//! instead embeds the fully decomposed X/CX/CCX step stream, emits it forward,
//! and emits the exact reversed stream for cleanup.  The surrounding divider
//! keeps the source live through multiplication and uses HMR only for product
//! transport, matching the executable register-shared lifecycle.

use crate::circuit::OperationType;
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use std::io::Cursor;

const FIELD_WIDTH: usize = 257;
const VALUE_WIDTH: usize = 256;
const WORK_WIDTH: usize = 259;
const LT_WIDTH: usize = 8;
const LQ_WIDTH: usize = 9;
const SHIFT_WIDTH: usize = 9;
const LRP_WIDTH: usize = 8;
const AUX_WIDTH: usize = 1;
const LQ_ZERO_ENCODING: usize = (1 << LQ_WIDTH) - 1;
const LS_ZERO_ENCODING: usize = 258;
const LRP_ZERO_ENCODING: usize = (1 << LRP_WIDTH) - 1;
const CORE_WIDTH: usize = 557;
const DIRTY_REFERENCE_WIDTH: usize = 10;
const LOCAL_WIDTH: usize = CORE_WIDTH + DIRTY_REFERENCE_WIDTH;
const SCHEDULE_STEPS: usize = 1_616;
const STREAM_RECORDS_PER_TRAVERSAL: usize = 316_231_401;
const STREAM_X_PER_TRAVERSAL: usize = 14_145_878;
const STREAM_CX_PER_TRAVERSAL: usize = 13_436_467;
// Includes the two emitted CCX gates for every clean-C3X MBU marker.
const STREAM_CCX_PER_TRAVERSAL: usize = 287_816_099;
const STREAM_HMR_PER_TRAVERSAL: usize = 0;
const STREAM_CZ_PER_TRAVERSAL: usize = 0;
// Complete source-bound census of all 316,231,401 authenticated primitive
// records. Each disjoint four-wire conjugation saves one CCX, and every shard
// is checked independently before either forward or inverse emission.
const CHUNK_CCX_CONJUGATIONS: [usize; 36] = [
    336, 358, 358, 366, 358, 358, 358, 366, 358, 358, 358, 366, 358, 358, 358,
    366, 358, 358, 358, 366, 358, 358, 358, 366, 358, 358, 358, 366, 358, 358,
    358, 366, 358, 358, 358, 332,
];
// A second authenticated census runs on the post-R034 stream. Each window
// commutes one repeated CCX past at most 32 reversible XOR gates, replaces its
// sole noncommuting conjugation by one CX, and saves exactly two CCX gates.
const CHUNK_GAP_CONJUGATIONS: [usize; 36] = [
    306, 737, 1_164, 2_202, 2_905, 2_943, 2_312, 3_132, 3_309, 3_485, 3_664,
    11_189, 17_699, 18_682, 19_245, 19_896, 20_523, 21_784, 22_583, 22_902,
    23_951, 24_298, 24_993, 25_223, 25_180, 24_964, 23_990, 23_834, 23_799,
    23_684, 23_559, 23_791, 23_484, 22_404, 20_915, 18_898,
];
// After both preceding source rewrites, a second exact commuting-gap pass
// exposes CX-blocked CCX conjugations. Each emits one CCX correction and
// saves one Toffoli and one serialized operation without allocating a qubit.
const CHUNK_CX_GAP_CONJUGATIONS: [usize; 36] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2_816, 5_760, 5_760, 6_688, 7_360,
    8_132, 8_628, 8_912, 9_672, 10_168, 10_752, 11_304, 11_476, 11_474,
    11_474, 11_476, 11_476, 11_474, 11_474, 11_476, 11_476, 11_474, 11_474,
    11_476, 10_456,
];
// A fourth exact pass handles two-or-more noncommuting X/CX blockers between
// identical outer CCX gates. Conjugating every blocker independently removes
// both outer Toffolis; an X blocker adds only a CX correction, while at most
// one CX blocker adds one CCX correction. Counts are authenticated per shard.
const CHUNK_MULTI_GAP_CONJUGATIONS: [usize; 36] = [
    156, 444, 772, 1_528, 2_078, 2_120, 1_595, 2_189, 2_356, 2_482, 2_632,
    7_564, 11_618, 12_102, 12_628, 13_096, 13_634, 14_132, 14_440, 14_675,
    15_208, 15_353, 15_717, 15_889, 15_858, 15_719, 14_973, 14_831, 14_804,
    14_694, 14_629, 14_817, 14_576, 13_801, 12_678, 11_432,
];
const CHUNK_MULTI_GAP_BLOCKERS: [usize; 36] = [
    312, 888, 1_544, 3_056, 4_156, 4_240, 3_190, 4_378, 4_712, 4_964, 5_264,
    15_128, 23_236, 24_204, 25_256, 26_192, 27_268, 28_336, 28_970, 29_440,
    30_506, 30_796, 31_524, 31_868, 31_806, 31_528, 30_036, 29_752, 29_698,
    29_478, 29_348, 29_724, 29_242, 27_692, 25_446, 22_946,
];
const CHUNK_MULTI_GAP_SAVINGS: [usize; 36] = [
    312, 888, 1_544, 3_056, 4_156, 4_240, 3_190, 4_378, 4_712, 4_964, 5_264,
    13_720, 20_332, 20_900, 22_144, 23_144, 24_340, 24_144, 24_316, 24_894,
    25_278, 25_368, 25_744, 25_972, 25_912, 25_634, 24_140, 23_856, 23_804,
    23_584, 23_452, 23_828, 23_348, 21_798, 19_550, 17_574,
];
const GAP_RING_WORDS: usize = 256;
const GAP_MAX_INTERVENING: usize = 32;

const fn half_plus_one_le() -> [u8; 33] {
    let mut bytes = [0xff; 33];
    bytes[0] = 0x18;
    bytes[1] = 0xfe;
    bytes[3] = 0x7f;
    bytes[31] = 0x7f;
    bytes[32] = 0;
    bytes
}

const HALF_PLUS_ONE_LE: [u8; 33] = half_plus_one_le();

const STREAM_CHUNKS: [&[u8]; 36] = [
    include_bytes!("paper2607_exactwidth_data/chunk-0001-0045.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0046-0090.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0091-0135.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0136-0180.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0181-0225.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0226-0270.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0271-0315.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0316-0360.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0361-0405.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0406-0450.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0451-0495.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0496-0540.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0541-0585.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0586-0630.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0631-0675.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0676-0720.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0721-0765.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0766-0810.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0811-0855.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0856-0900.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0901-0945.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0946-0990.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-0991-1035.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1036-1080.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1081-1125.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1126-1170.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1171-1215.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1216-1260.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1261-1305.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1306-1350.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1351-1395.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1396-1440.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1441-1485.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1486-1530.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1531-1575.zst"),
    include_bytes!("paper2607_exactwidth_data/chunk-1576-1616.zst"),
];

pub fn enabled() -> bool {
    std::env::var("PAPER2607_COHERENT_EEA").ok().as_deref() == Some("1")
}

fn read_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(bytes[offset..offset + 4].try_into().expect("u32 record"))
}

fn decode_chunk(compressed: &[u8]) -> Vec<u8> {
    let decoded = zstd::stream::decode_all(Cursor::new(compressed))
        .expect("decode paper2607 primitive stream");
    assert!(decoded.len() >= 24, "truncated paper2607 stream header");
    assert_eq!(&decoded[..8], b"P26EEA2\0");
    assert_eq!(read_u32(&decoded, 8), VALUE_WIDTH as u32);
    assert_eq!(read_u32(&decoded, 12), LOCAL_WIDTH as u32);
    assert_eq!((decoded.len() - 24) % 8, 0, "partial paper2607 record");
    decoded
}

fn emit_record(circ: &mut Circuit, local: &[&QReg], word: u64) {
    let kind = (word & 0xf) as u8;
    let arity = ((word >> 4) & 0xf) as usize;
    let q0 = ((word >> 8) & 0x3ff) as usize;
    let q1 = ((word >> 18) & 0x3ff) as usize;
    let q2 = ((word >> 28) & 0x3ff) as usize;
    let q3 = ((word >> 38) & 0x3ff) as usize;
    let q4 = ((word >> 48) & 0x3ff) as usize;
    assert!(q0 < local.len());
    match (kind, arity) {
        (1, 1) => circ.x(local[q0]),
        (2, 2) => {
            assert!(q1 < local.len());
            circ.cx(local[q0], local[q1]);
        }
        (3, 3) => {
            assert!(q1 < local.len() && q2 < local.len());
            circ.ccx(local[q0], local[q1], local[q2]);
        }
        (4, 1) => circ.z(local[q0]),
        (5, 2) => {
            assert!(q1 < local.len());
            circ.cz(local[q0], local[q1]);
        }
        (6, 2) => {
            assert!(q1 < local.len());
            circ.swap(local[q0], local[q1]);
        }
        (7, 5) => {
            assert!(q1 < local.len() && q2 < local.len());
            assert!(q3 < local.len() && q4 < local.len());
            circ.ccx(local[q0], local[q1], local[q4]);
            circ.ccx(local[q2], local[q4], local[q3]);
            circ.clear_and(local[q4], local[q0], local[q1]);
        }
        _ => panic!("invalid paper2607 primitive kind={kind} arity={arity}"),
    }
}

struct Core {
    phase1: QReg,
    phase2: QReg,
    iteration: QReg,
    sign: QReg,
    work1: Vec<QReg>,
    work2: Vec<QReg>,
    l_t: Vec<QReg>,
    l_q: Vec<QReg>,
    l_s: Vec<QReg>,
    l_rp: Vec<QReg>,
    aux: Vec<QReg>,
}

struct Terminal {
    iteration: QReg,
    work2: Vec<QReg>,
    l_s: Vec<QReg>,
}

struct CanonicalTopLoan {
    restored: bool,
    context: &'static str,
}

impl Drop for CanonicalTopLoan {
    fn drop(&mut self) {
        assert!(
            self.restored || std::thread::panicking(),
            "{} canonical top loan dropped without restore",
            self.context
        );
    }
}

/// Lend a canonical field register's known-zero extension lane to the EEA.
/// The replacement lane need not retain physical identity because the 257th
/// lane is internal, canonical zero state rather than ABI-visible data.
fn loan_canonical_top(
    circ: &mut Circuit,
    register: &mut Vec<QReg>,
    context: &'static str,
) -> CanonicalTopLoan {
    assert_eq!(
        register.len(),
        FIELD_WIDTH,
        "{context} canonical register width"
    );
    let live_before = circ.b.active_qubits;
    let top = register.pop().expect("canonical top lane");
    circ.zero_and_free(top);
    assert_eq!(register.len(), FIELD_WIDTH - 1);
    assert_eq!(
        circ.b.active_qubits + 1,
        live_before,
        "{context} canonical top loan must free one qubit"
    );
    circ.lowq_passenger_top_releases += 1;
    CanonicalTopLoan {
        restored: false,
        context,
    }
}

fn restore_canonical_top(circ: &mut Circuit, register: &mut Vec<QReg>, mut loan: CanonicalTopLoan) {
    assert_eq!(
        register.len(),
        FIELD_WIDTH - 1,
        "{} shortened canonical register width",
        loan.context
    );
    let live_before = circ.b.active_qubits;
    register.push(circ.alloc_qreg(&format!("{}.restored", loan.context)));
    assert_eq!(register.len(), FIELD_WIDTH);
    assert_eq!(
        circ.b.active_qubits,
        live_before + 1,
        "{} canonical top restore must allocate one clean qubit",
        loan.context
    );
    assert!(
        circ.lowq_passenger_top_releases > 0,
        "passenger top loan state underflow"
    );
    circ.lowq_passenger_top_releases -= 1;
    loan.restored = true;
}

fn free_clean(circ: &mut Circuit, register: Vec<QReg>) {
    for lane in register {
        circ.zero_and_free(lane);
    }
}

fn toggle_constant(circ: &mut Circuit, register: &[QReg], value: usize) {
    for (index, lane) in register.iter().enumerate() {
        if (value >> index) & 1 != 0 {
            circ.x(lane);
        }
    }
}

fn toggle_initial_work1(circ: &mut Circuit, work1: &[QReg]) {
    use crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;

    assert_eq!(work1.len(), WORK_WIDTH);
    circ.x(&work1[0]);
    for bit in 0..VALUE_WIDTH {
        if (SECP256K1_P_LE[bit / 8] >> (bit % 8)) & 1 != 0 {
            circ.x(&work1[WORK_WIDTH - 1 - bit]);
        }
    }
}

fn toggle_terminal_work1(circ: &mut Circuit, work1: &[QReg]) {
    use crate::point_add::trailmix_port::mod_arith::SECP256K1_P_LE;

    assert_eq!(work1.len(), WORK_WIDTH);
    for bit in 0..VALUE_WIDTH {
        if (SECP256K1_P_LE[bit / 8] >> (bit % 8)) & 1 != 0 {
            circ.x(&work1[bit]);
        }
    }
    circ.x(&work1[WORK_WIDTH - 1]);
}

fn local_wires<'a>(core: &'a Core, passenger: &'a [QReg]) -> Vec<&'a QReg> {
    assert!(
        passenger.len() >= DIRTY_REFERENCE_WIDTH,
        "paper2607 dirty-passenger lender shortage"
    );
    let mut wires = Vec::with_capacity(LOCAL_WIDTH);
    wires.extend([&core.phase1, &core.phase2, &core.iteration, &core.sign]);
    wires.extend(core.work1.iter());
    wires.extend(core.work2.iter());
    wires.extend(core.l_t.iter());
    wires.extend(core.l_q.iter());
    wires.extend(core.l_s.iter());
    wires.extend(core.l_rp.iter());
    wires.extend(core.aux.iter());
    wires.extend(passenger.iter().take(DIRTY_REFERENCE_WIDTH));
    assert_eq!(wires.len() - DIRTY_REFERENCE_WIDTH, CORE_WIDTH);
    assert_eq!(wires.len(), LOCAL_WIDTH);
    wires
}

fn count_stub_enabled(circ: &Circuit) -> bool {
    circ.b.count_only
        && std::env::var_os("POINT_ADD_HASH_OPS_LEN").is_none()
        && std::env::var("PAPER2607_COUNT_STUB").ok().as_deref() == Some("1")
}

fn emit_count_stub(circ: &mut Circuit) {
    circ.b
        .add_counted_kind(OperationType::X, STREAM_X_PER_TRAVERSAL);
    circ.b
        .add_counted_kind(OperationType::CX, STREAM_CX_PER_TRAVERSAL);
    circ.b
        .add_counted_kind(OperationType::CCX, STREAM_CCX_PER_TRAVERSAL);
    circ.b
        .add_counted_kind(OperationType::Hmr, STREAM_HMR_PER_TRAVERSAL);
    circ.b
        .add_counted_kind(OperationType::CZ, STREAM_CZ_PER_TRAVERSAL);
}

fn primitive_word(records: &[u8], index: usize) -> u64 {
    let offset = index * 8;
    u64::from_le_bytes(
        records[offset..offset + 8]
            .try_into()
            .expect("source-bound paper2607 primitive"),
    )
}

/// CCX(a,b;c), CX(c;d), CCX(a,b;c) = CX(c;d), CCX(a,b;d).
///
/// All four wires must be distinct. These gates are unconditional reversible
/// XOR permutations, so the identity preserves every computational basis
/// amplitude and phase; it saves one CCX without allocating any qubit.
fn ccx_conjugation(records: &[u8], index: usize) -> Option<(u64, u64)> {
    let outer = primitive_word(records, index);
    if outer & 0xff != 0x33 {
        return None;
    }
    let middle = primitive_word(records, index + 1);
    if middle & 0xff != 0x22 || primitive_word(records, index + 2) != outer {
        return None;
    }

    let first_control = (outer >> 8) & 0x3ff;
    let second_control = (outer >> 18) & 0x3ff;
    let outer_target = (outer >> 28) & 0x3ff;
    let middle_control = (middle >> 8) & 0x3ff;
    let middle_target = (middle >> 18) & 0x3ff;

    if first_control == second_control
        || first_control == outer_target
        || second_control == outer_target
        || middle_control != outer_target
        || middle_target == first_control
        || middle_target == second_control
        || middle_target == outer_target
    {
        return None;
    }

    let correction = 0x33
        | (first_control << 8)
        | (second_control << 18)
        | (middle_target << 28);
    Some((middle, correction))
}

fn chunk_conjugations(records: &[u8], expected: usize) -> Vec<(usize, u64, u64)> {
    assert_eq!(records.len() % 8, 0, "partial paper2607 primitive record");
    let count = records.len() / 8;
    let mut windows = Vec::with_capacity(if expected == usize::MAX {
        records.len() / 64
    } else {
        expected
    });
    let mut index = 0;
    while index + 2 < count {
        if let Some((middle, correction)) = ccx_conjugation(records, index) {
            windows.push((index, middle, correction));
            index += 3;
        } else {
            index += 1;
        }
    }
    assert_eq!(
        windows.len(),
        expected,
        "source-bound per-shard CCX-conjugation census drift",
    );
    windows
}

fn emit_primitive_slice(circ: &mut Circuit, wires: &[&QReg], records: &[u8], reverse: bool) {
    let words = records.chunks_exact(8);
    assert!(words.remainder().is_empty(), "partial primitive slice");
    if reverse {
        for record in words.rev() {
            emit_record(
                circ,
                wires,
                u64::from_le_bytes(record.try_into().expect("primitive record")),
            );
        }
    } else {
        for record in words {
            emit_record(
                circ,
                wires,
                u64::from_le_bytes(record.try_into().expect("primitive record")),
            );
        }
    }
}

fn materialize_r034_chunk(records: &[u8], expected: usize) -> Vec<u64> {
    let windows = chunk_conjugations(records, expected);
    let mut transformed = Vec::with_capacity(records.len() / 8 - expected);
    let mut previous = 0;
    for &(index, middle, correction) in &windows {
        assert!(previous <= index, "overlapping first-stage source conjugations");
        for record in records[previous * 8..index * 8].chunks_exact(8) {
            transformed.push(u64::from_le_bytes(record.try_into().expect("primitive record")));
        }
        transformed.push(middle);
        transformed.push(correction);
        previous = index + 3;
    }
    for record in records[previous * 8..].chunks_exact(8) {
        transformed.push(u64::from_le_bytes(record.try_into().expect("primitive record")));
    }
    assert_eq!(
        transformed.len(),
        records.len() / 8 - expected,
        "first-stage source conjugation count drift",
    );
    transformed
}

#[derive(Clone, Copy, Default)]
struct GapGate {
    kind: usize,
    controls: [usize; 2],
    target: usize,
    canonical_word: u64,
}

impl GapGate {
    fn decode(word: u64) -> Self {
        let kind = (word & 0xf) as usize;
        let arity = ((word >> 4) & 0xf) as usize;
        assert!((1..=3).contains(&kind) && arity == kind, "non-XOR gap primitive");
        let mut operands = [0usize; 3];
        for port in 0..kind {
            operands[port] = ((word >> (8 + 10 * port)) & 0x3ff) as usize;
            assert!(operands[port] < LOCAL_WIDTH, "gap primitive wire escapes local width");
            for previous in 0..port {
                assert_ne!(operands[previous], operands[port], "gap primitive aliases wires");
            }
        }
        if kind == 3 && operands[0] > operands[1] {
            operands.swap(0, 1);
        }
        let mut canonical_word = (kind | (kind << 4)) as u64;
        for (port, operand) in operands.iter().take(kind).enumerate() {
            canonical_word |= (*operand as u64) << (8 + 10 * port);
        }
        Self {
            kind,
            controls: [operands[0], operands[1]],
            target: operands[kind - 1],
            canonical_word,
        }
    }

    fn controls_wire(self, wire: usize) -> bool {
        self.controls[..self.kind - 1].contains(&wire)
    }

    fn commutes_with(self, other: Self) -> bool {
        self.target == other.target
            || (!self.controls_wire(other.target) && !other.controls_wire(self.target))
    }
}

#[derive(Clone, Copy, Default)]
struct GapSlot {
    gate: GapGate,
    position: usize,
    previous_target: usize,
}

#[derive(Clone, Copy)]
struct GapWindow {
    first: usize,
    blocker: usize,
    last: usize,
    correction: u64,
}

#[derive(Clone)]
struct MultiGapWindow {
    first: usize,
    last: usize,
    corrections: Vec<(usize, u64)>,
    toffoli_saving: usize,
}

fn gap_correction(
    outer: GapGate,
    middle: GapGate,
    expected_blocker: usize,
    expected_correction: usize,
) -> Option<u64> {
    // The authenticated second stage has only X/CX and the third stage only
    // CX/CCX; neither production pass accepts the other's gate histogram.
    if middle.kind != expected_blocker {
        return None;
    }
    let forward = middle.controls_wire(outer.target);
    let backward = outer.controls_wire(middle.target);
    if forward == backward {
        return None;
    }
    let mut controls = [usize::MAX; 3];
    let mut count = 0;
    let mut insert = |wire: usize| {
        if controls[..count].contains(&wire) {
            return;
        }
        controls[count] = wire;
        count += 1;
    };
    let target;
    if forward {
        target = middle.target;
        for &wire in &outer.controls[..outer.kind - 1] {
            insert(wire);
        }
        for &wire in &middle.controls[..middle.kind - 1] {
            if wire != outer.target {
                insert(wire);
            }
        }
    } else {
        target = outer.target;
        for &wire in &middle.controls[..middle.kind - 1] {
            insert(wire);
        }
        for &wire in &outer.controls[..outer.kind - 1] {
            if wire != middle.target {
                insert(wire);
            }
        }
    }
    if count + 1 != expected_correction || controls[..count].contains(&target) {
        return None;
    }
    if count == 2 && controls[0] > controls[1] {
        controls.swap(0, 1);
    }
    let kind = count + 1;
    let mut word = (kind | (kind << 4)) as u64;
    for (index, control) in controls.iter().take(count).enumerate() {
        word |= (*control as u64) << (8 + 10 * index);
    }
    word |= (target as u64) << (8 + 10 * count);
    Some(word)
}

fn gap_conjugations_with_limit(
    records: &[u64],
    expected: usize,
    expected_blocker: usize,
    expected_correction: usize,
    max_intervening: usize,
) -> Vec<GapWindow> {
    let mut ring = [GapSlot::default(); GAP_RING_WORDS];
    let mut heads = [usize::MAX; LOCAL_WIDTH];
    let mut windows = Vec::with_capacity(if expected == usize::MAX {
        records.len() / 64
    } else {
        expected
    });
    let mut last_selected: Option<usize> = None;

    for (position, &word) in records.iter().enumerate() {
        let current = GapGate::decode(word);
        let previous_head = heads[current.target];
        if current.kind == 3 {
            let mut previous = previous_head;
            while previous != usize::MAX
                && previous < position
                && position - previous - 1 <= max_intervening
            {
                let outer = ring[previous % GAP_RING_WORDS];
                assert_eq!(outer.position, previous, "bounded previous-target ring drift");
                let earlier = outer.previous_target;
                if outer.gate.kind == 3
                    && outer.gate.canonical_word == current.canonical_word
                    && last_selected.is_none_or(|last| previous > last)
                {
                    let mut blockers = 0;
                    let mut blocker = usize::MAX;
                    for index in previous + 1..position {
                        let inside = ring[index % GAP_RING_WORDS];
                        assert_eq!(inside.position, index, "bounded commuting ring drift");
                        if !current.commutes_with(inside.gate) {
                            blocker = index;
                            blockers += 1;
                            if blockers > 1 {
                                break;
                            }
                        }
                    }
                    if blockers == 1 {
                        let middle = ring[blocker % GAP_RING_WORDS].gate;
                        if let Some(correction) =
                            gap_correction(current, middle, expected_blocker, expected_correction)
                        {
                            windows.push(GapWindow {
                                first: previous,
                                blocker,
                                last: position,
                                correction,
                            });
                            last_selected = Some(position);
                            break;
                        }
                    }
                }
                previous = earlier;
            }
        }
        ring[position % GAP_RING_WORDS] = GapSlot {
            gate: current,
            position,
            previous_target: previous_head,
        };
        heads[current.target] = position;
    }
    if expected != usize::MAX {
        assert_eq!(
            windows.len(),
            expected,
            "source-bound per-shard commuting-gap conjugation census drift",
        );
    }
    windows
}

fn gap_conjugations(
    records: &[u64],
    expected: usize,
    expected_blocker: usize,
    expected_correction: usize,
) -> Vec<GapWindow> {
    gap_conjugations_with_limit(
        records,
        expected,
        expected_blocker,
        expected_correction,
        GAP_MAX_INTERVENING,
    )
}

fn apply_small_gate(gate: GapGate, state: &mut [bool], wires: &[usize]) {
    let target = wires.iter().position(|wire| *wire == gate.target).expect("gate target wire");
    let enabled = gate.controls[..gate.kind - 1].iter().all(|control| {
        let index = wires.iter().position(|wire| wire == control).expect("gate control wire");
        state[index]
    });
    if enabled {
        state[target] ^= true;
    }
}

fn verify_gap_core(outer: GapGate, middle: GapGate, correction_word: u64) {
    let correction = GapGate::decode(correction_word);
    let mut wires = Vec::new();
    for gate in [outer, middle, correction] {
        for wire in gate.controls[..gate.kind - 1].iter().chain(std::iter::once(&gate.target)) {
            if !wires.contains(wire) {
                wires.push(*wire);
            }
        }
    }
    assert!(wires.len() <= 4, "gap correction escaped four-wire support");
    for assignment in 0..1usize << wires.len() {
        let initial: Vec<bool> = (0..wires.len()).map(|bit| assignment >> bit & 1 == 1).collect();
        let mut original = initial.clone();
        apply_small_gate(outer, &mut original, &wires);
        apply_small_gate(middle, &mut original, &wires);
        apply_small_gate(outer, &mut original, &wires);
        let mut replacement = initial;
        apply_small_gate(middle, &mut replacement, &wires);
        apply_small_gate(correction, &mut replacement, &wires);
        assert_eq!(original, replacement, "gap correction truth-table mismatch");
    }
}

fn multi_gap_conjugations_with_limit(
    records: &[u64],
    max_intervening: usize,
    verify_cores: bool,
) -> Vec<MultiGapWindow> {
    let mut ring = [GapSlot::default(); GAP_RING_WORDS];
    let mut heads = [usize::MAX; LOCAL_WIDTH];
    let mut windows = Vec::new();
    let mut last_selected: Option<usize> = None;
    for (position, &word) in records.iter().enumerate() {
        let current = GapGate::decode(word);
        let previous_head = heads[current.target];
        if current.kind == 3 {
            let mut previous = previous_head;
            while previous != usize::MAX
                && previous < position
                && position - previous - 1 <= max_intervening
            {
                let outer = ring[previous % GAP_RING_WORDS];
                assert_eq!(outer.position, previous, "bounded multi-gap previous-target drift");
                let earlier = outer.previous_target;
                if outer.gate.kind == 3
                    && outer.gate.canonical_word == current.canonical_word
                    && last_selected.is_none_or(|last| previous > last)
                {
                    let mut corrections = Vec::new();
                    let mut cx_blockers = 0usize;
                    let mut supported = true;
                    for index in previous + 1..position {
                        let inside = ring[index % GAP_RING_WORDS];
                        assert_eq!(inside.position, index, "bounded multi-gap ring drift");
                        if current.commutes_with(inside.gate) {
                            continue;
                        }
                        let correction = match inside.gate.kind {
                            1 => gap_correction(current, inside.gate, 1, 2),
                            2 => {
                                cx_blockers += 1;
                                gap_correction(current, inside.gate, 2, 3)
                            }
                            _ => None,
                        };
                        let Some(correction) = correction else {
                            supported = false;
                            break;
                        };
                        if verify_cores {
                            verify_gap_core(current, inside.gate, correction);
                        }
                        corrections.push((index, correction));
                    }
                    if supported && corrections.len() >= 2 && cx_blockers <= 1 {
                        windows.push(MultiGapWindow {
                            first: previous,
                            last: position,
                            corrections,
                            toffoli_saving: 2 - cx_blockers,
                        });
                        last_selected = Some(position);
                        break;
                    }
                }
                previous = earlier;
            }
        }
        ring[position % GAP_RING_WORDS] = GapSlot {
            gate: current,
            position,
            previous_target: previous_head,
        };
        heads[current.target] = position;
    }
    windows
}

fn emit_gap_slice(circ: &mut Circuit, wires: &[&QReg], records: &[u64], reverse: bool) {
    if reverse {
        for &word in records.iter().rev() {
            emit_record(circ, wires, word);
        }
    } else {
        for &word in records {
            emit_record(circ, wires, word);
        }
    }
}

fn materialize_gap_chunk(records: &[u64], windows: &[GapWindow]) -> Vec<u64> {
    let mut transformed = Vec::with_capacity(records.len() - windows.len());
    let mut previous = 0;
    for &window in windows {
        assert!(previous <= window.first, "overlapping materialized gap windows");
        transformed.extend_from_slice(&records[previous..window.first]);
        transformed.extend_from_slice(&records[window.first + 1..=window.blocker]);
        transformed.push(window.correction);
        transformed.extend_from_slice(&records[window.blocker + 1..window.last]);
        previous = window.last + 1;
    }
    transformed.extend_from_slice(&records[previous..]);
    assert_eq!(
        transformed.len(),
        records.len() - windows.len(),
        "materialized commuting-gap operation count drift",
    );
    transformed
}

fn materialize_multi_gap_chunk(records: &[u64], windows: &[MultiGapWindow]) -> Vec<u64> {
    let blockers = windows.iter().map(|window| window.corrections.len()).sum::<usize>();
    let mut output = Vec::with_capacity(records.len() - 2 * windows.len() + blockers);
    let mut previous = 0;
    for window in windows {
        assert!(previous <= window.first, "overlapping materialized multi-gap windows");
        output.extend_from_slice(&records[previous..window.first]);
        let mut corrections = window.corrections.iter().peekable();
        for index in window.first + 1..window.last {
            output.push(records[index]);
            if corrections.peek().is_some_and(|(position, _)| *position == index) {
                output.push(corrections.next().expect("multi-gap correction").1);
            }
        }
        assert!(corrections.next().is_none(), "unemitted multi-gap correction");
        previous = window.last + 1;
    }
    output.extend_from_slice(&records[previous..]);
    assert_eq!(output.len(), records.len() - 2 * windows.len() + blockers);
    output
}

fn word_ccx_conjugation(records: &[u64], index: usize) -> Option<(u64, u64)> {
    if index + 2 >= records.len() {
        return None;
    }
    let outer = records[index];
    let middle = records[index + 1];
    if records[index + 2] != outer || outer & 0xff != 0x33 || middle & 0xff != 0x22 {
        return None;
    }
    let first_control = (outer >> 8) & 0x3ff;
    let second_control = (outer >> 18) & 0x3ff;
    let outer_target = (outer >> 28) & 0x3ff;
    let middle_control = (middle >> 8) & 0x3ff;
    let middle_target = (middle >> 18) & 0x3ff;
    if first_control == second_control
        || first_control == outer_target
        || second_control == outer_target
        || middle_control != outer_target
        || middle_target == first_control
        || middle_target == second_control
        || middle_target == outer_target
    {
        return None;
    }
    let correction = 0x33
        | (first_control << 8)
        | (second_control << 18)
        | (middle_target << 28);
    Some((middle, correction))
}

fn materialize_word_conjugations(records: &[u64]) -> (Vec<u64>, usize) {
    let mut output = Vec::with_capacity(records.len());
    let mut index = 0;
    let mut count = 0;
    while index < records.len() {
        if let Some((middle, correction)) = word_ccx_conjugation(records, index) {
            output.push(middle);
            output.push(correction);
            index += 3;
            count += 1;
        } else {
            output.push(records[index]);
            index += 1;
        }
    }
    assert_eq!(output.len(), records.len() - count);
    (output, count)
}

/// Research-only bounded-memory census for exact identities exposed after the
/// three authenticated production passes. It never changes the emitted circuit.
pub(crate) fn trace_expanded_conjugation_census() {
    let limits: Vec<usize> = std::env::var("Q813_EXPAND_LIMITS")
        .unwrap_or_else(|_| "32,64,128,255".to_string())
        .split(',')
        .map(|part| part.trim().parse::<usize>().expect("Q813_EXPAND_LIMITS value"))
        .collect();
    for limit in limits {
        assert!(limit < GAP_RING_WORDS, "gap limit exceeds ring capacity");
        let mut total_adjacent = 0usize;
        let mut total_x_gap = 0usize;
        let mut total_cx_gap = 0usize;
        let mut total_multi_windows = 0usize;
        let mut total_multi_blockers = 0usize;
        let mut total_multi_saving = 0usize;
        let mut per_chunk_multi = Vec::with_capacity(STREAM_CHUNKS.len());
        let mut per_chunk_blockers = Vec::with_capacity(STREAM_CHUNKS.len());
        let mut per_chunk_saving = Vec::with_capacity(STREAM_CHUNKS.len());
        let mut total_rounds = 0usize;
        for (chunk_index, compressed) in STREAM_CHUNKS.iter().enumerate() {
            let decoded = decode_chunk(compressed);
            let source = &decoded[24..];
            let first = materialize_r034_chunk(source, CHUNK_CCX_CONJUGATIONS[chunk_index]);
            let x_windows = gap_conjugations(
                &first,
                CHUNK_GAP_CONJUGATIONS[chunk_index],
                1,
                2,
            );
            let second = materialize_gap_chunk(&first, &x_windows);
            let cx_windows = gap_conjugations(
                &second,
                CHUNK_CX_GAP_CONJUGATIONS[chunk_index],
                2,
                3,
            );
            let mut current = materialize_gap_chunk(&second, &cx_windows);
            let mut chunk_adjacent = 0usize;
            let mut chunk_x_gap = 0usize;
            let mut chunk_cx_gap = 0usize;
            for round in 1..=16 {
                let (after_adjacent, adjacent) = materialize_word_conjugations(&current);
                let x_more = gap_conjugations_with_limit(&after_adjacent, usize::MAX, 1, 2, limit);
                let after_x = materialize_gap_chunk(&after_adjacent, &x_more);
                let cx_more = gap_conjugations_with_limit(&after_x, usize::MAX, 2, 3, limit);
                let after_cx = materialize_gap_chunk(&after_x, &cx_more);
                chunk_adjacent += adjacent;
                chunk_x_gap += x_more.len();
                chunk_cx_gap += cx_more.len();
                current = after_cx;
                total_rounds = total_rounds.max(round);
                if adjacent == 0 && x_more.is_empty() && cx_more.is_empty() {
                    break;
                }
            }
            total_adjacent += chunk_adjacent;
            total_x_gap += chunk_x_gap;
            total_cx_gap += chunk_cx_gap;
            let multi = multi_gap_conjugations_with_limit(&current, limit, true);
            let multi_blockers = multi.iter().map(|window| window.corrections.len()).sum::<usize>();
            let multi_saving = multi.iter().map(|window| window.toffoli_saving).sum::<usize>();
            total_multi_windows += multi.len();
            total_multi_blockers += multi_blockers;
            total_multi_saving += multi_saving;
            per_chunk_multi.push(multi.len());
            per_chunk_blockers.push(multi_blockers);
            per_chunk_saving.push(multi_saving);
            eprintln!(
                "Q813_EXPAND limit={} chunk={} adjacent={} x_gap={} cx_gap={} multi={} multi_blockers={} multi_saving={} records={}",
                limit,
                chunk_index,
                chunk_adjacent,
                chunk_x_gap,
                chunk_cx_gap,
                multi.len(),
                multi_blockers,
                multi_saving,
                current.len(),
            );
        }
        let toffoli_per_traversal = total_adjacent + 2 * total_x_gap + total_cx_gap;
        eprintln!(
            "Q813_EXPAND_TOTAL limit={} adjacent={} x_gap={} cx_gap={} multi={} multi_blockers={} multi_saving={} toffoli_per_traversal={} whole_circuit={} rounds={}",
            limit,
            total_adjacent,
            total_x_gap,
            total_cx_gap,
            total_multi_windows,
            total_multi_blockers,
            total_multi_saving,
            toffoli_per_traversal + total_multi_saving,
            4 * (toffoli_per_traversal + total_multi_saving),
            total_rounds,
        );
        eprintln!("Q813_EXPAND_MULTI_COUNTS limit={} {:?}", limit, per_chunk_multi);
        eprintln!("Q813_EXPAND_MULTI_BLOCKERS limit={} {:?}", limit, per_chunk_blockers);
        eprintln!("Q813_EXPAND_MULTI_SAVINGS limit={} {:?}", limit, per_chunk_saving);
    }
}

fn emit_conjugation_chunk(
    circ: &mut Circuit,
    wires: &[&QReg],
    records: &[u8],
    chunk_index: usize,
    expected_r034: usize,
    expected_gap: usize,
    expected_cx_gap: usize,
    reverse: bool,
) {
    let first_stage = materialize_r034_chunk(records, expected_r034);
    let first_windows = gap_conjugations(&first_stage, expected_gap, 1, 2);
    let transformed = materialize_gap_chunk(&first_stage, &first_windows);
    drop(first_windows);
    drop(first_stage);
    let windows = gap_conjugations(&transformed, expected_cx_gap, 2, 3);
    let third_stage = materialize_gap_chunk(&transformed, &windows);
    let multi = multi_gap_conjugations_with_limit(&third_stage, GAP_MAX_INTERVENING, false);
    assert_eq!(multi.len(), CHUNK_MULTI_GAP_CONJUGATIONS[chunk_index]);
    assert_eq!(
        multi.iter().map(|window| window.corrections.len()).sum::<usize>(),
        CHUNK_MULTI_GAP_BLOCKERS[chunk_index],
    );
    assert_eq!(
        multi.iter().map(|window| window.toffoli_saving).sum::<usize>(),
        CHUNK_MULTI_GAP_SAVINGS[chunk_index],
    );
    let fourth_stage = materialize_multi_gap_chunk(&third_stage, &multi);
    emit_gap_slice(circ, wires, &fourth_stage, reverse);
}

fn emit_forward(circ: &mut Circuit, core: &Core, passenger: &[QReg]) {
    if count_stub_enabled(circ) {
        emit_count_stub(circ);
        return;
    }
    let wires = local_wires(core, passenger);
    let mut expected_start = 1_u32;
    for (chunk_index, compressed) in STREAM_CHUNKS.iter().enumerate() {
        let decoded = decode_chunk(compressed);
        let start = read_u32(&decoded, 16);
        let end = read_u32(&decoded, 20);
        assert_eq!(start, expected_start, "paper2607 chunk gap");
        assert!(end >= start && end <= SCHEDULE_STEPS as u32);
        emit_conjugation_chunk(
            circ,
            &wires,
            &decoded[24..],
            chunk_index,
            CHUNK_CCX_CONJUGATIONS[chunk_index],
            CHUNK_GAP_CONJUGATIONS[chunk_index],
            CHUNK_CX_GAP_CONJUGATIONS[chunk_index],
            false,
        );
        expected_start = end + 1;
    }
    assert_eq!(expected_start, SCHEDULE_STEPS as u32 + 1);
}

fn emit_reverse(circ: &mut Circuit, core: &Core, passenger: &[QReg]) {
    if count_stub_enabled(circ) {
        emit_count_stub(circ);
        return;
    }
    let wires = local_wires(core, passenger);
    let mut expected_end = SCHEDULE_STEPS as u32;
    for (chunk_index, compressed) in STREAM_CHUNKS.iter().enumerate().rev() {
        let decoded = decode_chunk(compressed);
        let start = read_u32(&decoded, 16);
        let end = read_u32(&decoded, 20);
        assert_eq!(end, expected_end, "paper2607 reverse chunk gap");
        assert!(start >= 1 && start <= end);
        emit_conjugation_chunk(
            circ,
            &wires,
            &decoded[24..],
            chunk_index,
            CHUNK_CCX_CONJUGATIONS[chunk_index],
            CHUNK_GAP_CONJUGATIONS[chunk_index],
            CHUNK_CX_GAP_CONJUGATIONS[chunk_index],
            true,
        );
        expected_end = start - 1;
    }
    assert_eq!(expected_end, 0);
}

fn rotation_swaps(width: usize, shift: usize) -> Vec<(usize, usize)> {
    let shift = shift % width;
    if shift == 0 {
        return Vec::new();
    }
    let mut seen = vec![false; width];
    let mut swaps = Vec::with_capacity(width - 1);
    for start in 0..width {
        if seen[start] {
            continue;
        }
        let mut cycle = Vec::new();
        let mut lane = start;
        while !seen[lane] {
            seen[lane] = true;
            cycle.push(lane);
            lane = (lane + shift) % width;
        }
        for &other in cycle.iter().skip(1) {
            swaps.push((cycle[0], other));
        }
    }
    swaps
}

fn canonicalize_terminal_work2(circ: &mut Circuit, terminal: &Terminal) {
    // l_s stores (shift - 1) mod 259.  Apply the missing unit rotation
    // directly, then use the encoded bits for the remaining rotation.
    for (left, right) in rotation_swaps(WORK_WIDTH, 1) {
        circ.swap(&terminal.work2[left], &terminal.work2[right]);
    }
    for (bit, control) in terminal.l_s.iter().enumerate() {
        for (left, right) in rotation_swaps(WORK_WIDTH, 1usize << bit) {
            circ.cswap(control, &terminal.work2[left], &terminal.work2[right]);
        }
    }
}

fn restore_terminal_work2_rotation(circ: &mut Circuit, terminal: &Terminal) {
    for (bit, control) in terminal.l_s.iter().enumerate().rev() {
        let swaps = rotation_swaps(WORK_WIDTH, 1usize << bit);
        for &(left, right) in swaps.iter().rev() {
            circ.cswap(control, &terminal.work2[left], &terminal.work2[right]);
        }
    }
    let unit = rotation_swaps(WORK_WIDTH, 1);
    for &(left, right) in unit.iter().rev() {
        circ.swap(&terminal.work2[left], &terminal.work2[right]);
    }
}

fn initialize(circ: &mut Circuit, mut dx: Vec<QReg>) -> Core {
    use super::register_shared_eea_microkernels::decrement_mod_2n;
    use super::shrunken_pz_state_machine::{bit_length_lean, controlled_field_neg};
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;

    assert_eq!(dx.len(), FIELD_WIDTH);
    let iteration = circ.alloc_qreg("paper2607.iteration");
    compare_geq_const(circ, &dx, &HALF_PLUS_ONE_LE, &iteration);
    controlled_field_neg(circ, &iteration, &dx);

    let mut l_rp = circ.alloc_qreg_bits("paper2607.l-rp", LRP_WIDTH);
    l_rp.push(circ.alloc_qreg("paper2607.l-rp.high-temporary"));
    let source: Vec<&QReg> = dx.iter().take(VALUE_WIDTH).collect();
    bit_length_lean(circ, &source, &l_rp, false);
    let length_scratch = circ.alloc_qreg_bits("paper2607.length-decrement", LRP_WIDTH);
    decrement_mod_2n(circ, &l_rp, &length_scratch);
    free_clean(circ, length_scratch);
    let l_rp_high = l_rp.pop().expect("paper2607 l_rp temporary high bit");
    circ.zero_and_free(l_rp_high);
    assert_eq!(l_rp.len(), LRP_WIDTH);

    dx.push(circ.alloc_qreg("paper2607.work2-pad0"));
    dx.push(circ.alloc_qreg("paper2607.work2-pad1"));
    dx.reverse();
    let work2 = dx;

    let work1 = circ.alloc_qreg_bits("paper2607.work1", WORK_WIDTH);
    toggle_initial_work1(circ, &work1);
    let phase1 = circ.alloc_qreg("paper2607.phase1");
    let phase2 = circ.alloc_qreg("paper2607.phase2");
    let sign = circ.alloc_qreg("paper2607.sign");
    let l_t = circ.alloc_qreg_bits("paper2607.l-t", LT_WIDTH);
    let l_q = circ.alloc_qreg_bits("paper2607.l-q", LQ_WIDTH);
    let l_s = circ.alloc_qreg_bits("paper2607.l-s", SHIFT_WIDTH);
    toggle_constant(circ, &l_q, LQ_ZERO_ENCODING);
    toggle_constant(circ, &l_s, LS_ZERO_ENCODING);
    let aux = circ.alloc_qreg_bits("paper2607.aux", AUX_WIDTH);

    Core {
        phase1,
        phase2,
        iteration,
        sign,
        work1,
        work2,
        l_t,
        l_q,
        l_s,
        l_rp,
        aux,
    }
}

fn release_terminal(circ: &mut Circuit, core: Core) -> Terminal {
    toggle_terminal_work1(circ, &core.work1);
    free_clean(circ, core.work1);
    toggle_constant(circ, &core.l_t, VALUE_WIDTH - 1);
    free_clean(circ, core.l_t);
    toggle_constant(circ, &core.l_q, LQ_ZERO_ENCODING);
    free_clean(circ, core.l_q);
    toggle_constant(circ, &core.l_rp, LRP_ZERO_ENCODING);
    free_clean(circ, core.l_rp);
    circ.zero_and_free(core.phase1);
    circ.zero_and_free(core.phase2);
    circ.zero_and_free(core.sign);
    free_clean(circ, core.aux);
    Terminal {
        iteration: core.iteration,
        work2: core.work2,
        l_s: core.l_s,
    }
}

fn rebuild_terminal(circ: &mut Circuit, terminal: Terminal) -> Core {
    let work1 = circ.alloc_qreg_bits("paper2607.work1.rebuilt", WORK_WIDTH);
    toggle_terminal_work1(circ, &work1);
    let l_t = circ.alloc_qreg_bits("paper2607.l-t.rebuilt", LT_WIDTH);
    toggle_constant(circ, &l_t, VALUE_WIDTH - 1);
    let l_q = circ.alloc_qreg_bits("paper2607.l-q.rebuilt", LQ_WIDTH);
    toggle_constant(circ, &l_q, LQ_ZERO_ENCODING);
    let l_rp = circ.alloc_qreg_bits("paper2607.l-rp.rebuilt", LRP_WIDTH);
    toggle_constant(circ, &l_rp, LRP_ZERO_ENCODING);
    Core {
        phase1: circ.alloc_qreg("paper2607.phase1.rebuilt"),
        phase2: circ.alloc_qreg("paper2607.phase2.rebuilt"),
        iteration: terminal.iteration,
        sign: circ.alloc_qreg("paper2607.sign.rebuilt"),
        work1,
        work2: terminal.work2,
        l_t,
        l_q,
        l_s: terminal.l_s,
        l_rp,
        aux: circ.alloc_qreg_bits("paper2607.aux.rebuilt", AUX_WIDTH),
    }
}

fn finish(circ: &mut Circuit, mut core: Core) -> Vec<QReg> {
    use super::register_shared_eea_microkernels::increment_mod_2n;
    use super::shrunken_pz_state_machine::{bit_length_lean, controlled_field_neg};
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;

    circ.zero_and_free(core.phase1);
    circ.zero_and_free(core.phase2);
    circ.zero_and_free(core.sign);
    toggle_initial_work1(circ, &core.work1);
    free_clean(circ, core.work1);
    free_clean(circ, core.l_t);
    toggle_constant(circ, &core.l_q, LQ_ZERO_ENCODING);
    free_clean(circ, core.l_q);
    toggle_constant(circ, &core.l_s, LS_ZERO_ENCODING);
    free_clean(circ, core.l_s);
    free_clean(circ, core.aux);

    core.work2.reverse();
    let pad1 = core.work2.pop().expect("paper2607 Work2 pad1");
    let pad0 = core.work2.pop().expect("paper2607 Work2 pad0");
    circ.zero_and_free(pad1);
    circ.zero_and_free(pad0);
    assert_eq!(core.work2.len(), FIELD_WIDTH);

    core.l_rp
        .push(circ.alloc_qreg("paper2607.l-rp.high-temporary.finish"));
    let length_scratch = circ.alloc_qreg_bits("paper2607.length-increment", LRP_WIDTH);
    increment_mod_2n(circ, &core.l_rp, &length_scratch);
    free_clean(circ, length_scratch);
    let source: Vec<&QReg> = core.work2.iter().take(VALUE_WIDTH).collect();
    bit_length_lean(circ, &source, &core.l_rp, true);
    free_clean(circ, core.l_rp);

    controlled_field_neg(circ, &core.iteration, &core.work2);
    compare_geq_const(circ, &core.work2, &HALF_PLUS_ONE_LE, &core.iteration);
    circ.zero_and_free(core.iteration);
    core.work2
}

fn toggle_inverse_sign(circ: &mut Circuit, terminal: &Terminal) {
    use super::shrunken_pz_state_machine::controlled_field_neg;

    // Canonical Work2 is t' || 000, so lane 256 is already the clean field
    // top required by the 257-bit modular arithmetic interface.
    assert_eq!(terminal.work2.len(), WORK_WIDTH);
    circ.x(&terminal.iteration);
    controlled_field_neg(circ, &terminal.iteration, &terminal.work2[..FIELD_WIDTH]);
    circ.x(&terminal.iteration);
}

pub fn divide_forward(
    circ: &mut Circuit,
    dx: Vec<QReg>,
    mut dy: Vec<QReg>,
) -> (Vec<QReg>, Vec<QReg>, Vec<QReg>) {
    use super::shrunken_pz_state_machine::{
        release_q955_canonical_lambda_top, restore_q955_canonical_lambda_top,
    };
    use crate::point_add::trailmix_port::arith::rfold_mbu::mod_mul_canonical_mbu;

    assert_eq!(dx.len(), FIELD_WIDTH);
    assert_eq!(dy.len(), FIELD_WIDTH);
    let released_dy_top = loan_canonical_top(circ, &mut dy, "paper2607 forward dy");
    let core = initialize(circ, dx);
    emit_forward(circ, &core, &dy);
    let mut terminal = release_terminal(circ, core);
    canonicalize_terminal_work2(circ, &terminal);
    toggle_inverse_sign(circ, &terminal);

    restore_canonical_top(circ, &mut dy, released_dy_top);
    let mut lambda = circ.alloc_qreg_bits("paper2607.lambda", FIELD_WIDTH);
    mod_mul_canonical_mbu(circ, &lambda, &terminal.work2[..FIELD_WIDTH], &dy);
    toggle_inverse_sign(circ, &terminal);
    restore_terminal_work2_rotation(circ, &terminal);
    release_q955_canonical_lambda_top(circ, &mut lambda);

    let dy_ghosts: Vec<_> = dy.iter().map(|lane| circ.hmr_ghost(lane)).collect();
    free_clean(circ, dy);
    let core = rebuild_terminal(circ, terminal);
    emit_reverse(circ, &core, &lambda);
    let dx = finish(circ, core);

    restore_q955_canonical_lambda_top(circ, &mut lambda);
    let dy = circ.alloc_qreg_bits("paper2607.dy-restored", FIELD_WIDTH);
    mod_mul_canonical_mbu(circ, &dy, &lambda, &dx);
    for (ghost, lane) in dy_ghosts.into_iter().zip(&dy) {
        circ.resolve_ghost(ghost, lane);
    }
    (dx, dy, lambda)
}

pub fn divide_cancel(
    circ: &mut Circuit,
    dx: Vec<QReg>,
    mut dy: Vec<QReg>,
    lambda: Vec<QReg>,
) -> (Vec<QReg>, Vec<QReg>) {
    use crate::point_add::trailmix_port::arith::rfold_mbu::{
        mod_mul_canonical_mbu, mod_mul_canonical_mbu_undo,
    };

    assert_eq!(dx.len(), FIELD_WIDTH);
    assert_eq!(dy.len(), FIELD_WIDTH);
    assert_eq!(lambda.len(), FIELD_WIDTH);
    let lambda_ghosts: Vec<_> = lambda.iter().map(|lane| circ.hmr_ghost(lane)).collect();
    free_clean(circ, lambda);

    let released_forward_dy_top = loan_canonical_top(circ, &mut dy, "paper2607 cancel-forward dy");
    let core = initialize(circ, dx);
    emit_forward(circ, &core, &dy);
    let mut terminal = release_terminal(circ, core);
    canonicalize_terminal_work2(circ, &terminal);
    toggle_inverse_sign(circ, &terminal);

    restore_canonical_top(circ, &mut dy, released_forward_dy_top);
    let quotient = circ.alloc_qreg_bits("paper2607.quotient-check", FIELD_WIDTH);
    mod_mul_canonical_mbu(circ, &quotient, &terminal.work2[..FIELD_WIDTH], &dy);
    for (ghost, lane) in lambda_ghosts.into_iter().zip(&quotient) {
        circ.resolve_ghost(ghost, lane);
    }
    mod_mul_canonical_mbu_undo(circ, &quotient, &terminal.work2[..FIELD_WIDTH], &dy);
    free_clean(circ, quotient);

    toggle_inverse_sign(circ, &terminal);
    restore_terminal_work2_rotation(circ, &terminal);
    let released_reverse_dy_top = loan_canonical_top(circ, &mut dy, "paper2607 cancel-reverse dy");
    let core = rebuild_terminal(circ, terminal);
    emit_reverse(circ, &core, &dy);
    let dx = finish(circ, core);
    restore_canonical_top(circ, &mut dy, released_reverse_dy_top);
    (dx, dy)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_shard_conjugations_are_source_bound_and_exact() {
        let decoded = decode_chunk(STREAM_CHUNKS[0]);
        let records = &decoded[24..];
        let windows = chunk_conjugations(records, CHUNK_CCX_CONJUGATIONS[0]);
        assert_eq!(windows.len(), CHUNK_CCX_CONJUGATIONS[0]);
        assert_eq!(CHUNK_CCX_CONJUGATIONS.iter().sum::<usize>(), 12_904);
        assert_eq!(windows.first().map(|window| window.0), Some(456_940));
        assert_eq!(windows.last().map(|window| window.0), Some(7_665_282));

        for &(index, middle, correction) in &windows {
            let outer = primitive_word(records, index);
            assert_eq!(primitive_word(records, index + 1), middle);
            assert_eq!(primitive_word(records, index + 2), outer);

            let a = ((outer >> 8) & 0x3ff) as usize;
            let b = ((outer >> 18) & 0x3ff) as usize;
            let c = ((outer >> 28) & 0x3ff) as usize;
            let d = ((middle >> 18) & 0x3ff) as usize;
            let support = [a, b, c, d];

            let apply = |word: u64, mut state: u8| -> u8 {
                let arity = ((word >> 4) & 0xf) as usize;
                let mut ports = [0usize; 3];
                for (port, slot) in ports.iter_mut().take(arity).enumerate() {
                    let wire = ((word >> (8 + 10 * port)) & 0x3ff) as usize;
                    *slot = support
                        .iter()
                        .position(|&candidate| candidate == wire)
                        .expect("conjugation wire outside its four-bit support");
                }
                if ports[..arity - 1]
                    .iter()
                    .all(|&control| (state >> control) & 1 == 1)
                {
                    state ^= 1 << ports[arity - 1];
                }
                state
            };

            for state in 0..16 {
                let original = [outer, middle, outer]
                    .into_iter()
                    .fold(state, |current, word| apply(word, current));
                let forward = [middle, correction]
                    .into_iter()
                    .fold(state, |current, word| apply(word, current));
                let reverse = [correction, middle]
                    .into_iter()
                    .fold(state, |current, word| apply(word, current));
                assert_eq!(original, forward, "forward conjugation state mismatch");
                assert_eq!(original, reverse, "reverse conjugation state mismatch");
            }
        }
    }

    fn apply_swaps<T>(values: &mut [T], swaps: &[(usize, usize)]) {
        for &(left, right) in swaps {
            values.swap(left, right);
        }
    }

    #[test]
    fn rotation_schedule_moves_each_lane_right() {
        for shift in [1, 2, 3, 17, 128, 256] {
            let mut lanes: Vec<_> = (0..WORK_WIDTH).collect();
            apply_swaps(&mut lanes, &rotation_swaps(WORK_WIDTH, shift));
            for source in 0..WORK_WIDTH {
                assert_eq!(lanes[(source + shift) % WORK_WIDTH], source);
            }
        }
    }

    #[test]
    fn rotation_schedule_reverses_exactly() {
        for shift in [1, 2, 3, 17, 128, 256] {
            let swaps = rotation_swaps(WORK_WIDTH, shift);
            let mut lanes: Vec<_> = (0..WORK_WIDTH).collect();
            apply_swaps(&mut lanes, &swaps);
            for &(left, right) in swaps.iter().rev() {
                lanes.swap(left, right);
            }
            assert_eq!(lanes, (0..WORK_WIDTH).collect::<Vec<_>>());
        }
    }

    #[test]
    fn embedded_stream_is_complete_and_primitive() {
        let mut expected_start = 1_u32;
        let mut records = 0_usize;
        for compressed in STREAM_CHUNKS {
            let decoded = decode_chunk(compressed);
            let start = read_u32(&decoded, 16);
            let end = read_u32(&decoded, 20);
            assert_eq!(start, expected_start);
            for record in decoded[24..].chunks_exact(8).step_by(10_003) {
                let word = u64::from_le_bytes(record.try_into().expect("primitive record"));
                let kind = word & 0xf;
                let arity = (word >> 4) & 0xf;
                assert!(matches!((kind, arity), (1, 1) | (2, 2) | (3, 3) | (7, 5)));
                assert!(((word >> 8) & 0x3ff) < LOCAL_WIDTH as u64);
            }
            records += (decoded.len() - 24) / 8;
            expected_start = end + 1;
        }
        assert_eq!(expected_start, SCHEDULE_STEPS as u32 + 1);
        assert_eq!(records, STREAM_RECORDS_PER_TRAVERSAL);
    }
}
