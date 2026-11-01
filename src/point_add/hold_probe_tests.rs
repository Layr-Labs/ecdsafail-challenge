use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::Path;

const MAGIC: &[u8; 8] = b"QECCOPSZ";
const OP_BYTES: usize = 56;

fn read_u64(bytes: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(bytes[off..off + 8].try_into().unwrap())
}

fn kind_from_u32(value: u32) -> OperationType {
    use OperationType::*;
    match value {
        0 => Neg,
        1 => Register,
        2 => AppendToRegister,
        3 => BitInvert,
        4 => BitStore0,
        5 => BitStore1,
        6 => X,
        7 => Z,
        8 => CX,
        9 => CZ,
        10 => Swap,
        11 => R,
        12 => Hmr,
        13 => CCX,
        14 => CCZ,
        15 => PushCondition,
        16 => PopCondition,
        17 => DebugPrint,
        _ => panic!("unknown operation kind {value}"),
    }
}

fn load_ops(path: &Path) -> Vec<Op> {
    let mut file = File::open(path).unwrap();
    let mut header = [0u8; 16];
    file.read_exact(&mut header).unwrap();
    assert_eq!(&header[..8], MAGIC);
    let count = u64::from_le_bytes(header[8..].try_into().unwrap()) as usize;
    let mut decoder = zstd::stream::read::Decoder::new(BufReader::new(file)).unwrap();
    decoder.window_log_max(27).unwrap();
    let mut ops = Vec::with_capacity(count);
    let mut rec = [0u8; OP_BYTES];
    for _ in 0..count {
        decoder.read_exact(&mut rec).unwrap();
        let op = Op {
            kind: kind_from_u32(u32::from_le_bytes(rec[0..4].try_into().unwrap())),
            q_control2: QubitId(read_u64(&rec, 8)),
            q_control1: QubitId(read_u64(&rec, 16)),
            q_target: QubitId(read_u64(&rec, 24)),
            c_target: BitId(read_u64(&rec, 32)),
            c_condition: BitId(read_u64(&rec, 40)),
            r_target: RegisterId(read_u64(&rec, 48)),
        };
        op.validate();
        ops.push(op);
    }
    let mut extra = [0u8; 1];
    assert_eq!(decoder.read(&mut extra).unwrap(), 0);
    ops
}

fn write_ops(ops: &[Op], path: &Path) {
    let file = BufWriter::new(File::create(path).unwrap());
    let mut writer = file;
    writer.write_all(MAGIC).unwrap();
    writer.write_all(&(ops.len() as u64).to_le_bytes()).unwrap();
    let mut encoder = zstd::stream::write::Encoder::new(writer, 3).unwrap();
    let mut rec = [0u8; OP_BYTES];
    for op in ops {
        rec.fill(0);
        rec[0..4].copy_from_slice(&(op.kind as u32).to_le_bytes());
        rec[8..16].copy_from_slice(&op.q_control2.0.to_le_bytes());
        rec[16..24].copy_from_slice(&op.q_control1.0.to_le_bytes());
        rec[24..32].copy_from_slice(&op.q_target.0.to_le_bytes());
        rec[32..40].copy_from_slice(&op.c_target.0.to_le_bytes());
        rec[40..48].copy_from_slice(&op.c_condition.0.to_le_bytes());
        rec[48..56].copy_from_slice(&op.r_target.0.to_le_bytes());
        encoder.write_all(&rec).unwrap();
    }
    encoder.finish().unwrap().flush().unwrap();
}

#[test]
fn hold_probe_applies_two_passes() {
    let Ok(input) = std::env::var("HOLD_IN") else { return };
    let output = std::env::var("HOLD_OUT").expect("HOLD_OUT");
    let mut ops = load_ops(Path::new(&input));
    let depth = ops.iter().fold(0isize, |depth, op| match op.kind {
        OperationType::PushCondition => depth + 1,
        OperationType::PopCondition => depth - 1,
        _ => depth,
    });
    eprintln!("HOLD_PROBE condition_depth={depth} ops={}", ops.len());
    if depth != 0 {
        eprintln!("HOLD_PROBE prefix ends inside a condition; census skipped");
        return;
    }
    if std::env::var("PROBE_FRONTIER").map(|v| v == "1").unwrap_or(false) {
        let before = super::counts(&ops);
        ops = super::frontier_rewrite::apply(ops);
        let after = super::counts(&ops);
        eprintln!("HOLD_PROBE frontier before={before:?} after={after:?}");
    }
    if std::env::var("PROBE_LEASE").map(|v| v == "1").unwrap_or(false) {
        let before = super::counts(&ops);
        ops = super::lease_pass::run(ops);
        let after = super::counts(&ops);
        eprintln!("HOLD_PROBE lease before={before:?} after={after:?}");
    }
    for pass in 1..=2 {
        let before = super::counts(&ops);
        ops = super::hold_pass::hold_pass(ops);
        let after = super::counts(&ops);
        eprintln!("HOLD_PROBE pass={pass} before={before:?} after={after:?}");
        if before.1 == after.1 {
            break;
        }
    }
    write_ops(&ops, Path::new(&output));
}

#[test]
fn ops_tail_probe() {
    let Ok(input) = std::env::var("TAIL_IN") else { return };
    let output = std::env::var("TAIL_OUT").expect("TAIL_OUT");
    let pairs: usize = std::env::var("TAIL_PAIRS")
        .expect("TAIL_PAIRS")
        .parse()
        .expect("numeric TAIL_PAIRS");
    let mut ops = load_ops(Path::new(&input));
    let mut x = Op::empty();
    x.kind = OperationType::X;
    x.q_target = QubitId(0);
    ops.extend(std::iter::repeat_n(x, 2 * pairs));
    write_ops(&ops, Path::new(&output));
}
