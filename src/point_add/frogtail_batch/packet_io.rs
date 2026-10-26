//! Test-only loader for our own emitted, bounded whole-circuit packet.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, RegisterId};
use std::io::{BufReader, BufWriter, Read, Write};

pub fn load(path: &str) -> Vec<Op> {
    let mut file = std::fs::File::open(path).expect("own packet exists");
    let mut header = [0u8; 16];
    file.read_exact(&mut header).unwrap();
    assert_eq!(&header[..8], b"QECCOPSZ");
    let count = u64::from_le_bytes(header[8..].try_into().unwrap());
    assert!(count <= 100_000_000, "bounded local diagnostic packet");
    let mut dec = zstd::stream::read::Decoder::new(BufReader::new(file)).unwrap();
    dec.window_log_max(27).unwrap();
    let word = |record: &[u8], offset| u64::from_le_bytes(record[offset..offset+8].try_into().unwrap());
    let mut ops = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let mut rec = [0u8; 56];
        dec.read_exact(&mut rec).unwrap();
        let kind = match u32::from_le_bytes(rec[..4].try_into().unwrap()) {
            0=>K::Neg, 1=>K::Register, 2=>K::AppendToRegister,
            3=>K::BitInvert, 4=>K::BitStore0, 5=>K::BitStore1,
            6=>K::X, 7=>K::Z, 8=>K::CX, 9=>K::CZ, 10=>K::Swap,
            11=>K::R, 12=>K::Hmr, 13=>K::CCX, 14=>K::CCZ,
            15=>K::PushCondition, 16=>K::PopCondition, 17=>K::DebugPrint,
            _=>panic!("invalid own packet opcode"),
        };
        let op = Op { kind, q_control2:QubitId(word(&rec,8)),
            q_control1:QubitId(word(&rec,16)), q_target:QubitId(word(&rec,24)),
            c_target:BitId(word(&rec,32)), c_condition:BitId(word(&rec,40)),
            r_target:RegisterId(word(&rec,48)) };
        op.validate();
        ops.push(op);
    }
    let mut extra = [0u8;1];
    assert_eq!(dec.read(&mut extra).unwrap(),0);
    ops
}

/// Test-only writer for bounded local nonce/corpus diagnostics. The framing is
/// byte-identical to build_circuit; it never changes arithmetic operations.
pub fn write(ops: &[Op], path: &str) {
    let file = std::fs::File::create(path).unwrap();
    let mut out = BufWriter::new(file);
    out.write_all(b"QECCOPSZ").unwrap();
    out.write_all(&(ops.len() as u64).to_le_bytes()).unwrap();
    let mut enc = zstd::stream::write::Encoder::new(out, 3).unwrap();
    for op in ops {
        let mut rec = [0u8; 56];
        rec[0..4].copy_from_slice(&(op.kind as u32).to_le_bytes());
        rec[8..16].copy_from_slice(&op.q_control2.0.to_le_bytes());
        rec[16..24].copy_from_slice(&op.q_control1.0.to_le_bytes());
        rec[24..32].copy_from_slice(&op.q_target.0.to_le_bytes());
        rec[32..40].copy_from_slice(&op.c_target.0.to_le_bytes());
        rec[40..48].copy_from_slice(&op.c_condition.0.to_le_bytes());
        rec[48..56].copy_from_slice(&op.r_target.0.to_le_bytes());
        enc.write_all(&rec).unwrap();
    }
    let mut out = enc.finish().unwrap();
    out.flush().unwrap();
}
