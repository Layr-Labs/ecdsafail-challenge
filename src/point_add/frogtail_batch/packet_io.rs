//! Test-only loader for our own emitted, bounded whole-circuit packet.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, RegisterId};
use std::io::{BufReader, Read};

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
