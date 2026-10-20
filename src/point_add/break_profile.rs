use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};

pub fn kind(v: u32) -> OperationType {
    use OperationType::*;
    match v {
        0 => Neg, 1 => Register, 2 => AppendToRegister, 3 => BitInvert, 4 => BitStore0, 5 => BitStore1,
        6 => X, 7 => Z, 8 => CX, 9 => CZ, 10 => Swap, 11 => R, 12 => Hmr, 13 => CCX, 14 => CCZ,
        15 => PushCondition, 16 => PopCondition, 17 => DebugPrint, _ => panic!("bad kind {v}"),
    }
}

pub fn load_ops(path: &str) -> Vec<Op> {
    let mut file = File::open(path).expect("open");
    let mut header = [0u8; 16];
    file.read_exact(&mut header).unwrap();
    assert_eq!(&header[..8], b"QECCOPSZ");
    let n = u64::from_le_bytes(header[8..].try_into().unwrap()) as usize;
    let mut dec = zstd::stream::read::Decoder::new(BufReader::new(file)).unwrap();
    dec.window_log_max(27).unwrap();
    let mut ops = Vec::with_capacity(n);
    let mut rec = [0u8; 56];
    let r = |b: &[u8], o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
    for _ in 0..n {
        dec.read_exact(&mut rec).unwrap();
        let op = Op {
            kind: kind(u32::from_le_bytes(rec[0..4].try_into().unwrap())),
            q_control2: QubitId(r(&rec, 8)),
            q_control1: QubitId(r(&rec, 16)),
            q_target: QubitId(r(&rec, 24)),
            c_target: BitId(r(&rec, 32)),
            c_condition: BitId(r(&rec, 40)),
            r_target: RegisterId(r(&rec, 48)),
        };
        op.validate();
        ops.push(op);
    }
    ops
}

#[allow(dead_code)]
pub fn save_ops(path: &str, ops: &[Op]) {
    let file = File::create(path).unwrap();
    let mut w = BufWriter::new(file);
    w.write_all(b"QECCOPSZ").unwrap();
    w.write_all(&(ops.len() as u64).to_le_bytes()).unwrap();
    let mut enc = zstd::stream::write::Encoder::new(w, 3).unwrap();
    enc.window_log(27).unwrap();
    for o in ops {
        let mut rec = [0u8; 56];
        rec[0..4].copy_from_slice(&(o.kind as u32).to_le_bytes());
        for (i, v) in [o.q_control2.0, o.q_control1.0, o.q_target.0, o.c_target.0, o.c_condition.0, o.r_target.0].iter().enumerate() {
            rec[8 + 8 * i..16 + 8 * i].copy_from_slice(&v.to_le_bytes());
        }
        enc.write_all(&rec).unwrap();
    }
    enc.finish().unwrap().flush().unwrap();
}
