//! Reconstruct the previously tested v2 primary nonce-6 op stream.
//! The stage-1 patch carries the expected input records and checks each one.
//! The stage-2 patch is indexed against the stage-1 output. Some of its
//! removals are approximate; this is not a proof of point-addition validity.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, RegisterId};

const STAGE1: &[u8] = include_bytes!("v2_stage1.bin");
const STAGE2: &[u8] = include_bytes!("v2_stage2.bin");

fn u64_at(data: &[u8], pos: &mut usize) -> u64 {
    let v = u64::from_le_bytes(data[*pos..*pos + 8].try_into().unwrap());
    *pos += 8;
    v
}

fn read_op(data: &[u8], pos: &mut usize) -> Op {
    let kind = match u64_at(data, pos) {
        0 => K::Neg, 1 => K::Register, 2 => K::AppendToRegister,
        3 => K::BitInvert, 4 => K::BitStore0, 5 => K::BitStore1,
        6 => K::X, 7 => K::Z, 8 => K::CX, 9 => K::CZ, 10 => K::Swap,
        11 => K::R, 12 => K::Hmr, 13 => K::CCX, 14 => K::CCZ,
        15 => K::PushCondition, 16 => K::PopCondition, 17 => K::DebugPrint,
        n => panic!("invalid patch op kind {n}"),
    };
    Op { kind, q_control2: QubitId(u64_at(data,pos)), q_control1: QubitId(u64_at(data,pos)),
         q_target: QubitId(u64_at(data,pos)), c_target: BitId(u64_at(data,pos)),
         c_condition: BitId(u64_at(data,pos)), r_target: RegisterId(u64_at(data,pos)) }
}

fn apply(mut ops: Vec<Op>, data: &[u8], has_original: bool, expected_output: usize) -> Vec<Op> {
    let input_len = ops.len();
    let mut read = 0usize;
    let mut write = 0usize;
    let mut pos = 0usize;
    let count = u64_at(data, &mut pos) as usize;
    for _ in 0..count {
        let start = u64_at(data, &mut pos) as usize;
        let end = u64_at(data, &mut pos) as usize;
        let nnew = u64_at(data, &mut pos) as usize;
        assert!(read <= start && start < end && end <= input_len, "invalid patch interval");
        assert!(write <= read, "patch would overwrite unread operations");
        if write != read { ops.copy_within(read..start, write); }
        write += start - read;
        for &actual in &ops[start..end] {
            if has_original { assert_eq!(actual, read_op(data, &mut pos), "original operation mismatch"); }
        }
        assert!(write + nnew <= end, "patch would overwrite unread operations");
        for _ in 0..nnew {
            ops[write] = read_op(data, &mut pos);
            write += 1;
        }
        read = end;
    }
    assert!(write <= read, "patch would overwrite unread operations");
    if write != read { ops.copy_within(read..input_len, write); }
    write += input_len - read;
    ops.truncate(write);
    assert_eq!(pos, data.len(), "trailing patch data");
    assert_eq!(ops.len(), expected_output, "patch output length mismatch");
    ops
}

pub(super) fn finish(ops: Vec<Op>) -> Vec<Op> {
    assert_eq!(ops.len(), 22_197_172, "unexpected baseline op count");
    let ops = apply(ops, STAGE1, true, 22_192_582);
    let ops = apply(ops, STAGE2, false, 22_189_681);
    std::env::set_var("SL_COND", "mf");
    let ops = super::v2_phase::run(ops);
    std::env::remove_var("SL_COND");
    let ops = super::v2_truth::simplify_products(ops);
    let ops = super::interned_witness::witnesses(ops);
    let ops = super::v2_truth::simplify(ops);
    let mut ops = super::v2_classical_reuse::color(ops, 3203);
    assert_eq!(ops.len(), 22_188_909, "unexpected v2 primary op count");
    for bit in 0..48 {
        let mut x = Op::empty();
        x.kind = K::X;
        x.q_target = QubitId((6u64 >> bit) & 1);
        ops.push(x);
        ops.push(x);
    }
    assert_eq!(ops.len(), 22_189_005);
    ops
}
