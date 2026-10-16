//! y42-railtop: one pass in place of the tree's four stream-bound passes (sqdepth2, phase_cubic, rowcut, reader).
//!
//! Those passes replace single ops of their input by literal rows at absolute op indices and assert the length and a
//! hash of the whole input, so they stop the build on any change of the stream. With a rail switch of leapfrog.rs on
//! (`Y42_RAIL_MUL`, `Y42_RAIL_DIV`) the stream differs from the base's only inside the fused one-fold ticks; every
//! edit site lies outside them, in a stretch that is the base's op for op (same wires, same bits), only at another
//! index. `y42_bound.bin` holds the edits of the four passes composed (for each edited op of the base's unbound
//! stream, the rows that stand in its place in the base's bound stream), each carried to its index in this tree's
//! stream. The table is made outside the tree (experiments/y42-board/b6/bind.py in the Pensieve repo) from three gate
//! lists: the base's unbound and bound lists and this tree's unbound list.
//!
//! Binding check: the input's length and a position-weighted fingerprint of every op, both in the table's header. A
//! wrong input stops the build. `Y42_BOUND` = false (the default with every rail switch off): the input unchanged.
//!
//! Table: "Y42BOUND", u64 input length, u64 fingerprint, u32 edits, then per edit (u32 op index, u32 first row,
//! u32 rows), then the rows as 6 x u16 (kind, q_control2, q_control1, q_target, c_target, c_condition; 0xFFFF = none).
use crate::circuit::{BitId, Op, OperationType as K, QubitId};
const TABLE: &[u8] = include_bytes!("y42_bound.bin");
fn u32_at(p: usize) -> usize {
    u32::from_le_bytes(TABLE[p..p + 4].try_into().unwrap()) as usize
}
fn u64_at(p: usize) -> u64 {
    u64::from_le_bytes(TABLE[p..p + 8].try_into().unwrap())
}
fn row_at(p: usize) -> Op {
    let mut r = [0u64; 6];
    for (j, x) in r.iter_mut().enumerate() {
        let v = u16::from_le_bytes(TABLE[p + 2 * j..p + 2 * j + 2].try_into().unwrap());
        *x = if v == u16::MAX { u64::MAX } else { v as u64 };
    }
    let mut o = Op::empty();
    o.kind = match r[0] {
        0 => K::Neg,
        3 => K::BitInvert,
        4 => K::BitStore0,
        5 => K::BitStore1,
        6 => K::X,
        7 => K::Z,
        8 => K::CX,
        9 => K::CZ,
        11 => K::R,
        12 => K::Hmr,
        13 => K::CCX,
        14 => K::CCZ,
        15 => K::PushCondition,
        16 => K::PopCondition,
        k => panic!("y42 bound: op kind {k} in the table"),
    };
    o.q_control2 = QubitId(r[1]);
    o.q_control1 = QubitId(r[2]);
    o.q_target = QubitId(r[3]);
    o.c_target = BitId(r[4]);
    o.c_condition = BitId(r[5]);
    o
}
/// Sum over the ops of (a mix of the op's seven fields) x (2 x index + 1), wrapping.
fn fingerprint(ops: &[Op]) -> u64 {
    let mut acc = 0u64;
    for (i, o) in ops.iter().enumerate() {
        let mut h = 0x9E3779B97F4A7C15u64;
        for x in [o.kind as u64, o.q_control2.0, o.q_control1.0, o.q_target.0, o.c_target.0, o.c_condition.0, o.r_target.0] {
            h = (h ^ x).wrapping_mul(0x100000001B3);
            h ^= h >> 29;
        }
        acc = acc.wrapping_add(h.wrapping_mul(2 * i as u64 + 1));
    }
    acc
}

pub(super) fn run(ops: Vec<Op>) -> Vec<Op> {
    if super::leapfrog::unbind() { return ops; }
    if !super::leapfrog::Y42_BOUND {
        return ops;
    }
    assert!(TABLE.len() >= 28 && &TABLE[..8] == b"Y42BOUND", "y42 bound: table header");
    // the whole-stream binding is now informational: the edits bind by their region (rebind.rs)
    let exact = ops.len() as u64 == u64_at(8) && fingerprint(&ops) == u64_at(16);
    let ne = u32_at(24);
    let d = super::rebind::region_shift("y42_bound", &ops, (u32_at(28), u32_at(28 + 12 * (ne - 1))), exact);
    let flat = 28 + 12 * ne;
    assert!(flat <= TABLE.len() && (TABLE.len() - flat) % 12 == 0, "y42 bound: table size");
    let rows = (TABLE.len() - flat) / 12;
    let mut out = Vec::with_capacity(ops.len() + rows);
    let mut ei = 0;
    for (i, o) in ops.into_iter().enumerate() {
        if ei < ne && (u32_at(28 + 12 * ei) as isize + d) as usize == i {
            let (at, n) = (u32_at(32 + 12 * ei), u32_at(36 + 12 * ei));
            assert!(at + n <= rows, "y42 bound: row range");
            for j in at..at + n {
                let r = row_at(flat + 12 * j);
                r.validate();
                out.push(r);
            }
            ei += 1;
        } else {
            out.push(o);
        }
    }
    assert_eq!(ei, ne, "y42 bound: an edit's index was not reached");
    eprintln!("Y42_BOUND edits={ne} rows={rows} ops={}", out.len());
    out
}
