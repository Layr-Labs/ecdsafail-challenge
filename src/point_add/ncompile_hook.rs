// nasqret's exact record passes (1e9efad8, src/point_add/compile: peephole rounds, measurement-based
// uncompute of provable ANDs, affine Toffoli sharing) applied to a finished op list.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT};
#[path = "ncompile/optimize.rs"]
mod base;
#[path = "ncompile/cleanup.rs"]
mod cleanup;
#[path = "ncompile/pass.rs"]
mod pass;
#[path = "ncompile/affine.rs"]
mod affine;
fn ob(x: u16) -> BitId { if x == u16::MAX { NO_BIT } else { BitId(x as u64) } }
fn operation([kind, a, b, c]: [u16; 4]) -> Op {
    use OperationType::*;
    let qa = QubitId(a as u64); let qb = QubitId(b as u64);
    let mut op = Op::empty();
    op.kind = match kind {
        1 => { op.r_target = RegisterId(a as u64); Register }
        2 => { op.r_target = RegisterId(a as u64); op.q_target = qb; AppendToRegister }
        18 => { op.r_target = RegisterId(a as u64); op.c_target = BitId(b as u64); AppendToRegister }
        3 | 4 | 5 => { op.c_target = BitId(a as u64); op.c_condition = ob(b); if kind == 3 { BitInvert } else if kind == 4 { BitStore0 } else { BitStore1 } }
        6 | 7 => { op.q_target = qa; op.c_condition = ob(b); if kind == 6 { X } else { Z } }
        8 | 9 => { op.q_control1 = qa; op.q_target = qb; op.c_condition = ob(c); if kind == 8 { CX } else { CZ } }
        12 => { op.q_target = qa; op.c_target = ob(b); Hmr }
        13 => { op.q_control2 = qa; op.q_control1 = qb; op.q_target = QubitId(c as u64); CCX }
        15 => { op.c_condition = BitId(a as u64); PushCondition }
        16 => PopCondition,
        _ => panic!("ncompile: unsupported record {}", kind),
    };
    op
}
fn row(o: &Op) -> [u16; 4] {
    use OperationType::*;
    let bit = |x: BitId| if x == NO_BIT { 65535 } else { assert!(x.0 < 65535); x.0 as u16 };
    let q = |x: QubitId| { assert!(x.0 < 65535); x.0 as u16 };
    match o.kind {
        Register => [1, o.r_target.0 as u16, 65535, 65535],
        AppendToRegister => if o.c_target != NO_BIT { [18, o.r_target.0 as u16, bit(o.c_target), 65535] } else { [2, o.r_target.0 as u16, q(o.q_target), 65535] },
        BitInvert => [3, bit(o.c_target), bit(o.c_condition), 65535],
        BitStore0 => [4, bit(o.c_target), bit(o.c_condition), 65535],
        BitStore1 => [5, bit(o.c_target), bit(o.c_condition), 65535],
        X => [6, q(o.q_target), bit(o.c_condition), 65535],
        Z => [7, q(o.q_target), bit(o.c_condition), 65535],
        CX => [8, q(o.q_control1), q(o.q_target), bit(o.c_condition)],
        CZ => [9, q(o.q_control1), q(o.q_target), bit(o.c_condition)],
        Hmr => { assert!(o.c_condition == NO_BIT); [12, q(o.q_target), bit(o.c_target), 65535] }
        CCX => { assert!(o.c_condition == NO_BIT); [13, q(o.q_control2), q(o.q_control1), q(o.q_target)] }
        PushCondition => [15, bit(o.c_condition), 65535, 65535],
        PopCondition => [16, 65535, 65535, 65535],
        _ => panic!("ncompile: unsupported operation {:?}", o.kind),
    }
}
pub fn apply(ops: Vec<Op>, width: usize) -> Vec<Op> {
    let ops: Vec<Op> = ops.into_iter().filter(|o| o.kind != OperationType::DebugPrint).collect();
    let rows: Vec<[u16; 4]> = ops.iter().map(row).collect();
    drop(ops);
    // a fresh classical bit for the measurement-based uncompute: one past the highest bit in use
    let mut maxb = 0u32;
    for r in &rows { let bits: &[usize] = match r[0] { 3|4|5 => &[1, 2], 6|7 => &[2], 8|9 => &[3], 12 => &[2], 15 => &[1], 18 => &[2], _ => &[] };
        for &k in bits { if r[k] != 65535 { maxb = maxb.max(r[k] as u32); } } }
    let scratch = u16::try_from(maxb + 1).expect("ncompile: bit space");
    let mut out = Vec::with_capacity(rows.len());
    let mut compiler = pass::Pass::new(width, scratch, 2);
    let mut aff = affine::Affine::new();
    for chunk in rows.chunks(base::CHUNK) {
        compiler.chunk(chunk.to_vec(), |r| aff.push(r, |g| out.push(operation(g))));
    }
    compiler.finish();
    aff.flush(|g| out.push(operation(g)));
    eprintln!("NCOMPILE scratch={} ops={}", scratch, out.len());
    out
}
