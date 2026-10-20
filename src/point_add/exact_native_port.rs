use crate::circuit::{Op,OperationType,QubitId};
pub(super)fn run(ops:Vec<Op>)->Vec<Op>{super::break_profile::save_ops("raw.ops.bin",&ops);let mut ops=super::breakthrough_generic::run(ops);for _ in 0..96{let mut o=Op::empty();o.kind=OperationType::X;o.q_target=QubitId(0);o.validate();ops.push(o);}ops}
