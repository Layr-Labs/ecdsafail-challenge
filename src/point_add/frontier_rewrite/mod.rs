use quantum_ecc::circuit::Op;
mod catalog;
pub fn apply(ops:Vec<Op>)->Vec<Op> { catalog::optimize(ops) }
