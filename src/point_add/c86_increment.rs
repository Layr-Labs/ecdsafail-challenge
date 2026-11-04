//! Incremental exact CTX, lease, duplicate-loan/hold stack; fixed two rounds.
use crate::circuit::Op;
pub(crate) fn apply(mut ops:Vec<Op>)->Vec<Op>{
    for round in 0..2{eprintln!("C86_INCREMENT round={round}");
        ops=super::c86_ctx::apply(ops,&super::c86_ctx::DEFAULT);
        ops=super::c86_leases::apply(ops);
    }
    super::c86_hold::hold_pass(ops)
}
