use crate::circuit::Op;
pub(super) fn run(mut v:Vec<Op>)->Vec<Op>{
std::env::set_var("SL_COND","ur");v=super::cond_pass::run(v);v=super::zero_force::run(v);
// w124-on-6602: product_cache / copy_elision / value_rewrites tables are bound to 6602a4e8's gate list (SHA3 header)
// and refuse any other input; dropped here (lane 3 regenerates). The generic passes run unchanged.

v=super::classical_factors_xor::simplify_classical(v);v=super::classical_wide::simplify_classical(v);
v}
