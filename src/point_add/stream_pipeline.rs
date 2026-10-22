use crate::circuit::Op;
pub(super) fn run(mut v:Vec<Op>)->Vec<Op>{
std::env::set_var("SL_COND","ur");v=super::cond_pass::run(v);v=super::zero_force::run(v);
v=super::product_cache::run(v);v=super::copy_elision::run(v);
v=super::classical_factors_xor::simplify_classical(v);v=super::classical_wide::simplify_classical(v);
v=super::value_rewrites::run(v);super::tof_cancel::run(v)}
