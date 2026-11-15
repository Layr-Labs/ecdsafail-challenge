use crate::circuit::Op;
pub(super) fn run(mut v:Vec<Op>)->Vec<Op>{
v=super::source_edits::run(v,include_str!("row_edits.txt"));
std::env::set_var("SL_COND","ur");v=super::cond_pass::run(v);v=super::zero_force::run(v);
v=super::source_edits::run(v,include_str!("and_cache.txt"));
v=super::source_edits::run(v,include_str!("product_copy.txt"));
v=super::classical_factors_xor::simplify_classical(v);v=super::classical_wide::simplify_classical(v);
super::source_edits::run(v,include_str!("value_edits.txt"))}
