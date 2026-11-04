//! C85 exact generic post-passes. Keyed linear-span rows are applied by the builder before this fixed point.
use crate::circuit::{analyze_ops,Op,OperationType as K};
fn same(a:&[Op],b:&[Op])->bool{
 a.len()==b.len()&&a.iter().zip(b).all(|(x,y)|x.kind==y.kind&&x.q_control1==y.q_control1&&x.q_control2==y.q_control2&&x.q_target==y.q_target&&x.c_target==y.c_target&&x.c_condition==y.c_condition&&x.r_target==y.r_target)
}
pub(super) fn run(mut ops:Vec<Op>,config:&str)->Vec<Op>{
 if config=="off" {return ops;}
 let full=config.contains("stack");let fp=full||config.contains("fp");
 let cond=full||config.contains("cond");let sq=full||config.contains("sqtop");let y33=full||config.contains("y33");let wide=full||config.contains("wide");
 std::env::set_var("SL_COND","mfs");std::env::set_var("SL_SQTOP","1");
 for round in 0..32 {
  let before=ops.clone();let t0=ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
  if cond{ops=super::cond_pass::run(ops);}
  if sq{ops=super::sqtop_pass::run(ops);}
  if y33{let(_,nb,_,_)=analyze_ops(ops.iter());let mut next=u32::try_from(nb).unwrap();super::y33_clears::sweep(&mut ops,&mut next);}
  if wide{ops=super::classical_wide::simplify_products(ops);ops=super::classical_wide::simplify_classical(ops);}
  if fp{
   ops=super::truth_simplify::simplify_products(ops);ops=super::affine_simplify::simplify(ops);ops=super::quadratic_simplify::simplify(ops);ops=super::truth_simplify::simplify(ops);
   ops=super::interned_witness::witnesses(ops);ops=super::mabsorb::absorb(ops);ops=super::ctx_holds::apply(ops,&super::ctx_holds::DEFAULT);
  }
  if config.contains("c86fixed"){ops=super::c86_fixed::apply(ops);}
  if config.contains("c86increment"){ops=super::c86_increment::apply(ops);}
  if config.contains("c86ctx"){ops=super::c86_ctx::apply(ops,&super::c86_ctx::DEFAULT);}
  if config.contains("c86frontier"){ops=super::c86_frontier::apply(ops);}
  let stable=same(&before,&ops);let t=ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
  eprintln!("C85_FIXED_POINT round={round} before_ops={} after_ops={} before_T={t0} after_T={t} stable={stable}",before.len(),ops.len());
  if stable||!fp{return ops;}
 }
 panic!("C85 fixed point failed to converge within32 rounds");
}
