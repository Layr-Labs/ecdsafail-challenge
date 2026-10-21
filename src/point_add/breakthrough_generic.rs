use crate::circuit::{Op,OperationType,NO_BIT,analyze_ops};
fn report(name:&str,ops:&[Op]){
 let(mut depth,mut native,mut weight)=(0i32,0u64,0.0f64);
 for op in ops{match op.kind{OperationType::PushCondition=>depth+=1,OperationType::PopCondition=>{depth-=1;assert!(depth>=0);},OperationType::CCX|OperationType::CCZ=>{native+=1;weight+=2.0f64.powi(-depth-i32::from(op.c_condition!=NO_BIT));},_=>{}}}
 assert_eq!(depth,0);let(nq,nb,_,_)=analyze_ops(ops.iter());eprintln!("GENERIC_STAGE name={name} ops={} nq={nq} nb={nb} native={native} depth_weight={weight:.6} diagnostic_only=1",ops.len());
}
pub(super)fn run(mut ops:Vec<Op>)->Vec<Op>{
 report("raw",&ops);
 for name in["product","affine","quadratic","truth"]{ops=match name{"product"=>super::truth_simplify::simplify_products(ops),"affine"=>super::affine_simplify::simplify(ops),"quadratic"=>super::quadratic_simplify::simplify(ops),_=>super::truth_simplify::simplify(ops)};report(name,&ops);}
 ops=super::interned_witness::witnesses(ops);report("interned_witness",&ops);
 if std::env::var("HEO_MABSORB").is_ok_and(|v|v=="1"){ops=super::mabsorb::absorb(ops);report("measurement_absorption",&ops);}
 ops=super::pscan::run(ops);report("parity_scan",&ops);
 ops=super::cond_pass::run(ops);report("conditional",&ops);
 ops=super::sqtop_pass::run(ops);report("square_top",&ops);
 std::env::set_var("SL_COND","ur");ops=super::cond_pass::run(ops);std::env::remove_var("SL_COND");report("conditional_ur",&ops);
 ops=super::zero_force::run(ops);report("zero_force",&ops);
 ops=super::classical_factors_xor::simplify_classical(ops);report("classical_factors",&ops);
 ops=super::classical_wide::simplify_classical(ops);report("classical_wide",&ops);
 ops
}
