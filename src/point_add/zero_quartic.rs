//! Remove two universally zero quartic phase channels, preserving every draw.
//! The caller binds the complete input prefix; fresh guarded DAG/SAT proofs
//! certify each quartic and both incoming scratch values on that prefix.
use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT};
fn pair(o:&Op,k:K,a:QubitId,b:QubitId,m:crate::circuit::BitId)->bool{o.kind==k&&o.c_condition==m&&((o.q_control1==a&&o.q_target==b)||(o.q_control1==b&&o.q_target==a))}
pub fn sites(ops:&[Op])->Vec<(usize,[QubitId;6])>{
 let mut out=vec![];
 for i in 0..ops.len().saturating_sub(7){let o=&ops[i];if o.kind!=K::CCX{continue;}let a=o.q_control1;let b=o.q_control2;let u=o.q_target;
  if !((u.0==582&&[a.0,b.0].contains(&1098)&&[a.0,b.0].contains(&1220))||(u.0==1126&&[a.0,b.0].contains(&1218)&&[a.0,b.0].contains(&861))){continue;}
  let p=&ops[i..i+7];assert_eq!(o.c_condition,NO_BIT);assert_eq!(p[1].kind,K::CCX);assert_eq!(p[1].c_condition,NO_BIT);let(c,d,v)=(p[1].q_control1,p[1].q_control2,p[1].q_target);
  let qs=[a,b,c,d,u,v];for x in 0..6{for y in 0..x{assert_ne!(qs[x],qs[y]);}}
  assert!(pair(&p[2],K::CZ,u,v,NO_BIT));assert_eq!(p[3].kind,K::Hmr);assert_eq!(p[3].q_target,v);assert_eq!(p[3].c_condition,NO_BIT);assert!(pair(&p[4],K::CZ,c,d,p[3].c_target));assert_eq!(p[5].kind,K::Hmr);assert_eq!(p[5].q_target,u);assert_eq!(p[5].c_condition,NO_BIT);assert_eq!(p[5].c_target,p[3].c_target);assert!(pair(&p[6],K::CZ,a,b,p[5].c_target));
  assert_eq!(ops[i-1].kind,K::PushCondition);assert_eq!(ops[i-2].kind,K::Hmr);assert_eq!(ops[i-2].q_target,u);assert_eq!(ops[i-1].c_condition,ops[i-2].c_target);assert_eq!(ops[i+7].kind,K::PopCondition);
  out.push((i,qs));
 }
 assert_eq!(out.len(),2,"complete residual quartic channel census");out
}
pub fn local_controls(){
 // Complete old/new channel audit, including arbitrary incoming classical bit,
 // both measurement coins and inactive-branch dirty scratch. On an active
 // branch, independent global proofs must certify initially zero scratch.
 for x in 0..16{let(a,b,c,d)=(x&1!=0,x&2!=0,x&4!=0,x&8!=0);for guard in[false,true]{for dirty in 0..4{if guard&&dirty!=0{continue;}for oldm in[false,true]{for coins in 0..4{
  let(mut u,mut v)=(dirty&1!=0,dirty&2!=0);let(mut nu,mut nv)=(u,v);let(mut m,mut nm)=(oldm,oldm);let(mut phase,mut newphase)=(false,false);let(r1,r2)=(coins&1!=0,coins&2!=0);
  if guard{u^=a&&b;v^=c&&d;phase^=u&&v;phase^=v&&r1;v=false;m=r1;phase^=c&&d&&m;phase^=u&&r2;u=false;m=r2;phase^=a&&b&&m;
   newphase^=nv&&r1;nv=false;nm=r1;newphase^=nu&&r2;nu=false;nm=r2;
  }
  assert_eq!((u,v,m),(nu,nv,nm));assert_eq!(phase^newphase,guard&&a&&b&&c&&d);
 }}}}}
}
pub(super) fn run(ops:Vec<Op>)->Vec<Op>{
 local_controls();let sites=sites(&ops);let mut delete=vec![false;ops.len()];for(i,_)in sites{for j in[0,1,2,4,6]{delete[i+j]=true;}}
 ops.into_iter().zip(delete).filter_map(|(o,d)|if d{None}else{Some(o)}).collect()
}
