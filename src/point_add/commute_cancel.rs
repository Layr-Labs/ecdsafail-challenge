//! Cancel equal controlled-X involutions across only commuting operations.
//! Control writes and target reads delimit eligibility; classical guards are
//! snapshots of immutable (bit slot, write-version) pairs. No measurements move.
use crate::circuit::{analyze_ops,Op,OperationType as K,NO_BIT};
use std::collections::HashMap;
#[derive(Hash,Eq,PartialEq)]
struct Key{target:u64,a:u64,b:u64,va:u64,vb:u64,read:u64,guard:Vec<(u64,u64)>}
pub fn simplify(ops:Vec<Op>)->Vec<Op>{
 let(nq,nb,_,_)=analyze_ops(ops.iter());let mut qv=vec![0;nq as usize];let mut qr=qv.clone();let mut bv=vec![0;nb as usize];let mut guards=Vec::<(u64,u64)>::new();let mut pending=HashMap::<Key,usize>::new();let mut del=vec![false;ops.len()];let mut hits=0;
 for(i,o)in ops.iter().enumerate(){
  if o.kind==K::PushCondition{guards.push((o.c_condition.0,bv[o.c_condition.0 as usize]));continue;}
  if o.kind==K::PopCondition{guards.pop().unwrap();continue;}
  if o.kind==K::CCX{
   let(a,b)=if o.q_control1.0<o.q_control2.0{(o.q_control1.0,o.q_control2.0)}else{(o.q_control2.0,o.q_control1.0)};
   let mut g=guards.clone();if o.c_condition!=NO_BIT{g.push((o.c_condition.0,bv[o.c_condition.0 as usize]));}g.sort_unstable();g.dedup();
   let key=Key{target:o.q_target.0,a,b,va:qv[a as usize],vb:qv[b as usize],read:qr[o.q_target.0 as usize],guard:g};
   if let Some(j)=pending.remove(&key){del[j]=true;del[i]=true;hits+=1;}else{pending.insert(key,i);}
  }
  let mut read=|q:u64|qr[q as usize]+=1;
  match o.kind{
   K::CCX=>{read(o.q_control1.0);read(o.q_control2.0);qv[o.q_target.0 as usize]+=1;},
   K::CX=>{read(o.q_control1.0);qv[o.q_target.0 as usize]+=1;},
   K::X=>qv[o.q_target.0 as usize]+=1,
   K::Swap=>{read(o.q_control1.0);read(o.q_target.0);qv[o.q_target.0 as usize]+=1;qv[o.q_control1.0 as usize]+=1;},
   K::Hmr=>{read(o.q_target.0);qv[o.q_target.0 as usize]+=1;bv[o.c_target.0 as usize]+=1;},
   K::R=>{read(o.q_target.0);qv[o.q_target.0 as usize]+=1;},
   K::Z=>read(o.q_target.0),K::CZ=>{read(o.q_control1.0);read(o.q_target.0);},K::CCZ=>{read(o.q_control1.0);read(o.q_control2.0);read(o.q_target.0);},
   K::BitInvert|K::BitStore0|K::BitStore1=>bv[o.c_target.0 as usize]+=1,
   _=>{}
  }
 }
 eprintln!("COMMUTE_CANCEL pairs={hits} removed_ccx={}",hits*2);ops.into_iter().enumerate().filter(|(i,_)|!del[*i]).map(|(_,o)|o).collect()
}
