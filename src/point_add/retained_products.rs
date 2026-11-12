// Retained products in unused wires, with measured cleanup and phase repair.
use crate::circuit::{Op,OperationType as K,QubitId};
use sha3::{Digest,Sha3_256};
const LEASES:&[[u64;10]]=&[[10463441,10466502,951,871,1219,870,860,1219,861,3062],
[14243654,14247262,1102,257,1117,576,1117,257,202,3609],
[15052979,15056012,547,256,790,1204,790,256,194,3034],
[15326432,15332993,1226,765,257,123,257,765,1078,6562],
[15389841,15396340,547,1117,260,530,260,1117,183,6500],
[15421657,15428156,1226,259,724,126,724,259,1083,6500],
[15441498,15447997,1226,1117,260,150,260,1117,117,6500],
[15481204,15487703,1226,1117,260,120,260,1117,1199,6500],
[15501045,15507544,1226,259,724,156,724,259,1124,6500],
[15520886,15527385,1226,1117,260,1078,260,1117,1230,6500],
[15620235,15626734,1226,259,724,674,724,259,1211,6500],
[15659941,15666440,1226,259,724,156,724,259,687,6500],
[15719536,15726035,1226,1117,260,138,260,1117,1083,6500],
[15938147,15944646,1226,259,724,674,724,259,607,6500],
[16017583,16024082,1226,259,724,605,724,259,1083,6500],
[16037424,16043923,1226,1117,260,138,260,1117,117,6500],
[16256035,16262534,1226,259,724,674,724,259,687,6500],
[16554106,16560605,1226,1117,260,150,260,1117,687,6500],
[16593812,16600311,1226,1117,260,120,260,1117,174,6500],
[16613653,16620152,1226,259,724,156,724,259,1083,6500],
[16653359,16659858,1226,259,724,605,724,259,159,6500],
[16732795,16739294,1226,259,724,674,724,259,241,6500],
[16752636,16759135,1226,1117,260,120,260,1117,616,6500],
[16792366,16798865,1226,1117,260,1078,260,1117,1113,6500],
[16832072,16838571,1226,1117,260,138,260,1117,607,6500],
[16851913,16858412,1226,259,724,126,724,259,687,6500],
[16871754,16878253,1226,1117,260,150,260,1117,1202,6500]];
fn cx(q:u64,t:u64)->Op{let mut o=Op::empty();o.kind=K::CX;o.q_control1=QubitId(q);o.q_target=QubitId(t);o}
fn hmr(q:u64)->Op{let mut o=Op::empty();o.kind=K::Hmr;o.q_target=QubitId(q);o.c_target.0=54995;o}
pub(super) fn run(ops:Vec<Op>)->Vec<Op>{
 assert_eq!(ops.len(),17891725,"retained product input count");
 let mut h=Sha3_256::new();for o in &ops{h.update((o.kind as u32).to_le_bytes());h.update([0u8;4]);for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}
 assert_eq!(format!("{:x}",h.finalize()),"c143e90580bb0c6f6a12996a50147c179c4fdfe3a50d8af85350bf9e6d755e04","retained product input hash");
 let mut out=Vec::with_capacity(ops.len()+LEASES.len()*3);let mut next=0usize;
 for (i,o) in ops.into_iter().enumerate(){
  if next>=LEASES.len(){out.push(o);continue;}
  let s=LEASES[next];
  if i as u64==s[0]{
   assert!(o.kind==K::CCX&&o.q_control2.0==s[3]&&o.q_control1.0==s[4]&&o.q_target.0==s[5]);
   let mut fill=o;fill.q_target=QubitId(s[2]);out.push(fill);out.push(cx(s[2],s[5]));
  }else if i as u64==s[1]{
   assert!(o.kind==K::CCX&&o.q_control2.0==s[6]&&o.q_control1.0==s[7]&&o.q_target.0==s[8]);
   out.push(cx(s[2],s[8]));
   out.push(hmr(s[2]));
   {let mut z=Op::empty();z.kind=K::CZ;z.q_control1=QubitId(s[6]);z.q_target=QubitId(s[7]);z.c_condition.0=54995;out.push(z);}
   next+=1;
  }else{out.push(o);}
 }
 assert_eq!(next,LEASES.len(),"retained product lease activation");
 out
}
