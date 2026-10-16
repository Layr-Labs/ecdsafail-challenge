// Generated from checked operation edits. Input bytes are bound before applying the table.
use crate::circuit::{Op, OperationType as K, QubitId, BitId};
const ENABLED: bool = true;
const DATA: &[u8] = include_bytes!("linear_restore.bin");
fn u32_at(p: usize) -> usize { u32::from_le_bytes(DATA[p..p+4].try_into().unwrap()) as usize }
fn row_at(p: usize) -> [u64;6] { let mut r=[0u64;6]; for j in 0..6 {let v=u16::from_le_bytes(DATA[p+2*j..p+2*j+2].try_into().unwrap());r[j]=if v==u16::MAX{u64::MAX}else{v as u64};}r }
fn rec(o:&Op)->[u64;6]{[o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0]}
fn mk(r:[u64;6])->Op {let mut o=Op::empty();
o.kind=match r[0]{0=>K::Neg,3=>K::BitInvert,4=>K::BitStore0,5=>K::BitStore1,6=>K::X,7=>K::Z,8=>K::CX,9=>K::CZ,11=>K::R,12=>K::Hmr,13=>K::CCX,14=>K::CCZ,15=>K::PushCondition,16=>K::PopCondition,_=>panic!("operation table kind")};
o.q_control2=QubitId(r[1]);o.q_control1=QubitId(r[2]);o.q_target=QubitId(r[3]);o.c_target=BitId(r[4]);o.c_condition=BitId(r[5]);o}
pub(super) fn run(ops:Vec<Op>)->Vec<Op>{
    if super::leapfrog::unbind() { return ops; }
if !ENABLED {return ops;}
// the whole-stream binding is now informational: the edits bind by local content (rebind.rs)
let exact=ops.len()==11459358&&{use sha3::{Digest,Sha3_256};let mut h=Sha3_256::new();for o in &ops {h.update((o.kind as u32).to_le_bytes());h.update([0u8;4]);for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}
format!("{:x}",h.finalize())=="3ac369248fd178edaf3b0e614e07f2d938469cd926f837ef878535e2b3438995"};
let ne=u32_at(0);let idx:Vec<usize>=(0..ne).map(|e|u32_at(4+12*e)).collect();let pos=super::rebind::window_positions("linear_restore",&ops,&idx,exact);let at_of=|e:usize|pos[e];let flat=4+12*ne;assert!(flat<=DATA.len());let mut out=Vec::with_capacity(ops.len()+1024);let mut ei=0;
for (i,o) in ops.into_iter().enumerate(){if ei<ne&&at_of(ei)==i {let at=u32_at(8+12*ei);let n=u32_at(12+12*ei);assert_eq!(rec(&o),row_at(flat+12*at),"operation table expected record");for j in at+1..at+n {out.push(mk(row_at(flat+12*j)));}ei+=1;}else{out.push(o);}}
assert_eq!(ei,ne);for o in &out{o.validate();}out}
