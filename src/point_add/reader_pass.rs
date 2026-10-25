// Generated from checked reader and affine edit records.
use crate::circuit::{Op,OperationType as K,QubitId,BitId};
fn mk(r:[u64;6])->Op { let mut o=Op::empty();
o.kind=match r[0]{0=>K::Neg,3=>K::BitInvert,4=>K::BitStore0,5=>K::BitStore1,6=>K::X,7=>K::Z,8=>K::CX,9=>K::CZ,11=>K::R,12=>K::Hmr,13=>K::CCX,14=>K::CCZ,15=>K::PushCondition,16=>K::PopCondition,_=>panic!("unsupported checked IR kind")};
o.q_control2=QubitId(r[1]);o.q_control1=QubitId(r[2]);o.q_target=QubitId(r[3]);o.c_target=BitId(r[4]);o.c_condition=BitId(r[5]);o}
const ON:&[u8]=include_bytes!("reader_on.bin");
fn u32_at(d:&[u8],p:usize)->usize{u32::from_le_bytes(d[p..p+4].try_into().unwrap()) as usize}
fn row_at(d:&[u8],p:usize)->[u64;6]{let mut r=[0u64;6];for j in 0..6{let v=u16::from_le_bytes(d[p+2*j..p+2*j+2].try_into().unwrap());r[j]=if v==u16::MAX{u64::MAX}else{v as u64}}r}

pub(super) fn run(ops:Vec<Op>)->Vec<Op>{
let mode=std::env::var("READER_CUT").unwrap_or_default();if mode.is_empty()||mode=="0"{return ops}
assert_eq!(ops.len(),11287435,"READER_CUT body length binding");
let mut h=14695981039346656037u64;for o in &ops{for x in [o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h=(h^x).wrapping_mul(1099511628211u64)}}
assert_eq!(h,16119914888370573928u64,"READER_CUT complete prefix fingerprint binding");
use sha3::{Digest,Sha3_256};let mut sh=Sha3_256::new();for o in &ops{sh.update((o.kind as u32).to_le_bytes());sh.update([0u8;4]);for x in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{sh.update(x.to_le_bytes());}}assert_eq!(format!("{:x}",sh.finalize()),"baf107a4cab0e3a799fd972ca23efd6fad084b349d32a9e5b1a3f92a86f5290d","reader input-prefix");
let data=match mode.as_str(){"on"=>ON,"1"=>ON,_=>panic!("reader mode")};
let ne=u32_at(data,0);let flat=4+12*ne;assert!(flat<=data.len());
let mut out=Vec::with_capacity(ops.len()+100000);let mut ei=0;for (i,o) in ops.into_iter().enumerate(){if ei<ne&&u32_at(data,4+12*ei)==i{let at=u32_at(data,8+12*ei);let n=u32_at(data,12+12*ei);for j in at..at+n{out.push(mk(row_at(data,flat+12*j)))}ei+=1}else{out.push(o)}}assert_eq!(ei,ne);for o in &out{o.validate()}
eprintln!("READER_CUT mode={mode} extensions=1348 max_depth=4");out}
