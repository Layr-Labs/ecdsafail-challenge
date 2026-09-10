//! Exact inverse-R00 measurement uncomputation for the Q793 step.
//! Direction-specific: a measurement packet is never reversed.
use crate::{circuit::{Op,OperationType as K,QubitId,BitId,NO_BIT},point_add::trailmix_port::circuit::{Circuit,QReg}};
use std::cell::Cell;
#[path="r00_inverse_phase.rs"]mod inverse_phase;
thread_local! {static CAPTURE:Cell<bool>=const{Cell::new(false)};static CONDITIONAL_T:Cell<u64>=const{Cell::new(0)};static PACKETS:Cell<u64>=const{Cell::new(0)};}
pub(crate) fn reverse()->bool {super::metadata_muxlease::active("Q793_MBU_REV_R00")}
pub(crate) fn capturing()->bool{CAPTURE.with(Cell::get)}
pub(crate) fn reset(){CONDITIONAL_T.with(|x|x.set(0));PACKETS.with(|x|x.set(0));}
pub(crate) fn note(conditional_t:u64){CONDITIONAL_T.with(|x|x.set(x.get()+conditional_t));PACKETS.with(|x|x.set(x.get()+1));}
pub(crate) fn totals()->(u64,u64){(CONDITIONAL_T.with(Cell::get),PACKETS.with(Cell::get))}
struct Capture;impl Capture{fn new()->Self{CAPTURE.with(|x|assert!(!x.replace(true)));Self}}
impl Drop for Capture{fn drop(&mut self){CAPTURE.with(|x|x.set(false));}}
pub(crate) const KINDS:[K;18]=[K::Neg,K::Register,K::AppendToRegister,K::BitInvert,K::BitStore0,K::BitStore1,K::X,K::Z,K::CX,K::CZ,K::Swap,K::R,K::Hmr,K::CCX,K::CCZ,K::PushCondition,K::PopCondition,K::DebugPrint];
fn nct(o:&Op)->bool{matches!(o.kind,K::X|K::CX|K::CCX)&&o.c_condition==NO_BIT}
fn optimize(mut ops:Vec<Op>)->Vec<Op>{
 let window=std::env::var("Q795_CORE_CANCEL").ok().map(|v|v.parse::<usize>().unwrap()).unwrap_or(4096);
 let mut result=Vec::with_capacity(ops.len());let mut part=Vec::new();
 let flush=|part:&mut Vec<Op>,out:&mut Vec<Op>|{if part.is_empty(){return;}super::shared_optimize::cancel_nct(part,window,8);super::shared_optimize::cancel_nct_live(part,window);if super::metadata_muxlease::active("Q794_TFACTOR"){super::q794_tfactor::apply(part,64);super::shared_optimize::cancel_nct_live(part,window);}out.append(part);};
 for op in ops.drain(..){if nct(&op){part.push(op);}else{flush(&mut part,&mut result);result.push(op);}}flush(&mut part,&mut result);result
}
pub(crate) fn template(block:usize,j:usize,measurement:BitId)->Vec<Op>{
 assert!(reverse());
 let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
 let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
 let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let iteration=circ.alloc_qreg("iter");
 let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("helpers",23);
 assert_eq!(circ.b.next_qubit,565);
 {let _capture=Capture::new();super::q793_step_r03::step(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&iteration,&w1,&w2,&helpers,j,block);}
 let marks=super::q793_step_r03::marks();let at=|name:&str|marks.iter().find(|(n,_)|*n==name).expect("missing Q793 MBU raw span").1;
 let raw=circ.into_builder().ops;let sign=QubitId(helpers[0].id()as u64);assert_eq!(sign.0,542);assert!(raw.iter().all(nct));
 let start=at("mbu_after_loan");let end=at("mbu_after_r00");let mut phase=optimize(inverse_phase::body(&raw[start..end],sign));
 assert!(phase.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX|K::Neg|K::Z|K::CZ)&&o.c_condition==NO_BIT));
 for op in &mut phase{op.c_condition=measurement;op.validate();}
 let mut h=Op::empty();h.kind=K::Hmr;h.q_target=sign;h.c_target=measurement;h.validate();
 let mut output=Vec::with_capacity(raw.len()+1);output.extend(raw[end..].iter().rev().copied());output.push(h);output.extend(phase);output.extend(raw[..start].iter().rev().copied());
 let output=optimize(output);
 for op in &output {op.validate();assert!(!matches!(op.kind,K::PushCondition|K::PopCondition));for hole in [256,257,258]{let q=QubitId(w1[hole].id()as u64);assert!(op.q_target!=q&&op.q_control1!=q&&op.q_control2!=q);}}
 output
}
pub(crate) fn check_producer(produced:&[u64],producer:&[Op],sign:QubitId)->u32{
 let inverse:Vec<_>=producer.iter().rev().copied().collect();let phase=optimize(inverse_phase::body(producer,sign));
 super::q793_mbu_native::check(produced,&inverse,&phase,sign)
}
pub fn census(){
 let mut old_ops=0usize;let mut old_t=0usize;let mut new_ops=0usize;let mut new_t=0usize;let mut conditional_t=0usize;
 for block in 0..26{for j in 0..4{let copies=if block==25{4}else{16};let old=super::q793_lifecycle_r03::template(block,j);let new=template(block,j,BitId(0));
  old_ops+=copies*old.len();old_t+=copies*old.iter().filter(|o|o.kind==K::CCX).count();new_ops+=copies*new.len();new_t+=copies*new.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();conditional_t+=copies*new.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)&&o.c_condition!=NO_BIT).count();
 }}
 let expected_twice=2*new_t-conditional_t;let schedule_delta_twice=expected_twice as isize-2*old_t as isize;
 // The whole circuit invokes two Q793 lifecycles. Each MBU replaces only
 // that lifecycle's reverse schedule, so whole expected delta equals this
 // twice-scaled single-schedule delta (not four times the schedule delta).
 eprintln!("Q793_MBU_CENSUS old_ops={old_ops} old_T={old_t} new_ops={new_ops} static_T={new_t} conditional_T={conditional_t} expected_T_x2={expected_twice} whole_expected_delta={schedule_delta_twice}");
}
