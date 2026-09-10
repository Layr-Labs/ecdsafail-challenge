//! Exact direction-specific measurement uncomputation. Experimental opt-in.
//! Forward Sign and inverse R00 only; never reverse a measurement packet.
use crate::{circuit::{Op,OperationType as K,QubitId,BitId,NO_BIT},point_add::trailmix_port::circuit::{Circuit,QReg}};
use std::cell::Cell;
#[path="r00_inverse_phase.rs"]mod inverse_phase;
thread_local! {static CAPTURE:Cell<bool>=const{Cell::new(false)};static CONDITIONAL_T:Cell<u64>=const{Cell::new(0)};static PACKETS:Cell<u64>=const{Cell::new(0)};}
pub(crate) fn forward()->bool {super::metadata_muxlease::active("Q794_MBU_FWD_SIGN")}
pub(crate) fn reverse()->bool {super::metadata_muxlease::active("Q794_MBU_REV_R00")}
pub(crate) fn enabled()->bool {forward()||reverse()}
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
 let flush=|part:&mut Vec<Op>,out:&mut Vec<Op>|{if part.is_empty(){return;}super::shared_optimize::cancel_nct(part,window,8);super::shared_optimize::cancel_nct_live(part,window);if super::metadata_muxlease::active("Q794_TFACTOR"){super::q794_tfactor::apply(part,4096);super::shared_optimize::cancel_nct_live(part,window);}out.append(part);};
 for op in ops.drain(..){if nct(&op){part.push(op);}else{flush(&mut part,&mut result);result.push(op);}}flush(&mut part,&mut result);result
}
pub(crate) fn template(block:usize,j:usize,inverse:bool,measurement:BitId)->Vec<Op>{
 assert!(if inverse{reverse()}else{forward()});
 let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
 let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
 let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let iteration=circ.alloc_qreg("iter");
 let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("helpers",23);
 assert_eq!(circ.b.next_qubit,565);
 {let _capture=Capture::new();super::q794_step::step(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&iteration,&w1,&w2,&helpers,j,block);}
 let marks=super::q794_step::marks();let at=|name:&str|marks.iter().find(|(n,_)|*n==name).expect("missing MBU exact raw span").1;
 let raw=circ.into_builder().ops;let sign=QubitId(helpers[0].id()as u64);assert_eq!(sign.0,542);
 assert!(raw.iter().all(nct));
 let(start,end,phase)=if inverse {
  let start=at("mbu_after_loan");let end=at("mbu_after_r00");(start,end,inverse_phase::body(&raw[start..end],sign))
 }else{
  let mut pc=Circuit::new();pc.b.count_only=false;pc.b.fiat_hash=None;pc.b.next_qubit=565;
  pc.q797_a_support=Some(super::metadata_entry_head5::A_SUPPORTS[block]);
  let dirty:Vec<_>=helpers[1..].iter().chain(std::iter::once(&iteration)).map(QReg::borrowed_alias).collect();
  let(_,tend)=super::shared_step::SCHEDULE_SUPPORTS[block];
  super::q794_sign::measurement::emit(&mut pc,&rank,&a,&c,&sm,&p1,&p2,&helpers[0],&w1,&w2,&dirty,j,(tend+1).min(258));
  assert_eq!(pc.b.next_qubit,565);(at("before_sign"),at("mbu_after_sign"),pc.into_builder().ops)
 };
 let mut phase=optimize(phase);
 assert!(phase.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX|K::Neg|K::Z|K::CZ)&&o.c_condition==NO_BIT));
 for op in &mut phase{op.c_condition=measurement;op.validate();}
 let mut h=Op::empty();h.kind=K::Hmr;h.q_target=sign;h.c_target=measurement;h.validate();
 let mut output=Vec::with_capacity(raw.len()+1);
 if inverse {output.extend(raw[end..].iter().rev().copied());}else{output.extend_from_slice(&raw[..start]);}
 output.push(h);output.extend(phase);
 if inverse {output.extend(raw[..start].iter().rev().copied());}else{output.extend_from_slice(&raw[end..]);}
 let output=optimize(output);
 for op in &output {op.validate();assert!(!matches!(op.kind,K::PushCondition|K::PopCondition));for hole in [257,258]{let q=QubitId(w1[hole].id()as u64);assert!(op.q_target!=q&&op.q_control1!=q&&op.q_control2!=q);}}
 output
}
