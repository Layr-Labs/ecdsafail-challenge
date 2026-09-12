//! Whole physical fold20 step. Native/lifecycle/canonical qualification required.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
thread_local!{static TRACE:std::cell::RefCell<Vec<(&'static str,usize)>>=const{std::cell::RefCell::new(Vec::new())};}
pub(super) fn marks()->Vec<(&'static str,usize)>{TRACE.with(|t|t.borrow().clone())}
fn mark(c:&Circuit,name:&'static str){TRACE.with(|t|{let mut t=t.borrow_mut();if std::env::var_os("FOLD20_STAGE_COST").is_some(){let from=t.last().map(|x|x.1).unwrap_or(0);let ops=&c.b.ops[from..];eprintln!("FOLD20_STAGE_COST name={name} ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count());}t.push((name,c.b.ops.len()));});}
fn birth_cargo(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],d:&[QReg]){let mut cs=vec![(p1,true),(p2,true)];cs.extend(m.iter().map(|q|(q,false)));c.cx(&w1[3],&w1[2]);cs.push((&w1[2],true));mixed_mcx(c,&cs,&w1[3],d);c.cx(&w1[3],&w1[2]);}
fn birth_digit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,x:&QReg,polarity:bool,d:&[QReg]){let mut cs=vec![(p1,true),(p2,true),(x,polarity)];cs.extend(m.iter().enumerate().filter(|(i,_)|*i!=10).map(|(_,q)|(q,false)));mixed_mcx(c,&cs,&m[10],d);}
fn birth_flag(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],target:&QReg,d:&[QReg]){let mut cs=prefix.to_vec();cs.extend(m.iter().map(|q|(q,false)));mixed_mcx(c,&cs,target,d);}
pub(super) fn step(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,it:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],post_j:usize,block:usize){
    assert_eq!(h.len(),23);let n=c.b.next_qubit;let start=c.b.ops.len();TRACE.with(|t|t.borrow_mut().clear());let entry_j=(post_j+3)%4;
    let full=std::env::var_os("FOLD20_STEP_FULLWIDTH").is_some();let (rfirst,tend)=if full{(0,259)}else{super::shared_step::SCHEDULE_SUPPORTS[block]};let(lo,hi)=if full{(0,256)}else{super::metadata_entry_head5::A_SUPPORTS[block]};let oldsupport=c.q797_a_support.replace((lo,hi));
    let pool:Vec<_>=h.iter().chain(std::iter::once(it)).map(QReg::borrowed_alias).collect();let sign=&pool[0];let dirty=&pool[1..];
    if entry_j==0{birth_cargo(c,m,p1,p2,w1,&pool);birth_digit(c,m,p1,p2,&w2[0],false,&pool);}mark(c,"birth_decode");
    // Hold one global A-pad loan through T10, the phase rotation, and R01.
    // Each body returns h0=0; the intervening rotation restores its lenders
    // and leaves W1 unchanged. Terminal A255 skips that rotation entirely.
    let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();super::q792_fold20_address_r01::loan(c,m,sign,&bank,dirty,false);
    super::q792_t10_phaselease_r01::emit_with_loan(c,m,p1,p2,w1,w2,h,tend,entry_j,true);mark(c,"T10");
    super::q792_rotation_r01::rotate(c,m,p1,p2,w2,&pool,false);
    super::q792_r01_phaselease_r01::emit_with_loan(c,m,p1,p2,w1,w2,h,entry_j,259-rfirst,true);mark(c,"R01");
    c.ccx(p1,p2,sign);
    super::q792_r00_r01::emit(c,m,p1,p2,sign,w1,w2,dirty,entry_j,259-rfirst);mark(c,"R00");
    super::q792_rotation_r01::rotate(c,m,p1,p2,w2,dirty,true);super::q792_fast_routes_r01::r00(c,m,p1,p2,w2,dirty);
    super::q792_terminal_r01::emit(c,m,dirty,post_j==0,false);super::q792_fold20_counter_r02::emit(c,m,p1,p2,dirty,entry_j);mark(c,"counter");
    super::q792_fast_routes_r01::c1_inbound(c,m,p1,p2,sign,w1,w2,dirty);super::q792_passive_r01::emit(c,m,p1,p2,it,w1,w2,h,post_j,5);mark(c,"before_entry");
    super::q792_entry_boundary_r01::entry_with_support(c,m,p1,p2,sign,w1,w2,dirty,post_j,lo,hi);mark(c,"entry_transfer");
    // Newborn's Sign=1 implies phase11. P1 can fund rank while P2 is carry.
    c.cx(sign,p1);super::q792_unfold_lease_r01::emit(c,m,p1,sign,dirty,false);let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p1)).map(QReg::borrowed_alias).collect();
    super::q793_step_r03::newborn(c,&rank,&m[4..10],&m[10..16],&m[16..20],p2,sign,w1,w2,dirty,post_j);
    super::q792_unfold_lease_r01::emit(c,m,p1,sign,dirty,true);c.cx(sign,p1);
    super::q792_passive_r01::emit(c,m,p1,p2,it,w1,w2,h,post_j,4);mark(c,"newborn");
    super::q792_fast_routes_r01::r_to_t(c,m,p1,p2,sign,w1,w2,dirty,post_j);
    if post_j==0{birth_digit(c,m,p1,p2,sign,true,dirty);birth_flag(c,m,&[(p1,true),(p2,true)],sign,dirty);birth_cargo(c,m,p1,p2,w1,dirty);birth_flag(c,m,&[(p1,true)],p2,dirty);}mark(c,"before_sign");
    super::q792_sign_phaselease_r01::emit(c,m,p1,p2,sign,w1,w2,dirty,post_j,(tend+1).min(258));if post_j==0{birth_flag(c,m,&[(p1,true)],p2,dirty);}mark(c,"before_exit");
    if post_j==0{super::q792_szero_exit_r01::emit_with_loan(c,m,p1,p2,it,w1,w2,h,lo,hi,true);}mark(c,"after_exit");
    super::q792_passive_r01::emit(c,m,p1,p2,it,w1,w2,h,post_j,6);super::q792_fast_routes_r01::final_cargo(c,m,p1,p2,it,w1,w2,h,true);
    // S0 exit transports the held passenger through its existing SM3 loan
    // from the old A pad to the new A pad. All other stages preserve A.
    super::q792_fold20_address_r01::loan(c,m,sign,&bank,dirty,true);mark(c,"final");
    assert_eq!(c.b.next_qubit,n);for op in &c.b.ops[start..]{for x in [256,257,258]{let q=w1[x].id()as u64;assert!([op.q_target.0,op.q_control1.0,op.q_control2.0].iter().all(|&id|id!=q),"whole20 touched hole{x}");}}
    if std::env::var_os("Q795_TRACE").is_none(){let mut tail=c.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);c.b.ops.extend(tail);}c.q797_a_support=oldsupport;
}
#[path="q792_step_check_r01.rs"]mod check;
pub fn run(){check::run();}
