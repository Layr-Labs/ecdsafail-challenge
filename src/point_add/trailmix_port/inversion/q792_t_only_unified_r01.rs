//! One shared quotient/low preparation and one H on every T A0..252.
//! Physical sourcehead lends the sixth rank rail holding SMALL; the separate
//! paid mask adapter restores all quotient/C/SM donors after inverse chart.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn guard(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg]){
 let phase=[(p1,true),(p2,false)];mixed_mcx(c,&phase,g,d);let ts=super::q792_fold20_rank_r01::triples();let truth=ts.iter().enumerate().fold(0u32,|v,(i,t)|v|u32::from(t[0]==3)<<i);
 for av in 253..=255{super::q792_fold20_predicate_r01::rank_low(c,m,truth,63,av&63,&phase,g,d);}
}
fn small(c:&mut Circuit,r:&[QReg],sm:&[QReg],g:&QReg,out:&QReg,d:&[QReg]){let mut cs=vec![(g,true)];cs.extend(sm.iter().map(|q|(q,false)));super::q792_fold20_r01::table(c,&r.iter().collect::<Vec<_>>(),super::q792_fold20_rank_r01::triples().iter().map(|t|t[2]==0).collect(),&cs,out,d);}
fn cost(c:&Circuit,at:&mut usize,label:&str){if std::env::var_os("Q792_T_UNIFIED_COST").is_some(){let o=&c.b.ops[*at..];eprintln!("T_ONLY_UNIFIED_COST part={label} T={} N={}",o.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count(),o.len());}*at=c.b.ops.len();}
pub(super)fn emit_with_loan(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],_n:usize,j:usize,held:bool){
 assert_eq!(m.len(),20);assert_eq!(h.len(),23);if c.q797_a_support.is_some_and(|(lo,_)|lo>=253){return;}let owned=c.b.next_qubit;let mut ca=c.b.ops.len();let g=&h[0];let carry=&h[1];let mask=&h[2];let hold=&h[3];let d=&h[4..];
 let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,&h[1..]);}
 guard(c,m,p1,p2,g,&h[1..]);super::q792_unfold_lease_r01::emit(c,m,p2,g,&h[1..],false);cost(c,&mut ca,"guard-unfold");
 let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p2)).map(QReg::borrowed_alias).collect();let a=&m[4..10];let cl=&m[10..16];let sm=&m[16..20];let original=c.q797_a_support;let _scope=super::q792_t_narrow_support_r01::enter(original);
 let at=c.b.ops.len();let(root,route)=super::q794_handoffs::gather_a(c,&rank,a,w2,2,&h[2..]);c.cswap(g,root,carry);c.b.ops.extend(route.into_iter().rev());let carryloan=c.b.ops[at..].to_vec();c.cx(g,p1);
 super::q792_t_only_quotient_r02::pop(c,&rank,a,cl,sm,g,p1,mask,carry,w1,w2,&h[3..],j);cost(c,&mut ca,"carry-q-pop");
 small(c,&rank,sm,g,carry,&h[2..]);super::q792_t_low_full_unpack_unified_r01::emit(c,&rank,a,cl,sm,w1,w2,p1,carry,&h[2..],j,false,false);cost(c,&mut ca,"shared-low-unpack");
 // Sourcehead remains logical1 here; H deliberately treats its physical rail
 // as arbitrary packed cargo. Acquire the held SMALL rail only after unpack.
 let at=c.b.ops.len();let(root,route)=super::q794_handoffs::gather_a(c,&rank,a,&w1[..256],0,d);c.cx(g,root);c.cswap(g,root,hold);c.b.ops.extend(route.into_iter().rev());let headloan=c.b.ops[at..].to_vec();c.cswap(g,hold,carry);cost(c,&mut ca,"sourcehead-small-loan");
 super::q792_t_unified_mask_r01::emit(c,&rank,a,cl,sm,g,hold,mask,carry,w1,d,j,false);cost(c,&mut ca,"mask-loan");
 let rank6:Vec<_>=rank.iter().chain(std::iter::once(hold)).map(QReg::borrowed_alias).collect();super::q792_t_unified_rank_small_r01::emit(c,&rank6,sm,g,d,false);cost(c,&mut ca,"rank6-chart");
 let width=original.map_or(256,|(_,hi)|(hi.min(253)+1).next_power_of_two()).clamp(4,256);let bits=width.trailing_zeros()as usize;let upper:Vec<_>=a.iter().chain(&rank6[..2]).take(bits).map(QReg::borrowed_alias).collect();
 super::q792_t_only_h_body_r01::emit(c,&w1[..width],&w2[..width],&upper,p1,g,mask,carry,d);cost(c,&mut ca,"one-H");
 super::q792_t_unified_rank_small_r01::emit(c,&rank6,sm,g,d,true);super::q792_t_unified_mask_r01::emit(c,&rank,a,cl,sm,g,hold,mask,carry,w1,d,j,true);cost(c,&mut ca,"chart-mask-return");
 c.cswap(g,hold,carry);c.b.ops.extend(headloan.into_iter().rev());super::q792_t_low_full_unpack_unified_r01::emit(c,&rank,a,cl,sm,w1,w2,p1,carry,&h[2..],j,true,false);small(c,&rank,sm,g,carry,&h[2..]);cost(c,&mut ca,"sourcehead-low-return");
 c.cx(g,p1);c.b.ops.extend(carryloan.into_iter().rev());super::q792_unfold_lease_r01::emit(c,m,p2,g,&h[1..],true);guard(c,m,p1,p2,g,&h[1..]);if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,&h[1..]);}cost(c,&mut ca,"carry-fold-return");assert_eq!(c.b.next_qubit,owned);
}
pub(super)fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],n:usize,j:usize){emit_with_loan(c,m,p1,p2,w1,w2,h,n,j,false);}
#[path="q792_t_only_unified_check_r01.rs"]mod check;
pub fn run(){check::run();}
