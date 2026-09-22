//! T-only wide A40..252 physical wrapper. The missing rank bit is P2;
//! mask is funded from known sourcehead AFTER unpack/chart, then returned.
//! q0 acquisition is the separately checked shared quotient adapter.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn truth(f:impl Fn([usize;3])->bool)->u32{super::q792_fold20_rank_r01::triples().iter().enumerate().fold(0,|v,(i,&t)|v|((f(t)as u32)<<i))}
fn guard(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg]){
 let phase=[(p1,true),(p2,false)];mixed_mcx(c,&phase,g,d);
 for (lm,lv) in [(32usize,0usize),(56,32)]{super::q792_fold20_predicate_r01::rank_low(c,m,truth(|t|t[0]==0),lm,lv,&phase,g,d);}
 for av in 253..=255{super::q792_fold20_predicate_r01::rank_low(c,m,truth(|t|t[0]==3),63,av&63,&phase,g,d);}
}
fn small(c:&mut Circuit,rank:&[QReg],sm:&[QReg],g:&QReg,out:&QReg,d:&[QReg]){
 let values:Vec<_>=super::q792_fold20_rank_r01::triples().iter().map(|t|t[2]==0).collect();super::q792_fold20_r01::table(c,&rank.iter().collect::<Vec<_>>(),values,&[(g,true),(&sm[3],false)],out,d);
}
fn chart(c:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,_carry:&QReg,_mask:&QReg,d:&[QReg]){
 // After +8 token and low unpack, Cquarter+token<=62 for A>=40,
 // including C1 and all parked low residual values. Sourcehead funds mask.
 super::q792_t_upper_triangle_r01::emit(c,rank,cl,sm,Some((g,true)),d,false);
 super::metadata_arithmetic5::add(c,a,cl,None,false);for(l,r)in a.iter().zip(cl){c.cx(l,r);c.cx(r,l);c.cx(l,r);}
}
fn head_mask(c:&mut Circuit,w1:&[QReg],upper:&[QReg],g:&QReg,mask:&QReg){
 let at=c.b.ops.len();let mut nodes:Vec<_>=w1[..(1usize<<upper.len())].iter().collect();for q in upper{let mut next=Vec::new();for pair in nodes.chunks_exact(2){c.cswap(q,pair[0],pair[1]);next.push(pair[0]);}nodes=next;}
 let root=nodes[0];let route=c.b.ops[at..].to_vec();c.cx(g,root);c.cswap(g,root,mask);c.b.ops.extend(route.into_iter().rev());
}
fn price(c:&Circuit,at:&mut usize,label:&str){if std::env::var_os("Q792_T_ONLY_WIDE_COST").is_some(){let ops=&c.b.ops[*at..];eprintln!("T_ONLY_WIDE_COST {label} T={} N={}",ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count(),ops.len());}*at=c.b.ops.len();}
pub(super)fn emit_with_loan(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],_n:usize,j:usize,held:bool){
 assert_eq!(m.len(),20);assert_eq!(h.len(),23);let owned=c.b.next_qubit;if c.q797_a_support.is_some_and(|(lo,hi)|hi<=40||lo>=253){return;}
 let g=&h[0];let carry=&h[1];let mask=&h[2];let d=&h[3..];let mut cost=c.b.ops.len();
 let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,&h[1..]);}price(c,&mut cost,"global-entry");
 guard(c,m,p1,p2,g,&h[1..]);super::q792_unfold_lease_r01::emit(c,m,p2,g,&h[1..],false);price(c,&mut cost,"guard-unfold");
 let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p2)).map(QReg::borrowed_alias).collect();let a=&m[4..10];let cl=&m[10..16];let sm=&m[16..20];
 let at=c.b.ops.len();let(root,route)=super::q794_handoffs::gather_a(c,&rank,a,w2,2,&h[2..]);c.cswap(g,root,carry);c.b.ops.extend(route.into_iter().rev());let carry_ops=c.b.ops[at..].to_vec();
 c.cx(g,p1);
 // Root-owned q-only API is inserted once its source is settled.
 super::q792_t_only_quotient_r02::pop(c,&rank,a,cl,sm,g,p1,mask,carry,w1,w2,d,j);
 price(c,&mut cost,"carry-q-pop");
 super::q792_t_small_token_r01::emit(c,&rank,sm,g,d,false);small(c,&rank,sm,g,carry,d);
 super::q792_t_low_full_unpack_r04::emit(c,&rank,a,cl,sm,w1,w2,p1,carry,d,j,false,false);small(c,&rank,sm,g,carry,d);price(c,&mut cost,"token-low-unpack");
 let at=c.b.ops.len();chart(c,&rank,a,cl,sm,g,carry,mask,d);let chart_ops=c.b.ops[at..].to_vec();price(c,&mut cost,"wide-chart");
 let width=c.q797_a_support.map_or(256,|(_,hi)|(hi.min(253)+1).next_power_of_two()).clamp(64,256);let bits=width.trailing_zeros()as usize;
 let upper:Vec<_>=cl.iter().chain(&rank[..2]).take(bits).map(QReg::borrowed_alias).collect();let at=c.b.ops.len();head_mask(c,w1,&upper,g,mask);let head_ops=c.b.ops[at..].to_vec();price(c,&mut cost,"head-mask-loan");
 super::q792_t_only_h_body_r01::emit(c,&w1[..width],&w2[..width],&upper,p1,g,mask,carry,d);price(c,&mut cost,"arithmetic");
 c.b.ops.extend(head_ops.into_iter().rev());c.b.ops.extend(chart_ops.into_iter().rev());price(c,&mut cost,"head-chart-return");
 small(c,&rank,sm,g,carry,d);super::q792_t_low_full_unpack_r04::emit(c,&rank,a,cl,sm,w1,w2,p1,carry,d,j,true,false);small(c,&rank,sm,g,carry,d);super::q792_t_small_token_r01::emit(c,&rank,sm,g,d,true);price(c,&mut cost,"low-token-return");
 c.cx(g,p1);c.b.ops.extend(carry_ops.into_iter().rev());super::q792_unfold_lease_r01::emit(c,m,p2,g,&h[1..],true);guard(c,m,p1,p2,g,&h[1..]);price(c,&mut cost,"carry-fold-guard-return");
 if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,&h[1..]);}price(c,&mut cost,"global-return");assert_eq!(c.b.next_qubit,owned);
}
pub(super)fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],n:usize,j:usize){emit_with_loan(c,m,p1,p2,w1,w2,h,n,j,false);}
#[path="q792_t_only_wide_check_r02.rs"]mod check;
pub fn run(){check::run();}
