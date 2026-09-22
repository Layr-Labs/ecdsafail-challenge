//! One complete T-only H body on A<40. Ah=0 compresses the original rank
//! to Ch+4*Sh, freeing the already-funded P2 to hold the small-S flag.
//! All quantum branch controls and dirty passenger lifetimes are explicit.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn guard(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg]){let ts=super::q792_fold20_rank_r01::triples();let rt=ts.iter().enumerate().fold(0u32,|v,(i,t)|v|u32::from(t[0]==0)<<i);for(lm,lv)in[(32,0),(56,32)]{super::q792_fold20_predicate_r01::rank_low(c,m,rt,lm,lv,&[(p1,true),(p2,false)],g,d);}}
fn small(c:&mut Circuit,r:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,out:&QReg,d:&[QReg],j:usize){let ts=super::q792_fold20_rank_r01::triples();let mut cs=vec![(g,true)];cs.extend(sm.iter().map(|q|(q,false)));if j&1!=0{cs.push((&cl[0],j==1));}super::q792_fold20_r01::table(c,&r.iter().collect::<Vec<_>>(),ts.iter().map(|t|t[2]==0).collect(),&cs,out,d);}
fn cost(c:&Circuit,at:&mut usize,label:&str){if std::env::var_os("Q792_T_ONLY_COST").is_some(){let o=&c.b.ops[*at..];eprintln!("T_ONLY_NARROW_COST part={label} T={} N={}",o.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count(),o.len());}*at=c.b.ops.len();}
pub(super)fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],_n:usize,j:usize){emit_with_loan(c,m,p1,p2,w1,w2,h,_n,j,false);}
pub(super)fn emit_with_loan(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],_n:usize,j:usize,held:bool){
 assert_eq!(m.len(),20);assert_eq!(h.len(),23);if c.q797_a_support.is_some_and(|(lo,_)|lo>=40){return;}let owned=c.b.next_qubit;let mut ca=c.b.ops.len();let g=&h[0];let carry=&h[1];let mask=&h[2];let d=&h[3..];
 let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,&h[1..]);}cost(c,&mut ca,"global-entry");
 guard(c,m,p1,p2,g,&h[1..]);super::q792_unfold_lease_r01::emit(c,m,p2,g,&h[1..],false);cost(c,&mut ca,"guard-unfold");let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p2)).map(QReg::borrowed_alias).collect();let a=&m[4..10];let cl=&m[10..16];let sm=&m[16..20];
 let original=c.q797_a_support;let _quotient_scope=super::q792_t_narrow_support_r01::enter(original);let(lo,hi)=original.unwrap_or((0,256));c.q797_a_support=Some((lo,hi.min(40)));let width=(hi.min(40)+1).next_power_of_two();let address_bits=width.trailing_zeros()as usize;assert!(width<=64);
 let at=c.b.ops.len();let(root,route)=super::q794_handoffs::gather_a(c,&rank,a,w2,2,d);c.cswap(g,root,carry);c.b.ops.extend(route.into_iter().rev());let loan=c.b.ops[at..].to_vec();cost(c,&mut ca,"carry-loan");
 c.cx(g,p1);
 // Shared physical quotient helper will be supplied by independent endpoint work.
 super::q792_t_only_quotient_r02::pop(c,&rank,a,cl,sm,g,p1,mask,carry,w1,w2,d,j);cost(c,&mut ca,"q-mask-pop");
 small(c,&rank,cl,sm,g,carry,d,j);super::q792_t_low_full_unpack_narrow_r02::emit(c,&rank,a,cl,sm,w1,w2,p1,carry,d,j,false,false);cost(c,&mut ca,"low-unpack");
 let ts=super::q792_fold20_rank_r01::triples();let pairs:Vec<_>=ts.iter().enumerate().filter(|(_,t)|t[0]==0).map(|(r,t)|(r,t[1]+4*t[2])).collect();let at=c.b.ops.len();super::q792_unfold_lease_r01::permutation(c,&rank.iter().collect::<Vec<_>>(),g,d,&pairs);let chart=c.b.ops[at..].to_vec();c.cswap(g,p2,carry);cost(c,&mut ca,"rank-small-flag");
 let at=c.b.ops.len();let mut nodes:Vec<_>=w1[..width].iter().collect();for b in 0..address_bits{let mut next=Vec::new();for pair in nodes.chunks_exact(2){c.cswap(&a[b],pair[0],pair[1]);next.push(pair[0]);}nodes=next;}let head=nodes[0];let route=c.b.ops[at..].to_vec();c.cx(g,head);c.cswap(g,head,mask);c.b.ops.extend(route.iter().rev().copied());let maskloan=c.b.ops[at..].to_vec();cost(c,&mut ca,"source-head-mask-loan");
 super::q792_t_only_h_body_r01::emit(c,&w1[..width],&w2[..width],&a[..address_bits],p1,g,mask,carry,d);cost(c,&mut ca,"H-public-width");
 c.b.ops.extend(maskloan.into_iter().rev());c.cswap(g,p2,carry);c.b.ops.extend(chart.into_iter().rev());super::q792_t_low_full_unpack_narrow_r02::emit(c,&rank,a,cl,sm,w1,w2,p1,carry,d,j,true,false);small(c,&rank,cl,sm,g,carry,d,j);cost(c,&mut ca,"low-return");
 c.cx(g,p1);c.b.ops.extend(loan.into_iter().rev());cost(c,&mut ca,"q-mask-carry-return");
 c.q797_a_support=original;super::q792_unfold_lease_r01::emit(c,m,p2,g,&h[1..],true);guard(c,m,p1,p2,g,&h[1..]);if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,&h[1..]);}cost(c,&mut ca,"fold-guard-global-return");assert_eq!(c.b.next_qubit,owned);
}
#[path="q792_t_only_narrow_check_r02.rs"]mod check;
pub fn run(){check::run();}
