//! R01 scan chart: literal M_high=(A+C)>>6 on two rank wires.
//! M+S<=256: only M=128,S=128 needs a ninth high-rank state. Its
//! Ah=2,C_high=0,carry=0 endpoint stores the surplus code in known-zero SM0.
//! A_low and Csum_low stay unchanged, so carry=[A_low>Csum_low] uncomputes.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn carry(c:&mut Circuit,a:&[QReg],cl:&[QReg],out:&QReg,d:&[QReg],positive:bool){
 if !positive{c.x(out);}for bit in 0..6{for i in bit+1..6{c.cx(&a[i],&cl[i]);}let mut cs=vec![(&a[bit],true),(&cl[bit],false)];cs.extend(cl[bit+1..].iter().map(|q|(q,false)));mixed_mcx(c,&cs,out,d);for i in (bit+1..6).rev(){c.cx(&a[i],&cl[i]);}}
}
fn permutation(carry:usize)->Vec<usize>{
 let ts=super::q792_fold20_rank_r01::triples();let mut p:Vec<_>=(0..64).collect();let(mut assigned,mut used)=([false;64],[false;64]);
 for(r,t)in ts.iter().enumerate(){let h=t[0]+t[1]+carry;let sh=t[2];if h>3||h+sh>4{continue;}
  for z in 0..2{if h+sh==4&&z!=0{continue;}let mut nz=z;let slot=match h{0=>sh,1=>sh+4*t[0],2=>{if sh==2{if t[0]==2{assert_eq!(carry,0);nz=1;6}else{6+t[0]}}else{2*t[0]+sh}},3=>2*t[0]+sh,_=>unreachable!()};assert!(slot<8);let x=r+32*z;let y=h+4*slot+32*nz;assert!(!assigned[x]&&!used[y],"sum chart collision carry={carry} x={x} y={y}");p[x]=y;assigned[x]=true;used[y]=true;
  }
 }
 for x in 0..64{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=p[y];}p[y]=x;assigned[y]=true;used[x]=true;}}
 let mut check=p.clone();check.sort_unstable();assert_eq!(check,(0..64).collect::<Vec<_>>());p
}
fn transposition(c:&mut Circuit,w:&[&QReg],guard:Option<&QReg>,d:&[QReg],x:usize,y:usize){
 let delta=x^y;let pivot=delta.trailing_zeros()as usize;let base=if x>>pivot&1==0{x}else{y};
 for i in 0..6{if i!=pivot&&delta>>i&1!=0{c.cx(w[pivot],w[i]);}}
 let mut cs:Vec<_>=guard.into_iter().map(|q|(q,true)).collect();cs.extend((0..6).filter(|&i|i!=pivot).map(|i|(w[i],base>>i&1!=0)));mixed_mcx(c,&cs,w[pivot],d);
 for i in (0..6).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(w[pivot],w[i]);}}
}
fn cycles(p:&[usize])->Vec<Vec<usize>>{
 let mut out=Vec::new();let mut seen=[false;64];for x in 0..64{if seen[x]{continue;}let mut cycle=Vec::new();let mut at=x;loop{assert!(!seen[at]);seen[at]=true;cycle.push(at);at=p[at];if at==x{break;}}out.push(cycle);}out
}
pub(super) fn emit(c:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],d:&[QReg]){
 let w:Vec<_>=rank.iter().chain(std::iter::once(&sm[0])).collect();let flag=&d[0];let rest=&d[1..];
 let p0=permutation(0);let p1=permutation(1);let mut inv0=[0;64];for x in 0..64{inv0[p0[x]]=x;}
 // Factor the COMPLETE pair, including its reversible off-domain extension:
 // first P0, then (P1 P0^-1) only when carry=1. The common P0 is paid once.
 for cycle in cycles(&p0){for &y in &cycle[1..]{transposition(c,&w,None,d,cycle[0],y);}}
 let delta:Vec<_>=(0..64).map(|y|p1[inv0[y]]).collect();let dc=cycles(&delta);
 // Two involutions implement the difference permutation. A dirty flag
 // controls each by an echo, and is restored before the next involution.
 for reflect in 0..2{
  let involution=|c:&mut Circuit|{for cycle in &dc{for i in 0..cycle.len(){let k=(reflect+cycle.len()-i)%cycle.len();if i<k{transposition(c,&w,Some(flag),rest,cycle[i],cycle[k]);}}}};
  involution(c);carry(c,a,cl,flag,rest,true);involution(c);carry(c,a,cl,flag,rest,true);
 }
}
pub(super) fn sh(code:usize)->usize{let h=code&3;let slot=code>>2;match h{0|1=>slot&3,2=>if slot<6{slot&1}else{2},3=>slot&1,_=>unreachable!()}}

/// Exhaust the physical chart and carry operands with arbitrary borrowed rails.
/// Separately validate the numeric interpretation on every admitted scalar tuple.
pub fn run(){
 use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let rank=c.alloc_qreg_bits("rank",5);let a=c.alloc_qreg_bits("Alo",6);let cl=c.alloc_qreg_bits("Mlo",6);let sm=c.alloc_qreg_bits("SM",4);let d=c.alloc_qreg_bits("borrowed",20);let n=c.b.next_qubit;
 emit(&mut c,&rank,&a,&cl,&sm,&d);assert_eq!(n,c.b.next_qubit);let ops=c.into_builder().ops;let maps=[permutation(0),permutation(1)];let mut lanes=0u64;
 for pattern in 0..2{for first in (0..1usize<<18).step_by(64){let mut seed=0x792501ca17u64^first as u64^((pattern as u64)<<40);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
  for lane in 0..64{let code=first+lane;let r=code&63;let av=code>>6&63;let cv=code>>12&63;let expected=maps[usize::from(av>cv)][r];
   for(w,rk)in[(&mut before,r),(&mut after,expected)]{for(i,q)in rank.iter().chain(std::iter::once(&sm[0])).enumerate(){let b=1u64<<lane;w[q.id()as usize]=(w[q.id()as usize]&!b)|(((rk>>i&1)as u64)<<lane);}for(qs,v)in[(&a,av),(&cl,cv)]{for(i,q)in qs.iter().enumerate(){let b=1u64<<lane;w[q.id()as usize]=(w[q.id()as usize]&!b)|(((v>>i&1)as u64)<<lane);}}}
  }
  let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"sumchart first={first} pattern={pattern}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
 }}
 let ts=super::q792_fold20_rank_r01::triples();let mut scalar=0;for av in 0..254{for cv in 0..254-av{for sv in 0..=256-av-cv{if sv>255{continue;}let r=ts.iter().position(|t|*t==[av>>6,cv>>6,sv>>6]).unwrap();let sum=av+cv;let sm=sv>>2&15;let out=maps[usize::from((av&63)>(sum&63))][r+32*(sm&1)];assert_eq!(out&3,sum>>6);assert_eq!(sh(out&31),sv>>6);let logical_sm0=(out>>5)^usize::from((out&31==26||out&31==30)&&(out>>5!=0));assert_eq!(logical_sm0,sm&1);scalar+=1;}}}
 eprintln!("FOLD20_SUMCHART_PASS lanes={lanes} scalar={scalar} ops={} T={} inverse=true dirty_restored=true extra_qubits=0",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
}
