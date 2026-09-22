//! Prefix A-high chart valid on general T10: C>=2, S>=3, A+C+S<=256.
//! High sums below4 are unrestricted. At sum4 all low fields vanish, so
//! high-C and high-S must both be nonzero. Exactly26 ranks remain, with
//! A-high multiplicities13/8/4/1, fitting prefix buckets16/8/4/4.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn permutation()->[usize;32]{
 let ts=super::q792_fold20_rank_r01::triples();let mut p=std::array::from_fn(|i|i);let mut assigned=[false;32];let mut used=[false;32];let mut next=[0,16,24,28];let mut count=[0;4];
 for (i,t)in ts.iter().enumerate(){if t.iter().sum::<usize>()==4&&(t[1]==0||t[2]==0){continue;}let h=t[0];let to=next[h];next[h]+=1;count[h]+=1;p[i]=to;assigned[i]=true;assert!(!used[to]);used[to]=true;}
 assert_eq!(count,[13,8,4,1]);
 for x in 0..32{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=p[y];}p[y]=x;assigned[y]=true;used[x]=true;}}
 let mut sorted=p;sorted.sort_unstable();assert_eq!(sorted,std::array::from_fn(|i|i));p
}
pub(super) fn emit(c:&mut Circuit,rank:&[QReg],dirty:&[QReg]){
 assert_eq!(rank.len(),5);let p=permutation();let mut seen=[false;32];
 for root in 0..32{if seen[root]{continue;}seen[root]=true;let mut y=p[root];while y!=root{assert!(!seen[y]);seen[y]=true;let delta=root^y;let pivot=delta.trailing_zeros()as usize;let base=if root>>pivot&1==0{root}else{y};
  for i in 0..5{if i!=pivot&&delta>>i&1!=0{c.cx(&rank[pivot],&rank[i]);}}
  let cs:Vec<_>=(0..5).filter(|&i|i!=pivot).map(|i|(&rank[i],base>>i&1!=0)).collect();super::length_recompute::mixed_mcx(c,&cs,&rank[pivot],dirty);
  for i in (0..5).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(&rank[pivot],&rank[i]);}}y=p[y];
 }}
}
pub(super) fn prefix(rank:&[QReg],h:usize)->Vec<(&QReg,bool)>{match h{0=>vec![(&rank[4],false)],1=>vec![(&rank[4],true),(&rank[3],false)],2=>vec![(&rank[4],true),(&rank[3],true),(&rank[2],false)],3=>vec![(&rank[4],true),(&rank[3],true),(&rank[2],true)],_=>unreachable!()}}
pub fn run(){
 use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
 let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let rank=c.alloc_qreg_bits("rank",5);let d=c.alloc_qreg_bits("dirty",20);emit(&mut c,&rank,&d);let ops=c.into_builder().ops;let p=permutation();let mut lanes=0;
 for batch in 0..1024{let mut seed=0x792ac001u64^batch;let mut before:Vec<_>=(0..25).map(|_|{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed}).collect();for i in 0..5{before[i]=(0..64).fold(0,|v,l|v|(((l>>i)&1)as u64)<<l);}let mut f=Fixed;let mut sim=Simulator::new(25,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());for i in 0..5{let expected=(0..64).fold(0,|v,l|v|(((p[l&31]>>i)&1)as u64)<<l);assert_eq!(sim.qubits[i],expected);}assert_eq!(&sim.qubits[5..],&before[5..]);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;}
 let ts=super::q792_fold20_rank_r01::triples();let mut scalar=0usize;for a in 0..=251{for cc in 2..=253-a{for s in 3..=256-a-cc{let rk=ts.iter().position(|t|*t==[a>>6,cc>>6,s>>6]).unwrap();let code=p[rk];let high=if code<16{0}else if code<24{1}else if code<28{2}else{3};assert_eq!(high,a>>6);scalar+=1;}}}
 eprintln!("FOLD20_T10_A_CHART_PASS lanes={lanes} scalar={scalar} ops={} all32_permutation=true dirty_restored=true phase=0",ops.len());
}
