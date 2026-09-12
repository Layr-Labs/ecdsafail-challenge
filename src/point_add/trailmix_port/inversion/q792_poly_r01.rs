//! Exact data-polynomial resynthesis. Deterministic polarity descent on all
//! truth values; no EEA input, scalar trace, nonce, or test seed enters planning.
use crate::point_add::trailmix_port::circuit::QReg;
type Cubes=Vec<(usize,usize)>;
fn score(a:&[bool],pol:usize,k:usize)->usize{a.iter().enumerate().filter(|(_,on)|**on).map(|(m,_)|{let n=k+m.count_ones()as usize;(2*n).saturating_sub(3).max(1)+2*(m&pol).count_ones()as usize}).sum()}
fn flip(a:&mut[bool],bit:usize){for m in 0..a.len(){if m>>bit&1==0{a[m]^=a[m|(1<<bit)];}}}
pub(super) fn plan(truth:Vec<bool>,k:usize)->Cubes{
 use std::collections::HashMap;use std::sync::{Mutex,OnceLock};static CACHE:OnceLock<Mutex<HashMap<(Vec<bool>,usize),Cubes>>>=OnceLock::new();let mut cache=CACHE.get_or_init(||Mutex::new(HashMap::new())).lock().unwrap();if let Some(out)=cache.get(&(truth.clone(),k)){return out.clone();}
 let n=truth.len().trailing_zeros()as usize;assert!(truth.len().is_power_of_two()&&n<=12);let mut base=truth.clone();for bit in 0..n{for m in 0..base.len(){if m>>bit&1!=0{base[m]^=base[m^(1<<bit)];}}}let mut best=(score(&base,0,k),0usize,base.clone());
 let all=truth.len()-1;let alternating=all&0xaaa;for initial in [0,all,alternating,all^alternating]{let mut a=base.clone();for bit in 0..n{if initial>>bit&1!=0{flip(&mut a,bit);}}let mut pol=initial;for _ in 0..32{let old=score(&a,pol,k);let mut candidate=(old,usize::MAX);for bit in 0..n{flip(&mut a,bit);let cost=score(&a,pol^(1<<bit),k);flip(&mut a,bit);if cost<candidate.0{candidate=(cost,bit);}}if candidate.1==usize::MAX{break;}flip(&mut a,candidate.1);pol^=1<<candidate.1;}let cost=score(&a,pol,k);if cost<best.0{best=(cost,pol,a);}}
 let mut out:Cubes=best.2.iter().enumerate().filter_map(|(m,&on)|on.then_some((m,m&!best.1))).collect();
 if let Some(esop)=super::q792_esop_r01::plan(n,&truth,k){let cost=|p:&Cubes|p.iter().map(|&(m,v)|{let n=k+m.count_ones()as usize;(2*n).saturating_sub(3).max(1)+2*(m^v).count_ones()as usize}).sum::<usize>();if cost(&esop)<cost(&out){out=esop;}}
 for(x,&expected)in truth.iter().enumerate(){assert_eq!(out.iter().fold(false,|v,&(m,b)|v^(x&m==b)),expected,"data polynomial changed truth x={x}");}cache.insert((truth,k),out.clone());out
}
pub(super) fn terms<'a>(original:Vec<Vec<(&'a QReg,bool)>>,k:usize)->Vec<Vec<(&'a QReg,bool)>>{
 let mut wires:Vec<_>=original.iter().flatten().map(|(q,_)|*q).collect();wires.sort_by_key(|q|q.id());wires.dedup_by_key(|q|q.id());if wires.len()>12{return original;}let cubes:Vec<_>=original.iter().map(|cs|{let(mut m,mut v)=(0usize,0usize);for &(q,b)in cs{let i=wires.iter().position(|p|p.id()==q.id()).unwrap();m|=1<<i;if b{v|=1<<i;}}(m,v)}).collect();let truth=(0..1usize<<wires.len()).map(|x|cubes.iter().fold(false,|v,&(m,b)|v^(x&m==b))).collect();let p=plan(truth,k);let out:Vec<_>=p.into_iter().map(|(m,v)|wires.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,q)|(*q,v>>i&1!=0)).collect::<Vec<_>>()).collect();let cost=|p:&Vec<Vec<(&QReg,bool)>>|p.iter().map(|cs|(2*(k+cs.len())).saturating_sub(3).max(1)+2*cs.iter().filter(|(_,b)|!*b).count()).sum::<usize>();if cost(&out)<cost(&original){out}else{original}
}
