use crate::circuit::{Op,OperationType as K,QubitId,BitId,analyze_ops};use sha3::{Digest,Sha3_256};use std::collections::HashMap;
pub(super)const IDENTITY_NONCE:u64=261;
const LEASES:&[[u64;9]]=&[[5099308,5142443,1350,709,2,9,709,1243,745],[10879870,10980042,1428,584,2,1421,584,851,697]];
fn make(k:K,c2:u64,c1:u64,t:u64,ct:u64,cc:u64)->Op {
 let mut o=Op::empty();o.kind=k;o.q_control2=QubitId(c2);o.q_control1=QubitId(c1);o.q_target=QubitId(t);o.c_target=BitId(ct);o.c_condition=BitId(cc);o.validate();o
}
fn rewrite_ops(ops:Vec<Op>,leases:&[[u64;9]],nb:usize)->Vec<Op>{
 let no=u64::MAX;let starts:HashMap<_,_>=leases.iter().map(|s|(s[0]as usize,s)).collect();let ends:HashMap<_,_>=leases.iter().map(|s|(s[1]as usize,s)).collect();let mut rewritten=Vec::with_capacity(ops.len()+leases.len()*5);
 for(i,o)in ops.into_iter().enumerate(){if let Some(s)=starts.get(&i){let mut fill=o;fill.q_target=QubitId(s[2]);rewritten.push(fill);rewritten.push(make(K::CX,no,s[2],s[5],no,o.c_condition.0));}else if let Some(s)=ends.get(&i){
  if o.c_condition.0!=no{rewritten.push(make(K::PushCondition,no,no,no,no,o.c_condition.0));}
  rewritten.push(make(K::CX,no,s[2],s[8],no,no));rewritten.push(make(K::Hmr,no,no,s[2],nb as u64,no));rewritten.push(make(K::CZ,no,s[6],s[7],no,nb as u64));
  if o.c_condition.0!=no{rewritten.push(make(K::PopCondition,no,no,no,no,no));}
 }else{rewritten.push(o);}}
 rewritten
}

fn bind(ops:&[Op],count:usize,want:&str){assert_eq!(ops.len(),count);let mut h=Sha3_256::new();for o in ops{for v in[o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}assert_eq!(format!("{:x}",h.finalize()),want,"Complete canonical source binding");}
pub(super)fn run(ops:Vec<Op>)->Vec<Op>{
 bind(&ops,10995453,"d272df3f8bd9ca7d1e45dfcab6f87eca439ce3c36d2a0d24feae5092678e07cb");
 let(_,nb,_,_)=analyze_ops(ops.iter());let mut ops=rewrite_ops(ops,LEASES,nb as usize);
 bind(&ops,10995459,"9cd7196d0bbaedc5d5dfe19578f77920cb130d4f586da2f891d13d8d08dd45bf");
 let end=ops.len()-96;for(bit,pair)in ops[end..].chunks_exact(2).enumerate(){for o in pair{assert_eq!(o.kind,K::X);assert_eq!(o.q_target.0,(229u64>>bit)&1);}}ops.truncate(end);
 let mut ops=super::breakthrough_generic::run(ops);let(nq,_,_,_)=analyze_ops(ops.iter());assert!(nq<=1464);
 assert!(IDENTITY_NONCE<(1u64<<48));for bit in 0..48{let o=make(K::X,u64::MAX,u64::MAX,(IDENTITY_NONCE>>bit)&1,u64::MAX,u64::MAX);ops.extend([o,o]);}ops
}

#[cfg(test)]mod cache_tests{
use super::*;use crate::sim::Simulator;use sha3::digest::XofReader;
struct Fixed(u8);impl XofReader for Fixed{fn read(&mut self,out:&mut[u8]){out.fill(self.0);}}
#[test]fn complete_guarded_cache_preserves_phase_values_cleanup_cost_and_existing_width(){let n=u64::MAX;let mut caught=0;for inner in[false,true]{for mutate in[false,true]{let mut ops=vec![make(K::R,n,n,4,n,n),make(K::PushCondition,n,n,n,n,0)];let first=ops.len();ops.push(make(K::CCX,0,1,2,n,if inner{1}else{n}));if mutate{ops.push(make(K::BitInvert,n,n,n,0,n));}ops.extend([make(K::CX,n,0,1,n,n),make(K::X,n,n,1,n,n)]);let last=ops.len();ops.push(make(K::CCX,0,1,3,n,if inner{1}else{n}));ops.push(make(K::PopCondition,n,n,n,n,n));let f=ops[first];let l=ops[last];let lease=[first as u64,last as u64,4,f.q_control2.0,f.q_control1.0,f.q_target.0,l.q_control2.0,l.q_control1.0,l.q_target.0];let out=rewrite_ops(ops.clone(),&[lease],2);let faulty:Vec<_>=out.iter().filter(|o|o.kind!=K::CZ).copied().collect();assert!(out.iter().flat_map(|o|[o.q_control2.0,o.q_control1.0,o.q_target.0]).all(|q|q==n||q<5));for word in[0u8,255,0xa5,0x5a]{let mut ra=Fixed(word);let mut rb=Fixed(word);let mut rf=Fixed(word);let mut a=Simulator::new(5,3,&mut ra);let mut b=Simulator::new(5,3,&mut rb);let mut bad=Simulator::new(5,3,&mut rf);for lane in 0..64{for q in 0..4{a.qubits[q]|=((lane>>q&1)as u64)<<lane;}a.bits[0]|=((lane>>4&1)as u64)<<lane;a.bits[1]|=((lane>>5&1)as u64)<<lane;}b.qubits.clone_from(&a.qubits);bad.qubits.clone_from(&a.qubits);b.bits.clone_from(&a.bits);bad.bits.clone_from(&a.bits);let eff=a.bits[0]&if inner{a.bits[1]}else{u64::MAX};a.apply_iter(ops.iter());b.apply_iter(out.iter());bad.apply_iter(faulty.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.bits[..2],b.bits[..2]);assert_eq!(a.stats.toffoli_gates-b.stats.toffoli_gates,eff.count_ones()as u64);caught+=u64::from(a.phase!=bad.phase);}}}assert!(caught>0);}
}
