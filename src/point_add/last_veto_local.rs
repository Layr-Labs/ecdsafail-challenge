use crate::circuit::{Op,OperationType as K,NO_BIT};
use std::collections::{BTreeSet,HashMap};
fn var(v:usize,packet:usize)->u64{if v>=6{if packet>>(v-6)&1!=0{u64::MAX}else{0}}else{(0..64).fold(0,|m,b|m|(((b>>v)&1)as u64)<<b)}}
fn apply(ops:&[Op],q:&mut[u64],initial_bits:&HashMap<u64,u64>,drawvars:&[u64])->(u64,HashMap<u64,u64>){let mut bits=initial_bits.clone();let mut active=u64::MAX;let mut stack=vec![];let mut phase=0;let mut draw=0;for o in ops{if o.kind==K::PushCondition{stack.push(active);active&=*bits.get(&o.c_condition.0).unwrap();continue;}if o.kind==K::PopCondition{active=stack.pop().unwrap();continue;}let en=active&if o.c_condition==NO_BIT{u64::MAX}else{*bits.get(&o.c_condition.0).unwrap()};if o.kind==K::Hmr{let m=drawvars[draw];draw+=1;let t=o.q_target.0 as usize;phase^=q[t]&m&en;q[t]&=!en;let old=bits.get(&o.c_target.0).copied().unwrap_or(0);bits.insert(o.c_target.0,(old&!en)|(m&en));continue;}if en==0{continue;}let t=o.q_target.0 as usize;match o.kind{K::CCX=>q[t]^=q[o.q_control1.0 as usize]&q[o.q_control2.0 as usize]&en,K::CX=>q[t]^=q[o.q_control1.0 as usize]&en,K::X=>q[t]^=en,K::Z=>phase^=q[t]&en,K::CZ=>phase^=q[t]&q[o.q_control1.0 as usize]&en,K::Neg=>phase^=en,K::R=>q[t]&=!en,_=>panic!("local unexpected {:?}",o.kind)}}assert!(stack.is_empty());assert_eq!(draw,drawvars.len());(phase,bits)}
pub fn comparator(ops:&[Op],inputs:&BTreeSet<u64>){
 let produced:BTreeSet<_>=ops.iter().filter(|o|o.kind==K::Hmr).map(|o|o.c_target.0).collect();
 let external:BTreeSet<_>=ops.iter().filter(|o|o.c_condition!=NO_BIT&&!produced.contains(&o.c_condition.0)).map(|o|o.c_condition.0).collect();
 let draws=ops.iter().filter(|o|o.kind==K::Hmr).count();let ni=inputs.len();let n=ni+external.len()+draws;assert!(n<=22);
 let new:Vec<_>=ops.iter().filter(|o|matches!(o.kind,K::Hmr|K::PushCondition|K::PopCondition)).copied().collect();
 for o in &new{if o.kind==K::Hmr{assert!(!inputs.contains(&o.q_target.0),"measurement target overlaps a live comparator input");}}
 let mut q=vec![0;1234];let mut oldphase=0usize;
 for packet in 0..(1usize<<n.saturating_sub(6)){
  q.fill(0);for(j,&w)in inputs.iter().enumerate(){q[w as usize]=var(j,packet);}let init=q.clone();
  let bits:HashMap<_,_>=external.iter().enumerate().map(|(j,&b)|(b,var(ni+j,packet))).collect();
  let m:Vec<_>=(0..draws).map(|j|var(ni+external.len()+j,packet)).collect();
  let(p,b)=apply(ops,&mut q,&bits,&m);assert_eq!(q,init,"old comparator data/scratch identity");oldphase+=p.count_ones()as usize;
  let mut nq=init.clone();let(np,nb)=apply(&new,&mut nq,&bits,&m);assert_eq!(nq,init,"new zero-scratch measurement block data identity");assert_eq!(np,0,"new zero-scratch measurement block phase identity");assert_eq!(nb,b);
 }
 eprintln!("LAST_VETO comparator local PASS new data/phase/scratch/bit identity {} inputs/{} externalbits/{} MBU draws/{} total assignments; OLDphase_nonzero{oldphase} (baseline may rely on narrow-rail invariants/approximations)",ni,external.len(),draws,1usize<<n);
}
pub fn forward(old:&[Op],new:&[Op],g:u64,w:u64,out:u64,mode:bool){for packet in 0..1{let mut q=vec![0;1234];q[g as usize]=var(0,packet);q[w as usize]=var(1,packet);q[out as usize]=var(2,packet);let init=q.clone();let m=[var(3,packet)];let(p,_)=apply(old,&mut q,&HashMap::new(),&m);let mut expected=init.clone();expected[out as usize]^=init[g as usize]&!init[w as usize];assert_eq!(q,expected);assert_eq!(p,0);let mut nq=init.clone();let(p,_)=apply(new,&mut nq,&HashMap::new(),&m);expected=init.clone();if !mode{expected[out as usize]^=init[g as usize];}assert_eq!(nq,expected);assert_eq!(p,0);}eprintln!("LAST_VETO forward local PASS all16 g/w/dirty-out/MBU cases mode{mode}");}
pub fn reverse(old:&[Op],new:&[Op],a:u64,b:u64,w:u64,mode:bool){let mut q=vec![0;1234];q[a as usize]=var(0,0);q[b as usize]=var(1,0);q[w as usize]=var(2,0);let init=q.clone();let m=[var(3,0)];let(p,_)=apply(old,&mut q,&HashMap::new(),&m);assert_eq!(q,init);assert_eq!(p,init[a as usize]&init[b as usize]&!init[w as usize]);let(p,_)=apply(new,&mut q,&HashMap::new(),&m);assert_eq!(q,init);assert_eq!(p,if mode{0}else{init[a as usize]&init[b as usize]});eprintln!("LAST_VETO reverse local PASS all16 z2/eq/w/MBU cases mode{mode}");}
