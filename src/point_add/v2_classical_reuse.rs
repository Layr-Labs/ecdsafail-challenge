//! Exact classical value lifetime allocation. ABI bits stay fixed.
//! Initial-zero epochs are cleared before the enclosing outermost PUSH,
//! guaranteeing an unconditional initialization for all shot branches.
use crate::circuit::{Op,OperationType as K,BitId};
use std::collections::{BTreeMap,BinaryHeap};
use std::cmp::Reverse;
const NONE:u32=u32::MAX;
#[derive(Debug)]struct Epoch{logical:u32,start:u32,end:u32,init:bool,physical:u32}
fn touch(b:u32,i:u32,full:bool,scope:u32,fixed:&[bool],cur:&mut[u32],ep:&mut Vec<Epoch>){
 if fixed[b as usize]{return;}
 if full||cur[b as usize]==NONE{let init=!full;let start=if init{scope}else{i};cur[b as usize]=ep.len() as u32;ep.push(Epoch{logical:b,start,end:i,init,physical:NONE});}
 else{ep[cur[b as usize] as usize].end=i;}
}
pub(crate)fn color(ops:Vec<Op>,cap:u32)->Vec<Op>{
 let nb=ops.iter().flat_map(|o|[o.c_target.0,o.c_condition.0]).filter(|&b|b!=u64::MAX).max().map_or(0,|b|b+1) as usize;
 let mut fixed=vec![false;nb];for o in &ops{if o.kind==K::AppendToRegister&&o.c_target.0!=u64::MAX{fixed[o.c_target.0 as usize]=true;}}
 let mut cur=vec![NONE;nb];let mut ep=Vec::new();let(mut depth,mut outer)=(0usize,0u32);
 for(i,o)in ops.iter().enumerate(){let i=i as u32;let scope=if depth==0{i}else{outer};
  if o.c_condition.0!=u64::MAX{touch(o.c_condition.0 as u32,i,false,scope,&fixed,&mut cur,&mut ep);}
  if o.c_target.0!=u64::MAX&&o.kind!=K::AppendToRegister{
   let full=depth==0&&o.c_condition.0==u64::MAX&&matches!(o.kind,K::Hmr|K::BitStore0|K::BitStore1);
   touch(o.c_target.0 as u32,i,full,scope,&fixed,&mut cur,&mut ep);
  }
  if o.kind==K::PushCondition{if depth==0{outer=i;}depth+=1;}else if o.kind==K::PopCondition{assert!(depth>0);depth-=1;}
 }assert_eq!(depth,0);
 let mut order:Vec<_>=(0..ep.len()).collect();order.sort_unstable_by_key(|&i|(ep[i].start,ep[i].end,i));
 let mut free:BinaryHeap<Reverse<u32>>=BinaryHeap::new();let mut active:BinaryHeap<Reverse<(u32,u32)>>=BinaryHeap::new();
 let mut next=fixed.iter().rposition(|&x|x).map_or(0,|i|i as u32+1);for b in 0..next{if !fixed[b as usize]{free.push(Reverse(b));}}
 let mut initializations:BTreeMap<u32,Vec<u32>>=BTreeMap::new();
 for id in order{let e=&mut ep[id];while active.peek().is_some_and(|x|x.0.0<e.start){let Reverse((_,p))=active.pop().unwrap();free.push(Reverse(p));}
  let physical=free.pop().map_or_else(||{let p=next;next+=1;p},|x|x.0);e.physical=physical;active.push(Reverse((e.end,physical)));if e.init{initializations.entry(e.start).or_default().push(physical);}
 }
 assert!(next<=cap,"classical allocator needs {next} bits, exceeds cap {cap}");
 let ninit:usize=initializations.values().map(Vec::len).sum();let mut out=Vec::with_capacity(ops.len()+ninit);cur.fill(NONE);let mut eid=0usize;depth=0;
 let remap=|b:u32,full:bool,cur:&mut[u32],eid:&mut usize|->u32{
  if fixed[b as usize]{return b;}if full||cur[b as usize]==NONE{assert_eq!(ep[*eid].logical,b);cur[b as usize]=*eid as u32;*eid+=1;}ep[cur[b as usize] as usize].physical
 };
 for(i,mut o)in ops.into_iter().enumerate(){
  if let Some(v)=initializations.remove(&(i as u32)){assert_eq!(depth,0,"initialization inside condition stack");for p in v{let mut z=Op::empty();z.kind=K::BitStore0;z.c_target=BitId(p as u64);out.push(z);}}
  let old_cc=o.c_condition.0;
  if old_cc!=u64::MAX{o.c_condition=BitId(remap(old_cc as u32,false,&mut cur,&mut eid) as u64);}
  if o.c_target.0!=u64::MAX&&o.kind!=K::AppendToRegister{let full=depth==0&&old_cc==u64::MAX&&matches!(o.kind,K::Hmr|K::BitStore0|K::BitStore1);o.c_target=BitId(remap(o.c_target.0 as u32,full,&mut cur,&mut eid) as u64);}
  if o.kind==K::PushCondition{depth+=1;}else if o.kind==K::PopCondition{depth-=1;}
  out.push(o);
 }
 assert_eq!(eid,ep.len());assert!(initializations.is_empty());
 eprintln!("classical_reuse old_bits={nb} new_bits={next} epochs={} initializations={ninit}",ep.len());out
}
