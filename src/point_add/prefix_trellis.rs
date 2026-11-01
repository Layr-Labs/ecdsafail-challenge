//! Exact finite-state path-rank kernel with sequential threshold workspace.
use super::*;
#[path="trellis_table.rs"] mod data;
pub(super) const fn bound()->u128{data::BOUNDS[data::STEPS]as u128}
pub(super) const fn steps()->usize{data::STEPS}
fn width(t:usize)->usize{(32-(data::BOUNDS[t]-1).leading_zeros())as usize}
fn work_width(t:usize)->usize{(32-data::BOUNDS[t].leading_zeros())as usize}
#[path="prefix_dirty_qrom.rs"] mod dirty;
fn threshold(c:&mut Builder,ctx:&[QubitId],v:&[QubitId],t:usize,j:usize){let(a,b)=data::table(t,j);if !dirty::lookup(c,ctx,v,None,a,b){qrom(c,ctx,v,a,b,None);}}
fn erase_threshold(c:&mut Builder,ctx:&[QubitId],v:Vec<QubitId>,t:usize,j:usize){let ms=measure_release(c,&v);let(a,b)=data::table(t,j);if !dirty::lookup(c,ctx,&[],Some(&ms),a,b){phase_qrom(c,ctx,&ms,a,b);}c.free_bit_vec(&ms);}
// Copy only the carry of y + ~x, then undo the carry ladder. Both operands
// are restored. Optional control touches only the two carry-output gates.
fn ge_controlled(c:&mut Builder,x:&[QubitId],y:&[QubitId],out:QubitId,control:Option<QubitId>){
 let n=x.len();assert_eq!(n,y.len());assert!(n>0);
 match control{Some(q)=>c.cx(q,out),None=>c.x(out)}
 c.x_all(x);
 for i in 1..n{c.cx(y[i],x[i]);}
 if n>1{match control{Some(q)=>c.ccx(q,y[n-1],out),None=>c.cx(y[n-1],out)}}
 for i in(1..n.saturating_sub(1)).rev(){c.cx(y[i],y[i+1]);}
 for i in 0..n-1{c.ccx(x[i],y[i],y[i+1]);}
 if let Some(q)=control{
  if n>1{let d=y[0];c.ccx(q,x[n-1],d);c.ccx(d,y[n-1],out);c.ccx(q,x[n-1],d);c.ccx(d,y[n-1],out);}
  else{let d=c.alloc_qubit();c.ccx(q,x[0],d);c.ccx(d,y[0],out);c.ccx(q,x[0],d);c.release_clean(d);}
 }else{c.ccx(x[n-1],y[n-1],out);}
 for i in(0..n-1).rev(){c.ccx(x[i],y[i],y[i+1]);}
 for i in 1..n.saturating_sub(1){c.cx(y[i],y[i+1]);}
 for i in(1..n).rev(){c.cx(y[i],x[i]);}c.x_all(x);
}
fn ge(c:&mut Builder,x:&[QubitId],y:&[QubitId],out:QubitId){ge_controlled(c,x,y,out,None);}
// Controlled TTK modulo-2^n addition. With q=0 the carry ladders and
// surrounding XORs cancel; with q=1 this is the ordinary TTK adder.
fn cadd(c:&mut Builder,a:&[QubitId],b:&[QubitId],q:QubitId,inverse:bool){
 let k=a.len();assert_eq!(k,b.len());if k==0{return;}let start=c.op_count();
 for i in 1..k{c.cx(a[i],b[i]);}for i in(1..k.saturating_sub(1)).rev(){c.cx(a[i],a[i+1]);}
 for i in 0..k-1{c.ccx(b[i],a[i],a[i+1]);}
 for i in(1..k).rev(){c.ccx(q,a[i],b[i]);c.ccx(b[i-1],a[i-1],a[i]);}
 for i in 1..k.saturating_sub(1){c.cx(a[i],a[i+1]);}
 c.ccx(q,a[0],b[0]);for i in 1..k{c.cx(a[i],b[i]);}
 if inverse{c.prefix_reverse(start);}
}
// Add a known offset, borrowing arbitrary live wires and restoring them.
fn bias(c:&mut Builder,v:&[QubitId],t:usize,j:usize,inverse:bool){
 let b=data::BIASES[t][j];if b==0{return;}let start=c.op_count();
 let dirty:Vec<_>=c.walk_live().into_iter().filter(|q|!v.contains(q)).take(v.len()).collect();assert_eq!(dirty.len(),v.len());
 for i in 0..v.len(){if b>>i&1!=0{super::super::super::super::lowroom::inc_dirty(c,&v[i..],&dirty);}}
 if inverse{c.prefix_reverse(start);}
}
// ctx is the post-letter checksum state; rank is its path rank.
pub(super) fn pop(c:&mut Builder,ctx:&[QubitId],rank:&mut Vec<QubitId>,t:usize)->[QubitId;2]{
 assert_eq!(rank.len(),width(t));while rank.len()<work_width(t){rank.push(c.alloc_qubit());}let typ=c.alloc_qubit();let s=c.alloc_qubit();let shift=data::SHIFTS[t];let v=c.alloc_qubits(work_width(t)-shift);
 let mut blocked=rank.clone();blocked.extend([typ,s]);let pair=dirty::pair(c,ctx,&v,&blocked,data::table(t,1),data::table(t,2));if let Some(ref p)=pair{p.start(c,&v);}else{threshold(c,ctx,&v,t,1);}bias(c,&v,t,1,false);ge(c,&rank[shift..],&v,s);cadd(c,&v,&rank[shift..],s,true);bias(c,&v,t,1,true);let cached=if let Some(p)=pair{Some(p.finish_cached(c,&v))}else{threshold(c,ctx,&v,t,2);None};
 bias(c,&v,t,0,false);c.x(s);ge_controlled(c,&rank[shift..],&v,typ,Some(s));c.x(s);cadd(c,&v,&rank[shift..],typ,true);bias(c,&v,t,0,true);if let Some(p)=cached{p.erase(c,v);}else{erase_threshold(c,ctx,v,t,0);}
 while rank.len()>width(t-1){c.release_clean(rank.pop().unwrap());}[typ,s]
}
pub(super) fn push(c:&mut Builder,ctx:&[QubitId],rank:&mut Vec<QubitId>,t:usize,d:[QubitId;2]){
 assert_eq!(rank.len(),width(t-1));while rank.len()<work_width(t){rank.push(c.alloc_qubit());}let[typ,s]=d;let shift=data::SHIFTS[t];let v=c.alloc_qubits(work_width(t)-shift);
 let mut blocked=rank.clone();blocked.extend([typ,s]);let pair=dirty::pair(c,ctx,&v,&blocked,data::table(t,0),data::table(t,2));if let Some(ref p)=pair{p.start(c,&v);}else{threshold(c,ctx,&v,t,0);}bias(c,&v,t,0,false);cadd(c,&v,&rank[shift..],typ,false);c.x(s);ge_controlled(c,&rank[shift..],&v,typ,Some(s));c.x(s);bias(c,&v,t,0,true);let cached=if let Some(p)=pair{Some(p.finish_cached(c,&v))}else{threshold(c,ctx,&v,t,2);None};
 bias(c,&v,t,1,false);cadd(c,&v,&rank[shift..],s,false);ge(c,&rank[shift..],&v,s);bias(c,&v,t,1,true);if let Some(p)=cached{p.erase(c,v);}else{erase_threshold(c,ctx,v,t,1);}c.release_clean(typ);c.release_clean(s);while rank.len()>width(t){c.release_clean(rank.pop().unwrap());}
}
pub fn selftest(){
 controlled_add_selftest();
 compare_selftest();
 global_compare_selftest();
 dirty::selftest();
 dirty::test_room(Some(3));
 frame_roundtrip();
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};let mut h=Shake256::default();h.update(b"exact-checksum-trellis");let mut rng=h.finalize_xof();
 for t in 1..=data::STEPS{let mut c=Builder::new();let ctx=c.alloc_qubits(13);let original=c.alloc_qubits(width(t));let mut rank=original.clone();let spectator=c.alloc_qubits(2);let borrowed=c.alloc_qubits(384);let start=c.op_count();let d=pop(&mut c,&ctx,&mut rank,t);let mid=c.op_count();push(&mut c,&ctx,&mut rank,t,d);let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let mut cases=Vec::new();
 for(i,&key)in data::KEYS.iter().enumerate(){let a=(key&63)as usize;let b=((key>>6)&63)as usize;let r=(key>>12)as usize;let ix=|a,b,r|(r*63+a)*63+b;let ps=[ix(2*a%63,(a+b)%63,r),ix((a+b)%63,2*b%63,r),ix(2*a%63,(a+63-b)%63,r^1)];let q=1u32<<data::SHIFTS[t];let mut offset=0u32;for (d,p)in ps.into_iter().enumerate(){let bound=data::COUNTS[t-1][p];let ys:Vec<u32>=if t<=6{(0..bound).collect()}else{let mut ys=Vec::new();if bound>0{ys.extend([0,bound-1]);if bound>1{ys.push(1);}for j in 0..12u32{ys.push(((key as u32).wrapping_mul(1579)+j*7039)%bound);}}ys.sort_unstable();ys.dedup();ys};for y in ys{cases.push((key as u64,(offset+y)as u64,d as u64,y as u64));}offset+=bound.div_ceil(q)*q;}assert_eq!(offset,data::COUNTS[t][i]);}

 for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(key,x,_,_))in batch.iter().enumerate(){set(&mut sim,&ctx,key,lane);set(&mut sim,&original,x,lane);set(&mut sim,&spectator,(lane%4)as u64,lane);for (j,&q) in borrowed.iter().enumerate(){set(&mut sim,&[q],((j*37+lane*13+(j^lane)*7)%17%2)as u64,lane);}}sim.apply_iter(ops[start..mid].iter());let mid_mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&mid_mask,0,"pop phase t={t}");for(lane,&(key,_,dd,y))in batch.iter().enumerate(){assert_eq!(get(&sim,&ctx,lane),key);for (j,&q) in borrowed.iter().enumerate(){assert_eq!(get(&sim,&[q],lane),((j*37+lane*13+(j^lane)*7)%17%2)as u64,"pop borrowed j={j}");}assert_eq!(get(&sim,&d,lane),dd,"t={t} ctx={key}");let old_w=width(t-1);assert_eq!(get(&sim,&original[..old_w],lane),y,"rank t={t}");}sim.apply_iter(ops[mid..].iter());for(lane,&(key,x,_,_))in batch.iter().enumerate(){assert_eq!(get(&sim,&ctx,lane),key);assert_eq!(get(&sim,&rank,lane),x);assert_eq!(get(&sim,&spectator,lane),(lane%4)as u64);for (j,&q) in borrowed.iter().enumerate(){assert_eq!(get(&sim,&[q],lane),((j*37+lane*13+(j^lane)*7)%17%2)as u64,"borrowed j={j}");}}let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&mask,0);for i in 0..nq{let q=QubitId(i as u64);if !ctx.contains(&q)&&!rank.contains(&q)&&!spectator.contains(&q)&&!borrowed.contains(&q){assert_eq!(sim.qubit(q)&mask,0,"scratch t={t}");}}}
 println!("TRELLIS_KERNEL PASS tick={t} cases={} popT={} pushT={} Q={nq}",cases.len(),ccx(&ops[start..mid]),ccx(&ops[mid..]));
 }
}

fn frame_roundtrip(){
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};let mut h=Shake256::default();h.update(b"frame-forward-backward");let mut rng=h.finalize_xof();let mut c=Builder::new();let mut f=Frame{a:c.alloc_qubits(6),b:c.alloc_qubits(6),rel:c.alloc_qubit()};let old=(f.a.clone(),f.b.clone(),f.rel);let d=c.alloc_qubits(2);let start=c.op_count();back(&mut c,&mut f,d[0],d[1]);forward(&mut c,&mut f,d[0],d[1]);let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let cases:Vec<_>=(0..63u64).flat_map(|a|(0..63u64).flat_map(move|b|(0..2u64).flat_map(move|r|(0..3u64).map(move|dd|(a,b,r,dd))))).collect();
 for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(a,b,r,dd))in batch.iter().enumerate(){set(&mut sim,&old.0,a,lane);set(&mut sim,&old.1,b,lane);set(&mut sim,&[old.2],r,lane);set(&mut sim,&d,dd,lane);}sim.apply_iter(ops[start..].iter());for(lane,&(a,b,r,dd))in batch.iter().enumerate(){assert_eq!(get(&sim,&f.a,lane),a);assert_eq!(get(&sim,&f.b,lane),b);assert_eq!(get(&sim,&[f.rel],lane),r);assert_eq!(get(&sim,&d,lane),dd);}let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&mask,0);for i in 0..nq{let q=QubitId(i as u64);if !f.a.contains(&q)&&!f.b.contains(&q)&&q!=f.rel&&!d.contains(&q){assert_eq!(sim.qubit(q)&mask,0);}}}
 println!("TRELLIS_FRAME_ROUNDTRIP PASS cases={} T={}",cases.len(),ccx(&ops[start..]));
}

fn controlled_add_selftest(){
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};let mut h=Shake256::default();h.update(b"controlled-ttk-modular-addition");let mut rng=h.finalize_xof();
 for n in [1usize,2,3,4,5,6,7,8,9,10,11,14,20]{let mut c=Builder::new();let a=c.alloc_qubits(n);let b=c.alloc_qubits(n);let q=c.alloc_qubit();let start=c.op_count();cadd(&mut c,&a,&b,q,false);let mid=c.op_count();cadd(&mut c,&a,&b,q,true);let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let bound=1u64<<n;let mask=bound-1;let mut cases=Vec::new();if n<=8{for av in 0..bound{for bv in 0..bound{for v in 0..2{cases.push((av,bv,v));}}}}else{for j in 0..4096u64{let av=(j*1579+37)&mask;for bv in [0,1,mask,mask-av,av,(j*7039+113)&mask]{for v in 0..2{cases.push((av,bv,v));}}}}
 for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(av,bv,v))in batch.iter().enumerate(){set(&mut sim,&a,av,lane);set(&mut sim,&b,bv,lane);set(&mut sim,&[q],v,lane);}sim.apply_iter(ops[start..mid].iter());for(lane,&(av,bv,v))in batch.iter().enumerate(){assert_eq!(get(&sim,&a,lane),av);assert_eq!(get(&sim,&b,lane),(bv+v*av)&mask,"controlled add n={n}");assert_eq!(get(&sim,&[q],lane),v);}sim.apply_iter(ops[mid..].iter());for(lane,&(av,bv,v))in batch.iter().enumerate(){assert_eq!(get(&sim,&a,lane),av);assert_eq!(get(&sim,&b,lane),bv);assert_eq!(get(&sim,&[q],lane),v);}let live=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&live,0);for i in 0..nq{let x=QubitId(i as u64);if !a.contains(&x)&&!b.contains(&x)&&x!=q{assert_eq!(sim.qubit(x)&live,0);}}}
 assert_eq!(ccx(&ops[start..mid]),3*n-2);println!("CONTROLLED_TTK PASS n={n} cases={} T={} Q={nq}",cases.len(),ccx(&ops[start..mid]));
 }
}

fn compare_selftest(){
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};let mut h=Shake256::default();h.update(b"carry-only-comparator");let mut rng=h.finalize_xof();
 for n in [1usize,2,3,4,5,6,7,8,9,11,14,19,20]{
  let mut c=Builder::new();let a=c.alloc_qubits(n);let b=c.alloc_qubits(n);let q=c.alloc_qubit();let o=c.alloc_qubit();let p=c.alloc_qubit();let start=c.op_count();ge(&mut c,&a,&b,o);ge_controlled(&mut c,&a,&b,p,Some(q));let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let bound=1u64<<n;let mask=bound-1;let mut cases=Vec::new();
  if n<=8{for av in 0..bound{for bv in 0..bound{for v in 0..4{cases.push((av,bv,v));}}}}else{for j in 0..4096u64{let av=(j*1579+37)&mask;for bv in[0,1,mask,av,av.wrapping_sub(1)&mask,(av+1)&mask,(j*7039+113)&mask]{for v in 0..4{cases.push((av,bv,v));}}}}
  for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(av,bv,v))in batch.iter().enumerate(){set(&mut sim,&a,av,lane);set(&mut sim,&b,bv,lane);set(&mut sim,&[q],v&1,lane);set(&mut sim,&[o,p],if v&2!=0{3}else{0},lane);}sim.apply_iter(ops[start..].iter());for(lane,&(av,bv,v))in batch.iter().enumerate(){assert_eq!(get(&sim,&a,lane),av);assert_eq!(get(&sim,&b,lane),bv);assert_eq!(get(&sim,&[q],lane),v&1);assert_eq!(get(&sim,&[o],lane),(v>>1)^((av>=bv)as u64),"ge n={n}");assert_eq!(get(&sim,&[p],lane),(v>>1)^((v&1)&((av>=bv)as u64)),"cge n={n}");}let live=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&live,0);for i in 0..nq{let w=QubitId(i as u64);if !a.contains(&w)&&!b.contains(&w)&&![q,o,p].contains(&w){assert_eq!(sim.qubit(w)&live,0);}}}
  println!("CARRY_COMPARE PASS n={n} cases={} T={} Q={nq}",cases.len(),ccx(&ops[start..]));
 }
}

fn global_compare_selftest(){
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};let mut h=Shake256::default();h.update(b"carry-only-comparator");let mut rng=h.finalize_xof();
 for n in [1usize,2,3,4,5,6,7,8,9,11,14,19,20,31,32,33]{
  let mut c=Builder::new();let a=c.alloc_qubits(n);let b=c.alloc_qubits(n);let q=c.alloc_qubit();let o=c.alloc_qubit();let p=c.alloc_qubit();let start=c.op_count();crate::point_add::width_composition::xor_lt_seed(&mut c,&a,&b,None,o);crate::point_add::width_composition::xor_lt_seed(&mut c,&a,&b,Some(q),p);let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let bound=1u64<<n;let mask=bound-1;let mut cases=Vec::new();
  if n<=8{for av in 0..bound{for bv in 0..bound{for v in 0..4{cases.push((av,bv,v));}}}}else{for j in 0..4096u64{let av=(j*1579+37)&mask;for bv in[0,1,mask,av,av.wrapping_sub(1)&mask,(av+1)&mask,(j*7039+113)&mask]{for v in 0..4{cases.push((av,bv,v));}}}}
  for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(av,bv,v))in batch.iter().enumerate(){set(&mut sim,&a,av,lane);set(&mut sim,&b,bv,lane);set(&mut sim,&[q],v&1,lane);set(&mut sim,&[o,p],if v&2!=0{3}else{0},lane);}sim.apply_iter(ops[start..].iter());for(lane,&(av,bv,v))in batch.iter().enumerate(){assert_eq!(get(&sim,&a,lane),av);assert_eq!(get(&sim,&b,lane),bv);assert_eq!(get(&sim,&[q],lane),v&1);assert_eq!(get(&sim,&[o],lane),(v>>1)^((av<bv)as u64),"ge n={n}");assert_eq!(get(&sim,&[p],lane),(v>>1)^((av<bv+(v&1))as u64),"cge n={n}");}let live=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&live,0);for i in 0..nq{let w=QubitId(i as u64);if !a.contains(&w)&&!b.contains(&w)&&![q,o,p].contains(&w){assert_eq!(sim.qubit(w)&live,0);}}}
  println!("GLOBAL_CARRY_COMPARE PASS n={n} cases={} T={} Q={nq}",cases.len(),ccx(&ops[start..]));
 }
}
