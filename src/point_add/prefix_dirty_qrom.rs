//! Exact XOR lookup using an arbitrary borrowed array and a select/swap network.
use super::*;
#[path="lowroom_qrom.rs"] mod low;
thread_local!{static TEST_ROOM:std::cell::Cell<Option<usize>>=const{std::cell::Cell::new(None)};}
pub(super) fn test_room(room:Option<usize>){TEST_ROOM.with(|x|x.set(room));}
fn room(c:&Builder)->usize{let cap=super::super::super::super::super::walk_policy::physical_cap();let r=cap.saturating_sub(c.active_qubits()as usize);TEST_ROOM.with(|x|x.get().map_or(r,|q|r.min(q)))}
fn visit_cost(n:usize,r:usize)->usize{low::plan(n,r).0}
fn copy_cost(n:usize,w:usize,phase:bool,r:usize)->usize{let(t,j)=low::plan(n,r);t+if phase{0}else{((1usize<<n)-1)*w*if j==0{1}else{2}}}

fn eval(tree:&[(u8,u32,u32,u32)],terms:&[(usize,u32)],key:usize)->u32{
 let mut ix=0;loop{let(k,v,a,b)=tree[ix];match k{0=>return v,1=>ix=if key>>v&1==0{a}else{b}as usize,2=>{let mut z=v;for &(i,x) in &terms[a as usize..b as usize]{if key>>i&1!=0{z^=x;}}return z;},_=>unreachable!()}}
}
fn sparse_cost(tree:&[(u8,u32,u32,u32)],terms:&[(usize,u32)],ix:usize,root:bool,phase:bool)->usize{
 let(k,_,a,b)=tree[ix];match k{0=>0,1=>(if root{0}else{2})+sparse_cost(tree,terms,a as usize,false,phase)+sparse_cost(tree,terms,b as usize,false,phase),2=>{
  if root||phase{return 0;}let mut basis=[0u32;32];let mut rank=0;for &(_,mut x) in &terms[a as usize..b as usize]{for j in(0..32).rev(){if x>>j&1!=0{if basis[j]==0{basis[j]=x;rank+=1;break;}x^=basis[j];}}}rank
 },_=>unreachable!()}
}
fn visit(c:&mut Builder,input:&[QubitId],depth:usize,prefix:usize,ctl:Option<QubitId>,body:&mut impl FnMut(&mut Builder,usize,Option<QubitId>)){
 if depth==input.len(){body(c,prefix,ctl);return;}let bit=input[depth];if let Some(parent)=ctl{let q=c.alloc_qubit();c.ccx(parent,bit,q);visit(c,input,depth+1,prefix|(1<<depth),Some(q),body);c.cx(parent,q);visit(c,input,depth+1,prefix,Some(q),body);c.cx(parent,q);let m=c.alloc_bit();c.walk_and_marker(q,parent,bit,m);c.hmr(q,m);c.cz_if(parent,bit,m);c.free_bit(m);c.release_clean(q);}else{visit(c,input,depth+1,1<<depth,Some(bit),body);c.x(bit);visit(c,input,depth+1,0,Some(bit),body);c.x(bit);}
}
fn copy(c:&mut Builder,low:&[QubitId],pool:&[QubitId],w:usize,out:&[QubitId],phase:bool){
 let body=&mut |c:&mut Builder,j:usize,ctl:Option<QubitId>|{if j==0{return;}let q=ctl.unwrap();for bit in 0..w{if phase{c.cz(q,pool[j-1]);}else{c.ccx(q,pool[(j-1)*w+bit],out[bit]);}}};
 let mut blocked=pool.to_vec();blocked.extend(out);let r=room(c);low::visit(c,low,r,&blocked,body);
}
fn bulk(c:&mut Builder,high:&[QubitId],pool:&[QubitId],w:usize,k:usize,table:&[u32],out:&[QubitId],ms:Option<&[crate::circuit::BitId]>,base:Option<&[u32]>){
 let mut blocked=pool.to_vec();blocked.extend(out);let r=room(c);low::visit(c,high,r,&blocked,&mut |c,hi,ctl|{
  let first=table[hi<<k];if let Some(base)=base{let first=base[hi<<k];if let Some(ms)=ms{for (bit,&m) in ms.iter().enumerate(){if first>>bit&1!=0{if let Some(q)=ctl{c.z_if(q,m);}else{let q=c.alloc_qubit();c.x(q);c.z_if(q,m);c.x(q);c.release_clean(q);}}}}else{for bit in 0..w{if first>>bit&1!=0{if let Some(q)=ctl{c.cx(q,out[bit]);}else{c.x(out[bit]);}}}}}
  for j in 1..1usize<<k{let value=table[(hi<<k)|j]^first;if let Some(ms)=ms{for (bit,&m) in ms.iter().enumerate(){if value>>bit&1!=0{c.push_condition(m);if let Some(q)=ctl{c.cx(q,pool[j-1]);}else{c.x(pool[j-1]);}c.pop_condition();}}}else{for bit in 0..w{if value>>bit&1!=0{if let Some(q)=ctl{c.cx(q,pool[(j-1)*w+bit]);}else{c.x(pool[(j-1)*w+bit]);}}}}}
 });
}
pub(super) fn lookup(c:&mut Builder,input:&[QubitId],out:&[QubitId],ms:Option<&[crate::circuit::BitId]>,tree:&[(u8,u32,u32,u32)],terms:&[(usize,u32)])->bool{
 let mut indices=Vec::new();for &(kind,v,a,b)in tree{if kind==1{indices.push(v as usize);}if kind==2{indices.extend(terms[a as usize..b as usize].iter().map(|x|x.0));}}indices.sort_unstable();indices.dedup();let n=indices.len();if n<2{return false;}
 let inputs:Vec<_>=indices.iter().map(|&i|input[i]).collect();let table:Vec<_>=(0..1usize<<n).map(|x|{let key=indices.iter().enumerate().fold(0,|v,(j,&i)|v|(((x>>j)&1)<<i));eval(tree,terms,key)}).collect();let value_width=(32-table.iter().copied().max().unwrap().leading_zeros())as usize;if value_width==0{return false;}assert!(value_width<=if let Some(ms)=ms{ms.len()}else{out.len()});let phase=ms.is_some();let w=if phase{1}else{value_width};
 let pool:Vec<_>=c.walk_live().into_iter().filter(|q|!input.contains(q)&&!out.contains(q)).collect();let r=room(c);let best=(1..n).filter(|&k|((1usize<<k)-1)*w+2*n<=pool.len()).map(|k|(2*visit_cost(n-k,r)+2*copy_cost(k,w,phase,r),k)).min();let Some((cost,k))=best else{return false;};if room(c)>=n+1&&cost>=sparse_cost(tree,terms,0,true,phase){return false;}
 let pool=&pool[..((1usize<<k)-1)*w];copy(c,&inputs[..k],pool,w,out,phase);bulk(c,&inputs[k..],pool,w,k,&table,out,ms,Some(&table));copy(c,&inputs[..k],pool,w,out,phase);bulk(c,&inputs[k..],pool,w,k,&table,out,ms,None);true
}

// The borrowed array remains loaded only across arithmetic on excluded wires.
pub(super) struct Pair{inputs:Vec<QubitId>,pool:Vec<QubitId>,w:usize,k:usize,first:Vec<u32>,second:Vec<u32>}
pub(super) fn pair(c:&mut Builder,input:&[QubitId],out:&[QubitId],blocked:&[QubitId],f:(&[(u8,u32,u32,u32)],&[(usize,u32)]),g:(&[(u8,u32,u32,u32)],&[(usize,u32)]))->Option<Pair>{
 let mut indices=Vec::new();for(tree,terms)in[f,g]{for &(kind,v,a,b)in tree{if kind==1{indices.push(v as usize);}if kind==2{indices.extend(terms[a as usize..b as usize].iter().map(|x|x.0));}}}indices.sort_unstable();indices.dedup();let n=indices.len();if n<2{return None;}
 let inputs:Vec<_>=indices.iter().map(|&i|input[i]).collect();let values=|tree,terms|(0..1usize<<n).map(|x|{let key=indices.iter().enumerate().fold(0,|v,(j,&i)|v|(((x>>j)&1)<<i));eval(tree,terms,key)}).collect::<Vec<u32>>();let first=values(f.0,f.1);let second=values(g.0,g.1);let w=(32-first.iter().chain(&second).copied().max().unwrap().leading_zeros())as usize;if w==0{return None;}assert!(w<=out.len());
 let pool:Vec<_>=c.walk_live().into_iter().filter(|q|!input.contains(q)&&!out.contains(q)&&!blocked.contains(q)).collect();let r=room(c);let best=(1..n).filter(|&k|((1usize<<k)-1)*w+2*n<=pool.len()).map(|k|(3*visit_cost(n-k,r)+4*copy_cost(k,w,false,r),k)).min();let(cost,k)=best?;
 let independent=|tree:&[(u8,u32,u32,u32)],terms:&[(usize,u32)],v:&[u32]|{let bits=(32-v.iter().copied().max().unwrap().leading_zeros())as usize;if bits==0{return 0;}let dirty=(1..n).filter(|&k|((1usize<<k)-1)*bits+2*n<=pool.len()).map(|k|2*visit_cost(n-k,r)+2*copy_cost(k,bits,false,r)).min().unwrap_or(usize::MAX);if r>=n+1{dirty.min(sparse_cost(tree,terms,0,true,false))}else{dirty}};
 if cost>=independent(f.0,f.1,&first)+independent(g.0,g.1,&second){return None;}
 Some(Pair{inputs,pool:pool[..((1usize<<k)-1)*w].to_vec(),w,k,first,second})
}
impl Pair{
 pub(super) fn start(&self,c:&mut Builder,out:&[QubitId]){copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);bulk(c,&self.inputs[self.k..],&self.pool,self.w,self.k,&self.first,out,None,Some(&self.first));copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);}
 pub(super) fn finish(self,c:&mut Builder,out:&[QubitId]){let delta:Vec<_>=self.first.iter().zip(&self.second).map(|(a,b)|a^b).collect();bulk(c,&self.inputs[self.k..],&self.pool,self.w,self.k,&delta,out,None,Some(&self.second));copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);bulk(c,&self.inputs[self.k..],&self.pool,self.w,self.k,&self.second,out,None,None);copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);}
}

pub(super) fn selftest(){
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};let mut h=Shake256::default();h.update(b"bounded-clean-linear-qrom");let mut rng=h.finalize_xof();
 for n in 2..=10{for room in 0..=3{
  let mut c=Builder::new();let input=c.alloc_qubits(n);let out=c.alloc_qubits(7);let dirty=c.alloc_qubits(32);let start=c.op_count();let value=|key:usize|((key*1579+37)^(key*key+13)^(key>>3))&127;
  low::visit(&mut c,&input,room,&out,&mut |c,key,ctl|{for i in 0..7{if value(key)>>i&1!=0{if let Some(q)=ctl{c.cx(q,out[i]);}else{c.x(out[i]);}}}});
  let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);
  for base in(0..1usize<<n).step_by(64){sim.clear_for_shot();let count=64.min((1usize<<n)-base);for lane in 0..count{set(&mut sim,&input,(base+lane)as u64,lane);set(&mut sim,&out,(lane*19%128)as u64,lane);for(j,&q)in dirty.iter().enumerate(){set(&mut sim,&[q],((j*37+lane*13+(j^lane)*7)%17%2)as u64,lane);}}sim.apply_iter(ops[start..].iter());for lane in 0..count{assert_eq!(get(&sim,&input,lane),(base+lane)as u64);assert_eq!(get(&sim,&out,lane),((lane*19%128)^value(base+lane))as u64,"lookup n={n} room={room}");for(j,&q)in dirty.iter().enumerate(){assert_eq!(get(&sim,&[q],lane),((j*37+lane*13+(j^lane)*7)%17%2)as u64);}}let mask=if count==64{u64::MAX}else{(1u64<<count)-1};assert_eq!(sim.phase&mask,0);for i in 0..nq{let q=QubitId(i as u64);if !input.contains(&q)&&!out.contains(&q)&&!dirty.contains(&q){assert_eq!(sim.qubit(q)&mask,0);}}}
  assert!(nq<=n+7+32+room);println!("LOWROOM_QROM PASS n={n} room={room} T={} Q={nq}",ccx(&ops[start..]));
 }}
}

// A retained XOR cache supplies the final exact measurement correction.
pub(super) struct Cached{inputs:Vec<QubitId>,pool:Vec<QubitId>,w:usize,k:usize,table:Vec<u32>}
impl Pair{
 pub(super) fn finish_cached(self,c:&mut Builder,out:&[QubitId])->Cached{
  // v=F, pool=D xor Fdiff. First copy leaves F0 xor selected(D).
  copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);
  // second is G; H=F xor G is the required final threshold.
  bulk(c,&self.inputs[self.k..],&self.pool,self.w,self.k,&self.second,out,None,Some(&self.second));
  copy(c,&self.inputs[..self.k],&self.pool,self.w,out,false);
  let table=self.first.iter().zip(&self.second).map(|(a,b)|a^b).collect();
  Cached{inputs:self.inputs,pool:self.pool,w:self.w,k:self.k,table}
 }
}
impl Cached{
 fn phase_copy(&self,c:&mut Builder,ms:&[crate::circuit::BitId]){
  let r=room(c);low::visit(c,&self.inputs[..self.k],r,&self.pool,&mut |c,j,ctl|{
   if j==0{return;}let q=ctl.unwrap();for bit in 0..self.w{c.cz_if(q,self.pool[(j-1)*self.w+bit],ms[bit]);}
  });
 }
 pub(super) fn erase(self,c:&mut Builder,v:Vec<QubitId>){
  let ms=measure_release(c,&v);self.phase_copy(c,&ms);
  let r=room(c);low::visit(c,&self.inputs[self.k..],r,&self.pool,&mut |c,hi,ctl|{
   let first=self.table[hi<<self.k];
   for bit in 0..self.w{if first>>bit&1!=0{if let Some(q)=ctl{c.z_if(q,ms[bit]);}else{let q=c.alloc_qubit();c.x(q);c.z_if(q,ms[bit]);c.x(q);c.release_clean(q);}}}
   for j in 1..1usize<<self.k{let value=self.table[(hi<<self.k)|j]^first;for bit in 0..self.w{if value>>bit&1!=0{if let Some(q)=ctl{c.cx(q,self.pool[(j-1)*self.w+bit]);}else{c.x(self.pool[(j-1)*self.w+bit]);}}}}
  });
  self.phase_copy(c,&ms);c.free_bit_vec(&ms);
 }
}
