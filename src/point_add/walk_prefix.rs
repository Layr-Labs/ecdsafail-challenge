//! Fixed-prime prefix checksum, reversible small-residue prototype.
use super::*;
#[path="prefix_table.rs"] mod table;
use crate::circuit::{Op,OperationType};
pub(super) fn enabled()->bool{std::env::var_os("WALK_PREFIX").is_some()}
pub(super) const BOUND:u128=table::PREFIX_BOUND;

fn qrom(c:&mut Builder,input:&[QubitId],out:&[QubitId],rows:&[(u16,u8)],order:&[usize]){
 fn visit(c:&mut Builder,input:&[QubitId],out:&[QubitId],rows:&[(u16,u8)],order:&[usize],depth:usize,ctl:Option<QubitId>){
  if rows.is_empty(){return;}
  let v=rows[0].1;
  if rows.iter().all(|r|r.1==v){for(i,&q)in out.iter().enumerate(){if(v>>i)&1!=0{if let Some(a)=ctl{c.cx(a,q);}else{c.x(q);}}}return;}
  let bit=input[order[depth]];
  let(lo,hi):(Vec<_>,Vec<_>)=rows.iter().copied().partition(|r|r.0>>order[depth]&1==0);
  if let Some(a)=ctl{
   let q=c.alloc_qubit();c.ccx(a,bit,q);
   visit(c,input,out,&hi,order,depth+1,Some(q));
   c.cx(a,q);visit(c,input,out,&lo,order,depth+1,Some(q));c.cx(a,q);
   c.ccx(a,bit,q);c.release_clean(q);
  }else{
   visit(c,input,out,&hi,order,depth+1,Some(bit));
   c.x(bit);visit(c,input,out,&lo,order,depth+1,Some(bit));c.x(bit);
  }
 }
 visit(c,input,out,rows,order,0,None);
}
pub(super) fn encode(c:&mut Builder,ctx:&[QubitId],raw:&[QubitId])->Vec<QubitId>{
 assert_eq!(ctx.len(),9);assert_eq!(raw.len(),6);
 let rank=c.alloc_qubits(4);let mut input=ctx.to_vec();input.extend(raw);
 qrom(c,&input,&rank,table::FORWARD,table::ORDER0);
 input.truncate(9);input.extend(&rank);qrom(c,&input,raw,table::INVERSE,table::ORDER1);
 for&q in raw{c.release_clean(q);}rank
}
pub(super) fn decode(c:&mut Builder,ctx:&[QubitId],rank:&[QubitId])->Vec<QubitId>{
 assert_eq!(ctx.len(),9);assert_eq!(rank.len(),4);
 let raw=c.alloc_qubits(6);let mut input=ctx.to_vec();input.extend(rank);
 qrom(c,&input,&raw,table::INVERSE,table::ORDER1);
 input.truncate(9);input.extend(&raw);qrom(c,&input,rank,table::FORWARD,table::ORDER0);
 for&q in rank{c.release_clean(q);}raw
}
// Three-bit canonical modulo7 permutations. The unused word7 is fixed.
fn perm(c:&mut Builder,r:&[QubitId],which:usize,ctrl:Option<QubitId>,inverse:bool){
 let gates=table::PERMS[which];
 let one=|c:&mut Builder,t:usize,m:u8|{
  let cs:Vec<_>=(0..3).filter(|i|m>>i&1!=0).map(|i|r[i]).collect();
  match(ctrl,cs.len()){
   (None,0)=>c.x(r[t]),(None,1)=>c.cx(cs[0],r[t]),(None,2)=>c.ccx(cs[0],cs[1],r[t]),
   (Some(q),0)=>c.cx(q,r[t]),(Some(q),1)=>c.ccx(q,cs[0],r[t]),
   (Some(q),2)=>{let z=c.alloc_qubit();c.ccx(cs[0],cs[1],z);c.ccx(q,z,r[t]);c.ccx(cs[0],cs[1],z);c.release_clean(z);},_=>unreachable!()
  }
 };
 if inverse{for&(t,m)in gates.iter().rev(){one(c,t,m);}}else{for&(t,m)in gates{one(c,t,m);}}
}
fn add_bit(c:&mut Builder,r:&[QubitId],power:usize,q:Option<QubitId>,inverse:bool){perm(c,r,power%3,q,inverse)}
fn residue(c:&mut Builder,word:&[QubitId],implicit:Option<QubitId>,out:&[QubitId],inverse:bool){
 // implicit=Some(p) means the omitted LSB is !p and word starts at bit1.
 let mut terms:Vec<(Option<QubitId>,usize,bool)>=Vec::new();let shift=usize::from(implicit.is_some());
 if let Some(p)=implicit{terms.push((None,0,false));terms.push((Some(p),0,true));}
 for(i,&q)in word.iter().enumerate(){terms.push((Some(q),i+shift,i+1==word.len()));}
 if inverse{for&(q,p,neg)in terms.iter().rev(){add_bit(c,out,p,q,!neg);}}
 else{for&(q,p,neg)in &terms{add_bit(c,out,p,q,neg);}}
}
pub(super) struct Frame{pub(super) a:Vec<QubitId>,pub(super) b:Vec<QubitId>,pub(super) rel:QubitId}
impl Frame{
 pub(super) fn context(&self,typ:QubitId,s:QubitId)->Vec<QubitId>{let mut v=self.a.clone();v.extend(&self.b);v.extend([self.rel,typ,s]);v}
}
pub(super) fn frame(c:&mut Builder,r:&Rails,typ:QubitId)->Frame{
 let a=c.alloc_qubits(3);let b=c.alloc_qubits(3);let rel=c.alloc_qubit();
 let sa=*r.r1.last().unwrap();let sb=*r.r2.last().unwrap();
 residue(c,&r.r1,None,&a,false);residue(c,&r.r2,Some(r.r1[0]),&b,false);
 perm(c,&a,6,Some(sa),false);perm(c,&b,6,Some(sb),false);
 c.cx(sa,rel);c.cx(sb,rel);for i in 0..3{fredkin(c,typ,a[i],b[i]);}Frame{a,b,rel}
}
pub(super) fn clear_frame(c:&mut Builder,r:&Rails,typ:QubitId,f:Frame){
 let sa=*r.r1.last().unwrap();let sb=*r.r2.last().unwrap();
 for i in(0..3).rev(){fredkin(c,typ,f.a[i],f.b[i]);}c.cx(sb,f.rel);c.cx(sa,f.rel);
 perm(c,&f.b,6,Some(sb),true);perm(c,&f.a,6,Some(sa),true);
 residue(c,&r.r2,Some(r.r1[0]),&f.b,true);residue(c,&r.r1,None,&f.a,true);
 for q in f.a.into_iter().chain(f.b).chain([f.rel]){c.release_clean(q);}
}
pub(super) fn back(c:&mut Builder,f:&mut Frame,typ:QubitId,s:QubitId){
 for i in 0..3{fredkin(c,typ,f.a[i],f.b[i]);}
 perm(c,&f.b,6,Some(s),false);
 for i in 0..3{add_bit(c,&f.b,i,Some(f.a[i]),false);}
 // Multiplication by2 is a cyclic rotation on canonical residues0..6.
 f.a.rotate_right(1);
 for i in 0..3{fredkin(c,typ,f.a[i],f.b[i]);}
 c.cx(s,f.rel);
}
fn set(sim:&mut crate::sim::Simulator<'_,sha3::Shake256Reader>,q:&[QubitId],v:u64,lane:usize){for(i,&w)in q.iter().enumerate(){if v>>i&1!=0{*sim.qubit_mut(w)|=1u64<<lane;}}}
fn get(sim:&crate::sim::Simulator<'_,sha3::Shake256Reader>,q:&[QubitId],lane:usize)->u64{q.iter().enumerate().fold(0,|v,(i,&w)|v|(((sim.qubit(w)>>lane)&1)<<i))}
fn ccx(ops:&[Op])->usize{ops.iter().filter(|o|o.kind==OperationType::CCX).count()}
pub fn selftest(){
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};
 let mut h=Shake256::default();h.update(b"prefix-checksum-primitive-v1");let mut rng=h.finalize_xof();
 let mut c=Builder::new();let ctx=c.alloc_qubits(9);let raw=c.alloc_qubits(6);let spectator=c.alloc_qubits(3);let start=c.op_count();
 let rank=encode(&mut c,&ctx,&raw);let mid=c.op_count();let restored=decode(&mut c,&ctx,&rank);let(nq,nb)=c.i13_dims();let ops=c.take_ops();
 let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);
 for batch in table::FORWARD.chunks(64){sim.clear_for_shot();for(lane,&(key,_))in batch.iter().enumerate(){set(&mut sim,&ctx,(key&511)as u64,lane);set(&mut sim,&raw,(key>>9)as u64,lane);set(&mut sim,&spectator,((lane*5+3)%8)as u64,lane);}
  sim.apply_iter(ops[start..mid].iter());for(lane,&(_,v))in batch.iter().enumerate(){assert_eq!(get(&sim,&rank,lane),v as u64);}
  sim.apply_iter(ops[mid..].iter());for(lane,&(key,_))in batch.iter().enumerate(){assert_eq!(get(&sim,&restored,lane),(key>>9)as u64);assert_eq!(get(&sim,&ctx,lane),(key&511)as u64);assert_eq!(get(&sim,&spectator,lane),((lane*5+3)%8)as u64);}
  let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&mask,0);
  for q in 0..nq{let q=QubitId(q as u64);if !ctx.contains(&q)&&!restored.contains(&q)&&!spectator.contains(&q){assert_eq!(sim.qubit(q)&mask,0);}}
 }
 println!("PREFIX_QROM PASS cases={} encode_T={} decode_T={} Q={nq}",table::FORWARD.len(),ccx(&ops[start..mid]),ccx(&ops[mid..]));
 for w in [3usize,4,6,8,12]{
  let mut c=Builder::new();let r=Rails{r1:c.alloc_qubits(w),r2:c.alloc_qubits(w-1)};let typ=c.alloc_qubit();let start=c.op_count();let f=frame(&mut c,&r,typ);let cuts=(f.a.clone(),f.b.clone(),f.rel);let mid=c.op_count();clear_frame(&mut c,&r,typ,f);let(nq,nb)=c.i13_dims();let ops=c.take_ops();
  let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let mut cases=Vec::new();let bound=1i64<<(w-1);
  for sample in 0..4096i64{let a=if w<=6{sample%(2*bound)-bound}else{(sample*157+27)%(2*bound)-bound};let mut b=(sample/(2*bound)+sample*31+7)%(2*bound)-bound;if(a^b)&1==0{b^=1;}cases.push((a,b));}
  for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(a,b))in batch.iter().enumerate(){set(&mut sim,&r.r1,a as u64,lane);set(&mut sim,&r.r2,(b>>1)as u64,lane);set(&mut sim,&[typ],(a.abs()<b.abs())as u64,lane);}
   sim.apply_iter(ops[start..mid].iter());for(lane,&(a,b))in batch.iter().enumerate(){let(x,y)=if a.abs()<b.abs(){(b.abs(),a.abs())}else{(a.abs(),b.abs())};assert_eq!(get(&sim,&cuts.0,lane),(x%7)as u64,"a={a} b={b}");assert_eq!(get(&sim,&cuts.1,lane),(y%7)as u64);assert_eq!(get(&sim,&[cuts.2],lane),((a<0)^(b<0))as u64);}
   sim.apply_iter(ops[mid..].iter());let mask=u64::MAX;assert_eq!(sim.phase&mask,0);for q in 0..nq{let q=QubitId(q as u64);if !r.r1.contains(&q)&&!r.r2.contains(&q)&&q!=typ{assert_eq!(sim.qubit(q),0);}}
  }println!("PREFIX_RESIDUE PASS width={w} cases={} T={}",cases.len(),ccx(&ops[start..mid]));
 }
 let mut c=Builder::new();let mut f=Frame{a:c.alloc_qubits(3),b:c.alloc_qubits(3),rel:c.alloc_qubit()};let inputs=(f.a.clone(),f.b.clone(),f.rel);let typ=c.alloc_qubit();let s=c.alloc_qubit();let start=c.op_count();back(&mut c,&mut f,typ,s);let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let mut cases=Vec::new();for a in 0..7u64{for b in 0..7u64{for rel in 0..2{for d in 0..3{cases.push((a,b,rel,d));}}}}
 for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(a,b,r,d))in batch.iter().enumerate(){set(&mut sim,&inputs.0,a,lane);set(&mut sim,&inputs.1,b,lane);set(&mut sim,&[inputs.2],r,lane);set(&mut sim,&[typ],d&1,lane);set(&mut sim,&[s],d>>1,lane);}sim.apply_iter(ops[start..].iter());for(lane,&(a,b,r,d))in batch.iter().enumerate(){let(x,y)=if d==1{((a+b)%7,2*b%7)}else{(2*a%7,(a+if d==2{7-b}else{b})%7)};assert_eq!(get(&sim,&f.a,lane),x);assert_eq!(get(&sim,&f.b,lane),y);assert_eq!(get(&sim,&[f.rel],lane),r^(d>>1));}let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&mask,0);}
 println!("PREFIX_BACK PASS cases={} T={}",cases.len(),ccx(&ops[start..]));
}

fn group(q:QubitId,state:GState)->Group{Group{state,synth:false,a2:q,a1:q,a0:q,h3:q,l3:q,b2:q,b1:q,b0:q,m_g:None}}
pub(super) fn compress(c:&mut Builder,w:&mut Walk){
 assert_eq!(w.tape.off,1);assert!(!w.tape.prefix_used);assert!(w.tape.shared[0].is_none());
 let(typ,s)=w.tape.get(4);let f=frame(c,w.rails.as_ref().unwrap(),typ);let ctx=f.context(typ,s);
 let mut raw=Vec::new();for t in 1..=3{let(a,b)=w.tape.raw[t].take().unwrap();raw.extend([a,b]);}
 let rank=encode(c,&ctx,&raw);w.tape.groups[0]=Some(group(rank[0],GState::Prefix3));w.tape.prefix_rank=Some(rank);w.tape.prefix_live=true;w.tape.prefix_used=true;
 clear_frame(c,w.rails.as_ref().unwrap(),typ,f);
 eprintln!("PREFIX_COMPRESS live={} bound={BOUND}",c.active_qubits());
}
fn expand(c:&mut Builder,w:&mut Walk,f:&Frame){
 assert!(w.tape.prefix_live);w.tape.ensure_raw(c,4);let(typ,s)=w.tape.get(4);let ctx=f.context(typ,s);
 let rank=w.tape.prefix_rank.take().unwrap();let raw=decode(c,&ctx,&rank);
 for t in 1..=3{w.tape.raw[t]=Some((raw[2*(t-1)],raw[2*(t-1)+1]));}
 w.tape.groups[0]=None;w.tape.prefix_live=false;
 eprintln!("PREFIX_EXPAND live={}",c.active_qubits());
}
pub(super) fn before_reverse(c:&mut Builder,w:&mut Walk){
 w.tape.ensure_raw(c,4);let(typ,_)=w.tape.get(4);
 if let Some(f)=w.prefix_frame.take(){assert!(!w.tape.prefix_live);clear_frame(c,w.rails.as_ref().unwrap(),typ,f);}
 else if w.tape.prefix_live{let f=frame(c,w.rails.as_ref().unwrap(),typ);expand(c,w,&f);clear_frame(c,w.rails.as_ref().unwrap(),typ,f);}
}
pub(super) fn head_step(c:&mut Builder,w:&mut Walk,t:usize,top:usize,typ:QubitId,s:QubitId){
 if t==top{assert!(w.prefix_frame.is_none());w.prefix_frame=Some(frame(c,w.rails.as_ref().unwrap(),typ));}
 if t>4{back(c,w.prefix_frame.as_mut().unwrap(),typ,s);}
 if t==4{let f=w.prefix_frame.take().unwrap();expand(c,w,&f);w.prefix_frame=Some(f);}
}
impl Tape{
 pub(super) fn prefix_pack5(&mut self,c:&mut Builder){
  assert_eq!(self.state(0),GState::Prefix3);let mut state=self.prefix_rank.take().unwrap();
  for(t,bound)in[(4,BOUND),(5,3*BOUND)]{let(a,b)=self.raw[t].take().unwrap();chain_codec::dense_push(c,[a,b],&mut state,bound);}
  self.groups[0]=Some(group(state[0],GState::Prefix5));self.prefix_rank=Some(state);
 }
 pub(super) fn prefix_chain_base(&mut self){
  assert_eq!(self.state(0),GState::Prefix5);assert!(self.chains[0].is_none());let state=self.prefix_rank.take().unwrap();
  self.groups[0]=Some(group(state[0],GState::ChainBase));self.chains[0]=Some(chain_codec::Chain{base:0,top:0,state,bounds:vec![108]});
 }
 pub(super) fn prefix_unbase(&mut self,c:&mut Builder,mut state:Vec<QubitId>){
  assert!(self.prefix_rank.is_none());for(t,bound)in[(5,3*BOUND),(4,BOUND)]{let d=chain_codec::dense_pop_digit(c,&mut state,bound);self.raw[t]=Some((d[0],d[1]));}
  self.groups[0]=Some(group(state[0],GState::Prefix3));self.prefix_rank=Some(state);
 }
}
