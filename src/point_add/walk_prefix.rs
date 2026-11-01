//! Fixed-prime prefix checksum, reversible small-residue prototype.
use super::*;
#[path="prefix17_table.rs"] mod table;
use crate::circuit::{Op,OperationType};
pub(super) fn enabled()->bool{std::env::var_os("WALK_PREFIX").is_some()}
pub(super) const BOUND:u128=10742;
pub(super) const PREFIX_LOW_BITS:usize=7;
pub(super) const CHAIN_BOUND:u64=((BOUND*81+(1u128<<PREFIX_LOW_BITS)-1)>>PREFIX_LOW_BITS)as u64;

#[path="prefix31_arithmetic.rs"] mod arithmetic;
fn qrom(c:&mut Builder,input:&[QubitId],out:&[QubitId],tree:&[(u8,u16,u32,u32)],terms:&[(usize,u16)],ctrl:Option<QubitId>){
 fn value(c:&mut Builder,out:&[QubitId],v:u16,ctl:Option<QubitId>,second:Option<QubitId>){for(i,&q)in out.iter().enumerate(){if v>>i&1!=0{match(ctl,second){(None,None)=>c.x(q),(Some(a),None)|(None,Some(a))=>c.cx(a,q),(Some(a),Some(b))=>c.ccx(a,b,q)}}}}
 fn visit(c:&mut Builder,input:&[QubitId],out:&[QubitId],tree:&[(u8,u16,u32,u32)],terms:&[(usize,u16)],ix:usize,ctl:Option<QubitId>){
  let(kind,v,a,b)=tree[ix];match kind{
   0=>value(c,out,v,ctl,None),
   2=>{value(c,out,v,ctl,None);let ts=&terms[a as usize..b as usize];if let Some(q)=ctl{
    let mut basis=vec![0u16;out.len()];for&(_,mut z)in ts{for j in(0..out.len()).rev(){if z>>j&1!=0{if basis[j]==0{basis[j]=z;break;}z^=basis[j];}}}
    let mut forms=vec![Vec::new();out.len()];for&(i,mut z)in ts{for j in(0..out.len()).rev(){if z>>j&1!=0{forms[j].push(input[i]);z^=basis[j];}}assert_eq!(z,0);}
    for j in 0..out.len(){if basis[j]==0{continue;}let z=c.alloc_qubit();for&x in &forms[j]{c.cx(x,z);}for i in 0..out.len(){if i!=j&&basis[j]>>i&1!=0{c.cx(out[j],out[i]);}}c.ccx(q,z,out[j]);for i in 0..out.len(){if i!=j&&basis[j]>>i&1!=0{c.cx(out[j],out[i]);}}for&x in forms[j].iter().rev(){c.cx(x,z);}c.release_clean(z);}
   }else{for&(i,z)in ts{value(c,out,z,None,Some(input[i]));}}},
   1=>{let bit=input[v as usize];if let Some(parent)=ctl{let q=c.alloc_qubit();c.ccx(parent,bit,q);visit(c,input,out,tree,terms,b as usize,Some(q));c.cx(parent,q);visit(c,input,out,tree,terms,a as usize,Some(q));c.cx(parent,q);c.ccx(parent,bit,q);c.release_clean(q);}else{visit(c,input,out,tree,terms,b as usize,Some(bit));c.x(bit);visit(c,input,out,tree,terms,a as usize,Some(bit));c.x(bit);}},_=>unreachable!()
  }
 }
 visit(c,input,out,tree,terms,0,ctrl);
}
fn phase_qrom(c:&mut Builder,input:&[QubitId],ms:&[crate::circuit::BitId],tree:&[(u8,u16,u32,u32)],terms:&[(usize,u16)]){
 fn value(c:&mut Builder,ms:&[crate::circuit::BitId],v:u16,ctl:Option<QubitId>,second:Option<QubitId>){for(i,&m)in ms.iter().enumerate(){if v>>i&1!=0{match(ctl,second){(Some(a),Some(b))=>c.cz_if(a,b,m),(Some(a),None)|(None,Some(a))=>c.z_if(a,m),(None,None)=>{let q=c.alloc_qubit();c.x(q);c.z_if(q,m);c.x(q);c.release_clean(q);}}}}}
 fn visit(c:&mut Builder,input:&[QubitId],ms:&[crate::circuit::BitId],tree:&[(u8,u16,u32,u32)],terms:&[(usize,u16)],ix:usize,ctl:Option<QubitId>){let(kind,v,a,b)=tree[ix];match kind{
  0=>value(c,ms,v,ctl,None),2=>{value(c,ms,v,ctl,None);for&(i,z)in &terms[a as usize..b as usize]{value(c,ms,z,ctl,Some(input[i]));}},
  1=>{let bit=input[v as usize];if let Some(parent)=ctl{let q=c.alloc_qubit();c.ccx(parent,bit,q);visit(c,input,ms,tree,terms,b as usize,Some(q));c.cx(parent,q);visit(c,input,ms,tree,terms,a as usize,Some(q));c.cx(parent,q);c.ccx(parent,bit,q);c.release_clean(q);}else{visit(c,input,ms,tree,terms,b as usize,Some(bit));c.x(bit);visit(c,input,ms,tree,terms,a as usize,Some(bit));c.x(bit);}},_=>unreachable!()
 }}visit(c,input,ms,tree,terms,0,None);
}
fn measure_release(c:&mut Builder,qs:&[QubitId])->Vec<crate::circuit::BitId>{qs.iter().map(|&q|{let m=c.alloc_bit();c.hmr(q,m);c.release_clean(q);m}).collect()}
fn gray(c:&mut Builder,v:&[QubitId],inverse:bool){if inverse{for i in(0..v.len()-1).rev(){c.cx(v[i+1],v[i]);}}else{for i in 0..v.len()-1{c.cx(v[i+1],v[i]);}}}
pub(super) fn encode(c:&mut Builder,ctx:&[QubitId],raw:&[QubitId])->Vec<QubitId>{
 assert_eq!(ctx.len(),13);assert_eq!(raw.len(),8);let rank=c.alloc_qubits(5);gray(c,raw,false);let mut input=ctx.to_vec();input.extend(raw);
 qrom(c,&input,&rank,table::FORWARD_TREE,table::FORWARD_TREE_TERMS,None);let ms=measure_release(c,raw);input.truncate(13);input.extend(&rank);phase_qrom(c,&input,&ms,table::INVERSE_TREE,table::INVERSE_TREE_TERMS);c.free_bit_vec(&ms);gray(c,&rank,true);rank
}
pub(super) fn decode(c:&mut Builder,ctx:&[QubitId],rank:&[QubitId])->Vec<QubitId>{
 assert_eq!(ctx.len(),13);assert_eq!(rank.len(),5);let raw=c.alloc_qubits(8);gray(c,rank,false);let mut input=ctx.to_vec();input.extend(rank);
 qrom(c,&input,&raw,table::INVERSE_TREE,table::INVERSE_TREE_TERMS,None);let ms=measure_release(c,rank);input.truncate(13);input.extend(&raw);phase_qrom(c,&input,&ms,table::FORWARD_TREE,table::FORWARD_TREE_TERMS);c.free_bit_vec(&ms);gray(c,&raw,true);raw
}
fn unary(c:&mut Builder,r:&mut Vec<QubitId>,mode:u8,ctrl:Option<QubitId>){
 match mode{0=>arithmetic::neg(c,r,ctrl.expect("controlled residue negation")),1=>{assert!(ctrl.is_none());r.rotate_right(1);},2=>{assert!(ctrl.is_none());r.rotate_left(1);},_=>unreachable!()}
}
use arithmetic::residue;
pub(super) struct Frame{pub(super) a:Vec<QubitId>,pub(super) b:Vec<QubitId>,pub(super) rel:QubitId}
impl Frame{
 pub(super) fn context(&self,typ:QubitId,s:QubitId)->Vec<QubitId>{let mut v=self.a.clone();v.extend(&self.b);v.extend([self.rel,typ,s]);v}
}
pub(super) fn frame(c:&mut Builder,r:&Rails,typ:QubitId)->Frame{
 let mut a=c.alloc_qubits(5);let mut b=c.alloc_qubits(5);let rel=c.alloc_qubit();
 let sa=*r.r1.last().unwrap();let sb=*r.r2.last().unwrap();
 residue(c,&r.r1,None,&a,false);residue(c,&r.r2,Some(r.r1[0]),&b,false);
 unary(c,&mut a,0,Some(sa));unary(c,&mut b,0,Some(sb));
 c.cx(sa,rel);c.cx(sb,rel);for i in 0..5{fredkin(c,typ,a[i],b[i]);}Frame{a,b,rel}
}
pub(super) fn clear_frame(c:&mut Builder,r:&Rails,typ:QubitId,mut f:Frame){
 let sa=*r.r1.last().unwrap();let sb=*r.r2.last().unwrap();
 for i in(0..5).rev(){fredkin(c,typ,f.a[i],f.b[i]);}c.cx(sb,f.rel);c.cx(sa,f.rel);
 unary(c,&mut f.b,0,Some(sb));unary(c,&mut f.a,0,Some(sa));
 residue(c,&r.r2,Some(r.r1[0]),&f.b,true);residue(c,&r.r1,None,&f.a,true);
 for q in f.a.into_iter().chain(f.b).chain([f.rel]){c.release_clean(q);}
}
pub(super) fn back(c:&mut Builder,f:&mut Frame,typ:QubitId,s:QubitId){
 for i in 0..5{fredkin(c,typ,f.a[i],f.b[i]);}
 unary(c,&mut f.b,0,Some(s));
 arithmetic::add(c,&f.a,&f.b);unary(c,&mut f.a,1,None);
 for i in 0..5{fredkin(c,typ,f.a[i],f.b[i]);}
 c.cx(s,f.rel);
}
fn set(sim:&mut crate::sim::Simulator<'_,sha3::Shake256Reader>,q:&[QubitId],v:u64,lane:usize){for(i,&w)in q.iter().enumerate(){if v>>i&1!=0{*sim.qubit_mut(w)|=1u64<<lane;}}}
fn get(sim:&crate::sim::Simulator<'_,sha3::Shake256Reader>,q:&[QubitId],lane:usize)->u64{q.iter().enumerate().fold(0,|v,(i,&w)|v|(((sim.qubit(w)>>lane)&1)<<i))}
fn ccx(ops:&[Op])->usize{ops.iter().filter(|o|o.kind==OperationType::CCX).count()}
pub fn selftest(){
 arithmetic::selftest();
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};
 let mut h=Shake256::default();h.update(b"prefix-checksum-primitive-v1");let mut rng=h.finalize_xof();
 for w in [3usize,4,6,8,12]{
  let mut c=Builder::new();let r=Rails{r1:c.alloc_qubits(w),r2:c.alloc_qubits(w-1)};let typ=c.alloc_qubit();let start=c.op_count();let f=frame(&mut c,&r,typ);let cuts=(f.a.clone(),f.b.clone(),f.rel);let mid=c.op_count();clear_frame(&mut c,&r,typ,f);let(nq,nb)=c.i13_dims();let ops=c.take_ops();
  let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let mut cases=Vec::new();let bound=1i64<<(w-1);
  for sample in 0..4096i64{let a=if w<=6{sample%(2*bound)-bound}else{(sample*157+27)%(2*bound)-bound};let mut b=(sample/(2*bound)+sample*31+7)%(2*bound)-bound;if(a^b)&1==0{b^=1;}cases.push((a,b));}
  for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(a,b))in batch.iter().enumerate(){set(&mut sim,&r.r1,a as u64,lane);set(&mut sim,&r.r2,(b>>1)as u64,lane);set(&mut sim,&[typ],(a.abs()<b.abs())as u64,lane);}
   sim.apply_iter(ops[start..mid].iter());for(lane,&(a,b))in batch.iter().enumerate(){let(x,y)=if a.abs()<b.abs(){(b.abs(),a.abs())}else{(a.abs(),b.abs())};assert_eq!(get(&sim,&cuts.0,lane),(x%31)as u64,"a={a} b={b}");assert_eq!(get(&sim,&cuts.1,lane),(y%31)as u64);assert_eq!(get(&sim,&[cuts.2],lane),((a<0)^(b<0))as u64);}
   sim.apply_iter(ops[mid..].iter());let mask=u64::MAX;assert_eq!(sim.phase&mask,0);for(lane,&(a,b))in batch.iter().enumerate(){assert_eq!(get(&sim,&r.r1,lane),(a as u64)&((1u64<<w)-1));assert_eq!(get(&sim,&r.r2,lane),((b>>1)as u64)&((1u64<<(w-1))-1));}for q in 0..nq{let q=QubitId(q as u64);if !r.r1.contains(&q)&&!r.r2.contains(&q)&&q!=typ{assert_eq!(sim.qubit(q),0);}}
  }println!("PREFIX_RESIDUE PASS width={w} cases={} T={}",cases.len(),ccx(&ops[start..mid]));
 }
 let mut c=Builder::new();let mut f=Frame{a:c.alloc_qubits(5),b:c.alloc_qubits(5),rel:c.alloc_qubit()};let inputs=(f.a.clone(),f.b.clone(),f.rel);let typ=c.alloc_qubit();let s=c.alloc_qubit();let start=c.op_count();back(&mut c,&mut f,typ,s);let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let mut cases=Vec::new();for a in 0..31u64{for b in 0..31u64{for rel in 0..2{for d in 0..3{cases.push((a,b,rel,d));}}}}
 for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(a,b,r,d))in batch.iter().enumerate(){set(&mut sim,&inputs.0,a,lane);set(&mut sim,&inputs.1,b,lane);set(&mut sim,&[inputs.2],r,lane);set(&mut sim,&[typ],d&1,lane);set(&mut sim,&[s],d>>1,lane);}sim.apply_iter(ops[start..].iter());for(lane,&(a,b,r,d))in batch.iter().enumerate(){let(x,y)=if d==1{((a+b)%31,2*b%31)}else{(2*a%31,(a+if d==2{31-b}else{b})%31)};assert_eq!(get(&sim,&f.a,lane),x);assert_eq!(get(&sim,&f.b,lane),y);assert_eq!(get(&sim,&[f.rel],lane),r^(d>>1));}let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};assert_eq!(sim.phase&mask,0);}
 for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(a,b,r,d))in batch.iter().enumerate(){set(&mut sim,&inputs.0,a,lane);set(&mut sim,&inputs.1,b,lane);set(&mut sim,&[inputs.2],r,lane);set(&mut sim,&[typ],d&1,lane);set(&mut sim,&[s],d>>1,lane);}sim.apply_iter(ops[start..].iter());let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};for i in 0..nq{let q=QubitId(i as u64);if !f.a.contains(&q)&&!f.b.contains(&q)&&q!=f.rel&&q!=typ&&q!=s{assert_eq!(sim.qubit(q)&mask,0,"back scratch");}}for(lane,&(_,_,_,d))in batch.iter().enumerate(){assert_eq!(get(&sim,&[typ],lane),d&1);assert_eq!(get(&sim,&[s],lane),d>>1);}}
 println!("PREFIX_BACK PASS cases={} T={}",cases.len(),ccx(&ops[start..]));
}

fn forward(c:&mut Builder,f:&mut Frame,typ:QubitId,s:QubitId){
 c.cx(s,f.rel);for i in 0..5{fredkin(c,typ,f.a[i],f.b[i]);}unary(c,&mut f.a,2,None);
 let at=c.op_count();arithmetic::add(c,&f.a,&f.b);c.prefix_reverse(at);unary(c,&mut f.b,0,Some(s));for i in 0..5{fredkin(c,typ,f.a[i],f.b[i]);}
}
fn context(f:&Frame)->Vec<QubitId>{let mut v=f.a.clone();v.extend(&f.b);v.push(f.rel);v}
fn group(q:QubitId,state:GState)->Group{Group{state,synth:false,a2:q,a1:q,a0:q,h3:q,l3:q,b2:q,b1:q,b0:q,m_g:None}}
pub(super) fn compress(c:&mut Builder,w:&mut Walk){
 assert_eq!(w.tape.off,1);assert!(!w.tape.prefix_used);assert!(w.tape.shared[..3].iter().all(Option::is_none));
 let(typ,s)=w.tape.get(12);let mut f=frame(c,w.rails.as_ref().unwrap(),typ);back(c,&mut f,typ,s);for t in(1..=11).rev(){let(a,b)=w.tape.get(t);back(c,&mut f,a,b);}
 let mut rank=Vec::new();for t in 1..=11{let(a,b)=w.tape.raw[t].take().unwrap();forward(c,&mut f,a,b);trellis::push(c,&context(&f),&mut rank,t,[a,b]);}
 w.tape.groups[0]=Some(group(rank[0],GState::Prefix3));w.tape.groups[1]=Some(group(rank[0],GState::Prefix3));w.tape.groups[2]=Some(group(rank[0],GState::Prefix3));w.tape.prefix_rank=Some(rank);w.tape.prefix_live=true;w.tape.prefix_used=true;
 forward(c,&mut f,typ,s);clear_frame(c,w.rails.as_ref().unwrap(),typ,f);eprintln!("TRELLIS_COMPRESS live={} bound={BOUND}",c.active_qubits());
}
fn pop_one(c:&mut Builder,w:&mut Walk,f:&mut Frame,t:usize){
 assert!(w.tape.prefix_live);assert!(w.tape.raw[t].is_none());let mut rank=w.tape.prefix_rank.take().unwrap();let before=c.report_totals().map_or(0.,|x|x.1);let (d,peak)=c.r3_peak(|c|trellis::pop(c,&context(f),&mut rank,t));eprintln!("TRELLIS31_POP tick={t} peak={peak} T={}",c.report_totals().map_or(0.,|x|x.1)-before);w.tape.raw[t]=Some((d[0],d[1]));back(c,f,d[0],d[1]);
 if t==11{w.tape.groups[2]=None;}if t==6{w.tape.groups[1]=None;}if t==1{assert!(rank.is_empty());w.tape.groups[0]=None;w.tape.prefix_live=false;}else{w.tape.prefix_rank=Some(rank);}
 eprintln!("TRELLIS_POP t={t} live={}",c.active_qubits());
}
pub(super) fn before_reverse(c:&mut Builder,w:&mut Walk,t:usize){
 if t==1{if let Some(mut f)=w.prefix_frame.take(){assert!(!w.tape.prefix_live);w.tape.ensure_raw(c,1);let(a,b)=w.tape.get(1);forward(c,&mut f,a,b);clear_frame(c,w.rails.as_ref().unwrap(),a,f);}return;}
 if w.tape.prefix_live{let mut f=if let Some(f)=w.prefix_frame.take(){f}else{assert_eq!(t,12);w.tape.ensure_raw(c,12);let(a,b)=w.tape.get(12);let mut f=frame(c,w.rails.as_ref().unwrap(),a);back(c,&mut f,a,b);f};pop_one(c,w,&mut f,t-1);w.prefix_frame=Some(f);}
}
pub(super) fn head_step(c:&mut Builder,w:&mut Walk,t:usize,top:usize,typ:QubitId,s:QubitId){
 if t==top{assert!(w.prefix_frame.is_none());w.prefix_frame=Some(frame(c,w.rails.as_ref().unwrap(),typ));}
 let mut f=w.prefix_frame.take().unwrap();if t>=12{back(c,&mut f,typ,s);}if(2..=12).contains(&t){pop_one(c,w,&mut f,t-1);}w.prefix_frame=Some(f);
}
impl Tape{
 pub(super) fn prefix_pack5(&mut self,c:&mut Builder){
  assert_eq!(self.state(2),GState::Prefix3);let mut state=self.prefix_rank.take().unwrap();let mut bound=BOUND;for t in 12..=15{let(a,b)=self.raw[t].take().unwrap();chain_codec::dense_push(c,[a,b],&mut state,bound);bound*=3;}assert_eq!(bound,870102);self.groups[2]=Some(group(state[0],GState::Prefix5));self.prefix_rank=Some(state);
 }
 pub(super) fn prefix_chain_base(&mut self){
  assert_eq!(self.state(2),GState::Prefix5);assert!(self.chains[0].is_none());assert!(self.prefix_low.is_none());let mut state=self.prefix_rank.take().unwrap();assert_eq!(state.len(),20);let high=state.split_off(PREFIX_LOW_BITS);self.prefix_low=Some(state);for g in 0..3{self.groups[g]=Some(group(high[0],GState::ChainBase));}self.chains[0]=Some(chain_codec::Chain{base:0,top:2,state:high,bounds:vec![CHAIN_BOUND]});
 }
 pub(super) fn prefix_unbase(&mut self,c:&mut Builder,high:Vec<QubitId>){
  assert!(self.prefix_rank.is_none());assert_eq!(self.state(2),GState::ChainBase);let mut state=self.prefix_low.take().unwrap();assert_eq!(state.len(),PREFIX_LOW_BITS);state.extend(high);assert_eq!(state.len(),20);let mut bound=BOUND*27;for t in(12..=15).rev(){let d=chain_codec::dense_pop_digit(c,&mut state,bound);self.raw[t]=Some((d[0],d[1]));bound/=3;}for g in 0..3{self.groups[g]=Some(group(state[0],GState::Prefix3));}self.prefix_rank=Some(state);
 }
}
#[path="prefix_trellis.rs"] pub mod trellis;
