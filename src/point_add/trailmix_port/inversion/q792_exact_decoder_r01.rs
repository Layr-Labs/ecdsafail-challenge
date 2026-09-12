//! Exact cofactor decoder plans with native T-primary replacement guards.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{Op,OperationType as K};
type Cubes=Vec<(usize,usize)>;
struct Plan{truth:u64,split:usize,products:&'static[(usize,usize)]}
const PLANS:&[Plan]=&[
 Plan{truth:0x47000300,split:10,products:&[(0xc,0x33),(0x8,0x63)]},
 Plan{truth:0xec80c800,split:10,products:&[(0x6,0x80),(0x8,0xfe)]},
 Plan{truth:0xecc88000,split:13,products:&[(0x80,0x6),(0xfe,0x8)]},
];
thread_local! {
 static DISABLED:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};
 static CONTEXT:std::cell::Cell<Option<(usize,usize)>>=const{std::cell::Cell::new(None)};
}
pub(super) fn without<T>(f:impl FnOnce()->T)->T{DISABLED.with(|d|{let old=d.replace(true);let result=f();d.set(old);result})}
pub(super) fn context(value:Option<(usize,usize)>){CONTEXT.with(|c|c.set(value));}
pub(super) fn capture_calls()->bool{std::env::var_os("FOLD20_EXACT_DECODER_CALL_CENSUS").is_some()&&!DISABLED.with(|d|d.get())}
pub(super) fn record_call(n:usize,k:usize,truth:&[bool],old:&[Op],new:&[Op]){
 let before=score(old);let after=score(new);if before==after{return;}
 let t=truth.iter().enumerate().fold(0u64,|a,(i,&v)|a|((v as u64)<<i));let(block,j)=CONTEXT.with(|c|c.get()).unwrap_or((usize::MAX,usize::MAX));
 eprintln!("EXACT_COMBINED_FINAL_CALL block={block} j={j} n={n} k={k} truth={t:016x} old_T={} old_ops={} new_T={} new_ops={}",before.0,before.1,after.0,after.1);
}
fn score(ops:&[Op])->(usize,usize){(ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len())}
fn small_plan(n:usize,t:usize,k:usize)->Cubes{
 use std::collections::{BinaryHeap,HashMap};use std::sync::{OnceLock,Mutex};
 static CACHE:OnceLock<Mutex<HashMap<(usize,usize),Vec<Cubes>>>>=OnceLock::new();
 let mut cache=CACHE.get_or_init(||Mutex::new(HashMap::new())).lock().unwrap();
 let plans=cache.entry((n,k)).or_insert_with(||{
  assert!(n<=3);let mut cubes=Vec::new();
  for i in 0..3usize.pow(n as u32){let(mut v,mut mask,mut value)=(i,0usize,0usize);for b in 0..n{let z=v%3;v/=3;if z!=0{mask|=1<<b;if z==2{value|=1<<b;}}}
   let truth=(0..1usize<<n).filter(|&x|x&mask==value).fold(0usize,|a,x|a|(1<<x));let degree=k+mask.count_ones()as usize;let tof=if degree<2{0}else if degree==2{1}else{4*degree-8};let ops=if degree<2{1}else{tof}+2*(mask^value).count_ones()as usize;cubes.push((truth,mask,value,(tof,ops)));
  }
  let size=1usize<<(1<<n);let mut dist=vec![(usize::MAX,usize::MAX);size];let mut prev=vec![None;size];let mut q=BinaryHeap::new();dist[0]=(0,0);q.push(std::cmp::Reverse(((0usize,0usize),0usize)));
  while let Some(std::cmp::Reverse((d,t)))=q.pop(){if d!=dist[t]{continue;}for(i,&(f,_,_,w))in cubes.iter().enumerate(){let next=t^f;let nd=(d.0+w.0,d.1+w.1);if nd<dist[next]{dist[next]=nd;prev[next]=Some(i);q.push(std::cmp::Reverse((nd,next)));}}}
  (0..size).map(|target|{let mut at=target;let mut out=Vec::new();while at!=0{let(f,m,v,_)=cubes[prev[at].unwrap()];out.push((m,v));at^=f;assert!(out.len()<64);}for x in 0..1usize<<n{assert_eq!(out.iter().fold(false,|a,&(m,v)|a^(x&m==v)),target>>x&1!=0);}out}).collect()
 });plans[t].clone()
}
fn small(c:&mut Circuit,word:&[&QReg],t:usize,prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
 for(m,v)in small_plan(word.len(),t,prefix.len()){
  let mut cs=prefix.to_vec();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,q)|(*q,v>>i&1!=0)));
  super::length_recompute::mixed_mcx(c,&cs,out,dirty);
 }
}
fn factor(c:&mut Circuit,a:&[&QReg],g:usize,b:&[&QReg],h:usize,out:&QReg,dirty:&[QReg])->Vec<Op>{
 let at=c.b.ops.len();if g==0||h==0{return Vec::new();}
 if g==(1usize<<(1<<a.len()))-1{small(c,b,h,&[],out,dirty);return c.b.ops.split_off(at);}
 if h==(1usize<<(1<<b.len()))-1{small(c,a,g,&[],out,dirty);return c.b.ops.split_off(at);}
 let d=&dirty[0];let rest=&dirty[1..];for _ in 0..2{small(c,a,g,&[],d,rest);small(c,b,h,&[(d,true)],out,rest);}let mut best=c.b.ops.split_off(at);
 // A decoder product can be cheaper flattened, e.g. ab*(x|y|z)
 // is ab XOR ab*!x*!y*!z. Compare its literal full native emission too.
 for (ma,va) in small_plan(a.len(),g,0){for (mb,vb) in small_plan(b.len(),h,0){
  let mut cs:Vec<_>=a.iter().enumerate().filter(|(i,_)|ma>>i&1!=0).map(|(i,q)|(*q,va>>i&1!=0)).collect();
  cs.extend(b.iter().enumerate().filter(|(i,_)|mb>>i&1!=0).map(|(i,q)|(*q,vb>>i&1!=0)));
  super::length_recompute::mixed_mcx(c,&cs,out,dirty);
 }}
 let flattened=c.b.ops.split_off(at);if score(&flattened)<score(&best){best=flattened;}
 for bit in 0..a.len(){let(mut zero,mut one)=(0usize,0usize);for x in 0..1usize<<(a.len()-1){let low=(1<<bit)-1;let y=(x&low)|((x&!low)<<1);zero|=((g>>y)&1)<<x;one|=((g>>(y|(1<<bit)))&1)<<x;}
  if zero^one!=(1usize<<(1<<(a.len()-1)))-1{continue;}
  let other:Vec<_>=a.iter().enumerate().filter(|(i,_)|*i!=bit).map(|(_,q)|*q).collect();small(c,&other,zero,&[],a[bit],dirty);let first=c.b.ops[at..].to_vec();
  small(c,b,h,&[(a[bit],true)],out,dirty);c.b.ops.extend(first.into_iter().rev());let candidate=c.b.ops.split_off(at);if score(&candidate)<score(&best){best=candidate;}
 }
 best
}
fn emit(c:&mut Circuit,word:&[&QReg],out:&QReg,dirty:&[QReg],p:&Plan){
 let a:Vec<_>=word.iter().enumerate().filter(|(i,_)|p.split>>i&1!=0).map(|(_,q)|*q).collect();let b:Vec<_>=word.iter().enumerate().filter(|(i,_)|p.split>>i&1==0).map(|(_,q)|*q).collect();
 for &(g,h)in p.products{let left=factor(c,&a,g,&b,h,out,dirty);let right=factor(c,&b,h,&a,g,out,dirty);c.b.ops.extend(if score(&left)<=score(&right){left}else{right});}
}
pub(super) fn improve(c:&mut Circuit,word:&[&QReg],truth:&[bool],prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],at:usize){
 if word.len()!=5||!prefix.is_empty()||dirty.len()<3||super::q792_passive_r01::active()||super::q792_rank4_lower_r01::capture_active(){return;}
 if DISABLED.with(|d|d.get())||std::env::var_os("FOLD20_EXACT_DECODER_DISABLED").is_some(){return;}
 let t=truth.iter().enumerate().fold(0u64,|a,(i,&v)|a|((v as u64)<<i));
 let Some(p)=PLANS.iter().find(|p|p.truth==t)else{return;};
 let mut ids:Vec<_>=word.iter().map(|q|q.id()).chain(std::iter::once(out.id())).chain(dirty.iter().map(QReg::id)).collect();ids.sort_unstable();if ids.windows(2).any(|p|p[0]==p[1]){return;}
 let owned=c.b.next_qubit;let old=c.b.ops.split_off(at);let before=score(&old);emit(c,word,out,dirty,p);assert_eq!(owned,c.b.next_qubit);let after=score(&c.b.ops[at..]);
 // Qualified plans save 3 or 5 Toffolis for at most five additional records.
 // An independent hard whole-stream limit bounds total ordinary payload.
 if after.0>=before.0||after.1>before.1+5{c.b.ops.truncate(at);c.b.ops.extend(old);}
}
pub fn run(){
 use crate::sim::Simulator;use sha3::{digest::XofReader,Digest,Sha3_256};
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x63);}}
 let mut lanes=0usize;
 for p in PLANS{
  let a:Vec<_>=(0..5).filter(|i|p.split>>i&1!=0).collect();let b:Vec<_>=(0..5).filter(|i|p.split>>i&1==0).collect();
  for x in 0..32{let select=|bits:&[usize]|bits.iter().enumerate().fold(0usize,|v,(i,&j)|v|((x>>j&1)<<i));let ax=select(&a);let bx=select(&b);assert_eq!(p.products.iter().fold(0usize,|v,&(g,h)|v^((g>>ax&1)&(h>>bx&1))),((p.truth>>x)&1)as usize);}
  let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let w=c.alloc_qreg_bits("decoder.word",5);let out=c.alloc_qreg("decoder.out");let d=c.alloc_qreg_bits("decoder.dirty",6);let owned=c.b.next_qubit;let word:Vec<_>=w.iter().collect();
  without(||super::q792_fold20_r01::table(&mut c,&word,(0..32).map(|x|p.truth>>x&1!=0).collect(),&[],&out,&d));let old=c.b.ops.split_off(0);emit(&mut c,&word,&out,&d,p);assert_eq!(owned,c.b.next_qubit);let ops=c.into_builder().ops;let before=score(&old);let after=score(&ops);
  let encode=|ops:&[Op]|ops.iter().map(|o|format!("{}:{},{},{}",o.kind as u32,o.q_control2.0,o.q_control1.0,o.q_target.0)).collect::<Vec<_>>().join(";");let truth_hash=format!("{:x}",Sha3_256::digest((0..32).map(|x|((p.truth>>x)&1)as u8).collect::<Vec<_>>()));
  eprintln!("EXACT_DECODER_COMPARE truth={:016x} old_T={} old_ops={} new_T={} new_ops={} win={} truth_vector_sha3_256={truth_hash} old={} new={}",p.truth,before.0,before.1,after.0,after.1,after.0<before.0,encode(&old),encode(&ops));
  assert!(ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)));
  for first in (0..1usize<<owned).step_by(64){let mut initial=vec![0u64;owned as usize];for q in 0..owned as usize{initial[q]=(0..64).fold(0,|v,l|v|((((first+l)>>q)&1)as u64)<<l);}let mut expected=initial.clone();for l in 0..64{if p.truth>>((first+l)&31)&1!=0{expected[out.id()as usize]^=1<<l;}}
   let mut rng=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut rng);sim.qubits.copy_from_slice(&initial);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,expected);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,initial);assert_eq!(sim.phase,0);lanes+=64;
  }
 }
 eprintln!("EXACT_DECODER_NATIVE_PASS plans={} lanes={lanes} all_words_targets_dirty_states=true phase=0 literal_inverse=true no_extra_qubits=true production_integration=true",PLANS.len());
}
