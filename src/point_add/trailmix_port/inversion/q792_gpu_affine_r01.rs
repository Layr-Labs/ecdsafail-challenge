//! Exact affine-coordinate ANF candidates found using two Intel Arc Pro B50.
//! GPU search is offline only; this emitter is deterministic ordinary NCT.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{Op,OperationType as K};
struct Plan{n:usize,k:usize,truth:u64,pol:usize,anf:u64,gates:&'static[u8]}
include!("q792_gpu_affine_plans_r01.rs");
fn truth(plan:&Plan){
 for x in 0..1usize<<plan.n{let mut y=x;for &g in plan.gates{y^=((y>>(g>>3))&1)<<(g&7);}y^=plan.pol;
  let got=(0..1usize<<plan.n).fold(false,|v,m|v^((plan.anf>>m&1!=0)&&(y&m==m)));assert_eq!(got,plan.truth>>x&1!=0,"affine truth");
 }
}
fn emit_anf(c:&mut Circuit,word:&[&QReg],prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],p:&Plan){
 for &g in p.gates{c.cx(word[(g>>3)as usize],word[(g&7)as usize]);}
 for(i,q)in word.iter().enumerate(){if p.pol>>i&1!=0{c.x(q);}}
 for &(q,v)in prefix{if !v{c.x(q);}}
 let prefix:Vec<_>=prefix.iter().map(|&(q,_)|(q,true)).collect();
 for m in 0..1usize<<p.n{if p.anf>>m&1==0{continue;}let mut cs=prefix.clone();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));super::length_recompute::mixed_mcx(c,&cs,out,dirty);}
 // The caller restores the mixed prefix frame separately (original values).
 for(i,q)in word.iter().enumerate().rev(){if p.pol>>i&1!=0{c.x(q);}}
 for &g in p.gates.iter().rev(){c.cx(word[(g>>3)as usize],word[(g&7)as usize]);}
}
fn scored(ops:&[Op])->(usize,usize){(ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len())}
pub(super) fn improve(c:&mut Circuit,word:&[&QReg],truths:&[bool],prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],at:usize){
 if !(4..=6).contains(&word.len())||super::q792_passive_r01::active()||super::q792_rank4_lower_r01::capture_active(){return;}
 let t=truths.iter().enumerate().fold(0u64,|t,(i,&b)|t|((b as u64)<<i));let key=(word.len(),prefix.len(),t);
 let Ok(i)=PLANS.binary_search_by_key(&key,|p|(p.n,p.k,p.truth))else{return;};let p=&PLANS[i];
 if dirty.len()<(p.n+p.k).saturating_sub(2){return;}
 let mut ids:Vec<_>=word.iter().map(|q|q.id()).chain(prefix.iter().map(|(q,_)|q.id())).chain(std::iter::once(out.id())).chain(dirty.iter().map(QReg::id)).collect();ids.sort_unstable();if ids.windows(2).any(|v|v[0]==v[1]){return;}
 static PROOF:std::sync::OnceLock<()>=std::sync::OnceLock::new();PROOF.get_or_init(||{for p in PLANS{truth(p);}});
 let old=c.b.ops.split_off(at);let before=scored(&old);let owned=c.b.next_qubit;emit(c,word,prefix,out,dirty,p);
 for &(q,v)in prefix.iter().rev(){if !v{c.x(q);}}
 assert_eq!(c.b.next_qubit,owned);let after=scored(&c.b.ops[at..]);
 if after.0>=before.0||after.1>before.1{c.b.ops.truncate(at);c.b.ops.extend(old);}
}
pub fn run(){
 use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x5b);}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 let mut lanes=0usize;let mut total_t=0usize;
 for p in PLANS{truth(p);let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;
  let w=c.alloc_qreg_bits("gpu.word",p.n);let pre=c.alloc_qreg_bits("gpu.prefix",p.k);let out=c.alloc_qreg("gpu.target");let dirty=c.alloc_qreg_bits("gpu.dirty",p.n+p.k+2);let owned=c.b.next_qubit;
  let word:Vec<_>=w.iter().collect();let prefix:Vec<_>=pre.iter().enumerate().map(|(i,q)|(q,i%3!=1)).collect();emit(&mut c,&word,&prefix,&out,&dirty,p);for &(q,v)in prefix.iter().rev(){if !v{c.x(q);}}assert_eq!(c.b.next_qubit,owned);let ops=c.into_builder().ops;total_t+=scored(&ops).0;
  assert!(ops.iter().all(|op|matches!(op.kind,K::X|K::CX|K::CCX)));
  for pattern in 0..p.k+3{for repetition in 0..2{let mut seed=0xb5079220260912u64^p.truth^(pattern as u64)^((repetition as u64)<<32);
   let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();for(i,q)in w.iter().enumerate(){before[q.id()as usize]=(0..64).fold(0u64,|v,l|v|((((l%(1<<p.n))>>i)&1)as u64)<<l);}
   for(i,&(q,v))in prefix.iter().enumerate(){before[q.id()as usize]=if pattern<=p.k{if v^(pattern==i+1){u64::MAX}else{0}}else{rnd(&mut seed)};}
   let mut after=before.clone();for l in 0..64{if p.truth>>(l%(1<<p.n))&1!=0&&prefix.iter().all(|&(q,v)|(before[q.id()as usize]>>l&1!=0)==v){after[out.id()as usize]^=1u64<<l;}}
   let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"gpu n={} k={} truth={:x} pattern={pattern}",p.n,p.k,p.truth);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
  }}
 }
 eprintln!("FOLD20_GPU_AFFINE_PASS plans={} lanes={lanes} aggregate_native_T={total_t} all_truths_exact=true arbitrary_dirty=true phase=0 inverse=true no_extra_qubits=true",PLANS.len());
}

// Recombine the fixed public affine frame with exact mixed-polarity cubes.
// Both arms have the same mixed-prefix frame left for the original caller.
fn emit_esop(c:&mut Circuit,word:&[&QReg],prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],p:&Plan){
 let transformed:Vec<bool>=(0..1usize<<p.n).map(|y|
  (0..1usize<<p.n).fold(false,|v,m|v^((p.anf>>m&1!=0)&&(y&m==m)))).collect();
 let mut cubes=super::q792_esop_r01::plan(p.n,&transformed,p.k).expect("admitted affine ESOP width");
 for &g in p.gates{c.cx(word[(g>>3)as usize],word[(g&7)as usize]);}
 for(i,q)in word.iter().enumerate(){if p.pol>>i&1!=0{c.x(q);}}
 for &(q,v)in prefix{if !v{c.x(q);}}
 let positive:Vec<_>=prefix.iter().map(|&(q,_)|(q,true)).collect();
 let mut frame=0usize;
 while !cubes.is_empty(){
  let pick=(0..cubes.len()).min_by_key(|&i|{let(m,v)=cubes[i];((frame^(m^v))&m).count_ones()}).unwrap();
  let(m,v)=cubes.remove(pick);let toggles=(frame^(m^v))&m;
  for(i,q)in word.iter().enumerate(){if toggles>>i&1!=0{c.x(q);}}frame^=toggles;
  let mut cs=positive.clone();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));
  super::length_recompute::mixed_mcx(c,&cs,out,dirty);
 }
 for(i,q)in word.iter().enumerate().rev(){if frame>>i&1!=0{c.x(q);}}
 for(i,q)in word.iter().enumerate().rev(){if p.pol>>i&1!=0{c.x(q);}}
 for &g in p.gates.iter().rev(){c.cx(word[(g>>3)as usize],word[(g&7)as usize]);}
}
fn emit(c:&mut Circuit,word:&[&QReg],prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],p:&Plan){
 let at=c.b.ops.len();let owned=c.b.next_qubit;
 emit_anf(c,word,prefix,out,dirty,p);let old=c.b.ops.split_off(at);let before=scored(&old);
 emit_esop(c,word,prefix,out,dirty,p);assert_eq!(c.b.next_qubit,owned);
 let after=scored(&c.b.ops[at..]);
 if after.0>=before.0||after.1>before.1{c.b.ops.truncate(at);c.b.ops.extend(old);}
}
