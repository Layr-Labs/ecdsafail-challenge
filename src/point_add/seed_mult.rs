use super::builder::Builder;
use crate::circuit::{QubitId,analyze_ops};
use crate::sim::Simulator;
use ruint::aliases::{U256,U512};
use sha3::digest::{ExtendableOutput,Update,XofReader};
#[derive(Clone,Copy)] enum G{X(QubitId),C(QubitId,QubitId),T(QubitId,QubitId,QubitId)}
#[derive(Clone,Copy)] enum S{Q(QubitId),One}
fn emit(c:&mut Builder,ops:&mut Vec<G>,g:G){match g{G::X(t)=>c.x(t),G::C(a,t)=>c.cx(a,t),G::T(a,b,t)=>c.ccx(a,b,t)}ops.push(g);}
fn xor(c:&mut Builder,ops:&mut Vec<G>,ss:&[S],t:QubitId){for s in ss{emit(c,ops,match*s{S::Q(a)=>G::C(a,t),S::One=>G::X(t)});}}
fn product(c:&mut Builder,ops:&mut Vec<G>,a:&[S],b:&[S],t:QubitId,qa:QubitId,qb:QubitId){xor(c,ops,a,qa);xor(c,ops,b,qb);emit(c,ops,G::T(qa,qb,t));xor(c,ops,b,qb);xor(c,ops,a,qa);}
fn erase_t(c:&mut Builder,t:QubitId,s0:QubitId,s1:QubitId){let m=c.alloc_bit();c.hmr(t,m);c.push_condition(m);c.cz(s0,s1);c.pop_condition();c.free_bit(m);}
struct Plan{out:Vec<QubitId>,body:Vec<G>,t:QubitId,w:QubitId,qa:QubitId,qb:QubitId}
fn construct(c:&mut Builder,b:&[QubitId],s0:QubitId,s1:QubitId)->Plan{
 let n=b.len();let t=c.alloc_qubit();c.ccx(s0,s1,t);let qa=c.alloc_qubit();let qb=c.alloc_qubit();let mut w=c.alloc_qubit();let mut ops=Vec::new();let mut out=vec![c.alloc_qubit()];emit(c,&mut ops,G::X(out[0]));emit(c,&mut ops,G::C(s0,w));let sign=*b.last().unwrap();
 for i in 1..n+2{let x=S::Q(if i<n{b[i]}else{sign});let h1=S::Q(if i-1<n{b[i-1]}else{sign});let h2=if i==1{None}else{Some(S::Q(if i-2<n{b[i-2]}else{sign}))};
  if i&1==1{let nw=c.alloc_qubit();let mut a=vec![S::Q(w),S::Q(s0),S::Q(s1)];let mut bb=vec![x,S::Q(s0),S::Q(t)];if let Some(h)=h2{a.push(h);bb.push(h);}product(c,&mut ops,&a,&bb,nw,qa,qb);let mut yy=vec![x];if let Some(h)=h2{yy.push(h);}xor(c,&mut ops,&yy,w);let mut z=vec![S::Q(s0)];if let Some(h)=h2{z.push(h);}xor(c,&mut ops,&z,nw);out.push(w);w=nw;
  }else{let y=c.alloc_qubit();let mut hh=vec![h1];if let Some(h)=h2{hh.push(h);}product(c,&mut ops,&[S::Q(s1)],&hh,y,qa,qb);let mut yy=vec![x,S::Q(w)];if let Some(h)=h2{yy.push(h);}xor(c,&mut ops,&yy,y);let a=vec![S::Q(y),x,S::Q(s0)];let mut bb=vec![x,S::Q(s0),S::Q(t)];if let Some(h)=h2{bb.push(h);}product(c,&mut ops,&a,&bb,w,qa,qb);xor(c,&mut ops,&[S::Q(s0),S::Q(y),x],w);out.push(y);}
 }
 xor(c,&mut ops,&[S::Q(sign),S::Q(t)],w);let top=c.alloc_qubit();xor(c,&mut ops,&[S::Q(sign),S::Q(t)],top);out.push(top);assert_eq!(out.len(),n+3);erase_t(c,t,s0,s1);c.release_clean(t);c.release_clean(w);c.release_clean(qa);c.release_clean(qb);Plan{out,body:ops,t,w,qa,qb}
}
fn undo(c:&mut Builder,p:&Plan,s0:QubitId,s1:QubitId){for q in[p.t,p.w,p.qa,p.qb]{c.reacquire(q);}c.ccx(s0,s1,p.t);for g in p.body.iter().rev(){match*g{G::X(t)=>c.x(t),G::C(a,t)=>c.cx(a,t),G::T(a,b,t)=>c.ccx(a,b,t)}}erase_t(c,p.t,s0,s1);for q in[p.t,p.w,p.qa,p.qb]{c.release_clean(q);}}
fn bit(v:U512,i:usize)->bool{((v>>i)&U512::from(1))!=U512::ZERO}
fn put<R:XofReader>(s:&mut Simulator<R>,r:&[QubitId],v:U512,l:usize){for(i,&q)in r.iter().enumerate(){if bit(v,i){*s.qubit_mut(q)|=1u64<<l;}}}
fn check<R:XofReader>(s:&Simulator<R>,r:&[QubitId],v:U512,l:usize)->bool{r.iter().enumerate().all(|(i,&q)|((s.qubit(q)>>l)&1)==bit(v,i)as u64)}
fn rand(st:&mut u64)->U512{let mut x=U512::ZERO;for j in 0..4{*st^=*st<<13;*st^=*st>>7;*st^=*st<<17;x|=U512::from(*st)<<(64*j);}x}
pub(super)fn run(){for n in[5usize,9,65,129,257]{let mut c=Builder::new();let b=c.alloc_qubits(n);let s0=c.alloc_qubit();let s1=c.alloc_qubit();let _idle=c.alloc_qubits(256);let p=construct(&mut c,&b,s0,s1);let split=c.op_count();let bt=c.report_totals().unwrap().1;let peak=c.take_win_peak();undo(&mut c,&p,s0,s1);let it=c.report_totals().unwrap().1-bt;let ops=c.take_ops();let(nq,nb,_,_)=analyze_ops(ops.iter());let mask=(U512::from(1)<<n)-U512::from(1);let outmask=(U512::from(1)<<(n+3))-U512::from(1);let mut cases=Vec::new();let mut st=0x5a173u64;
 if n<10{for v in(1usize..1usize<<n).step_by(2){for sb in 0..4{cases.push((U512::from(v),sb));}}}else{for i in 0..4096{let mut v=rand(&mut st)&mask;if n==257&&i&4!=0{v|=U512::from(1)<<256;}v|=U512::from(1);cases.push((v,i&3));}}
 let(mut db,mut ph,mut ib,mut dirty,mut fdirty,mut shots,mut total)=(0usize,0usize,0usize,0usize,0usize,0usize,0u64);let mut first=String::new();
 for seed in[61091u64,61092]{let mut h=sha3::Shake256::default();h.update(b"alternating-odd-mult");h.update(&seed.to_le_bytes());let mut xof=h.finalize_xof();let mut sim=Simulator::new(nq as usize,(nb as usize).max(1),&mut xof);for batch in cases.chunks(64){sim.clear_for_shot();for(l,&(v,sb))in batch.iter().enumerate(){put(&mut sim,&b,v,l);if sb&1!=0{*sim.qubit_mut(s0)|=1u64<<l;}if sb&2!=0{*sim.qubit_mut(s1)|=1u64<<l;}}sim.apply_iter(ops[..split].iter());let valid=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};ph+=(sim.phase&valid).count_ones()as usize;
 for(l,&(v,sb))in batch.iter().enumerate(){let negative=bit(v,n-1);let mag=if negative{(U512::from(1)<<n)-v}else{v};let alpha=5-2*((sb&1)as i32)-4*(((sb>>1)&1)as i32);let prod=mag*U512::from(alpha.unsigned_abs());let want=(if negative^(alpha<0){U512::ZERO.wrapping_sub(prod)}else{prod})&outmask;if !check(&sim,&p.out,want,l)||!check(&sim,&b,v,l){db+=1;if first.is_empty(){first=format!("n={n},v={v:#x},sb={sb},alpha={alpha}");}}}
 for q in[p.t,p.w,p.qa,p.qb]{if sim.qubit(q)&valid!=0{fdirty+=1;}}sim.apply_iter(ops[split..].iter());ph+=(sim.phase&valid).count_ones()as usize;for(l,&(v,sb))in batch.iter().enumerate(){if !check(&sim,&b,v,l)||((sim.qubit(s0)>>l)&1)!=(sb&1)as u64||((sim.qubit(s1)>>l)&1)!=((sb>>1)&1)as u64{ib+=1;}}for&q in b.iter().chain([s0,s1].iter()){*sim.qubit_mut(q)=0;}if sim.qubits.iter().any(|v|v&valid!=0){dirty+=1;}shots+=batch.len();}total+=sim.stats.toffoli_gates;}
 println!("SEED_MULT {{\"n\":{n},\"T\":{bt},\"inverse_T\":{it},\"Q\":{peak},\"cases\":{shots},\"data_bad\":{db},\"phase_bad\":{ph},\"input_bad\":{ib},\"forward_aux_bad\":{fdirty},\"dirty_batches\":{dirty},\"mean_roundtrip_T\":{},\"first\":\"{first}\"}}",total as f64/shots as f64);
 }}

pub(super) fn seed_product(c:&mut Builder,b:&[QubitId],s0:QubitId,s1:QubitId)->Vec<QubitId>{construct(c,b,s0,s1).out}
