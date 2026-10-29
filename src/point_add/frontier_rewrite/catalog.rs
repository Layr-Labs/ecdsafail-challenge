//! Exact local signed-permutation identities on three or four existing wires.
use std::collections::HashMap;
use quantum_ecc::circuit::{Op,OperationType as K,QubitId,NO_BIT,NO_QUBIT};
#[derive(Clone,Copy,Debug)]
struct Gate { kind:K,t:u8,c:u8,d:u8 }
#[derive(Clone)]
struct Entry { toffoli:usize,gates:Vec<Gate> }
type Table=HashMap<[u8;16],Entry>;
fn nonlinear(k:K)->usize {usize::from(matches!(k,K::CCX|K::CCZ))}
fn allowed(o:&Op)->bool {o.c_condition==NO_BIT&&matches!(o.kind,K::Neg|K::X|K::Z|K::CX|K::CZ|K::Swap|K::CCX|K::CCZ)}
fn gate(kind:K,t:u8,c:u8,d:u8)->Gate {Gate {kind,t,c,d}}
fn alphabet(n:u8)->Vec<Gate> {
 let mut v=vec![gate(K::Neg,255,255,255)];
 for t in 0..n {v.push(gate(K::X,t,255,255));v.push(gate(K::Z,t,255,255));}
 for t in 0..n {for c in 0..n {if t==c {continue;}v.push(gate(K::CX,t,c,255));if t<c {v.push(gate(K::CZ,t,c,255));v.push(gate(K::Swap,t,c,255));}}}
 for t in 0..n {for a in 0..n {for b in a+1..n {if t!=a&&t!=b {v.push(gate(K::CCX,t,a,b));}}}}
 for a in 0..n {for b in a+1..n {for c in b+1..n {v.push(gate(K::CCZ,c,a,b));}}}
 v
}
fn identity(n:usize)->[u8;16] {let mut s=[0;16];for (i,x) in s.iter_mut().enumerate().take(1<<n){*x=(i as u8)<<1;}s}
fn step(mut s:[u8;16],n:usize,g:Gate)->[u8;16] {
 for entry in s.iter_mut().take(1<<n) {
  let mut x=*entry>>1;let mut p=*entry&1;
  let bit=|q:u8|(x>>q)&1;
  match g.kind {
   K::Neg=>p^=1,K::X=>x^=1<<g.t,K::Z=>p^=bit(g.t),
   K::CX=>if bit(g.c)!=0{x^=1<<g.t;},K::CZ=>p^=bit(g.c)&bit(g.t),
   K::CCX=>if bit(g.c)&bit(g.d)!=0{x^=1<<g.t;},K::CCZ=>p^=bit(g.t)&bit(g.c)&bit(g.d),
   K::Swap=>if bit(g.t)!=bit(g.c){x^=(1<<g.t)|(1<<g.c);},_=>unreachable!()
  }
  *entry=(x<<1)|p;
 }
 s
}
fn extend(n:usize,letters:&[Gate],s:[u8;16],cost:usize,prefix:&mut Vec<Gate>,table:&mut Table) {
 let improve=table.get(&s).map(|old|(cost,prefix.len())<(old.toffoli,old.gates.len())).unwrap_or(true);
 if improve {table.insert(s,Entry {toffoli:cost,gates:prefix.clone()});}
 if prefix.len()==3 {return;}
 for &g in letters {let next_cost=cost+nonlinear(g.kind);if next_cost>1 {continue;}prefix.push(g);extend(n,letters,step(s,n,g),next_cost,prefix,table);prefix.pop();}
}
fn catalog(n:usize)->Table {let mut table=Table::new();extend(n,&alphabet(n as u8),identity(n),0,&mut Vec::new(),&mut table);table}
fn wires(ops:&[Op])->Vec<QubitId> {
 let mut v=Vec::new();for o in ops {for q in [o.q_target,o.q_control1,o.q_control2] {if q!=NO_QUBIT&&!v.contains(&q){v.push(q);}}}v.sort_unstable();v
}
fn local(o:&Op,w:&[QubitId])->Gate {let id=|q|if q==NO_QUBIT{255}else{w.iter().position(|&x|x==q).unwrap() as u8};gate(o.kind,id(o.q_target),id(o.q_control1),id(o.q_control2))}
fn lifted(g:Gate,w:&[QubitId])->Op {let mut o=Op::empty();o.kind=g.kind;if g.t!=255{o.q_target=w[g.t as usize];}if g.c!=255{o.q_control1=w[g.c as usize];}if g.d!=255{o.q_control2=w[g.d as usize];}o}
fn signature(ops:&[Op],w:&[QubitId])->[u8;16] {ops.iter().fold(identity(w.len()),|s,o|step(s,w.len(),local(o,w)))}
#[cfg(test)]
pub fn equivalent(a:&[Op],b:&[Op])->bool {let mut all=a.to_vec();all.extend_from_slice(b);let w=wires(&all);assert!(w.len()<=4);signature(a,&w)==signature(b,&w)}
pub fn optimize(ops:Vec<Op>)->Vec<Op> {
 let tables=[catalog(3),catalog(4)];eprintln!("catalog entries3={} entries4={}",tables[0].len(),tables[1].len());
 let mut out:Vec<Op>=Vec::with_capacity(ops.len() + 1_000_000);let mut saved=0usize;let mut rewrites=0usize;
 for (input_index,op) in ops.into_iter().enumerate() {
  out.push(op);
  loop {
   let mut found=None;
   for len in (2..=5).rev() {
    if out.len()<len {continue;}
    let window=&out[out.len()-len..];let count:usize=window.iter().map(|o|nonlinear(o.kind)).sum();
    if count<2||!window.iter().all(allowed){continue;}
    let w=wires(window);if !(3..=4).contains(&w.len()){continue;}
    let key=signature(window,&w);
    if let Some(entry)=tables[w.len()-3].get(&key) {
     if entry.toffoli<count {
      let replacement:Vec<_>=entry.gates.iter().map(|g|lifted(*g,&w)).collect();
      found=Some((len,replacement,count-entry.toffoli,w,key));break;
     }
    }
   }
   let Some((len,replacement,gain,w,key))=found else {break;};
   eprintln!("catalog_rewrite input_end={input_index} output_begin={} old_len={len} new_len={} native_saved={gain} wires={w:?} signature={key:?}",out.len()-len,replacement.len());
   out.truncate(out.len()-len);out.extend(replacement);saved+=gain;rewrites+=1;
  }
 }
 eprintln!("research_catalog rewrites={rewrites} native_toffolis_saved={saved}");out
}

#[cfg(all(test, greedyfrog_legacy_tests))] // needs the study_check crate
mod fixed_simulator_certificate {
 use super::*;
 #[test]
 fn every_catalog_entry_matches_the_fixed_simulator() {
  let mut random=study_check::stream(b"catalog-certificate",&[]);
  for n in [3,4] {
   let roles:Vec<_>=(0..n).map(|q|QubitId(q as u64)).collect();
   for (key,entry) in catalog(n) {
    let mut sim=quantum_ecc::sim::Simulator::new(n,0,&mut random);
    for lane in 0..64 {for q in 0..n {if (lane>>q)&1!=0 {sim.qubits[q]|=1u64<<lane;}}}
    let ops:Vec<_>=entry.gates.iter().map(|g|lifted(*g,&roles)).collect();
    for op in &ops {op.validate();}
    sim.apply_iter(ops.iter());
    for lane in 0..64 {
     let input=lane&((1<<n)-1);let mut image=0u8;
     for q in 0..n {image|=(((sim.qubits[q]>>lane)&1) as u8)<<q;}
     let sign=((sim.phase>>lane)&1) as u8;
     assert_eq!((image<<1)|sign,key[input]);
    }
   }
  }
 }
}
