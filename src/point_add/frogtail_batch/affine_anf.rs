//! Exact affine changes of variables for Boolean chart polynomials.
use crate::circuit::QubitId;
use std::collections::{BTreeSet,HashMap};
use std::cell::RefCell;
thread_local! {static CACHE:RefCell<HashMap<(Vec<u64>,u8),(Vec<u64>,Vec<(usize,usize,usize)>)>>=RefCell::new(HashMap::new());}
fn weight(m:u64,style:u8)->usize {let n=m.count_ones() as usize;match style{
 0=>match n{0|1=>0,2=>2,3=>5,_=>8*n-20},
 1=>match n{0|1=>0,2=>2,_=>8*n-16},
 2=>match n{0|1|2=>0,3=>2,_=>8*n-24},
 3=>match n{0|1=>0,2=>2,3=>4,_=>8*n-22},
 _=>match n{0|1|2=>0,3=>2,4=>4,_=>8*n-30},
}}
fn cost(p:&[u64],style:u8)->usize {p.iter().map(|&m|weight(m,style)).sum()}
fn change(p:&[u64],i:usize,j:usize)->Vec<u64> {
 let mut out:BTreeSet<u64>=p.iter().copied().collect();
 for &m in p {if m>>i&1 !=0 {let k=if i==j {m&!(1<<i)} else {(m&!(1<<i))|(1<<j)}; if !out.insert(k){out.remove(&k);}}}
 out.into_iter().collect()
}
fn change_product(p:&[u64],i:usize,j:usize,k:usize)->Vec<u64>{
 let mut out:BTreeSet<u64>=p.iter().copied().collect();
 for &m in p {if m>>i&1 !=0 {let n=(m&!(1<<i))|(1<<j)|(1<<k);if !out.insert(n){out.remove(&n);}}}
 out.into_iter().collect()
}
pub fn optimize(terms:&[Vec<QubitId>])->(Vec<Vec<QubitId>>,Vec<(QubitId,QubitId,QubitId)>) {optimize_style(terms,0)}
pub fn optimize_style(terms:&[Vec<QubitId>],style:u8)->(Vec<Vec<QubitId>>,Vec<(QubitId,QubitId,QubitId)>) {
 let qs:Vec<_>=terms.iter().flatten().copied().map(|q|q.0).collect::<BTreeSet<_>>().into_iter().map(QubitId).collect();
 if qs.len()>20 {return (terms.to_vec(),vec![]);}
 let p:Vec<u64>=terms.iter().map(|k|k.iter().fold(0,|m,q|m|(1<<qs.iter().position(|x|x==q).unwrap()))).collect::<BTreeSet<_>>().into_iter().collect();
 let (p,moves)=CACHE.with(|c|{let mut c=c.borrow_mut(); c.entry((p.clone(),style)).or_insert_with(||{
  let mut p=p;let mut moves=vec![];
  loop {let now=cost(&p,style); let mut best=now;let mut found=None;
   for i in 0..qs.len(){for j in 0..qs.len(){let q=change(&p,i,j);let v=cost(&q,style);if v<best {best=v;found=Some((q,i,j));}}}
   match found {Some((q,i,j))=>{p=q;moves.push((j,i,i));},None=>{
    let mut best=now;let mut next=None;
    for i in 0..qs.len(){for j in 0..qs.len(){if j==i{continue;}for k in j+1..qs.len(){if k==i{continue;}
     let q=change_product(&p,i,j,k);let v=cost(&q,style)+if style==0{8}else{4};
     if v<best{best=v;next=Some((q,j,k,i));}
    }}}
    if let Some((q,j,k,i))=next{p=q;moves.push((j,k,i));}else{break;}
   }}
  }
  (p,moves)
 }).clone()});
 (p.iter().map(|m|(0..qs.len()).filter(|i|m>>i&1!=0).map(|i|qs[i]).collect()).collect(),moves.iter().map(|&(a,b,t)|(qs[a],qs[b],qs[t])).collect())
}

#[cfg(test)]
mod tests {
 use super::*;
 use super::super::builder::{B,G,AnfCall};
 use crate::{sim::Simulator,circuit::analyze_ops};
 use sha3::digest::XofReader;
 struct Fixed(u8);impl XofReader for Fixed{fn read(&mut self,out:&mut[u8]){out.fill(self.0);}}
 #[test]
 fn affine_factored_charts_all_inputs_and_measurements(){
  for masks in [vec![0u64,1,3,5,7,11,19,35,67,15,23,39,71,31,47,79,63,95],vec![19u64,29,35,45,50,60],vec![51u64,60,67,76]] {for use_clean in 0usize..=3 {for mode in 0..3 {
   let mut b=B::new();let qs=b.alloc_n(7);let target=b.alloc();let dirty=b.alloc_n(12);let clean=b.alloc_n(use_clean);
   let orig:Vec<Vec<QubitId>>=masks.iter().map(|m|(0..7).filter(|i|m>>i&1!=0).map(|i|qs[i]).collect()).collect();
   if mode<2 {
    let (terms,affine)=optimize(&orig);
    for &(a,c,t) in &affine{if a==t{b.x(t)}else if c==t{b.cx(a,t)}else{b.ccx(a,c,t)}}
    b.anf_terms_clean(&terms,if mode==0{Some(target)}else{None},&clean,&dirty);
    for &(a,c,t) in affine.iter().rev(){if a==t{b.x(t)}else if c==t{b.cx(a,t)}else{b.ccx(a,c,t)}}
   }else{
    let i=b.anf_spec(AnfCall{clean:clean.clone(),affine:vec![],fold:vec![],flip:false,terms:orig,target,dirty:dirty.clone(),cond:crate::circuit::NO_BIT});
    b.g(G::AnfC(i));b.g(G::AnfU(i));b.g(G::AnfC(i));b.g(G::AnfU(i));
   }
   let(_,nb,_,_)=analyze_ops(b.ops.iter());
   for byte in [0,255,170,85] {for batch in 0..2 {
    let mut rng=Fixed(byte);let mut sim=Simulator::new(b.width() as usize,nb as usize,&mut rng);
    let mut truth=0u64;
    for shot in 0..64 {let row=batch*64+shot;
     for i in 0..7 {sim.qubits[qs[i].0 as usize]|=(((row>>i)&1) as u64)<<shot;}
     for (i,q) in dirty.iter().enumerate(){sim.qubits[q.0 as usize]|=(((row*37+i*17)>>3&1)as u64)<<shot;}
     let f=masks.iter().fold(false,|f,m|f^((row as u64&m)==*m));truth|=(f as u64)<<shot;
    }
    let init=sim.qubits.clone();sim.apply_iter(b.ops.iter());
    assert_eq!(sim.phase,if mode==1{truth}else{0});
    assert_eq!(sim.qubits[target.0 as usize],if mode==0{truth}else{0});
    for q in qs.iter().chain(&dirty).chain(&clean){assert_eq!(sim.qubits[q.0 as usize],init[q.0 as usize]);}
   }}
  }
 }
}
}
}
