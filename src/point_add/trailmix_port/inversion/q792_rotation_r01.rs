//! Physical Work2 +/-1 rotations selected by existing phase bits.
//! Common reflection plus one of two directional reflections; no clean flag.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
fn pairs(n:usize,offset:usize)->Vec<(usize,usize)> {(0..n).filter_map(|i|{let j=(offset+n-i)%n;if i<j{Some((i,j))}else{None}}).collect()}
fn reflection(circ:&mut Circuit,word:&[QReg],guard:&QReg,offset:usize) {
    for (i,j) in pairs(word.len(),offset){circ.cx(&word[j],&word[i]);circ.ccx(guard,&word[i],&word[j]);circ.cx(&word[j],&word[i]);}
}
fn selected_reflection(circ:&mut Circuit,word:&[QReg],p1:&QReg,p2:&QReg,flag:&QReg,offset:usize,phase2:bool) {
    let pairs=pairs(word.len(),offset);
    if !phase2{circ.x(p2);}
    // Dirty echo over a whole reflection. The CNOT conjugations commute
    // with the flag update; cancel the middle pair before emitting gates.
    for &(i,j) in &pairs{circ.cx(&word[j],&word[i]);}
    for &(i,j) in &pairs{circ.ccx(flag,&word[i],&word[j]);}
    circ.ccx(p1,p2,flag);
    for &(i,j) in &pairs{circ.ccx(flag,&word[i],&word[j]);}
    for &(i,j) in &pairs{circ.cx(&word[j],&word[i]);}
    circ.ccx(p1,p2,flag);
    if !phase2{circ.x(p2);}
}
pub(super) fn rotate(circ:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,word:&[QReg],helpers:&[QReg],post:bool) {
    assert_eq!(word.len(),259);assert!(helpers.len()>=16);let start=circ.b.ops.len();
    let mut terminal:Vec<_>=m[..4].iter().map(|q|(q,true)).collect();terminal.push((&m[5],true));
    // Terminal canonical phase00 must skip the R pre-shift. Its marker
    // temporarily toggles P1; the post-shift is already off in phase00.
    if !post{mixed_mcx(circ,&terminal,p1,helpers);circ.x(p1);}
    // A=reflection0, B=reflection258. Chronological A^(u+v);B^u;A^v.
    circ.cx(p2,p1);reflection(circ,word,p1,0);circ.cx(p2,p1);
    reflection(circ,word,p1,258);
    reflection(circ,word,p2,0);
    if !post{circ.x(p1);mixed_mcx(circ,&terminal,p1,helpers);}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}

/// Full-width independent value/phase/inverse test of the fused rotations.
pub fn run(){
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 let mut cases=0;for post in [false,true]{let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let p1=c.alloc_qreg("p1");let p2=c.alloc_qreg("p2");let word=c.alloc_qreg_bits("word",259);let dirty=c.alloc_qreg_bits("dirty",16);let owned=c.b.next_qubit;rotate(&mut c,&m,&p1,&p2,&word,&dirty,post);assert_eq!(c.b.next_qubit,owned);let ops=c.into_builder().ops;
  for case in 0..32{let mut seed=0x833792f051u64^case;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();for l in 0..64{let a=l&1;let b=(l>>1)&1;let terminal=(l>>2)&1;for(q,v)in [(p1.id(),a),(p2.id(),b)]{before[q as usize]=(before[q as usize]&!(1<<l))|((v as u64)<<l);}for(q,v)in [(m[0].id(),1),(m[1].id(),1),(m[2].id(),1),(m[3].id(),1),(m[5].id(),terminal)]{before[q as usize]=(before[q as usize]&!(1<<l))|((v as u64)<<l);}}
   let mut after=before.clone();for l in 0..64{let a=(before[p1.id()as usize]>>l)&1;let b=(before[p2.id()as usize]>>l)&1;let terminal=(before[m[5].id()as usize]>>l)&1;let g=if post{a}else{a^terminal^1};if g!=0{for i in 0..259{let from=if b==1{(i+258)%259}else{(i+1)%259};let val=(before[word[from].id()as usize]>>l)&1;let q=word[i].id()as usize;after[q]=(after[q]&!(1<<l))|(val<<l);}}}
   let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"rotation post={post} case={case}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);cases+=64;
  }
 }
 eprintln!("Q792_ROTATION_FUSION_PASS lanes={cases} width=259 terminal_and_phase_all=true dirty_restored=true phase=0 inverse=true no_extra_qubits=true");
}
