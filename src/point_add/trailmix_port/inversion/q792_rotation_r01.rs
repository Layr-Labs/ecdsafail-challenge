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
    reflection(circ,word,p1,0);
    selected_reflection(circ,word,p1,p2,&helpers[0],258,false);
    selected_reflection(circ,word,p1,p2,&helpers[0],1,true);
    if !post{circ.x(p1);mixed_mcx(circ,&terminal,p1,helpers);}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
