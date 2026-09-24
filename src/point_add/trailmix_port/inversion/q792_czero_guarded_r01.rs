//! Guarded reversible C0 chart. On C0: A8/S6 and six zero scratch rails.
//! On other metadata it is an arbitrary reversible extension, restored around
//! the sole phase00 comparator center. No clean qubit is allocated.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn trans(c:&mut Circuit,w:&[&QReg],g:&QReg,d:&[QReg],x:usize,y:usize){
    if x==y{return;}let delta=x^y;let p=delta.trailing_zeros()as usize;let base=if x>>p&1==0{x}else{y};
    for i in 0..w.len(){if i!=p&&delta>>i&1!=0{c.cx(w[p],w[i]);}}
    let mut cs:Vec<_>=(0..w.len()).filter(|&i|i!=p).map(|i|(w[i],base>>i&1!=0)).collect();cs.push((g,true));mixed_mcx(c,&cs,w[p],d);
    for i in (0..w.len()).rev(){if i!=p&&delta>>i&1!=0{c.cx(w[p],w[i]);}}
}
fn swaps()->Vec<(usize,usize)>{
    let ts=super::q792_fold20_rank_r01::triples();let mut pairs=Vec::new();
    for(r,t)in ts.iter().enumerate(){if t[1]!=0{continue;}let x=super::q792_fold20_rank_r01::encode(r,0,0,0,&ts);let tag=x&15;let cl=if tag==15{x>>6&15}else{x>>10&63};pairs.push((tag|cl<<4,t[0]|t[2]<<2));}
    let mut perm:Vec<_>=(0..1024).collect();let mut assigned=vec![false;1024];let mut used=assigned.clone();for &(x,y)in &pairs{assert!(!assigned[x]&&!used[y]);assigned[x]=true;used[y]=true;perm[x]=y;}
    for x in 0..1024{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=perm[y];}perm[y]=x;assigned[y]=true;used[x]=true;}}
    let mut seen=vec![false;1024];let mut out=Vec::new();for root in 0..1024{if seen[root]{continue;}seen[root]=true;let mut y=perm[root];while y!=root{assert!(!seen[y]);seen[y]=true;out.push((root,y));y=perm[y];}}
    for &(x,y)in &pairs{let mut z=x;for &(a,b)in &out{if z==a{z=b}else if z==b{z=a}}assert_eq!(z,y);}out
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],g:&QReg,d:&[QReg],inverse:bool){
    assert_eq!(m.len(),20);assert!(d.len()>=16);let at=c.b.ops.len();
    // For C0 the reflected side is exactly C_low63 on an edge tag.
    let tag:Vec<_>=m[..4].iter().collect();let mut cs:Vec<_>=m[10..16].iter().map(|q|(q,true)).collect();cs.push((g,true));
    let outputs:Vec<_>=m[4..10].iter().chain(&m[16..20]).collect();
    for group in outputs.chunks(8){super::q792_output_basis_r01::emit(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&cs,group,d);}
    // Peak original A[2..6] and C are zero; move its index into C[0..4].
    for i in 0..4{let mut cs:Vec<_>=m[..4].iter().map(|q|(q,true)).collect();cs.push((g,true));c.cx(&m[6+i],&m[10+i]);cs.push((&m[10+i],true));mixed_mcx(c,&cs,&m[6+i],d);c.cx(&m[6+i],&m[10+i]);}
    let word:Vec<_>=m[..4].iter().chain(&m[10..16]).collect();for(x,y)in swaps(){trans(c,&word,g,d,x,y);}if inverse{c.b.ops[at..].reverse();}
}
