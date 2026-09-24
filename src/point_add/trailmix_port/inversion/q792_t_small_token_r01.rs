//! Before T low unpack: Sq0 stays0, admitted Sq1..54 becomes Sq+8.
//! With A>=40,C>=1,A+C+S<=256, Cquarter+token<=62. Low unpack may
//! then park three residual bits in zero SM0..2. Inverse unpack precedes
//! inverse token. A<=39 requires a paid complete narrow fallback.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn permutation()->Vec<usize>{let ts=super::q792_fold20_rank_r01::triples();ts.iter().enumerate().map(|(i,t)|{let group:Vec<_>=ts.iter().enumerate().filter(|(_,u)|u[..2]==t[..2]).map(|(j,_)|j).collect();group[(group.iter().position(|&j|j==i).unwrap()+1)%group.len()]}).collect()}
fn trans(c:&mut Circuit,r:&[QReg],sm:&QReg,g:&QReg,d:&[QReg],a:usize,b:usize){let delta=a^b;let p=delta.trailing_zeros()as usize;let base=if a>>p&1==0{a}else{b};
    for i in 0..5{if i!=p&&delta>>i&1!=0{c.cx(&r[p],&r[i]);}}
    let mut cs=vec![(g,true),(sm,true)];cs.extend((0..5).filter(|&i|i!=p).map(|i|(&r[i],base>>i&1!=0)));mixed_mcx(c,&cs,&r[p],d);
    for i in (0..5).rev(){if i!=p&&delta>>i&1!=0{c.cx(&r[p],&r[i]);}}
}
fn sh_zero(c:&mut Circuit,r:&[QReg],out:&QReg,d:&[QReg]){
    // Exact all32-rank ANF, polarity21; independently truth-audited.
    for i in 0..5{if 21>>i&1!=0{c.x(&r[i]);}}
    for term in [1,2,3,4,8,9,10,18,20,25,28,31]{let cs:Vec<_>=(0..5).filter(|&i|term>>i&1!=0).map(|i|(&r[i],true)).collect();mixed_mcx(c,&cs,out,d);}
    for i in (0..5).rev(){if 21>>i&1!=0{c.x(&r[i]);}}
}
pub(super) fn emit(c:&mut Circuit,r:&[QReg],sm:&[QReg],g:&QReg,d:&[QReg],inverse:bool){
    assert_eq!(r.len(),5);assert_eq!(sm.len(),4);assert!(d.len()>=6);let at=c.b.ops.len();let owned=c.b.next_qubit;let p=permutation();let mut seen=[false;32];
    for a in 0..32{if seen[a]{continue;}seen[a]=true;let mut b=p[a];while b!=a{trans(c,r,&sm[3],g,d,a,b);seen[b]=true;b=p[b];}}
    c.cx(g,&sm[3]);
    for _ in 0..2{let mut cs=vec![(g,true),(&d[0],true)];cs.extend(sm[..3].iter().map(|q|(q,false)));mixed_mcx(c,&cs,&sm[3],&d[1..]);sh_zero(c,r,&d[0],&d[1..]);}
    if inverse{c.b.ops[at..].reverse();}assert_eq!(c.b.next_qubit,owned);
}
pub fn run(){
    use crate::{sim::Simulator,circuit::OperationType as K};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let q=c.alloc_qreg_bits("T-small-token",18);let owned=c.b.next_qubit;
    emit(&mut c,&q[..5],&q[5..9],&q[9],&q[10..],false);assert_eq!(c.b.next_qubit,owned);let ops=c.into_builder().ops;for op in &ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
    let ts=super::q792_fold20_rank_r01::triples();let p=permutation();let mut total=0;
    for first in (0..1usize<<18).step_by(64){let before:Vec<_>=(0..18).map(|b|(0..64).fold(0u64,|v,l|v|((((first+l)>>b)&1)as u64)<<l)).collect();let mut after=vec![0u64;18];
        for l in 0..64{let raw=first+l;let mut r=raw&31;let mut sm=raw>>5&15;if raw>>9&1!=0{if sm&8!=0{r=p[r];}sm^=8;if ts[r][2]==0&&sm&7==0{sm^=8;}}let expected=(raw&!511)|r|(sm<<5);for i in 0..18{after[i]|=(((expected>>i)&1)as u64)<<l;}}
        let mut f=Fixed;let mut sim=Simulator::new(18,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"T token first{first}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }
    eprintln!("T_SMALL_TOKEN_NATIVE_PASS cases={total} T={} N={} inverse=true phase=0 additional_clean_loans=0 whole_H=false",ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len());
}
