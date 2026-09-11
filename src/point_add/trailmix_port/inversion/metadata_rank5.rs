//! Native high-index transitions for the alternative 21-bit layout.
//! rank5 + A_low6 + C_low6 + S_bits2..5; S0 and S1 are virtual.
//! These row permutations require caller-proven admissible counter endpoints.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
use std::collections::BTreeMap;
fn triples()->Vec<[usize;3]> {(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn rows(axis:usize)->Vec<Vec<usize>> {
    let mut groups:BTreeMap<Vec<usize>,Vec<(usize,usize)>>=BTreeMap::new();
    for (i,t) in triples().iter().enumerate() {groups.entry(if axis<3 {t.iter().enumerate().filter(|(j,_)|*j!=axis).map(|(_,v)|*v).collect()}else{vec![t[0],t[1]+t[2]]}).or_default().push((if axis<3 {t[axis]}else{t[1]},i));}
    groups.values_mut().map(|v|{v.sort();v.iter().map(|p|p.1).collect()}).collect()
}
pub(super) fn basis_swap(circ:&mut Circuit,rank:&[QReg],guard:&QReg,extras:&[(&QReg,bool)],helpers:&[QReg],left:usize,right:usize) {
    let mut value=left;let mut edges=Vec::new();
    for bit in 0..5 {if (left^right)>>bit&1!=0 {edges.push((bit,value));value^=1<<bit;}}
    assert_eq!(value,right);let path=edges.clone();edges.extend(path[..path.len()-1].iter().rev().copied());
    for (bit,value) in edges {
        let mut cs=vec![(guard,true)];cs.extend_from_slice(extras);cs.extend((0..5).filter(|&i|i!=bit).map(|i|(&rank[i],value>>i&1!=0)));
        mixed_mcx(circ,&cs,&rank[bit],helpers);
    }
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],guard:&QReg,extras:&[QReg],helpers:&[QReg],axis:usize,reverse:bool) {
    let mixed:Vec<_>=extras.iter().map(|q|(q,true)).collect();
    emit_mixed(circ,rank,guard,&mixed,helpers,axis,reverse);
}
pub(super) fn emit_mixed(circ:&mut Circuit,rank:&[QReg],guard:&QReg,extras:&[(&QReg,bool)],helpers:&[QReg],axis:usize,reverse:bool) {
    assert_eq!(rank.len(),5);assert!(axis<4);let start=circ.b.ops.len();
    for row in rows(axis) {for i in 1..row.len() {basis_swap(circ,rank,guard,extras,helpers,row[0],row[i]);}}
    if reverse {circ.b.ops[start..].reverse();}
}

struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    assert_eq!(triples().len(),32);let mut total=0;
    for axis in 0..4 {for n_extra in [0,6] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank5",5);let al=circ.alloc_qreg_bits("a_low",6);let cl=circ.alloc_qreg_bits("c_low",6);let sm=circ.alloc_qreg_bits("s_mid",4);assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("guard");let helpers=circ.alloc_qreg_bits("helpers",16);let owned=circ.b.next_qubit;
        let extras=&al[..n_extra];emit(&mut circ,&rank,&guard,extras,&helpers,axis,false);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        let mut expected:Vec<_>=(0..32).collect();for row in rows(axis) {for i in 0..row.len(){expected[row[i]]=row[(i+1)%row.len()];}}
        let cases=32*2*(1<<n_extra);
        for pattern in 0..4 {for batch in 0..cases/64 {
            let mut seed=0x617d30fb29e4ca85^batch as u64^((pattern as u64)<<30);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let k=batch*64+lane;let r=k&31;let on=k>>5&1!=0;let ex=k>>6;let mapped=if on&&ex==(1<<n_extra)-1 {expected[r]}else{r};
                for i in 0..5 {put(&mut before,&rank[i],lane,r>>i&1!=0);put(&mut after,&rank[i],lane,mapped>>i&1!=0);}
                for i in 0..n_extra {for w in [&mut before,&mut after]{put(w,&extras[i],lane,ex>>i&1!=0);}}
                for w in [&mut before,&mut after]{put(w,&guard,lane,on);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"axis={axis} extras={n_extra} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        let _=(cl,sm);eprintln!("CODEC_RANK5_UPDATE axis={axis} extras={n_extra} T={} ops={} metadata_wires=21 component_wires={owned} PASS",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
    }}
    eprintln!("CODEC_RANK5_PASS lanes={total}; 5-bit index permutations with dirty helpers; complete counters/terminal/arithmetic integration still missing");
}
