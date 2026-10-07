//! Read raw LT+shared sums directly from21-bit metadata using borrowed LS0 carry.
//! Component only: virtual phase offsets and zero/256 semantics belong to callers.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_sum_query_programs.rs"]mod programs;
pub(super) fn add4(circ:&mut Circuit,a:&[QReg],c:&[QReg],carry:&QReg,inverse:bool) {
    assert_eq!(a.len(),4);assert_eq!(c.len(),4);
    let mut gates:Vec<(u8,&QReg,&QReg,Option<&QReg>)>=Vec::new();
    for i in 0..4 {gates.push((0,&a[i],&c[i],None));}gates.push((0,&a[0],&c[0],None));
    for i in (1..4).rev() {if i==3 {gates.push((0,&a[i],carry,None));}if i+1<4 {gates.push((0,&a[i],&a[i+1],None));}}
    for i in 0..4 {gates.push((1,&a[i],if i+1<4 {&a[i+1]} else {carry},Some(&c[i])));}
    for i in (1..4).rev() {gates.push((0,&a[i],&c[i],None));gates.push((1,&a[i-1],&a[i],Some(&c[i-1])));}
    for i in 1..3 {gates.push((0,&a[i],&a[i+1],None));}
    for i in 0..4 {gates.push((0,&a[i],&c[i],None));}
    for offset in 0..gates.len() {let (kind,a,t,b)=gates[if inverse {gates.len()-1-offset}else{offset}];
        if kind==0 {circ.cx(a,t);}else{circ.ccx(a,b.unwrap(),t);}
    }
}
fn high(circ:&mut Circuit,rank:&[QReg],carry:&QReg,guard:&QReg,target:&QReg,helpers:&[QReg],program:&[(u16,u16)],low:&[(&QReg,bool)]) {
    for &(mask,value) in program {
        let mut cs=vec![(guard,true)];cs.extend((0..11).filter(|&i|mask>>i&1!=0).map(|i|(if i==10 {carry}else{&rank[i]},value>>i&1!=0)));cs.extend_from_slice(low);
        length_recompute::mixed_mcx(circ,&cs,target,helpers);
    }
}
fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],s0:&QReg,guard:&QReg,target:&QReg,helpers:&[QReg],bound:usize,equal:bool,known:bool) {
    assert!(bound<=288);assert!(helpers.len()>=14);
    if known {circ.x(s0);}add4(circ,a,c,s0,false);
    if !equal {high(circ,rank,s0,guard,target,helpers,programs::BELOW[bound/16],&[]);}
    let lows=if equal {vec![(0..4).map(|i|(i,(bound>>i)&1!=0)).collect()]}else{length_recompute::below_cubes(4,bound%16)};
    for low in lows {let controls:Vec<_>=low.iter().map(|&(i,v)|(&c[i],v)).collect();high(circ,rank,s0,guard,target,helpers,programs::EQUAL[bound/16],&controls);}
    add4(circ,a,c,s0,true);if known {circ.x(s0);}
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
fn check_adder() {
    let mut c=Circuit::new();let a=c.alloc_qreg_bits("sum.a",4);let b=c.alloc_qreg_bits("sum.b",4);let carry=c.alloc_qreg("sum.carry");add4(&mut c,&a,&b,&carry,false);let ops=c.into_builder().ops;
    for batch in 0..8 {
        let mut before=vec![0u64;9];let mut after=before.clone();
        for lane in 0..64 {let n=batch*64+lane;let av=n&15;let bv=n>>4&15;let cv=n>>8&1;
            for i in 0..4 {put(&mut before,&a[i],lane,av>>i&1!=0);put(&mut after,&a[i],lane,av>>i&1!=0);put(&mut before,&b[i],lane,bv>>i&1!=0);put(&mut after,&b[i],lane,(av+bv)>>i&1!=0);}
            put(&mut before,&carry,lane,cv!=0);put(&mut after,&carry,lane,(cv^((av+bv)>>4))!=0);
        }
        let mut f=Fixed;let mut sim=Simulator::new(9,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
    }
    eprintln!("CODEC_SUM_ADD4_PASS lanes=512 carry_xor_phase_reverse=PASS");
}
pub fn run() {
    check_adder();let triples:Vec<_>=(0..16).flat_map(|a|(0..16).flat_map(move|c|(0..16).filter(move|&s|a+c+s<=16).map(move|s|[a,c,s]))).collect();
    let bounds=[0usize,1,15,16,17,31,32,63,127,128,129,255,256,257,271,272,286,287,288];let mut total=0usize;
    for equal in [false,true] {for &bound in &bounds {let mut printed=false;for known in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("query.rank",10);let a=circ.alloc_qreg_bits("query.a",4);let c=circ.alloc_qreg_bits("query.c",4);let sm=circ.alloc_qreg_bits("query.s23",2);let s0=circ.alloc_qreg("query.s0");assert_eq!(circ.b.next_qubit,21);
        let guard=circ.alloc_qreg("query.guard");let target=circ.alloc_qreg("query.target");let helpers=circ.alloc_qreg_bits("query.dirty",16);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&a,&c,&s0,&guard,&target,&helpers,bound,equal,known);assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));for q in &sm{assert!(op.q_target.0!=q.id()as u64&&op.q_control1.0!=q.id()as u64&&op.q_control2.0!=q.id()as u64);}}
        let tof=b.ops.iter().filter(|o|o.kind==OperationType::CCX).count();
        let cases=1024*16*16*2;
        for pattern in 0..2 {for batch in 0..cases/64 {
            let mut seed=0x891fc674a502d39bu64^batch as u64^pattern as u64;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {let n=batch*64+lane;let r=n&1023;let al=n>>10&15;let cl=n>>14&15;let on=n>>18&1!=0;
                let sum=if r<966 {(triples[r][0]+triples[r][1])*16+al+cl}else{0};let hit=on&&r<966&&if equal {sum==bound}else{sum<bound};
                for i in 0..10{put(&mut before,&rank[i],lane,r>>i&1!=0);put(&mut after,&rank[i],lane,r>>i&1!=0);}
                for i in 0..4{for (q,v) in [(&a[i],al>>i&1!=0),(&c[i],cl>>i&1!=0)]{put(&mut before,q,lane,v);put(&mut after,q,lane,v);}}
                let scratch=if on {known}else{(n+pattern)%2!=0};let old=(n+pattern)%2!=0;
                for (q,v) in [(&s0,scratch),(&guard,on),(&target,old)]{put(&mut before,q,lane,v);put(&mut after,q,lane,if q.id()==target.id(){v^hit}else{v});}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"sum query bound={bound} eq={equal} known={known} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        if !printed {eprintln!("CODEC_SUM_QUERY equal={equal} bound={bound} T={tof} ops={} metadata_wires=21 component_wires={owned} full_rank_low_guard_dirty_phase_reverse=PASS",b.ops.len());printed=true;}
    }}}
    eprintln!("CODEC_SUM_QUERY_PASS lanes={total}; exact raw LT+shared comparisons without24-bit unpacking; no fullQ799 circuit");
}

pub(super) fn xor_high_equal(circ:&mut Circuit,rank:&[QReg],carry:&QReg,guard:&QReg,target:&QReg,helpers:&[QReg],bound:usize) {
    high(circ,rank,carry,guard,target,helpers,programs::EQUAL[bound],&[]);
}
