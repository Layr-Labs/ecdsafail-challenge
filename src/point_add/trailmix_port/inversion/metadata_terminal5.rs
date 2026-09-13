//! Terminal history counter on the alternative21-bit metadata code.
//! Active raw A<=254. Terminal rank(3,0,0)=29 and A_low63 select history.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],helpers:&[QReg],quarter:bool,inverse:bool) {
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(helpers.len()>=16);if !quarter{return;}
    let hist:Vec<_>=c.iter().chain(&sm[..2]).collect();let mut terminal:Vec<_>=(0..5).map(|i|(&rank[i],29>>i&1!=0)).collect();terminal.extend(a.iter().map(|q|(q,true)));
    for k in 0..8{let i=if inverse{k}else{7-k};let mut cs=terminal.clone();cs.extend(hist[..i].iter().map(|&q|(q,true)));mixed_mcx(circ,&cs,hist[i],helpers);}
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run(){
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();assert_eq!(triples[29],[3,0,0]);let mut total=0;
    for quarter in [false,true]{
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("term5.rank",5);let a=circ.alloc_qreg_bits("term5.a",6);let c=circ.alloc_qreg_bits("term5.c",6);let sm=circ.alloc_qreg_bits("term5.sm",4);assert_eq!(circ.b.next_qubit,21);let helpers=circ.alloc_qreg_bits("term5.dirty",16);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&a,&c,&sm,&helpers,quarter,false);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        for pattern in 0..2{for batch in 0..(1<<21)/64{
            let mut seed=0xb29183ac7df6450e^batch as u64^((pattern as u64)<<28);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{
                let k=batch*64+lane;let r=k&31;let al=k>>5&63;let hist=k>>11&255;let upper=k>>19&3;let result=if quarter&&r==29&&al==63{(hist+1)&255}else{hist};
                for i in 0..5{for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..6{for w in [&mut before,&mut after]{put(w,&a[i],lane,al>>i&1!=0);}put(&mut before,&c[i],lane,hist>>i&1!=0);put(&mut after,&c[i],lane,result>>i&1!=0);}
                for i in 0..4{put(&mut before,&sm[i],lane,((hist>>6)|(upper<<2))>>i&1!=0);put(&mut after,&sm[i],lane,((result>>6)|(upper<<2))>>i&1!=0);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("CODEC_TERMINAL5 quarter={quarter} T={} ops={} metadata_wires=21 component_wires={owned} all_physical_codes_two_dirty_patterns_phase_reverse=PASS",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
    }
    eprintln!("CODEC_TERMINAL5_PASS lanes={total}; terminal8-bit history under exact marker, native lifecycle entry/exit still missing");
}
