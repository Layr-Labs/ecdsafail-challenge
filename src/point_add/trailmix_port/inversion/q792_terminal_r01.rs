//! Eight-bit terminal history in the disjoint folded20 marker.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
pub(super) fn emit(c:&mut Circuit,m:&[QReg],d:&[QReg],quarter:bool,inverse:bool){
    assert_eq!(m.len(),20);assert!(d.len()>=16);if !quarter{return;}
    let hist:Vec<_>=m[10..16].iter().chain(&m[16..18]).collect();let mut base:Vec<_>=m[..4].iter().map(|q|(q,true)).collect();base.push((&m[5],true));
    for k in 0..8{let i=if inverse{k}else{7-k};let mut cs=base.clone();cs.extend(hist[..i].iter().map(|&q|(q,true)));mixed_mcx(c,&cs,hist[i],d);}
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x99)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut total=0;for quarter in [false,true]{let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let d=c.alloc_qreg_bits("d",20);let n=c.b.next_qubit;emit(&mut c,&m,&d,quarter,false);assert_eq!(c.b.next_qubit,n);let ops=c.into_builder().ops;
        eprintln!("FOLD20_TERMINAL_BUILT quarter={quarter} T={} ops={}",ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len());
        for first in (0..1usize<<20).step_by(64){let mut seed=0x7927e4d1u64^first as u64;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();for bit in 0..20{before[bit]=(0..64).fold(0,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}let mut after=before.clone();
            for lane in 0..64{let code=first+lane;let mut out=code;if quarter&&code&15==15&&code>>5&1!=0{let h=(code>>10)&255;out=(code&!(255<<10))|(((h+1)&255)<<10);}for bit in 0..20{let mask=1u64<<lane;after[bit]=(after[bit]&!mask)|(((out>>bit&1)as u64)<<lane);}}
            let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
    }eprintln!("FOLD20_TERMINAL_NATIVE_PASS lanes={total} all20bit_physical_codes=true history8=true inverse=true phase=0");
}
