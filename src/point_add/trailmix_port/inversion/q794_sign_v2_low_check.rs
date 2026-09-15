//! Native exact low carry for C1/C2/C>=3, including arbitrary C2 head cargo.
use super::*;
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,l:usize,v:usize){let bit=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!bit)|if v!=0{bit}else{0};}
fn maj(mut s:usize,mut y:usize,mut carry:usize)->(usize,usize,usize){y^=s;s^=carry;carry^=y&s;(s,y,carry)}
pub fn run(){
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
    let g=circ.alloc_qreg("g");let mask=circ.alloc_qreg("mask");let carry=circ.alloc_qreg("carry");let source=circ.alloc_qreg_bits("source",259);let target=circ.alloc_qreg_bits("target",259);let dirty=circ.alloc_qreg_bits("dirty",21);let owned=circ.b.next_qubit;
    virtual_low_correction(&mut circ,&rank,&c,&sm,&g,&mask,&carry,&source,&target,&dirty,0);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
    for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for hole in [257,258]{let q=source[hole].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q);}}
    let mut cases=Vec::new();for cv in 1..=3{for ah in 0..4{for t in 0..4{for raw_b in 0..4{for passenger in 0..2{for enabled in 0..2{for inside in 0..2{for extra in 0..2{cases.push((cv,ah,t,raw_b,passenger,enabled,inside,extra));}}}}}}}}
    let mut total=0;
    for pattern in 0..4{for batch in 0..cases.len().div_ceil(64){let mut rng=0xa794c251u64^(pattern as u64)<<32^batch as u64;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut after=before.clone();
        for lane in 0..64{let(cv,ah,t,raw_b,passenger,enabled,inside,extra)=cases[(batch*64+lane)%cases.len()];
            let r=ts.iter().position(|&x|x==[ah,0,0]).unwrap();
            let(s0,b0,c0)=maj(t&1,raw_b&1,0);let(s1,b1,c1)=maj(t>>1,raw_b>>1,c0);
            let v1=if cv==1{0}else if cv==2{1}else{passenger};
            let u=if t&1!=0{raw_b}else{1+2*(1^v1^((t>>1)*(raw_b&1)))};
            let want=if enabled!=0&&inside!=0{usize::from(t>u)}else{c1};
            for w in [&mut before,&mut after]{
                for i in 0..5{put(w,&rank[i],lane,(r>>i)&1);}
                for i in 0..6{put(w,&c[i],lane,(cv>>i)&1);}
                for q in &sm{put(w,q,lane,0);}
                put(w,&g,lane,enabled);put(w,&mask,lane,inside);put(w,&source[0],lane,s0);put(w,&source[1],lane,s1);put(w,&target[0],lane,b0);put(w,&target[1],lane,b1);put(w,&target[257],lane,passenger);
            }
            put(&mut before,&carry,lane,c1^extra);put(&mut after,&carry,lane,want^extra);
        }
        let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"Sign v2 carry pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);
        sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}
    eprintln!("Q794_SIGN_V2_LOW_PASS lanes={total} T={} ops={}; C1v1=0/C2v1=1/C3ordinary, all low chart bits/cargo/g/mask/output biases, arbitrary21dirty, NCTphase0/inverse/noalloc/noholes; whole adapter separately validated",b.ops.iter().filter(|o|o.kind==K::CCX).count(),b.ops.len());
}
