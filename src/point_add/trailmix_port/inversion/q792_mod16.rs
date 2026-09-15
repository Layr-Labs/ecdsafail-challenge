//! Exact modulo16 q=0 cycle. Generic twelve-wire chart, not physical-Q792 by
//! itself. Diagnostic peak-reduction probe for the fourth omitted Work1 rail.
//!
//! Structure: the shipped 9-wire modulo8 chart (q793_mod8) applied to the low
//! three bit-planes, followed by an affine plane-3 correction (conditional
//! swaps/shears per (t0,b0,v0)) and a constant plane (ANF over the post-chart
//! low bits, gated by reachability H=(t0|v0) through a shared dirty echo).
//! Verified exhaustively (Python prototype, runtime/pro-k4-chart-derivation.md):
//! identity off guard, exact cycle on guard for all 4096 codes, arbitrary
//! dirty wire restored, phase 0, literal inverse. 228 ops, 2644 T (mcx model).
//!
//! Chart wires: [t0,t1,t2,t3, b0,b1,b2,b3, v0,v1,v2,v3] where in the physical
//! Q792 layout t=Work1 low bits, b=Work2 low bits, v=Work2 top lanes
//! (v0..v3 = W2[258],W2[257],W2[256],W2[255]).
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

const PLAN: &[(usize, &[i8])] = &[
    (6, &[3]),
    (2, &[13, 1, 7]),
    (6, &[3]),
    (10, &[7]),
    (6, &[13, 1, -5, 11]),
    (10, &[7]),
    (10, &[13, 1, 5, -9, 7]),
    (10, &[13, 1, 9, 3]),
    (10, &[13, 1]),
    (6, &[3]),
    (2, &[13, -1, 9, 7]),
    (6, &[3]),
    (10, &[3]),
    (2, &[13, -1, 9, 11]),
    (10, &[3]),
    (2, &[13, -1, 9, 5, 7]),
    (2, &[13, -1, 9]),
    (10, &[13, 1, 6, 10]),
    (5, &[2]),
    (9, &[2]),
    (10, &[13, 1, 5, 9, 6, 10]),
    (9, &[2]),
    (5, &[2]),
    (2, &[13, -1, 9, 2, 6]),
    (5, &[2]),
    (1, &[13, 1, 6]),
    (5, &[2]),
    (9, &[6]),
    (5, &[13, 1, -5, 10]),
    (9, &[6]),
    (9, &[13, 1, 5, -9, 6]),
    (9, &[13, 1, 9, 2]),
    (9, &[13, 1]),
    (5, &[2]),
    (1, &[13, -1, 9, 6]),
    (5, &[2]),
    (9, &[2]),
    (1, &[13, -1, 9, 10]),
    (9, &[2]),
    (1, &[13, -1, 9, 5, 6]),
    (1, &[13, -1, 9]),
    (8, &[1]),
    (0, &[13, -5, 9]),
    (8, &[1]),
    (4, &[1]),
    (0, &[13, 5, 9]),
    (4, &[1]),
    (8, &[13, 1, 5]),
    (7, &[4]),
    (3, &[8, 13, 1, -5, -9]),
    (7, &[4]),
    (11, &[4]),
    (3, &[12, 13, 1, -5, -9]),
    (11, &[4]),
    (7, &[4]),
    (3, &[8, 13, 1, 5, -9]),
    (7, &[4]),
    (11, &[4, 13, 1, 5, -9]),
    (7, &[4]),
    (3, &[8, 13, -1, -5, 9]),
    (7, &[4]),
    (11, &[8]),
    (7, &[12, 13, -1, -5, 9]),
    (11, &[8]),
    (7, &[4]),
    (3, &[8, 13, 1, -5, 9]),
    (7, &[4]),
    (11, &[4]),
    (3, &[12, 13, 1, -5, 9]),
    (11, &[4]),
    (3, &[8, 13, 1, -5, 9]),
    (7, &[4]),
    (3, &[8, 13, -1, 5, 9]),
    (7, &[4]),
    (11, &[8]),
    (7, &[12, 13, -1, 5, 9]),
    (11, &[8]),
    (11, &[4, 13, -1, 5, 9]),
    (7, &[4]),
    (3, &[8, 13, 1, 5, 9]),
    (7, &[4]),
    (11, &[8, 13, 1, 5, 9]),
    (13, &[1]),
    (13, &[9]),
    (13, &[1, 9]),
    (3, &[13, 14, 1]),
    (3, &[13, 14, 1, 2]),
    (3, &[13, 14, 1, 3]),
    (3, &[13, 14, 1, 5]),
    (3, &[13, 14, 1, 2, 5]),
    (3, &[13, 14, 1, 3, 5]),
    (3, &[13, 14, 1, 2, 6, 9]),
    (3, &[13, 14, 1, 3, 6, 9]),
    (3, &[13, 14, 1, 2, 5, 6, 9]),
    (3, &[13, 14, 1, 3, 5, 6, 9]),
    (3, &[13, 14, 1, 2, 7, 9]),
    (3, &[13, 14, 1, 3, 7, 9]),
    (3, &[13, 14, 1, 2, 5, 7, 9]),
    (3, &[13, 14, 1, 3, 5, 7, 9]),
    (3, &[13, 14, 1, 2, 6, 10]),
    (3, &[13, 14, 1, 3, 6, 10]),
    (3, &[13, 14, 1, 2, 5, 6, 10]),
    (3, &[13, 14, 1, 3, 5, 6, 10]),
    (3, &[13, 14, 1, 7, 10]),
    (3, &[13, 14, 1, 5, 7, 10]),
    (3, &[13, 14, 1, 6, 7, 9, 10]),
    (3, &[13, 14, 1, 5, 6, 7, 9, 10]),
    (3, &[13, 14, 1, 6, 11]),
    (3, &[13, 14, 1, 5, 6, 11]),
    (11, &[13, 14, 1, 5]),
    (11, &[13, 14, 1, 2, 5]),
    (11, &[13, 14, 1, 3, 5]),
    (11, &[13, 14, 9]),
    (11, &[13, 14, 1, 9]),
    (11, &[13, 14, 1, 2, 5, 9]),
    (11, &[13, 14, 3, 6, 9]),
    (11, &[13, 14, 1, 3, 6, 9]),
    (11, &[13, 14, 1, 2, 5, 6, 9]),
    (11, &[13, 14, 1, 3, 5, 6, 9]),
    (11, &[13, 14, 2, 3, 5, 6, 9]),
    (11, &[13, 14, 1, 2, 3, 5, 6, 9]),
    (11, &[13, 14, 2, 7, 9]),
    (11, &[13, 14, 1, 2, 7, 9]),
    (11, &[13, 14, 1, 2, 5, 6, 7, 9]),
    (11, &[13, 14, 1, 2, 5, 10]),
    (11, &[13, 14, 1, 3, 5, 10]),
    (11, &[13, 14, 1, 2, 5, 6, 10]),
    (11, &[13, 14, 1, 3, 5, 6, 10]),
    (11, &[13, 14, 1, 5, 7, 10]),
    (11, &[13, 14, 9, 10]),
    (11, &[13, 14, 1, 9, 10]),
    (11, &[13, 14, 2, 5, 9, 10]),
    (11, &[13, 14, 1, 2, 5, 9, 10]),
    (11, &[13, 14, 3, 5, 9, 10]),
    (11, &[13, 14, 1, 3, 5, 9, 10]),
    (11, &[13, 14, 2, 6, 9, 10]),
    (11, &[13, 14, 1, 2, 6, 9, 10]),
    (11, &[13, 14, 1, 5, 6, 9, 10]),
    (11, &[13, 14, 1, 2, 5, 6, 9, 10]),
    (11, &[13, 14, 1, 3, 5, 6, 9, 10]),
    (11, &[13, 14, 1, 2, 5, 7, 9, 10]),
    (11, &[13, 14, 1, 2, 5, 11]),
    (11, &[13, 14, 1, 3, 5, 11]),
    (11, &[13, 14, 1, 5, 6, 11]),
    (11, &[13, 14, 9, 11]),
    (11, &[13, 14, 1, 9, 11]),
    (11, &[13, 14, 2, 5, 9, 11]),
    (11, &[13, 14, 3, 5, 9, 11]),
    (11, &[13, 14, 2, 6, 9, 11]),
    (11, &[13, 14, 1, 2, 6, 9, 11]),
    (11, &[13, 14, 1, 2, 5, 6, 9, 11]),
    (11, &[13, 14, 1, 5, 7, 9, 11]),
    (11, &[13, 14, 1, 5, 6, 10, 11]),
    (11, &[13, 14, 1, 2, 5, 9, 10, 11]),
    (11, &[13, 14, 1, 5, 6, 9, 10, 11]),
    (13, &[1]),
    (13, &[9]),
    (13, &[1, 9]),
    (3, &[13, 14, 1]),
    (3, &[13, 14, 1, 2]),
    (3, &[13, 14, 1, 3]),
    (3, &[13, 14, 1, 5]),
    (3, &[13, 14, 1, 2, 5]),
    (3, &[13, 14, 1, 3, 5]),
    (3, &[13, 14, 1, 2, 6, 9]),
    (3, &[13, 14, 1, 3, 6, 9]),
    (3, &[13, 14, 1, 2, 5, 6, 9]),
    (3, &[13, 14, 1, 3, 5, 6, 9]),
    (3, &[13, 14, 1, 2, 7, 9]),
    (3, &[13, 14, 1, 3, 7, 9]),
    (3, &[13, 14, 1, 2, 5, 7, 9]),
    (3, &[13, 14, 1, 3, 5, 7, 9]),
    (3, &[13, 14, 1, 2, 6, 10]),
    (3, &[13, 14, 1, 3, 6, 10]),
    (3, &[13, 14, 1, 2, 5, 6, 10]),
    (3, &[13, 14, 1, 3, 5, 6, 10]),
    (3, &[13, 14, 1, 7, 10]),
    (3, &[13, 14, 1, 5, 7, 10]),
    (3, &[13, 14, 1, 6, 7, 9, 10]),
    (3, &[13, 14, 1, 5, 6, 7, 9, 10]),
    (3, &[13, 14, 1, 6, 11]),
    (3, &[13, 14, 1, 5, 6, 11]),
    (11, &[13, 14, 1, 5]),
    (11, &[13, 14, 1, 2, 5]),
    (11, &[13, 14, 1, 3, 5]),
    (11, &[13, 14, 9]),
    (11, &[13, 14, 1, 9]),
    (11, &[13, 14, 1, 2, 5, 9]),
    (11, &[13, 14, 3, 6, 9]),
    (11, &[13, 14, 1, 3, 6, 9]),
    (11, &[13, 14, 1, 2, 5, 6, 9]),
    (11, &[13, 14, 1, 3, 5, 6, 9]),
    (11, &[13, 14, 2, 3, 5, 6, 9]),
    (11, &[13, 14, 1, 2, 3, 5, 6, 9]),
    (11, &[13, 14, 2, 7, 9]),
    (11, &[13, 14, 1, 2, 7, 9]),
    (11, &[13, 14, 1, 2, 5, 6, 7, 9]),
    (11, &[13, 14, 1, 2, 5, 10]),
    (11, &[13, 14, 1, 3, 5, 10]),
    (11, &[13, 14, 1, 2, 5, 6, 10]),
    (11, &[13, 14, 1, 3, 5, 6, 10]),
    (11, &[13, 14, 1, 5, 7, 10]),
    (11, &[13, 14, 9, 10]),
    (11, &[13, 14, 1, 9, 10]),
    (11, &[13, 14, 2, 5, 9, 10]),
    (11, &[13, 14, 1, 2, 5, 9, 10]),
    (11, &[13, 14, 3, 5, 9, 10]),
    (11, &[13, 14, 1, 3, 5, 9, 10]),
    (11, &[13, 14, 2, 6, 9, 10]),
    (11, &[13, 14, 1, 2, 6, 9, 10]),
    (11, &[13, 14, 1, 5, 6, 9, 10]),
    (11, &[13, 14, 1, 2, 5, 6, 9, 10]),
    (11, &[13, 14, 1, 3, 5, 6, 9, 10]),
    (11, &[13, 14, 1, 2, 5, 7, 9, 10]),
    (11, &[13, 14, 1, 2, 5, 11]),
    (11, &[13, 14, 1, 3, 5, 11]),
    (11, &[13, 14, 1, 5, 6, 11]),
    (11, &[13, 14, 9, 11]),
    (11, &[13, 14, 1, 9, 11]),
    (11, &[13, 14, 2, 5, 9, 11]),
    (11, &[13, 14, 3, 5, 9, 11]),
    (11, &[13, 14, 2, 6, 9, 11]),
    (11, &[13, 14, 1, 2, 6, 9, 11]),
    (11, &[13, 14, 1, 2, 5, 6, 9, 11]),
    (11, &[13, 14, 1, 5, 7, 9, 11]),
    (11, &[13, 14, 1, 5, 6, 10, 11]),
    (11, &[13, 14, 1, 2, 5, 9, 10, 11]),
    (11, &[13, 14, 1, 5, 6, 9, 10, 11]),
];

/// Literal index 0..11 -> word[i], 12 -> guard, 13 -> the echo dirty wire.
pub(crate) fn cycle_swap(circ:&mut Circuit,word:[&QReg;12],g:&QReg,dirty:&[QReg]){
    // Widest consume is guard+d+7 low-bit literals = 9 controls; the ladder
    // path needs n-2=7 lenders. The real exit caller passes the full helper
    // bank (>=20); the selftest allocates exactly 7.
    assert!(dirty.len()>=7);
    let mut ids:Vec<_>=word.iter().map(|q|q.id()).chain(std::iter::once(g.id())).chain(dirty.iter().map(QReg::id)).collect();
    ids.sort_unstable();assert!(ids.windows(2).all(|x|x[0]!=x[1]),"mod16 chart aliases a lender/guard");
    let owned=circ.b.next_qubit;let active=circ.b.active_qubits;
    let echo=&dirty[0];let rest=&dirty[1..];
    for &(target,lits) in PLAN {
        let cs:Vec<_>=lits.iter().map(|&lit|{
            let index=lit.unsigned_abs()as usize-1;
            let q=if index==12{g}else if index==13{echo}else{word[index]};
            (q,lit>0)
        }).collect();
        let tq=if target==13{echo}else{word[target]};
        super::length_recompute::mixed_mcx(circ,&cs,tq,rest);
    }
    assert_eq!(circ.b.next_qubit,owned);assert_eq!(circ.b.active_qubits,active);
}

fn scalar(code:usize)->usize{
    let(t,b,v)=(code&15,code>>4&15,code>>8&15);
    if(t|v)&1==0{return code;}
    let m=15usize;
    let inv_t=inverse_16(t);let inv_v=inverse_16(v);
    let(u,r)=if t&1!=0{(b,(m.wrapping_sub(b*v).wrapping_mul(inv_t))&m)}
        else{((m.wrapping_sub(t*b).wrapping_mul(inv_v))&m,b)};
    assert_eq!((t*r+u*v)&m,m);
    u|((if u&1!=0{t}else{v})<<4)|(r<<8)
}

fn inverse_16(odd:usize)->usize{
    // Newton over the 2-adics: x0=1 (correct mod 2), x1=x0*(2-a) mod 4,
    // x2=x1*(2-a*x1) mod 16.
    let x1=(2usize.wrapping_sub(odd))&3;
    (x1.wrapping_mul(2usize.wrapping_sub(odd.wrapping_mul(x1))))&15
}

pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
    let word=circ.alloc_qreg_bits("q792.mod16.chart",12);let g=circ.alloc_qreg("q792.mod16.guard");let dirty=circ.alloc_qreg_bits("q792.mod16.dirty",7);
    cycle_swap(&mut circ,std::array::from_fn(|i|&word[i]),&g,&dirty);
    let b=circ.into_builder();assert_eq!(b.next_qubit,20);
    assert!(b.ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)));
    let t=b.ops.iter().filter(|o|o.kind==K::CCX).count();assert_eq!(t,2644);
    let mut rng=Fixed;let mut sim=Simulator::new(20,0,&mut rng);let mut lanes=0;
    for guard in 0..2{for pattern in 0..8{for first in(0..4096).step_by(64){
        let mut before=vec![0u64;20];let mut expected=before.clone();
        for lane in 0..64{
            let code=first+lane;let mapped=scalar(code);assert_eq!(scalar(mapped),code);
            for (state,value)in[(&mut before,code),(&mut expected,if guard==1{mapped}else{code})]{
                for bit in 0..12{state[word[bit].id()as usize]|=(((value>>bit)&1)as u64)<<lane;}
                state[g.id()as usize]|=(guard as u64)<<lane;
                for bit in 0..7{state[dirty[bit].id()as usize]|=(((pattern>>bit)&1)as u64)<<lane;}
            }
        }
        sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,expected);assert_eq!(sim.phase,0);
        sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
    }}}
    eprintln!("Q792_MOD16_INTEGRATED_PRIMITIVE_PASS lanes={lanes} physical_interface=20 chart=12 guard=1 dirty=7 clean=0 T={t} ops={}; NOT wholeQ792 or9024",b.ops.len());
}
