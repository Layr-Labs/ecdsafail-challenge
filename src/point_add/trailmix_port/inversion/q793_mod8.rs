//! Exact modulo8 q=0 cycle. Generic nine-wire chart, not physical-Q793 by itself.
//! Source gate plan efd63764dfc9dffb923e88c09084565cafdd1a9f5b6c1f9b15571d12fe386674.
//! Chart [t0,t1,t2,b0,b1,b2,v0,v1,v2], b=u if t odd, otherwise b=r.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
const PLAN:&[(usize,&[i8])]=&[
    (8, &[10,1,4,-7,3]),
    (8, &[10,1,4,7,6]),
    (2, &[10,1,-4,7,6]),
    (2, &[6]),
    (5, &[10,1,3]),
    (2, &[6]),
    (5, &[9]),
    (8, &[10,1,-4,6]),
    (5, &[9]),
    (8, &[10,-1,7,4,3]),
    (5, &[9]),
    (8, &[10,-1,7,6]),
    (5, &[9]),
    (2, &[6]),
    (5, &[10,-1,7,3]),
    (2, &[6]),
    (8, &[10,1]),
    (2, &[10,-1,7]),
    (8, &[10,1,5,8]),
    (4, &[2]),
    (7, &[2]),
    (8, &[10,1,4,7,5,8]),
    (7, &[2]),
    (4, &[2]),
    (2, &[10,-1,7,2,5]),
    (7, &[10,1,4,-7,2]),
    (7, &[10,1,4,7,5]),
    (1, &[10,1,-4,7,5]),
    (1, &[5]),
    (4, &[10,1,2]),
    (1, &[5]),
    (4, &[8]),
    (7, &[10,1,-4,5]),
    (4, &[8]),
    (7, &[10,-1,7,4,2]),
    (4, &[8]),
    (7, &[10,-1,7,5]),
    (4, &[8]),
    (1, &[5]),
    (4, &[10,-1,7,2]),
    (1, &[5]),
    (7, &[10,1]),
    (1, &[10,-1,7]),
    (0, &[10,-4,7]),
    (6, &[10,1,-4]),
    (0, &[10,-4,7]),
    (0, &[10,4,7]),
    (3, &[10,1,7]),
    (0, &[10,4,7]),
    (6, &[10,1,4]),
];
pub(crate) fn cycle_swap(circ:&mut Circuit,word:[&QReg;9],g:&QReg,dirty:&[QReg]){
    assert!(dirty.len()>=4);
    let mut ids:Vec<_>=word.iter().map(|q|q.id()).chain(std::iter::once(g.id())).chain(dirty.iter().map(QReg::id)).collect();
    ids.sort_unstable();assert!(ids.windows(2).all(|x|x[0]!=x[1]),"mod8 chart aliases a lender/guard");
    let owned=circ.b.next_qubit;let active=circ.b.active_qubits;
    for &(target,lits)in PLAN {
        let cs:Vec<_>=lits.iter().map(|&lit|{let index=lit.unsigned_abs()as usize-1;let q=if index==9{g}else{word[index]};(q,lit>0)}).collect();
        super::length_recompute::mixed_mcx(circ,&cs,word[target],dirty);
    }
    assert_eq!(circ.b.next_qubit,owned);assert_eq!(circ.b.active_qubits,active);
}
fn scalar(code:usize)->usize{
    let(t,b,v)=(code&7,code>>3&7,code>>6&7);
    if(t|v)&1==0{return code;}
    let(u,r)=if t&1!=0{(b,7usize.wrapping_sub(b*v).wrapping_mul(t)&7)}
      else{(7usize.wrapping_sub(t*b).wrapping_mul(v)&7,b)};
    assert_eq!((t*r+u*v)&7,7);
    u|((if u&1!=0{t}else{v})<<3)|(r<<6)
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
    let word=circ.alloc_qreg_bits("q793.mod8.chart",9);let g=circ.alloc_qreg("q793.mod8.guard");let dirty=circ.alloc_qreg_bits("q793.mod8.dirty",4);
    cycle_swap(&mut circ,std::array::from_fn(|i|&word[i]),&g,&dirty);
    let b=circ.into_builder();assert_eq!(b.next_qubit,14);
    assert!(b.ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)));
    let t=b.ops.iter().filter(|o|o.kind==K::CCX).count();assert_eq!(t,226);
    let mut rng=Fixed;let mut sim=Simulator::new(14,0,&mut rng);let mut lanes=0;
    for guard in 0..2{for pattern in 0..16{for first in(0..512).step_by(64){
        let mut before=vec![0u64;14];let mut expected=before.clone();
        for lane in 0..64{
            let code=first+lane;let mapped=scalar(code);assert_eq!(scalar(mapped),code);
            for (state,value)in[(&mut before,code),(&mut expected,if guard==1{mapped}else{code})]{
                for bit in 0..9{state[word[bit].id()as usize]|=(((value>>bit)&1)as u64)<<lane;}
                state[g.id()as usize]|=(guard as u64)<<lane;
                for bit in 0..4{state[dirty[bit].id()as usize]|=(((pattern>>bit)&1)as u64)<<lane;}
            }
        }
        sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,expected);assert_eq!(sim.phase,0);
        sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
    }}}
    eprintln!("Q793_MOD8_INTEGRATED_PRIMITIVE_PASS lanes={lanes} physical_interface=14 chart=9 guard=1 dirty=4 clean=0 T={t} ops={}; NOT wholeQ793 or9024",b.ops.len());
}

