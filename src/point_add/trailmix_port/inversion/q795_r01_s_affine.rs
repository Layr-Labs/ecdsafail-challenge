//! Closed affine high-S oracle in the EXISTING lexicographic rank code.
//! One conditionally clean scratch; exact X/CX/CCX only, no allocation.
//! On arbitrary scratch this is a restored, pure target-XOR extension, not
//! necessarily the high-S predicate. Its caller retains the scratch selector.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

const TERMS: [&[u8];4] = [&[1,2,6,9,25,31],&[12,15,17,22],&[3,14,19,29],&[11,31]];
const FRAMES: [&[(i8,usize)];4] = [
    &[(-1,3),(4,0),(0,3),(0,4),(4,0),(-1,1),(2,3),(-1,3),(3,0),(3,2),(2,4),(4,1)],
    &[(3,2),(4,0),(4,2),(-1,2),(0,1),(-1,1),(1,4),(-1,4)],
    &[(1,3),(2,3),(1,0),(4,2)],
    &[(4,0),(4,1),(1,3)],
];

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],h:usize,target:&QReg,scratch:&QReg) {
    assert_eq!(rank.len(),5);assert!(h<4);
    let mut ids:Vec<_>=rank.iter().map(QReg::id).collect();ids.extend([target.id(),scratch.id()]);ids.sort_unstable();
    assert!(ids.windows(2).all(|w|w[0]!=w[1]),"high-S affine wire alias");
    for &(c,t) in FRAMES[h] {if c<0 {circ.x(&rank[t]);}else{circ.cx(&rank[c as usize],&rank[t]);}}
    for &m in TERMS[h] {
        let controls:Vec<_>=(0..5).filter(|&b|m>>b&1!=0).map(|b|(&rank[b],true)).collect();
        super::paired_clean_mcx::toggle(circ,&controls,target,scratch);
    }
    for &(c,t) in FRAMES[h].iter().rev() {if c<0 {circ.x(&rank[t]);}else{circ.cx(&rank[c as usize],&rank[t]);}}
}

pub(super) fn check_producers() {
    use crate::circuit::OperationType;
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut total=0;
    for h in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("affine.rank",5);
        let target=circ.alloc_qreg("affine.target");let scratch=circ.alloc_qreg("affine.scratch");let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,h,&target,&scratch);assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();let t=b.ops.iter().filter(|o|o.kind==OperationType::CCX).count();assert_eq!(t,[12,10,12,10][h]);
        for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        for batch in 0..2 {
            let mut before=vec![0u64;owned as usize];let mut wanted=0u64;let mut clean=0u64;
            for lane in 0..64 {let k=batch*64+lane;
                for bit in 0..5 {before[rank[bit].id() as usize]|=u64::from(k>>bit&1!=0)<<lane;}
                before[target.id() as usize]|=u64::from(k>>5&1!=0)<<lane;
                before[scratch.id() as usize]|=u64::from(k>>6&1!=0)<<lane;
                wanted|=u64::from(triples[k&31][2]==h)<<lane;clean|=u64::from(k>>6&1==0)<<lane;
            }
            let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            for q in 0..owned as usize {if q!=target.id() as usize {assert_eq!(sim.qubits[q],before[q]);}}
            let delta=sim.qubits[target.id() as usize]^before[target.id() as usize];assert_eq!(delta&clean,wanted&clean);assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
            sim.qubits[target.id() as usize]^=u64::MAX;sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits[target.id() as usize]^(before[target.id() as usize]^u64::MAX),delta);
            total+=64;
        }
        eprintln!("R01_S_AFFINE_PRODUCER h={h} T={t} ops={}",b.ops.len());
    }
    eprintln!("R01_S_AFFINE_PRODUCER_PASS {total} states: all rank, target and scratch; clean truth, all-wire restoration, arbitrary-scratch target-XOR, zero phase, inverse");
}
