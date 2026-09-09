//! Pure target-XOR extension of a one-clean-scratch MCX.
//! NOT a guarded MCX: arbitrary scratch can change its target predicate.
//! Call only with scratch zero, or within a separately proved matched pair.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

/// Exact AND on scratch=0; restores every other wire for arbitrary scratch.
/// No target-controlled gates, allocation, or relative phase. For n>=2:2n-3T.
pub(super) fn toggle(circ:&mut Circuit,controls:&[(&QReg,bool)],target:&QReg,scratch:&QReg) {
    let mut ids=vec![target.id(),scratch.id()];ids.extend(controls.iter().map(|(q,_)|q.id()));ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"paired clean MCX aliases");
    for &(q,p) in controls {if !p {circ.x(q);}}
    match controls.len() {
        0=>circ.x(target),1=>circ.cx(controls[0].0,target),2=>circ.ccx(controls[0].0,controls[1].0,target),
        n=>{
            let mut wires=vec![scratch];wires.extend(controls.iter().map(|&(q,_)|q));
            let mut marked=vec![false;wires.len()];marked[0]=true;let mut triples=Vec::new();
            loop {
                let mut choice=None;
                for t in (0..wires.len()).rev() {
                    if !marked[t] {continue;}
                    let unmarked:Vec<_>=(t+1..wires.len()).filter(|&i|!marked[i]).take(2).collect();
                    if unmarked.len()==2 {choice=Some((unmarked[0],unmarked[1],t));break;}
                }
                let Some((x,y,t))=choice else {break;};
                triples.push((x,y,t));marked[t]=false;marked[x]=true;marked[y]=true;
            }
            let remaining:Vec<_>=(0..wires.len()).filter(|&i|!marked[i]).collect();
            assert_eq!(remaining.len(),2);assert_eq!(triples.len(),n-2);
            for &(x,y,t) in &triples {circ.ccx(wires[x],wires[y],wires[t]);if t!=0 {circ.x(wires[t]);}}
            circ.ccx(wires[remaining[0]],wires[remaining[1]],target);
            for &(x,y,t) in triples.iter().rev() {if t!=0 {circ.x(wires[t]);}circ.ccx(wires[x],wires[y],wires[t]);}
        }
    }
    for &(q,p) in controls.iter().rev() {if !p {circ.x(q);}}
}

pub mod verification {
    use super::*;
    use crate::circuit::OperationType;
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed;
    impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    pub fn run() {
        let mut total=0usize;
        for n in 0..=12 {for mixed in [false,true] {
            let mut circ=Circuit::new();let controls=circ.alloc_qreg_bits("paired.controls",n);
            let target=circ.alloc_qreg("paired.target");let scratch=circ.alloc_qreg("paired.scratch");let owned=circ.b.next_qubit;
            let cs:Vec<_>=controls.iter().enumerate().map(|(i,q)|(q,!mixed||i%2==0)).collect();
            toggle(&mut circ,&cs,&target,&scratch);assert_eq!(circ.b.next_qubit,owned);
            let b=circ.into_builder();let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
            assert_eq!(t,if n<2{0}else{2*n-3});
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let cases=1usize<<(n+2);
            for batch in 0..cases.div_ceil(64) {
                let mut before=vec![0u64;owned as usize];let mut and=0u64;let mut clean=0u64;
                for lane in 0..64 {
                    let k=(batch*64+lane)%cases;let mut product=true;
                    for (i,&(q,p)) in cs.iter().enumerate() {let v=k>>i&1!=0;before[q.id() as usize]|=u64::from(v)<<lane;product&=v==p;}
                    before[scratch.id() as usize]|=u64::from(k>>n&1!=0)<<lane;
                    before[target.id() as usize]|=u64::from(k>>(n+1)&1!=0)<<lane;
                    and|=u64::from(product)<<lane;clean|=u64::from(k>>n&1==0)<<lane;
                }
                let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);
                sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
                for q in 0..owned as usize {if q!=target.id() as usize {assert_eq!(sim.qubits[q],before[q],"restoration n={n}");}}
                let delta=sim.qubits[target.id() as usize]^before[target.id() as usize];assert_eq!(delta&clean,and&clean,"clean AND n={n}");
                sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
                sim.qubits[target.id() as usize]^=u64::MAX;sim.apply_iter(b.ops.iter());
                assert_eq!(sim.qubits[target.id() as usize]^(before[target.id() as usize]^u64::MAX),delta,"target XOR n={n}");
                total+=64;
            }
        }}
        eprintln!("paired clean MCX PASS {total} lanes; exhaustive n0..12, mixed polarities, arbitrary scratch/output, clean AND, target-XOR extension, all lenders restored, exact phase/inverse");
    }
}
