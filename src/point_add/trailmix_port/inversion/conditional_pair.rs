//! MCX using a scratch bit known only when an external guard is1.
//! Greedy AND reduction derived from Khattar/Gidney arXiv:2407.17966v2,
//! theorem5.1 and section5.2. All gates are exact X/CX/CCX, no relative phase.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder;

/// target ^= guard * matched(other_guard) * product(others). Scratch must
/// equal known only when BOTH external guards match; arbitrary otherwise. Every control and lender restores.
/// No clean qubit is allocated. For n>=3 other controls:2n+4 Toffoli.
pub(super) fn guarded_pair(
    circ:&mut Circuit,guard:&QReg,other_guard:(&QReg,bool),others:&[(&QReg,bool)],target:&QReg,
    scratch:&QReg,known:bool,dirty:&[QReg],
) {
    assert!(dirty.len()>=2);let mut ids=vec![guard.id(),other_guard.0.id(),target.id(),scratch.id()];ids.extend(dirty[..2].iter().map(QReg::id));ids.extend(others.iter().map(|(q,_)|q.id()));ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"conditional MCX aliases");
    if !other_guard.1 {circ.x(other_guard.0);}
    for &(q,positive) in others {if !positive {circ.x(q);}}
    if others.len()<=2 {
        let mut controls=vec![guard,other_guard.0];controls.extend(others.iter().map(|&(q,_)|q));
        mcx_dirty_ladder(circ,&controls,target,&dirty[..2].iter().collect::<Vec<_>>());
    } else {
        if known {circ.x(scratch);}
        let mut wires=vec![scratch];wires.extend(others.iter().map(|&(q,_)|q));
        let mut marked=vec![false;wires.len()];marked[0]=true;
        let mut triples=Vec::new();
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
        assert_eq!(remaining.len(),2);assert_eq!(triples.len(),others.len()-2);
        for &(x,y,t) in &triples {circ.ccx(wires[x],wires[y],wires[t]);if t!=0 {circ.x(wires[t]);}}
        // Both guards remain explicit in the sole target action. If either is
        // false, compute and inverse cancel for arbitrary scratch/control data.
        mcx_dirty_ladder(circ,&[guard,other_guard.0,wires[remaining[0]],wires[remaining[1]]],target,&dirty[..2].iter().collect::<Vec<_>>());
        for &(x,y,t) in triples.iter().rev() {if t!=0 {circ.x(wires[t]);}circ.ccx(wires[x],wires[y],wires[t]);}
        if known {circ.x(scratch);}
    }
    for &(q,positive) in others.iter().rev() {if !positive {circ.x(q);}}
    if !other_guard.1 {circ.x(other_guard.0);}
}


/// Exhaustive small truth tables include an unknown scratch whenever either
/// external guard is off, which cannot be modelled as another reduced control.
pub fn run() {
    use crate::circuit::OperationType;use crate::sim::Simulator;use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    let mut total=0;
    for n in 0..=8 {for polarity in [false,true] {for known in [false,true] {
        let mut circ=Circuit::new();let others=circ.alloc_qreg_bits("others",n);let g=circ.alloc_qreg("g");let h=circ.alloc_qreg("h");let scratch=circ.alloc_qreg("scratch");let target=circ.alloc_qreg("target");let dirty=circ.alloc_qreg_bits("dirty",2);let owned=circ.b.next_qubit;
        let cs:Vec<_>=others.iter().enumerate().map(|(i,q)|(q,i%2==0)).collect();
        guarded_pair(&mut circ,&g,(&h,polarity),&cs,&target,&scratch,known,&dirty);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
        assert_eq!(b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),match n{0=>1,1=>4,2=>8,_=>2*n+4});
        for batch in 0..(1usize<<(n+6))/64 {
            let mut before=vec![0u64;owned as usize];let mut after=before.clone();
            for lane in 0..64 {let k=batch*64+lane;let gv=k>>n&1!=0;let hv=k>>(n+1)&1!=0;let on=gv&&(hv==polarity);let sv=if on{known}else{k>>(n+2)&1!=0};let tv=k>>(n+3)&1!=0;
                let mut flip=on;
                for i in 0..n {let v=k>>i&1!=0;flip&=v==(i%2==0);if v{before[others[i].id()as usize]|=1<<lane;}}
                for (q,v) in [(&g,gv),(&h,hv),(&scratch,sv),(&target,tv),(&dirty[0],k>>(n+4)&1!=0),(&dirty[1],k>>(n+5)&1!=0)] {if v{before[q.id()as usize]|=1<<lane;}}
                if flip{after[target.id()as usize]|=1<<lane;}
            }
            for i in 0..before.len(){after[i]^=before[i];}
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
    }}}
    eprintln!("CONDITIONAL_PAIR_PASS lanes={total}; both guards explicit, dirty off-domain scratch, exact phase and inverse");
}
