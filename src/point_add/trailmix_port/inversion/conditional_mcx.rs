//! MCX using a scratch bit known only when an external guard is1.
//! Greedy AND reduction derived from Khattar/Gidney arXiv:2407.17966v2,
//! theorem5.1 and section5.2. All gates are exact X/CX/CCX, no relative phase.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder;

/// target ^= guard * product(others). Scratch must equal known iff guard=1;
/// its value is unrestricted when guard=0. Every control and lender restores.
/// No clean qubit is allocated. For k>=4 total controls:2k-2 Toffoli.
pub(super) fn guarded(
    circ:&mut Circuit,guard:&QReg,others:&[(&QReg,bool)],target:&QReg,
    scratch:&QReg,known:bool,dirty:&QReg,
) {
    let mut ids=vec![guard.id(),target.id(),scratch.id(),dirty.id()];ids.extend(others.iter().map(|(q,_)|q.id()));ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"conditional MCX aliases");
    for &(q,positive) in others {if !positive {circ.x(q);}}
    if others.len()<=2 {
        let mut controls=vec![guard];controls.extend(others.iter().map(|&(q,_)|q));
        mcx_dirty_ladder(circ,&controls,target,&[dirty]);
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
        // The sole target action includes guard. When guard=0, the compute
        // and its literal inverse cancel for arbitrary scratch/control data.
        mcx_dirty_ladder(circ,&[guard,wires[remaining[0]],wires[remaining[1]]],target,&[dirty]);
        for &(x,y,t) in triples.iter().rev() {if t!=0 {circ.x(wires[t]);}circ.ccx(wires[x],wires[y],wires[t]);}
        if known {circ.x(scratch);}
    }
    for &(q,positive) in others.iter().rev() {if !positive {circ.x(q);}}
}

pub mod verification {
    use super::*;
    use crate::circuit::OperationType;
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed;
    impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    fn rnd(s:&mut u64)->u64 {*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(words:&mut[u64],q:&QReg,lane:usize,bit:bool){let v=&mut words[q.id() as usize];*v=(*v&!(1u64<<lane))|(u64::from(bit)<<lane);}
    pub fn run() {
        let mut total=0usize;
        for n in [0usize,1,2,3,4,5,6,7,8,12,24,32] {for known in [false,true] {for mixed in [false,true] {
            let mut circ=Circuit::new();let controls=circ.alloc_qreg_bits("conditional.controls",n);
            let guard=circ.alloc_qreg("conditional.guard");let target=circ.alloc_qreg("conditional.target");
            let scratch=circ.alloc_qreg("conditional.scratch");let dirty=circ.alloc_qreg("conditional.dirty");let owned=circ.b.next_qubit;
            let others:Vec<_>=controls.iter().enumerate().map(|(i,q)|(q,!mixed || i%2==0)).collect();
            guarded(&mut circ,&guard,&others,&target,&scratch,known,&dirty);
            assert_eq!(circ.b.next_qubit,owned);
            let b=circ.into_builder();let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
            let expected_t=match n {0|1=>0usize.max(n),2=>4,_=>2*n};assert_eq!(t,expected_t);
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let cases=if n<=8 {1usize<<(n+4)}else{256};
            for batch in 0..cases.div_ceil(64) {
                let mut random=0x7e8149a53f60bd22u64^batch as u64;
                let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();let mut expected=before.clone();
                for lane in 0..64 {
                    let k=batch*64+lane;let on=if n<=8 {(k>>n)&1!=0}else{k%3!=0};
                    let scratch_bit=if on {known}else{if n<=8 {(k>>(n+1))&1!=0}else{k%2!=0}};
                    let out=if n<=8 {(k>>(n+2))&1!=0}else{k%2!=0};
                    let lender=if n<=8 {(k>>(n+3))&1!=0}else{k%5!=0};
                    let mut and=on;
                    for (i,&(q,positive)) in others.iter().enumerate() {
                        let value=if n<=8 {(k>>i)&1!=0}else{if k%(n+1)==i+1 {!positive}else{positive}};
                        put(&mut before,q,lane,value);put(&mut expected,q,lane,value);and&=value==positive;
                    }
                    for (q,value) in [(&guard,on),(&scratch,scratch_bit),(&dirty,lender)] {put(&mut before,q,lane,value);put(&mut expected,q,lane,value);}
                    put(&mut before,&target,lane,out);put(&mut expected,&target,lane,out^and);
                }
                let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits.copy_from_slice(&before);
                sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);assert_eq!(sim.qubits,expected,"conditional MCX n={n} known={known} mixed={mixed} batch={batch}");
                sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.phase,0);assert_eq!(sim.qubits,before,"conditional inverse n={n}");
                total+=64;
            }
        }}}
        eprintln!("conditional clean MCX PASS {total} lanes;0..32 other controls, both known values, mixed polarities, arbitrary scratch when guard0, dirty restored, exact phase and reverse, zero new clean qubits");
    }
}
