//! Shared-state EEA arithmetic with no allocated carry register.
//!
//! The six sweeps are the Takahashi–Tani–Kunihiro adder, arXiv:0910.2530,
//! section 2.2. This implementation adds quantum endpoint predicates to its
//! gates, lowering those predicates with restored dirty passenger lenders.
//! This is not yet the complete point-add route.
use super::length_recompute::{above_cubes,mixed_mcx};
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

/// Add/subtract a little-endian prefix of `source` into `target`. Its length
/// is `endpoint_raw + 2`, clipped to source.len() by the caller contract.
/// Optionally XOR carry-out (addition) / borrow-out (subtraction) into sign.
/// Endpoint and outer controls survive, including arbitrary initial sign.
/// No clean wire or carry wire is allocated. Source and dirty helpers restore.
pub fn prefix_addsub(
    circ:&mut Circuit,source:&[QReg],target:&[QReg],endpoint_raw:&[QReg],
    controls:&[&QReg],sign:Option<&QReg>,helpers:&[QReg],subtract:bool,
) {
    prefix_addsub_impl(circ,source,target,endpoint_raw,controls,sign,helpers,subtract,None);
}

fn prefix_addsub_impl(
    circ:&mut Circuit,source:&[QReg],target:&[QReg],endpoint_raw:&[QReg],
    controls:&[&QReg],sign:Option<&QReg>,helpers:&[QReg],subtract:bool,
    parity_loan:Option<(&QReg,bool)>,
) {
    if parity_loan.is_some() {assert_eq!(controls.len(),1);}
    let n=source.len();assert_eq!(target.len(),n);assert!(n>=2);
    assert!(!endpoint_raw.is_empty() && endpoint_raw.len()<usize::BITS as usize);
    assert!(helpers.len()>=endpoint_raw.len()+controls.len());
    let mut ids:Vec<_>=source.iter().chain(target).chain(endpoint_raw).chain(helpers).map(QReg::id).collect();
    ids.extend(controls.iter().map(|q|q.id()));if let Some(q)=sign {ids.push(q.id());}
    ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"prefix arithmetic aliases");
    // Each cell is a selected original gate, represented as (required highest
    // data index, exact-top predicate, original controls, original target).
    let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    // The exterior CX sweeps conjugate the selected arithmetic. Their
    // extra operations outside the prefix cancel after the source restores.
    for i in 0..n {cells.push((i,2,vec![&source[i]],&target[i]));}
    cells.push((0,3,vec![&source[0]],&target[0]));
    for i in (1..n).rev() {
        if let Some(z)=sign {cells.push((i,1,vec![&source[i]],z));}
        if i+1<n {cells.push((i+1,2,vec![&source[i]],&source[i+1]));}
    }
    for i in 0..n {
        if i+1<n {cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}
        if let Some(z)=sign {cells.push((i,1,vec![&source[i],&target[i]],z));}
    }
    for i in (1..n).rev() {
        cells.push((i,0,vec![&source[i]],&target[i]));
        cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));
    }
    for i in 1..n-1 {cells.push((i+1,2,vec![&source[i]],&source[i+1]));}
    for i in 0..n {cells.push((i,2,vec![&source[i]],&target[i]));}
    if subtract {cells.reverse();}
    for (i,tag,gate_controls,out) in cells {
        let cubes=if tag>=2 {vec![Vec::new()]} else if tag==1 {
            if i==0 || i-1>=1usize<<endpoint_raw.len() {Vec::new()}
            else {vec![(0..endpoint_raw.len()).map(|bit|(bit,((i-1)>>bit)&1!=0)).collect()]}
        } else if i<2 {vec![Vec::new()]}
        else {above_cubes(endpoint_raw.len(),i-2)};
        for cube in cubes {
            let mut cs:Vec<_>=gate_controls.iter().map(|&q|(q,true)).collect();
            if tag!=2 {cs.extend(controls.iter().map(|&q|(q,true)));}
            cs.extend(cube.iter().map(|&(bit,value)|(&endpoint_raw[bit],value)));
            if tag!=2 {
                if let Some((scratch,known))=parity_loan {
                    let others:Vec<_>=cs.into_iter().filter(|(q,positive)|{if q.id()==controls[0].id(){assert!(*positive);false}else{true}}).collect();
                    super::conditional_mcx::guarded(circ,controls[0],&others,out,scratch,known,&helpers[0]);
                    continue;
                }
            }
            mixed_mcx(circ,&cs,out,helpers);
        }
    }
}

/// Algorithm-3 coefficient block after quotient-bit exchange and before the
/// post-shift. L holds quotient length in phases 00/01/10 and residual length
/// in phase 11. The endpoint representation is physical prefix length minus
/// two, so all active T endpoints fit in eight bits without a carry register.
pub fn coefficient_block(
    circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],
    phase1:&QReg,phase2:&QReg,sign:&QReg,helpers:&[QReg],
) {
    coefficient_block_with_support(circ,work1,work2,lt,shift,shared,phase1,phase2,sign,helpers,259,None);
}

/// Schedule support must include the complete selected prefix, including carry.
pub(super) fn coefficient_block_with_support(
    circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],
    phase1:&QReg,phase2:&QReg,sign:&QReg,helpers:&[QReg],support_end:usize,shift_parity:Option<bool>,
) {
    assert!((2..=259).contains(&support_end));
    use crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder;
    assert_eq!(lt.len(),8);assert_eq!(shared.len(),8);assert_eq!(shift.len(),8);
    assert_eq!(work1.len(),259);assert_eq!(work2.len(),259);assert!(helpers.len()>=11);
    let mut ids:Vec<_>=work1.iter().chain(work2).chain(lt).chain(shift).chain(shared)
        .chain(helpers).map(QReg::id).collect();
    ids.extend([phase1.id(),phase2.id(),sign.id()]);ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"coefficient block aliases");
    let dirty:Vec<_>=helpers.iter().collect();
    let negate=|circ:&mut Circuit,inverse:bool| {
        if !inverse {for q in shared {circ.x(q);}}
        let order:Vec<_>=if inverse {(0..8).collect()}else{(0..8).rev().collect()};
        for j in order {mcx_dirty_ladder(circ,&shared[..j].iter().collect::<Vec<_>>(),&shared[j],&dirty);}
        if inverse {for q in shared {circ.x(q);}}
    };
    let shift_add=|circ:&mut Circuit,subtract:bool| {
        let mut cells=Vec::new();for i in 0..8 {for j in (i..8).rev(){cells.push((i,j));}}
        if subtract {cells.reverse();}
        for (i,j) in cells {
            let mut controls=vec![&shift[i]];controls.extend(shared[i..j].iter());
            mcx_dirty_ladder(circ,&controls,&shared[j],&dirty);
        }
    };
    negate(circ,false);shift_add(circ,true);
    for (a,b) in lt.iter().zip(shared) {circ.cswap(phase2,a,b);}
    // After quotient exchange, phase01 has Sign=0. On reachable states
    // T-subtract enable therefore equals Sign ? Phase2 : Phase1. Temporarily
    // select it with the existing phase wires; restore both after arithmetic.
    circ.cswap(sign,phase1,phase2);
    prefix_addsub_impl(circ,&work1[..support_end],&work2[..support_end],lt,&[phase1],None,helpers,true,shift_parity.map(|known|(&shift[0],known)));
    circ.cswap(sign,phase1,phase2);
    circ.cx(phase1,sign);
    prefix_addsub_impl(circ,&work1[..support_end],&work2[..support_end],lt,&[phase1],Some(sign),helpers,false,shift_parity.map(|known|(&shift[0],known)));
    for (a,b) in lt.iter().zip(shared).rev() {circ.cswap(phase2,a,b);}
    shift_add(circ,false);negate(circ,true);
}

pub mod verification {
    use super::*;
    use crate::circuit::{OperationType,QubitId};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed;
    impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x57);}}
    fn rnd(s:&mut u64)->u64 {*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn set(words:&mut[u64],q:&QReg,lane:usize,bit:bool) {
        let x=&mut words[q.id() as usize];*x=(*x&!(1<<lane))|(u64::from(bit)<<lane);
    }
    pub fn run() {
        let mut total=0;
        for n in [2usize,3,4,5,6,8,16,64,256,259] {
            for subtract in [false,true] {for signed in [false,true] {
                let width=if n>256 {9}else{8};
                let mut circ=Circuit::new();
                let a=circ.alloc_qreg_bits("prefix.source",n);
                let breg=circ.alloc_qreg_bits("prefix.target",n);
                let endpoint=circ.alloc_qreg_bits("prefix.endpoint",width);
                let ctrl=circ.alloc_qreg("prefix.control");
                let sign=circ.alloc_qreg("prefix.sign");
                let helpers=circ.alloc_qreg_bits("prefix.borrowed_passenger",width+2);
                let owned=circ.b.next_qubit;
                prefix_addsub(&mut circ,&a,&breg,&endpoint,&[&ctrl],signed.then_some(&sign),&helpers,subtract);
                assert_eq!(owned,circ.b.next_qubit,"clean carry allocated");
                let b=circ.into_builder();
                let cases=if n<=6 {(1usize<<(2*n+2))*(n-1)}else{64*(n-1).div_ceil(32)};
                for batch in 0..cases.div_ceil(64) {
                    let mut random=0x317df9ace826b504u64^batch as u64;
                    let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();
                    let mut expected=before.clone();
                    for lane in 0..64 {
                        let k=batch*64+lane;let end=2+k%(n-1);let v=k/(n-1);
                        let on=if n<=6 {(v>>(2*n))&1!=0}else{k&1!=0};
                        let z=if n<=6 {(v>>(2*n+1))&1!=0}else{rnd(&mut random)&1!=0};
                        for words in [&mut before,&mut expected] {
                            set(words,&ctrl,lane,on);set(words,&sign,lane,z);
                            for (bit,q) in endpoint.iter().enumerate(){set(words,q,lane,((end-2)>>bit)&1!=0);}
                        }
                        let mut carry=false;
                        for i in 0..n {
                            let av=if n<=6 {(v>>i)&1!=0}else{((before[a[i].id() as usize]>>lane)&1)!=0};
                            let bv=if n<=6 {(v>>(n+i))&1!=0}else{((before[breg[i].id() as usize]>>lane)&1)!=0};
                            set(&mut before,&a[i],lane,av);set(&mut expected,&a[i],lane,av);
                            set(&mut before,&breg[i],lane,bv);
                            let out=if on && i<end {
                                let out=av^bv^carry;
                                carry=if subtract {(!bv && (av||carry)) || (av&&carry)}else{(av&&bv)||(carry&&(av||bv))};out
                            }else{bv};
                            set(&mut expected,&breg[i],lane,out);
                        }
                        set(&mut expected,&sign,lane,z^(signed&&on&&carry));
                    }
                    let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
                    for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
                    sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
                    for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"prefix n={n} subtract={subtract} signed={signed} batch={batch} wire={q}");}
                    sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.phase,0);
                    for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"prefix inverse");}
                    total+=64;
                }
                let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
                eprintln!("prefix arithmetic n={n} subtract={subtract} signed={signed} PASS T={t}, no new clean wires");
            }}
        }
        eprintln!("prefix arithmetic TOTAL PASS {total} native lanes, source/dirty/phase/reverse restored");
    }
}
