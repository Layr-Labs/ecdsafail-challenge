//! R-side interval arithmetic for the shared LQ/LR EEA representation.
//! Uses the same six-sweep no-carry adder as shared_arithmetic. All endpoint
//! predicates are lowered to exact mixed-control X gates with dirty lenders.
use super::length_recompute::{above_cubes,below_cubes,mixed_mcx};
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

type Cube<'a>=Vec<(&'a QReg,bool)>;
fn eq<'a>(r:&'a[QReg],value:usize)->Vec<Cube<'a>> {
    if value>=1usize<<r.len() {Vec::new()} else {
        vec![r.iter().enumerate().map(|(i,q)|(q,(value>>i)&1!=0)).collect()]
    }
}
fn below<'a>(r:&'a[QReg],bound:usize)->Vec<Cube<'a>> {
    below_cubes(r.len(),bound).iter().map(|c|c.iter().map(|&(i,v)|(&r[i],v)).collect()).collect()
}
fn above<'a>(r:&'a[QReg],bound:usize)->Vec<Cube<'a>> {
    above_cubes(r.len(),bound).iter().map(|c|c.iter().map(|&(i,v)|(&r[i],v)).collect()).collect()
}
fn product<'a>(a:Vec<Cube<'a>>,b:Vec<Cube<'a>>)->Vec<Cube<'a>> {
    a.iter().flat_map(|x|b.iter().map(move |y|x.iter().chain(y).copied().collect())).collect()
}

/// Add/subtract the selected BE interval [start_raw+2, n-tail) in place.
/// Controls and metadata must describe a NONEMPTY interval on enabled lanes.
/// If n=2^width+3, (start_raw,tail_raw)=(0,0) denotes true tail=2^width,
/// the one-bit extreme R window. Other tail codes retain their usual value.
/// The independent sign bit optionally receives overflow/borrow XOR.
/// No clean wire is allocated, and source/passenger wires restore exactly.
pub fn interval_addsub(
    circ:&mut Circuit,source:&[QReg],target:&[QReg],start:&[QReg],tail:&[QReg],
    controls:&[&QReg],sign:Option<&QReg>,helpers:&[QReg],subtract:bool,
) {
    interval_addsub_impl(circ,source,target,start,tail,controls,sign,helpers,subtract,true,0,None);
}

fn interval_addsub_impl(
    circ:&mut Circuit,source:&[QReg],target:&[QReg],start:&[QReg],tail:&[QReg],
    controls:&[&QReg],sign:Option<&QReg>,helpers:&[QReg],subtract:bool,handle_wrap:bool,support_first:usize,shift_parity:Option<bool>,
) {
    if shift_parity.is_some() {assert_eq!(controls.len(),1);assert!(!handle_wrap);}
    let n=source.len();assert_eq!(target.len(),n);assert!(n>=3);
    assert_eq!(start.len(),tail.len());assert!(!start.is_empty() && start.len()<usize::BITS as usize);
    assert!(helpers.len()>=2*start.len()+controls.len());
    let mut ids:Vec<_>=source.iter().chain(target).chain(start).chain(tail).chain(helpers).map(QReg::id).collect();
    ids.extend(controls.iter().map(|q|q.id()));if let Some(q)=sign {ids.push(q.id());}
    ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"R interval aliases");
    let a:Vec<_>=source.iter().rev().collect();let b:Vec<_>=target.iter().rev().collect();
    let modulus=1usize<<tail.len();let wrapped=handle_wrap && n==modulus+3;
    let m=n-support_first;assert!(m>=2 && m<=n);
    // Tags: 0 interval support, 1 exact top, 2 exact top excluding singleton.
    // Interval support specifies lo<=min and max<hi in LE coordinates.
    let mut cells:Vec<(usize,usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    // Unconditional exterior CX sweeps cancel on every inactive/outside
    // lane. Only the lowest selected bit needs an S1 cancellation. The
    // source-chain conjugation cuts links immediately below/above that bit;
    // all extra upper/lower links cancel when the source is restored.
    for i in 0..m {cells.push((i,i,3,vec![a[i]],b[i]));}
    for i in 0..m {cells.push((i,i,4,vec![a[i]],b[i]));}
    if let Some(z)=sign {for i in (1..m).rev(){cells.push((i,i,2,vec![a[i]],z));}}
    for i in (0..m-1).rev() {
        cells.push((i,i,3,vec![a[i]],a[i+1]));
        cells.push((i,i,6,vec![a[i]],a[i+1]));
        cells.push((i+1,i+1,6,vec![a[i]],a[i+1]));
    }
    for i in 0..m {
        if i+1<m {cells.push((i,i+1,0,vec![a[i],b[i]],a[i+1]));}
        if let Some(z)=sign {cells.push((i,i,1,vec![a[i],b[i]],z));}
    }
    for i in (1..m).rev() {
        cells.push((i-1,i,0,vec![a[i]],b[i]));
        cells.push((i-1,i,0,vec![a[i-1],b[i-1]],a[i]));
    }
    for i in 0..m-1 {
        cells.push((i+1,i+1,6,vec![a[i]],a[i+1]));
        cells.push((i,i,6,vec![a[i]],a[i+1]));
        cells.push((i,i,3,vec![a[i]],a[i+1]));
    }
    for i in 0..m {cells.push((i,i,3,vec![a[i]],b[i]));}
    if subtract {cells.reverse();}
    let wrap=||product(eq(start,0),eq(tail,0));
    let singleton=|i:usize| {
        if i+3>n {return Vec::new();}
        if wrapped && i==modulus {wrap()}
        else {product(eq(start,n-i-3),eq(tail,i))}
    };
    let low_eq=|value:usize| {
        let mut c=eq(tail,value);
        if wrapped && (value==0 || value==modulus) {c.extend(wrap());}
        c
    };
    for (min,max,tag,gate_controls,out) in cells {
        let mut cubes=if tag==3 {vec![Vec::new()]}
        else if tag==4 || tag==6 {low_eq(max)}
        else if tag==0 {
            // For nonempty windows, threshold XOR equals the interval test,
            // except the width-one case of an inner adjacent-source cell.
            let mut c=below(tail,min+1);
            if wrapped && min<modulus {c.extend(wrap());}
            if max+3>n {c.push(Vec::new());}
            else {c.extend(above(start,n-max-3));}
            if max==min+2 {c.extend(singleton(min+1));}
            c
        } else if max+3<=n {eq(start,n-max-3)} else {Vec::new()};
        if tag==2 {cubes.extend(singleton(max));}
        for cube in cubes {
            let mut cs:Vec<_>=gate_controls.iter().map(|&q|(q,true)).collect();
            if tag!=3 && tag!=6 {cs.extend(controls.iter().map(|&q|(q,true)));}
            cs.extend(cube);
            if tag!=3 && tag!=6 {
                if let Some(known)=shift_parity {
                    // Under the arithmetic guard, LS0 is a schedule constant.
                    // Remove that factor before borrowing it as scratch. The
                    // unconditional source conjugation keeps its exact predicates.
                    if cs.iter().any(|(q,value)|q.id()==tail[0].id() && *value!=known) {continue;}
                    let others:Vec<_>=cs.into_iter().filter(|(q,positive)| {
                        if q.id()==controls[0].id() {assert!(*positive);false}
                        else {q.id()!=tail[0].id()}
                    }).collect();
                    super::conditional_mcx::guarded(circ,controls[0],&others,out,&tail[0],known,&helpers[0]);
                    continue;
                }
            }
            mixed_mcx(circ,&cs,out,helpers);
        }
    }
}

/// Algorithm-3 remainder subtraction/restoration after pre-shift and before
/// quotient exchange. Terminal LTtruth256 disables the whole R action.
pub fn remainder_block(
    circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],
    phase1:&QReg,phase2:&QReg,sign:&QReg,helpers:&[QReg],
) {
    remainder_block_with_support(circ,work1,work2,lt,shift,shared,phase1,phase2,sign,helpers,0,None);
}

/// The complete BE arithmetic interval must start at or after support_first.
/// Endpoint predicates keep the original 259-wire coordinate system.
pub(super) fn remainder_block_with_support(
    circ:&mut Circuit,work1:&[QReg],work2:&[QReg],lt:&[QReg],shift:&[QReg],shared:&[QReg],
    phase1:&QReg,phase2:&QReg,sign:&QReg,helpers:&[QReg],support_first:usize,shift_parity:Option<bool>,
) {
    use crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder;
    assert_eq!(work1.len(),259);assert_eq!(work2.len(),259);
    assert_eq!(lt.len(),8);assert_eq!(shift.len(),8);assert_eq!(shared.len(),8);assert!(helpers.len()>=19);
    let mut ids:Vec<_>=work1.iter().chain(work2).chain(lt).chain(shift).chain(shared)
        .chain(helpers).map(QReg::id).collect();ids.extend([phase1.id(),phase2.id(),sign.id()]);
    ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"R block aliases");
    let dirty:Vec<_>=helpers.iter().collect();let term:Vec<_>=lt.iter().collect();
    mcx_dirty_ladder(circ,&term,phase1,&dirty);circ.x(phase1);
    let add_lt=|circ:&mut Circuit,inverse:bool| {
        let mut cells=Vec::new();for i in 0..8 {for j in (i..8).rev(){cells.push((i,j));}}
        if inverse {cells.reverse();}
        for (i,j) in cells {let mut cs=vec![&lt[i]];cs.extend(shared[i..j].iter());mcx_dirty_ladder(circ,&cs,&shared[j],&dirty);}
    };
    let increment=|circ:&mut Circuit,inverse:bool| {
        let js:Vec<_>=if inverse {(0..8).collect()}else{(0..8).rev().collect()};
        for j in js {mcx_dirty_ladder(circ,&shared[..j].iter().collect::<Vec<_>>(),&shared[j],&dirty);}
    };
    add_lt(circ,false);increment(circ,false);
    // A wrapped tail occurs only at the first R peak: t=1, q=0, t'=0,
    // r'=1, true LS=256. The source is then exactly 2^256 in LE order.
    // Extending its one-bit interval down to zero adds only zero source bits;
    // target low bits and the top carry/borrow are unchanged. We can therefore
    // use the ordinary raw-tail interval on this proven EEA domain, removing
    // the generic sixteen-control wrap correction from every arithmetic cell.
    // The public interval helper retains full arbitrary-input wrap semantics.
    interval_addsub_impl(circ,work2,work1,shared,shift,&[phase1],Some(sign),helpers,true,false,support_first,shift_parity);
    circ.ccx(phase1,phase2,sign);
    // Reachable flags after R satisfy: an inactive phase10 has Sign=0.
    // Thus restore-enable equals Sign ? !Phase2 : R_enable. A negated
    // Fredkin stores that selector in the existing Phase1 wire, with Phase2
    // retaining the information needed for exact reversal. No clean flag.
    circ.x(phase2);circ.cswap(sign,phase1,phase2);circ.x(phase2);
    interval_addsub_impl(circ,work2,work1,shared,shift,&[phase1],None,helpers,false,false,support_first,shift_parity);
    circ.x(phase2);circ.cswap(sign,phase1,phase2);circ.x(phase2);
    increment(circ,true);add_lt(circ,true);
    circ.x(phase1);mcx_dirty_ladder(circ,&term,phase1,&dirty);
}

pub mod verification {
    use super::*;
    use crate::circuit::{OperationType,QubitId};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed;
    impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x35);}}
    fn rnd(s:&mut u64)->u64 {*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn set(words:&mut[u64],q:&QReg,lane:usize,bit:bool) {
        let x=&mut words[q.id() as usize];*x=(*x&!(1<<lane))|(u64::from(bit)<<lane);
    }
    pub fn run() {
        let mut total=0;
        for (n,width) in [(4usize,2usize),(5,1),(6,2),(7,2),(8,3),(16,4),(259,8)] {
            let modulus=1usize<<width;let mut pairs=Vec::new();
            for start in 0..modulus.min(n-2) {for tail in 0..modulus {
                let lo=if n==modulus+3 && start==0 && tail==0 {modulus}else{tail};
                let hi=n-start-2;if lo<hi {pairs.push((start,tail,lo,hi));}
            }}
            assert!(!pairs.is_empty());
            for subtract in [false,true] {for signed in [false,true] {
                let mut circ=Circuit::new();
                let a=circ.alloc_qreg_bits("interval.source",n);
                let breg=circ.alloc_qreg_bits("interval.target",n);
                let start=circ.alloc_qreg_bits("interval.start",width);
                let tail=circ.alloc_qreg_bits("interval.tail",width);
                let ctrl=circ.alloc_qreg("interval.control");let sign=circ.alloc_qreg("interval.sign");
                let helpers=circ.alloc_qreg_bits("interval.borrowed_passenger",2*width+2);
                let owned=circ.b.next_qubit;
                interval_addsub(&mut circ,&a,&breg,&start,&tail,&[&ctrl],signed.then_some(&sign),&helpers,subtract);
                assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();
                let variants=if n<=5 {1usize<<(2*n+2)}else{8};
                let cases=pairs.len()*variants;
                for batch in 0..cases.div_ceil(64) {
                    let mut random=0xe1935bd742cfa680u64^batch as u64;
                    let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut random)).collect();let mut expected=before.clone();
                    for lane in 0..64 {
                        let k=batch*64+lane;let (st,tl,lo,hi)=pairs[k%pairs.len()];let v=(k/pairs.len())%variants;
                        let on=if n<=5 {(v>>(2*n))&1!=0}else{v&1!=0};
                        let z=if n<=5 {(v>>(2*n+1))&1!=0}else{v&2!=0};
                        for words in [&mut before,&mut expected] {
                            set(words,&ctrl,lane,on);set(words,&sign,lane,z);
                            for (reg,value) in [(&start,st),(&tail,tl)] {for (j,q) in reg.iter().enumerate(){set(words,q,lane,(value>>j)&1!=0);}}
                        }
                        let mut carry=false;
                        for i in 0..n {
                            let aq=&a[n-1-i];let bq=&breg[n-1-i];
                            let av=if n<=5 {(v>>i)&1!=0}else if v&4!=0 {true}else{(before[aq.id() as usize]>>lane)&1!=0};
                            let bv=if n<=5 {(v>>(n+i))&1!=0}else if v&4!=0 {false}else{(before[bq.id() as usize]>>lane)&1!=0};
                            set(&mut before,aq,lane,av);set(&mut expected,aq,lane,av);set(&mut before,bq,lane,bv);
                            let out=if on && i>=lo && i<hi {
                                let out=av^bv^carry;
                                carry=if subtract {(!bv&&(av||carry))||(av&&carry)}else{(av&&bv)||(carry&&(av||bv))};out
                            }else{bv};set(&mut expected,bq,lane,out);
                        }
                        set(&mut expected,&sign,lane,z^(signed&&on&&carry));
                    }
                    let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
                    for (q,&word) in before.iter().enumerate(){*sim.qubit_mut(QubitId(q as u64))=word;}
                    sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
                    for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"interval n={n} sub={subtract} signed={signed} batch={batch} wire={q}");}
                    sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.phase,0);
                    for (q,&word) in before.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"interval inverse");}
                    total+=64;
                }
                let t=b.ops.iter().filter(|op|op.kind==OperationType::CCX).count();
                eprintln!("interval arithmetic n={n} width={width} sub={subtract} signed={signed} PASS {} endpoint pairs, T={t}, no clean allocation",pairs.len());
            }}
        }
        eprintln!("interval arithmetic TOTAL PASS {total} native lanes, singleton/wrap/source/dirty/sign/phase/reverse checked");
    }
}
