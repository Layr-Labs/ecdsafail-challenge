//! One paid small-class/default flag, owned only between prefix preparation
//! return and A2. SM3 is zero on g&mask smallS, never assumed zero offcare.
//! Every SM2 parity/class producer returns before the next center; every
//! semantic A1 data operand returns before prefix/cache/SM3 cleanup.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::seed_ha_gate;

fn support(c:&Circuit)->(bool,bool){let(lo,hi)=c.q797_a_support.unwrap_or((0,256));((lo..hi).contains(&0),(lo..hi).contains(&1))}
pub(super) fn has_small(c:&Circuit)->bool{let(a,b)=support(c);a||b}
pub(super) fn begin(c:&mut Circuit,aa:&[QReg],flag:&QReg,g:&QReg)->Vec<crate::circuit::Op>{
    assert_eq!(aa.len(),8);let(a,b)=support(c);assert!(a||b);let at=c.b.ops.len();
    c.x(flag); // default = NOT selected(A0 OR A1), on the clean g&mask loan.
    if a&&b{
        let mut cs=vec![(g,true)];cs.extend(aa.iter().skip(1).map(|q|(q,false)));seed_ha_gate(c,&cs,flag,g);
    }else{
        let value=if a{0}else{1};let mut cs=vec![(g,true)];cs.extend(aa.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));seed_ha_gate(c,&cs,flag,g);
    }
    c.b.ops[at..].to_vec()
}
pub(super) fn small_cache(c:&mut Circuit,aa:&[QReg],default:&QReg,out:&QReg,value:usize){
    assert!(value<2);let(a,b)=support(c);assert!(if value==0{a}else{b});
    c.x(default);
    if a&&b{
        if value==0{c.x(&aa[0]);}c.ccx(default,&aa[0],out);if value==0{c.x(&aa[0]);}
    }else{c.cx(default,out);}
    c.x(default);
}

// Retained restoring Vandaele/Khattar-Gidney operand frame specialized to
// three bits, copied from q792_r01_seed_parity's source-bound comparator.
// Both output actions include mask/C0/class/t0. No helper or data port is
// treated as free; only the established g1 X(g)=0 output loan is reused.
fn compare3(c:&mut Circuit,a:[&QReg;3],b:[&QReg;3],base:&[(&QReg,bool)],out:&QReg,g:&QReg){
    for &q in &b{c.x(q);}
    for i in 1..3{c.cx(a[i],b[i]);}
    let mut cs=base.to_vec();cs.push((a[2],true));seed_ha_gate(c,&cs,out,g);
    c.cx(a[1],a[2]);
    for i in 0..2{c.ccx(a[i],b[i],a[i+1]);}
    let mut cs=base.to_vec();cs.extend([(a[2],true),(b[2],true)]);seed_ha_gate(c,&cs,out,g);
    for i in (0..2).rev(){c.ccx(a[i],b[i],a[i+1]);}
    c.cx(a[1],a[2]);
    for i in (1..3).rev(){c.cx(a[i],b[i]);}
    for &q in b.iter().rev(){c.x(q);}
}
const A1_ODD0:&[usize]=&[8,9,10,11,12,14,17,23,25,26,28,29,30,39,40,41,44,53,54,56,60,69,71,78,84,101,108];
pub(super) fn a1_head(c:&mut Circuit,word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,g:&QReg){
    assert_eq!(word.len(),11);
    // The physical v2 stores logical b2 on the even A1/S1 chart, and
    // logical v2 = 1 XOR b1 XOR q0. Prepare only that q0 data operand.
    // t0 is stable; coefficient head t1/t2 and b2 passenger are not read.
    c.cx(word[4],word[9]);c.x(word[9]);
    let mut even=base.to_vec();even.push((word[0],false));
    compare3(c,[word[6],word[7],word[9]],[word[3],word[4],word[8]],&even,ha,g);
    c.x(word[9]);c.cx(word[4],word[9]);
    // Odd logical t=3, b2=0. Seven independent physical source/prefix
    // bits suffice; polarity2 is fully paid and returned around the oracle.
    let inputs=[word[3],word[4],word[6],word[7],word[8],word[9],word[10]];
    c.x(inputs[1]);let mut odd=base.to_vec();odd.push((word[0],true));
    for &m in A1_ODD0{let mut cs=odd.clone();cs.extend(inputs.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));seed_ha_gate(c,&cs,ha,g);}
    c.x(inputs[1]);
}

// A2 keeps logical t2=1 while the physical bit is a parked passenger.
// The complete correction is t0*!physical_t2*(1 XOR b0*v0)*delta.
// Retain the original A2 class-SM2 producer and its literal return; SM3
// has already closed. Only the paid T1/B1 frame below changes, and it
// returns every operand/prefix on arbitrary inputs before the next class.
pub(super) fn a2_delta(c:&mut Circuit,word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,g:&QReg,shift:usize){
    assert_eq!(word.len(),11);assert!(shift<2);
    let mut factor=base.to_vec();factor.extend([(word[0],true),(word[2],false)]);
    if shift==0{
        // V2*(1 XOR B0*V0), with both physical XOR actions paid.
        let mut cs=factor.clone();cs.push((word[8],true));seed_ha_gate(c,&cs,ha,g);
        cs.extend([(word[3],true),(word[6],true)]);seed_ha_gate(c,&cs,ha,g);
        // T1' = T1 XOR B0 XOR V0*(B1 XOR Q0 XOR B0).
        c.cx(word[3],word[1]);c.cx(word[9],word[4]);c.cx(word[3],word[4]);
        c.ccx(word[6],word[4],word[1]);
        let mut cs=factor.clone();cs.extend([(word[7],true),(word[1],true)]);seed_ha_gate(c,&cs,ha,g);
        cs.extend([(word[3],true),(word[6],true)]);seed_ha_gate(c,&cs,ha,g);
        c.ccx(word[6],word[4],word[1]);
        c.cx(word[3],word[4]);c.cx(word[9],word[4]);c.cx(word[3],word[1]);
    }else{
        // delta = V1 XOR V0*(T1 XOR B1), under !B0*V0.
        let mut cs=factor.clone();cs.push((word[7],true));seed_ha_gate(c,&cs,ha,g);
        cs.extend([(word[3],true),(word[6],true)]);seed_ha_gate(c,&cs,ha,g);
        c.cx(word[1],word[4]);
        let mut cs=factor.clone();cs.extend([(word[6],true),(word[3],false),(word[4],true)]);seed_ha_gate(c,&cs,ha,g);
        c.cx(word[1],word[4]);
    }
}
