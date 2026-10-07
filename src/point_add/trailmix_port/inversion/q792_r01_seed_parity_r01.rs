//! Paid parity/default cache inside the existing seed lifetime only.
//! SM2 is returned before every A-class cache and prefix cleanup; SM3 is
//! untouched. Arbitrary off-mask scratch is allowed by the masked HA center.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::seed_ha_gate;

const ODD0:&[usize]=&[60,67,70,73,76,102,103,104,106,110,113,116,117,120,130,132,165,166,173,176,193,197,200,229,232,293,301,308,321,324,352,354,358,364,365,368,417,421,424,448,480,556,609,612,613,616,672,804,864];
const ODD1:&[usize]=&[39,46,53,56,66,68,72,96,98,101,102,105,116,168,172,192,196,224,228,293,296,356];
const ODD2:&[usize]=&[34,37,38,45,48,101,104,108,164];

fn cache(c:&mut Circuit,aa:&[QReg],t0:&QReg,out:&QReg,g:&QReg,odd:bool)->Vec<crate::circuit::Op>{
    let at=c.b.ops.len();
    // On g&mask, SM2 starts0 and becomes parity AND NOT(A0 OR A1).
    // Cache producers use the same genuine X(g)=0 helper as the seed.
    // Outside this care they remain pure cache-XOR and are reversed before
    // another consumer; only the HA action observes the mask/C0 guard.
    seed_ha_gate(c,&[(g,true),(t0,odd)],out,g);
    let support=c.q797_a_support.unwrap_or((0,256));
    if (support.0..support.1).contains(&0)&&(support.0..support.1).contains(&1){
        let mut cs=vec![(g,true),(t0,odd)];cs.extend(aa.iter().skip(1).map(|q|(q,false)));seed_ha_gate(c,&cs,out,g);
    }else{for ac in 0..2{if (support.0..support.1).contains(&ac){
        let mut cs=vec![(g,true),(t0,odd)];cs.extend(aa.iter().enumerate().map(|(i,q)|(q,ac>>i&1!=0)));seed_ha_gate(c,&cs,out,g);
    }}}
    c.b.ops[at..].to_vec()
}

// Restoring Vandaele/Khattar-Gidney comparator specialized to2/3bits.
// The retained project's q792_r01_sumchart carry uses the same elementary
// operand frame. Only its two output actions receive the full seed guard.
// out ^= base AND [a>b], with all operand/control ports literally restored.
fn compare(c:&mut Circuit,a:&[&QReg],b:&[&QReg],base:&[(&QReg,bool)],out:&QReg,g:&QReg){
    let n=a.len();assert!(n==2||n==3);assert_eq!(b.len(),n);
    for &q in b{c.x(q);}
    for i in 1..n{c.cx(a[i],b[i]);}
    let mut cs=base.to_vec();cs.push((a[n-1],true));seed_ha_gate(c,&cs,out,g);
    for i in (2..n).rev(){c.cx(a[i-1],a[i]);}
    for i in 0..n-1{c.ccx(a[i],b[i],a[i+1]);}
    let mut cs=base.to_vec();cs.extend([(a[n-1],true),(b[n-1],true)]);seed_ha_gate(c,&cs,out,g);
    for i in (0..n-1).rev(){c.ccx(a[i],b[i],a[i+1]);}
    for i in 2..n{c.cx(a[i-1],a[i]);}
    for i in (1..n).rev(){c.cx(a[i],b[i]);}
    for &q in b.iter().rev(){c.x(q);}
}

pub(super) fn emit(c:&mut Circuit,aa:&[QReg],word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,sm2:&QReg,g:&QReg,shift:usize){emit_impl(c,aa,word,base,ha,sm2,g,shift,None);}

pub(super) fn emit_cached(c:&mut Circuit,word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,sm2:&QReg,g:&QReg,shift:usize,default:&QReg){emit_impl(c,&[],word,base,ha,sm2,g,shift,Some(default));}

fn cache_input(c:&mut Circuit,aa:&[QReg],t0:&QReg,out:&QReg,g:&QReg,odd:bool,default:Option<&QReg>)->Vec<crate::circuit::Op>{
    if let Some(d)=default{
        let at=c.b.ops.len();if !odd{c.x(t0);}c.ccx(d,t0,out);if !odd{c.x(t0);}c.b.ops[at..].to_vec()
    }else{cache(c,aa,t0,out,g,odd)}
}

fn emit_impl(c:&mut Circuit,aa:&[QReg],word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,sm2:&QReg,g:&QReg,shift:usize,default:Option<&QReg>){
    assert_eq!(word.len(),11);assert!(default.is_some()||aa.len()==8);assert!(shift<3);
    let mut selected=base.to_vec();selected.push((sm2,true));
    let even=cache_input(c,aa,word[0],sm2,g,false,default);
    match shift{
        0=>compare(c,&word[6..9],&word[3..6],&selected,ha,g),
        1=>compare(c,&word[6..8],&word[4..6],&selected,ha,g),
        2=>{let mut cs=selected.clone();cs.extend([(word[6],true),(word[5],false)]);seed_ha_gate(c,&cs,ha,g);},
        _=>unreachable!(),
    }
    c.b.ops.extend(even.into_iter().rev());
    let odd=cache_input(c,aa,word[0],sm2,g,true,default);
    if shift==0{odd0_arithmetic(c,word,&selected,ha,g);}else if shift==1{odd1_arithmetic(c,word,&selected,ha,g);}else{
    let (pol,terms)=(0,ODD2);
    for (i,&q) in word[1..].iter().enumerate(){if pol>>i&1!=0{c.x(q);}}
    for &m in terms{let mut cs=selected.clone();cs.extend(word[1..].iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));seed_ha_gate(c,&cs,ha,g);}
    for (i,&q) in word[1..].iter().enumerate().rev(){if pol>>i&1!=0{c.x(q);}}
    }
    c.b.ops.extend(odd.into_iter().rev());
}

// Default odd-sh0 arithmetic: R=(-(1+B*V)*Todd-Q*V) mod8, with
// Todd=(physicalT&6)|1 and Q=2q0+4q1. Stable P=B0*V0 splits the
// low remainder bit: P0 has R0=1 and compares highbits strictly;
// P1 has R0=0,V0=1 and compares highbits with <=. Both branch
// predicates and comparator outputs are paid. The captured T1/T2 or
// B1/B2 operand frame returns literally before the old SM2 odd-cache
// return; SM3 and all prefix/phase/caller ownership remain untouched.
fn odd0_arithmetic(c:&mut Circuit,word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,g:&QReg){
    assert_eq!(word.len(),11);
    let mut p1=base.to_vec();p1.extend([(word[3],true),(word[6],true)]);
    // P0: triangular odd-coefficient permutation of T1/T2 into R1/R2.
    let at=c.b.ops.len();
    c.ccx(word[4],word[6],word[1]);c.ccx(word[3],word[7],word[1]);
    c.ccx(word[9],word[6],word[1]);c.x(word[1]);
    c.ccx(word[5],word[6],word[2]);c.ccx(word[4],word[7],word[2]);
    c.ccx(word[3],word[8],word[2]);c.ccx(word[10],word[6],word[2]);
    c.ccx(word[9],word[7],word[2]);c.x(word[2]);
    seed_ha_gate(c,&[(g,true),(word[1],true),(word[9],true),(word[6],true)],word[2],g);
    let frame=c.b.ops[at..].to_vec();
    // base XOR base*B0*V0 gives the exact P0 selector for arbitrarycache.
    compare(c,&[word[7],word[8]],&[word[1],word[2]],base,ha,g);
    compare(c,&[word[7],word[8]],&[word[1],word[2]],&p1,ha,g);
    c.b.ops.extend(frame.into_iter().rev());
    // P1: B0=V0=1. R highbits are a triangular B1/B2 permutation;
    // T2 and both low branch inputs are never mutated or read as zero.
    let at=c.b.ops.len();
    c.cx(word[8],word[5]);c.cx(word[10],word[5]);c.cx(word[1],word[5]);c.x(word[5]);
    c.ccx(word[1],word[4],word[5]);c.ccx(word[1],word[7],word[5]);c.ccx(word[9],word[4],word[5]);
    c.cx(word[7],word[4]);c.cx(word[9],word[4]);c.x(word[4]);
    let frame=c.b.ops[at..].to_vec();
    seed_ha_gate(c,&p1,ha,g);
    compare(c,&[word[4],word[5]],&[word[7],word[8]],&p1,ha,g);
    c.b.ops.extend(frame.into_iter().rev());
}

// Default odd-sh1: R=(-(1+B*V)*Todd-4q0*V) mod8, threshold2*(V&3).
// Both low remainder parities reduce to Rhigh<(V&3). Stable P=B0*V0
// pays the two branch selectors through the retained restoring comparator.
// Every triangular operand frame returns before the original oddSM2 cache
// inverse. No SM3/phase/helper/branch-flag ownership or caller changes.
fn odd1_arithmetic(c:&mut Circuit,word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,g:&QReg){
    assert_eq!(word.len(),11);
    let mut p1=base.to_vec();p1.extend([(word[3],true),(word[6],true)]);
    // P0: T1/T2 become the high remainder using six quadratic products.
    let at=c.b.ops.len();
    c.ccx(word[4],word[6],word[1]);c.ccx(word[3],word[7],word[1]);c.x(word[1]);
    c.ccx(word[5],word[6],word[2]);c.ccx(word[4],word[7],word[2]);
    c.ccx(word[3],word[8],word[2]);c.ccx(word[9],word[6],word[2]);c.x(word[2]);
    let frame=c.b.ops[at..].to_vec();
    compare(c,&[word[6],word[7]],&[word[1],word[2]],base,ha,g);
    compare(c,&[word[6],word[7]],&[word[1],word[2]],&p1,ha,g);
    c.b.ops.extend(frame.into_iter().rev());
    // P1: B0=V0=1. Two quadratic terms prepare the high remainder.
    // V0 is the comparator's unchanged low operand and branch control.
    let at=c.b.ops.len();
    c.cx(word[8],word[5]);c.cx(word[9],word[5]);c.cx(word[1],word[5]);c.x(word[5]);
    c.ccx(word[1],word[4],word[5]);c.ccx(word[1],word[7],word[5]);
    c.cx(word[7],word[4]);c.x(word[4]);
    let frame=c.b.ops[at..].to_vec();
    compare(c,&[word[6],word[7]],&[word[4],word[5]],&p1,ha,g);
    c.b.ops.extend(frame.into_iter().rev());
}
