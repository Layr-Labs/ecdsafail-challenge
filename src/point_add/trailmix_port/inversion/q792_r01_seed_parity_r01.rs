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

pub(super) fn emit(c:&mut Circuit,aa:&[QReg],word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,sm2:&QReg,g:&QReg,shift:usize){
    assert_eq!(word.len(),11);assert_eq!(aa.len(),8);assert!(shift<3);
    let mut selected=base.to_vec();selected.push((sm2,true));
    let even=cache(c,aa,word[0],sm2,g,false);
    match shift{
        0=>compare(c,&word[6..9],&word[3..6],&selected,ha,g),
        1=>compare(c,&word[6..8],&word[4..6],&selected,ha,g),
        2=>{let mut cs=selected.clone();cs.extend([(word[6],true),(word[5],false)]);seed_ha_gate(c,&cs,ha,g);},
        _=>unreachable!(),
    }
    c.b.ops.extend(even.into_iter().rev());
    let odd=cache(c,aa,word[0],sm2,g,true);
    let (pol,terms)=match shift{0=>(0,ODD0),1=>(150,ODD1),2=>(0,ODD2),_=>unreachable!()};
    for (i,&q) in word[1..].iter().enumerate(){if pol>>i&1!=0{c.x(q);}}
    for &m in terms{let mut cs=selected.clone();cs.extend(word[1..].iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));seed_ha_gate(c,&cs,ha,g);}
    for (i,&q) in word[1..].iter().enumerate().rev(){if pol>>i&1!=0{c.x(q);}}
    c.b.ops.extend(odd.into_iter().rev());
}
