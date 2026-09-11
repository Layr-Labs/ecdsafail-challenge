//! Exact affine minterm differences, and symmetric clean-S XOR extensions.
//! Transfer's dirty extension is qualified only in a closed mirrored key walk.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

pub(super) fn transition(circ:&mut Circuit,word:&[&QReg],old:usize,new:usize,out:&QReg,scratch:Option<&[QReg]>,helpers:&[QReg]){
    let n=word.len();assert!((4..=6).contains(&n));assert!(old<1<<n&&new<1<<n&&old!=new);
    let mut ids:Vec<_>=word.iter().map(|q|q.id()).collect();ids.push(out.id());
    if let Some(s)=scratch{assert!(n<=5&&s.len()>=n-3);ids.extend(s.iter().map(QReg::id));}
    else{assert!(helpers.len()>=n-3);ids.extend(helpers[..n-3].iter().map(QReg::id));}
    ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"exit prefix alias");
    let diff=old^new;let pivot=diff.trailing_zeros()as usize;let targets:Vec<_>=(0..n).filter(|&i|i!=pivot&&diff>>i&1!=0).collect();let mut value=old;
    for &i in &targets{circ.cx(word[pivot],word[i]);if old>>pivot&1!=0{value^=1<<i;}}
    let cs:Vec<_>=(0..n).filter(|&i|i!=pivot).map(|i|(word[i],value>>i&1!=0)).collect();
    if let Some(s)=scratch{super::q794_transfer::exit_clean_toggle(circ,&cs,out,s);}
    else{super::length_recompute::mixed_mcx(circ,&cs,out,helpers);}
    for &i in targets.iter().rev(){circ.cx(word[pivot],word[i]);}
}

