//! Paid endpoint class and original Clow frame across a complete R seed.
//! rank2 is zero only on inherited g&mask small-S care. It is never read by
//! any intervening old seed operator. Every frame closes before Q/carry.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::Op;
use super::{arithmetic,prefix_high_flag,seed_ha_gate};
pub(super) struct Frame{input:Vec<Op>,queries:Vec<Op>}

fn copy_filtered(c:&mut Circuit,flag:&QReg,root:&QReg,out:&QReg){
    c.x(flag);c.ccx(flag,root,out);c.x(flag);
}
fn repair(c:&mut Circuit,selectors:&[(&QReg,bool)],root:&QReg,reserved:&QReg,out:&QReg,g:&QReg){
    for q in [root,reserved]{let mut cs=vec![(g,true)];cs.extend_from_slice(selectors);cs.push((q,true));seed_ha_gate(c,&cs,out,g);}
}
pub(super) fn begin(circ:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,
                    roots:&[QReg],reserved:&QReg,shift:usize,c0:bool)->Option<Frame>{
    if shift>=2{return None;}assert_eq!(rank.len(),5);assert_eq!(sm.len(),4);
    let allow=|value:usize|circ.q797_a_support.map_or(true,|(lo,_)|lo<=value);
    let small1=allow(1);let small2=allow(2);
    if shift==1&&c0{
        // C odd always passes C>=1. Keep only hybrid parity: no six-bit
        // operand addition is needed. The M1 cache returns before the body.
        let q_at=circ.b.ops.len();circ.cx(&a[0],&cl[0]);
        let at=circ.b.ops.len();
        if small1{let cs:Vec<_>=std::iter::once((g,true)).chain(cl.iter().chain(rank[..2].iter()).enumerate().map(|(i,q)|(q,i==0))).collect();seed_ha_gate(circ,&cs,&sm[2],g);}
        let flag=circ.b.ops[at..].to_vec();circ.cx(&a[0],&cl[0]);
        circ.cx(&roots[1],&sm[0]);
        if small1{circ.ccx(&sm[2],&roots[1],&sm[0]);circ.ccx(&sm[2],reserved,&sm[0]);}
        circ.cx(&a[0],&cl[0]);circ.b.ops.extend(flag.into_iter().rev());circ.cx(&a[0],&cl[0]);
        return Some(Frame{input:Vec::new(),queries:circ.b.ops[q_at..].to_vec()});
    }
    // All other prefix queries share one original-Clow operand frame and
    // one rank2 endpoint class. Temporary SM3 flags return before the body.
    let input_at=circ.b.ops.len();circ.cx(&a[0],&cl[0]);arithmetic::add(circ,a,cl,None,true);
    let value=usize::from(c0);let high=prefix_high_flag(circ,rank,g,&sm[3],false);
    let mut cs=vec![(g,true),(&sm[3],true)];cs.extend(cl.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));
    seed_ha_gate(circ,&cs,&rank[2],g);circ.b.ops.extend(high.into_iter().rev());
    if c0{
        let high=prefix_high_flag(circ,rank,g,&sm[3],true);let mut cs=vec![(g,true),(&sm[3],true)];
        cs.extend(cl.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend(a.iter().map(|q|(q,true)));
        seed_ha_gate(circ,&cs,&rank[2],g);circ.b.ops.extend(high.into_iter().rev());
    }
    let input=circ.b.ops[input_at..].to_vec();let query_at=circ.b.ops.len();
    if shift==0&&c0{
        circ.cx(&roots[1],&sm[0]);
        if small1{let mut selectors=vec![(&rank[2],true)];selectors.extend(a.iter().map(|q|(q,false)));selectors.extend(rank[..2].iter().map(|q|(q,false)));
            repair(circ,&selectors,&roots[1],reserved,&sm[0],g);}
        copy_filtered(circ,&rank[2],&roots[0],&sm[1]);
    }else{
        copy_filtered(circ,&rank[2],&roots[1],&sm[0]);
        if shift==0{
            copy_filtered(circ,&rank[2],&roots[0],&sm[1]);
            if small2{let mut selectors:Vec<_>=a.iter().map(|q|(q,false)).collect();selectors.extend(cl.iter().enumerate().map(|(i,q)|(q,i==1)));selectors.extend(rank[..2].iter().map(|q|(q,false)));
                repair(circ,&selectors,&roots[0],reserved,&sm[1],g);}
        }
    }
    Some(Frame{input,queries:circ.b.ops[query_at..].to_vec()})
}
pub(super) fn close(c:&mut Circuit,frame:Frame){
    // The intervening complete seed is HA-only and returns every operand.
    // Therefore unguarded copies and all cache/operand loans cancel exactly
    // for arbitrary inactive ports. Original rank2/Clow return before Q/carry.
    c.b.ops.extend(frame.queries.into_iter().rev());c.b.ops.extend(frame.input.into_iter().rev());
}
