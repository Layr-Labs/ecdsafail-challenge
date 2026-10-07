//! Three adjacent addressed Work1 rails, keeping Work1[0..2] fixed.
//! Each paid window closes before carry or before the external A-pad return.
//! All unused ports and every borrowed input return by the literal inverse.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::Op;
use super::{gate,seed_ha_gate,prefix_high_flag,arithmetic};

/// Disjoint even/odd four-rail block muxes, followed by a paid local rotation.
/// Port0/1/2 hold W1[M/M+1/M+2] whenever that source index is at least3.
/// Reserved missing Work1[2] is handled explicitly by prefix/Q consumers.
pub(super) fn route(c:&mut Circuit,m:&[QReg],w:&[QReg],d:&[QReg])->(Vec<QReg>,Vec<Op>){
    assert_eq!(m.len(),8);assert_eq!(w.len(),259);let start=c.b.ops.len();
    let lo=c.q797_a_support.map_or(0,|(lo,_)|lo.min(253)).max(3);
    let mut lanes:Vec<Vec<Option<&QReg>>>=Vec::new();
    for parity in 0..2{for r in 0..4{
        let mut nodes:Vec<_>=(0..32).map(|k|{let at=8*k+4*parity+r;(at>=lo).then_some(&w[at])}).collect();
        if nodes.iter().all(Option::is_none){let dummy=if parity==0&&r<3{8+r}else{4*parity+r};assert!(dummy>=3);nodes[(dummy-4*parity-r)/8]=Some(&w[dummy]);}
        lanes.push(nodes);
    }}
    let need_increment=lanes[..4].iter().any(|v|v.iter().filter(|x|x.is_some()).count()>1);
    let mut roots=Vec::new();
    for parity in 0..2{
        let inc_at=c.b.ops.len();
        if parity==0&&need_increment{for bit in (0..5).rev(){let mut cs=vec![(&m[2],true)];cs.extend(m[3..3+bit].iter().map(|q|(q,true)));gate(c,&cs,&m[3+bit],d);}}
        let increment=c.b.ops[inc_at..].to_vec();
        for r in 0..4{
            let mut nodes=lanes[4*parity+r].clone();
            for bit in 0..5{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
                (Some(left),Some(right))=>{c.cswap(&m[3+bit],left,right);Some(left)},
                (Some(q),None)|(None,Some(q))=>Some(q),_=>None,
            });}nodes=next;}
            roots.push(nodes[0].unwrap().borrowed_alias());
        }
        if parity==0{c.b.ops.extend(increment.into_iter().rev());}
    }
    let mut ids:Vec<_>=roots.iter().map(QReg::id).collect();ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
    for r in 0..4{c.cswap(&m[2],&roots[r],&roots[r+4]);}
    for r in 0..7{c.cswap(&m[0],&roots[r],&roots[r+1]);}
    for (a,b)in [(0,2),(2,4),(4,6),(1,3),(3,5),(5,7)]{c.cswap(&m[1],&roots[a],&roots[b]);}
    (roots,c.b.ops[start..].to_vec())
}

fn loan(c:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,g:&QReg){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v)in cs{assert_ne!(q.id(),out.id());if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}else{unique.push((q,v));}}
    // X(g) is genuine zero on all active R states, including mask0. The
    // dirty offguard extension is paired before/after the HA-only seed.
    seed_ha_gate(c,&unique,out,g);
}

/// C enters/returns with original C0 and all other M_low bits. The window
/// route is already open; only the paid operand/selector frame lives here.
pub(super) fn prefix(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],root:&QReg,w1_reserved:&QReg,
                    base:&[(&QReg,bool)],out:&QReg,offset:usize,needed:usize,c0:bool,g:&QReg,d:&[QReg]){
    assert!(offset<=1&&(1..=2).contains(&needed));
    let small=if offset==1&&c0{Some(1usize)}else if offset==0&&!c0{Some(2)}else{None};
    let small=small.filter(|&value|circ.q797_a_support.map_or(true,|(lo,_)|lo<=value));
    circ.cx(&a[0],&c[0]); // Hybrid parity -> literal M_low.
    let m:Vec<_>=c.iter().chain(rank[..2].iter()).collect();
    let flag_at=circ.b.ops.len();
    if let Some(value)=small{let mut cs=vec![(g,true),(base[1].0,true)];cs.extend(m.iter().enumerate().map(|(i,&q)|(q,value>>i&1!=0)));gate(circ,&cs,&sm[2],d);}
    let small_flag=circ.b.ops[flag_at..].to_vec();
    arithmetic::add(circ,a,c,None,true); // Original C_low for endpoint gates.
    let mut terms=vec![(root,false)];if small.is_some(){terms.extend([(root,true),(w1_reserved,true)]);}
    let consume=|circ:&mut Circuit,tail:&[(&QReg,bool)]|{
        for &(q,correct)in &terms{let mut cs=base.to_vec();cs.push((q,true));if correct{cs.push((&sm[2],true));}cs.extend_from_slice(tail);loan(circ,&cs,out,g);}
    };
    consume(circ,&[]);
    for absent in 0..needed{
        if (absent&1!=0)!=c0{continue;}
        let high=prefix_high_flag(circ,rank,g,&sm[3],false);
        let mut tail=vec![(&sm[3],true)];tail.extend(c.iter().enumerate().map(|(i,q)|(q,absent>>i&1!=0)));consume(circ,&tail);
        circ.b.ops.extend(high.into_iter().rev());
        if absent==1{
            let high=prefix_high_flag(circ,rank,g,&sm[3],true);
            let mut tail=vec![(&sm[3],true)];tail.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));tail.extend(a.iter().map(|q|(q,true)));consume(circ,&tail);
            circ.b.ops.extend(high.into_iter().rev());
        }
    }
    arithmetic::add(circ,a,c,None,false);
    circ.b.ops.extend(small_flag.into_iter().rev());circ.cx(&a[0],&c[0]);
}

fn swap(c:&mut Circuit,cs:&[(&QReg,bool)],left:&QReg,right:&QReg,d:&[QReg]){
    c.cx(right,left);let mut ex=cs.to_vec();ex.push((left,true));gate(c,&ex,right,d);c.cx(right,left);
}
/// Exact guarded quotient SWAP, including arbitrary incoming decision.
/// M0's missing windowrail is Work1[2]; cancel the dummy center first.
pub(super) fn quotient(c:&mut Circuit,rank:&[QReg],cl:&[QReg],roots:&[QReg],w:&[QReg],g:&QReg,decision:&QReg,d:&[QReg]){
    c.cswap(g,&roots[2],decision);
    if c.q797_a_support.map_or(true,|(lo,_)|lo==0){
        let mut cs=vec![(g,true)];cs.extend(cl.iter().chain(rank[..2].iter()).map(|q|(q,false)));
        swap(c,&cs,&roots[2],decision,d);swap(c,&cs,&w[2],decision,d);
    }
}
