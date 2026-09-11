//! Quarter-step cycle exit using a global padding loan and relocated passenger data.
//! Caller supplies post-entry state at j0, before S-zero phase flips.
//! Work1[A_raw+1] must be0 globally, including already-terminal inputs.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_remainder5_programs.rs"] mod programs;
fn triples()->Vec<[usize;3]> {
    (0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()
}
// axis0: Work[A_raw+1]; axis1: Work[259-C]. The latter is used only under
// the exit guard (S0,C1..255), so S0 rank rows suffice for its high selector.
fn addressed(circ:&mut Circuit,rank:&[QReg],low:&[QReg],guard:Option<&QReg>,passenger:Option<&QReg>,word:&[QReg],helpers:&[QReg],axis:usize) {
    if axis==0&&guard.is_none(){if let Some(p)=passenger{
        let(q,ops)=super::q798_handoffs::gather_a(circ,rank,low,word,1,helpers);
        circ.cx(q,p);circ.cx(p,q);circ.cx(q,p);circ.b.ops.extend(ops.into_iter().rev());return;
    }}
    let flag=&helpers[0];let dirty=&helpers[1..];
    for h in 0..4 {for _echo in 0..2 {
        let cubes:Vec<_>=if axis==0 {programs::EQUAL[h].to_vec()} else {
            triples().iter().enumerate().filter(|(_,t)|t[1]==h&&t[2]==0).map(|(r,_)|(31u16,r as u16)).collect()
        };
        for (m,v) in cubes {
            let mut cs=Vec::new();if let Some(g)=guard{cs.push((g,true));}cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,flag,dirty);
        }
        for lo in 0..64 {
            let value=64*h+lo;if axis==1&&value==0{continue;}
            let target=&word[if axis==0 {value+1}else{259-value}];
            let mut cs=vec![(flag,true)];if let Some(g)=guard{cs.push((g,true));}cs.extend((0..6).map(|i|(&low[i],lo>>i&1!=0)));
            if let Some(p)=passenger {circ.cx(target,p);cs.push((p,true));mixed_mcx(circ,&cs,target,dirty);circ.cx(target,p);}
            else {mixed_mcx(circ,&cs,target,dirty);}
        }
    }}
}
// Under the independent exit guard S_mid is0: cache the high selector and
// use another S bit as conditional clean MCX scratch. Both restore off guard.
fn selected_exit(circ:&mut Circuit,rank:&[QReg],low:&[QReg],sm:&[QReg],g:&QReg,passenger:Option<&QReg>,word:&[QReg],helpers:&[QReg],axis:usize) {
    if axis==0{if let Some(p)=passenger{
        super::q797_cargo_moves::exchange_a(circ,rank,low,word,1,p,&[(g,true)],helpers);return;
    }}
    let flag=&sm[1];let scratch=&sm[2];let dirty=&helpers[0];
    for h in 0..4 {
        let cubes:Vec<_>=if axis==0 {programs::EQUAL[h].to_vec()} else {
            triples().iter().enumerate().filter(|(_,t)|t[1]==h&&t[2]==0).map(|(r,_)|(31u16,r as u16)).collect()
        };
        let high=|circ:&mut Circuit| {for &(m,v) in &cubes {
            let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect();
            super::conditional_mcx::guarded(circ,g,&cs,flag,scratch,false,dirty);
        }};
        high(circ);
        for lo in 0..64 {
            let value=64*h+lo;if axis==1&&value==0{continue;}
            let target=&word[if axis==0 {value+1}else{259-value}];
            let mut cs=vec![(flag,true)];cs.extend((0..6).map(|i|(&low[i],lo>>i&1!=0)));
            if let Some(p)=passenger {
                circ.cx(target,p);cs.push((p,true));
                super::conditional_mcx::guarded(circ,g,&cs,target,scratch,false,dirty);
                circ.cx(target,p);
            } else {super::conditional_mcx::guarded(circ,g,&cs,target,scratch,false,dirty);}
        }
        high(circ);
    }
}
fn exit_guard(circ:&mut Circuit,rank:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,g:&QReg,helpers:&[QReg]) {
    // j0 and phase11 make both implicit S bits0. Sign1 excludes trueS256 entry.
    for &(m,v) in programs::EQUAL[4] {
        let mut cs=vec![(p1,true),(p2,true),(sign,false)];cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,helpers);
    }
}
pub(super) fn exit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize) {
    assert!(helpers.len()>=24);let start=circ.b.ops.len();let g=&helpers[0];let shuttle=&sm[3];let dirty=&helpers[2..];
    addressed(circ,rank,a,None,Some(g),w1,dirty,0);
    exit_guard(circ,rank,sm,p1,p2,sign,g,dirty);
    for (x,y) in w1.iter().zip(w2) {circ.cx(y,x);circ.ccx(g,x,y);circ.cx(y,x);}
    // The old padding loan moved to Work2. S_mid[3] is0 under g, and
    // neither A update nor the A-address decoder observes it. Park cargo
    // here only across that interval, restoring it before interpreting S.
    selected_exit(circ,rank,a,sm,g,Some(shuttle),w2,dirty,0);
    let a_start=circ.b.ops.len();
    super::q794_Aupdate::update(circ,rank,a,c,sm,g,w1,w2,dirty,lo,hi,false);
    for op in &circ.b.ops[a_start..] {
        let q=shuttle.id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A update observes parked S bit");
    }
    selected_exit(circ,rank,a,sm,g,Some(shuttle),w1,dirty,0);
    super::q794_transfer::transfer(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty,0,true);
    circ.cx(g,iteration);
    exit_guard(circ,rank,sm,p1,p2,sign,g,dirty);
    addressed(circ,rank,a,None,Some(g),w1,dirty,0);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
fn exit_guard_signless(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,helpers:&[QReg]) {
    for &(m,v) in programs::EQUAL[4] {
        let mut cs=vec![(p1,true),(p2,true)];cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,helpers);
    }
    let mut birth=vec![(p1,true),(p2,true)];birth.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));mixed_mcx(circ,&birth,g,helpers);
}
fn take_exit_head(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,passenger:&QReg,word:&[QReg],dirty:&[QReg]) {
    // C is positive on g. Prune C0 rather than aliasing another word position.
    // Address v is the residual length C; leaves above the block's support bound c_max() are omitted.
    let c_max=super::length_recompute::c_max();
    let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|v|if v==0||v>c_max{None}else{Some(&word[259-v])}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{super::metadata_muxlease::predicate_swap(circ,rank,1,level-6,left,right,dirty);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].unwrap();let ops=circ.b.ops[start..].to_vec();circ.cswap(g,root,passenger);circ.cx(g,root);circ.b.ops.extend(ops.into_iter().rev());
}
/// The exit guard excludes A_old255. Omit that leaf physically: W1[257]
/// no longer exists even though the old mux would select it only off guard.
fn take_second(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,passenger:&QReg,w1:&[QReg],dirty:&[QReg]) {
    let start=circ.b.ops.len();let(lo,hi)=circ.q797_a_support.unwrap_or((0,256));
    let mut nodes:Vec<_>=(0..256).map(|v|if v<255&&(lo..hi).contains(&v){Some(&w1[v+2])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&a[level],left,right);}else{super::metadata_muxlease::predicate_swap(circ,rank,0,level-6,left,right,dirty);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let route=circ.b.ops[start..].to_vec();if let Some(root)=nodes[0]{circ.cswap(g,root,passenger);}circ.b.ops.extend(route.into_iter().rev());
}
pub(super) fn exit_signless(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize) {
    exit_signless_inner(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,lo,hi,false);
}
pub(super) fn exit_phase_cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize) {
    exit_signless_inner(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,lo,hi,true);
}
fn exit_signless_inner(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize,cargo:bool) {
    assert!(helpers.len()>=23);let start=circ.b.ops.len();let g=&helpers[0];let shuttle=&sm[3];let dirty=&helpers[2..];
    addressed(circ,rank,a,None,Some(g),w1,dirty,0);
    exit_guard_signless(circ,rank,a,c,sm,p1,p2,g,dirty);
    assert!(super::metadata_muxlease::active("Q795_PHASE_LOAN"));
    take_second(circ,rank,a,g,&sm[2],w1,dirty);
    if cargo {
        take_exit_head(circ,rank,c,g,&sm[0],w2,dirty);
    }
    // The second passenger has already left W1[A+2] for SM2. Thus at
    // A0 slot2 is genuinely zero and can receive the old padding passenger.
    super::q794_exit_low::swap_a0(circ,rank,a,g,&w1[1],&w1[2],dirty);
    for (i,(x,y)) in w1.iter().zip(w2).enumerate() {if ![0,1,257,258].contains(&i){circ.cx(y,x);circ.ccx(g,x,y);circ.cx(y,x);}}
    super::q794_mod4::cycle_swap(circ,[&w1[0],&w1[1],&w2[0],&w2[1],&w2[258],&w2[257]],g,dirty);
    // The old padding loan moved to Work2. S_mid[3] is0 under g, and
    // neither A update nor the A-address decoder observes it. Park cargo
    // here only across that interval, restoring it before interpreting S.
    selected_exit(circ,rank,a,sm,g,Some(shuttle),w2,dirty,0);
    // Undo the ordinary A0 selection (slot1), then take its relocated
    // slot2. Both predicates restore arbitrary off-guard work and lenders.
    super::q794_exit_low::swap_a0(circ,rank,a,g,&w2[1],shuttle,dirty);
    super::q794_exit_low::swap_a0(circ,rank,a,g,&w2[2],shuttle,dirty);
    if cargo {circ.cswap(g,&sm[0],&sm[1]);}
    let a_start=circ.b.ops.len();
    super::q794_Aupdate::update(circ,rank,a,c,sm,g,w1,w2,dirty,lo,hi,false);
    for op in &circ.b.ops[a_start..] {
        let q=shuttle.id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A update observes parked S bit");
        if cargo {let q=sm[1].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A update observes phase cargo");}
        if super::metadata_muxlease::active("Q795_PHASE_LOAN"){let q=sm[2].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"A update observes second phase cargo");}
    }
    if cargo {
        super::q797_cargo_moves::exchange_a(circ,rank,a,w1,0,&sm[1],&[(g,true)],dirty);
        circ.cx(g,&sm[1]); // New coefficient head was1; return S scratch to0.
    }
    selected_exit(circ,rank,a,sm,g,Some(shuttle),w1,dirty,0);
    if super::metadata_muxlease::active("Q795_PHASE_LOAN"){super::q797_cargo_moves::exchange_a(circ,rank,a,w2,2,&sm[2],&[(g,true)],dirty);}
    // All four S_mid loans have now returned to zero on the exit guard.
    super::q794_transfer::transfer_exit(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty);
    circ.cx(g,iteration);
    exit_guard_signless(circ,rank,a,c,sm,p1,p2,g,dirty);
    addressed(circ,rank,a,None,Some(g),w1,dirty,0);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
