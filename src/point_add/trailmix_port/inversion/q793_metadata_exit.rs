//! New three-hole cycle exit. Pending full integrated native verification.
//! Padding cargo is parked BEFORE the low3 cycle, so A0/A1 need no fake t bits.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{length_recompute::mixed_mcx,q793_loans};
#[path="metadata_remainder5_programs.rs"] mod programs;

fn mcx_cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
fn exit_rank_toggle(circ:&mut Circuit,rank:&[QReg],base:&[(&QReg,bool)],g:&QReg,dirty:&[QReg]){
    let cubes=programs::EQUAL[4];
    if super::metadata_muxlease::active("Q793_RANK_ECHO_EXIT")&&dirty.len()>=2{
        let truth:Vec<_>=(0..32u16).map(|x|cubes.iter().fold(false,|v,&(m,b)|v^((x&m)==b))).collect();let(polarity,terms)=super::metadata_muxlease::swap_terms(truth,5);
        let direct:usize=cubes.iter().map(|(m,_)|mcx_cost(base.len()+m.count_ones()as usize)).sum();let echo=2*terms.iter().map(|m|mcx_cost(m.count_ones()as usize)).sum::<usize>()+2*mcx_cost(base.len()+1);
        if echo<direct{let d=&dirty[0];let rest=&dirty[1..];for &(q,_)in base{assert_ne!(q.id(),d.id());}
            let compute=|circ:&mut Circuit|{for i in 0..5{if polarity>>i&1!=0{circ.x(&rank[i]);}}for &m in &terms{let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)).collect();match cs.len(){0=>circ.x(d),1=>circ.cx(cs[0].0,d),_=>mixed_mcx(circ,&cs,d,rest)}}for i in (0..5).rev(){if polarity>>i&1!=0{circ.x(&rank[i]);}}};
            let consume=|circ:&mut Circuit|{let mut cs=base.to_vec();cs.push((d,true));mixed_mcx(circ,&cs,g,rest);};consume(circ);compute(circ);consume(circ);compute(circ);return;}
    }
    for &(m,v)in cubes{let mut cs=base.to_vec();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,dirty);}
}

fn guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]) {
    let mut base=vec![(p1,true),(p2,true)];base.extend(sm.iter().map(|q|(q,false)));exit_rank_toggle(circ,rank,&base,g,dirty);
    let mut birth=vec![(p1,true),(p2,true)];birth.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));
    mixed_mcx(circ,&birth,g,dirty);
}

fn second(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,passenger:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]) {
    let start=circ.b.ops.len();
    // This is the INTERNAL S0 exit chart. The A254 second cargo has moved
    // from boundary W2[255] to W2[256] with the final phase11 right rotation.
    // W4 lever A4 (Q793_A4_CMAX): restrict the selector to the block's
    // analytic A-support; A254->W2[256] is always retained.
    let (lo,hi)=if super::metadata_muxlease::active("Q793_A4_CMAX"){circ.q797_a_support.unwrap_or((0,256))}else{(0,256)};
    let mut nodes:Vec<_>=(0..256).map(|v|match v{0..=253 if (lo..hi).contains(&v)=>Some(&w1[v+2]),254=>Some(&w2[256]),_=>None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{if level<6{circ.cswap(&a[level],l,r);}else{super::metadata_muxlease::predicate_swap(circ,rank,0,level-6,l,r,dirty);}Some(l)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let route=circ.b.ops[start..].to_vec();circ.cswap(g,nodes[0].unwrap(),passenger);circ.b.ops.extend(route.into_iter().rev());
}

fn head(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,passenger:&QReg,w2:&[QReg],dirty:&[QReg]) {
    let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|v|if v==0{None}else{Some(&w2[259-v])}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{super::metadata_muxlease::predicate_swap(circ,rank,1,level-6,l,r,dirty);}Some(l)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let route=circ.b.ops[start..].to_vec();let root=nodes[0].unwrap();circ.cswap(g,root,passenger);circ.cx(g,root);
    circ.b.ops.extend(route.into_iter().rev());
}

pub(super) fn exit_phase_cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize) {
    assert!(helpers.len()>=23);let owned=circ.b.next_qubit;let start=circ.b.ops.len();let g=&helpers[0];let dirty=&helpers[2..];
    // Terminal Work2[258] is a genuine zero. The post-exit r readers ignore
    // it on A255, and no SM cargo remains during the rank transfer.
    if std::env::var("Q793_HELD_LOAN").ok().as_deref()!=Some("1"){q793_loans::global_a(circ,rank,a,g,w1,&w2[258],None,dirty);}
    guard(circ,rank,a,c,sm,p1,p2,g,dirty);
    second(circ,rank,a,g,&sm[2],w1,w2,dirty);
    head(circ,rank,c,g,&sm[0],w2,dirty);
    q793_loans::global_a(circ,rank,a,&sm[3],w1,&w2[258],Some(g),dirty);
    for(i,(x,y))in w1.iter().zip(w2).enumerate(){if ![0,1,2,256,257,258].contains(&i){circ.cswap(g,x,y);}}
    super::q793_mod8::cycle_swap(circ,[&w1[0],&w1[1],&w1[2],&w2[0],&w2[1],&w2[2],&w2[258],&w2[257],&w2[256]],g,dirty);
    circ.cswap(g,&sm[0],&sm[1]);
    let update_start=circ.b.ops.len();
    super::q793_Aupdate::update(circ,rank,a,c,sm,g,w1,w2,dirty,lo,hi,false);
    for op in &circ.b.ops[update_start..]{for q in [&sm[1],&sm[2],&sm[3]]{let id=q.id()as u64;assert!(op.q_target.0!=id&&op.q_control1.0!=id&&op.q_control2.0!=id,"Aupdate observes parked cargo");}}
    super::q797_cargo_moves::exchange_a(circ,rank,a,w1,0,&sm[1],&[(g,true)],dirty);
    circ.cx(g,&sm[1]);
    // Return the second cargo before depositing padding cargo. At A255 the
    // second lives in W2[257], while the padding donor is W2[258].
    super::q797_cargo_moves::exchange_a(circ,rank,a,w2,2,&sm[2],&[(g,true)],dirty);
    q793_loans::global_a(circ,rank,a,&sm[3],w1,&w2[258],Some(g),dirty);
    super::q793_transfer::transfer_exit(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty);
    circ.cx(g,iteration);
    guard(circ,rank,a,c,sm,p1,p2,g,dirty);
    if std::env::var("Q793_HELD_LOAN").ok().as_deref()!=Some("1"){q793_loans::global_a(circ,rank,a,g,w1,&w2[258],None,dirty);}
    assert_eq!(circ.b.next_qubit,owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"exit touched omitted Work1[{h}]");}}
}
