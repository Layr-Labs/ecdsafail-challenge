//! Own dual-cargo pilot: A254/C1 borrows the existing residual head Work2[257].
//! Routing-only isolation: second hole not removed, not a whole Q794 result.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q797_cargo_moves as moves,q798_handoffs,metadata_muxlease as mux,length_recompute::mixed_mcx};

pub(crate) fn enabled()->bool{true}

// The rank5 A_high==3 predicate is the XOR of (rank&28)==28 and rank==28.
// Product terms are normalized to avoid duplicate/opposite controls.
fn high_terms<'a>(rank:&'a[QReg],a:&'a[QReg],terms:&[Vec<(&'a QReg,bool)>])->Vec<Vec<(&'a QReg,bool)>>{
    let mut out=Vec::new();for term in terms{for (mask,value) in [(28usize,28usize),(31,28)]{
        let mut cs=term.clone();let mut valid=true;
        for (q,v) in (0..5).filter(|&i|mask>>i&1!=0).map(|i|(&rank[i],value>>i&1!=0)).chain((0..6).map(|i|(&a[i],62>>i&1!=0))){
            if let Some(&(_,old))=cs.iter().find(|&&(x,_)|x.id()==q.id()){if old!=v{valid=false;break;}}else{cs.push((q,v));}
        }
        if valid{out.push(cs);}
    }}out
}

fn gather_gap<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&'a[QReg],w2:&'a[QReg],dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let (lo,hi)=circ.q797_a_support.unwrap_or((0,256));assert!(lo<hi&&hi<=256);
    let mut nodes:Vec<_>=(0..256).map(|v|if v==255||!(lo..hi).contains(&v){None}else if v==254{Some(&w2[257])}else{Some(&w1[v+3])}).collect();
    for level in 0..8 {let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&a[level],left,right);}else{mux::predicate_swap(circ,rank,0,level-6,left,right,dirty);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    (nodes[0].expect("nonempty active C1 support"),circ.b.ops[start..].to_vec())
}

/// Original swap+flip into gap0, except A254 uses a plain swap with head1.
/// All control terms must exclude terminal A255, as in the original callers.
pub(super) fn inbound(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&[QReg],w2:&[QReg],from:usize,terms:&[Vec<(&QReg,bool)>],helpers:&[QReg]){
    if !enabled(){moves::adjacent_a_terms_flip(circ,rank,a,w1,from,3,terms,helpers);return;}
    let shuttle=&helpers[0];let dirty=&helpers[1..];
    moves::exchange_a_terms(circ,rank,a,w1,from,shuttle,terms,dirty);
    let(root,ops)=gather_gap(circ,rank,a,w1,w2,dirty);
    // X on the target before SWAP cancels the old X on its source after
    // SWAP. This is a literal permutation identity for arbitrary data.
    for cs in high_terms(rank,a,terms){mixed_mcx(circ,&cs,root,dirty);}
    circ.cx(shuttle,root);for term in terms{let mut cs=term.clone();cs.push((root,true));mixed_mcx(circ,&cs,shuttle,dirty);}circ.cx(shuttle,root);
    circ.b.ops.extend(ops.into_iter().rev());
    let(root,ops)=q798_handoffs::gather_a(circ,rank,a,w1,from,dirty);
    circ.cx(shuttle,root);for term in terms{let mut cs=term.clone();cs.push((root,true));mixed_mcx(circ,&cs,shuttle,dirty);}circ.cx(shuttle,root);
    for term in terms{mixed_mcx(circ,term,root,dirty);}circ.b.ops.extend(ops.into_iter().rev());
}

/// Keep the existing newborn handoff except A254: its host already arrived
/// at Work2[256] by the physical T10 rotation, so this branch is identity.
pub(super) fn newborn(circ:&mut Circuit,rank:&[QReg],a:&[QReg],sign:&QReg,left:&QReg,right:&QReg,dirty:&[QReg]){
    circ.cswap(sign,left,right);circ.cx(sign,left);
    if !enabled(){return;}
    let terms=high_terms(rank,a,&[vec![(sign,true)]]);
    // Each primitive is involutory; aggregate the ESOP terms separately.
    // F^-1=SWAP*X_left must not be repeated once per overlapping ESOP cube.
    for cs in &terms{mixed_mcx(circ,cs,left,dirty);}
    for term in &terms{circ.cx(right,left);let mut cs=term.clone();cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);circ.cx(right,left);}
}

fn swap_terms(circ:&mut Circuit,terms:&[Vec<(&QReg,bool)>],left:&QReg,right:&QReg,dirty:&[QReg]){
    for term in terms{circ.cx(right,left);let mut cs=term.clone();cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);circ.cx(right,left);}
}

/// Just before entry Work1[256] holds SECOND cargo. Work2[255] is zero in
/// both exact A254/C1 integer alternatives after the last-bit rotation.
/// Park second cargo there, then use the vacated Work1[256] for first cargo
/// while restoring residual head Work2[256]=1 for the entry length reader.
/// Selected head reads start at A+2=256, beyond the temporary W2[255] cargo.
pub(super) fn before_entry(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    if !enabled(){return;}
    // A254+C0+S1/2 has rank29. rank[1]=0 rejects the other A_high3 codes;
    // S_middle=0 holds for both analytically proved extreme alternatives.
    let mut base=vec![(p1,true),(p2,false),(&rank[1],false)];base.extend(c.iter().chain(sm).map(|q|(q,false)));
    let terms=high_terms(rank,a,&[base]);
    swap_terms(circ,&terms,&w1[256],&w2[255],dirty); // park second cargo in proved zero
    swap_terms(circ,&terms,&w1[256],&w2[256],dirty);
    for cs in &terms{mixed_mcx(circ,cs,&w2[256],dirty);}
}

/// Entry Sign marks exactly newborn11. At A254, put the passenger back in
/// its normal phase11 residual head and clear the temporarily borrowed slot.
pub(super) fn after_entry(circ:&mut Circuit,rank:&[QReg],a:&[QReg],sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    if !enabled(){return;}
    let terms=high_terms(rank,a,&[vec![(sign,true)]]);
    for cs in &terms{mixed_mcx(circ,cs,&w2[256],dirty);}
    swap_terms(circ,&terms,&w1[256],&w2[256],dirty);
    swap_terms(circ,&terms,&w1[256],&w2[255],dirty); // restore second cargo and zero
}

