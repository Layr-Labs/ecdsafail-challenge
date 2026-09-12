//! Exact global A-addressed loan with a physical terminal replacement.
//! Selection never addresses omitted W1[256..258], even off domain.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn controlled_swap(circ:&mut Circuit,cs:&[(&QReg,bool)],a:&QReg,b:&QReg,dirty:&[QReg]) {
    circ.cx(b,a);let mut controls=cs.to_vec();controls.push((a,true));
    mixed_mcx(circ,&controls,b,dirty);circ.cx(b,a);
}
fn high_swap(circ:&mut Circuit,rank:&[QReg],bit:usize,a:&QReg,b:&QReg,dirty:&[QReg]) {
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4)
        .filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    assert_eq!(triples.len(),32);
    let mut anf:Vec<_>=triples.iter().map(|t|t[0]>>bit&1!=0).collect();
    for k in 0..5{for m in 0..32{if m>>k&1!=0{anf[m]^=anf[m^(1<<k)];}}}
    // Controlled transpositions sharing the same two rails commute. Their
    // product is controlled by the XOR of these exact metadata monomials.
    for(m,on)in anf.into_iter().enumerate(){if on{
        let cs:Vec<_>=(0..5).filter(|&k|m>>k&1!=0).map(|k|(&rank[k],true)).collect();
        controlled_swap(circ,&cs,a,b,dirty);
    }}
}

/// For every physical rank/low-A code, exchange passenger with:
///   A<255: word[A+1]; A=255: terminal_host.
/// This is an exact addressed SWAP for arbitrary data, independently of any
/// zero promise. A is decoded from rank's high-A plus six low bits. Optional
/// guard false means identity. All routing, dirty data and metadata restore.
/// Caller separately proves that its selected donor is zero on the required
/// reachable domain and that the parked passenger survives the loan lifetime.
/// In the proposed terminal use, terminal_host=SM2, which is NOT a selector.
pub(super) fn global_a(
    circ:&mut Circuit,rank:&[QReg],a:&[QReg],passenger:&QReg,word:&[QReg],
    terminal_host:&QReg,guard:Option<&QReg>,dirty:&[QReg],
) {
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(word.len(),259);
    assert!(dirty.len()>=4);
    let bank:Vec<_>=(0..256).map(|v|if v==255{terminal_host}else{&word[v+1]}).collect();
    let mut ids:Vec<_>=bank.iter().copied().chain(rank).chain(a)
        .chain(std::iter::once(passenger)).chain(guard).chain(dirty).map(QReg::id).collect();
    ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"loan alias");
    let owned=circ.b.next_qubit;let all_start=circ.b.ops.len();
    // EXPERIMENT: prune the selector by the block's A support exactly as
    // q794_handoffs::gather_a does (leaves outside (lo..hi) u {255} are never
    // addressed on the reachable domain). Q793_LOAN_PRUNE=0 restores the full tree.
    let prune=std::env::var("Q793_LOAN_PRUNE").ok().as_deref()!=Some("0");
    let (lo,hi)=if prune{circ.q797_a_support.unwrap_or((0,256))}else{(0,256)};
    let mut nodes:Vec<Option<&QReg>>=bank.iter().enumerate().map(|(v,&q)|if (lo..hi).contains(&v)||v==255{Some(q)}else{None}).collect();
    let pswap=std::env::var("Q793_LOAN_PSWAP").ok().as_deref()!=Some("0");
    for level in 0..8{let mut next=Vec::new();
        for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
            (Some(l),Some(r))=>{
                if level<6{controlled_swap(circ,&[(&a[level],true)],l,r,dirty);}
                else if pswap{super::metadata_muxlease::predicate_swap(circ,rank,0,level-6,l,r,dirty);}
                else{high_swap(circ,rank,level-6,l,r,dirty);}
                Some(l)
            },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
        });}nodes=next;
    }
    let route=circ.b.ops[all_start..].to_vec();let root=nodes[0].expect("nonempty loan selector");
    if let Some(g)=guard{controlled_swap(circ,&[(g,true)],root,passenger,dirty);}
    else{circ.cx(root,passenger);circ.cx(passenger,root);circ.cx(root,passenger);}
    circ.b.ops.extend(route.into_iter().rev());assert_eq!(circ.b.next_qubit,owned);
    for op in &circ.b.ops[all_start..]{for h in [256usize,257,258]{
        let hole=word[h].id()as u64;
        assert!(op.q_target.0!=hole&&op.q_control1.0!=hole&&op.q_control2.0!=hole,
            "global loan touched omitted Work1[{h}]");
    }}
}
