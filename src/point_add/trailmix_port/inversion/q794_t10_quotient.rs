//! Two-hole-safe T10 quotient pop and mask funding. No fresh quantum rail.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{length_recompute::mixed_mcx,metadata_muxlease as mux,metadata_arithmetic5_encoded::add};
#[path="q794_t10_numeric_quotient.rs"] pub(crate) mod numeric;
fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
pub(super) fn gate(circ:&mut Circuit,controls:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut cs=Vec::new();for &(q,v)in controls{
        assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=cs.iter().find(|&&(p,_):&&(&QReg,bool)|p.id()==q.id()){if old!=v{return;}}else{cs.push((q,v));}
    }mixed_mcx(circ,&cs,out,dirty);
}
/// C is already C+A modulo64. On C_sum_low0, the discarded low carry
/// equals [A_low!=0]. Thus sum mod256=0 iff H3 XOR A0*(H3 XOR H0 XOR H4).
fn endpoint_prepared(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],base:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],paired_guard:Option<&QReg>){
    for azero in [false,true]{
        let truth:Vec<_>=triples().iter().map(|t|{let h=t[0]+t[1];if azero{h==0||h==3||h==4}else{h==3}}).collect();
        let(polarity,terms)=mux::swap_terms(truth,5);
        for term in terms{
            let mut cs=base.to_vec();cs.extend(c.iter().map(|q|(q,false)));
            if azero{cs.extend(a.iter().map(|q|(q,false)));}
            cs.extend((0..5).filter(|&i|term>>i&1!=0).map(|i|(&rank[i],polarity>>i&1==0)));
            if let Some(g)=paired_guard{
                let mut controls=Vec::new();let mut saw_guard=false;
                for &(q,v) in &cs{
                    assert_ne!(q.id(),out.id());
                    if q.id()==g.id(){assert!(v);saw_guard=true;}else{controls.push((q,v));}
                }
                assert!(saw_guard);circ.x(g);
                super::paired_clean_mcx::toggle(circ,&controls,out,g);
                circ.x(g);
            }else{gate(circ,&cs,out,dirty);}
        }
    }
}
pub(super) fn endpoint(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],base:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    add(circ,a,c,None,false);endpoint_prepared(circ,rank,a,c,base,out,dirty,None);add(circ,a,c,None,true);
}
/// Exchange only nonzero sum addresses1..255 -> W1[2..256]. No omitted
/// rail is even emitted in a disabled tree. All high dirty-carry echoes
/// are inherited exactly from the donor's quotient-selection function.
fn normal_exchanges(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,passengers:&[&QReg],w1:&[QReg],helpers:&[QReg],endpoint_cache:Option<&QReg>){
    assert!(helpers.len()>=18);add(circ,a,c,None,false);let start=circ.b.ops.len();let d=&helpers[0];let dirty=&helpers[1..];
    let mut nodes:Vec<_>=(0..256).map(|s|if s==0{None}else{Some(&w1[s+1])}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{
            if level<6{circ.cswap(&c[level],left,right);}else{
                let bit=level-6;let ts=triples();let controls:Vec<_>=rank.iter().chain(std::iter::once(d)).collect();
                let truth:Vec<_>=(0..64).map(|r|((ts[r&31][0]+ts[r&31][1]+(r>>5))>>bit)&1!=0).collect();
                add(circ,a,c,None,true);add(circ,a,c,Some(d),false);mux::truth_swap(circ,&controls,truth.clone(),left,right,dirty);
                add(circ,a,c,None,true);add(circ,a,c,Some(d),false);mux::truth_swap(circ,&controls,truth,left,right,dirty);
                let zero:Vec<_>=ts.iter().map(|t|((t[0]+t[1])>>bit)&1!=0).collect();mux::truth_swap(circ,&rank.iter().collect::<Vec<_>>(),zero,left,right,dirty);
            }Some(left)
        },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].unwrap();let route=circ.b.ops[start..].to_vec();
    for &p in passengers{
        circ.cx(p,root);
        if let Some(cache)=endpoint_cache{
            gate(circ,&[(g,true),(cache,false),(root,true)],p,helpers);
        }else{
            gate(circ,&[(g,true),(root,true)],p,helpers);
            endpoint_prepared(circ,rank,a,c,&[(g,true),(root,true)],p,helpers,None);
        }
        circ.cx(p,root);
    }
    circ.b.ops.extend(route.into_iter().rev());add(circ,a,c,None,true);
}
fn normal_exchange(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,p:&QReg,w1:&[QReg],helpers:&[QReg]){
    normal_exchanges(circ,rank,a,c,g,&[p],w1,helpers,None);
}

/// The normal pop and zero-mask loan share exactly the same quotient route.
/// Their endpoint-only companions commute with the OTHER normal map, because
/// normal and endpoint centers have disjoint metadata guards. Compute the
/// route once, perform both center swaps, then undo it before touching DATA.
/// This is also exact for arbitrary incoming p/mask and offguard work bits.
pub(super) fn pop_and_mask_loan(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,p:&QReg,mask:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    normal_exchanges(circ,rank,a,c,g,&[p,mask],w1,dirty,None);
    circ.cx(p,&w2[1]);endpoint(circ,rank,a,c,&[(g,true),(&w1[0],false),(&w2[1],true)],p,dirty);circ.cx(p,&w2[1]);
    endpoint(circ,rank,a,c,&[(g,true),(&w1[0],true),(&w2[0],false)],p,dirty);
    endpoint(circ,rank,a,c,&[(g,true)],&w2[258],dirty);
    circ.cx(mask,&w2[258]);endpoint(circ,rank,a,c,&[(g,true),(&w2[258],true)],mask,dirty);circ.cx(mask,&w2[258]);
}
pub(super) fn pop(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,p:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    normal_exchange(circ,rank,a,c,g,p,w1,dirty);
    // Even-t endpoint b1 is the quotient payload; pop into initially-zero P1.
    circ.cx(p,&w2[1]);endpoint(circ,rank,a,c,&[(g,true),(&w1[0],false),(&w2[1],true)],p,dirty);circ.cx(p,&w2[1]);
    // Odd-t endpoint q=1 XOR b0. Copy without changing u0: the subsequent
    // coefficient ADD itself changes u0 to1, erasing the implicit quotient.
    endpoint(circ,rank,a,c,&[(g,true),(&w1[0],true),(&w2[0],false)],p,dirty);
}
pub(super) fn mask_loan(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,p:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],inverse:bool){
    // Normal domains use the now-zero quotient slot; M256 uses v0=1,
    // outside the coefficient scan. The guard subsets are disjoint.
    normal_exchange(circ,rank,a,c,g,p,w1,dirty);
    if !inverse{endpoint(circ,rank,a,c,&[(g,true)],&w2[258],dirty);}
    circ.cx(p,&w2[258]);endpoint(circ,rank,a,c,&[(g,true),(&w2[258],true)],p,dirty);circ.cx(p,&w2[258]);
    if inverse{endpoint(circ,rank,a,c,&[(g,true)],&w2[258],dirty);}
}

/// P2 is a zero phase/cache rail under g at both public call boundaries.
/// Hold g*M256 there only while metadata and the phase bits are otherwise
/// unchanged; restore it BEFORE the fused carry prefix needs the same cache.
pub(super) fn pop_and_mask_cached(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,p:&QReg,mask:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    if numeric::enabled(){numeric::pop_and_mask(circ,rank,a,c,g,p,mask,cache,w1,w2,dirty);return;}
    assert!(dirty.iter().all(|q|q.id()!=cache.id()&&q.id()!=p.id()&&q.id()!=mask.id()));
    cached_endpoint(circ,rank,a,c,g,cache,dirty);
    normal_exchanges(circ,rank,a,c,g,&[p,mask],w1,dirty,Some(cache));
    circ.cx(p,&w2[1]);gate(circ,&[(g,true),(cache,true),(&w1[0],false),(&w2[1],true)],p,dirty);circ.cx(p,&w2[1]);
    gate(circ,&[(g,true),(cache,true),(&w1[0],true),(&w2[0],false)],p,dirty);
    gate(circ,&[(g,true),(cache,true)],&w2[258],dirty);
    circ.cx(mask,&w2[258]);gate(circ,&[(g,true),(cache,true),(&w2[258],true)],mask,dirty);circ.cx(mask,&w2[258]);
    cached_endpoint(circ,rank,a,c,g,cache,dirty);
}

pub(super) fn mask_return_cached(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,mask:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    if numeric::enabled(){numeric::mask_return(circ,rank,a,c,g,mask,cache,w1,w2,dirty);return;}
    assert!(dirty.iter().all(|q|q.id()!=cache.id()&&q.id()!=mask.id()));
    cached_endpoint(circ,rank,a,c,g,cache,dirty);
    normal_exchanges(circ,rank,a,c,g,&[mask],w1,dirty,Some(cache));
    circ.cx(mask,&w2[258]);gate(circ,&[(g,true),(cache,true),(&w2[258],true)],mask,dirty);circ.cx(mask,&w2[258]);
    gate(circ,&[(g,true),(cache,true)],&w2[258],dirty);
    cached_endpoint(circ,rank,a,c,g,cache,dirty);
}

/// Matched pure-cache-XOR extension: on g1 X(g) is a clean scratch;
/// on g0 all consumers still retain g, and the repeated oracle removes
/// the arbitrary extension. Rank/A/C/g and dirty helpers are restored.
fn cached_endpoint(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,cache:&QReg,dirty:&[QReg]){
    let paired=super::metadata_muxlease::active("Q794_T10_CACHE_PAIRED");
    add(circ,a,c,None,false);
    endpoint_prepared(circ,rank,a,c,&[(g,true)],cache,dirty,if paired{Some(g)}else{None});
    add(circ,a,c,None,true);
}
