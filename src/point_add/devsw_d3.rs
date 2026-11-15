//! D3 switches, baked by s25 (constants, no environment reads; NS is off in fused columns at its call site)
pub fn c6r()->u32{0}
pub fn c6r_max()->u32{1000000}
pub fn c6r_brk()->u32{0}
pub fn c6s()->u32{0}
pub fn c6s_max()->u32{1000000}
pub fn c6s_brk()->u32{0}
pub fn tally()->u32{0}
pub fn ns()->u32{1}
pub fn ns_brk()->u32{0}
/// replica of frogdrop::inc_mixed's choice: number of anc wires it touches for `bits` bits and `anc` wires
pub fn incmixed_used(bits:usize,anc:usize)->usize{
    use super::frogdrop::{conditional_inc_need as need,conditional_inc_cost as cost};
    if bits==0{return 0;}
    let old_k=anc.min(bits-1);let old_suffix=bits-old_k;
    let old_cost=old_k+if old_suffix==1{0}else{4*old_suffix};
    let mut best:Option<(usize,usize)>=None;
    for k in 0..=old_k{let suffix=bits-k;let n=need(suffix);
        if n<=anc-k{let c=k+cost(suffix);if c<old_cost&&best.is_none_or(|(p,_)|c<p){best=Some((c,k));}}}
    if let Some((_,k))=best{k+need(bits-k)}else{old_k}
}
pub fn incmixed_cost(bits:usize,anc:usize)->usize{
    use super::frogdrop::{conditional_inc_need as need,conditional_inc_cost as cost};
    if bits==0{return 0;}
    let old_k=anc.min(bits-1);let old_suffix=bits-old_k;
    let old_cost=old_k+if old_suffix==1{0}else{4*old_suffix};
    let mut best:Option<usize>=None;
    for k in 0..=old_k{let suffix=bits-k;let n=need(suffix);
        if n<=anc-k{let c=k+cost(suffix);if c<old_cost&&best.is_none_or(|p|c<p){best=Some(c);}}}
    best.unwrap_or(old_cost)
}
