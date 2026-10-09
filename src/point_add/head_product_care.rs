//! Exact multiplication by the implied-odd leading source, no truncation.
//! For a zero-extended H-bit input target and H-bit source a, returns
//! target*(a|1) in exactly 2H bits. The same map is a permutation on every
//! arbitrary target bitstring; only its sign admission needs zero padding.
use super::{builder::B,frogdrop::cadd_tail_and_mixed};
use crate::circuit::QubitId;
pub fn head_product(b:&mut B,t:&[QubitId],a:&[QubitId],c0:QubitId,h:QubitId,
                    anc:&[QubitId],andc:&[QubitId],dirty:&[QubitId]){
    assert_eq!(t.len(),2*a.len());
    // Target high H bits are zero only on the admitted sign-read care.
    // Every omitted upper control is then zero; elsewhere the retained gates
    // still form a clean permutation and are reversed with their answer ignored.
    for i in (0..a.len()).rev(){
        let lo=i+1;let nm=(a.len()-1).min(t.len()-lo);
        let tail=&t[lo+nm..];
        cadd_tail_and_mixed(b,t[i],&t[lo..lo+nm],&a[1..nm+1],tail,c0,h,anc,dirty,andc);
    }
}
