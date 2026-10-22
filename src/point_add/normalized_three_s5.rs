//! Three-owner complete HT-S5 thirty-bit division epoch.
//! Replaces only the literal loop after digit and initial Zflip, before
//! q_g saving and either payload transition. It does not replace S5 as a
//! whole or change precision.
use super::builder::B;
use super::cross_three::{Cross,Gate};
/// Input/output raw Q and ring coordinates. A retains the complete HT
/// predicate, e/work initially globally zero. Q has NO quotient parks;
/// these thirty quotients are written only into the ring target cells.
/// PH may contain the materialized payload extra and is never a carry.
/// Inside C, q0=x128 is zero on A because raw Q[Y]=0. It stays out of all
/// 128 source cells and returns from every arithmetic record before the
/// next in-place swap. Off A, the exact literal brackets restore it even
/// when it carries an inactive counter passenger.
pub(crate) fn run(b:&mut B,c:&Cross<'_>){
    assert_eq!(c.qb,30);
    let frame=super::normalized_three_frame::record(b,c);
    b.play(&frame,false);
    let mut arithmetic=super::normalized_three_arithmetic::D{ht:true,payload_open:true};
    for k in(0..30).rev(){
        let target=super::normalized_three_frame::natural_target(c,k);
        arithmetic.divide_inplace(b,c,&target,Gate::Natural(k),false);
    }
    b.play(&frame,true);
}

