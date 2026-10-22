//! Fixed-column bridge with three external scalar owners.
//!
//! The fourth legacy role, x128, borrows Q[Yhi]. This is a real lifetime
//! reuse, not an omitted qubit declaration: Q is the unparked operand
//! at entry/exit, its bit length is at most Yhi, and DONE Q<2^26 with
//! Yhi>=28. Thus Q[Yhi] is
//! globally zero. All fixed quotient parks begin at Q[Yhi+1].
//!
//! Complete reciprocal V pairs use this lane as the old x128 R owner and
//! return it before every cmp_y/cmp_v call. Those comparators may instead
//! use it as their physical zero source cell at Yhi: x128 has no separate
//! use inside either ripple and is restored by their full up/down pair.
//! Generic, parked and unparked clean banks must exclude this scalar.
//! Payload digits exclude it from their helper bank and retain it solely
//! as the physical zero source pad. The full payload transitions already
//! truncate their Y source at Yhi and propagate their complete carry tail.
//!
//! No range, fixed quotient cap, paid reciprocal head, comparator family,
//! counter mapping, or phase protocol is changed by this bridge.

use super::builder::B;
use super::direct_three::Column;
use super::frogdrop_col::ColPar;

pub(crate) fn run(b:&mut B,column:&Column<'_>,cp:&ColPar){
    assert_eq!((column.q.len(),cp.n,cp.qb),(128,257,30));
    assert!((28..=96).contains(&cp.sy.1));
    assert!((cp.hr||cp.ht)&&!(cp.sw||cp.psw||cp.dl||cp.dq));
    // These are the inherited selected fixed dispatch, not a new smaller
    // care domain. In particular a generic Q129 park cannot append the
    // borrowed owner to Q a second time.
    assert!(super::frogdrop_col::c665_pool4());
    assert!(super::frogdrop_col::c660_sx7_raw());
    assert!(super::payload::splice258::enabled());
    assert_eq!(std::env::var("S5_NOPARK").as_deref(),Ok("1"));
    assert!(std::env::var_os("FD_MIDG_OLD5").is_none());
    assert!(std::env::var_os("QUOT_IP5_FUSED").is_none());
    let r=column.roles;
    let loan=column.q[cp.sy.1];
    assert!(![r.tag,r.cut,r.work,column.phase].contains(&loan));
    assert!(!column.meta.y.contains(&loan)&&!column.meta.sum.contains(&loan));
    assert!(!column.dirty.contains(&loan));
    // Fixed ABI: SX0=cut, SX1=toggle, SX2=prefix=x128, SX3=tag.
    let legacy=super::direct_column::Column{
        meta:column.meta,
        roles:super::outer_size::Roles{tag:r.tag,cut:r.cut,toggle:r.work,prefix:loan},
        ring:column.ring,q:column.q,phase:column.phase,
        compact:column.compact,dirty:column.dirty,clean_external:column.clean_external,
    };
    super::midg::direct_fixed_middle::run(b,&legacy,cp);
}
