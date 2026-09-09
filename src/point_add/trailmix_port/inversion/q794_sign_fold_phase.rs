//! Folded-rank Sign phase oracle. Install as a child of q794_sign_fold.rs.
//! Caller HMRs a reachable pure Sign first and conditions the ENTIRE body
//! (including rank conversion) on that outcome. Never reverse this oracle.
//! Source-ready composition; requires fresh folded native phase qualification.
use super::*;
use crate::point_add::trailmix_port::inversion as inv;
#[path="sign_phase_output.rs"] mod output;

pub(crate) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,n:usize) {
    assert!(helpers.len()>=22);
    assert!(inv::metadata_muxlease::active("Q794_SIGN_MAJ_HISTORY"));
    assert!(helpers.iter().chain(rank).all(|q|q.id()!=sign.id()));
    let owned=circ.b.next_qubit;
    let sign_id=crate::circuit::QubitId(sign.id() as u64);
    inv::q794_rank_fold::convert(circ,rank,helpers,false);
    inv::q798_sign_erase::code(circ,p1,p2,sign,helpers,false);
    // These are the FOLDED local selectors, not q798_handoffs/top helpers.
    move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    move_top_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    let mask=&helpers[0];let dirty=&helpers[1..];
    let loan_start=circ.b.ops.len();
    mask_loan(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
    let loan=circ.b.ops[loan_start..].to_vec();
    // Folded Sign requires MAJ, so the combined top-carry loan is disabled
    // exactly as in its ordinary emitter, regardless of the ambient flag.
    let top_start=circ.b.ops.len();
    top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
    let top=circ.b.ops[top_start..].to_vec();
    circ.cswap(p1,p2,mask);
    let outer=circ.b.ops.len();circ.ccx(p1,p2,sign);
    assert_eq!(output::phase_output(&mut circ.b.ops[outer..],sign_id),1);
    inv::q795_t11::park_c1(circ,p1,p2,sign,helpers);
    let inner=circ.b.ops.len();
    inv::q794_sign_fold_maj::emit(circ,rank,c,sm,p1,p2,mask,sign,w1,w2,dirty,j,n);
    output::phase_output(&mut circ.b.ops[inner..],sign_id);
    inv::q795_t11::park_c1(circ,p1,p2,sign,helpers);
    circ.cswap(p1,p2,mask);
    circ.b.ops.extend(top.into_iter().rev());
    circ.b.ops.extend(loan.into_iter().rev());
    move_top_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    inv::q798_sign_erase::code(circ,p1,p2,sign,helpers,true);
    inv::q794_rank_fold::convert(circ,rank,helpers,true);
    assert_eq!(circ.b.next_qubit,owned,"folded phase body allocated a quantum lane");
}
