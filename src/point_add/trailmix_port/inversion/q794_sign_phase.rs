//! Source-ready PHASE BODY only; install as child module of q794_sign.rs.
//! This is experimental, unqualified native production code.
//! Caller must first HMR reachable pure Sign and execute this entire body only
//! when that measurement is 1. Do not reverse this body as an EEA inverse.
//! Suggested parent declaration:
//! #[path="q794_sign_phase.rs"] pub(super) mod measurement;
use super::*;
use crate::point_add::trailmix_port::inversion as inv;
#[path="sign_phase_output.rs"] mod output;

pub(crate) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,n:usize) {
    if inv::metadata_muxlease::active("Q794_SIGN_RANK_FOLD"){
        inv::q794_sign_fold::measurement::emit(circ,rank,a,c,sm,p1,p2,sign,w1,w2,helpers,j,n);return;
    }
    assert!(helpers.len()>=22);
    let owned=circ.b.next_qubit;
    let sign_id=crate::circuit::QubitId(sign.id() as u64);
    inv::q798_sign_erase::code(circ,p1,p2,sign,helpers,false);
    inv::q798_handoffs::move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    move_top_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    let mask=&helpers[0];let dirty=&helpers[1..];
    let loan_start=circ.b.ops.len();
    mask_loan(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
    let loan=circ.b.ops[loan_start..].to_vec();
    let maj=inv::metadata_muxlease::active("Q794_SIGN_MAJ_HISTORY");
    let combined=inv::metadata_muxlease::active("Q794_SIGN_COMBINED_TOP")&&!maj;
    let top_start=circ.b.ops.len();
    if combined {
        top_flag_and_loan(circ,rank,c,sm,p1,p2,mask,&dirty[0],w1,&dirty[1..],j);
    } else {
        inv::q795_t11_top::top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
    }
    let top=circ.b.ops[top_start..].to_vec();
    circ.cswap(p1,p2,mask);
    let outer=circ.b.ops.len();circ.ccx(p1,p2,sign);
    assert_eq!(output::phase_output(&mut circ.b.ops[outer..],sign_id),1);
    inv::q795_t11::park_c1(circ,p1,p2,sign,helpers);
    let inner=circ.b.ops.len();
    if maj {inv::q794_sign_maj_history::emit(circ,rank,c,sm,p1,p2,mask,sign,w1,w2,dirty,j,n);}
    else {inv::q794_sign_two_pass::emit(circ,rank,c,sm,p1,p2,mask,sign,w1,w2,dirty,j,n);}
    output::phase_output(&mut circ.b.ops[inner..],sign_id);
    inv::q795_t11::park_c1(circ,p1,p2,sign,helpers);
    circ.cswap(p1,p2,mask);
    circ.b.ops.extend(top.into_iter().rev());
    circ.b.ops.extend(loan.into_iter().rev());
    move_top_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    inv::q798_handoffs::move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    inv::q798_sign_erase::code(circ,p1,p2,sign,helpers,true);
    assert_eq!(circ.b.next_qubit,owned,"phase body allocated a quantum lane");
}
