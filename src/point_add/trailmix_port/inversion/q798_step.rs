//! Experimental signless scheduled EEA step: 542 owned wires, 24 borrowed.
//! Public reversible point-addition benchmark optimization. No measurement.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_remainder5_programs.rs"] mod programs;
pub(super) fn loan(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&[QReg],sign:&QReg,dirty:&[QReg]) {
    let(q,ops)=super::q798_handoffs::gather_a(circ,rank,a,w1,1,dirty);
    circ.cx(q,sign);circ.cx(sign,q);circ.cx(q,sign);circ.b.ops.extend(ops.into_iter().rev());
}
pub(super) fn decode_birth(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w2:&[QReg],dirty:&[QReg],j:usize){
    if j!=0{return;}
    let mut cs=vec![(p1,true),(p2,true),(&w2[0],false)];
    cs.extend(rank.iter().chain(a).chain(sm).chain(&c[1..]).map(|q|(q,false)));
    mixed_mcx(circ,&cs,&c[0],dirty);
}
pub(super) fn encode_birth(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,dirty:&[QReg],j:usize){
    if j!=0{return;}
    let mut cs=vec![(p1,true),(p2,true),(sign,true)];
    cs.extend(rank.iter().chain(a).chain(sm).chain(&c[1..]).map(|q|(q,false)));
    mixed_mcx(circ,&cs,&c[0],dirty);
    let mut cs=vec![(p1,true),(p2,true)];
    cs.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));
    mixed_mcx(circ,&cs,sign,dirty);
}
pub(super) fn hide_birth(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,dirty:&[QReg],j:usize){
    if j!=0{return;}
    let mut cs=vec![(p1,true)];cs.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));
    mixed_mcx(circ,&cs,p2,dirty);
}
pub(super) fn s_zero_phase_flips(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],helpers:&[QReg],j:usize) {
    phase_flips(circ,rank,a,c,sm,p1,p2,w1,&w1[2],helpers,j);
}
pub(super) fn phase_flips(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],odd_discriminator:&QReg,helpers:&[QReg],j:usize) {
    if j%2!=0{return;}
    // For phases01/10, S1=(j/2) xor C0. Swap these phases only at S0.
    // The surrounding CNOTs put phase parity in P1, so phases00/11 are identity.
    circ.cx(p2,p1);
    for &(m,v) in programs::EQUAL[4] {
        let mut cs=vec![(p1,true),(&c[0],j==2)];
        cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
        mixed_mcx(circ,&cs,p2,helpers);
    }
    if j==0 {
        // At the first trueS256 ascent, entry phase update already changed
        // phase00 to01. Cancel this odd-phase swap as well as the even one.
        let mut peak=vec![(p1,true)];peak.extend(rank.iter().map(|q|(q,false)));peak.extend(a.iter().map(|q|(q,false)));peak.extend(c.iter().map(|q|(q,false)));peak.extend(sm.iter().map(|q|(q,false)));peak.push((odd_discriminator,false));
        mixed_mcx(circ,&peak,p2,helpers);
    }
    circ.cx(p2,p1);
    if j!=0{return;}
    // For phases00/11 the two low S bits are0 at j0. Flip both phase bits
    // using their invariant parity, with reversible corrections for exceptions.
    circ.cx(p1,p2);
    let base=vec![(p2,false)];
    for &(m,v) in programs::EQUAL[4] {
        let mut cs=base.clone();cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
        mixed_mcx(circ,&cs,p1,helpers);
    }
    // First R-ascent trueS256: rawA0,C0 and Work1[2] padding0. Its phase
    // stays unchanged. The phase11 trueS256 entry has Sign1 and was already excluded.
    let mut peak=base.clone();peak.extend(rank.iter().map(|q|(q,false)));peak.extend(a.iter().map(|q|(q,false)));peak.extend(c.iter().map(|q|(q,false)));peak.extend(sm.iter().map(|q|(q,false)));peak.push((&w1[2],false));
    mixed_mcx(circ,&peak,p1,helpers);
    // Terminal history lives in C_low6/S_mid[0..2], not an old shift byte.
    // Under S_upper0 only its low6 can be nonzero. Exclude rank29,A_low63,
    // C_low!=0 by XOR of all-C and C-zero cubes. Newly completed history0
    // still flips phase11->00; already-terminal j0 history was incremented.
    let mut terminal=base;terminal.extend((0..5).map(|i|(&rank[i],29>>i&1!=0)));terminal.extend(a.iter().map(|q|(q,true)));terminal.extend(sm.iter().map(|q|(q,false)));
    mixed_mcx(circ,&terminal,p1,helpers);terminal.extend(c.iter().map(|q|(q,false)));mixed_mcx(circ,&terminal,p1,helpers);
    circ.cx(p1,p2);
}

pub(super) fn step(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],post_j:usize,block:usize) {
    step_inner(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,post_j,block,false);
}
pub(super) fn before_exit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],post_j:usize,block:usize) {
    step_inner(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,post_j,block,true);
}
fn step_inner(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],post_j:usize,block:usize,prefix_only:bool) {
    assert!(post_j<4&&block<26&&helpers.len()>=24);let start=circ.b.ops.len();
    assert!(!super::metadata_muxlease::active("Q799_T11_COMPARE"),"unadapted direct comparison disabled");
    let entry_j=(post_j+3)%4;let (rfirst,tend)=super::shared_step::SCHEDULE_SUPPORTS[block];let rcap=259-rfirst;
    let(lo,hi)=super::metadata_entry_head5::A_SUPPORTS[block];
    let previous_support=circ.q797_a_support.replace((lo,hi));
    let sign=&helpers[0];let dirty=&helpers[1..];
    decode_birth(circ,rank,a,c,sm,p1,p2,w2,helpers,entry_j);
    loan(circ,rank,a,w1,sign,dirty);circ.ccx(p1,p2,sign);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    super::metadata_arithmetic5_encoded::phase10_with_support(circ,rank,a,c,p1,p2,sign,w1,w2,dirty,tend);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    circ.ccx(p1,p2,sign);loan(circ,rank,a,w1,sign,dirty);
    super::metadata_rotation5::rotate(circ,rank,a,p1,p2,w2,helpers,false);
    super::metadata_remainder015_funded::signless(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,entry_j,rcap);
    loan(circ,rank,a,w1,sign,dirty);circ.ccx(p1,p2,sign);
    super::metadata_remainder5_phased::phase00_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,entry_j,rcap);
    super::metadata_rotation5::rotate(circ,rank,a,p1,p2,w2,dirty,true);
    super::metadata_terminal5::emit(circ,rank,a,c,sm,dirty,post_j==0,false);
    super::metadata_phase_counter5::emit(circ,rank,a,c,sm,p1,p2,dirty,entry_j);
    super::metadata_entry_boundary5::entry_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,post_j,lo,hi);
    encode_birth(circ,rank,a,c,sm,p1,p2,sign,dirty,post_j);
    hide_birth(circ,rank,a,c,sm,p1,p2,dirty,post_j);
    super::q798_sign_erase::emit(circ,rank,a,c,sm,p1,p2,sign,w1,w2,dirty,post_j,(tend+1).min(258));
    hide_birth(circ,rank,a,c,sm,p1,p2,dirty,post_j);
    loan(circ,rank,a,w1,sign,dirty);
    if prefix_only {circ.q797_a_support=previous_support;return;}
    if post_j==0{super::metadata_exit_boundary5::exit_signless(circ,rank,a,c,sm,p1,p2,iteration,w1,w2,helpers,lo,hi);}
    s_zero_phase_flips(circ,rank,a,c,sm,p1,p2,w1,helpers,post_j);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);circ.b.ops.extend(tail);
    circ.q797_a_support=previous_support;
}
