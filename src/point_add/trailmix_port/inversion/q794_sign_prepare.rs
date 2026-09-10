//! Closed Sign address preparation; no extra qubits or clean helpers.
//! Active guard matches guarded prepare exactly. Off guard this is an arbitrary
//! reversible address extension, valid ONLY around guard-rooted closed gathers.
//! Never use as a drop-in replacement for callers that observe prepared state
//! outside those closed regions. Carry can be arbitrary; it is XOR-updated.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::point_add::trailmix_port::inversion::{length_recompute::mixed_mcx,metadata_arithmetic5_encoded};

pub(crate) fn emit(circ:&mut Circuit,c:&[QReg],sm:&[QReg],guard:&QReg,carry:Option<&QReg>,helpers:&[QReg],j:usize,inverse:bool){
    if std::env::var("Q794_SIGN_PREPARE_RIPPLE").ok().as_deref()!=Some("1"){
        crate::point_add::trailmix_port::inversion::metadata_phase115_phased::prepare(circ,c,sm,guard,carry,helpers,j,inverse);return;
    }
    assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(j<4);
    let z=carry.expect("closed Sign prepare needs its existing carry rail");
    let mut ids:Vec<_>=c.iter().chain(sm).chain(helpers).map(QReg::id).collect();
    ids.extend([guard.id(),z.id()]);ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"closed Sign prepare aliases");
    let start=circ.b.ops.len();let word:Vec<_>=c.iter().chain(std::iter::once(z)).collect();
    let low=(4-j)%4;
    // Add the two compile-time virtual low S bits to the existing seven-bit
    // C/carry word. Descending targets use the ORIGINAL lower-bit predicate.
    for i in 0..2{if low>>i&1==0{continue;}for k in (i..7).rev(){
        let controls:Vec<_>=word[i..k].iter().map(|&q|(q,true)).collect();
        if std::env::var("Q794_SIGN_PREPARE_CLEAN").ok().as_deref()==Some("1") {
            // Guard is conditionally zero after X. Offguard target predicates
            // may differ, but every source and the guard are restored exactly.
            circ.x(guard);
            crate::point_add::trailmix_port::inversion::paired_clean_mcx::toggle(circ,&controls,word[k],guard);
            circ.x(guard);
        } else {mixed_mcx(circ,&controls,word[k],helpers);}
    }}
    // Add 4*sm to the high C nibble and XOR overflow into the SAME carry.
    // This adder restores sm and needs no quantum scratch or clean carry.
    metadata_arithmetic5_encoded::add(circ,sm,&c[2..],Some(z),false);
    if inverse{circ.b.ops[start..].reverse();}
}
