//! Tagged stage-2 refill from the outside packet to the middle packet.
//!
//! C=W|delayed-D identifies an active switching escape. On that class the
//! boundary packet's size and raw SZ both hold M=bl(t_j), 98<=M<=128;
//! Q is positive, has at most128 bits, and has no idle counter. The body
//! returns the same raw SZ, replaces packet size by bl(Q), and retains C.
//! No raw SY word and raw SZ high word coexist on distinct allocations.
//!
//! The complete body is controlled as a literal unitary permutation.
//! Consequently C=0 restores every data/helper port even if the decoded
//! intermediate interpretation or conditional clean assertions fail there.

use crate::circuit::QubitId;
use super::super::builder::{B,G};
use super::super::frogdrop_col::{Fd,rec};
use super::super::joint_boundary::BoundaryView;
use super::super::mask::mc_xor;
use std::collections::BTreeSet;

/// XOR the three high bits of M into raw SZ high. The only admitted low
/// residues are0 and2..31:0 denotes128, and a nonzero residue denotes
/// 96+residue. Thus high3 is100 for zero and011 otherwise.
fn xor_m_high(b:&mut B,sz:&[QubitId],zero:QubitId,pre:QubitId,dirty:&[QubitId]) {
    let eq:Vec<_>=sz[..5].iter().map(|&q|(q,true)).collect();
    mc_xor(b,&eq,zero,&[pre],dirty);
    for &q in &sz[5..7] {b.x(q);b.cx(zero,q);}
    b.cx(zero,sz[7]);
    mc_xor(b,&eq,zero,&[pre],dirty);
}

/// The external dirty-control helper and C must never be hidden donors in
/// the recorded body. Reject opaque records rather than assuming ports.
fn excludes(record:&[G],forbidden:&[QubitId]) {
    for gate in record {
        let ports:Vec<QubitId>=match *gate {
            G::X(a)=>vec![a],
            G::Cx(a,z)|G::Swap(a,z)=>vec![a,z],
            G::Ccx(a,c,z)|G::AndC(a,c,z)|G::AndU(a,c,z)=>vec![a,c,z],
            _=>panic!("tagged refill requires literal unitary-compatible gates"),
        };
        assert!(ports.iter().all(|q|!forbidden.contains(q)),
            "tagged refill body touches its outer control/helper");
    }
}

/// `flags` and raw SZ are owned by the outside stage2 caller. Flags start
/// zero globally; raw SZ is M on C=1. C=1 implies no DONE counter, a valid
/// boundary active packet, and98<=M<=128. The distinct control helper is
/// arbitrary dirty data and is returned. Every supplied donor is restored.
#[allow(clippy::too_many_arguments)]
pub(crate) fn tagged_refill(b:&mut B,fd:&Fd,raw_sz:&[QubitId],tag:QubitId,
    flags:[QubitId;2],control_helper:QubitId,dirty:&[QubitId]) {
    assert_eq!(fd.sy.len(),5);assert_eq!(fd.q.len(),128);assert_eq!(raw_sz.len(),8);
    let [branch,case]=flags;
    assert!(raw_sz.iter().chain(flags.iter()).all(|q|
        !fd.q.contains(q)&&!fd.ring.contains(q)),
        "tagged refill size/flag owners overlap its data words");
    let view=BoundaryView::from_fd(fd);
    let mut occupied:BTreeSet<_>=view.ports().into_iter().collect();
    assert_eq!(occupied.len(),11);
    for &q in raw_sz.iter().chain(flags.iter()).chain([&tag,&control_helper]) {
        assert!(occupied.insert(q),"tagged refill owners alias");
    }
    // The Q prefix is actual input data even while its high five lanes are
    // encoded. Exclude the complete logical source from dirty decompositions.
    occupied.extend(fd.q.iter().copied());
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied()
        .filter(|q|!occupied.contains(q)&&seen.insert(*q)).collect();
    assert!(bank.len()>=9,"tagged refill needs nine restored dirty donors");
    let raw_sy:Vec<_>=fd.sy.iter().chain(raw_sz[5..8].iter()).copied().collect();
    let old_no_rows=b.no_rows;b.no_rows=true;
    let body=rec(b,|b| {
        // C implies SZ=M in98..128. Keep its existing low-five residue;
        // the exact M-high predicate clears only the three shared lanes
        // needed by the inverse codec. No encoded size-bit scan is needed.
        xor_m_high(b,raw_sz,branch,case,&bank);
        let boundary=super::super::joint_prefix::boundary_active_record(
            b,&raw_sy,&fd.q[123..128],fd.ph,branch,case,&bank);
        b.play(&boundary,true);
        // The decoded SY now equals M, while SZlow already holds Mlow.
        // Clear SYlow directly; its shared high lanes are cleared below.
        for i in 0..5 {b.cx(raw_sz[i],raw_sy[i]);}
        xor_m_high(b,raw_sz,branch,case,&bank);
        // All eight output lanes are now zero; length128 has its genuine
        // eighth output bit and cannot alias the not-found-yet sentinel0.
        super::msb_probe_range(b,&fd.q,0,128,&raw_sy,&[branch],case,&bank);
        let middle=super::super::joint_prefix::aligned_active_record(
            b,&raw_sy,&fd.q[123..128],fd.ph,branch,case,&bank);
        b.play(&middle,false);
        // Encoding returned SZhigh to zero. Restore the exact original M.
        xor_m_high(b,raw_sz,branch,case,&bank);
    });
    b.no_rows=old_no_rows;
    excludes(&body,&[tag,control_helper]);
    // This treats recorded AND compute/uncompute as actual controlled CCX
    // gates; it never measures an inactive dirty temporary or hides a row.
    b.play_ctrl_full_dirty(&body,tag,control_helper);
}
