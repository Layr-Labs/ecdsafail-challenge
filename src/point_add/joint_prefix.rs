//! Reversible prefix compression of a size and five high data/park bits.
//!
//! Source primitive only. This is NOT a physical allocation reduction until
//! every caller supplies the complete domain and all encoded readers.
//!
//! Care domain: 1<=SY<=128; H=0 if SY<=108, arbitrary H otherwise.
//! 108 + 20*32 = 748 states fit in ten bits instead of thirteen.
//! Low code r=SY-1 in [0,107]; high code r=32*(SY-105)+H in
//! [128,767]. The disjoint code classes are tagged by upper5>=4.
//! Encoding returns original SY[5..8] to zero and the supplied flag to zero.
//! All primitives are literal unitary gates, including every dirty helper.

use super::builder::{B, G};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// Exact disjoint dyadic cover of [109,256). No upper-domain assumption is
/// used to synthesize this predicate; input 128 remains represented exactly.
fn high_size(b: &mut B, sy: &[QubitId], flag: QubitId, dirty: &[QubitId]) {
    for (value, low_free) in [(109usize,0usize),(110,1),(112,4),(128,7)] {
        let lits: Vec<_> = (low_free..8)
            .map(|i| (sy[i], (value >> i) & 1 == 0)).collect();
        mc_xor(b, &lits, flag, &[], dirty);
    }
}

/// A complete record: replay forward to compress or backward to decode.
///
/// Encoded low5 lives in sy[0..5], encoded upper5 in high[0..5].
/// The three returned owners sy[5],sy[6],sy[7] may be lent ONLY while the
/// encoded representation is in effect and must be zero before decoding.
/// `flag` starts zero and is returned. All thirteen input owners are distinct;
/// at least nine distinct arbitrary dirty helpers remain outside every port.
///
/// Low-SY done counters are outside this domain. A caller MUST either use a
/// separately proved done-class codec or retain a complete enable around the
/// whole record and every borrower. This primitive does not authorize lending
/// conditionally returned owners as globally clean measurement ancillas.
pub(crate) fn record(b: &mut B, sy: &[QubitId], high: &[QubitId],
                     flag: QubitId, dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(sy.len(),8);
    assert_eq!(high.len(),5);
    let mut ports=BTreeSet::new();
    for q in sy.iter().chain(high).chain([&flag]) {
        assert!(ports.insert(*q), "joint prefix codec aliases a port");
    }
    let mut seen=BTreeSet::new();
    let donors: Vec<_> = dirty.iter().copied()
        .filter(|q|!ports.contains(q) && seen.insert(*q)).collect();
    assert!(donors.len()>=9, "joint prefix codec lacks dirty helpers");
    b.begin();
    high_size(b,sy,flag,&donors);
    // Both branches first subtract one. On the high branch subtract104
    // more, leaving the five-bit tag SY-105 in [4,23].
    b.begin();
    super::modp_frogdrop::add_const_exact(b,sy,None,1,&donors);
    let one=b.end(); b.play(&one,true);
    b.begin();
    super::modp_frogdrop::add_const_exact(b,sy,Some(flag),104,&donors);
    let rest=b.end(); b.play(&rest,true);
    for i in 0..5 { b.cswap(flag,sy[i],high[i]); }
    // High branch: sy5/sy6 already zero. Low branch: high is zero, so
    // these two controlled moves put the two remaining size bits into tag.
    // The first CX needs no control because its source is zero on high.
    b.x(flag);
    for i in 0..2 {
        b.cx(sy[5+i],high[i]);
        b.ccx(flag,high[i],sy[5+i]);
    }
    b.x(flag);
    // Erase the retained branch from the final disjoint tag, not from
    // metadata that has already been overwritten by the five payload bits.
    b.x(flag);
    let small: Vec<_> = high[2..5].iter().map(|&q|(q,true)).collect();
    mc_xor(b,&small,flag,&[],&donors);
    b.end()
}

fn ge_small(b:&mut B,v:&[QubitId],threshold:usize,out:QubitId,dirty:&[QubitId]) {
    assert!(threshold>0 && threshold<(1usize<<v.len()));
    // [v>=threshold]: the exact threshold word, plus every disjoint cube
    // whose first differing bit is a zero of threshold changed to one.
    let eq:Vec<_>=v.iter().enumerate().map(|(i,&q)|(q,(threshold>>i)&1==0)).collect();
    mc_xor(b,&eq,out,&[],dirty);
    for bit in 0..v.len() {
        if (threshold>>bit)&1!=0 {continue;}
        let mut lits:Vec<_>=(bit+1..v.len()).map(|i|(v[i],(threshold>>i)&1==0)).collect();
        lits.push((v[bit],false));
        mc_xor(b,&lits,out,&[],dirty);
    }
}

/// Aligned active-class codec including the phase bit.
///
/// Additional care bounds: SY109..112 has H<2^(SY-108); SY<=108 has H=0.
/// Active rank before phase folding:
///   SY1..108: SY-1;
///   SY109/110/111/112: 108/112/120/128 + H;
///   SY113..128: 160+32*(SY-113)+H.
/// Final rank is active_rank+672*phase. Bits0..4 remain on sy0..4;
/// bits5..10 are high0..4 followed by the original phase owner.
/// Every high data bit that can be live stays at its same encoded low-bit
/// index. This property is required by the piecewise masked-ripple view.
///
/// Both flags start/finish zero. No caller may apply this to done counters,
/// even though the final rank leaves enough capacity for a separate class.
pub(crate) fn aligned_active_record(b:&mut B,sy:&[QubitId],high:&[QubitId],
    phase:QubitId,branch:QubitId,case:QubitId,dirty:&[QubitId])->Vec<G> {
    assert_eq!(sy.len(),8);assert_eq!(high.len(),5);
    let mut ports=BTreeSet::new();
    for q in sy.iter().chain(high).chain([&phase,&branch,&case]) {
        assert!(ports.insert(*q),"aligned codec aliases a port");
    }
    let mut seen=BTreeSet::new();
    let donors:Vec<_>=dirty.iter().copied()
        .filter(|q|!ports.contains(q)&&seen.insert(*q)).collect();
    assert!(donors.len()>=9);
    b.begin();
    ge_small(b,sy,113,branch,&donors);
    b.begin();super::modp_frogdrop::add_const_exact(b,sy,None,1,&donors);
    let one=b.end();b.play(&one,true);
    b.begin();super::modp_frogdrop::add_const_exact(b,sy,Some(branch),107,&donors);
    let offset=b.end();b.play(&offset,true);
    // High branch tag SY-108 in5..20; low branch retains SY-1 in0..111.
    for i in 0..5 {b.cswap(branch,sy[i],high[i]);}
    // Descending source values are essential: a lower case may create
    // another source value (108+H can equal109), which has already passed.
    for (old,base,width) in [(111usize,128usize,4usize),(110,120,3),(109,112,2),(108,108,1)] {
        let input:Vec<_>=sy.iter().enumerate().map(|(i,&q)|(q,(old>>i)&1==0)).collect();
        mc_xor(b,&input,case,&[],&donors);
        let changed=old^base;
        for i in 0..8 {if(changed>>i)&1!=0{b.cx(case,sy[i]);}}
        for i in 0..width {b.cswap(case,sy[i],high[i]);}
        // The destination is an aligned interval of exactly2^width.
        // Other low cases, the high branch's raw H<=31, and the untouched
        // ordinary low range0..107 are outside this interval.
        let output:Vec<_>=(width..8).map(|i|(sy[i],(base>>i)&1==0)).collect();
        mc_xor(b,&output,case,&[],&donors);
    }
    b.x(branch);
    for i in 0..3 {
        b.cx(sy[5+i],high[i]);
        b.ccx(branch,high[i],sy[5+i]);
    }
    b.x(branch);
    ge_small(b,high,5,branch,&donors);
    // Old phase is the high bit of a six-bit tag. Change tag h+32*PH
    // into h+21*PH with a controlled low-five add and exact carry repair.
    // h is0..20; on PH1 newlow>=21 precisely when the new high bit is0.
    super::modp_frogdrop::add_const_exact(b,high,Some(phase),21,&donors);
    ge_small(b,high,21,phase,&donors);
    b.end()
}

/// The same normalized active rank, using only ONE returned clean flag.
/// This does not read or modify the phase owner. It permits a complete
/// V-boundary address bridge using three temporary raw-SY high owners and
/// one flag; all four return before the reciprocal core starts.
///
/// The high-branch witness is erased before medium cases from SY<32 and
/// H>=5: high SY is now raw payload, whereas every medium source is108..111.
/// Medium cases then return H to zero, so the high witness can be recovered
/// from H alone for the final low-word fold. No additional clean owner.
pub(crate) fn normalized_one_flag_record(b:&mut B,sy:&[QubitId],high:&[QubitId],
    flag:QubitId,dirty:&[QubitId])->Vec<G> {
    assert_eq!(sy.len(),8);assert_eq!(high.len(),5);
    let mut ports=BTreeSet::new();
    for q in sy.iter().chain(high).chain([&flag]) {
        assert!(ports.insert(*q),"normalized codec aliases a port");
    }
    let mut seen=BTreeSet::new();
    let donors:Vec<_>=dirty.iter().copied()
        .filter(|q|!ports.contains(q)&&seen.insert(*q)).collect();
    assert!(donors.len()>=10);
    b.begin();
    ge_small(b,sy,113,flag,&donors);
    b.begin();super::modp_frogdrop::add_const_exact(b,sy,None,1,&donors);
    let one=b.end();b.play(&one,true);
    b.begin();super::modp_frogdrop::add_const_exact(b,sy,Some(flag),107,&donors);
    let offset=b.end();b.play(&offset,true);
    for i in 0..5 {b.cswap(flag,sy[i],high[i]);}
    // Exact dyadic H>=5 cover:5,6..7,8..15,16..31.
    for (base,free) in [(5usize,0usize),(6,1),(8,3),(16,4)] {
        let mut ctl:Vec<_>=(free..5).map(|i|(high[i],(base>>i)&1==0)).collect();
        ctl.extend(sy[5..8].iter().map(|&q|(q,true)));
        mc_xor(b,&ctl,flag,&[],&donors);
    }
    for (old,base,width) in [(111usize,128usize,4usize),(110,120,3),(109,112,2),(108,108,1)] {
        let input:Vec<_>=sy.iter().enumerate().map(|(i,&q)|(q,(old>>i)&1==0)).collect();
        mc_xor(b,&input,flag,&[],&donors);
        for i in 0..8 {if((old^base)>>i)&1!=0{b.cx(flag,sy[i]);}}
        for i in 0..width {b.cswap(flag,sy[i],high[i]);}
        let output:Vec<_>=(width..8).map(|i|(sy[i],(base>>i)&1==0)).collect();
        mc_xor(b,&output,flag,&[],&donors);
    }
    ge_small(b,high,5,flag,&donors);
    b.x(flag);
    for i in 0..3 {b.cx(sy[5+i],high[i]);b.ccx(flag,high[i],sy[5+i]);}
    b.x(flag);
    ge_small(b,high,5,flag,&donors);
    b.end()
}

/// Global class wrapper using a binary done-counter format.
///
/// Entry `done` contains the exact retained done predicate. All other flags
/// start zero. On done, phase=1, SY1..26, high[4]=0 and high[0..4] hold
/// counter bits2..5; counter bit6 has a separate physical owner after the
/// public column159 relocation. Before159 that bit is provably zero.
/// On not-done, the complete aligned-active care domain is required.
///
/// Done rank=1536+16*(SY-1)+H4; active rank<=1343. Thus top two encoded
/// bits11 identify done without a retained class qubit. `done` is zero
/// on exit. Backward replay reconstructs it; caller then erases it from
/// the restored raw state using its ORIGINAL exact predicate.
///
/// This defines a reversible class codec, not the complete outer-stage
/// protocol. In particular a first-HT SY>128 state requires its own bridge.
pub(crate) fn global_record(b:&mut B,sy:&[QubitId],high:&[QubitId],
    phase:QubitId,done:QubitId,branch:QubitId,case:QubitId,
    control_helper:QubitId,dirty:&[QubitId])->Vec<G> {
    assert_eq!(sy.len(),8);assert_eq!(high.len(),5);
    let mut ports=BTreeSet::new();
    for q in sy.iter().chain(high).chain([&phase,&done,&branch,&case,&control_helper]) {
        assert!(ports.insert(*q),"global prefix codec aliases a port");
    }
    let mut seen=BTreeSet::new();
    let donors:Vec<_>=dirty.iter().copied()
        .filter(|q|!ports.contains(q)&&seen.insert(*q)).collect();
    assert!(donors.len()>=9);
    let active=aligned_active_record(b,sy,high,phase,branch,case,&donors);
    b.begin();
    b.x(done);
    b.play_ctrl_full_dirty(&active,done,control_helper);
    b.x(done);
    b.begin();
    super::modp_frogdrop::add_const_exact(b,&sy[..5],Some(done),1,&donors);
    let decrement=b.end();b.play(&decrement,true);
    // Nine-bit right rotation by4: [SY5,H4] -> [H4,SY5]. The constant
    // permutation has one cycle and eight controlled SWAP primitives.
    let slots:Vec<_>=sy[..5].iter().chain(&high[..4]).copied().collect();
    for j in 1..9 {b.cswap(done,slots[0],slots[(4*j)%9]);}
    b.cx(done,high[4]);
    b.ccx(phase,high[4],done);
    b.end()
}

fn ge_with(b:&mut B,word:&[QubitId],value:usize,target:QubitId,
    extra:&[(QubitId,bool)],dirty:&[QubitId]) {
    assert!(value>0&&value<(1usize<<word.len()));
    let mut eq:Vec<_>=word.iter().enumerate()
        .map(|(i,&q)|(q,(value>>i)&1==0)).collect();
    eq.extend_from_slice(extra);mc_xor(b,&eq,target,&[],dirty);
    for bit in 0..word.len() {
        if (value>>bit)&1!=0 {continue;}
        let mut term:Vec<_>=(bit+1..word.len())
            .map(|i|(word[i],(value>>i)&1==0)).collect();
        term.push((word[bit],false));term.extend_from_slice(extra);
        mc_xor(b,&term,target,&[],dirty);
    }
}

/// Asymmetric boundary packet. HR has Q<2^SY, whereas HT permits
/// Q<2^(SY+31). The latter is the unchanged public quotient envelope;
/// the symmetric middle packet is not valid on a raw HT column boundary.
///
/// HR rank: SY1..123 -> SY-1; SY124..127 -> 124/128/136/144+H;
/// SY128 ->160+H. HT local rank: SY1..92 ->SY-1;
/// SY93..96 ->92/96/104/112+H; SY97..128 ->128+32*(SY-97)+H.
/// Add192 to the HT rank. HR occupies [0,192), HT [192,1344).
/// Original SY5 temporarily supplies a sixth high-tag bit. Once the
/// offset is added, exchanging it with PH leaves the original phase in
/// SY5, where the final tag>=6 predicate erases it exactly.
pub(crate) fn boundary_active_record(b:&mut B,sy:&[QubitId],high:&[QubitId],
    phase:QubitId,branch:QubitId,case:QubitId,dirty:&[QubitId])->Vec<G> {
    assert_eq!(sy.len(),8);assert_eq!(high.len(),5);
    let mut occupied=BTreeSet::new();
    for q in sy.iter().chain(high).chain([&phase,&branch,&case]) {
        assert!(occupied.insert(*q),"boundary active codec aliases a port");
    }
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied()
        .filter(|q|!occupied.contains(q)&&seen.insert(*q)).collect();
    assert!(bank.len()>=9);
    rec_boundary(b,|b| {
        ge_with(b,sy,128,branch,&[(phase,true)],&bank);
        ge_with(b,sy,97,branch,&[(phase,false)],&bank);
        let one=rec_boundary(b,|b|
            super::modp_frogdrop::add_const_exact(b,sy,None,1,&bank));
        b.play(&one,true);
        for (ht,offset) in [(false,122u64),(true,92u64)] {
            if !ht {b.x(phase);}
            b.and_c(branch,phase,case);
            let sub=rec_boundary(b,|b|
                super::modp_frogdrop::add_const_exact(b,sy,Some(case),offset,&bank));
            b.play(&sub,true);
            b.and_u(branch,phase,case);
            if !ht {b.x(phase);}
        }
        // HR high tag5; HT high tags4..35. SY5 is the high tag bit.
        for i in 0..5 {b.cswap(branch,sy[i],high[i]);}
        for (ht,cases) in [
            (false,[(126usize,144usize,4usize),(125,136,3),(124,128,2),(123,124,1)]),
            (true,[(95usize,112usize,4usize),(94,104,3),(93,96,2),(92,92,1)]),
        ] {
            for (old,base,width) in cases {
                let mut input:Vec<_>=sy.iter().enumerate()
                    .map(|(i,&q)|(q,(old>>i)&1==0)).collect();
                input.push((phase,!ht));mc_xor(b,&input,case,&[],&bank);
                for i in 0..8 {if ((old^base)>>i)&1!=0 {b.cx(case,sy[i]);}}
                for i in 0..width {b.cswap(case,sy[i],high[i]);}
                let mut output:Vec<_>=(width..8)
                    .map(|i|(sy[i],(base>>i)&1==0)).collect();
                output.push((phase,!ht));mc_xor(b,&output,case,&[],&bank);
            }
        }
        // High SY5 may be one, so both halves of the low-word move
        // require the low-branch control, unlike the middle codec.
        b.x(branch);
        for i in 0..3 {
            b.ccx(branch,sy[5+i],high[i]);
            b.ccx(branch,high[i],sy[5+i]);
        }
        b.x(branch);
        let wide:Vec<_>=high.iter().copied().chain([sy[5]]).collect();
        ge_with(b,&wide,5,branch,&[(phase,true)],&bank);
        ge_with(b,&wide,4,branch,&[(phase,false)],&bank);
        super::modp_frogdrop::add_const_exact(b,&wide,Some(phase),6,&bank);
        b.swap(phase,sy[5]);
        let final_tag:Vec<_>=high.iter().copied().chain([phase]).collect();
        ge_small(b,&final_tag,6,sy[5],&bank);
    })
}

fn rec_boundary(b:&mut B,body:impl FnOnce(&mut B))->Vec<G> {
    b.begin();body(b);b.end()
}

/// Full boundary packet with the same binary DONE class as global_record.
/// `reverse_active` selects the pre-map epoch: HR has the wide Q word,
/// HT the narrow one. Only active PH is toggled before encoding; decoding
/// returns its original logical value. DONE retains PH=1 and rank1536+.
/// This packet requires an explicit separate first-HT/DQ transport.
#[allow(clippy::too_many_arguments)]
pub(crate) fn boundary_record(b:&mut B,sy:&[QubitId],high:&[QubitId],
    phase:QubitId,done:QubitId,branch:QubitId,case:QubitId,
    control_helper:QubitId,dirty:&[QubitId],reverse_active:bool)->Vec<G> {
    assert_eq!(sy.len(),8);assert_eq!(high.len(),5);
    let mut occupied=BTreeSet::new();
    for q in sy.iter().chain(high).chain([&phase,&done,&branch,&case,&control_helper]) {
        assert!(occupied.insert(*q),"boundary packet aliases a port");
    }
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied()
        .filter(|q|!occupied.contains(q)&&seen.insert(*q)).collect();
    assert!(bank.len()>=9);
    let active=boundary_active_record(b,sy,high,phase,branch,case,&bank);
    rec_boundary(b,|b| {
        if reverse_active {b.x(done);b.cx(done,phase);b.x(done);}
        b.x(done);b.play_ctrl_full_dirty(&active,done,control_helper);b.x(done);
        let one=rec_boundary(b,|b|
            super::modp_frogdrop::add_const_exact(b,&sy[..5],Some(done),1,&bank));
        b.play(&one,true);
        let slots:Vec<_>=sy[..5].iter().chain(&high[..4]).copied().collect();
        for j in 1..9 {b.cswap(done,slots[0],slots[(4*j)%9]);}
        b.cx(done,high[4]);b.ccx(phase,high[4],done);
    })
}
