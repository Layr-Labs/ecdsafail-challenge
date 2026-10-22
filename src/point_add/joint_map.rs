//! Literal reversible building blocks for the joint map metadata format.
//!
//! These routines allocate no wires. The complete map wrapper has to supply
//! and restore their explicit ports; merely declaring this module does not
//! enable a compressed layout.

use super::super::builder::{B, G};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;

fn record(b: &mut B, f: impl FnOnce(&mut B)) -> Vec<G> {
    b.begin();
    f(b);
    b.end()
}

fn unique(ports: &[QubitId]) {
    let mut seen = std::collections::HashSet::new();
    for &q in ports { assert!(seen.insert(q.0), "joint-map port alias"); }
}

/// XOR [word >= bound] into target. The disjoint binary cover is exact
/// on every word, including unused codes. No clean prefix is assumed.
pub(crate) fn xor_ge(b: &mut B, word: &[QubitId], bound: usize,
                     target: QubitId, dirty: &[QubitId]) {
    assert!(word.len() < usize::BITS as usize);
    let ports: Vec<_> = word.iter().copied().chain([target]).collect();
    unique(&ports);
    let bank: Vec<_> = dirty.iter().copied().filter(|q| !ports.contains(q)).collect();
    let end = 1usize << word.len();
    let mut at = bound.min(end);
    while at < end {
        let free = if at == 0 { word.len() }
                   else { (at.trailing_zeros() as usize).min(word.len()) };
        let controls: Vec<_> = (free..word.len())
            .map(|i| (word[i], at >> i & 1 == 0)).collect();
        mc_xor(b, &controls, target, &[], &bank);
        at += 1usize << free;
    }
}

/// target += zero_extend(source), modulo target width. Dirty padding is
/// restored by TTK and its high contribution is then subtracted exactly.
/// Neither the padding nor an overflow lane is assumed clean.
pub(crate) fn add_zero_extended(b: &mut B, source: &[QubitId],
                               target: &[QubitId], dirty: &[QubitId]) {
    assert!(source.len() >= 2 && target.len() >= source.len());
    let ports: Vec<_> = source.iter().chain(target).copied().collect();
    unique(&ports);
    let npad = target.len() - source.len();
    let mut pad = Vec::new();
    for &q in dirty {
        if pad.len() == npad { break; }
        if !ports.contains(&q) && !pad.contains(&q) { pad.push(q); }
    }
    assert_eq!(pad.len(), npad, "joint-map dirty padding short");
    let padded: Vec<_> = source.iter().chain(&pad).copied().collect();
    super::super::arith::ttk_add(b, &padded, target, None, None);
    match npad {
        0 => {},
        1 => b.cx(pad[0], target[source.len()]),
        _ => {
            let remove = record(b, |b| super::super::arith::ttk_add(
                b, &pad, &target[source.len()..], None, None));
            b.play(&remove, true);
        }
    }
}

/// Record the in-place radix conversion 64*a+u -> 63*a+u on thirteen
/// lanes, low first. Care domain: 0<=a<=92, 0<=u<=62; flags are zero.
/// All three flags and all dirty donors return exactly. The recorded tape
/// is unitary and its inverse restores the original ports, including in a
/// controlled replay. The care restriction is used only for flag cleanup.
pub(crate) fn radix63_record(b: &mut B, low: &[QubitId], high: &[QubitId],
                            flags: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(low.len(), 6);
    assert_eq!(high.len(), 7);
    assert_eq!(flags.len(), 3);
    let ports: Vec<_> = low.iter().chain(high).chain(flags).copied().collect();
    unique(&ports);
    let bank: Vec<_> = dirty.iter().copied().filter(|q| !ports.contains(q)).collect();
    let (a, borrow, overflow) = (flags[0], flags[1], flags[2]);
    record(b, |b| {
        // a = original floor(high/64). Subtract its low six bits from u;
        // the seventh target bit is exactly the unsigned borrow.
        b.cx(high[6], a);
        let low_with_borrow: Vec<_> = low.iter().copied().chain([borrow]).collect();
        let subtract = record(b, |b| add_zero_extended(b, &high[..6], &low_with_borrow, &bank));
        b.play(&subtract, true);
        // high' = high - a - borrow; low' = (u - (high mod64)) mod64.
        // Hence 64*high'+low' is exactly 63*original_high+original_u.
        for flag in [a, borrow] {
            let decrement = record(b, |b| super::super::modp_frogdrop::add_const_exact(
                b, high, Some(flag), 1, &bank));
            b.play(&decrement, true);
        }
        // The old high-bit is now [rank>=4032], equivalently [high'>=63].
        // Save the parity of the total decrement on borrow before erasing a.
        b.cx(a, borrow);
        xor_ge(b, high, 63, a, &bank);
        // Let d=original_high-high'. Since original_u<=62,
        // floor((high'+low')/63)=d. Its parity clears the remaining flag.
        let sum: Vec<_> = high.iter().copied().chain([overflow]).collect();
        let sum_record = record(b, |b| add_zero_extended(b, low, &sum, &bank));
        b.play(&sum_record, false);
        xor_ge(b, &sum, 63, borrow, &bank);
        xor_ge(b, &sum, 126, borrow, &bank);
        b.play(&sum_record, true);
    })
}

/// XOR membership in [lo,hi), intersected with one residue modulo2^bits.
/// Intersections of the disjoint binary interval cover remain disjoint.
fn xor_interval_residue(b: &mut B, word: &[QubitId], lo: usize, hi: usize,
                        bits: usize, residue: usize, target: QubitId,
                        dirty: &[QubitId]) {
    assert!(bits <= word.len() && hi <= 1usize << word.len());
    assert!(residue < 1usize << bits && lo <= hi);
    let mut at = lo;
    while at < hi {
        let aligned = if at == 0 { word.len() } else { at.trailing_zeros() as usize };
        let remaining = (usize::BITS - 1 - (hi-at).leading_zeros()) as usize;
        let free = aligned.min(remaining).min(word.len());
        let fixed_low_mask = ((1usize << bits)-1) & !((1usize << free)-1);
        if (at ^ residue) & fixed_low_mask == 0 {
            let mut controls: Vec<_> = (free..word.len())
                .map(|i| (word[i], at >> i & 1 == 0)).collect();
            controls.extend((0..free.min(bits)).map(|i| (word[i], residue >> i & 1 == 0)));
            mc_xor(b, &controls, target, &[], dirty);
        }
        at += 1usize << free;
    }
}

fn xor_interval(b: &mut B, word: &[QubitId], lo: usize, hi: usize,
                target: QubitId, dirty: &[QubitId]) {
    xor_interval_residue(b, word, lo, hi, 0, 0, target, dirty);
}

fn constant(b: &mut B, word: &[QubitId], value: usize, subtract: bool, dirty: &[QubitId]) {
    let r = record(b, |b| super::super::modp_frogdrop::add_const_exact(
        b, word, None, value as u64, dirty));
    b.play(&r, subtract);
}

fn rotate_up(b: &mut B, word: &[QubitId], amount: usize) {
    let n = word.len();
    let amount = amount % n;
    if amount == 0 { return; }
    let (mut a, mut d) = (n, amount);
    while d != 0 { let rem = a%d; a=d; d=rem; }
    for start in 0..a {
        let orbit: Vec<_> = (0..n/a).map(|i| word[(start+i*amount)%n]).collect();
        for i in (1..orbit.len()).rev() { b.swap(orbit[i], orbit[i-1]); }
    }
}

/// Compress the partial-max map ABI to the structured thirteen-bit rank.
///
/// Entry: `u` is six bits, u=0 for e=0 and u=2e-1+t otherwise. `w` is
/// eight bits: M-1 when H=0; otherwise 128+8*(M-126)+H. Here 1<=M<=128,
/// 0<=e<=min(31,M-1), and 0<=H<2^max(0,M-125). All three flags are zero.
/// Exit: [u,w] holds the structured rank0..8148; w[7] and all flags are
/// zero. Its exact inverse restores the original partial-max ABI.
///
/// Each branch maps downward below every later branch's input interval.
/// Its output lies in a disjoint rank block (or residue within that block),
/// so the branch flag is erased from the output without retaining a tag.
/// The main radix63 branch borrows w[7] only conditionally: that bit is
/// zero on this branch, and the complete controlled tape is identity off
/// it. All lowering uses literal unitary gates, including dirty replay.
pub(crate) fn structured_record(b: &mut B, u: &[QubitId], w: &[QubitId],
                               flags: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(u.len(), 6);
    assert_eq!(w.len(), 8);
    assert_eq!(flags.len(), 3);
    let ports: Vec<_> = u.iter().chain(w).chain(flags).copied().collect();
    unique(&ports);
    let mut available = Vec::new();
    for &q in dirty {
        if !ports.contains(&q) && !available.contains(&q) { available.push(q); }
    }
    let helper = *available.first().expect("joint-map controlled replay donor");
    let bank = &available[1..];
    // The thirteen-bit constant additions need at least14 distinct dirty
    // donors (the existing map's ring/P dirty bank supplies these).
    assert!(bank.len() >= 14);
    let word: Vec<_> = u.iter().chain(w).copied().collect();
    let flag = flags[0];
    record(b, |b| {
        for branch in 0..10 {
            let (in_lo, in_hi, out_lo, out_hi, residue_bits, residue_zero) = match branch {
                0 => (0,8,0,128,0,true),
                1 => (8,16,128,384,0,true),
                2 => (16,32,384,1408,0,true),
                3 => (32,125,1408,7267,0,true),
                4 => (125,126,7267,7393,1,true),
                5 => (126,127,7393,7645,2,true),
                6 => (127,128,7645,8149,3,true),
                7 => (129,130,7267,7393,1,false),
                8 => (137,140,7393,7645,2,false),
                9 => (145,152,7645,8149,3,false),
                _ => unreachable!(),
            };
            xor_interval(b, w, in_lo, in_hi, flag, bank);
            let transform = record(b, |b| {
                match branch {
                    0 => {
                        // u<16, M-1<8: move the three M bits into the
                        // two zero high-u bits and the old lowest M bit.
                        for i in 0..3 { b.swap(word[4+i],word[6+i]); }
                    },
                    1 => {
                        b.x(w[3]); // M-9 = (M-1)-8
                        for i in 0..3 { b.swap(word[5+i],word[6+i]); }
                        constant(b,&word,128,false,bank);
                    },
                    2 => constant(b,&word,640,true,bank),
                    3 => {
                        constant(b,w,32,true,bank);
                        let radix = radix63_record(b,u,&w[..7],&[w[7],flags[1],flags[2]],bank);
                        b.play(&radix,false);
                        constant(b,&word,1408,false,bank);
                    },
                    4..=6 => {
                        let value = 125+branch-4;
                        for (i,&q) in w.iter().enumerate() { if value>>i&1!=0 { b.x(q); } }
                        rotate_up(b,&word[..6+residue_bits],residue_bits);
                        constant(b,&word,out_lo,false,bank);
                    },
                    7..=9 => {
                        let fixed = 128+8*(branch-7);
                        for (i,&q) in w.iter().enumerate() { if fixed>>i&1!=0 { b.x(q); } }
                        rotate_up(b,&word[..6+residue_bits],residue_bits);
                        constant(b,&word,out_lo,false,bank);
                    },
                    _ => unreachable!(),
                }
            });
            b.play_ctrl_full_dirty(&transform,flag,helper);
            // The H-zero and H-nonzero cases share a rank block. The low
            // residue of rank-base distinguishes them without another flag.
            if residue_bits == 0 {
                xor_interval(b,&word,out_lo,out_hi,flag,bank);
            } else {
                let zero = out_lo & ((1usize<<residue_bits)-1);
                for residue in 0..1usize<<residue_bits {
                    if (residue == zero) == residue_zero {
                        xor_interval_residue(b,&word,out_lo,out_hi,residue_bits,residue,flag,bank);
                    }
                }
            }
        }
    })
}

/// Core partial-max format: M<=125 has w=M-1; M>=126 has
/// w=128+8*(M-126)+H, including H=0. Thus w7 is the immutable high-M
/// tag and its low three bits are the actual high-Q data on that branch.
///
/// Expose M-1 in w[..7] and H in three zero target ports; w7 returns0.
/// The inverse accepts a changed H provided H<2^max(0,M-125), so a whole
/// Q rotation or Q/ring swap may run between the two records. The caller
/// must restore the raw M view and return all three H ports by the inverse.
pub(crate) fn materialize_record(b: &mut B, w: &[QubitId], high: &[QubitId],
                                dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(w.len(),8);
    assert_eq!(high.len(),3);
    let ports: Vec<_> = w.iter().chain(high).copied().collect();
    unique(&ports);
    let bank: Vec<_> = dirty.iter().copied().filter(|q| !ports.contains(q)).collect();
    record(b, |b| {
        for i in 0..3 { b.ccx(w[7],w[i],high[i]); }
        for i in 0..3 { b.cx(high[i],w[i]); }
        b.cswap(w[7],w[0],w[3]);
        b.cswap(w[7],w[1],w[4]);
        super::super::modp_frogdrop::add_const_exact(b,&w[..7],Some(w[7]),125,&bank);
        xor_ge(b,&w[..7],125,w[7],&bank);
    })
}

fn xor_range_controls(b: &mut B, word: &[QubitId], lo: usize, hi: usize,
                      outside: &[(QubitId,bool)], target: QubitId, clean: &[QubitId], dirty: &[QubitId]) {
    assert!(lo<=hi && hi<=1usize<<word.len());
    let mut at=lo;
    while at<hi {
        let aligned=if at==0 {word.len()}else{at.trailing_zeros() as usize};
        let remaining=(usize::BITS-1-(hi-at).leading_zeros()) as usize;
        let free=aligned.min(remaining).min(word.len());
        let mut controls=outside.to_vec();
        controls.extend((free..word.len()).map(|i|(word[i],at>>i&1==0)));
        mc_xor(b,&controls,target,clean,dirty);
        at+=1usize<<free;
    }
}

/// Effective M predicate while low-M shots hold M-1-e on widened epochs.
/// High-M shots keep their base tag and H bits unchanged, so their M-e
/// predicate reads only tag bits3/4/7, the five e bits, and the held widening
/// control. In particular it never reads W0..2 while a high-Q ripple uses
/// those ports as temporary carries. `wide=None` selects the base epoch.
pub(crate) fn xor_max_ge(b: &mut B, w: &[QubitId], ez: &[QubitId],
                        wide: Option<(QubitId,bool)>, bound: usize,
                        target: QubitId, dirty: &[QubitId]) {
    xor_max_ge_clean(b,w,ez,wide,bound,target,&[],dirty);
}

/// `clean` is zero only at this complete predicate boundary and is returned
/// before the caller's body. No decoder prefix survives across a map row.
/// Paired replay converts both AND forms to literal CCX; its all-data U and
/// exact inverse remain the same tape even on skipped dirty-helper shots.
#[allow(clippy::too_many_arguments)]
fn xor_max_ge_clean(b: &mut B, w: &[QubitId], ez: &[QubitId],
                    wide: Option<(QubitId,bool)>, bound: usize,
                    target: QubitId, clean: &[QubitId], dirty: &[QubitId]) {
    assert_eq!(w.len(),8);
    assert_eq!(ez.len(),5);
    if bound==0 {b.x(target);return;}
    if bound>128 {return;}
    let mut ports:Vec<_>=w.iter().chain(ez).copied().collect();
    ports.push(target);
    if let Some((q,_))=wide {ports.push(q);}
    ports.extend_from_slice(clean);
    unique(&ports);
    let bank:Vec<_>=dirty.iter().copied().filter(|q|!ports.contains(q)).collect();
    xor_range_controls(b,&w[..7],bound-1,128,&[(w[7],true)],target,clean,&bank);
    for tag in 0..3 {
        let base=126+tag;
        let mut c=vec![(w[7],false),(w[3],tag&1==0),(w[4],tag&2==0)];
        if let Some((q,neg))=wide {
            c.push((q,!neg)); // widening predicate is false
            if base>=bound {mc_xor(b,&c,target,clean,&bank);}
            c.pop();c.push((q,neg));
            if base>=bound {
                xor_range_controls(b,ez,0,(base-bound+1).min(32),&c,target,clean,&bank);
            }
        }else if base>=bound {mc_xor(b,&c,target,clean,&bank);}
    }
}

pub(crate) fn xor_max_eq(b: &mut B, w: &[QubitId], ez: &[QubitId],
                        wide: Option<(QubitId,bool)>, value: usize,
                        target: QubitId, dirty: &[QubitId]) {
    xor_max_eq_clean(b,w,ez,wide,value,target,&[],dirty);
}

#[allow(clippy::too_many_arguments)]
fn xor_max_eq_clean(b: &mut B, w: &[QubitId], ez: &[QubitId],
                    wide: Option<(QubitId,bool)>, value: usize,
                    target: QubitId, clean: &[QubitId], dirty: &[QubitId]) {
    assert_eq!(w.len(),8);assert_eq!(ez.len(),5);
    if value==0 || value>128 {return;}
    let mut ports:Vec<_>=w.iter().chain(ez).copied().chain([target]).collect();
    if let Some((q,_))=wide {ports.push(q);}
    ports.extend_from_slice(clean);
    unique(&ports);
    let bank:Vec<_>=dirty.iter().copied().filter(|q|!ports.contains(q)).collect();
    let mut low=vec![(w[7],true)];
    low.extend(w[..7].iter().enumerate().map(|(i,&q)|(q,(value-1)>>i&1==0)));
    mc_xor(b,&low,target,clean,&bank);
    for tag in 0..3 {
        let base=126+tag;
        let mut c=vec![(w[7],false),(w[3],tag&1==0),(w[4],tag&2==0)];
        if let Some((q,neg))=wide {
            if base==value {c.push((q,!neg));mc_xor(b,&c,target,clean,&bank);c.pop();}
            if base>=value && base-value<32 {
                c.push((q,neg));
                c.extend(ez.iter().enumerate().map(|(i,&q)|(q,(base-value)>>i&1==0)));
                mc_xor(b,&c,target,clean,&bank);
            }
        }else if base==value {mc_xor(b,&c,target,clean,&bank);}
    }
}

/// Only low-M shots change their stored M-1 during widening. The high-M
/// tag/H word stays fixed; its address queries account for e explicitly.
/// `flag` is zero and returned. The emitted record subtracts e on widening
/// shots; play its exact inverse to restore the base-M epoch.
pub(crate) fn low_widen_record(b: &mut B, w: &[QubitId], ez: &[QubitId],
                              wide: (QubitId,bool), flag: QubitId,
                              dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(w.len(),8);assert_eq!(ez.len(),5);
    let ports:Vec<_>=w.iter().chain(ez).copied().chain([wide.0,flag]).collect();
    unique(&ports);
    let mut bank=Vec::new();
    for &q in dirty {if !ports.contains(&q)&&!bank.contains(&q){bank.push(q);}}
    let helper=bank.remove(0);
    record(b,|b|{
        let controls=[wide,(w[7],true)];
        mc_xor(b,&controls,flag,&[],&bank);
        let add=record(b,|b|add_zero_extended(b,ez,&w[..7],&bank));
        let subtract:Vec<_>=add.iter().rev().copied().collect();
        // add_zero_extended is fully unitary (X/CX/CCX); reversing its
        // primitive list is its exact inverse.
        b.play_ctrl_full_dirty(&subtract,flag,helper);
        mc_xor(b,&controls,flag,&[],&bank);
    })
}

/// Map scratch in the partial-max epoch. The three physical high-Q ports
/// have become t/c0/e. Logical Q125..127 live in W on high-M shots.
pub(crate) struct Core {
    pub w: Vec<QubitId>,
    pub ez: Vec<QubitId>,
    pub t: QubitId,
    pub c0: QubitId,
    pub e: QubitId,
    pub g: QubitId,
    pub h: QubitId,
    /// Original public operand bound, independent of the full target span
    /// retained by controlled-map rows. Q above it is zero on enabled shots.
    pub source_bound: usize,
    /// Late plain maps park the three counter passengers outside low_q;
    /// Wlow7 is then the ordinary maximum-minus1 and W7 stays clean.
    pub raw_cut: bool,
    /// Only the raw-cut branch supplies SW and the complemented HT phase.
    /// Both are globally clean for the whole map and returned at its end.
    pub row_helpers: Vec<QubitId>,
    pub dirty: Vec<QubitId>,
}

impl Core {
    fn check(&self, ring: &[QubitId], low_q: &[QubitId]) {
        assert_eq!(self.w.len(),8);assert_eq!(self.ez.len(),5);
        if self.raw_cut {assert!(self.source_bound<=low_q.len() && low_q.len()<=121);}
        else {assert_eq!(low_q.len(),125);assert!(self.row_helpers.is_empty());}
        assert!((2..=128).contains(&self.source_bound));
        let ports:Vec<_>=ring.iter().chain(low_q).chain(&self.w).chain(&self.ez)
            .copied().chain([self.t,self.c0,self.e,self.g,self.h])
            .chain(self.row_helpers.iter().copied()).collect();
        unique(&ports);
        assert!(self.dirty.iter().all(|q|!ports.contains(q)));
    }

    fn max_ge(&self,b:&mut B,wide:Option<(QubitId,bool)>,bound:usize,
              target:QubitId,clean:&[QubitId]) {
        if self.raw_cut {
            if bound==0 {b.x(target);}
            else if bound<=128 {xor_range_controls(b,&self.w[..7],bound-1,128,
                &[],target,clean,&self.dirty);}
        } else {xor_max_ge_clean(b,&self.w,&self.ez,wide,bound,target,clean,&self.dirty);}
    }

    fn max_eq(&self,b:&mut B,wide:Option<(QubitId,bool)>,value:usize,
              target:QubitId,clean:&[QubitId]) {
        if self.raw_cut {
            if (1..=128).contains(&value) {
                let c:Vec<_>=self.w[..7].iter().enumerate()
                    .map(|(i,&q)|(q,(value-1)>>i&1==0)).collect();
                mc_xor(b,&c,target,clean,&self.dirty);
            }
        } else {xor_max_eq_clean(b,&self.w,&self.ez,wide,value,target,clean,&self.dirty);}
    }

    fn widen_record(&self,b:&mut B,wide:(QubitId,bool))->Vec<G> {
        if !self.raw_cut {return low_widen_record(b,&self.w,&self.ez,wide,self.c0,&self.dirty);}
        // M-1>=e on every active and DONE map. The seven-bit subtraction
        // therefore remains an ordinary size; the extra W7 owner is idle.
        let add=record(b,|b|super::super::arith::ttk_add(b,
            &self.ez.iter().copied().chain([self.g,self.h]).collect::<Vec<_>>(),
            &self.w[..7],Some(wide.0),None));
        record(b,|b| {
            if wide.1 {b.x(wide.0);}
            b.play(&add,true);
            if wide.1 {b.x(wide.0);}
        })
    }

    /// f=[lane<cut], cut=N-effectiveM. Each query returns its clean bank
    /// before body; body must return those same owners before the next query.
    fn walk(&self,b:&mut B,n:usize,lo:usize,hi:usize,wide:Option<(QubitId,bool)>,
            f:QubitId,clean:&[QubitId],mut body:impl FnMut(&mut B,usize,QubitId)) {
        if lo>=hi{return;}
        b.x(f);
        self.max_ge(b,wide,n-lo,f,clean);
        for l in lo..hi {
            if l>lo {self.max_eq(b,wide,n-l,f,clean);}
            body(b,l,f);
        }
        // At lane hi-1 the held predicate is effectiveM<=N-hi.
        b.x(f);
        self.max_ge(b,wide,n-hi+1,f,clean);
    }

    fn stages(&self,b:&mut B,flag:(QubitId,bool),reverse:bool,
              mut body:impl FnMut(&mut B,usize,QubitId)) {
        let order:Vec<_>=if reverse {(0..5).rev().collect()}else{(0..5).collect()};
        for k in order {
            let c=[flag,(self.ez[k],false)];
            mc_xor(b,&c,self.c0,&[],&self.dirty);
            body(b,k,self.c0);
            mc_xor(b,&c,self.c0,&[],&self.dirty);
        }
    }

    fn ring_rotate(&self,b:&mut B,ring:&[QubitId],flag:(QubitId,bool),up:bool) {
        let r=record(b,|b|self.stages(b,flag,false,|b,k,c|super::crot_up(b,c,ring,1usize<<k)));
        b.play(&r,!up);
    }

    fn q_rotate(&self,b:&mut B,low_q:&[QubitId],m:usize,flag:(QubitId,bool),down:bool) {
        let high=[self.e,self.g,self.h];
        let expose=if self.raw_cut {vec![]}else{materialize_record(b,&self.w,&high,&self.dirty)};
        b.play(&expose,false);
        let q:Vec<_>=if self.raw_cut {low_q.to_vec()}else{low_q.iter().copied().chain(high).collect()};
        assert!(self.source_bound<=m);
        let mut support:std::collections::BTreeSet<usize>=(0..self.source_bound).collect();
        let r=record(b,|b|self.stages(b,flag,false,|b,k,c|{
            let step=(1usize<<k)%q.len();
            super::crot_up_care(b,c,&q,step,&support);
            let shifted:Vec<_>=support.iter().map(|&i|(i+step)%q.len()).collect();
            support.extend(shifted);
        }));
        b.play(&r,down);
        b.play(&expose,true);
    }

    fn shift(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,
             flag:(QubitId,bool),up:bool) {
        let n=ring.len();
        self.stages(b,flag,up,|b,k,c|{
            let s=1usize<<k;
            if s>=hi {return;}
            let r=record(b,|b|{
                // This is the parent's complete region shift. The retained
                // mask selects every original destination, including low
                // cells below the public variable interval.
                for l in s..lo.max(s) {b.cswap(c,ring[l],ring[l-s]);}
                // c0 holds this stage's control. e is zero throughout the
                // shift; g is returned by every complete controlled swap.
                self.walk(b,n,lo.max(s),hi,Some(flag),self.h,&[self.g,self.e],|b,l,f|{
                    b.and_c(c,f,self.g);
                    b.cswap(self.g,ring[l],ring[l-s]);
                    b.and_u(c,f,self.g);
                });
            });
            b.play(&r,up);
        });
    }

    fn pminus(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,
              tail:usize,flag:(QubitId,bool)) {
        assert!(lo>42+tail && hi<=ring.len());
        let r=record(b,|b|{
            for &q in &ring[..lo.min(256)] {b.x(q);}
            // The enclosing control implies widening. Use a separate
            // returned constant-one port inside the record so the outer
            // control never aliases one of its own inner operands.
            b.x(self.g);
            // e is returned before the later constant subtractor. g is
            // held one and c0 is the outside replay helper: neither is lent.
            self.walk(b,ring.len(),lo,hi.min(256),Some((self.g,false)),self.h,&[self.e],
                |b,l,f|b.cx(f,ring[l]));
            b.x(self.g);
            super::sub_const_dirty(b,&ring[..10+tail],976,self.e,&self.dirty);
            super::sub_const_dirty(b,&ring[32..33+tail],1,self.e,&self.dirty);
        });
        if flag.1 {b.x(flag.0);}
        b.play_ctrl_full(&r,flag.0,self.c0);
        if flag.1 {b.x(flag.0);}
    }

    fn swap_operands(&self,b:&mut B,ring:&[QubitId],low_q:&[QubitId],lo:usize,hi:usize) {
        let high=[self.e,self.g,self.h];
        let expose=if self.raw_cut {vec![]}else{materialize_record(b,&self.w,&high,&self.dirty)};
        b.play(&expose,false);
        let q:Vec<_>=if self.raw_cut {low_q.to_vec()}else{low_q.iter().copied().chain(high).collect()};
        let cut=super::Cut{v:self.w[..7].to_vec(),a:ring.len() as isize-1,neg:true};
        // W7 is zero for this complete raw epoch; empty decoder prefixes
        // leave it untouched except as a returned query temp.
        super::masked_swapf(b,ring,&q,&cut,lo,hi,self.c0,&[],self.w[7],&self.dirty);
        b.play(&expose,true);
    }

    /// Variable frame rotation for cut=N-1-effective(M-1). Low-M words
    /// are already adjusted; high-M words subtract e only during rotation.
    fn frame_rotation(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize)->Vec<G> {
        if self.raw_cut {return record(b,|b|
            super::rot_by_range(b,ring,&self.w[..7],lo-1,hi-1,false,&self.dirty));}
        let high=[self.e,self.g,self.h];
        record(b,|b|{
            let expose=materialize_record(b,&self.w,&high,&self.dirty);
            b.play(&expose,false);
            super::rot_by_range(b,ring,&self.w[..7],lo-1,hi-1,false,&self.dirty);
            xor_ge(b,&self.w[..7],125,self.w[7],&self.dirty);
            for k in 0..5 {
                let c=[(self.w[7],false),(self.t,false),(self.ez[k],false)];
                mc_xor(b,&c,self.c0,&[],&self.dirty);
                super::crot_up(b,self.c0,ring,ring.len()-(1usize<<k)%ring.len());
                mc_xor(b,&c,self.c0,&[],&self.dirty);
            }
            xor_ge(b,&self.w[..7],125,self.w[7],&self.dirty);
            b.play(&expose,true);
        })
    }

    fn frame(&self,b:&mut B,ring:&[QubitId],low_q:&[QubitId],
             par:&super::MapPar,inverse:bool) {
        let n=ring.len();
        let (llo,lhi)=(n-par.chi,n-par.clo);
        assert!(0<llo && llo<=lhi && lhi<n && par.m<=128 && par.m>=2);
        assert!(self.source_bound<=par.m);
        // Normalization has returned a word <= the original operand bound.
        // These suffix lanes are clean throughout the complete frame on
        // enabled shots. Paired replay uses a literal all-data U/U^-1 on
        // skipped shots, so their counter contents need not be zero there.
        let mut anc=low_q[self.source_bound.min(low_q.len())..].to_vec();
        if self.raw_cut {anc.push(self.w[7]);anc.extend_from_slice(&self.row_helpers);}
        let r=record(b,|b|{
            let rot=self.frame_rotation(b,ring,llo,lhi);
            b.play(&rot,false);
            let v:Vec<_>=(0..n).map(|i|ring[(i+n-1)%n]).collect();
            let mut begun=false;
            for i in (llo..n-1).rev() {
                let lo=i+1;
                let nm=(par.m-1).min(n-lo);
                let nt=par.tail.min(n-lo-nm);
                let source_width=nm.min(self.source_bound-1);
                let tail_width=nm+nt-source_width;
                let variable=i<lhi;
                if variable {
                    if !begun {b.x(self.e);begun=true;}
                    // The previous complete row returned g/h/c0. Borrow
                    // them only for this predicate; e remains the held mask.
                    self.max_eq(b,Some((self.t,false)),lo,self.e,&[self.g,self.h,self.c0]);
                    b.and_c(v[i],self.e,self.g);
                }
                let enable=if variable {self.g}else{v[i]};
                if source_width<=124 {
                    let used=tail_width.saturating_sub(1).min(anc.len());
                    let mut carry=anc[used..].to_vec();
                    if !variable {carry.extend([self.e,self.g]);}
                    if tail_width==0 {carry.push(self.h);}
                    carry.truncate(source_width);
                    let bank:Vec<_>=anc[..used].iter().chain(&carry).copied().collect();
                    if !super::super::row_add::choose(b,enable,&v[lo..lo+source_width],&low_q[1..1+source_width],
                        &v[lo+source_width..lo+nm+nt],self.c0,self.h,&bank,&self.dirty,used,carry.len()) {
                        super::cadd_tail_and_mixed(b,enable,&v[lo..lo+source_width],&low_q[1..1+source_width],
                            &v[lo+source_width..lo+nm+nt],self.c0,self.h,&anc[..used],&self.dirty,&carry);
                    }
                }else{
                    // A = Q[1..125] + 2^124 * W7 * W[0..width-124].
                    // Add the common low word once, carrying through the
                    // COMPLETE original target. The remaining translation
                    // starts at bit124 and has at most three source bits.
                    // Both adders return c0/h/source before the next row;
                    // enable=v[i] or its held mask is outside every target.
                    let low_target=&v[lo..lo+124];
                    let low_source=&low_q[1..125];
                    let low_tail=&v[lo+124..lo+nm+nt];
                    if !super::super::row_add::choose(b,enable,low_target,low_source,
                        low_tail,self.c0,self.h,&[],&self.dirty,0,0) {
                        super::cadd_tail_and_mixed(b,enable,low_target,low_source,
                            low_tail,self.c0,self.h,&[],&self.dirty,&[]);
                    }
                    b.and_c(enable,self.w[7],self.h);
                    super::joint_tail::cadd_tail_no_h(b,self.h,
                        &v[lo+124..lo+source_width],&self.w[..source_width-124],
                        &v[lo+source_width..lo+nm+nt],self.c0,&[],&self.dirty,&[]);
                    b.and_u(enable,self.w[7],self.h);
                }
                if variable {b.and_u(v[i],self.e,self.g);}
            }
            if begun {self.max_eq(b,Some((self.t,false)),llo,self.e,&[self.g,self.h,self.c0]);}
            b.play(&rot,true);
        });
        super::pair_control::capture_frame(&r,inverse);
        b.play(&r,inverse);
    }
}

/// Joint map constructor for the raw bridge descriptor. The bridge must
/// rebind both Q's logical high lanes and any counter references to W0..2;
/// physical Q125..127 instead occur as raw SY5..7. Endpoint B0 uses its
/// separate short-Q donor bank and is intentionally not admitted here.
pub(crate) fn late_plain(cp:&super::super::frogdrop_col::ColPar)->bool {
    // The public counter-epoch switch is identical to set_counter_epoch.
    // Three suffix owners below it are zero on BOTH active and DONE shots.
    let ctop=if cp.col>=159 {120}else{121};
    cp.dn && cp.ht && !cp.hr && !cp.sw && !cp.dl && !cp.dq
        && !cp.nomap && cp.sz!=(0,0) && cp.n==257 && cp.nq==128
        && cp.m<=ctop-3
}

pub(crate) fn stage_record(b:&mut B,fd:&super::super::frogdrop_col::Fd,
    cp:&super::super::frogdrop_col::ColPar,sc:&super::super::frogdrop_col::ColScr)
    ->(Vec<G>,Option<(QubitId,QubitId)>) {
    assert_ne!(cp.sz,(0,0));
    assert_eq!(fd.sy.len(),8,"joint map requires the explicit raw-size bridge");
    assert_eq!(fd.sx.len(),7);assert_eq!(fd.q.len(),128);
    assert_eq!(&fd.q[125..],&fd.sx[..3],"joint map Q high bridge missing");
    let sw=sc.sz[0];
    let plain=late_plain(cp);
    let controlled=cp.dn && !plain;
    let qend=if plain {
        let ctop=super::super::frogdrop_col::q_data_end(fd);
        assert_eq!(ctop,if cp.col>=159 {120}else{121});
        assert!(cp.m<=ctop-3);ctop-3
    }else{125};
    let parked=if plain {fd.q[qend..qend+3].to_vec()}else{vec![]};
    let outside=[sw,fd.ph];
    let mut donors=Vec::new();
    for &q in &sc.dirty {if !outside.contains(&q)&&!parked.contains(&q)&&!donors.contains(&q){donors.push(q);}}
    assert!(donors.len()>=18);
    // The last two arbitrary ports belong only to the outer NAND replay.
    // Excluding them for plain/clean maps too makes all recipes uniform.
    donors.truncate(donors.len()-2);
    let mut w=fd.sx.clone();w.push(sc.sz[2]);
    let core=Core{w,ez:fd.sy[..5].to_vec(),t:fd.sy[5],c0:fd.sy[6],e:fd.sy[7],
        g:sc.sz[1],h:sc.sz[3],source_bound:cp.m,raw_cut:plain,
        row_helpers:if plain {vec![sw,fd.ph]}else{vec![]},dirty:donors};
    let par=super::MapPar{clo:cp.n-cp.smax.1,chi:cp.n-cp.smax.0,
        m:if cp.dn {128}else{cp.m},tail:cp.tail,emax:cp.emax};
    let old_booth=b.allow_booth;let old_rows=b.no_rows;
    let old_simple=b.cancel_simple_pairs;
    let old_commuting=b.cancel_commuting_pairs;
    // The explicit shared-Q frame preserves every classic row and carry.
    // Signed/Booth recipe adaptation is a separate, unimplemented funding
    // option; do not silently retain a recipe with different source ports.
    b.allow_booth=false;
    // Plain late rows have globally clean helpers on active AND DONE
    // inputs, so the inherited exact deferred row lowering is available.
    if plain {b.no_rows=false;}
    if controlled {
        b.no_rows=false;
        super::super::row_add::classic_map_begin(outside);
        super::pair_control::begin(outside);
        // Preserve semantic frame boundaries until paired-control lowering.
        // Otherwise enclosing-record cancellation can remove the frame's
        // opening materialize_record against the preceding Q unmaterialize
        // across X(t), making the exact full-frame lookup fail. The same
        // ordinary cancellation policy is restored before any replay.
        b.cancel_simple_pairs=false;
        b.cancel_commuting_pairs=false;
    }
    let r=record(b,|b|{
        if plain {
            // The raw bridge puts logical counter bits125..127 on W0..2.
            // The three public-zero Q suffix cells are never operands,
            // helpers or dirty donors during the following complete map.
            for i in 0..3 {b.swap(core.w[i],parked[i]);}
            // Late active and DONE shots are HT. SW was zero globally.
            b.x(fd.ph);
        }
        let entry=core.entry_record(b,&fd.ring,&fd.q[..qend],cp.m,cp.smax.0,cp.smax.1);
        b.play(&entry,false);
        map_tz(b,&fd.ring,&fd.q[..qend],&par,&core);
        b.play(&entry,true);
        if plain {
            b.x(fd.ph);
            for i in 0..3 {b.swap(core.w[i],parked[i]);}
        }
    });
    b.cancel_simple_pairs=old_simple;
    b.cancel_commuting_pairs=old_commuting;
    if controlled {
        let rows=super::super::row_add::classic_map_end();
        for &gate in &r {
            let touched=match gate {
                G::X(a)=>outside.contains(&a),
                G::Cx(a,t)|G::Swap(a,t)=>outside.contains(&a)||outside.contains(&t),
                G::Ccx(a,c,t)|G::AndC(a,c,t)|G::AndU(a,c,t)=>
                    [a,c,t].iter().any(|q|outside.contains(q)),
                G::RowAdd(id,_)=>{assert!(rows.contains_key(&id));false},
                _=>panic!("joint map unsupported replay primitive: {:?}",gate),
            };
            assert!(!touched,"joint map touched outer SW/PH");
        }
        super::pair_control::finish(rows);
    }
    b.allow_booth=old_booth;b.no_rows=old_rows;
    super::super::frogdrop_col::MAP_PH_OUT.with(|x|x.set(false));
    super::super::frogdrop_col::MAP_SWPH.with(|x|x.set(false));
    (r,controlled.then_some((sw,fd.ph)))
}

/// Replay one freshly captured joint map. This function includes the held
/// done predicate but no raw/encoded bridge and no old SX/SY bank move.
/// Every controlled cp.dn column is in the actual skipped-map set; late
/// plain columns instead retain the parent's alternating DONE map. On switch shots
/// SW implies !PH; on done shots SW=0 and PH=1, so PH&(SW xor D)=D.
pub(crate) fn play_stage(b:&mut B,fd:&super::super::frogdrop_col::Fd,
    cp:&super::super::frogdrop_col::ColPar,sc:&super::super::frogdrop_col::ColScr,r:&[G]) {
    if !cp.dn || late_plain(cp) {b.play(r,false);return;}
    let sw=sc.sz[0];
    let mut bank=Vec::new();
    for &q in &sc.dirty {if ![sw,fd.ph].contains(&q)&&!bank.contains(&q){bank.push(q);}}
    let n=bank.len();assert!(n>=2);
    let (w1,w2)=(bank[n-2],bank[n-1]);
    super::super::frogdrop_col::map_done_flag(b,fd,cp,sw,&bank);
    let clean_ph=!cp.hr&&!cp.sw&&!cp.dl&&!cp.dq&&cp.ht;
    if clean_ph {
        // Here PH=1 and SW was0 globally; use the returned PH owner as the
        // clean replay helper while !SW selects every active shot.
        b.x(sw);b.x(fd.ph);
        super::pair_control::play_ctrl_full(b,r,sw,fd.ph);
        b.x(fd.ph);b.x(sw);
    }else{
        super::pair_control::play_ctrl_nand2(b,r,fd.ph,sw,w1,w2);
    }
    super::super::frogdrop_col::map_done_flag(b,fd,cp,sw,&bank);
}

/// Full TZ map on a represented 128-bit Q. Entry/exit keep the same base-M
/// partial-max ABI; logical high Q is allowed to change from X to Y.
/// Counter/outer-control transport belongs to the caller, which must ensure
/// that this operand domain holds on every enabled shot. Skipped shots need
/// the complete literal paired-frame replay, not a clean-ancilla shortcut.
pub(crate) fn map_tz(b:&mut B,ring:&[QubitId],low_q:&[QubitId],
                    par:&super::MapPar,sc:&Core) {
    sc.check(ring,low_q);
    let n=ring.len();
    assert_eq!(n,257);
    assert!(par.m<=128 && par.emax<=31);
    let (lo,hi)=(par.clo,par.chi);
    let hi2=(hi+par.emax).min(n-1);
    let widepar=super::MapPar{clo:lo,chi:hi2,m:par.m,tail:par.tail,emax:par.emax};
    let rev:Vec<_>=ring.iter().rev().copied().collect();
    let probe=record(b,|b|{
        super::tz_probe(b,&low_q[..par.emax+1],&sc.ez,par.emax,&[],sc.e,&sc.dirty);
        super::tz_probe_gated(b,&rev[..par.emax+1],&sc.ez,par.emax,&[],sc.e,&sc.dirty,
            &[(low_q[0],false)]);
    });
    b.play(&probe,false);
    b.x(low_q[0]);b.cx(low_q[0],sc.t);b.x(low_q[0]);
    let (yev,xev)=((sc.t,true),(sc.t,false));
    let wy=sc.widen_record(b,yev);
    let wx=sc.widen_record(b,xev);
    sc.ring_rotate(b,ring,yev,true);
    b.play(&wy,false);
    sc.shift(b,ring,lo,hi2,yev,false);
    sc.q_rotate(b,low_q,par.m,xev,true);
    // Both captured frame recipes read t=actual widening. This explicit
    // first-frame renaming preserves the parent's F / F^-1 pair identity.
    b.x(sc.t);sc.frame(b,ring,low_q,&widepar,false);b.x(sc.t);
    sc.q_rotate(b,low_q,par.m,xev,false);
    sc.pminus(b,ring,lo,hi2,par.tail,yev);
    b.play(&wy,true);
    sc.ring_rotate(b,ring,yev,false);
    sc.swap_operands(b,ring,low_q,lo,hi);
    sc.ring_rotate(b,ring,xev,true);
    b.play(&wx,false);
    sc.pminus(b,ring,lo,hi2,par.tail,xev);
    sc.q_rotate(b,low_q,par.m,yev,true);
    sc.frame(b,ring,low_q,&widepar,true);
    sc.q_rotate(b,low_q,par.m,yev,false);
    sc.shift(b,ring,lo,hi2,xev,true);
    b.play(&wx,true);
    sc.ring_rotate(b,ring,xev,false);
    b.x(ring[n-1]);b.cx(ring[n-1],sc.t);b.x(ring[n-1]);
    b.play(&probe,true);
}

fn transpose_codes(b:&mut B,word:&[QubitId],a:usize,z:usize,dirty:&[QubitId]) {
    let mut at=a;
    let mut steps=Vec::new();
    for i in 0..word.len() {
        if (a^z)>>i&1!=0 {
            steps.push((at,i));at^=1usize<<i;
        }
    }
    assert_eq!(at,z);
    let toggle=|b:&mut B,(value,bit):(usize,usize)|{
        let c:Vec<_>=(0..word.len()).filter(|&i|i!=bit)
            .map(|i|(word[i],value>>i&1==0)).collect();
        mc_xor(b,&c,word[bit],&[],dirty);
    };
    for &s in &steps {toggle(b,s);}
    for &s in steps[..steps.len().saturating_sub(1)].iter().rev() {toggle(b,s);}
}

fn priority_lane(b:&mut B,out:&[QubitId],value:usize,source:&[(QubitId,bool)],
                 gate:&[(QubitId,bool)],tmp:QubitId,dirty:&[QubitId]) {
    for pass in 0..2 {
        let v=if pass==0 {0}else{value};
        let mut c:Vec<_>=out.iter().enumerate().map(|(i,&q)|(q,v>>i&1==0)).collect();
        c.extend_from_slice(source);c.extend_from_slice(gate);
        mc_xor(b,&c,tmp,&[],dirty);
        if pass==0 {for (i,&q) in out.iter().enumerate(){if value>>i&1!=0 {b.cx(tmp,q);}}}
    }
}

impl Core {
    fn source_literals(&self,low_q:&[QubitId],lane:usize)->Vec<(QubitId,bool)> {
        if lane<125 {vec![(low_q[lane],false)]}
        else {assert!(lane<128);vec![(self.w[7],false),(self.w[lane-125],false)]}
    }

    fn min_q_probe(&self,b:&mut B,low_q:&[QubitId],out:&[QubitId],m:usize,
                   order_neg:bool) {
        for lane in (0..m).rev() {
            priority_lane(b,out,lane,&self.source_literals(low_q,lane),
                &[(self.g,order_neg)],self.h,&self.dirty);
        }
    }

    fn min_ring_probe(&self,b:&mut B,ring:&[QubitId],out:&[QubitId],
                      mlo:usize,mhi:usize,order_neg:bool) {
        let n=ring.len();
        // Physical Q127 is still the zero top bit of size-minus1. It is
        // outside out (seven bits) and supplies the returned cut predicate.
        self.max_ge(b,None,mhi,self.e,&[]);
        for lane in (mlo.saturating_sub(1)..mhi).rev() {
            if lane+1<mhi {self.max_eq(b,None,lane+1,self.e,&[]);}
            priority_lane(b,out,lane,&[(ring[n-1-lane],false)],
                &[(self.g,order_neg),(self.e,false)],self.h,&self.dirty);
        }
        self.max_ge(b,None,mlo.max(1),self.e,&[]);
        for lane in (0..mlo.saturating_sub(1)).rev() {
            priority_lane(b,out,lane,&[(ring[n-1-lane],false)],
                &[(self.g,order_neg)],self.h,&self.dirty);
        }
    }

    fn toggle_order(&self,b:&mut B,low_q:&[QubitId],mlo:usize,mhi:usize) {
        if self.raw_cut {
            let source=|i:usize|low_q.get(i).copied();
            super::super::payload::read_lane(b,&self.w[..7],mlo.max(1)-1,mhi-1,
                &source,true,&[],self.g,&[],&[],&self.dirty);
            return;
        }
        if mlo<=125 {
            let source=|i:usize|low_q.get(i).copied();
            super::super::payload::read_lane(b,&self.w[..7],mlo.max(1)-1,mhi.min(125)-1,
                &source,true,&[(self.w[7],true)],self.g,&[],&[],&self.dirty);
        }
        for tag in 0..3 {
            let c=[(self.w[7],false),(self.w[3],tag&1==0),(self.w[4],tag&2==0),
                (self.w[tag],true)];
            mc_xor(b,&c,self.g,&[],&self.dirty);
        }
    }

    /// Reversible map boundary pack. Input raw top size occupies ez5 plus
    /// t/c0/e (the former physical SY5..7), and Q125..127 occupy W0..2.
    /// Other W bits, g/h, and W7 are zero. Output is the core W8 format;
    /// all raw-size ports and g/h are zero. This exact same record inverted
    /// after the map restores the NEW Q high bits and the NEW ring-top size.
    /// No old order bit or operand-specific high word survives the core.
    pub(crate) fn entry_record(&self,b:&mut B,ring:&[QubitId],low_q:&[QubitId],
                               m:usize,mlo:usize,mhi:usize)->Vec<G> {
        self.check(ring,low_q);
        assert!(m<=128 && 1<=mlo && mlo<=mhi && mhi<=128);
        let raw_sy:Vec<_>=self.ez.iter().copied().chain([self.t,self.c0,self.e]).collect();
        let sy=&raw_sy[..7];
        if self.raw_cut {
            assert!(mhi<=m && m<=low_q.len());
            return record(b,|b| {
                constant(b,&raw_sy,1,true,&self.dirty);
                // No high-Q escape: every W lane is zero after parking.
                for lane in (0..m).rev() {
                    priority_lane(b,&self.w[..7],lane,&[(low_q[lane],false)],
                        &[],self.h,&self.dirty);
                }
                let up=super::super::arith::up_m(b,&self.w[..7],sy,self.e,true);
                let dn=super::super::arith::down_m(b,&self.w[..7],sy,self.e,
                    super::super::arith::Dm::Restore,true);
                b.play(&up,false);b.cx(sy[6],self.g);b.play(&dn,false);
                for i in 0..7 {b.cswap(self.g,self.w[i],sy[i]);}
                let qprobe=record(b,|b|self.min_q_probe(b,low_q,sy,m,false));
                let rprobe=record(b,|b|self.min_ring_probe(b,ring,sy,mlo,mhi,true));
                b.play(&qprobe,true);b.play(&rprobe,true);
                self.toggle_order(b,low_q,mlo,mhi);
            });
        }
        record(b,|b|{
            constant(b,&raw_sy,1,true,&self.dirty);
            // Initial escape tag is [H!=0]. Native H=0 has the seven W
            // output ports zero, so the inherited priority probe is legal.
            b.x(self.w[7]);
            let zero:Vec<_>=self.w[..3].iter().map(|&q|(q,true)).collect();
            mc_xor(b,&zero,self.w[7],&[],&self.dirty);
            for lane in (0..m.min(125)).rev() {
                priority_lane(b,&self.w[..7],lane,&[(low_q[lane],false)],
                    &[(self.w[7],true)],self.h,&self.dirty);
            }
            let order=record(b,|b|{
                let up=super::super::arith::up_m(b,&self.w[..7],sy,self.e,true);
                let dn=super::super::arith::down_m(b,&self.w[..7],sy,self.e,
                    super::super::arith::Dm::Restore,true);
                b.play(&up,false);b.cx(sy[6],self.g);b.play(&dn,false);
                for i in 0..7 {b.cswap(self.g,self.w[i],sy[i]);}
            });
            let replay=self.dirty[0];
            b.x(self.w[7]);b.play_ctrl_full_dirty(&order,self.w[7],replay);b.x(self.w[7]);
            // On H!=0, X has size126/127/128. Keep H in W0..2 and put
            // the category M-126 into W3/4. Only three comparisons can swap.
            b.ccx(self.w[7],self.w[2],self.w[4]);
            mc_xor(b,&[(self.w[7],false),(self.w[2],true),(self.w[1],false)],
                self.w[3],&[],&self.dirty);
            for case in 0..3 {
                let (yin,yout,old_tag,new_tag,sy_xor)=match case {
                    0=>(126,125,0,1,3),
                    1=>(127,125,0,2,2),
                    2=>(127,126,1,2,1),
                    _=>unreachable!(),
                };
                let predicate=|b:&mut B,y:usize,tag:usize|{
                    let mut c=vec![(self.w[7],false),(self.w[2],true),
                        (self.w[1],case!=2),(self.w[3],tag&1==0),(self.w[4],tag&2==0)];
                    if case!=2 {c.push((self.w[0],false));}
                    c.extend(sy.iter().enumerate().map(|(i,&q)|(q,y>>i&1==0)));
                    mc_xor(b,&c,self.h,&[],&self.dirty);
                };
                predicate(b,yin,old_tag);
                b.cx(self.h,self.g);
                for i in 0..2 {if (old_tag^new_tag)>>i&1!=0 {b.cx(self.h,self.w[3+i]);}}
                for i in 0..7 {if sy_xor>>i&1!=0 {b.cx(self.h,sy[i]);}}
                predicate(b,yout,new_tag);
            }
            // Include H=0 in the three high-M escape groups. These spare
            // codewords cannot occur on another valid branch beforehand.
            for (a,z) in [(125,128),(126,136),(127,144)] {transpose_codes(b,&self.w,a,z,&self.dirty);}
            let qprobe=record(b,|b|self.min_q_probe(b,low_q,sy,m,false));
            let rprobe=record(b,|b|self.min_ring_probe(b,ring,sy,mlo,mhi,true));
            b.play(&qprobe,true);b.play(&rprobe,true);
            self.toggle_order(b,low_q,mlo,mhi);
        })
    }
}
