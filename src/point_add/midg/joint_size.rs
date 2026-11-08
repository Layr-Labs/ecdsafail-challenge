//! Direct readers for the eleven-bit size/phase/high-Q prefix code.
//!
//! Source integration only. The allocation fence remains in the caller.
//! A normalized active view deliberately ignores the top tag bit: after
//! an HT-controlled subtraction of 21 it is the conditional-zero q0 port.
//! Low/medium size readers must run only after a ripple has restored the
//! encoded low word, which also supplies logical Q123..127 as dirty source.

use crate::circuit::QubitId;
use super::super::builder::{B, G};
use super::super::frogdrop_col::{Fd, rec};
use super::super::mask::mc_xor;
use std::collections::BTreeSet;

/// Conditional zero Q112..119, borrowed only after the reverse MAJ sweep
/// has restored those cells. Six lanes hold a persistent decoder of E.low7;
/// two hold literal AND work. C=ak & [1<=Y<=limit] is retained on the old
/// query workspace. Every final toggle contains C. Thus arbitrary off-C
/// cache data undergoes only a completely reversed unitary preparation.
struct LowDecoder<'a> {
    view: &'a View,
    root: QubitId,
    ak: QubitId,
    limit: usize,
    lanes: &'a [QubitId],
    decoder: super::super::mask::Dec<'a>,
    live: bool,
}

impl<'a> LowDecoder<'a> {
    fn new(view:&'a View, bits:&'a [QubitId], lanes:&'a [QubitId],
        root:QubitId, ak:QubitId, limit:usize) -> Self {
        assert_eq!(bits.len(),7);assert_eq!(lanes.len(),8);
        Self {view,root,ak,limit,lanes,
            decoder:super::super::mask::Dec::new(bits,&lanes[..6]),live:false}
    }

    fn toggle(&mut self,b:&mut B,v:usize,source:QubitId,
        top:Option<(QubitId,bool)>,flight:QubitId,dirty:&[QubitId]) {
        assert!((1..=self.limit).contains(&v));
        if !self.live {
            self.view.xor_range(b,1,self.limit,self.root,&[(self.ak,false)],&[],dirty);
            self.live=true;
        }
        let mut ctl=self.decoder.ctrls(b,v-1);
        assert_eq!(ctl.len(),1);
        ctl.push((source,true));
        if let Some(q)=top {ctl.push(q);}
        assert!(ctl.iter().all(|(q,_)|!self.lanes.contains(q)||*q==self.lanes[5]));
        for &(q,neg) in &ctl {if neg {b.x(q);}}
        b.ccx(ctl[0].0,ctl[1].0,self.lanes[6]);
        if ctl.len()==3 {b.ccx(self.lanes[6],ctl[2].0,self.lanes[7]);}
        b.ccx(self.root,self.lanes[if ctl.len()==3 {7}else{6}],flight);
        if ctl.len()==3 {b.ccx(self.lanes[6],ctl[2].0,self.lanes[7]);}
        b.ccx(ctl[0].0,ctl[1].0,self.lanes[6]);
        for &(q,neg) in ctl.iter().rev() {if neg {b.x(q);}}
    }

    fn clear(&mut self,b:&mut B,dirty:&[QubitId]) {
        self.decoder.clear(b);
        if self.live {
            self.view.xor_range(b,1,self.limit,self.root,&[(self.ak,false)],&[],dirty);
            self.live=false;
        }
    }
}

fn cache_geometry(view:&View,t:&[QubitId],s:&[QubitId],roles:&[QubitId],
    cache:&[QubitId]) {
    assert_eq!(cache.len(),8);
    let mut seen=BTreeSet::new();
    for &q in cache {
        assert!(seen.insert(q)&&!view.ports().contains(&q)&&!t.contains(&q)&&!roles.contains(&q));
        if let Some(i)=s.iter().position(|&p|p==q) {assert!(i>=112&&i<=119);}
    }
}

fn dirty_ccx(n:usize)->usize {match n {0|1=>0,2=>1,_=>4*(n-2)}}
fn one_clean_ccx(n:usize)->usize {
    if n<=2 {return dirty_ccx(n);}if n==3 {return 2;}
    let(mut rest,mut available,mut stack,mut cost)=(n-2,2usize,1usize,1usize);
    while rest>=2 {
        let take=(available+1).min(rest);
        cost+=2*(take-1);available+=take-1;rest-=take;stack+=1;
    }
    cost+dirty_ccx(stack+rest)
}

/// Complete public primitive cost, including retained-C preparation,
/// decoder initialization, every address update, and final cleanup.
/// No candidate/old gate tapes are built for this choice.
fn prefer_low_decoder(view:&View,range:(usize,usize),limit:usize,top:bool)->bool {
    let end=range.1.min(limit);if range.0>end {return false;}
    let old:usize=(range.0..=end).map(|v|view.size_terms(v,v).iter()
        .map(|t|one_clean_ccx(t.len()+if top {3}else{2})).sum::<usize>())
        .sum::<usize>()*if top {2}else{1};
    let mut new=2*view.size_terms(1,limit).iter()
        .map(|t|dirty_ccx(t.len()+1)).sum::<usize>();
    let mut previous=None;
    // In V-bit queries the higher-address/top=1 XOR is emitted first.
    // Successive duplicate addresses reuse the same complete decoder.
    for i in (0..=range.1).rev() {
        for v in if top {vec![i+1,i]}else{vec![i]} {
            if v<range.0||v>end {continue;}
            let address=v-1;
            let keep=previous.map_or(0,|old:usize|(0..6)
                .take_while(|&level|((old^address)>>(5-level))==0).count());
            new+=if previous.is_some(){2*(6-keep)}else{6};
            new+=if top {5}else{3};previous=Some(address);
        }
    }
    if previous.is_some(){new+=6;}
    new<old
}

pub(crate) fn enabled() -> bool {
    std::env::var("C660_JOINT_SIZE").as_deref() == Ok("1")
}

#[derive(Clone, Debug)]
pub(crate) struct View {
    pub low: [QubitId; 5],
    pub high: [QubitId; 6],
    /// True only while the complete selected act is retained. The caller
    /// has normalized HT phase and must not read the original class then.
    pub normalized: bool,
}

impl View {
    pub(crate) fn from_fd(fd: &Fd, normalized: bool) -> Self {
        assert_eq!(fd.sy.len(), 5);
        assert_eq!(fd.q.len(), 128);
        let low = fd.sy.as_slice().try_into().unwrap();
        let high = [fd.q[123], fd.q[124], fd.q[125], fd.q[126], fd.q[127], fd.ph];
        Self::new(low, high, normalized)
    }

    pub(crate) fn new(low: [QubitId; 5], high: [QubitId; 6], normalized: bool) -> Self {
        let ports: Vec<_> = low.iter().chain(&high).copied().collect();
        assert_eq!(ports.iter().collect::<BTreeSet<_>>().len(), ports.len());
        Self { low, high, normalized }
    }

    pub(crate) fn ports(&self) -> Vec<QubitId> {
        self.low.iter().chain(&self.high).copied().collect()
    }

    pub(crate) fn word(&self) -> Vec<QubitId> {
        self.low.iter().chain(&self.high[..if self.normalized { 5 } else { 6 }])
            .copied().collect()
    }

    /// (base, number of freely varying low high-Q bits) in active rank.
    pub(crate) fn active_interval(size: usize) -> (usize, usize) {
        assert!((1..=128).contains(&size));
        match size {
            1..=108 => (size - 1, 0),
            109 => (108, 1),
            110 => (112, 2),
            111 => (120, 3),
            112 => (128, 4),
            _ => (160 + 32 * (size - 113), 5),
        }
    }

    /// Ordered code intervals for a contiguous size range. Holes between
    /// valid active prefixes are permitted: they encode no reachable state.
    /// Raw class includes both phases and all binary done-counter values.
    pub(crate) fn size_intervals(&self, lo: usize, hi: usize) -> Vec<(usize, usize)> {
        let lo = lo.max(1);
        let hi = hi.min(128);
        if lo > hi { return vec![]; }
        let (start, _) = Self::active_interval(lo);
        let (last, free) = Self::active_interval(hi);
        let end = last + (1 << free);
        if self.normalized { return vec![(start, end)]; }
        let mut out = vec![(start, end), (start + 672, end + 672)];
        let done_hi = hi.min(26);
        if lo <= done_hi {
            out.push((1536 + 16 * (lo - 1), 1536 + 16 * done_hi));
        }
        out
    }

    /// Exact dyadic interval cover. An individual cube has no source or
    /// target mutation except the supplied XOR target and restored dirt.
    pub(crate) fn interval_terms(bits: &[QubitId], mut lo: usize, hi: usize)
        -> Vec<Vec<(QubitId, bool)>> {
        assert!(lo <= hi && hi <= (1usize << bits.len()));
        let mut out = vec![];
        while lo < hi {
            let alignment = if lo == 0 { bits.len() } else { lo.trailing_zeros() as usize };
            let remaining = usize::BITS as usize - 1 - (hi - lo).leading_zeros() as usize;
            let free = alignment.min(remaining).min(bits.len());
            out.push((free..bits.len()).map(|i| (bits[i], (lo >> i) & 1 == 0)).collect());
            lo += 1usize << free;
        }
        out
    }

    pub(crate) fn size_terms(&self, lo: usize, hi: usize) -> Vec<Vec<(QubitId, bool)>> {
        let bits = self.word();
        self.size_intervals(lo, hi).into_iter()
            .flat_map(|(a, z)| Self::interval_terms(&bits, a, z)).collect()
    }

    fn donors(&self, target: QubitId, extra: &[(QubitId, bool)], clean: &[QubitId],
              dirty: &[QubitId]) -> Vec<QubitId> {
        let mut ports: BTreeSet<_> = self.ports().into_iter().collect();
        // A logical high-Q data target can be a freely varying low rank
        // bit. Individual terms below must omit that bit. In normalized
        // mode H5 is likewise an ignored q0 passenger, not size metadata.
        ports.insert(target);
        for &(q, _) in extra { assert!(!clean.contains(&q)); ports.insert(q); }
        for &q in clean { assert!(ports.insert(q), "joint size query aliases a clean owner"); }
        let mut seen = BTreeSet::new();
        dirty.iter().copied().filter(|q| !ports.contains(q) && seen.insert(*q)).collect()
    }

    pub(crate) fn xor_range(&self, b: &mut B, lo: usize, hi: usize, target: QubitId,
                          extra: &[(QubitId, bool)], clean: &[QubitId], dirty: &[QubitId]) {
        let dirty = self.donors(target, extra, clean, dirty);
        for mut term in self.size_terms(lo, hi) {
            // Callers may retain an enable implying one of these literals.
            // Duplicate equal literals are harmless algebraically, but never
            // pass duplicate physical controls to the MCX implementation.
            let mut contradictory = false;
            for &(q, neg) in extra {
                match term.iter().find(|(p, _)| *p == q) {
                    Some((_, old)) if *old != neg => { contradictory = true; break; }
                    Some(_) => {}
                    None => term.push((q, neg)),
                }
            }
            if !contradictory {
                assert!(!term.iter().any(|(q,_)| *q==target),
                    "joint size target is not free in this prefix");
                mc_xor(b, &term, target, clean, &dirty);
            }
        }
    }

    pub(crate) fn xor_eq(&self, b: &mut B, size: usize, target: QubitId,
                       extra: &[(QubitId, bool)], clean: &[QubitId], dirty: &[QubitId]) {
        self.xor_range(b, size, size, target, extra, clean, dirty);
    }

    pub(crate) fn xor_le(&self, b: &mut B, limit: usize, target: QubitId,
                       extra: &[(QubitId, bool)], clean: &[QubitId], dirty: &[QubitId]) {
        self.xor_range(b, 1, limit.min(128), target, extra, clean, dirty);
    }

    pub(crate) fn xor_bit(&self, b: &mut B, bit: usize, target: QubitId,
                        extra: &[(QubitId, bool)], clean: &[QubitId], dirty: &[QubitId]) {
        assert!(bit < 8);
        let width = 1usize << bit;
        for start in (width..=128).step_by(2 * width) {
            self.xor_range(b, start, (start + width - 1).min(128), target, extra, clean, dirty);
        }
    }

    fn xor_tag_ge(&self, b: &mut B, limit: usize, target: QubitId,
                  extra: &[(QubitId, bool)], dirty: &[QubitId]) {
        assert!(!self.normalized, "original class read while PH/q0 is borrowed");
        let dirty = self.donors(target, extra, &[], dirty);
        for mut term in Self::interval_terms(&self.high, limit, 64) {
            assert!(extra.iter().all(|(q, _)| !self.high.contains(q)));
            term.extend_from_slice(extra);
            mc_xor(b, &term, target, &[], &dirty);
        }
    }

    pub(crate) fn xor_phase(&self, b: &mut B, target: QubitId,
                          extra: &[(QubitId, bool)], dirty: &[QubitId]) {
        self.xor_tag_ge(b, 21, target, extra, dirty);
    }

    pub(crate) fn xor_done(&self, b: &mut B, target: QubitId,
                         extra: &[(QubitId, bool)], dirty: &[QubitId]) {
        self.xor_tag_ge(b, 48, target, extra, dirty);
    }

    /// Complete HT activity from the unnormalized global class. Done
    /// packets occupy H>=48 and are excluded without touching counter bits.
    /// At DQ, Z>=SY is code>=2*SY-226; both metadata operands remain held.
    pub(crate) fn xor_ht_active(&self,b:&mut B,code:&[QubitId],dq:bool,
        target:QubitId,dirty:&[QubitId]) {
        assert!(!self.normalized && code.len()==5);
        assert!(code.iter().all(|q|!self.ports().contains(q)));
        let mut bank=self.donors(target,&[],&[],dirty);
        bank.retain(|q|!code.contains(q));
        if !dq {
            for term in Self::interval_terms(&self.high,21,48) {
                mc_xor(b,&term,target,&[],&bank);
            }
            return;
        }
        let word=self.word();
        for size in 1..=128usize {
            let (base,free)=Self::active_interval(size);
            let threshold=(2*size).saturating_sub(226);
            if threshold>=32 {continue;}
            for size_term in Self::interval_terms(&word,672+base,672+base+(1<<free)) {
                for gap_term in Self::interval_terms(code,threshold,32) {
                    let mut term=size_term.clone();term.extend_from_slice(&gap_term);
                    mc_xor(b,&term,target,&[],&bank);
                }
            }
        }
    }

    /// Capture +21 under retained HT activity. Replay inverse at entry,
    /// forward at exit. H5 is returned before the exit replay; act must
    /// not be recomputed from the temporarily normalized metadata.
    pub(crate) fn ht_phase_record(&self, b: &mut B, act: QubitId,
                                dirty: &[QubitId]) -> Vec<G> {
        assert!(!self.normalized && !self.ports().contains(&act));
        let dirty = self.donors(act, &[], &[], dirty);
        rec(b, |b| super::super::modp_frogdrop::add_const_exact(
            b, &self.high, Some(act), 21, &dirty))
    }

    /// Source view for a masked ripple. Only the inverse sweep may query
    /// low/medium size, after every alias at source indices123..127 returns.
    pub(crate) fn masked_source(&self, low_q: &[QubitId], x128: QubitId,
                               len: usize) -> Vec<QubitId> {
        assert!(self.normalized && low_q.len() >= 123 && len <= 129);
        assert!(!self.ports().contains(&x128));
        let mut source: Vec<_> = low_q[..123].iter().chain(&self.low).copied().collect();
        source.push(x128);
        source.truncate(len);
        assert_eq!(source.iter().collect::<BTreeSet<_>>().len(), source.len());
        source
    }

    /// Apply an exact selected swap without ever reading a moved prefix
    /// bit. The two data ports must be absent from every size cube. This
    /// permits high-Q free suffix bits and the normalized H5 q0 passenger.
    pub(crate) fn swap_at(&self, b:&mut B, size:usize, a:QubitId, z:QubitId,
        extra:&[(QubitId,bool)], dirty:&[QubitId]) {
        assert!(a!=z && extra.iter().all(|(q,_)| *q!=a && *q!=z));
        let mut excluded:BTreeSet<_>=self.ports().into_iter().collect();
        excluded.extend([a,z]);
        excluded.extend(extra.iter().map(|(q,_)|*q));
        let mut seen=BTreeSet::new();
        let bank:Vec<_>=dirty.iter().copied()
            .filter(|q|!excluded.contains(q)&&seen.insert(*q)).collect();
        for mut term in self.size_terms(size,size) {
            assert!(!term.iter().any(|(q,_)|*q==a||*q==z),
                "selected swap moves a joint size-prefix bit");
            let mut contradictory=false;
            for &(q,neg) in extra {
                match term.iter().find(|(p,_)|*p==q) {
                    Some((_,old)) if *old!=neg=>{contradictory=true;break;},
                    Some(_)=>{},None=>term.push((q,neg)),
                }
            }
            if !contradictory {super::super::mid2::mc_swap(b,&term,a,z,&[],&bank);}
        }
    }

    /// Gather in the two affine address regions, with four singleton
    /// medium prefixes. A complete membership flag protects sparse public
    /// ranges; absent addresses never inherit an arbitrary tree root.
    /// Low gathers touch no L port. High gathers may change L because
    /// their address and membership depend only on H. Every gather and
    /// membership flag is restored before the next region.
    pub(crate) fn gathered_at(&self,b:&mut B,leaves:&[(usize,QubitId)],
        flag:QubitId,dirty:&[QubitId],mut body:impl FnMut(&mut B,QubitId,QubitId,&[QubitId])) {
        assert!(self.normalized && !self.ports().contains(&flag));
        assert!(leaves.windows(2).all(|p|p[0].0<p[1].0));
        let mut excluded:BTreeSet<_>=self.ports().into_iter().collect();
        excluded.insert(flag);excluded.extend(leaves.iter().map(|(_,q)|*q));
        let mut seen=BTreeSet::new();
        let bank:Vec<_>=dirty.iter().copied()
            .filter(|q|!excluded.contains(q)&&seen.insert(*q)).collect();
        for (lo,hi) in [(1,108),(109,109),(110,110),(111,111),(112,112),(113,128)] {
            let part:Vec<_>=leaves.iter().copied().filter(|(size,_)|(lo..=hi).contains(size)).collect();
            if part.is_empty(){continue;}
            assert!(part.windows(2).all(|p|p[0].0+1==p[1].0));
            let (first,last)=(part[0].0,part[part.len()-1].0);
            let mut swaps=vec![];
            let root=if lo==1 {
                let address:Vec<_>=self.low.iter().chain(&self.high[..2]).copied().collect();
                assert!(part.iter().all(|(_,q)|!address.contains(q)));
                let indexed:Vec<_>=part.iter().map(|(size,q)|(size-1,*q)).collect();
                super::swap_tree(&address,&indexed,address.len(),&mut swaps)
            } else if lo==113 {
                let address=&self.high[..5];
                assert!(part.iter().all(|(_,q)|!address.contains(q)));
                let indexed:Vec<_>=part.iter().map(|(size,q)|(size-108,*q)).collect();
                super::swap_tree(address,&indexed,address.len(),&mut swaps)
            } else {part[0].1};
            // Size terms cannot observe any of the data moved by this
            // group's tree or by body, including the free medium suffix.
            for term in self.size_terms(first,last) {
                assert!(term.iter().all(|(q,_)|!part.iter().any(|(_,p)|p==q)));
            }
            self.xor_range(b,first,last,flag,&[],&[],&bank);
            for &(q,a,z) in &swaps {b.cswap(q,a,z);}
            body(b,root,flag,&bank);
            for &(q,a,z) in swaps.iter().rev() {b.cswap(q,a,z);}
            self.xor_range(b,first,last,flag,&[],&[],&bank);
        }
    }
}

fn ripple_donors(view: &View, t: &[QubitId], s: &[QubitId], roles: &[QubitId],
                 dirty: &[QubitId]) -> Vec<QubitId> {
    assert!(view.normalized && t.len() == s.len());
    let mut operands = BTreeSet::new();
    for &q in t.iter().chain(s) {
        assert!(operands.insert(q), "joint ripple aliases two operand ports");
    }
    // L is deliberately part of the source, but H is immutable metadata.
    assert!(view.high.iter().all(|q| !operands.contains(q)));
    for &q in roles { assert!(operands.insert(q), "joint ripple aliases a role"); }
    operands.extend(view.ports());
    let mut seen = BTreeSet::new();
    let out: Vec<_> = dirty.iter().copied()
        .filter(|q| !operands.contains(q) && seen.insert(*q)).collect();
    assert!(out.len() >= 12, "joint ripple lacks restored arbitrary donors");
    out
}

fn maj_all(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId) {
    for i in 0..t.len() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
    }
}

/// Exact existing masked comparator with an encoded, restore-ordered size
/// query. Q[SY] must have been moved to the existing q0 slot, as before.
/// Source cells above SY may be arbitrary: including L's size prefixes.
#[allow(clippy::too_many_arguments)]
pub(crate) fn masked_cmp(b: &mut B, view: &View, t: &[QubitId], s: &[QubitId],
    range: (usize, usize), ak: QubitId, flight: QubitId, c0: QubitId,
    query_temp: QubitId, cache: &[QubitId], dirty: &[QubitId], complement: bool) {
    assert!(1 <= range.0 && range.0 <= range.1 && range.1 <= 128);
    assert!(range.1 < t.len());
    cache_geometry(view,t,s,&[ak,flight,c0,query_temp],cache);
    let mut dirty = ripple_donors(view, t, s, &[ak, flight, c0, query_temp], dirty);
    dirty.retain(|q|!cache.contains(q));
    // A complete fifteen-bit quotient park ends strictly below Q112 when
    // Y<=97. Higher sizes keep the unchanged reader and clean workspace.
    let cached=prefer_low_decoder(view,range,97,false);
    let bits=view.word();
    let mut decoder=LowDecoder::new(view,&bits[..7],cache,query_temp,ak,97);
    let old_literal=super::super::mask::R11O11_DECCC.with(|c| {
        let old=c.borrow().clone();if cached {c.borrow_mut().extend_from_slice(cache);}old
    });
    if complement { for &q in t { b.x(q); } }
    maj_all(b, t, s, c0);
    for i in (0..t.len()).rev() {
        if (range.0..=range.1).contains(&i) {
            if cached&&i<=97 {
                decoder.toggle(b,i,s[i],None,flight,&dirty);
            } else {
                view.xor_eq(b, i, flight, &[(s[i], true), (ak, false)],
                            &[query_temp], &dirty);
            }
        }
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.ccx(x, t[i], s[i]);
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(flight, x, t[i]);
        b.cx(s[i], x);
    }
    decoder.clear(b,&dirty);
    super::super::mask::R11O11_DECCC.with(|c|*c.borrow_mut()=old_literal);
    if complement { for &q in t { b.x(q); } }
}

/// Exact existing masked add. `flight => ak` and `flight => !top` are
/// the inherited pool4 implied-owner contract; both are restored within
/// each query. The running mask is returned by its terminal CX as before.
#[allow(clippy::too_many_arguments)]
pub(crate) fn masked_add(b: &mut B, view: &View, t: &[QubitId], s: &[QubitId],
    range: (usize, usize), flight: QubitId, ak: QubitId, top: QubitId,
    c0: QubitId, mask: QubitId, dirty: &[QubitId], subtract: bool) {
    assert!(1 <= range.0 && range.0 <= range.1 && range.1 <= 128);
    assert!(range.1 < t.len());
    let dirty = ripple_donors(view, t, s, &[flight, ak, top, c0, mask], dirty);
    if subtract { for &q in t { b.x(q); } }
    maj_all(b, t, s, c0);
    for i in (0..t.len()).rev() {
        if (range.0..=range.1).contains(&i) {
            for term in view.size_terms(i, i) {
                super::super::mask::mc_xor_implied_pair(
                    b, flight, ak, top, &term, mask, &dirty);
            }
        }
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.ccx(x, t[i], s[i]);
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(mask, x, t[i]);
        b.cx(s[i], x);
    }
    b.cx(flight, mask);
    if subtract { for &q in t { b.x(q); } }
}

/// Clean-source reciprocal query, with its carry read delayed until the
/// reverse sweep reaches the logical boundary. Original logical source
/// bits above SY are zero. The selected e=!carry means adding Y has no
/// outgoing carry (or subtracting Y has no outgoing borrow), so original
/// target writes strictly above the queried boundary are identities.
/// Those cells may therefore be restored before e is computed. The L
/// prefix aliases at123..127 have then returned before any low/medium
/// size query. For high sizes the query reads immutable H only.
///
/// `top=Some` selects SY-1 when top=1, exactly the inherited V-bit read;
/// otherwise the boundary is SY. Flight must start zero on the forward
/// arithmetic boundary. Capturing/reversing the whole record implements
/// its inverse without requiring zero at inverse entry.
#[allow(clippy::too_many_arguments)]
pub(crate) fn clean_query(b:&mut B,view:&View,t:&[QubitId],s:&[QubitId],
    range:(usize,usize),ak:QubitId,flight:QubitId,c0:QubitId,
    query_temp:QubitId,top:Option<QubitId>,cache:&[QubitId],dirty:&[QubitId],complement:bool) {
    assert!(range.0>=1 && range.0<=range.1 && range.1<t.len());
    let mut roles=vec![ak,flight,c0,query_temp];
    if let Some(q)=top {roles.push(q);}
    cache_geometry(view,t,s,&roles,cache);
    let mut dirty=ripple_donors(view,t,s,&roles,dirty);
    dirty.retain(|q|!cache.contains(q));
    // These complete reciprocal epochs have no parked quotient: Q=Y.
    // Q112..119 are zero on ak & Y<=108. All source cells at112+ have
    // returned before the first low query, and no later cell uses them.
    let cached=prefer_low_decoder(view,range,108,top.is_some());
    let bits=view.word();
    let mut decoder=LowDecoder::new(view,&bits[..7],cache,query_temp,ak,108);
    let old_literal=super::super::mask::R11O11_DECCC.with(|c| {
        let old=c.borrow().clone();if cached {c.borrow_mut().extend_from_slice(cache);}old
    });
    if complement {for &q in t {b.x(q);}}
    maj_all(b,t,s,c0);
    for i in (0..t.len()).rev() {
        // Both queries XOR the same flight and read unchanged controls.
        // Higher first ends all high-size queries before C takes workspace.
        if let Some(q)=top {
            let v=i+1;
            if (range.0..=range.1).contains(&v) {
                if cached&&v<=108 {
                    decoder.toggle(b,v,s[i],Some((q,false)),flight,&dirty);
                } else {
                    view.xor_eq(b,v,flight,&[(s[i],true),(ak,false),(q,false)],
                        &[query_temp],&dirty);
                }
            }
        }
        if (range.0..=range.1).contains(&i) {
            if cached&&i<=108 {
                decoder.toggle(b,i,s[i],top.map(|q|(q,true)),flight,&dirty);
            } else {
                let mut extra=vec![(s[i],true),(ak,false)];
                if let Some(q)=top {extra.push((q,true));}
                view.xor_eq(b,i,flight,&extra,&[query_temp],&dirty);
            }
        }
        let x=if i==0 {c0}else{s[i-1]};
        b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);
        b.cx(s[i],x);b.ccx(flight,x,t[i]);b.cx(s[i],x);
    }
    decoder.clear(b,&dirty);
    super::super::mask::R11O11_DECCC.with(|c|*c.borrow_mut()=old_literal);
    if complement {for &q in t {b.x(q);}}
}
