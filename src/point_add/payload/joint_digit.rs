//! Payload digit over the joint size/phase/high-Q code.
//!
//! Source integration only. No materialized raw SY high word is borrowed.
//! The sum word is temporarily changed to Z mod32. Together with encoded
//! Y and 226<=Z+Y<=257 this determines Z uniquely, including Z=256.
//! All arithmetic writes use the complete retained phase activity. H5 is
//! ignored by normalized size readers and carries logical P258 until the
//! complete quotient transition, not merely the digit, has finished.

use crate::circuit::QubitId;
use super::{PlCol, KE, NP, splice258, joint_kernel};
use super::super::builder::{B,G};
use super::super::frogdrop_col::{Fd,ColPar,ColScr,rec};
use super::super::midg::joint_size::View;
use super::super::mask::mc_xor;
use std::collections::BTreeSet;

#[derive(Clone,Copy)]
enum Size { Y, Z }

struct Sizes {
    y: View,
    zlow: Vec<QubitId>,
}

fn donors(dirty:&[QubitId], forbidden:&[QubitId])->Vec<QubitId> {
    let used:BTreeSet<_>=forbidden.iter().copied().collect();
    let mut seen=BTreeSet::new();
    dirty.iter().copied().filter(|q|!used.contains(q)&&seen.insert(*q)).collect()
}

fn dirty_price(n:usize)->usize {
    match n {0|1=>0,2=>1,_=>4*(n-2)}
}

/// Literal price of the inherited returned-known-prefix construction.
fn known_price(mut rest:usize,mut available:usize)->usize {
    let mut stack=1;let mut cost=0;
    while rest>=2 {
        let take=(available+1).min(rest);
        cost+=2*(take-1);available+=take-1;rest-=take;stack+=1;
    }
    cost+dirty_price(stack+rest)
}

fn one_clean_price(n:usize)->usize {
    if n<=2 {dirty_price(n)}else if n==3 {2}else{1+known_price(n-2,2)}
}

/// Only literal X/CX/CCX are allowed here: known lanes need be one only
/// when root is one. The retained root remains a final control, and the
/// whole preparation is reversed even when every known lane is dirty.
fn known_query(b:&mut B,root:QubitId,known:&[QubitId],lits:&[(QubitId,bool)],
    target:QubitId,dirty:&[QubitId]) {
    assert!(!known.is_empty());
    let mut used=BTreeSet::new();
    assert!(std::iter::once(root).chain(known.iter().copied())
        .chain(lits.iter().map(|&(q,_)|q)).chain(std::iter::once(target))
        .all(|q|used.insert(q)));
    let forbidden:Vec<_>=used.into_iter().collect();let bank=donors(dirty,&forbidden);
    for &(q,neg) in lits {if neg {b.x(q);}}
    let rest:Vec<_>=lits.iter().map(|&(q,_)|q).collect();
    let mut available=known.to_vec();let mut stack=vec![root];let mut pos=0;
    let prep=rec(b,|b| {
        while rest.len()-pos>=2 {
            let take=(available.len()+1).min(rest.len()-pos);
            let summary=available.pop().unwrap();b.x(summary);
            let work=&available[..take-2];for &q in work {b.x(q);}
            let mut previous=rest[pos];
            for j in 1..take {
                let dst=if j+1==take {summary}else{work[j-1]};
                b.ccx(previous,rest[pos+j],dst);previous=dst;
            }
            stack.push(summary);available.extend_from_slice(&rest[pos..pos+take]);pos+=take;
        }
    });
    b.play(&prep,false);stack.extend_from_slice(&rest[pos..]);
    super::super::mask::mcx_dirty(b,&stack,target,&bank);
    b.play(&prep,true);
    for &(q,neg) in lits.iter().rev() {if neg {b.x(q);}}
}

/// Symmetric difference of two half-open numeric intervals. Unlike a
/// logical size equality, this retains unused codes between size blocks.
fn interval_delta(a:Option<(usize,usize)>,z:Option<(usize,usize)>)->Vec<(usize,usize)> {
    let mut ends=vec![];
    for (lo,hi) in a.into_iter().chain(z) {ends.extend([lo,hi]);}
    ends.sort_unstable();ends.dedup();
    let contains=|range:Option<(usize,usize)>,v:usize|
        range.is_some_and(|(lo,hi)|lo<=v&&v<hi);
    let mut out:Vec<(usize,usize)>=vec![];
    for pair in ends.windows(2) {
        let (lo,hi)=(pair[0],pair[1]);
        if contains(a,lo)^contains(z,lo) {
            if let Some(last)=out.last_mut() {
                if last.1==lo {last.1=hi;continue;}
            }
            out.push((lo,hi));
        }
    }
    out
}

impl Sizes {
    fn ports(&self)->Vec<QubitId> {
        self.y.ports().into_iter().chain(self.zlow.iter().copied()).collect()
    }

    /// Z is the unique integer with the stored residue for which Z+Y is in
    /// [226,257]. For each residue, consecutive candidate Z values differ
    /// by32; their allowed Y intervals are adjacent, so a range needs at
    /// most32 residue clauses, with no new physical flag.
    fn terms(&self,size:Size,lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>> {
        match size {
            Size::Y=>self.y.size_terms(lo,hi),
            Size::Z=>{
                let lo=lo.max(1);let hi=hi.min(256);
                if lo>hi {return vec![];}
                let mut out=vec![];
                for residue in 0..32usize {
                    let first=lo+((residue+32-lo%32)%32);
                    if first>hi {continue;}
                    let last=hi-((hi+32-residue)%32);
                    let ylo=(226isize-last as isize).max(1) as usize;
                    let yhi=(257isize-first as isize).min(128);
                    if yhi<ylo as isize {continue;}
                    for mut term in self.y.size_terms(ylo,yhi as usize) {
                        term.extend(self.zlow.iter().enumerate().map(|(i,&q)|(q,(residue>>i)&1==0)));
                        out.push(term);
                    }
                }
                out
            }
        }
    }

    fn xor_terms(&self,b:&mut B,terms:Vec<Vec<(QubitId,bool)>>,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        let mut forbidden=self.ports();forbidden.push(target);
        forbidden.extend(extra.iter().map(|&(q,_)|q));forbidden.extend_from_slice(clean);
        assert!(!clean.contains(&target));
        assert!(clean.iter().all(|q|!self.ports().contains(q)&&!extra.iter().any(|(p,_)|p==q)));
        let bank=donors(dirty,&forbidden);
        for mut term in terms {
            let mut contradiction=false;
            for &(q,neg) in extra {
                if let Some(&(_,old))=term.iter().find(|(p,_)|*p==q) {
                    if old!=neg {contradiction=true;break;}
                } else {term.push((q,neg));}
            }
            if contradiction {continue;}
            assert!(!term.iter().any(|&(q,_)|q==target));
            mc_xor(b,&term,target,clean,&bank);
        }
    }

    fn xor_range(&self,b:&mut B,size:Size,lo:usize,hi:usize,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        self.xor_terms(b,self.terms(size,lo,hi),target,extra,clean,dirty);
    }

    /// XOR the exact change of two existing range predicates. For Z, a
    /// one-step bound change affects only its one residue modulo32. The
    /// numeric Y interval difference includes encoding holes, so a held
    /// mask returns even for arbitrary inactive/off-DONE metadata.
    fn xor_range_delta(&self,b:&mut B,size:Size,old:(usize,usize),new:(usize,usize),
        target:QubitId,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        assert!(self.y.normalized);
        if old==new {return;}
        let span=|range:(usize,usize)| {
            let spans=self.y.size_intervals(range.0,range.1);
            assert!(spans.len()<=1);spans.first().copied()
        };
        let word=self.y.word();let mut terms=vec![];
        match size {
            Size::Y=>for (lo,hi) in interval_delta(span(old),span(new)) {
                terms.extend(View::interval_terms(&word,lo,hi));
            },
            Size::Z=>for residue in 0..32usize {
                let zspan=|range:(usize,usize)| {
                    let lo=range.0.max(1);let hi=range.1.min(256);
                    if lo>hi {return None;}
                    let first=lo+((residue+32-lo%32)%32);
                    if first>hi {return None;}
                    let last=hi-((hi+32-residue)%32);
                    let ylo=(226isize-last as isize).max(1) as usize;
                    let yhi=(257isize-first as isize).min(128);
                    if yhi<ylo as isize {None}else{span((ylo,yhi as usize))}
                };
                for (lo,hi) in interval_delta(zspan(old),zspan(new)) {
                    for mut term in View::interval_terms(&word,lo,hi) {
                        term.extend(self.zlow.iter().enumerate()
                            .map(|(i,&q)|(q,(residue>>i)&1==0)));
                        terms.push(term);
                    }
                }
            },
        }
        self.xor_terms(b,terms,target,extra,clean,dirty);
    }

    fn xor_eq(&self,b:&mut B,size:Size,v:usize,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        self.xor_range(b,size,v,v,target,extra,clean,dirty);
    }

    /// Temporary SizeZ arithmetic view. On active shots E<108 is moved
    /// into the vacant tag interval by E'=E+zlow+799. Since E=Y-1,
    /// E'=(S-226)+32*(32-floor(Z/32)): Z's high part is now direct.
    /// Medium/high Y keeps its existing representation. Off act, every
    /// gate is identity with flag returned, even for arbitrary metadata.
    /// Only ring-source kernels may use this view: no encoded word port
    /// may be changed by the intervening MAJ pass or a target write.
    fn z_epoch_record(&self,b:&mut B,act:QubitId,flag:QubitId,
        dirty:&[QubitId])->Vec<G> {
        assert!(self.y.normalized&&act!=flag);
        let word=self.y.word();
        let mut excluded=self.ports();excluded.extend([act,flag]);
        assert!(!self.ports().contains(&act)&&!self.ports().contains(&flag));
        let bank=donors(dirty,&excluded);assert!(bank.len()>=11);
        let pad=&bank[..5];
        let source:Vec<_>=self.zlow.iter().chain(pad).copied().collect();
        rec(b,|b| {
            for mut term in View::interval_terms(&word,0,108) {
                term.push((act,false));mc_xor(b,&term,flag,&[],&bank);
            }
            // Zero-extension without clean pads: add zlow+32*pad, then
            // subtract pad from the high half. Both source words return.
            super::super::arith::ttk_add(b,&source,&word,Some(flag),None);
            let remove_pad=rec(b,|b|super::super::arith::ttk_add(
                b,pad,&word[5..],Some(flag),None));
            b.play(&remove_pad,true);
            super::super::modp_frogdrop::add_const_exact(b,&word,Some(flag),799,&bank);
            // Active untouched packets have H<=20; translated packets
            // have H24..29. act=0 returns flag without any code assumption.
            mc_xor(b,&[(act,false),(self.y.high[3],false),(self.y.high[4],false)],
                flag,&[],&bank);
        })
    }

    /// Disjoint equality predicates in the temporary view. The low-Y
    /// branch only reaches Z>=118. The two code classes are disjoint on
    /// ALL words (new H>=24 versus untouched H<=20), and distinct values
    /// are disjoint by their residue/high tag or adjacent Y intervals.
    /// Arbitrary off-act completions need not equal the old decoder:
    /// every arithmetic write/decision there is disabled and A^-1 returns
    /// the original packet. No old-view range or guard may read this view.
    fn z_epoch_terms(&self,v:usize)->Vec<Vec<(QubitId,bool)>> {
        if !(1..=256).contains(&v) {return vec![];}
        let residue:Vec<_>=self.zlow.iter().enumerate()
            .map(|(i,&q)|(q,((v%32)>>i)&1==0)).collect();
        let mut out=vec![];
        if v>=118 {
            let tag=32-v/32;
            let mut term:Vec<_>=self.y.high[..5].iter().enumerate()
                .map(|(i,&q)|(q,(tag>>i)&1==0)).collect();
            term.extend_from_slice(&residue);out.push(term);
        }
        let lo=(226isize-v as isize).max(109) as usize;
        let hi=(257isize-v as isize).min(128);
        if hi>=lo as isize {
            for mut term in self.y.size_terms(lo,hi as usize) {
                term.extend_from_slice(&residue);out.push(term);
            }
        }
        out
    }

    /// Static literal admission for a complete kernel, including both
    /// 186T metadata translations. Compare to the currently selected
    /// class decoder for ADD/CMP, or held-membership DIV. No gate tapes
    /// are generated for pricing and no arithmetic spans are shortened.
    fn prefer_z_epoch(&self,lo:usize,hi:usize,extras:&[usize],divide:bool)->bool {
        let mut old=0;let mut old_class=8;let mut new=372;
        for v in lo..=hi {
            let original=self.terms(Size::Z,v,v);let shifted=self.z_epoch_terms(v);
            if divide {
                old+=2*original.iter().map(|t|dirty_price(t.len())).sum::<usize>()+14;
                new+=2*shifted.iter().map(|t|dirty_price(t.len())).sum::<usize>()+14;
            } else {
                let (low,high)=self.class_terms(Size::Z,v);
                for &extra in extras {
                    old+=original.iter().map(|t|one_clean_price(t.len()+extra)).sum::<usize>();
                    old_class+=low.iter().map(|t|known_price(t.len()+extra,3)).sum::<usize>();
                    old_class+=high.iter().map(|t| {
                        let n=t.len()+extra;dirty_price(n).min(known_price(n-1,1))
                    }).sum::<usize>();
                    new+=shifted.iter().map(|t|one_clean_price(t.len()+extra)).sum::<usize>();
                }
            }
        }
        new<if divide {old}else{old.min(old_class)}
    }

    /// Choose one complete inverse digit pair by literal public price.
    /// The old path is its exact direct/class/translated minimum, including
    /// both separate metadata epochs. The fused path has one restoring
    /// ripple played backwards, two dirty membership queries per boundary,
    /// and a materialized enable containing the unchanged sign. Its extra
    /// guard literal is charged in both directions. No alternate tape is
    /// captured merely for pricing; a rejected pair emits the old path.
    fn inverse_fusion_choice(&self,size:Size,lo:usize,hi:usize,source_len:usize,
        allow_shift:bool,k:usize)->Option<bool> {
        let allow_shift=matches!(size,Size::Z)&&allow_shift;
        let mut old_queries=0;
        for extras in [[2usize,1usize],[2usize,4usize]] {
            let mut direct=0;let mut class=8;let mut shifted=372;
            for v in lo..=hi {
                let original=self.terms(size,v,v);
                let (low,high)=self.class_terms(size,v);
                for extra in extras {
                    direct+=original.iter().map(|t|one_clean_price(t.len()+extra)).sum::<usize>();
                    class+=low.iter().map(|t|known_price(t.len()+extra,3)).sum::<usize>();
                    class+=high.iter().map(|t| {
                        let n=t.len()+extra;dirty_price(n).min(known_price(n-1,1))
                    }).sum::<usize>();
                    if allow_shift {
                        shifted+=self.z_epoch_terms(v).iter()
                            .map(|t|one_clean_price(t.len()+extra)).sum::<usize>();
                    }
                }
            }
            let unshifted=direct.min(class);
            old_queries+=if allow_shift {unshifted.min(shifted)}else{unshifted};
        }
        let mut fused=0;let mut shifted=372;
        for v in lo..=hi {
            fused+=2*self.terms(size,v,v).iter().map(|t|dirty_price(t.len())).sum::<usize>()+14;
            if allow_shift {
                shifted+=2*self.z_epoch_terms(v).iter().map(|t|dirty_price(t.len())).sum::<usize>()+14;
            }
        }
        if matches!(size,Size::Y) {
            fused=fused.min(self.y_decoder_price(lo,hi)+14*(hi-lo+1));
        }
        let use_shift=allow_shift&&shifted<fused;
        let new_queries=if use_shift {shifted}else{fused};
        let end=(33usize.saturating_sub(k)).min(32);
        let guard_delta=2*View::interval_terms(&self.zlow,0,end).iter()
            .map(|t|dirty_price(t.len()+2)-dirty_price(t.len()+1)).sum::<usize>();
        // The common lower-write pass and the original guard cancel from
        // the comparison. ADD+CMP pays4*source_len MAJ/undo CCXs, the
        // inverse restoring ripple pays2*source_len.
        (new_queries+2*source_len+guard_delta<old_queries+4*source_len).then_some(use_shift)
    }

    /// Full literal price of a persistent low-Z decoder, versus the two
    /// dirty membership queries already used by virtual_divide. A high
    /// query is unchanged. The exact ten-bit address walk includes every
    /// high-tag boundary and the final literal clear of all nine prefixes.
    fn prefer_z_decoder(&self,lo:usize,hi:usize)->bool {
        let mut old=0;let mut new=0;let mut current=None;
        for v in (lo..=hi).rev() {
            let terms=self.z_epoch_terms(v);
            old+=2*terms.iter().map(|t|dirty_price(t.len())).sum::<usize>();
            let has_low=(118..=256).contains(&v);
            if has_low {
                let address=((32-v/32)<<5)+(v%32);
                let mut keep=0;
                if let Some(previous)=current {
                    while keep<9&&((previous^address)>>(8-keep))==0 {keep+=1;}
                    new+=9-keep;
                }
                new+=9-keep;current=Some(address);
                new+=2*dirty_price(3);
            }
            new+=2*terms.iter().skip(usize::from(has_low))
                .map(|t|dirty_price(t.len())).sum::<usize>();
        }
        if current.is_some() {new+=9;}
        new<old
    }

    /// Current complete SizeZ restoring-query price, including its chosen
    /// translated low-class decoder and both metadata frames. This mirrors
    /// the existing dispatch without changing that fallback implementation.
    fn current_z_divide_price(&self,lo:usize,hi:usize,shifted:bool)->usize {
        let mut price=14*(hi-lo+1)+if shifted {372}else{0};
        let cached=shifted&&self.prefer_z_decoder(lo,hi);
        let mut current=None;
        for v in (lo..=hi).rev() {
            if !shifted {
                price+=2*self.terms(Size::Z,v,v).iter()
                    .map(|t|dirty_price(t.len())).sum::<usize>();
                continue;
            }
            let terms=self.z_epoch_terms(v);
            if !cached {
                price+=2*terms.iter().map(|t|dirty_price(t.len())).sum::<usize>();
                continue;
            }
            let has_low=(118..=256).contains(&v);
            if has_low {
                let address=((32-v/32)<<5)+(v%32);let mut keep=0;
                if let Some(previous)=current {
                    while keep<9&&((previous^address)>>(8-keep))==0 {keep+=1;}
                    price+=9-keep;
                }
                price+=9-keep;current=Some(address);price+=2*dirty_price(3);
            }
            price+=2*terms.iter().skip(usize::from(has_low))
                .map(|t|dirty_price(t.len())).sum::<usize>();
        }
        if current.is_some() {price+=9;}
        price
    }

    /// Full direct ALLZ price: EMPTY568 + rank524, in both directions.
    /// The optional seven-prefix decoder is used only at requested Z>=160.
    /// Every prefix transition and final clear is charged literally; the
    /// unchanged14 local CCXs per boundary are included on both paths.
    fn all_z_divide_price(lo:usize,hi:usize,cached:bool)->usize {
        let mut price=2184+14*(hi-lo+1);let mut current=None;
        for v in (lo..=hi).rev() {
            if !(98..=256).contains(&v) {continue;}
            if cached&&v>=160 {
                let address=v-96;let mut keep=0;
                if let Some(previous)=current {
                    while keep<7&&((previous^address)>>(6-keep))==0 {keep+=1;}
                    price+=7-keep;
                }
                price+=7-keep;current=Some(address);price+=2;
            } else {price+=2*dirty_price(8);}
        }
        if current.is_some() {price+=7;}
        price
    }

    fn all_z_divide_choice(&self,lo:usize,hi:usize,shifted:bool)->Option<bool> {
        let direct=Self::all_z_divide_price(lo,hi,false);
        let cached=Self::all_z_divide_price(lo,hi,true);
        let use_cache=cached<direct;
        (direct.min(cached)<self.current_z_divide_price(lo,hi,shifted))
            .then_some(use_cache)
    }

    /// Complete normalized E -> EMPTY V8 -> biased raw Z address.
    /// Q=Y and226<=Z+Y<=257 are required only on act. Both literal frames
    /// are exactly identity on act0, with arbitrary dirty metadata/helpers.
    fn all_z_epoch_record(&self,b:&mut B,act:QubitId,flag:QubitId,
        dirty:&[QubitId])->Vec<G> {
        assert!(self.y.normalized);
        let word=self.y.word();
        rec(b,|b| {
            let empty=super::super::empty_packet::record(b,&word,act,dirty);
            b.play(&empty,false);
            let rank=super::super::empty_packet::z_rank_from_empty_record(
                b,&word,&self.zlow,act,flag,dirty);
            b.play(&rank,false);
        })
    }

    /// Low SizeY queries start only after undo_cell has returned every
    /// Q112..117 source lane. Six literal prefixes hold a seven-bit E
    /// equality; the three upper E bits remain explicit negative controls.
    /// Include every address transition and final clear in admission.
    fn y_decoder_price(&self,lo:usize,hi:usize)->usize {
        let mut price=0;let mut current=None;
        for v in (lo..=hi).rev() {
            if v<=108 {
                assert!(v>=1);let address=v-1;let mut keep=0;
                if let Some(previous)=current {
                    while keep<6&&((previous^address)>>(5-keep))==0 {keep+=1;}
                    price+=6-keep;
                }
                price+=6-keep;current=Some(address);
                price+=2*dirty_price(4);
            } else {
                price+=2*self.terms(Size::Y,v,v).iter()
                    .map(|t|dirty_price(t.len())).sum::<usize>();
            }
        }
        if current.is_some() {price+=6;}
        price
    }

    fn prefer_y_decoder(&self,lo:usize,hi:usize)->bool {
        self.y_decoder_price(lo,hi)<(lo..=hi).map(|v|
            2*self.terms(Size::Y,v,v).iter().map(|t|dirty_price(t.len())).sum::<usize>()
        ).sum::<usize>()
    }

    /// Exact split of the inherited numeric equality intervals at E=128.
    /// Padding holes stay included exactly as in terms(); this is not a
    /// valid-state-only decoder. Z has one fixed five-bit residue here.
    fn class_terms(&self,size:Size,v:usize)->(Vec<Vec<(QubitId,bool)>>,Vec<Vec<(QubitId,bool)>>) {
        assert!(self.y.normalized);
        let (range,residue)=match size {
            Size::Y=>((v,v),None),
            Size::Z=>{
                if !(1..=256).contains(&v) {return(vec![],vec![]);}
                let lo=(226isize-v as isize).max(1) as usize;
                let hi=(257isize-v as isize).min(128);
                if hi<lo as isize {return(vec![],vec![]);}
                ((lo,hi as usize),Some(v%32))
            },
        };
        let word=self.y.word();let mut low=vec![];let mut high=vec![];
        for (lo,hi) in self.y.size_intervals(range.0,range.1) {
            if lo<128 {low.extend(View::interval_terms(&word[..7],lo,hi.min(128)));}
            if hi>128 {high.extend(View::interval_terms(&word,lo.max(128),hi));}
        }
        if let Some(residue)=residue {
            for term in low.iter_mut().chain(high.iter_mut()) {
                term.extend(self.zlow.iter().enumerate()
                    .map(|(i,&q)|(q,(residue>>i)&1==0)));
            }
        }
        (low,high)
    }

    /// The existing callback workspace retains C=[E<128] over a complete
    /// ripple. Only H2..4 determine C; none is an arithmetic operand, even
    /// when logical Q aliases L. H5/P258 is ignored. This exact preparation
    /// is also its inverse and costs four literal CCX in either direction.
    fn toggle_class(&self,b:&mut B,class:QubitId,dirty:&[QubitId]) {
        assert!(self.y.normalized&&!self.ports().contains(&class));
        let mut excluded=self.ports();excluded.push(class);
        let bank=donors(dirty,&excluded);
        let lits:Vec<_>=self.y.high[2..5].iter().map(|&q|(q,true)).collect();
        mc_xor(b,&lits,class,&[],&bank);
    }

    /// Public source-price admission for one whole inverse kernel. The
    /// callback extras are distinct from every applicable metadata cube
    /// in these two callers. No alternate gate tapes are built to price it.
    fn prefer_class(&self,size:Size,lo:usize,hi:usize,extras:&[usize])->bool {
        let mut old=0;let mut new=8; // class preparation and literal inverse
        for v in lo..=hi {
            let original=self.terms(size,v,v);let (low,high)=self.class_terms(size,v);
            for &extra in extras {
                old+=original.iter().map(|term|one_clean_price(term.len()+extra)).sum::<usize>();
                new+=low.iter().map(|term|known_price(term.len()+extra,3)).sum::<usize>();
                new+=high.iter().map(|term| {
                    let n=term.len()+extra;
                    dirty_price(n).min(known_price(n-1,1))
                }).sum::<usize>();
            }
        }
        new<old
    }

    /// All-data equality using held C and conditionally returned metadata.
    /// Low clauses use C as retained root and three complemented high lanes
    /// as known ones. A high clause has a positive high literal, which in
    /// turn implies !C; it may use complemented C as one known lane. No
    /// measurement cleanup is performed on any conditional helper.
    fn xor_eq_class(&self,b:&mut B,size:Size,v:usize,target:QubitId,
        extra:&[(QubitId,bool)],class:QubitId,dirty:&[QubitId]) {
        assert!(self.y.normalized&&!self.ports().contains(&class));
        let upper=&self.y.high[2..5];
        assert!(target!=class&&!upper.contains(&target));
        assert!(extra.iter().all(|&(q,_)|q!=class&&!upper.contains(&q)));
        let mut excluded=self.ports();excluded.extend([class,target]);
        excluded.extend(extra.iter().map(|&(q,_)|q));
        let bank=donors(dirty,&excluded);
        let (low,high)=self.class_terms(size,v);
        for (is_low,terms) in [(true,low),(false,high)] {
            for mut term in terms {
                let mut contradiction=false;
                for &(q,neg) in extra {
                    if let Some(&(_,old))=term.iter().find(|(p,_)|*p==q) {
                        if old!=neg {contradiction=true;break;}
                    } else {term.push((q,neg));}
                }
                if contradiction {continue;}
                assert!(!term.iter().any(|&(q,_)|q==target||q==class));
                if is_low {
                    assert!(term.iter().all(|&(q,_)|!upper.contains(&q)));
                    for &q in upper {b.x(q);}
                    known_query(b,class,upper,&term,target,&bank);
                    for &q in upper.iter().rev() {b.x(q);}
                } else if known_price(term.len()-1,1)<dirty_price(term.len()) {
                    let pos=term.iter().position(|&(q,neg)|!neg&&upper.contains(&q))
                        .expect("high dyadic interval lacks a positive high literal");
                    let root=term.remove(pos).0;
                    b.x(class);known_query(b,root,&[class],&term,target,&bank);b.x(class);
                } else {mc_xor(b,&term,target,&[],&bank);}
            }
        }
    }

    fn xor_bit(&self,b:&mut B,size:Size,bit:usize,target:QubitId,
        dirty:&[QubitId]) {
        let width=1usize<<bit;
        let end=match size {Size::Y=>128,Size::Z=>256};
        for lo in (width..=end).step_by(2*width) {
            self.xor_range(b,size,lo,(lo+width-1).min(end),target,&[],&[],dirty);
        }
    }

    /// S-226 -> Z mod32. This is the exact five-bit function of the old
    /// normalized Y readers on every packet, including padding holes:
    /// E<108: L+1; 108..110:13; 110..112:12; 112..120:14;
    /// 120..128:15; 128..160:16; 160..672:H+12; E>=672:0.
    /// A complete membership flag survives each small arithmetic block;
    /// the Y source returns before that predicate is read again. H5 is
    /// ignored throughout, and the captured inverse restores S off-act.
    fn to_z_record(&self,b:&mut B,flag:QubitId,dirty:&[QubitId])->Vec<G> {
        assert!(self.y.normalized);
        let mut occupied=self.ports();occupied.push(flag);
        let bank=donors(dirty,&occupied);
        let word=self.y.word();
        assert_eq!(word.len(),10);
        rec(b,|b| {
            super::super::modp_frogdrop::add_const_exact(b,&self.zlow,None,226,&bank);
            for (lo,hi,constant) in [(0,108,1u64),(108,110,13),(110,112,12),
                (112,120,14),(120,128,15),(128,160,16),(160,672,12)] {
                let query=|b:&mut B|for term in View::interval_terms(&word,lo,hi) {
                    mc_xor(b,&term,flag,&[],&bank);
                };
                query(b);
                let add=rec(b,|b| {
                    let source=match lo {
                        0=>Some(self.y.low.as_slice()),
                        160=>Some(&self.y.high[..5]),
                        _=>None,
                    };
                    if let Some(source)=source {
                        super::super::arith::ttk_add(b,source,&self.zlow,Some(flag),None);
                    }
                    super::super::modp_frogdrop::add_const_exact(
                        b,&self.zlow,Some(flag),constant,&bank);
                });
                b.play(&add,true);
                query(b);
            }
        })
    }
}

/// Retain one complete range predicate through a whole immutable-size
/// walk. Every query returns its clean prefixes before body; only `flag`
/// remains held. Bodies below write distinct P lanes, never read size
/// bits, extra controls, sign or prefix owners. P258 may alias H5, which
/// every normalized size query ignores. The finite public-range source
/// ledger admits all three callers in both directions. Emit directly:
/// capturing the old quadratic range walk would retain its large tape.
#[allow(clippy::too_many_arguments)]
fn range_walk(b:&mut B,sizes:&Sizes,size:Size,start:usize,end:usize,
    flag:QubitId,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId],
    range:impl Fn(usize)->(usize,usize),mut body:impl FnMut(&mut B,usize)) {
    if start>=end {return;}
    let first=range(start);
    sizes.xor_range(b,size,first.0,first.1,flag,extra,clean,dirty);
    let mut previous=first;
    for l in start..end {
        let next=range(l);
        sizes.xor_range_delta(b,size,previous,next,flag,extra,clean,dirty);
        body(b,l);previous=next;
    }
    sizes.xor_range(b,size,previous.0,previous.1,flag,extra,clean,dirty);
}

/// Exact rotation of a whole physical word. The metadata and queried flag
/// are outside the word; every intermediate flag is returned. Using the
/// full word makes the captured inverse valid on inactive garbage too.
fn rotate_up_const(b:&mut B,word:&[QubitId],amount:usize,flag:QubitId) {
    if word.len()<2 {return;}
    let shift=amount%word.len();if shift==0 {return;}
    let mut a=word.len();let mut d=shift;
    while d!=0 {let t=a%d;a=d;d=t;}
    for start in 0..a {
        let mut orbit=vec![start];let mut next=(start+shift)%word.len();
        while next!=start {orbit.push(next);next=(next+shift)%word.len();}
        for i in (1..orbit.len()).rev() {b.cswap(flag,word[orbit[i]],word[orbit[i-1]]);}
    }
}

/// Literal interval query used only by the complete rotation conjugation.
/// All work and metadata ports have already been removed from `dirty`.
fn rotation_interval(b:&mut B,bits:&[QubitId],lo:usize,hi:usize,
    target:QubitId,extra:&[(QubitId,bool)],dirty:&[QubitId]) {
    assert!(!bits.contains(&target)&&extra.iter().all(|(q,_)|*q!=target&&!bits.contains(q)));
    for mut term in View::interval_terms(bits,lo,hi) {
        term.extend_from_slice(extra);mc_xor(b,&term,target,&[],dirty);
    }
}

/// U' is rotation by Z on the acted domain and a reversible extension
/// elsewhere. It is used ONLY as U'^-1; reflection(act); U'. On act=0
/// reflection is identity, so the two complete records cancel even for
/// padding holes and arbitrary skipped/DONE data. Do not use this reader
/// in generic xor_bit, a gathered query, or with the old U's inverse.
///
/// 226<=Z+Y<=257 and 1<=Y<=128 imply Z=96+L+32*r, r in0..5.
/// The three returned owners are e/fa/g; sv and top_save remain held.
fn z_rotation_record(b:&mut B,sizes:&Sizes,word:&[QubitId],
    e:QubitId,fa:QubitId,g:QubitId,dirty:&[QubitId])->Vec<G> {
    assert!(sizes.y.normalized&&sizes.zlow.len()==5&&word.len()==NP);
    let encoded=sizes.y.word();let low=&sizes.y.low;let high=&sizes.y.high[..5];
    let z=&sizes.zlow;
    let address:Vec<_>=encoded.iter().chain(z).copied().collect();
    let mut unique:BTreeSet<_>=address.iter().copied().collect();
    assert_eq!(unique.len(),address.len());
    assert!([e,fa,g].into_iter().all(|q|unique.insert(q)));
    assert!(word.iter().all(|q|!unique.contains(q)));
    assert_eq!(word.iter().collect::<BTreeSet<_>>().len(),word.len());
    let mut excluded=sizes.ports();excluded.extend_from_slice(word);excluded.extend([e,fa,g]);
    let bank=donors(dirty,&excluded);assert!(bank.len()>=8);
    let d=bank[0];
    let low_region=|b:&mut B|rotation_interval(b,&encoded,0,108,fa,&[],&bank);
    rec(b,|b| {
        // Constant rotation has no Toffoli: the same cycle convention as
        // rotate_up_const, with unconditional swaps for the bias96.
        let shift=96usize%word.len();let mut gcd=word.len();let mut rem=shift;
        while rem!=0 {let next=gcd%rem;gcd=rem;rem=next;}
        for start in 0..gcd {
            let mut orbit=vec![start];let mut next=(start+shift)%word.len();
            while next!=start {orbit.push(next);next=(next+shift)%word.len();}
            for i in (1..orbit.len()).rev() {b.swap(word[orbit[i]],word[orbit[i-1]]);}
        }
        for bit in 0..5 {rotate_up_const(b,word,1usize<<bit,z[bit]);}

        // E<108: Y=E+1. Put w=H+ceil((E.low+L)/32) into H.low3.
        // e is erased before every rotation; the record never uses g.
        low_region(b);
        let a=rec(b,|b| {
            super::super::arith::ttk_add(b,low,z,Some(fa),Some((e,d)));
            super::super::modp_frogdrop::add_const_exact(b,&high[..3],Some(e),1,&bank);
            // After modulo addition, carry=[sum<E.low]. This exact full
            // five-bit query clears e, including arbitrary fa=0 data.
            for &q in z {b.x(q);}
            super::super::arith::ttk_carry(b,low,z,fa,e,d);
            for &q in z {b.x(q);}
            let nonzero=|b:&mut B| {
                b.cx(fa,e);rotation_interval(b,z,0,1,e,&[(fa,false)],&bank);
            };
            nonzero(b);
            super::super::modp_frogdrop::add_const_exact(b,&high[..3],Some(e),1,&bank);
            nonzero(b);
        });
        b.play(&a,false);
        // r=5-w mod8; on fa=1 w is0..5, hence no modular ambiguity.
        // NOT followed by +6 is an affine three-bit X/CX permutation.
        let negate=rec(b,|b| {
            for &q in &high[..3] {b.x(q);}
            super::super::modp_frogdrop::add_const_exact(b,&high[..3],None,6,&bank);
        });
        b.play(&negate,false);
        for bit in 0..3 {
            b.ccx(fa,high[bit],g);rotate_up_const(b,word,32usize<<bit,g);b.ccx(fa,high[bit],g);
        }
        b.play(&negate,true);b.play(&a,true);low_region(b);

        // The disjoint medium/high cases have r in{0,1}. Accumulate one
        // returned predicate, perform a single rotation32, then uncompute.
        // Padding holes take a chosen extension inside their whole block.
        let one=rec(b,|b| {
            for (lo,hi,limit) in [(108,112,20),(112,120,19),(120,128,18),(128,160,17)] {
                rotation_interval(b,&encoded,lo,hi,fa,&[],&bank);
                rotation_interval(b,z,0,limit+1,g,&[(fa,false)],&bank);
                rotation_interval(b,&encoded,lo,hi,fa,&[],&bank);
            }
            rotation_interval(b,high,5,21,fa,&[],&bank);
            let sum=rec(b,|b|super::super::arith::ttk_add(b,high,z,Some(fa),Some((e,d))));
            b.play(&sum,false);
            rotation_interval(b,z,0,22,g,&[(fa,false),(e,true)],&bank);
            b.play(&sum,true);
            rotation_interval(b,high,5,21,fa,&[],&bank);
        });
        b.play(&one,false);rotate_up_const(b,word,32,g);b.play(&one,true);
    })
}

fn rotation_record(b:&mut B,sizes:&Sizes,size:Size,word:&[QubitId],flag:QubitId,
    work:[QubitId;2],dirty:&[QubitId])->Vec<G> {
    if matches!(size,Size::Z) {return z_rotation_record(b,sizes,word,work[0],work[1],flag,dirty);}
    assert!(!word.contains(&flag));
    let bank=donors(dirty,word);
    rec(b,|b| {
        let bits=match size {Size::Y=>8,Size::Z=>9};
        for bit in 0..bits {
            sizes.xor_bit(b,size,bit,flag,&bank);
            rotate_up_const(b,word,1usize<<bit,flag);
            sizes.xor_bit(b,size,bit,flag,&bank);
        }
    })
}

/// Always materialize fa, including a publicly constant guard: act is
/// subsequently X-borrowed as a conditional-zero carry and cannot be read
/// by a query in the ripple. The same involution erases fa after return.
fn toggle_guard(b:&mut B,sizes:&Sizes,to_z:&[G],act:QubitId,fa:QubitId,
    lim:isize,dirty:&[QubitId]) {
    assert_ne!(act,fa);
    if lim<226 {return;}
    b.play(to_z,true);
    let end=((lim-226+1) as usize).min(32);
    let mut forbidden=sizes.ports();forbidden.extend([act,fa]);
    let bank=donors(dirty,&forbidden);
    for mut term in View::interval_terms(&sizes.zlow,0,end) {
        term.push((act,false));mc_xor(b,&term,fa,&[],&bank);
    }
    b.play(to_z,false);
}

/// Complete inverse-pair enable. Keep it independent of sv while sv is
/// loaned as membership workspace. On every live extracted e, guard257
/// and !sv hold, hence this guard258 enable is also true. Off enable e=0.
fn toggle_inverse_enable(b:&mut B,sizes:&Sizes,to_z:&[G],act:QubitId,
    sv:QubitId,fa:QubitId,lim:isize,dirty:&[QubitId]) {
    assert!(act!=sv&&act!=fa&&sv!=fa);
    if lim<226 {return;}
    b.play(to_z,true);
    let end=((lim-226+1) as usize).min(32);
    let mut forbidden=sizes.ports();forbidden.extend([act,sv,fa]);
    let bank=donors(dirty,&forbidden);
    for mut term in View::interval_terms(&sizes.zlow,0,end) {
        term.extend([(act,false),(sv,true)]);
        mc_xor(b,&term,fa,&[],&bank);
    }
    b.play(to_z,false);
}

/// Complete restoring ripple with an optional persistent low-class
/// decoder. SizeZ uses nine Q112..120 lanes, zero on enabled translated-low
/// shots because Q=Y and Y<=108; its source is the disjoint ring. SizeY
/// uses six Q112..117 lanes only from the first query v<=108 onward, after
/// those source cells and all encoded L cells have been restored. Higher
/// Y classes may leave the prefix lanes dirty, but explicit class controls
/// disable their contribution and literal Dec.clear returns them.
/// Off enable e=0 in both production directions, so arbitrary membership
/// values cannot write arithmetic or leave a mask. This whole-kernel
/// contract is essential: the cached query is not an all-data oracle.
#[allow(clippy::too_many_arguments)]
fn virtual_divide_kernel(b:&mut B,sizes:&Sizes,size:Size,shifted:bool,
    prefixes:&[QubitId],t:&[QubitId],s:&[QubitId],carry:QubitId,
    enable:QubitId,e:QubitId,mask:QubitId,tmp:QubitId,lo:usize,hi:usize,
    dirty:&[QubitId]) {
    let z_cached=shifted&&sizes.prefer_z_decoder(lo,hi);
    let y_cached=!shifted&&matches!(size,Size::Y)&&sizes.prefer_y_decoder(lo,hi);
    if !z_cached&&!y_cached {
        let mut query=|b:&mut B,v,target,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]| {
            if shifted {sizes.xor_terms(b,sizes.z_epoch_terms(v),target,extra,clean,dirty);}
            else {sizes.xor_eq(b,size,v,target,extra,clean,dirty);}
        };
        joint_kernel::virtual_divide(b,t,s,carry,enable,e,mask,tmp,lo,hi,dirty,&mut query);
        return;
    }
    assert_eq!(prefixes.len(),9);
    let prefixes=if z_cached {prefixes}else{&prefixes[..6]};
    let mut used:BTreeSet<_>=sizes.ports().into_iter().chain(t.iter().copied())
        .chain([carry,enable,e,mask,tmp]).collect();
    assert!(prefixes.iter().all(|q|used.insert(*q)),
        "persistent Q prefixes overlap a target, metadata or role port");
    if z_cached {
        assert!(matches!(size,Size::Z)&&s.iter().all(|q|!prefixes.contains(q)));
    } else {
        // Source loans are temporal here, not disjoint for the full pass:
        // every present prefix must be its original Q112+i source cell.
        // Dec starts below109, after all of these cells have been undone.
        assert!(s.iter().enumerate().all(|(i,q)|
            prefixes.iter().position(|p|p==q).is_none_or(|j|i==112+j)));
    }
    let bank=donors(dirty,prefixes);
    let address:Vec<_>=if z_cached {
        sizes.zlow.iter().chain(&sizes.y.high[..5]).copied().collect()
    }else{sizes.y.word()[..7].to_vec()};
    let prior=super::super::mask::R11O11_DECCC.with(|state| {
        let prior=state.borrow().clone();let mut scoped=prior.clone();
        for &q in prefixes {if !scoped.contains(&q) {scoped.push(q);}}
        *state.borrow_mut()=scoped;prior
    });
    let mut decoder=super::super::mask::Dec::new(&address,prefixes);
    let mut query=|b:&mut B,v,target,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]| {
        assert!(extra.is_empty()&&clean.is_empty(),
            "persistent decoder is scoped to virtual_divide membership queries");
        if z_cached {
            let has_low=(118..=256).contains(&v);
            if has_low {
                let address=((32-v/32)<<5)+(v%32);
                let matched=decoder.ctrls(b,address);assert_eq!(matched.len(),1);
                mc_xor(b,&[(sizes.y.high[3],false),(sizes.y.high[4],false),matched[0]],
                    target,&[],dirty);
            }
            let high:Vec<_>=sizes.z_epoch_terms(v).into_iter().skip(usize::from(has_low)).collect();
            sizes.xor_terms(b,high,target,&[],&[],dirty);
        } else if v<=108 {
            let matched=decoder.ctrls(b,v-1);assert_eq!(matched.len(),1);
            mc_xor(b,&[(sizes.y.high[2],true),(sizes.y.high[3],true),
                (sizes.y.high[4],true),matched[0]],target,&[],dirty);
        } else {
            sizes.xor_eq(b,Size::Y,v,target,&[],&[],dirty);
        }
    };
    joint_kernel::virtual_divide(b,t,s,carry,enable,e,mask,tmp,lo,hi,&bank,&mut query);
    drop(query);decoder.clear(b);
    super::super::mask::R11O11_DECCC.with(|state|*state.borrow_mut()=prior);
}

/// Complete ring-source restoring kernel in the direct ALLZ coordinate.
/// On enabled valid shots a positive rank1/rank2 implies Z>=160, hence
/// Y<=97 and Q112..118 are zero. Else those lanes are arbitrary data:
/// literal CCX decoder cleanup restores them, and e=0 off enable makes
/// the complete restoring kernel identity despite arbitrary membership.
/// This is not an all-data standalone equality oracle.
#[allow(clippy::too_many_arguments)]
fn all_z_divide_kernel(b:&mut B,sizes:&Sizes,cached:bool,prefixes:&[QubitId],
    t:&[QubitId],s:&[QubitId],carry:QubitId,enable:QubitId,e:QubitId,
    mask:QubitId,tmp:QubitId,lo:usize,hi:usize,dirty:&[QubitId]) {
    let word=sizes.y.word();
    assert!(word.iter().chain(&sizes.zlow).all(|q|!t.contains(q)&&!s.contains(q)),
        "direct ALLZ metadata overlaps ring-source arithmetic");
    if !cached {
        let mut query=|b:&mut B,v,target,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]| {
            assert!(extra.is_empty()&&clean.is_empty());
            super::super::empty_packet::xor_z_eq(
                b,&word,&sizes.zlow,v,target,extra,clean,dirty);
        };
        joint_kernel::virtual_divide(b,t,s,carry,enable,e,mask,tmp,lo,hi,dirty,&mut query);
        return;
    }
    assert_eq!(prefixes.len(),7);
    let mut used:BTreeSet<_>=sizes.ports().into_iter().chain(t.iter().copied())
        .chain(s.iter().copied()).chain([carry,enable,e,mask,tmp]).collect();
    assert!(prefixes.iter().all(|q|used.insert(*q)),
        "direct ALLZ prefixes overlap data, metadata or a retained role");
    let bank=donors(dirty,prefixes);
    let address:Vec<_>=sizes.zlow.iter().chain(&word[7..10]).copied().collect();
    let prior=super::super::mask::R11O11_DECCC.with(|state| {
        let prior=state.borrow().clone();let mut scoped=prior.clone();
        for &q in prefixes {if !scoped.contains(&q) {scoped.push(q);}}
        *state.borrow_mut()=scoped;prior
    });
    let mut decoder=super::super::mask::Dec::new(&address,prefixes);
    let mut query=|b:&mut B,v,target,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]| {
        assert!(extra.is_empty()&&clean.is_empty(),
            "direct ALLZ cache is scoped to restoring membership queries");
        if (160..=256).contains(&v) {
            let matched=decoder.ctrls(b,v-96);assert_eq!(matched.len(),1);
            // rank1 is positive for values160..223, rank2 for224..256.
            // Either root guarantees the complete seven-lane zero bank
            // on enabled shots; all other address bits stay in Dec.
            let root=if v<224 {address[6]}else{address[7]};
            b.ccx(root,matched[0].0,target);
        } else {
            super::super::empty_packet::xor_z_eq(
                b,&word,&sizes.zlow,v,target,&[],&[],dirty);
        }
    };
    joint_kernel::virtual_divide(b,t,s,carry,enable,e,mask,tmp,lo,hi,&bank,&mut query);
    drop(query);decoder.clear(b);
    super::super::mask::R11O11_DECCC.with(|state|*state.borrow_mut()=prior);
}

fn play_nonincreasing(b:&mut B,old:&[G],candidate:&[G]) {
    let take=match(super::read_lane_tree::prices(old),super::read_lane_tree::prices(candidate)) {
        (Some((of,oi)),Some((nf,ni)))=>nf<=of&&ni<=oi&&(nf<of||ni<oi),
        _=>false,
    };
    b.play(if take {candidate}else{old},false);
}

fn index_tree(leaves:&[(usize,QubitId)],level:usize,
    swaps:&mut Vec<(usize,QubitId,QubitId)>)->QubitId {
    assert!(!leaves.is_empty());
    if level==0 {assert_eq!(leaves.len(),1);return leaves[0].1;}
    let bit=level-1;
    let split=leaves.partition_point(|&(v,_)|(v>>bit)&1==0);
    if split==0 {return index_tree(leaves,bit,swaps);}
    if split==leaves.len() {return index_tree(leaves,bit,swaps);}
    let a=index_tree(&leaves[..split],bit,swaps);
    let z=index_tree(&leaves[split..],bit,swaps);
    swaps.push((bit,a,z));a
}

/// One complete selected gather. Z's five actual low ports supply the
/// lower tree levels. Its higher address bits are queried successively
/// into the same flag and returned before the next level. Equal-level
/// swaps belong to disjoint subtrees, so the level grouping preserves the
/// ordinary postorder permutation. Membership is formed only after every
/// address flag was returned, then the complete gather is inverted.
fn gathered(b:&mut B,sizes:&Sizes,size:Size,leaves:&[(usize,QubitId)],flag:QubitId,
    dirty:&[QubitId],mut body:impl FnMut(&mut B,QubitId,QubitId,&[QubitId])) {
    if leaves.is_empty() {return;}
    if matches!(size,Size::Y) {sizes.y.gathered_at(b,leaves,flag,dirty,body);return;}
    assert!(leaves.windows(2).all(|w|w[0].0+1==w[1].0));
    let leaf_ports:Vec<_>=leaves.iter().map(|(_,q)|*q).collect();
    let address_ports:Vec<_>=sizes.y.word().into_iter().chain(sizes.zlow.iter().copied()).collect();
    // Normalized H5 is logical P258, not an address bit. Public candidate
    // leaf lists may include it even when the final enable excludes that
    // address. It is safe data throughout gather/body/inverse and remains
    // excluded from every dirty-helper bank by Sizes::ports().
    assert!(leaf_ports.iter().all(|q|!address_ports.contains(q)&&*q!=flag));
    assert_eq!(leaf_ports.iter().copied().collect::<BTreeSet<_>>().len(),leaf_ports.len());
    let bank=donors(dirty,&leaf_ports);
    let mut swaps=vec![];let root=index_tree(leaves,9,&mut swaps);
    let gather=rec(b,|b| {
        for bit in 0..9 {
            if !swaps.iter().any(|&(j,_,_)|j==bit) {continue;}
            if bit>=5 {sizes.xor_bit(b,size,bit,flag,&bank);}
            let control=if bit<5 {sizes.zlow[bit]}else{flag};
            for &(_,a,z) in swaps.iter().filter(|&&(j,_,_)|j==bit) {b.cswap(control,a,z);}
            if bit>=5 {sizes.xor_bit(b,size,bit,flag,&bank);}
        }
    });
    b.play(&gather,false);
    sizes.xor_range(b,size,leaves[0].0,leaves.last().unwrap().0,flag,&[],&[],&bank);
    body(b,root,flag,&bank);
    sizes.xor_range(b,size,leaves[0].0,leaves.last().unwrap().0,flag,&[],&[],&bank);
    b.play(&gather,true);
}

fn z_swap_mcx_price(n:usize,clean:usize)->usize {
    if n<=2 {return dirty_price(n);}
    let used=clean.min(n-2);
    if used==0 {return dirty_price(n);}
    let rest=n-used-1;
    used+if rest==1 {dirty_price(rest+1)}else{known_price(rest,2*used)}
}

/// In the untouched Y>=109 branch, h=floor(Z/32) is3+r. The four
/// medium codes can first be permuted so H=Y-108 (1..4); ordinary high
/// codes already have H=Y-108 (5..20). For1<=H<=20,
/// r=carry5(H+z) XOR [(H+z)mod32<=21]. If carry is one the low sum is at
/// most19, so the XOR is zero. Otherwise it is exactly [H+z<=21].
/// This record returns all metadata and XORs one bit into g on ALL data.
fn z_high_rank_record(b:&mut B,sizes:&Sizes,g:QubitId,dirty:&[QubitId])->Vec<G> {
    let high=&sizes.y.high[..5];let low=&sizes.y.low;let z=&sizes.zlow;
    let mut excluded=sizes.ports();excluded.push(g);let bank=donors(dirty,&excluded);
    assert!(!sizes.ports().contains(&g)&&bank.len()>=5);
    rec(b,|b| {
        let medium=rec(b,|b| {
            // E108..111: H3<->1. E112..119: H3<->2. The reverse
            // transposition partners are outside the acted high class.
            mc_xor(b,&[(high[0],false),(high[2],true),(high[3],true),(high[4],true),
                (low[2],false),(low[3],false),(low[4],true)],high[1],&[],&bank);
            mc_xor(b,&[(high[1],false),(high[2],true),(high[3],true),(high[4],true),
                (low[3],true),(low[4],false)],high[0],&[],&bank);
        });
        b.play(&medium,false);
        super::super::arith::ttk_carry_u(b,high,z,g,bank[0]);
        let sum=rec(b,|b|super::super::arith::ttk_add(b,high,z,None,None));
        b.play(&sum,false);
        for term in View::interval_terms(z,0,22) {mc_xor(b,&term,g,&[],&bank);}
        b.play(&sum,true);b.play(&medium,true);
    })
}

/// Complete high-class and public-address membership. Leaves are payload
/// only, so these original H/L controls remain valid after the gather.
fn z_high_swap_terms(sizes:&Sizes,lo:usize,hi:usize,g:QubitId)->Vec<Vec<(QubitId,bool)>> {
    let mut out=vec![];let word=sizes.y.word();
    for (rank,base) in [(false,96usize),(true,128usize)] {
        let a=lo.saturating_sub(base);let end=(hi+1).saturating_sub(base).min(32);
        if a>=end {continue;}
        for class in View::interval_terms(&word,108,672) {
            for mut address in View::interval_terms(&sizes.zlow,a,end) {
                address.extend_from_slice(&class);address.push((g,!rank));out.push(address);
            }
        }
    }
    out
}

/// Two complete conjugations in the paid translated-Z packet. Their
/// swap bodies retain both original enable and full class/range care.
/// All metadata/payload outside the selected swap is restored, including
/// arbitrary off-enable packets. H5 may be a payload leaf; H0..4 may not.
/// Return false before emitting anything if the literal source price is
/// not below both inherited selected-swap alternatives.
fn z_selected_swap(b:&mut B,sizes:&Sizes,leaves:&[(usize,QubitId)],
    flight:QubitId,enable:QubitId,g:QubitId,clean:&[QubitId],dirty:&[QubitId])->bool {
    if leaves.is_empty() {return false;}
    assert!(sizes.y.normalized&&sizes.zlow.len()==5);
    assert!(leaves.windows(2).all(|p|p[0].0+1==p[1].0));
    let (lo,hi)=(leaves[0].0,leaves.last().unwrap().0);
    assert!(lo>=1&&hi<=256);
    let metadata:Vec<_>=sizes.y.word().into_iter().chain(sizes.zlow.iter().copied()).collect();
    let mut occupied:BTreeSet<_>=metadata.iter().copied().collect();
    assert_eq!(occupied.len(),metadata.len());
    assert!([flight,enable,g].into_iter().chain(clean.iter().copied()).all(|q|occupied.insert(q)));
    assert!(leaves.iter().all(|(_,q)|!occupied.contains(q)));
    assert_eq!(leaves.iter().map(|(_,q)|q).collect::<BTreeSet<_>>().len(),leaves.len());
    occupied.extend(leaves.iter().map(|&(_,q)|q));
    let bank=donors(dirty,&occupied.into_iter().collect::<Vec<_>>());
    let high=&sizes.y.high[..5];
    let raw_address:Vec<_>=sizes.zlow.iter().chain(high).copied().collect();
    let low_terms=View::interval_terms(&raw_address,lo,hi+1);
    let mut low_swaps=vec![];let low_root=index_tree(leaves,9,&mut low_swaps);
    let high_leaves:Vec<_>=leaves.iter().copied().filter(|(v,_)|(98..=148).contains(v)).collect();
    let high_terms=if high_leaves.is_empty() {vec![]}else {
        z_high_swap_terms(sizes,high_leaves[0].0,high_leaves.last().unwrap().0,g)
    };
    let mut high_swaps=vec![];
    let high_root=if high_leaves.is_empty() {None}else{Some(index_tree(&high_leaves,8,&mut high_swaps))};

    // Public literal prices only. Cached generic Z-bit prices depend on
    // encoding geometry, never on qubit IDs or an input/cohort trajectory.
    static BIT_PRICES:std::sync::OnceLock<[usize;4]>=std::sync::OnceLock::new();
    let bit_prices=BIT_PRICES.get_or_init(||std::array::from_fn(|j| {
        let width=1usize<<(j+5);
        (width..=256).step_by(2*width).map(|a|sizes.terms(Size::Z,a,(a+width-1).min(256))
            .iter().map(|t|dirty_price(t.len())).sum::<usize>()).sum()
    }));
    let old_enum:usize=leaves.iter().map(|&(v,_)|1+2*sizes.terms(Size::Z,v,v).iter()
        .map(|t|z_swap_mcx_price(t.len()+1,clean.len())).sum::<usize>()).sum();
    let old_gather=2*low_swaps.len()+z_swap_mcx_price(3,clean.len())
        +2*sizes.terms(Size::Z,lo,hi).iter().map(|t|dirty_price(t.len())).sum::<usize>()
        +(5..9).filter(|j|low_swaps.iter().any(|(bit,_,_)|bit==j))
            .map(|j|4*bit_prices[j-5]).sum::<usize>();
    let new_low=26+2*low_swaps.len()+low_terms.iter()
        .map(|t|z_swap_mcx_price(t.len()+2,clean.len()+1)).sum::<usize>();
    let new_high=if high_root.is_none(){0}else{218+2*high_swaps.len()+high_terms.iter()
        .map(|t|z_swap_mcx_price(t.len()+2,clean.len())).sum::<usize>()};
    if 372+new_low+new_high>=old_enum.min(old_gather) {return false;}
    assert!(bank.len()>=11);
    let epoch=sizes.z_epoch_record(b,enable,g,&bank);b.play(&epoch,false);

    // H->-H mod32 converts translated H24..29 to the actual Z high
    // word. Untouched acted Y>=109 has H3..20, whose negated address
    // is at least384 and is excluded by the full ten-bit Z<=256 range.
    let low_frame=rec(b,|b| {
        for &q in high {b.x(q);}
        super::super::modp_frogdrop::inc_dirty_free(b,high,&bank);
    });
    b.play(&low_frame,false);
    let low_gather=rec(b,|b|for &(bit,a,z) in &low_swaps {b.cswap(raw_address[bit],a,z);});
    b.play(&low_gather,false);
    let low_clean:Vec<_>=std::iter::once(g).chain(clean.iter().copied()).collect();
    for mut term in low_terms {
        term.push((enable,false));
        super::super::mid2::mc_swap(b,&term,low_root,flight,&low_clean,&bank);
    }
    b.play(&low_gather,true);b.play(&low_frame,true);

    if let Some(root)=high_root {
        let rank=z_high_rank_record(b,sizes,g,&bank);b.play(&rank,false);
        let gather=rec(b,|b| {
            for bit in 0..8 {
                if !high_swaps.iter().any(|(j,_,_)|*j==bit) {continue;}
                let control=if bit<5 {sizes.zlow[bit]}else{g};
                let negative=bit==5||bit==6;
                if negative {b.x(g);}
                for &(_,a,z) in high_swaps.iter().filter(|(j,_,_)|*j==bit) {b.cswap(control,a,z);}
                if negative {b.x(g);}
            }
        });
        b.play(&gather,false);
        for mut term in high_terms {
            term.push((enable,false));
            super::super::mid2::mc_swap(b,&term,root,flight,clean,&bank);
        }
        b.play(&gather,true);b.play(&rank,true);
    }
    b.play(&epoch,true);
    true
}

fn selected_swap(b:&mut B,sizes:&Sizes,size:Size,range:(usize,usize),
    lane:&dyn Fn(usize)->Option<QubitId>,flight:QubitId,enable:QubitId,
    flag:QubitId,clean:&[QubitId],dirty:&[QubitId]) {
    assert!(flight!=enable&&flight!=flag&&enable!=flag);
    let leaves:Vec<_>=(range.0..=range.1).filter_map(|v|lane(v).map(|q|(v,q))).collect();
    if matches!(size,Size::Z)&&z_selected_swap(b,sizes,&leaves,flight,enable,flag,clean,dirty) {return;}
    let old=rec(b,|b| {
        for &(v,q) in &leaves {
            assert!(q!=flight&&q!=enable&&q!=flag);
            sizes.xor_eq(b,size,v,flag,&[(enable,false)],clean,dirty);
            b.cswap(flag,flight,q);
            sizes.xor_eq(b,size,v,flag,&[(enable,false)],clean,dirty);
        }
    });
    let candidate=rec(b,|b|gathered(b,sizes,size,&leaves,flag,dirty,|b,root,member,bank| {
        super::super::mid2::mc_swap(b,&[(enable,false),(member,false)],root,flight,clean,bank);
    }));
    // Price only real primitive gates, in both playback directions. Opaque
    // rows keep the original lowering; no packed gate is counted as one.
    play_nonincreasing(b,&old,&candidate);
}

fn read_selected(b:&mut B,sizes:&Sizes,size:Size,range:(usize,usize),
    lane:&dyn Fn(usize)->Option<QubitId>,target:QubitId,enable:QubitId,
    clean:&[QubitId],dirty:&[QubitId]) {
    let leaves:Vec<_>=(range.0..=range.1).filter_map(|v|lane(v).map(|q|(v,q))).collect();
    let old=rec(b,|b| {
        for &(v,q) in &leaves {
            sizes.xor_eq(b,size,v,target,&[(enable,false),(q,false)],clean,dirty);
        }
    });
    let Some((&flag,pre))=clean.split_last() else {b.play(&old,false);return;};
    let candidate=rec(b,|b|gathered(b,sizes,size,&leaves,flag,dirty,|b,root,member,bank| {
        mc_xor(b,&[(enable,false),(member,false),(root,false)],target,pre,bank);
    }));
    play_nonincreasing(b,&old,&candidate);
}

fn expand_pre_record(b:&mut B,sizes:&Sizes,size:Size,range:(usize,usize),
    raw:&[QubitId],act:QubitId,flag:QubitId,dirty:&[QubitId])->Vec<G> {
    assert_eq!(raw.len(),NP);assert!(!raw.contains(&flag));
    rec(b,|b| {
        // h=257-T. Start with act &[T>=0], then remove T=i-1 as the
        // descending adjacent-swap threshold rises. No raw lane is used
        // as a metadata scratch owner while it can contain payload.
        b.cx(act,flag);
        let mut threshold=0usize;
        for i in ((257-range.1)+1..NP).rev() {
            let next=258-i;
            while threshold<next {
                if threshold>=range.0 && threshold<=range.1 {
                    sizes.xor_eq(b,size,threshold,flag,&[(act,false)],&[],dirty);
                }
                threshold+=1;
            }
            b.cswap(flag,raw[i],raw[i-1]);
        }
        sizes.xor_range(b,size,threshold,range.1,flag,&[(act,false)],&[],dirty);
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn col_digit_phase_joint(b:&mut B,fd:&Fd,cp:&ColPar,sc:&ColScr,pl:&PlCol,
    act:QubitId,ht:bool,roles:[QubitId;4],top_save:Option<QubitId>)
    ->splice258::PhaseTransition {
    assert!(super::super::frogdrop_col::c660_joint_size()&&splice258::enabled());
    assert_eq!(fd.sy.len(),5);assert_eq!(fd.ring.len(),257);assert_eq!(fd.q.len(),128);
    assert_eq!(pl.p.len(),splice258::PHYSICAL_NP);
    let [e,sv,fa,g]=roles;
    let raw=splice258::raw_context(pl,fd.ph);
    let sizes=Sizes{y:View::from_fd(fd,true),zlow:sc.sz[..5].to_vec()};
    let mut occupied=sizes.ports();occupied.extend(raw.p.iter().copied());
    // The size packet's ignored H5 is deliberately also raw P258.
    assert_eq!(sizes.y.high[5],fd.ph);
    let mut ordinary=BTreeSet::new();
    for q in roles.into_iter().chain([act]).chain(top_save) {
        assert!(ordinary.insert(q)&&!occupied.contains(&q));
    }
    assert!(ht==top_save.is_none(),"HR requires its separate returned top-save owner");
    occupied.extend(ordinary.iter().copied());
    let mut all_dirty=pl.dirty.clone();all_dirty.extend(fd.ring.iter().copied());
    all_dirty.extend(fd.q.iter().copied());all_dirty.extend(pl.p.iter().copied());
    let bank=donors(&all_dirty,&occupied);
    let raw_class=View::from_fd(fd,false);
    let phase=if ht {Some(raw_class.ht_phase_record(b,act,&bank))}else{None};
    if let Some(p)=&phase {b.play(p,true);}
    let to_z=sizes.to_z_record(b,g,&bank);b.play(&to_z,false);
    let zr=(cp.sz.0.max(1),cp.sz.1.min(256));
    let yr=(cp.sy.0.max(1),cp.sy.1.min(128));
    assert!(zr.0<=zr.1&&yr.0<=yr.1);
    let (rsize,rr,tsize,tr)=if ht {(Size::Y,yr,Size::Z,zr)}
        else {(Size::Z,zr,Size::Y,yr)};
    // HR's leading Z bit was displaced by the in-place quotient. Expose
    // the same one as the inherited top shuttle, then restore after digit.
    let top=top_save.map(|save|rec(b,|b| {
        for v in zr.0..=zr.1 {
            sizes.xor_eq(b,Size::Z,v,g,&[(act,false)],&[fa,e],&bank);
            b.x(fd.ring[v-1]);b.ccx(g,fd.ring[v-1],save);b.x(fd.ring[v-1]);
            b.ccx(g,save,fd.ring[v-1]);
            sizes.xor_eq(b,Size::Z,v,g,&[(act,false)],&[fa,e],&bank);
        }
    }));
    if let Some(t)=&top {b.play(t,false);}
    let expand=expand_pre_record(b,&sizes,tsize,tr,&raw.p,act,g,&bank);
    b.play(&expand,false);
    let logical_q:Vec<_>=fd.q[..123].iter().chain(sizes.y.low.iter()).copied().collect();
    let (rsource,tsource)=if ht {(&logical_q,&fd.ring)}else{(&fd.ring,&logical_q)};
    let z_epoch=(yr.0<=108).then(||sizes.z_epoch_record(b,act,g,&bank));
    let mut all_z_epoch:Option<Vec<G>>=None;
    let mut segment_start=b.tof;
    for k in (0..KE).rev() {
        if (rr.0+tr.0).max(226)>257usize.saturating_sub(k) {continue;}
        toggle_guard(b,&sizes,&to_z,act,fa,257-k as isize,&bank);
        let end=(k+rr.1+1).min(NP);
        let t=raw.p[k..end].to_vec();
        let s=rsource[..(end-k).min(rsource.len())].to_vec();
        let hi=rr.1.min(t.len()-1);
        let shifted=!ht&&z_epoch.is_some()&&sizes.prefer_z_epoch(rr.0,hi,&[],true);
        let all_z=if ht {None}else{sizes.all_z_divide_choice(rr.0,hi,shifted)};
        if all_z.is_some() {
            assert!(sizes.y.word().iter().chain(&sizes.zlow).all(|q|!t.contains(q)&&!s.contains(q)));
            let epoch=all_z_epoch.get_or_insert_with(||sizes.all_z_epoch_record(b,act,g,&bank));
            b.play(epoch,false);
        } else if shifted {
            assert!(sizes.y.word().iter().chain(&sizes.zlow).all(|q|!t.contains(q)&&!s.contains(q)));
            b.play(z_epoch.as_ref().unwrap(),false);
        }
        b.x(act);
        if let Some(cached)=all_z {
            all_z_divide_kernel(b,&sizes,cached,&fd.q[112..119],
                &t,&s,act,fa,e,g,sv,rr.0,hi,&bank);
        } else {
            virtual_divide_kernel(b,&sizes,rsize,shifted,&fd.q[112..121],
                &t,&s,act,fa,e,g,sv,rr.0,hi,&bank);
        }
        b.x(act);
        if all_z.is_some() {b.play(all_z_epoch.as_ref().unwrap(),true);}
        else if shifted {b.play(z_epoch.as_ref().unwrap(),true);}
        selected_swap(b,&sizes,rsize,rr,&|v|(v+k<NP).then(||raw.p[v+k]),
            e,fa,g,&[sv],&bank);
        toggle_guard(b,&sizes,&to_z,act,fa,257-k as isize,&bank);
    }
    super::super::f1_profile("digit.divide",segment_start,b.tof);segment_start=b.tof;
    read_selected(b,&sizes,tsize,tr,&|v|(v<NP).then(||raw.p[NP-1-v]),sv,act,&[e,fa,g],&bank);
    // Reflection moves each parked e_k from d[R+k] to W[T+1+k].
    // Whole-word conjugation returns the off-act word unchanged.
    let rotate=rotation_record(b,&sizes,rsize,&raw.p,g,[e,fa],&bank);
    b.play(&rotate,true);
    b.play(&to_z,true);
    for code in 0..32usize {
        let length=32-code;
        if length<2 {continue;}
        let mut term:Vec<_>=sizes.zlow.iter().enumerate().map(|(i,&q)|(q,(code>>i)&1==0)).collect();
        term.push((act,false));mc_xor(b,&term,g,&[e,fa],&bank);
        for i in 0..length/2 {b.cswap(g,raw.p[i],raw.p[length-1-i]);}
        mc_xor(b,&term,g,&[e,fa],&bank);
    }
    b.play(&to_z,false);b.play(&rotate,false);
    super::super::f1_profile("digit.sign_relocate",segment_start,b.tof);segment_start=b.tof;
    for k in 0..KE {
        if (rr.0+tr.0).max(226)>257usize.saturating_sub(k) {continue;}
        toggle_guard(b,&sizes,&to_z,act,fa,257-k as isize,&bank);
        selected_swap(b,&sizes,tsize,tr,&|v|(v+1+k<NP).then(||raw.p[NP-2-v-k]),
            e,fa,g,&[],&bank);
        toggle_guard(b,&sizes,&to_z,act,fa,257-k as isize,&bank);
        let end=(k+tr.1+1).min(NP);
        let t:Vec<_>=(k..end).map(|i|raw.p[NP-1-i]).collect();
        let s=tsource[..(end-k).min(tsource.len())].to_vec();
        let hi=tr.1.min(t.len()-1);
        assert!(sizes.y.high[..5].iter().all(|q|!t.contains(q)&&!s.contains(q)),
            "held decoder class overlaps a ripple operand");
        if let Some(shifted)=sizes.inverse_fusion_choice(tsize,tr.0,hi,s.len(),z_epoch.is_some(),k) {
            toggle_inverse_enable(b,&sizes,&to_z,act,sv,fa,258-k as isize,&bank);
            // Preserve the existing fusion admission. Only its already
            // selected HT translated SizeZ path enters this new comparison.
            let all_z=if ht&&shifted {sizes.all_z_divide_choice(tr.0,hi,shifted)}else{None};
            if all_z.is_some() {
                assert!(sizes.y.word().iter().chain(&sizes.zlow).all(|q|!t.contains(q)&&!s.contains(q)));
                let epoch=all_z_epoch.get_or_insert_with(||sizes.all_z_epoch_record(b,act,g,&bank));
                b.play(epoch,false);
            } else if shifted {
                assert!(sizes.y.word().iter().chain(&sizes.zlow).all(|q|!t.contains(q)&&!s.contains(q)));
                b.play(z_epoch.as_ref().unwrap(),false);
            }
            // fa=1 implies original sv=0: the complete restoring record
            // has its ordinary zero membership workspace. On fa=0, e=0;
            // every boundary/lower write and mask update is disabled,
            // and each membership query is reversed with no intervening
            // metadata change. Thus arbitrary sv, data and X(act) carry
            // return exactly there, in either literal direction. Do not
            // expose this conditional sv to a measured clean-AND helper.
            let restoring=rec(b,|b| {
                b.x(act);
                if let Some(cached)=all_z {
                    all_z_divide_kernel(b,&sizes,cached,&fd.q[112..119],
                        &t,&s,act,fa,e,g,sv,tr.0,hi,&bank);
                } else {
                    virtual_divide_kernel(b,&sizes,tsize,shifted,&fd.q[112..121],
                        &t,&s,act,fa,e,g,sv,tr.0,hi,&bank);
                }
                b.x(act);
            });
            b.play(&restoring,true);
            if all_z.is_some() {b.play(all_z_epoch.as_ref().unwrap(),true);}
            else if shifted {b.play(z_epoch.as_ref().unwrap(),true);}
            toggle_inverse_enable(b,&sizes,&to_z,act,sv,fa,258-k as isize,&bank);
            continue;
        }
        let add_shifted=ht&&z_epoch.is_some()&&sizes.prefer_z_epoch(tr.0,hi,&[2,1],false);
        if add_shifted {
            assert!(sizes.y.word().iter().chain(&sizes.zlow).all(|q|!t.contains(q)&&!s.contains(q)));
            b.play(z_epoch.as_ref().unwrap(),false);
        }
        let add_class=!add_shifted&&sizes.prefer_class(tsize,tr.0,hi,&[2,1]);
        if add_class {sizes.toggle_class(b,fa,&bank);}
        let mut add_query=|b:&mut B,v,target,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]| {
            if add_shifted {sizes.xor_terms(b,sizes.z_epoch_terms(v),target,extra,clean,dirty);}
            else if add_class {sizes.xor_eq_class(b,tsize,v,target,extra,fa,dirty);}
            else {sizes.xor_eq(b,tsize,v,target,extra,clean,dirty);}
        };
        b.x(act);
        joint_kernel::virtual_add(b,&t,&s,act,e,g,fa,tr.0,hi,&bank,&mut add_query);
        b.x(act);
        if add_class {sizes.toggle_class(b,fa,&bank);}
        if add_shifted {b.play(z_epoch.as_ref().unwrap(),true);}
        toggle_guard(b,&sizes,&to_z,act,fa,258-k as isize,&bank);
        let compare_shifted=ht&&z_epoch.is_some()&&sizes.prefer_z_epoch(tr.0,hi,&[2,4],false);
        if compare_shifted {b.play(z_epoch.as_ref().unwrap(),false);}
        let compare_class=!compare_shifted&&sizes.prefer_class(tsize,tr.0,hi,&[2,4]);
        if compare_class {sizes.toggle_class(b,g,&bank);}
        let mut compare_query=|b:&mut B,v,target,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]| {
            if compare_shifted {sizes.xor_terms(b,sizes.z_epoch_terms(v),target,extra,clean,dirty);}
            else if compare_class {sizes.xor_eq_class(b,tsize,v,target,extra,g,dirty);}
            else {sizes.xor_eq(b,tsize,v,target,extra,clean,dirty);}
        };
        b.x(act);
        joint_kernel::virtual_compare(b,&t,&s,act,fa,e,sv,g,tr.0,hi,&bank,&mut compare_query);
        b.x(act);
        if compare_class {sizes.toggle_class(b,g,&bank);}
        if compare_shifted {b.play(z_epoch.as_ref().unwrap(),true);}
        toggle_guard(b,&sizes,&to_z,act,fa,258-k as isize,&bank);
    }
    super::super::f1_profile("digit.inverse",segment_start,b.tof);segment_start=b.tof;
    // R+T<=257: the widening interval indicator equals [l<R] XOR
    // [l<258-T]. sv is zero off-act, so neither walk reads borrowed act.
    let widen_end=NP-1-tr.0;
    range_walk(b,&sizes,rsize,rr.0,widen_end,g,&[],&[e,fa],&bank,
        |l|(l+1,rr.1),|b,l|b.ccx(sv,g,raw.p[l]));
    range_walk(b,&sizes,tsize,rr.0,widen_end.min(258),g,&[],&[e,fa],&bank,
        |l|(tr.0,(257-l).min(tr.1)),|b,l|b.ccx(sv,g,raw.p[l]));
    super::super::f1_profile("digit.widen",segment_start,b.tof);segment_start=b.tof;
    // P[R] is not modified by the following strict complement, so erase
    // sign first and return its owner for the completed complement walk.
    read_selected(b,&sizes,rsize,rr,&|v|(v<NP).then(||raw.p[v]),sv,act,&[e,fa,g],&bank);
    super::super::f1_profile("digit.erase_sign",segment_start,b.tof);segment_start=b.tof;
    range_walk(b,&sizes,rsize,rr.0+1,NP,g,&[(act,false)],&[e,sv,fa],&bank,
        |l|(rr.0,(l-1).min(rr.1)),|b,l|b.cx(g,raw.p[l]));
    super::super::f1_profile("digit.complement",segment_start,b.tof);
    if let Some(t)=&top {b.play(t,true);}
    b.play(&to_z,true);
    splice258::PhaseTransition{raw,act,phase:fd.ph,ht}
}

/// Close only after the complete q/bq payload transition. The retained
/// activity may have moved (the caller must update session.act). Size and
/// sum code are restored; PH becomes zero on active shots before +21 puts
/// the HT class back. Inactive compressed payload and class are unchanged.
pub(crate) fn finish_joint_phase(b:&mut B,fd:&Fd,cp:&ColPar,sc:&ColScr,
    session:&splice258::PhaseTransition,flag:QubitId,dirty:&[QubitId]) {
    assert_eq!(fd.sy.len(),5);assert_eq!(session.phase,fd.ph);
    assert!(!session.raw.p.contains(&flag)&&flag!=session.act);
    let sizes=Sizes{y:View::from_fd(fd,true),zlow:sc.sz[..5].to_vec()};
    assert!(!sizes.ports().contains(&flag));
    let mut forbidden=sizes.ports();forbidden.extend(session.raw.p.iter().copied());
    forbidden.extend([flag,session.act]);
    let mut all=dirty.to_vec();all.extend(fd.ring.iter().copied());all.extend(fd.q.iter().copied());
    let bank=donors(&all,&forbidden);
    let z=sizes.to_z_record(b,flag,&bank);b.play(&z,false);
    let (size,range)=if session.ht {(Size::Y,(cp.sy.0.max(1),cp.sy.1.min(128)))}
        else {(Size::Z,(cp.sz.0.max(1),cp.sz.1.min(256)))};
    let mut query=|b:&mut B,v,target|sizes.xor_eq(b,size,v,target,&[(session.act,false)],&[],&bank);
    let close=splice258::compress_post_by_query_record(b,&session.raw.p,range,flag,&mut query);
    b.play(&close,false);b.play(&z,true);
    if session.ht {
        let phase=View::from_fd(fd,false).ht_phase_record(b,session.act,&bank);
        b.play(&phase,false);
    }
}
