//! Exact boundary/middle transitions while the logical Q word equals Y.
//! Both packet formats use the same eleven physical owners. Their different
//! high-Q envelopes are intentional; raw outer swaps must use BoundaryView.

use crate::circuit::QubitId;
use super::builder::{B,G};
use super::frogdrop_col::{Fd,rec,ge_cd};
use super::joint_boundary::{BoundaryView,HT_OFFSET,DONE_BASE};
use super::midg::joint_size::View;
use super::mask::{mc_xor,Dec};
use std::collections::BTreeSet;

fn bank(ports:&[QubitId],dirty:&[QubitId])->Vec<QubitId> {
    let occupied:BTreeSet<_>=ports.iter().copied().collect();
    let mut seen=BTreeSet::new();
    dirty.iter().copied().filter(|q|!occupied.contains(q)&&seen.insert(*q)).collect()
}

/// Translate normal Boundary into normal Middle, only where `extra` holds.
/// Q=Y implies H<2^max(SY-123,0), even in Boundary's wider HT envelope.
/// Descending HT first vacates its source codes before HR uses that space.
/// Every move is nondecreasing and every destination excludes later inputs.
pub(crate) fn boundary_to_middle_record(b:&mut B,fd:&Fd,flag:QubitId,
    extra:&[(QubitId,bool)],dirty:&[QubitId])->Vec<G> {
    let word=BoundaryView::from_fd(fd).word();
    assert!(!word.contains(&flag));
    assert!(extra.iter().all(|(q,_)|!word.contains(q)&&*q!=flag));
    let mut occupied=word.clone();occupied.push(flag);
    occupied.extend(extra.iter().map(|&(q,_)|q));
    let dirty=bank(&occupied,dirty);
    let old_rows=b.no_rows;b.no_rows=true;
    let out=rec(b,|b| {
        for wide in [true,false] {
            // HT1..92 is one contiguous +480 translation. Keep all larger
            // HT moves first, so their destinations are already >=764.
            let first=if wide {93usize}else{1usize};
            for size in (first..=128).rev() {
                let old=BoundaryView::interval(size,wide).0+if wide {HT_OFFSET}else{0};
                let new=View::active_interval(size).0+if wide {672}else{0};
                let free=size.saturating_sub(123);
                assert!(free<=5 && old%(1<<free)==0 && new%(1<<free)==0 && new>=old);
                if old==new {continue;}
                let controls=|value:usize| {
                    let mut c:Vec<_>=(free..word.len()).map(|i|(word[i],value>>i&1==0)).collect();
                    c.extend_from_slice(extra);c
                };
                mc_xor(b,&controls(old),flag,&[],&dirty);
                for (i,&q) in word.iter().enumerate() {
                    if (old^new)>>i&1!=0 {b.cx(flag,q);}
                }
                mc_xor(b,&controls(new),flag,&[],&dirty);
            }
            if wide {
                // On Q=Y care these 92 input codes have no high-Q payload.
                // HR remains below192 and DONE starts at1536. The output
                // interval is therefore empty until this move, and extra
                // is unchanged/disjoint throughout. Compute at the source,
                // translate, then erase at the destination: flag returns0
                // both on selected care and when extra is false.
                assert_eq!(word.len(),11);
                assert!(dirty.len()>=7);
                let query=|b:&mut B,lo,hi| {
                    for mut term in View::interval_terms(&word,lo,hi) {
                        term.extend_from_slice(extra);
                        mc_xor(b,&term,flag,&[],&dirty);
                    }
                };
                query(b,HT_OFFSET,HT_OFFSET+92);
                super::modp_frogdrop::add_const_exact(b,&word[5..11],Some(flag),15,&dirty);
                query(b,672,764);
            }
        }
    });
    b.no_rows=old_rows;out
}

/// Interchange the two active Middle phases, preserving size/high-Q and DONE.
fn flip_middle_phase(b:&mut B,fd:&Fd,active:QubitId,ht:QubitId,dirty:&[QubitId]) {
    let view=View::from_fd(fd,false);
    let mut occupied=view.ports();occupied.extend([active,ht]);
    assert_ne!(active,ht);assert!(!view.ports().contains(&active)&&!view.ports().contains(&ht));
    let dirty=bank(&occupied,dirty);
    let query=|b:&mut B,lo,hi,target| {
        for term in View::interval_terms(&view.high,lo,hi) {mc_xor(b,&term,target,&[],&dirty);}
    };
    query(b,0,42,active);query(b,21,42,ht);
    super::modp_frogdrop::add_const_exact(b,&view.high,Some(active),21,&dirty);
    let subtract=rec(b,|b|super::modp_frogdrop::add_const_exact(b,&view.high,Some(ht),42,&dirty));
    b.play(&subtract,true);
    query(b,21,42,ht);b.cx(active,ht);
    query(b,0,42,active);
}

/// Forward: PRE-map Boundary -> Middle. Reverse: Middle -> PRE-map Boundary.
/// Apply the reverse before the outer swap, while Q=Y on every active shot.
pub(crate) fn pre_map_record(b:&mut B,fd:&Fd,flags:[QubitId;2],dirty:&[QubitId])->Vec<G> {
    let old_rows=b.no_rows;b.no_rows=true;
    let out=rec(b,|b| {
        let cvt=boundary_to_middle_record(b,fd,flags[0],&[],dirty);
        b.play(&cvt,false);
        flip_middle_phase(b,fd,flags[0],flags[1],dirty);
    });
    b.no_rows=old_rows;out
}

/// Swap one logical Q lane with an arbitrary separate partner under `extra`.
/// For a high Q lane the free low packet bit is used only in its capacity
/// classes. All other classes have that logical bit and partner identically
/// zero on the selected outer-swap care domain. Controls never read the
/// low packet bit being swapped, so all source prefixes survive the swap.
#[allow(clippy::too_many_arguments)]
pub(crate) fn logical_lane_swap(b:&mut B,fd:&Fd,view:&BoundaryView,index:usize,
    partner:QubitId,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
    assert!(index<128 && !view.ports().contains(&partner));
    let mut occupied=view.ports();occupied.extend([partner]);
    occupied.extend(extra.iter().map(|&(q,_)|q));occupied.extend_from_slice(clean);
    if index<123 {
        occupied.push(fd.q[index]);let dirty=bank(&occupied,dirty);
        super::mid2::mc_swap(b,extra,fd.q[index],partner,clean,&dirty);return;
    }
    let bit=index-123;
    let lane=view.low[bit];
    assert!(extra.iter().all(|&(q,_)|q!=lane && q!=partner));
    assert!(clean.iter().all(|q|!view.ports().contains(q)&&*q!=partner));
    let dirty=bank(&occupied,dirty);
    let word=view.word();
    let mut terms=Vec::new();
    for (wide,lo,offset) in [(false,124+bit,0),(true,93+bit,HT_OFFSET)] {
        let start=BoundaryView::interval(lo,wide).0+offset;
        let (last,free)=BoundaryView::interval(128,wide);
        terms.extend(View::interval_terms(&word,start,offset+last+(1<<free)));
    }
    if bit<4 {terms.extend(View::interval_terms(&word,DONE_BASE,2048));}
    for mut term in terms {
        assert!(!term.iter().any(|&(q,_)|q==lane));
        let mut contradiction=false;
        for &(q,neg) in extra {
            match term.iter().find(|(p,_)|*p==q) {
                Some(&(_,old)) if old!=neg=>{contradiction=true;break;},
                Some(_)=>{},None=>term.push((q,neg)),
            }
        }
        if !contradiction {super::mid2::mc_swap(b,&term,lane,partner,clean,&dirty);}
    }
}

/// The parent's exact running SZ cut, with logical instead of physical Q.
/// `extra` is !C at stage2 and empty for the return swap before map.
#[allow(clippy::too_many_arguments)]
pub(crate) fn middle_swap(b:&mut B,fd:&Fd,view:&BoundaryView,sz:&[QubitId],h:usize,
    clo:usize,chi:usize,flag:QubitId,pre:&[QubitId],extra:&[(QubitId,bool)],dirty:&[QubitId]) {
    let n=fd.ring.len();let qlo=n-128;
    let mut occupied=view.ports();occupied.extend_from_slice(sz);occupied.push(flag);
    occupied.extend_from_slice(pre);occupied.extend(extra.iter().map(|&(q,_)|q));
    let dirty=bank(&occupied,dirty);
    for lane in chi.max(qlo)..n {
        logical_lane_swap(b,fd,view,n-1-lane,fd.ring[lane],extra,pre,&dirty);
    }
    let lo=clo.max(qlo);if lo>=chi{return;}
    ge_cd(b,sz,lo as isize+1-h as isize,flag,pre,&dirty);
    let mut dec=Dec::new(sz,pre);
    let at=|lane:usize|lane.checked_sub(h).filter(|&v|v<(1usize<<sz.len()));
    for lane in lo..chi {
        if lane>lo {if let Some(v)=at(lane) {let c=dec.ctrls(b,v);mc_xor(b,&c,flag,&[],&dirty);}}
        let mut controls=extra.to_vec();controls.push((flag,true));
        // Decoder prefixes are retained here, hence they are not clean
        // MCX helpers during the selected data-lane operation.
        logical_lane_swap(b,fd,view,n-1-lane,fd.ring[lane],&controls,&[],&dirty);
    }
    if let Some(v)=at(chi) {let c=dec.ctrls(b,v);mc_xor(b,&c,flag,&[],&dirty);}
    dec.clear(b);
}
