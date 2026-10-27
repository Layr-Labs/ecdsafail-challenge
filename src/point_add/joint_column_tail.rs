//! Joint outside packet: the complete switching/DQ tail with one retained
//! C=W|D tag. Source integration only; no new physical owner is allocated.

use super::super::builder::{B,G};
use super::super::frogdrop_col::{Fd,ColPar,ColScr,map_done_flag};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn record(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}

/// XOR C & (lo<=word<hi). The dyadic cubes are disjoint, including on
/// arbitrary off-C data; no clean prefix or cut flag is required.
fn range(b:&mut B,word:&[QubitId],mut lo:usize,hi:usize,c:QubitId,
    target:QubitId,dirty:&[QubitId]) {
    assert!(lo<=hi && hi<=1usize<<word.len());
    while lo<hi {
        let aligned=if lo==0 {word.len()}else{lo.trailing_zeros() as usize};
        let remaining=(usize::BITS-1-(hi-lo).leading_zeros()) as usize;
        let free=aligned.min(remaining).min(word.len());
        let mut ctl=vec![(c,false)];
        ctl.extend((free..word.len()).map(|i|(word[i],lo>>i&1==0)));
        mc_xor(b,&ctl,target,&[],dirty);
        lo+=1usize<<free;
    }
}

/// Priority probe under C and lane<cut_a-value(cut). Output is size-base,
/// where base=0 gives raw size, base=1 gives positive size-minus1. Only tmp
/// is globally clean; out may be arbitrary on C=0 shots. Every source and
/// cut is unchanged, and each complete input/output predicate returns tmp.
fn probe(b:&mut B,source:&[QubitId],limit:usize,cut:&[QubitId],cut_a:usize,
    out:&[QubitId],base:usize,c:QubitId,tmp:QubitId,dirty:&[QubitId]) {
    assert!(limit<=source.len() && base<=1 && limit-base<1usize<<out.len());
    for lane in (0..limit).rev() {
        let value=lane+1-base;
        let end=cut_a.saturating_sub(lane).min(1usize<<cut.len());
        let mut at=0usize;
        while at<end {
            let aligned=if at==0 {cut.len()}else{at.trailing_zeros() as usize};
            let remaining=(usize::BITS-1-(end-at).leading_zeros()) as usize;
            let free=aligned.min(remaining).min(cut.len());
            for pass in 0..2 {
                let v=if pass==0 {0}else{value};
                let mut ctl=vec![(c,false),(source[lane],false)];
                ctl.extend((free..cut.len()).map(|i|(cut[i],at>>i&1==0)));
                ctl.extend(out.iter().enumerate().map(|(i,&q)|(q,v>>i&1==0)));
                mc_xor(b,&ctl,tmp,&[],dirty);
                if pass==0 {for(i,&q)in out.iter().enumerate(){if value>>i&1!=0{b.cx(tmp,q);}}}
            }
            at+=1usize<<free;
        }
    }
}

/// Input is the ordinary outside boundary code immediately after the map.
/// On C=pool0, the map bridge has ALREADY changed raw PH from0 to1 before
/// encoding: Q=t_j, top=r_j (or delayed top=t_j), so the wide HT packet is
/// the correct transient class. All SX owners are zero here.
///
/// Output on C: the original tail's ring/Q layout, PH=1, packet size equal
/// to bl(bottom t_j), and C retained on SX3. This tagged size deliberately
/// replaces the possibly >128 top size. The next column must copy it into
/// raw SZ, skip the first swap, refill SY from Q, and erase C by its inherited
/// first-HT/DQ js predicate. Other shots retain their complete packet/data.
pub(crate) fn apply(b:&mut B,fd:&Fd,cp:&ColPar,sc:&ColScr) {
    assert!(super::super::frogdrop_col::c660_joint_size());
    assert!(cp.sw && fd.sy.len()==5 && fd.sx.len()==7 && fd.q.len()==128);
    assert_eq!(cp.n,257);
    let c=sc.sz[0];
    let raw_sy:Vec<_>=fd.sy.iter().chain(fd.sx[..3].iter()).copied().collect();
    let(done,branch,case,helper)=(fd.sx[3],fd.sx[4],fd.sx[5],fd.sx[6]);
    let mut ports:BTreeSet<_>=raw_sy.iter().chain(fd.q.iter()).chain(fd.sx.iter())
        .chain(fd.ring.iter()).chain(sc.sz[..4].iter()).copied().collect();
    ports.insert(fd.ph);
    let mut seen=BTreeSet::new();
    let dirty:Vec<_>=sc.dirty.iter().copied().filter(|q|!ports.contains(q)&&seen.insert(*q)).collect();
    let code=super::super::joint_prefix::boundary_record(b,&raw_sy,&fd.q[123..128],fd.ph,
        done,branch,case,helper,&dirty,false);
    b.play(&code,true);
    for i in 0..3 {b.swap(fd.sx[i],fd.q[125+i]);}
    let relocate=|q:QubitId|->QubitId {
        if let Some(i)=fd.q[125..128].iter().position(|&p|p==q){fd.sx[i]}else{q}
    };
    let raw=Fd{ring:fd.ring.clone(),q:fd.q[..125].iter().copied().chain(fd.sx[..3].iter().copied()).collect(),
        sy:fd.sy.iter().copied().chain(fd.q[125..128].iter().copied()).collect(),
        sx:fd.sx.clone(),ph:fd.ph,cnt:fd.cnt.iter().copied().map(relocate).collect()};
    map_done_flag(b,&raw,cp,done,&dirty);
    let sy=&raw.sy;
    let tmp=sy[7];
    let u:Vec<_>=sc.sz[1..4].iter().copied().chain(fd.sx[3..7].iter().copied()).chain([fd.ph]).collect();
    assert_eq!(u.len(),8);
    let owned:Vec<_>=u.iter().chain(sy).chain(raw.q.iter()).chain(raw.ring.iter()).copied().chain([c]).collect();
    assert_eq!(owned.iter().collect::<BTreeSet<_>>().len(),owned.len());
    let inc=record(b,|b|super::super::modp_frogdrop::inc_dirty_free(b,sy,&dirty));
    b.play(&inc,true); // SY>=1, SY<=128: tmp is globally zero.
    b.cx(c,fd.ph);     // PH=0 on C; U is conditionally all-zero.
    let n=raw.ring.len();
    let rev:Vec<_>=raw.ring.iter().rev().copied().collect();
    let ylo=cp.sz.0.min(cp.sy.0).max(1);
    let umax=(cp.l0+cp.qb+1).min(n-ylo);
    assert!(umax<256 && cp.swl.1<=raw.q.len());
    // U=old bottom size (r_prev for W, r_next for D). The same bound is
    // already used by the parent's overlap-safe bottom/Q swap.
    let p1=record(b,|b|probe(b,&raw.ring,umax,&sy[..7],n-1,&u,0,c,tmp,&dirty));
    b.play(&p1,false);
    let p2=record(b,|b|probe(b,&rev,cp.l0,&u,n,&sy[..7],1,c,tmp,&dirty));
    b.play(&p2,true);
    for l in 0..n/2 {b.cswap(c,raw.ring[l],raw.ring[n-1-l]);}
    // SYlow7 is now zero on C but remains arbitrary data off C. Keep it
    // untouched while a globally clean SY7 walks the exact old swap mask.
    let lmin=(n-umax).min(cp.swl.1);
    for l in 0..lmin {b.cswap(c,raw.ring[l],raw.q[l]);}
    if lmin<cp.swl.1 {
        range(b,&u,0,n-cp.swl.1+1,c,tmp,&dirty);
        for l in (lmin..cp.swl.1).rev() {
            b.cswap(tmp,raw.ring[l],raw.q[l]);
            if l>lmin {range(b,&u,n-l,n-l+1,c,tmp,&dirty);}
        }
        range(b,&u,0,n-lmin,c,tmp,&dirty);
    }
    // Both tagged classes now have bottom t_j, Q=r_j. Retain its size,
    // rather than the first-HT top r_prev which can exceed128.
    let pm=record(b,|b|probe(b,&raw.ring,cp.m.min(128),&u,n,&sy[..7],1,c,tmp,&dirty));
    b.play(&pm,false);
    let pu=record(b,|b|probe(b,&rev,umax,&sy[..7],n-1,&u,0,c,tmp,&dirty));
    b.play(&pu,true);
    b.cx(c,fd.ph); // U[7] returned; restore the early HT phase.
    b.play(&inc,false);
    map_done_flag(b,&raw,cp,done,&dirty);
    for i in 0..3 {b.swap(fd.sx[i],fd.q[125+i]);}
    b.play(&code,false);
    // Codec helpers are returned. Preserve the sole first-HT/DQ tag for
    // the next column; the pool owner is available to stage15 afterwards.
    b.cx(c,fd.sx[3]);b.cx(fd.sx[3],c);
}
