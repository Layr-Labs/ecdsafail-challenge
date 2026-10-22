//! Three ordinary clean digit owners: current e bit, original W sign, carry-in.
//! Size predicates and masked writes use literal reversible gates with dirty
//! donors. No raw size lane is borrowed, and no AND is measurement-uncomputed.
use super::{B, DigScr, Ph, QubitId, NP, KE, mc_xor};

type Lit = (QubitId, bool);

fn toggle(b: &mut B, controls: &[Lit], target: QubitId, dirty: &[QubitId]) {
    let mut ct = Vec::new();
    for &(q, neg) in controls {
        assert_ne!(q, target, "minimal3 control aliases target");
        if let Some(&(_, old)) = ct.iter().find(|&&(x, _)| x == q) {
            if old != neg { return; }
        } else { ct.push((q, neg)); }
    }
    let ds: Vec<_> = dirty.iter().copied().filter(|q| *q != target && !ct.iter().any(|(c,_)| c == q)).collect();
    assert!(ds.len() >= ct.len().saturating_sub(2));
    mc_xor(b, &ct, target, &[], &ds);
}

fn equal(v: &[QubitId], value: usize) -> Vec<Lit> {
    v.iter().enumerate().map(|(i,&q)| (q, (value >> i) & 1 == 0)).collect()
}

// Disjoint binary prefix cubes for an inclusive integer interval.
fn ranges(v: &[QubitId], lo: usize, hi: usize) -> Vec<Vec<Lit>> {
    let end = 1usize << v.len();
    if lo > hi || lo >= end { return vec![]; }
    let mut a = lo;
    let z = hi.min(end - 1);
    let mut out = Vec::new();
    while a <= z {
        let fit = (usize::BITS - 1 - (z-a+1).leading_zeros()) as usize;
        let skip = fit.min((a.trailing_zeros() as usize).min(v.len()));
        out.push(v.iter().enumerate().skip(skip)
            .map(|(i,&q)| (q, (a >> i) & 1 == 0)).collect());
        a += 1usize << skip;
    }
    out
}

fn swap(b: &mut B, ct: &[Lit], x: QubitId, y: QubitId, dirty: &[QubitId]) {
    assert_ne!(x,y);
    b.cx(y,x);
    let mut cc=ct.to_vec(); cc.push((x,false));
    // Both ports must stay outside the dirty decomposition, including x
    // while it contains x XOR y.
    let ds:Vec<_>=dirty.iter().copied().filter(|q|*q!=x&&*q!=y).collect();
    toggle(b,&cc,y,&ds);
    b.cx(y,x);
}

type Swaps = Vec<(QubitId,QubitId,QubitId)>;

// All current lane maps have a contiguous defined address interval. A pruned
// gather is an exact permutation for every raw address, even outside it; the
// separate interval predicate prevents an invalid address from using its root.
fn tree(reg:&[QubitId],range:(usize,usize),lane:&dyn Fn(usize)->Option<QubitId>)
        -> Option<(QubitId,(usize,usize),Swaps)> {
    let leaves:Vec<_>=(range.0..=range.1.min((1usize<<reg.len())-1))
        .filter_map(|v|lane(v).map(|q|(v,q))).collect();
    if leaves.is_empty() {return None;}
    assert!(leaves.windows(2).all(|w|w[1].0==w[0].0+1));
    let mut swaps=Vec::with_capacity(leaves.len()-1);
    let root=super::read_lane_tree::collect_tree(reg,&leaves,reg.len(),&mut swaps);
    Some((root,(leaves[0].0,leaves.last().unwrap().0),swaps))
}

fn play_tree(b:&mut B,swaps:&[(QubitId,QubitId,QubitId)],inverse:bool) {
    if inverse {
        for &(c,x,y) in swaps.iter().rev() {b.cswap(c,x,y);}
    } else {
        for &(c,x,y) in swaps {b.cswap(c,x,y);}
    }
}

// On acted digit states S=SZ+SY lies in [231,257]. Thus (S-228) mod256
// is an ordinary value in [3,29]. Transform the OTHER size's low eight lanes,
// leaving the complete queried address (including col0's ninth SZ bit) raw.
// TTK has no carry owner and restores its source: c0 may be an arbitrary MAJ
// carry here. The ninth size lane, if present, is untouched, not a zero pad.
// Every invocation has act among extra; inactive sizes need no domain promise.
fn sum_guard(b:&mut B,reg:&[QubitId],range:(usize,usize),other:&[QubitId],limit:usize,
             extra:&[Lit],target:QubitId,dirty:&[QubitId]) {
    if limit<228 || range.0>range.1 {return;}
    assert!((8..=9).contains(&reg.len()) && (8..=9).contains(&other.len()));
    assert!(reg.iter().all(|q|!other.contains(q)));
    assert!(limit<=258);
    let code=&other[..8];
    let transform=super::super::frogdrop_col::rec(b,|b| {
        super::super::arith::ttk_add(b,&reg[..8],code,None,None);
        let bias=super::super::frogdrop_col::rec(b,|b|
            super::super::frogdrop::add_const_dirty_exact(b,code,228,dirty));
        b.play(&bias,true);
    });
    b.play(&transform,false);
    for a in ranges(reg,range.0,range.1) {
        for z in ranges(code,0,limit-228) {
            let mut ct=a.clone();ct.extend(z);ct.extend_from_slice(extra);
            toggle(b,&ct,target,dirty);
        }
    }
    b.play(&transform,true);
}

fn read(b:&mut B,reg:&[QubitId],range:(usize,usize),lane:&dyn Fn(usize)->Option<QubitId>,
        neg:bool,extra:&[Lit],target:QubitId,dirty:&[QubitId]) {
    let Some((root,valid,swaps))=tree(reg,range,lane) else{return;};
    play_tree(b,&swaps,false);
    for mut ct in ranges(reg,valid.0,valid.1) {
        ct.extend_from_slice(extra);ct.push((root,neg));toggle(b,&ct,target,dirty);
    }
    play_tree(b,&swaps,true);
}

fn addressed_swap(b: &mut B, reg:&[QubitId], range:(usize,usize), other:&[QubitId],limit:usize,
                  lane:&dyn Fn(usize)->Option<QubitId>,e:QubitId,act:QubitId,c0:QubitId,dirty:&[QubitId]) {
    let Some((root,valid,swaps))=tree(reg,range,lane) else{return;};
    play_tree(b,&swaps,false);
    // Between complete ripples c0 is returned clean. The predicate depends
    // only on unchanged sizes/act, not on either swapped data port.
    let guard=super::super::frogdrop_col::rec(b,|b|
        sum_guard(b,reg,valid,other,limit,&[(act,false)],c0,dirty));
    b.play(&guard,false);b.cswap(c0,root,e);b.play(&guard,true);
    play_tree(b,&swaps,true);
}

// At the queried boundary the ORIGINAL source bit is zero on active shots.
// After MAJ, even when source[v+1] is live, carry(v+1)=target[v]&source[v-1].
// The v=0 boundary has clean carry-in and therefore zero carry.
fn query(b:&mut B,t:&[QubitId],s:&[QubitId],reg:&[QubitId],range:(usize,usize),other:&[QubitId],
         limit:usize,extra:&[Lit],e:QubitId,c0:QubitId,dirty:&[QubitId]) {
    if range.0==0 {sum_guard(b,reg,(0,0),other,limit,extra,e,dirty);}
    let valid=(range.0.max(1),range.1.min(t.len()-1));
    let Some((rt,valid,ts))=tree(reg,valid,&|v|t.get(v).copied()) else{return;};
    assert!(valid.1<=s.len());
    let (rs,svalid,ss)=tree(reg,valid,&|v|s.get(v-1).copied()).unwrap();
    assert_eq!(valid,svalid);
    play_tree(b,&ts,false);play_tree(b,&ss,false);
    let guard=super::super::frogdrop_col::rec(b,|b|
        sum_guard(b,reg,valid,other,limit,extra,c0,dirty));
    // c0 is DIRTY inside MAJ. C(d) F C(d) F with F:d^=predicate
    // gives e ^= predicate & !(rt&rs), independent of the original d.
    // Both selected ports and all size lanes are restored after each C/F;
    // only e changes. Return c0 before undoing either gather and MAJ.
    let body=|b:&mut B| {
        b.cx(c0,e);toggle(b,&[(c0,false),(rt,false),(rs,false)],e,dirty);
    };
    body(b);b.play(&guard,false);body(b);b.play(&guard,true);
    play_tree(b,&ss,true);play_tree(b,&ts,true);
}

// One final absent source cell is a literal zero, not a physical owner.
// Its MAJ would only write a discarded outgoing carry into that zero cell;
// skip it. Its sum cell is target[last] ^= gate & source[last-1].
fn ripple(b:&mut B,t:&[QubitId],s:&[QubitId],c0:QubitId,subtract:bool,
          mid:&mut dyn FnMut(&mut B),write:&mut dyn FnMut(&mut B,usize,QubitId,QubitId)) {
    assert!(!t.is_empty() && s.len()<=t.len() && t.len()-s.len()<=1);
    if subtract { for &q in t {b.x(q);} }
    for i in 0..s.len() {
        let x=if i==0{c0}else{s[i-1]};
        b.cx(s[i],t[i]);b.cx(s[i],x);b.ccx(x,t[i],s[i]);
    }
    mid(b);
    for i in (0..t.len()).rev() {
        let x=if i==0{c0}else{s[i-1]};
        if i<s.len() {
            b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);
            b.cx(s[i],x);write(b,i,x,t[i]);b.cx(s[i],x);
        } else { write(b,i,x,t[i]); }
    }
    if subtract { for &q in t {b.x(q);} }
}

fn masked_write(b:&mut B,reg:&[QubitId],range:(usize,usize),minimum:isize,
                e:QubitId,carry:QubitId,target:QubitId,dirty:&[QubitId]) {
    let lo=range.0.max(minimum.max(0) as usize);
    for mut ct in ranges(reg,lo,range.1) {
        ct.extend([(e,false),(carry,false)]);toggle(b,&ct,target,dirty);
    }
}

pub(super) fn digit(b:&mut B,p:&[QubitId],ph:&Ph,act:QubitId,sc:&DigScr,dirty:&[QubitId]) {
    assert_eq!(sc.e.len(),1);
    assert!(!sc.sa.contains(&act) && !sc.sb.contains(&act), "minimal3 act aliases raw size");
    let (e,sv,c0)=(sc.e[0],sc.sv,sc.c0);
    assert!(e!=sv&&e!=c0&&sv!=c0&&[e,sv,c0].iter().all(|q|!sc.sa.contains(q)&&!sc.sb.contains(q)&&*q!=act));
    assert_eq!(p.len(),NP);
    // Ordinary owners and size controls are never dirty donors, including
    // while c0 holds a sum predicate or a live MAJ carry.
    let bank:Vec<_>=dirty.iter().copied().filter(|q|![e,sv,c0,act].contains(q)
        &&!sc.sa.contains(q)&&!sc.sb.contains(q)).collect();
    let dirty=&bank[..];
    let (rlo,rhi)=ph.rr;let(tlo,thi)=ph.tr;
    for k in (0..KE).rev() {
        if rlo+tlo>257-k {continue;}
        let top=(k+rhi+1).min(NP);
        let tt=&p[k..top];let ss=&ph.src_r[..(top-k).min(ph.src_r.len())];
        let mut mid=|b:&mut B|query(b,tt,ss,&ph.rv,ph.rr,&ph.tv,257-k,&[(act,false)],e,c0,dirty);
        if ph.ht {
            ripple(b,tt,ss,c0,true,&mut mid,&mut |b,_,carry,target|b.ccx(e,carry,target));
        } else {
            assert!(ph.sz_mask);
            // sv is still clean: W's sign is read only after all forward
            // digits. Track e & [SZ>=i] by interval differences, then erase
            // the mask before e is parked. No source/target data is a control.
            let mut mask=super::Mask::new(&ph.rv,rhi,false,vec![(e,false)],sv,&[],dirty).with_lo(rlo);
            {
                let mut write=|b:&mut B,i:usize,carry:QubitId,target:QubitId| {
                    mask.goto(b,Some(i as isize));b.ccx(sv,carry,target);
                };
                ripple(b,tt,ss,c0,true,&mut mid,&mut write);
            }
            mask.goto(b,None);
        }
        let lane=|v:usize|p.get(v+k).copied();
        addressed_swap(b,&ph.rv,ph.rr,&ph.tv,257-k,&lane,e,act,c0,dirty);
    }
    let lane=|v:usize|NP.checked_sub(1+v).and_then(|i|p.get(i).copied());
    read(b,&ph.tv,ph.tr,&lane,false,&[(act,false)],sv,dirty);
    // Reflect exactly the inherited in-place e segment. The full raw-size
    // register is temporarily transformed to (SZ+SY-228) modulo its width; none of its
    // high bits is a helper. This is a literal reversible permutation off act.
    let dest:std::collections::BTreeSet<usize>=(0..31).collect();
    let rot=super::super::frogdrop_col::rec(b,|b|
        super::super::frogdrop::rot_by_range_care(b,p,&ph.rv,rlo,rhi,true,dirty,&dest));
    b.play(&rot,false);
    let code=super::super::frogdrop_col::rec(b,|b| {
        ripple(b,&sc.sa,&sc.sb,c0,false,&mut |_|{},
            &mut |b,_,carry,target|b.cx(carry,target));
        let bias=super::super::frogdrop_col::rec(b,|b|
            super::super::frogdrop::add_const_dirty_exact(b,&sc.sa,228,dirty));
        b.play(&bias,true);
    });
    b.play(&code,false);
    for sum in (rlo+tlo).max(228)..=(rhi+thi).min(257) {
        let len=258-sum;
        let mut ct=equal(&sc.sa,sum-228);ct.push((act,false));
        for i in 0..len/2 {swap(b,&ct,p[i],p[len-1-i],dirty);}
    }
    b.play(&code,true);b.play(&rot,true);
    for k in 0..KE {
        if rlo+tlo>257-k {continue;}
        let top=(k+thi+1).min(NP);
        let tt:Vec<_>=(k..top).map(|i|p[NP-1-i]).collect();
        let ss=&ph.src_t[..(top-k).min(ph.src_t.len())];
        let lane=|v:usize|NP.checked_sub(2+v+k).and_then(|i|p.get(i).copied());
        addressed_swap(b,&ph.tv,ph.tr,&ph.rv,257-k,&lane,e,act,c0,dirty);
        let mut write=|b:&mut B,i:usize,carry:QubitId,target:QubitId| {
            if ph.ht {
                assert!(ph.virt_m1);
                // Same margin-one write prefix as the inherited HT digit.
                masked_write(b,&ph.tv,ph.tr,i as isize,e,carry,target,dirty);
            } else {toggle(b,&[(e,false),(carry,false)],target,dirty);}
        };
        ripple(b,&tt,ss,c0,false,&mut |_|{},&mut write);
        let mut mid=|b:&mut B|query(b,&tt,ss,&ph.tv,ph.tr,&ph.rv,258-k,&[(act,false),(sv,true)],e,c0,dirty);
        ripple(b,&tt,ss,c0,true,&mut mid,&mut |_,_,_,_|{});
    }
    // Sign extension into the gap. Both comparisons are direct disjoint
    // prefix cubes, so there is no live mask flag or decoder owner.
    for l in rlo..NP.saturating_sub(1+tlo) {
        for a in ranges(&ph.rv,rlo,rhi.min(l)) {
            for z in ranges(&ph.tv,tlo,thi.min(NP-2-l)) {
                let mut ct=a.clone();ct.extend(z);ct.extend([(act,false),(sv,false)]);
                toggle(b,&ct,p[l],dirty);
            }
        }
    }
    for l in rlo+1..NP {
        if l>rhi {b.cx(act,p[l]);}
        else {for mut ct in ranges(&ph.rv,rlo,l-1) {ct.push((act,false));toggle(b,&ct,p[l],dirty);}}
    }
    let lane=|v:usize|p.get(v).copied();
    read(b,&ph.rv,ph.rr,&lane,false,&[(act,false)],sv,dirty);
}
