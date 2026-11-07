//! Source-only three-owner digit ABI. No borrowed phase is assumed clean:
//! HR first removes the adjacent shuttle and uses virtual_boundary_divide;
//! only then is PH the unchanged original phase throughout this module.

use super::{B, DigScr, QubitId, mc_xor};
use super::super::frogdrop_col::{Fd, ColPar, rec};
use std::cell::Cell;

pub(super) fn enabled() -> bool {
    std::env::var("C660_THREE_ROLE_DIGIT").as_deref() == Ok("1")
}

/// The original activity is a function of metadata, never of the target
/// act being narrowed. The low word not belonging to the current raw view
/// temporarily holds S-226, leaving that complete raw view unchanged.
pub(super) struct Policy<'a> {
    pub fd: &'a Fd,
    pub cp: &'a ColPar,
    pub z_view: &'a Cell<bool>,
    pub raw_z: Vec<QubitId>,
    pub ht: bool,
}

fn interval(bits: &[QubitId], lo: usize, hi: usize) -> Vec<Vec<(QubitId,bool)>> {
    if lo > hi || lo >= (1usize << bits.len()) { return vec![]; }
    let end = (hi + 1).min(1usize << bits.len());
    let mut at = lo;
    let mut out = Vec::new();
    while at < end {
        let align = if at == 0 { bits.len() } else { (at.trailing_zeros() as usize).min(bits.len()) };
        let fit = (usize::BITS - 1 - (end-at).leading_zeros()) as usize;
        let low = align.min(fit);
        out.push((low..bits.len()).map(|i| (bits[i], (at >> i) & 1 == 0)).collect());
        at += 1usize << low;
    }
    out
}

impl Policy<'_> {
    /// act ^= A(original metadata) & [S>lim]. This involution narrows
    /// A to A&[S<=lim] on entry, then restores A after a complete epoch.
    /// g is returned before arithmetic, including when e and sign are live.
    pub(super) fn narrow(&self, b: &mut B, sc: &DigScr, act: QubitId, lim: isize) {
        assert_eq!(sc.fa, act);
        assert_eq!(self.raw_z.len(), 8);
        assert_eq!(self.cp.l0, 128, "activity formulas retain the original switching boundary");
        assert!(![sc.e[0],sc.sv,sc.g,self.fd.ph].contains(&act));
        let z = self.z_view.get();
        let raw = if z { self.raw_z.as_slice() } else { self.fd.sy.as_slice() };
        let dst = if z { &sc.sb[..5] } else { sc.sa.as_slice() };
        let src = if z { sc.sa.as_slice() } else { &sc.sb[..5] };
        assert!(!raw.iter().any(|q| dst.contains(q)));
        let dirty: Vec<_> = sc.dirty.iter().copied().filter(|q|
            !self.fd.q.contains(q) && !raw.contains(q) && !dst.contains(q)
            && ![act,sc.e[0],sc.sv,sc.g,self.fd.ph].contains(q)).collect();
        assert!(dirty.len() >= 16);
        let code = rec(b, |b| {
            super::super::arith::ttk_add(b, src, dst, None, None);
            let sub = rec(b, |b| super::super::frogdrop::add_const_dirty_exact(b,dst,2,&dirty));
            b.play(&sub,true);
        });
        let done = self.ht && self.cp.dn;
        if self.cp.dn {
            assert!([sc.e[0],sc.sv,sc.g,act].iter().all(|q| !self.fd.q.contains(q)));
        }
        if done {
            super::super::frogdrop_col::mc_xor_dn(b,&[],sc.g,&[],&dirty,self.fd,self.cp.l0,true);
        }
        b.play(&code,false);
        let mut base = vec![(self.fd.ph,!self.ht)];
        if done { base.push((sc.g,true)); }
        let first = (lim + 1).max(226) as usize;
        if first <= 257 {
            // Most columns need only one five-bit interval. Switching/DQ
            // columns retain the exact source size condition, on either
            // shared raw view, with no inferred inactive-size assumption.
            let simple = if self.ht { !self.cp.dq } else { !self.cp.sw };
            if !simple { assert!(self.cp.sz.1 < 256,
                "raw-eight-bit switching predicates exclude the column-zero wide endpoint"); }
            if simple {
                for mut c in interval(dst,first-226,31) {
                    c.extend_from_slice(&base); mc_xor(b,&c,act,&[],&dirty);
                }
            } else {
                for sum in first..=257 {
                    let (lo,hi) = if self.ht {
                        // DQ: Z>=Y. Here raw is Z or Y respectively.
                        if z { ((sum+1)/2,255) } else { (0,sum/2) }
                    } else if self.cp.dl {
                        // w=!PH & Z<=128 & Z<=Y. S<=257 makes Z<=128
                        // redundant in Z<=Y; HR is therefore Z>Y.
                        if z { (sum/2+1,255) } else { (0,(sum-1)/2) }
                    } else {
                        // Ordinary switching HR requires Z>=129.
                        if z { (129,255) } else { (0,sum-129) }
                    };
                    let eq: Vec<_> = dst.iter().enumerate()
                        .map(|(i,&q)|(q,((sum-226)>>i)&1==0)).collect();
                    for mut c in interval(raw,lo,hi) {
                        c.extend_from_slice(&eq); c.extend_from_slice(&base);
                        mc_xor(b,&c,act,&[],&dirty);
                    }
                }
            }
        }
        b.play(&code,true);
        if done {
            super::super::frogdrop_col::mc_xor_dn(b,&[],sc.g,&[],&dirty,self.fd,self.cp.l0,true);
        }
    }
}

/// HR division with s[R] a virtual zero, while the physical lane may carry
/// an unrelated in-place quotient bit. No adjacent-save owner is used.
/// After undoing cell i, x is carry_i and t[i] is original complemented d_i.
/// At i=R the virtual zero gives carry_(R+1)=t[i]&x. Decide e there, write
/// that boundary with e*x, and write lower cells by the unchanged UMA rule.
/// Higher cells are restored without writes. Off-act e stays zero and the
/// full ladder restores arbitrary phase, source, and target data exactly.
#[allow(clippy::too_many_arguments)]
pub(super) fn virtual_boundary_divide(b:&mut B,t:&[QubitId],s:&[QubitId],carry:QubitId,
    reg:&[QubitId],lo:usize,hi:usize,enable:QubitId,e:QubitId,g:QubitId,tmp:QubitId,dirty:&[QubitId]) {
    assert_eq!(t.len(),s.len());
    let mut occupied=std::collections::BTreeSet::new();
    assert!(t.iter().chain(s).chain(reg).chain([&carry,&enable,&e,&g,&tmp])
        .all(|q| occupied.insert(q.0)), "virtual boundary ports must be disjoint");
    assert!(lo>=1 && hi<256 && reg.len()==8);
    assert!(![carry,enable,e,g,tmp].iter().enumerate().any(|(i,q)|[carry,enable,e,g,tmp][..i].contains(q)));
    assert!(!t.contains(&tmp)&&!s.contains(&tmp)&&!reg.contains(&tmp));
    let donors:Vec<_>=dirty.iter().copied().filter(|q| !t.contains(q)&&!s.contains(q)
        &&!reg.contains(q)&&![carry,enable,e,g,tmp].contains(q)).collect();
    assert!(donors.len()>=16);
    for &q in t {b.x(q);}
    for i in 0..t.len() {
        let x=if i==0 {carry} else {s[i-1]};
        b.cx(s[i],t[i]); b.cx(s[i],x); b.ccx(x,t[i],s[i]);
    }
    // Sign has not been read yet: sv is one returned, globally clean
    // conjunction temp at each query/mask toggle, never a held prefix.
    let temps=[tmp];
    let mut mask=super::Mask::new(reg,hi,false,vec![(e,false)],g,&temps,&donors).with_lo(lo);
    for i in (0..t.len()).rev() {
        let x=if i==0 {carry} else {s[i-1]};
        b.ccx(x,t[i],s[i]); b.cx(s[i],x); b.cx(s[i],t[i]);
        if (lo..=hi).contains(&i) {
            let eq:Vec<_>=reg.iter().enumerate().map(|(k,&q)|(q,(i>>k)&1==0)).collect();
            let mut c=eq.clone(); c.push((enable,false));
            mc_xor(b,&c,e,&temps,&donors);
            c.extend([(t[i],false),(x,false)]); mc_xor(b,&c,e,&temps,&donors);
            let mut boundary=eq; boundary.extend([(e,false),(x,false)]);
            mc_xor(b,&boundary,t[i],&temps,&donors);
        }
        // g=e & [R>=i+1], strictly below the virtual boundary. At the
        // moment e changes (i=R), this predicate remains zero, so the
        // incremental Mask state remains valid without an extra reset.
        mask.goto(b,Some((i+1) as isize));
        b.cx(s[i],x); b.ccx(g,x,t[i]); b.cx(s[i],x);
    }
    mask.goto(b,None);
    for &q in t {b.x(q);}
}
