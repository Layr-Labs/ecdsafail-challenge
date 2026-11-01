use super::builder::{B, G, ONE};
use super::lilypad::{ParityCtl,PWalk,PSched};
use crate::circuit::{QubitId,BitId};
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum PL { C(bool), Q(QubitId) }
pub(super) fn lq_fold(b: &mut B, p: &ParityCtl) -> PL {
    if p.qs.is_empty() {
        return PL::C(p.flip);
    }
    for &q in &p.qs[1..] {
        b.cx(q, p.qs[0]);
    }
    if p.flip {
        b.x(p.qs[0]);
    }
    PL::Q(p.qs[0])
}

pub(super) fn lq_unfold(b: &mut B, p: &ParityCtl) {
    if p.qs.is_empty() {
        return;
    }
    if p.flip {
        b.x(p.qs[0]);
    }
    for &q in p.qs[1..].iter().rev() {
        b.cx(q, p.qs[0]);
    }
}

/// Low-lane literals of the value rings in frame `frame`: lanes 1..3 of G and F (lane 0 is the constant `l0`).
/// At frames with kv = 3 the stored values are three-lane signed numbers, so lane 3 is the sign extension of lane 2.
/// What a mod-2^r page formula returns: bit of V, or bit of V ^ U.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) enum LqKind {
    V,
    D,
}

/// V = (G U + sp) F^-1 mod 2^r for odd F.
pub(super) fn lq_ref_v(r: usize, g: u64, f: u64, u: u64, rho: bool) -> u64 {
    let m = (1u64 << r) - 1;
    let p = super::frogdrop_sched::p().as_limbs()[0] & m;
    let sp = if rho { p.wrapping_neg() & m } else { p };
    assert!(f & 1 == 1);
    let mut inv = 1u64;
    for _ in 0..8 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(f.wrapping_mul(inv))) & m;
    }
    assert_eq!(f.wrapping_mul(inv) & m, 1);
    g.wrapping_mul(u).wrapping_add(sp).wrapping_mul(inv) & m
}

/// ANF over the distinct lanes of `shape` (3r + 1 slots g0.., f0.., u0.., rho: -1 = constant 0, -2 = constant 1,
/// k >= 0 = distinct lane k), generated from the exact truth table of every assignment.
fn lq_anf_r(r: usize, kind: LqKind, bit: usize, shape: &[i16]) -> std::rc::Rc<Vec<u32>> {
    type Key = (usize, LqKind, usize, Vec<i16>);
    thread_local! {
        static CACHE: std::cell::RefCell<std::collections::HashMap<Key, std::rc::Rc<Vec<u32>>>> =
            std::cell::RefCell::new(std::collections::HashMap::new());
    }
    let key = (r, kind, bit, shape.to_vec());
    if let Some(v) = CACHE.with(|c| c.borrow().get(&key).cloned()) {
        return v;
    }
    assert_eq!(shape.len(), 3 * r + 1);
    assert_eq!(shape[r], -2, "F must be odd: f0 is the constant 1");
    let nv = shape.iter().filter(|&&s| s >= 0).map(|&s| s as usize + 1).max().unwrap_or(0);
    assert!(nv <= 20);
    let mut tt = vec![0u8; 1 << nv];
    for a in 0..1usize << nv {
        let v = |k: usize| -> u64 {
            match shape[k] {
                -1 => 0,
                -2 => 1,
                s => ((a >> s) & 1) as u64,
            }
        };
        let word = |o: usize| (0..r).map(|i| v(o + i) << i).sum::<u64>();
        let (g, f, u, rho) = (word(0), word(r), word(2 * r), v(3 * r) == 1);
        let mut x = lq_ref_v(r, g, f, u, rho);
        if kind == LqKind::D {
            x ^= u;
        }
        tt[a] = ((x >> bit) & 1) as u8;
    }
    for k in 0..nv {
        for m in 0..1usize << nv {
            if m & (1 << k) != 0 {
                tt[m] ^= tt[m ^ (1 << k)];
            }
        }
    }
    let res = std::rc::Rc::new((0..1usize << nv).filter(|&m| tt[m] != 0).map(|m| m as u32).collect::<Vec<_>>());
    CACHE.with(|c| c.borrow_mut().insert(key, res.clone()));
    res
}

/// target ^= [ctl] & (bit `bit` of the page formula `kind`) from the literals of the low r lanes of G, F, U and of
/// rho, by its ANF with the codebase's dirty multi-controlled toggles (`dirty` borrowed and restored).
#[allow(clippy::too_many_arguments)]
pub(super) fn lq_vr_xor(
    b: &mut B,
    r: usize,
    kind: LqKind,
    bit: usize,
    g: &[PL],
    f: &[PL],
    u: &[PL],
    rho: PL,
    ctl: Option<QubitId>,
    target: QubitId,
    dirty: &[QubitId],
) {
    assert!(g.len() == r && f.len() == r && u.len() == r);
    let slots: Vec<PL> = g.iter().chain(f).chain(u).copied().chain([rho]).collect();
    let mut lanes: Vec<QubitId> = vec![];
    let shape: Vec<i16> = slots
        .iter()
        .map(|l| match *l {
            PL::C(false) => -1,
            PL::C(true) => -2,
            PL::Q(q) => {
                let i = lanes.iter().position(|&x| x == q).unwrap_or_else(|| {
                    lanes.push(q);
                    lanes.len() - 1
                });
                i as i16
            }
        })
        .collect();
    let anf = lq_anf_r(r, kind, bit, &shape);
    assert!(!lanes.contains(&target) && ctl.map_or(true, |c| c != target && !lanes.contains(&c)));
    let dirty: Vec<QubitId> =
        dirty.iter().copied().filter(|q| *q != target && !lanes.contains(q) && Some(*q) != ctl).collect();
    for &m in anf.iter() {
        let mut controls: Vec<(QubitId, bool)> = ctl.into_iter().map(|c| (c, false)).collect();
        controls.extend((0..lanes.len()).filter(|k| m & (1 << k) != 0).map(|k| (lanes[k], false)));
        super::mask::mc_xor(b, &controls, target, &[], &dirty);
    }
}

/// mc_xor with the virtual ONE control dropped; `dirty` filtered against the gate's own lanes.
fn lq_mcx(b: &mut B, ctls: &[QubitId], target: QubitId, dirty: &[QubitId]) {
    let lits: Vec<(QubitId, bool)> = ctls.iter().copied().filter(|&q| q != ONE).map(|q| (q, false)).collect();
    let dirty: Vec<QubitId> =
        dirty.iter().copied().filter(|q| *q != target && !lits.iter().any(|l| l.0 == *q)).collect();
    let clean:Vec<_>=b.low_clean.iter().copied().filter(|q|*q!=target&&!lits.iter().any(|l|l.0==*q)).collect();
    let dirty:Vec<_>=dirty.into_iter().filter(|q|!clean.contains(q)).collect();
    super::mask::mc_xor(b, &lits, target, &clean, &dirty);
}

/// t += [AND ctls] a (mod 2^n), a restored: the TTK ripple runs uncontrolled and only its writes into t carry the
/// controls (ctls empty: the plain TTK adder).
fn lq_ttk_add_ctl_base(b: &mut B, a: &[QubitId], t: &[QubitId], ctls: &[QubitId], dirty: &[QubitId]) {
    // A sign-extended source can repeat its sign owner. Do not run the
    // in-place source carry ladder through repeated physical positions.
    let mut coeff:std::collections::BTreeMap<u64,u64>=std::collections::BTreeMap::new();
    for(i,q)in a.iter().enumerate(){*coeff.entry(q.0).or_default()+=1u64<<i;}
    if coeff.len()<a.len(){
        for(q,k)in coeff {let mut ctl=ctls.to_vec();ctl.push(QubitId(q));lq_add_const(b,t,k,&ctl,dirty);}
        return;
    }
    let n = t.len();
    assert_eq!(a.len(), n);
    let wr = |b: &mut B, i: usize| {
        let mut c = ctls.to_vec();
        c.push(a[i]);
        lq_mcx(b, &c, t[i], dirty);
    };
    if n == 1 {
        wr(b, 0);
        return;
    }
    for i in 1..n {
        b.cx(a[i], t[i]);
    }
    for i in (1..n - 1).rev() {
        b.cx(a[i], a[i + 1]);
    }
    for i in 0..n - 1 {
        b.ccx(t[i], a[i], a[i + 1]);
    }
    for i in (1..n).rev() {
        wr(b, i);
        b.ccx(t[i - 1], a[i - 1], a[i]);
    }
    for i in 1..n - 1 {
        b.cx(a[i], a[i + 1]);
    }
    wr(b, 0);
    for i in 1..n {
        b.cx(a[i], t[i]);
    }
}

/// q <- q (1 + 2 a) mod 2^m under [AND ctls]; `a` (at least m - 1 lanes) restored.
pub(super) fn lq_mul_odd(b: &mut B, a: &[QubitId], q: &[QubitId], ctls: &[QubitId], dirty: &[QubitId]) {
    let m = q.len();
    for i in (0..m.saturating_sub(1)).rev() {
        let target = &q[i + 1..];
        let mut c = ctls.to_vec();
        c.push(q[i]);
        lq_ttk_add_ctl(b, &a[..target.len()], target, &c, dirty);
    }
}

/// q += [AND ctls] k (mod 2^m), by multi-controlled increments.
fn lq_add_const_base(b: &mut B, q: &[QubitId], k: u64, ctls: &[QubitId], dirty: &[QubitId]) {
    fn mc_cost(n:usize,clean:usize)->usize{match n{0|1=>0,2=>1,_=>{let h=clean.min(n-2);let rem=n-h;h+if rem==2{1}else{4*(rem-2)}}}}
    fn plan(i:usize,n:usize,k:u64,c:usize,cl:usize)->(usize,Vec<(usize,bool)>){
        if i==n{return(0,vec![]);}
        if k&1==0{return plan(i+1,n,k>>1,c,cl);}
        let cost:usize=(0..n-i).map(|j|mc_cost(c+j,cl)).sum();
        let(mut ca,mut a)=plan(i+1,n,k>>1,c,cl);ca+=cost;a.push((i,false));
        let(mut cb,mut bb)=plan(i+1,n,(k+1)>>1,c,cl);cb+=cost;bb.push((i,true));
        if cb<ca{(cb,bb)}else{(ca,a)}
    }
    let(_,digits)=plan(0,q.len(),k&((1u64<<q.len())-1),ctls.len(),b.low_clean.len());
    for(j,neg)in digits {
        let word=&q[j..];b.begin();
        for i in (1..word.len()).rev(){let mut c=ctls.to_vec();c.extend(&word[..i]);lq_mcx(b,&c,word[i],dirty);}
        lq_mcx(b,ctls,word[0],dirty);let step=b.end();b.play(&step,neg);
    }
}

/// ((sp - 1) / 2 mod 2^(r-1)) for rho = 0 and rho = 1.
fn lq_half_consts(r: usize) -> (u64, u64) {
    let m = (1u64 << r) - 1;
    let p = super::frogdrop_sched::p().as_limbs()[0] & m;
    let (s0, s1) = (p, p.wrapping_neg() & m);
    assert!(s0 & 1 == 1 && s1 & 1 == 1);
    ((s0 - 1) >> 1, (s1 - 1) >> 1)
}

/// In place under [AND ctls]: q = U_hi (U = 2 U_hi, U0 = 0, n = r - 1 lanes) becomes V_hi, where
/// V = 2 V_hi + 1 = (G U + sp) F^-1 mod 2^r: X_hi = G U_hi + (sp - 1)/2 and V_hi = (X_hi - F_hi) F^-1 (mod 2^n).
/// `g` = G lanes 1..n-1 and `f` = F lanes 1..n (G, F odd); every other lane is restored.
pub(super) fn lq_codec_hi(b: &mut B, q: &[QubitId], g: &[QubitId], f: &[QubitId], rho: PL, ctls: &[QubitId], dirty: &[QubitId]) {
    let n = q.len();
    assert!(n >= 2 && g.len() >= n - 1 && f.len() >= n);
    lq_mul_odd(b, g, q, ctls, dirty);
    lq_codec_offset(b,q,f,rho,ctls,dirty);
    b.begin();
    lq_mul_odd(b, f, q, ctls, dirty);
    let mf = b.end();
    b.play(&mf, true);
}

/// Clean h (n = r - 1 lanes) <- V_hi for an even G (post-step state): V = 2 V_hi + 1 = (G U + sp) F^-1 mod 2^r, so
/// X_hi = (G/2) U + (sp - 1)/2 and V_hi = (X_hi - F_hi) F^-1 (mod 2^n). `gh` = G lanes 1..n, `u` = U lanes
/// 0..n-1, `f` = F lanes 1..n; every other lane is restored. Undo by playing it reversed.
///
/// With `g1_one`, G' = 2 (mod 4) and `gh` = G lanes 2..n: (G/2) U = U + 2 (G/4) U.
#[allow(clippy::too_many_arguments)]
pub(super) fn lq_oracle_even(b: &mut B, h: &[QubitId], gh: &[QubitId], u: &[QubitId], f: &[QubitId], rho: PL, dirty: &[QubitId], g1_one: bool) {
    let n = h.len();
    assert!(n >= 2 && gh.len() + usize::from(g1_one) >= n && u.len() >= n && f.len() >= n);
    let (c0, c1) = lq_half_consts(n + 1);
    for j in 0..n {
        let (b0, b1) = ((c0 >> j) & 1 == 1, (c1 >> j) & 1 == 1);
        match rho {
            PL::C(v) => {
                if if v { b1 } else { b0 } {
                    b.x(h[j]);
                }
            }
            PL::Q(rq) => {
                if b0 {
                    b.x(h[j]);
                }
                if b0 != b1 {
                    b.cx(rq, h[j]);
                }
            }
        }
    }
    if g1_one {
        lq_ttk_add_ctl(b, &u[..n], h, &[], dirty);
        for i in 0..n - 1 {
            let target = &h[i + 1..];
            lq_ttk_add_ctl(b, &gh[..target.len()], target, &[u[i]], dirty);
        }
    } else {
        for i in 0..n {
            let target = &h[i..];
            lq_ttk_add_ctl(b, &gh[..target.len()], target, &[u[i]], dirty);
        }
    }
    for &x in h {
        b.x(x);
    }
    lq_ttk_add_ctl(b, &f[..n], h, &[], dirty);
    for &x in h {
        b.x(x);
    }
    b.begin();
    lq_mul_odd(b, f, h, &[], dirty);
    let mf = b.end();
    b.play(&mf, true);
}
#[cfg(test)]
#[path="tests_lq851.rs"]
mod tests_lq851;

#[cfg(test)]
fn page_xor_sign(b: &mut B, target: &[QubitId], negs: &[QubitId], inv: bool) {
    for &q in target {
        for &n in negs { b.cx(n, q); }
        if inv { b.x(q); }
    }
}

#[cfg(test)]
fn ttk_add_hooked_t0s(b: &mut B, a: &[QubitId], t1: &[QubitId], s_lanes: &[QubitId], s_inv: bool, hooks: &[(usize, BitId)]) {
    let n = t1.len() + 1;
    assert_eq!(a.len(), n);
    assert!(n >= 3 && !s_lanes.is_empty());
    let t = |i: usize| t1[i - 1];
    let c1 = |b: &mut B| {
        for &q in &s_lanes[1..] {
            b.cx(q, s_lanes[0]);
        }
        b.ccx(s_lanes[0], a[0], a[1]);
        if s_inv {
            b.cx(a[0], a[1]);
        }
        for &q in s_lanes[1..].iter().rev() {
            b.cx(q, s_lanes[0]);
        }
    };
    for &(i, m) in hooks {
        assert!(i >= 1 && i < n, "carry hook {i} outside 1..{n}");
        b.z_if(a[i], m);
    }
    for i in 1..n {
        b.cx(a[i], t(i));
    }
    for i in (1..n - 1).rev() {
        b.cx(a[i], a[i + 1]);
    }
    c1(b);
    for i in 1..n - 1 {
        b.ccx(t(i), a[i], a[i + 1]);
    }
    for &(i, m) in hooks {
        b.z_if(a[i], m);
    }
    for i in (2..n).rev() {
        b.cx(a[i], t(i));
        b.ccx(t(i - 1), a[i - 1], a[i]);
    }
    b.cx(a[1], t(1));
    c1(b);
    for i in 1..n - 1 {
        b.cx(a[i], a[i + 1]);
    }
    for i in 1..n {
        b.cx(a[i], t(i));
    }
}

/// Exact pre-add or post-add cofactor bit from G'=2 (mod 4).
/// The low known value lanes are never read, so they may host cofactor bits.
pub(super) fn value_bit_oracle(b:&mut B,u:&[QubitId],gh:&[QubitId],f:&[QubitId],e:QubitId,rho:&ParityCtl,target:Option<QubitId>,dirty:&[QubitId],post:bool){
 let filtered_dirty:Vec<_>=dirty.iter().copied().filter(|q|Some(*q)!=target).collect();let dirty=filtered_dirty.as_slice();
 let p=f.len();assert_eq!(u.len(),p+1);assert_eq!(gh.len(),p-1);
 let rp=lq_fold(b,rho);let PL::Q(rq)=rp else{panic!("physical rho needed")};
 let read=|b:&mut B,q:QubitId|{if let Some(t)=target{b.cx(q,t)}else{b.z_if(q,crate::circuit::NO_BIT)}};
 let mut transforms=vec![];
 if post{
  b.begin();lq_codec_hi(b,&u[..p],gh,f,rp,&[],dirty);transforms.push(b.end());
 }else{
  b.begin();pre_value_transform(b,u,gh,f,e,rq,dirty,true);transforms.push(b.end());
  let unique=|q:&[QubitId]|q.iter().map(|q|q.0).collect::<std::collections::BTreeSet<_>>().len()==q.len();
  if unique(f)&&unique(gh){b.begin();pre_value_transform(b,u,gh,f,e,rq,dirty,false);transforms.push(b.end());}
 }
 let mut low_candidates=vec![];
 if p>=3 {
  if post{
   b.begin();lq_codec_hi(b,&u[..p-1],&gh[..p-2],&f[..p-1],rp,&[],dirty);low_candidates.push(b.end());
  }else{
   b.begin();pre_value_transform(b,&u[..p],&gh[..p-2],&f[..p-1],e,rq,dirty,true);low_candidates.push(b.end());
   let unique=|q:&[QubitId]|q.iter().map(|q|q.0).collect::<std::collections::BTreeSet<_>>().len()==q.len();
   if unique(&f[..p-1])&&unique(&gh[..p-2]){b.begin();pre_value_transform(b,&u[..p],&gh[..p-2],&f[..p-1],e,rq,dirty,false);low_candidates.push(b.end());}
  }
 }
 let mut low_best=None;let mut low_cost=f64::INFINITY;
 for low in low_candidates{let cost=b.measure(&low,true);if cost<low_cost{low_cost=cost;low_best=Some(low);}}
 let top=u[if post{p-1}else{p}];let mut best=vec![];let mut best_cost=f64::INFINITY;
 for transform in transforms {
  b.begin();b.play(&transform,false);read(b,top);b.play(&transform,true);let original=b.end();
  b.begin();read(b,top);triangular_top_delta(b,&transform,top,target,low_best.as_deref());let projected=b.end();
  for candidate in [original,projected]{let cost=b.measure(&candidate,false);if cost<best_cost{best_cost=cost;best=candidate;}}
 }
 b.play(&best,false);
 lq_unfold(b,rho);
}

/// c_p = V_p xor U_p xor V'_p, with all low-word operands restored.
pub(super) fn carry_oracle(b:&mut B,u:&[QubitId],g:&[QubitId],f:&[QubitId],e:QubitId,rho:&ParityCtl,target:Option<QubitId>,dirty:&[QubitId]){
 let p=f.len();
 if let Some(t)=target{b.cx(u[p],t)}else{b.z_if(u[p],crate::circuit::NO_BIT)}
 value_bit_oracle(b,u,&g[1..],f,e,rho,target,dirty,false);
 value_bit_oracle(b,u,&g[1..],f,e,rho,target,dirty,true);
}

fn pre_value_transform(b:&mut B,u:&[QubitId],gh:&[QubitId],f:&[QubitId],e:QubitId,rq:QubitId,dirty:&[QubitId],general:bool){
 let p=f.len();
 if general{
  b.cx(e,rq);
  for i in (0..p).rev(){
   let t=&u[i+1..];let ct=[u[i]];
   b.x(rq);lq_add_const(b,t,1,&[u[i],rq],dirty);b.x(rq);
   if t.len()>1{lq_ttk_add_ctl(b,&gh[..t.len()-1],&t[1..],&ct,dirty);}
   for &x in t{b.cx(rq,x);}
   lq_ttk_add_ctl(b,&f[..t.len()],t,&ct,dirty);
   for &x in t{b.cx(rq,x);}
  }
  b.cx(e,rq);
}else{
  b.cx(e,rq);
  b.begin();
  for &q in f {b.cx(rq,q);}
  lq_add_const(b,f,1,&[],dirty);
  lq_ttk_add_ctl(b,gh,&f[1..],&[],dirty);
  for &q in f {b.cx(rq,q);}
  let ft=b.end();
  b.play(&ft,false);
  lq_mul_odd(b,f,u,&[],dirty);
  for &q in u {b.cx(rq,q);}
  lq_add_const(b,u,1,&[rq],dirty);
  b.play(&ft,true);
  b.cx(e,rq);
 }
  let mask=(1u64<<(p+1))-1;let c0=super::frogdrop_sched::p().as_limbs()[0]&mask;
  // Bitwise-complement conjugation changes an addition of p into subtraction of p.
  for &q in u{b.cx(rq,q);}
  lq_add_const(b,u,c0,&[],dirty);
  for &q in u{b.cx(rq,q);}
  b.begin();lq_mul_odd(b,f,u,&[],dirty);let div=b.end();b.play(&div,true);
}

/// For a triangular word permutation, the top bit never controls another operation.
/// Its delta can therefore be sent directly to an output (or to a phase), after
/// which only the lower-word permutation needs reversing.
fn triangular_top_delta(b:&mut B,transform:&[G],top:QubitId,target:Option<QubitId>,direct_lower:Option<&[G]>){
 let mut front=vec![];let mut lower=vec![];
 let inverse=|g:G|match g{G::AndC(a,c,t)=>G::AndU(a,c,t),G::AndU(a,c,t)=>G::AndC(a,c,t),_=>g};
 for &g in transform {
  let into_top=match g{
   G::X(t)=>t==top,
   G::Cx(a,t)=>{assert!(a!=top);t==top},
   G::Ccx(a,c,t)=>{assert!(a!=top&&c!=top);t==top},
   G::AndC(a,c,t)|G::AndU(a,c,t)=>{assert!(a!=top&&c!=top&&t!=top);false},
   _=>panic!("unexpected gate in triangular low-word permutation: {:?}",g),
  };
  if into_top{
   front.push(match(g,target){
    (G::X(_),Some(t))=>G::X(t),(G::X(_),None)=>G::Neg,
    (G::Cx(a,_),Some(t))=>G::Cx(a,t),(G::Cx(a,_),None)=>G::ZIf(a,crate::circuit::NO_BIT),
    (G::Ccx(a,c,_),Some(t))=>G::Ccx(a,c,t),(G::Ccx(a,c,_),None)=>G::Cz(a,c),
    _=>unreachable!(),
   });
  }else{
   front.push(g);
   if lower.last().copied()==Some(inverse(g)){lower.pop();}else{lower.push(g);}
  }
 }
 b.play(&front,false);
 if let Some(direct)=direct_lower{let a=b.measure(direct,true);let c=b.measure(&lower,true);b.play(if a<c{direct}else{&lower},true);}else{b.play(&lower,true);}
}

fn lq_codec_offset_base(b:&mut B,q:&[QubitId],f:&[QubitId],rho:PL,ctls:&[QubitId],dirty:&[QubitId]){
    let n=q.len();
    let mask = (1u64 << n) - 1;
    let (c0, c1) = lq_half_consts(n + 1);
    match rho {
        PL::C(v) => lq_add_const(b, q, if v { c1 } else { c0 }, ctls, dirty),
        PL::Q(rq) => {
            // C(rho) = (c0+1) + (c1-c0-1)*rho - !rho.
            // The first two terms are high-bit constants for the low secp256k1 lanes.
            lq_add_const(b, q, c0.wrapping_add(1)&mask, ctls, dirty);
            let mut c=ctls.to_vec();c.push(rq);
            lq_add_const(b,q,c1.wrapping_sub(c0).wrapping_sub(1)&mask,&c,dirty);
            b.x(rq);b.begin();lq_add_const(b,q,1,&c,dirty);let dec=b.end();b.play(&dec,true);b.x(rq);
        }
    }
    for &x in q {
        lq_mcx(b, ctls, x, dirty);
    }
    lq_ttk_add_ctl(b, &f[..n], q, ctls, dirty);
    for &x in q {
        lq_mcx(b, ctls, x, dirty);
    }
}

/// Fuse the conditional G/F exchange with the two odd multiplications.
/// On the no-swap branch they cancel; on the swap branch their ratio is G/F.
pub(super) fn lq_codec_crossing_swap(b:&mut B,q:&[QubitId],g:&[QubitId],f:&[QubitId],rho:PL,sg:QubitId,dirty:&[QubitId],swap:impl FnOnce(&mut B)){
    lq_mul_odd(b,g,q,&[],dirty);
    lq_codec_offset(b,q,f,rho,&[sg],dirty);
    swap(b);
    b.begin();lq_mul_odd(b,g,q,&[],dirty);let div=b.end();b.play(&div,true);
}

/// Toggle only the top coordinate of the post-add low-word codec.
/// Its delta depends exclusively on the lower coordinates and restored sources.
pub(super) fn post_top_delta(b:&mut B,u:&[QubitId],gh:&[QubitId],f:&[QubitId],rho:&ParityCtl,dirty:&[QubitId]){
 let p=f.len();assert!(p>=2&&u.len()>=p&&gh.len()>=p-1);let top=u[p-1];
 let dirty:Vec<_>=dirty.iter().copied().filter(|q|*q!=top).collect();
 let rp=lq_fold(b,rho);
 b.begin();lq_codec_hi(b,&u[..p],gh,f,rp,&[],&dirty);let transform=b.end();
 let lower=if p>=3{b.begin();lq_codec_hi(b,&u[..p-1],&gh[..p-2],&f[..p-1],rp,&[],&dirty);Some(b.end())}else{None};
 triangular_top_delta(b,&transform,top,Some(top),lower.as_deref());
 lq_unfold(b,rho);
}

/// Reuse an already hosted post-add bit in the incoming-carry identity.
pub(super) fn carry_from_host_oracle(b:&mut B,u:&[QubitId],gh:&[QubitId],f:&[QubitId],e:QubitId,rho:&ParityCtl,host:QubitId,target:Option<QubitId>,dirty:&[QubitId]){
 let p=f.len();
 if let Some(t)=target{b.cx(u[p],t);b.cx(host,t);}else{b.z_if(u[p],crate::circuit::NO_BIT);b.z_if(host,crate::circuit::NO_BIT);}
 value_bit_oracle(b,u,gh,f,e,rho,target,dirty,false);
}

/// A clean conjunction of the outer controls, restored after the arithmetic.
fn arithmetic_control(b:&mut B,ctls:&[QubitId],blocked:&[QubitId])->Option<(QubitId,Vec<QubitId>,Vec<G>)>{
 let mut ct:Vec<_>=ctls.iter().copied().filter(|q|*q!=ONE).collect();ct.sort_by_key(|q|q.0);ct.dedup();
 let mut pool:Vec<_>=b.low_clean.iter().copied().filter(|q|!blocked.contains(q)&&!ct.contains(q)).collect();pool.sort_by_key(|q|q.0);pool.dedup();
 if pool.len()<ct.len().saturating_sub(1){return None;}
 b.begin();let h=if ct.is_empty(){ONE}else if ct.len()==1{ct[0]}else{
  let mut h=ct[0];for &q in &ct[1..]{let t=pool.pop().unwrap();b.and_c(h,q,t);h=t;}h
 };let fold=b.end();Some((h,pool,fold))
}
fn arithmetic_choice(b:&mut B,base:Vec<G>,pooled:Vec<G>){
 let a=b.measure(&base,true);let c=b.measure(&pooled,true);b.play(if c<a{&pooled}else{&base},false);
}
pub(super) fn lq_ttk_add_ctl(b:&mut B,a:&[QubitId],t:&[QubitId],ctls:&[QubitId],dirty:&[QubitId]){
 if t.len()<2 || b.low_clean.is_empty() || a.iter().enumerate().any(|(i,q)|a[..i].contains(q)){return lq_ttk_add_ctl_base(b,a,t,ctls,dirty);}
 let blocked:Vec<_>=a.iter().chain(t).copied().collect();
 let Some((h,pool,fold))=arithmetic_control(b,ctls,&blocked)else{return lq_ttk_add_ctl_base(b,a,t,ctls,dirty)};
 if pool.is_empty(){return lq_ttk_add_ctl_base(b,a,t,ctls,dirty);}
 b.begin();lq_ttk_add_ctl_base(b,a,t,ctls,dirty);let base=b.end();
 b.begin();b.play(&fold,false);low_ctrl_add_pool(b,a,t,h,&pool);b.play(&fold,true);let pooled=b.end();arithmetic_choice(b,base,pooled);
}
pub(super) fn lq_add_const(b:&mut B,q:&[QubitId],k:u64,ctls:&[QubitId],dirty:&[QubitId]){
 let k=k&((1u64<<q.len())-1);if k==0{return;}
 if b.low_clean.is_empty(){return lq_add_const_base(b,q,k,ctls,dirty);}
 let Some((h,pool,fold))=arithmetic_control(b,ctls,q)else{return lq_add_const_base(b,q,k,ctls,dirty)};
 let need=q.len()-1-k.trailing_zeros()as usize;
 if pool.len()<need{return lq_add_const_base(b,q,k,ctls,dirty);}
 b.begin();lq_add_const_base(b,q,k,ctls,dirty);let base=b.end();
 b.begin();b.play(&fold,false);super::modp_ft::const_add_pool(b,q,h,k,&pool);b.play(&fold,true);let pooled=b.end();arithmetic_choice(b,base,pooled);
}

// Keep low-word recordings in primitive gates for exact top-coordinate projection.
fn low_ctrl_add_pool(b: &mut B, a: &[QubitId], t: &[QubitId], ctl: QubitId, pool: &[QubitId]) {
    use super::arith::{down_m, ttk_add, up_m, Dm};
    let n = t.len();
    assert!(n >= 2 && a.len() == n);
    let pn = pool.len().min(n - 1);
    if pn == 0 {
        ttk_add(b, a, t, Some(ctl), None);
        return;
    }
    let c = pool;
    for i in 0..pn {
        if i == 0 {
            b.and_c(a[0], t[0], c[0]);
        } else {
            b.cx(c[i - 1], a[i]);
            b.cx(c[i - 1], t[i]);
            b.and_c(a[i], t[i], c[i]);
            b.cx(c[i - 1], c[i]);
        }
    }
    // lanes pn..n-1: Cuccaro, the carry into the top lane ends in a[n - 2]
    let (th, sh) = (&t[pn..n - 1], &a[pn..n - 1]);
    if !th.is_empty() {
        let up = up_m(b, th, sh, c[pn - 1], false);
        b.play(&up, false);
    }
    let ct = if th.is_empty() { c[pn - 1] } else { a[n - 2] };
    b.cx(ct, a[n - 1]);
    b.ccx(ctl, a[n - 1], t[n - 1]);
    b.cx(ct, a[n - 1]);
    if !th.is_empty() {
        let dn = down_m(b, th, sh, c[pn - 1], Dm::Cond(ctl), false);
        b.play(&dn, false);
    }
    for i in (0..pn).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], c[0]);
            b.ccx(ctl, a[0], t[0]);
        } else {
            b.cx(c[i - 1], c[i]);
            b.and_u(a[i], t[i], c[i]);
            b.cx(c[i - 1], t[i]);
            b.ccx(ctl, a[i], t[i]);
            b.cx(c[i - 1], a[i]);
        }
    }
}

/// Exact controlled addition with a restored incoming carry, using all available clean carries.
fn low_add_cin(b:&mut B,a:&[QubitId],t:&[QubitId],cin:QubitId,ctl:QubitId){
 use super::arith::{up_m,down_m,Dm};
 let n=t.len();assert!(n>0&&a.len()==n);assert!(!a.contains(&cin)&&!t.contains(&cin));
 let mut pool:Vec<_>=b.low_clean.iter().copied().filter(|q|!a.contains(q)&&!t.contains(q)&&*q!=cin&&*q!=ctl).collect();pool.sort_by_key(|q|q.0);pool.dedup();
 let pn=pool.len().min(n-1);let incoming=|i:usize|if i==0{cin}else{pool[i-1]};
 for i in 0..pn{let c=incoming(i);b.cx(c,a[i]);b.cx(c,t[i]);b.and_c(a[i],t[i],pool[i]);b.cx(c,a[i]);b.cx(c,pool[i]);}
 let ci=incoming(pn);let up=up_m(b,&t[pn..n-1],&a[pn..n-1],ci,false);b.play(&up,false);
 let carry=if pn==n-1{ci}else{a[n-2]};b.cx(carry,a[n-1]);b.ccx(ctl,a[n-1],t[n-1]);b.cx(carry,a[n-1]);
 let down=down_m(b,&t[pn..n-1],&a[pn..n-1],ci,Dm::Cond(ctl),false);b.play(&down,false);
 for i in (0..pn).rev(){let c=incoming(i);b.cx(c,pool[i]);b.cx(c,a[i]);b.and_u(a[i],t[i],pool[i]);b.cx(c,a[i]);b.cx(c,t[i]);b.cx(c,a[i]);b.ccx(ctl,a[i],t[i]);b.cx(c,a[i]);}
}
fn lq_codec_offset(b:&mut B,q:&[QubitId],f:&[QubitId],rho:PL,ctls:&[QubitId],dirty:&[QubitId]){
 let PL::Q(rq)=rho else{return lq_codec_offset_base(b,q,f,rho,ctls,dirty)};
 if ctls.len()>1||f.iter().enumerate().any(|(i,x)|f[..i].contains(x)){return lq_codec_offset_base(b,q,f,rho,ctls,dirty);}
 b.begin();lq_codec_offset_base(b,q,f,rho,ctls,dirty);let old=b.end();
 b.begin();let n=q.len();let mask=(1u64<<n)-1;let(c0,c1)=lq_half_consts(n+1);
 lq_add_const(b,q,c0.wrapping_add(1)&mask,ctls,dirty);
 let mut c=ctls.to_vec();c.push(rq);lq_add_const(b,q,c1.wrapping_sub(c0).wrapping_sub(1)&mask,&c,dirty);
 let ctl=ctls.first().copied().unwrap_or(ONE);for &x in q{b.cx(ctl,x);}b.x(rq);
 low_add_cin(b,&f[..n],q,rq,ctl);b.x(rq);for &x in q{b.cx(ctl,x);}
 let merged=b.end();let cm=b.measure(&merged,true);let co=b.measure(&old,true);b.play(if cm<co{&merged}else{&old},false);
}
