//! lfw: exact width post-pass. The planner and its approximations are untouched: this runs on the emitted stream.
//! 1. tight segments from the builder's alloc/release log (a release is the builder's own |0> claim);
//! 2. every wire carries a definition kept current by substitution: a linear form plus AND pairs of linear forms
//!    over live wires (CX(d,x) rewrites x_old = x_new ^ d inside every form holding x; X flips the constant; SWAP renames;
//!    CCX(a,b,x) on a wire held linearly adds the pair (a,b)); anything else invalidates;
//! 3. at every op where more than `cap` segments are live, one wire w untouched across the window is erased
//!    (CX/X for a linear definition; HMR plus conditioned Z/Neg/CZ fixups when it has an AND pair, 0 T) and recomputed
//!    after the window (1 CCX per AND pair), with every form wire untargeted across the window;
//! 4. the split segments are recoloured onto ids 0..cap-1; outputs go back to their register ids by SWAPs at the end.
use crate::circuit::{analyze_ops, BitId, Op, OperationType, QubitId, QubitOrBit, NO_BIT};
use std::collections::BTreeSet;
struct ZeroXof;
impl sha3::digest::XofReader for ZeroXof { fn read(&mut self, buf: &mut [u8]) { buf.fill(0); } }

const FORM_MAX: usize = 24;
const ANDS_MAX: usize = 8;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Form { w: Vec<u32>, c: bool }
impl Form {
    fn one(x: u32) -> Self { Form { w: vec![x], c: false } }
    fn has(&self, x: u32) -> bool { self.w.binary_search(&x).is_ok() }
    fn toggle(&mut self, x: u32) { match self.w.binary_search(&x) { Ok(p) => { self.w.remove(p); } Err(p) => self.w.insert(p, x) } }
    fn xor(&mut self, o: &Form) { for &x in &o.w { self.toggle(x); } self.c ^= o.c; }
    fn rename(&mut self, a: u32, b: u32) { let (ha, hb) = (self.has(a), self.has(b)); if ha != hb { if ha { self.toggle(a); self.toggle(b); } else { self.toggle(b); self.toggle(a); } } }
    fn eval(&self, qs: &[u64], bs: &[u64]) -> u64 { let mut v = if self.c { u64::MAX } else { 0 }; for &x in &self.w { v ^= if (x as usize) < qs.len() { qs[x as usize] } else { bs[x as usize - qs.len()] }; } v }
}
#[derive(Clone, PartialEq, Debug, Default)]
struct Def { lin: Form, ands: Vec<(Form, Form)>, cands: Vec<(u32, Form, Form)>, tris: Vec<(Form, Form, Form)> }
impl Def {
    fn is_zero(&self) -> bool { self.lin.w.is_empty() && !self.lin.c && self.ands.is_empty() && self.cands.is_empty() && self.tris.is_empty() }
    fn mentions(&self, x: u32) -> bool { self.lin.has(x) || self.ands.iter().any(|(a, b)| a.has(x) || b.has(x)) || self.cands.iter().any(|(m, a, b)| *m == x || a.has(x) || b.has(x)) || self.tris.iter().any(|(a, b, c)| a.has(x) || b.has(x) || c.has(x)) }
    fn in_tri(&self, x: u32) -> bool { self.tris.iter().any(|(a, b, c)| a.has(x) || b.has(x) || c.has(x)) }
    fn in_product(&self, x: u32) -> bool { self.ands.iter().any(|(a, b)| a.has(x) || b.has(x)) || self.cands.iter().any(|(m, a, b)| *m == x || a.has(x) || b.has(x)) || self.in_tri(x) }
    fn wires(&self) -> Vec<u32> { let mut v: Vec<u32> = self.lin.w.clone(); for (a, b) in &self.ands { v.extend(&a.w); v.extend(&b.w); } for (m, a, b) in &self.cands { v.push(*m); v.extend(&a.w); v.extend(&b.w); } for (a, b, c) in &self.tris { v.extend(&a.w); v.extend(&b.w); v.extend(&c.w); } v.sort(); v.dedup(); v }
    fn eval(&self, qs: &[u64], bs: &[u64]) -> u64 { let mut v = self.lin.eval(qs, bs); for (a, b) in &self.ands { v ^= a.eval(qs, bs) & b.eval(qs, bs); }
        for (m, a, b) in &self.cands { v ^= bs[*m as usize - qs.len()] & a.eval(qs, bs) & b.eval(qs, bs); }
        for (a, b, c) in &self.tris { v ^= a.eval(qs, bs) & b.eval(qs, bs) & c.eval(qs, bs); } v }
    fn push_tri(&mut self, a: Form, b: Form, c: Form) { let mut v = vec![a, b, c]; v.sort(); let t = (v[0].clone(), v[1].clone(), v[2].clone()); if let Some(k) = self.tris.iter().position(|x| *x == t) { self.tris.remove(k); } else { self.tris.push(t); } }
    fn push_cand(&mut self, m: u32, a: Form, b: Form) { let (a, b) = if a <= b { (a, b) } else { (b, a) }; let t = (m, a, b); if let Some(k) = self.cands.iter().position(|x| *x == t) { self.cands.remove(k); } else { self.cands.push(t); } }
    fn push_and(&mut self, a: Form, b: Form) { let p = if a <= b { (a, b) } else { (b, a) }; if let Some(k) = self.ands.iter().position(|x| *x == p) { self.ands.remove(k); } else { self.ands.push(p); } }
    /// fold constant forms: AND(0,B) = 0, AND(1,B) = B; false if over the size caps
    fn normalize(&mut self) -> bool {
        let ands = std::mem::take(&mut self.ands);
        for (a, b) in ands {
            if a.w.is_empty() { if a.c { self.lin.xor(&b); } continue; }
            if b.w.is_empty() { if b.c { self.lin.xor(&a); } continue; }
            if Def::hosts(&a, &b).is_none() {
                // nested forms: A.B = (A^B).B ^ B, or A.(A^B) ^ A; equal forms: A.A = A
                let mut c = a.clone(); c.xor(&b);
                if c.w.is_empty() { if !c.c { self.lin.xor(&a); } else { /* A.(A^1) = 0 */ } continue; }
                if Def::hosts(&c, &b).is_some() { self.lin.xor(&b); self.push_and(c, b); continue; }
                if Def::hosts(&a, &c).is_some() { self.lin.xor(&a); self.push_and(a, c); continue; }
            }
            self.push_and(a, b);
        }
        let cands = std::mem::take(&mut self.cands);
        for (m, a, b) in cands {
            if a.w.is_empty() { if a.c { self.push_and(Form::one(m), b); } continue; }
            if b.w.is_empty() { if b.c { self.push_and(Form::one(m), a); } continue; }
            if Def::hosts(&a, &b).is_none() {
                let mut c = a.clone(); c.xor(&b);
                if c.w.is_empty() { if !c.c { self.push_and(Form::one(m), a); } continue; }
                if Def::hosts(&c, &b).is_some() { self.push_and(Form::one(m), b.clone()); self.push_cand(m, c, b); continue; }
                if Def::hosts(&a, &c).is_some() { self.push_and(Form::one(m), a.clone()); self.push_cand(m, a, c); continue; }
            }
            self.push_cand(m, a, b);
        }
        if self.cands.len() > ANDS_MAX || self.cands.iter().any(|(_, a, b)| a.w.len() > FORM_MAX || b.w.len() > FORM_MAX) { return false; }
        let tris = std::mem::take(&mut self.tris);
        for (a, b, c) in tris {
            let fs = [a, b, c];
            if let Some(k) = fs.iter().position(|f| f.w.is_empty()) { if fs[k].c { let o: Vec<Form> = fs.iter().enumerate().filter(|(j, _)| *j != k).map(|(_, f)| f.clone()).collect(); self.push_and(o[0].clone(), o[1].clone()); } continue; }
            let [a, b, c] = fs; self.push_tri(a, b, c);
        }
        if self.tris.len() > 4 || self.tris.iter().any(|(a, b, c)| a.w.len() > FORM_MAX || b.w.len() > FORM_MAX || c.w.len() > FORM_MAX) { return false; }
        self.lin.w.len() <= FORM_MAX && self.ands.len() <= ANDS_MAX && self.ands.iter().all(|(a, b)| a.w.len() <= FORM_MAX && b.w.len() <= FORM_MAX)
    }
    /// host wires for materialising AND(a, b): one of a outside b, one of b outside a
    fn hosts(a: &Form, b: &Form) -> Option<(u32, u32)> { let ha = a.w.iter().find(|x| !b.has(**x))?; let hb = b.w.iter().find(|x| !a.has(**x))?; Some((*ha, *hb)) }
    fn qonly(f: &Form, nq: u32) -> bool { f.w.iter().all(|&y| y < nq) }
    fn bitpair(a: &Form, b: &Form, nq: u32) -> bool { a.w.len() == 1 && a.w[0] >= nq && !a.c && !b.w.is_empty() && Def::qonly(b, nq) }
    /// Toffolis to recompute: one per qubit-qubit AND pair (a bit-qubit pair is a conditioned CX)
    fn cost(&self, nq: u32) -> usize { self.ands.iter().filter(|(a, b)| Def::qonly(a, nq) && Def::qonly(b, nq)).count() + self.cands.len() + 4 * self.tris.len() }
    fn hosts3(a: &Form, b: &Form, c: &Form) -> Option<(u32, u32, u32)> { let ha = a.w.iter().find(|x| !b.has(**x) && !c.has(**x))?; let hb = b.w.iter().find(|x| !a.has(**x) && !c.has(**x))?; let hc = c.w.iter().find(|x| !a.has(**x) && !b.has(**x))?; Some((*ha, *hb, *hc)) }
    /// every AND pair: two disjoint non-empty qubit forms (one host each), or a lone condition bit times a qubit form
    fn emittable(&self, nq: u32) -> bool { self.ands.iter().all(|(a, b)| (Def::qonly(a, nq) && Def::qonly(b, nq) && Def::hosts(a, b).is_some()) || Def::bitpair(a, b, nq) || Def::bitpair(b, a, nq))
        && self.cands.iter().all(|(m, a, b)| *m >= nq && Def::qonly(a, nq) && Def::qonly(b, nq) && Def::hosts(a, b).is_some())
        && self.tris.iter().all(|(a, b, c)| Def::qonly(a, nq) && Def::qonly(b, nq) && Def::qonly(c, nq) && Def::hosts3(a, b, c).is_some()) }
}

/// replace wire x inside d by x's own definition dx (x_old = dx): always valid in the linear part; inside an AND form only for a linear dx
fn inline_into(d: &mut Def, x: u32, dx: &Option<Def>) -> bool {
    let Some(dx) = dx else { return false };
    if dx.mentions(x) { return false; }
    let in_and = d.in_product(x);
    let dx_lin = dx.ands.is_empty() && dx.cands.is_empty() && dx.tris.is_empty();
    if in_and && !dx_lin {
        // only plain AND pairs may hold x, and dx may only add plain products: (A^P.Q).B = A.B ^ P.Q.B
        if !dx.cands.is_empty() || !dx.tris.is_empty() || d.cands.iter().any(|(m, a, b)| *m == x || a.has(x) || b.has(x)) || d.in_tri(x) { return false; }
        if d.ands.iter().any(|(a, b)| a.has(x) && b.has(x)) && dx.ands.len() > 1 { return false; }
    }
    let mut xl = dx.lin.clone(); xl.toggle(x); // x_old ^ x is replaced: F ^= {x} ^ dx.lin
    if d.lin.has(x) { d.lin.xor(&xl); for (p, r) in &dx.ands { d.push_and(p.clone(), r.clone()); } for (m, p, r) in &dx.cands { d.push_cand(*m, p.clone(), r.clone()); } for (p, r, t) in &dx.tris { d.push_tri(p.clone(), r.clone(), t.clone()); } }
    if !dx_lin {
        let ands = std::mem::take(&mut d.ands);
        for (a, b) in ands {
            let (xa, xb) = (a.has(x), b.has(x));
            let (mut a2, mut b2) = (a.clone(), b.clone()); if xa { a2.xor(&xl); } if xb { b2.xor(&xl); }
            for (p, r) in &dx.ands { if xa { d.push_tri(p.clone(), r.clone(), b2.clone()); } if xb { d.push_tri(p.clone(), r.clone(), a2.clone()); } if xa && xb { d.push_and(p.clone(), r.clone()); } }
            d.push_and(a2, b2);
        }
        return true;
    }
    for (p, r) in d.ands.iter_mut() { if p.has(x) { p.xor(&xl); } if r.has(x) { r.xor(&xl); } }
    for (_, p, r) in d.cands.iter_mut() { if p.has(x) { p.xor(&xl); } if r.has(x) { r.xor(&xl); } }
    for (p, r, t) in d.tris.iter_mut() { if p.has(x) { p.xor(&xl); } if r.has(x) { r.xor(&xl); } if t.has(x) { t.xor(&xl); } }
    true
}
fn targets(op: &Op) -> [u64; 2] {
    use OperationType::*;
    match op.kind { CCX | CX | X | Hmr | R => [op.q_target.0, u64::MAX], Swap => [op.q_target.0, op.q_control1.0], _ => [u64::MAX; 2] }
}
fn touched(op: &Op) -> [u64; 3] { [op.q_control2.0, op.q_control1.0, op.q_target.0] }

pub struct Report { pub runs: usize, pub run_ops: usize, pub covers: usize, pub ccx_added: usize, pub uncovered: Vec<usize>, pub max_id: u64 }

/// segments: (q, start, end_exclusive) in op indices; inputs start at 0.
pub fn tight_segments(ops: &[Op], log: &[(u64, usize, bool)]) -> Vec<(u64, usize, usize)> { tight_segments_ex(ops, log).0 }
/// segments plus the starts of pseudo-segments (touches with no earlier segment to extend)
pub fn tight_segments_ex(ops: &[Op], log: &[(u64, usize, bool)]) -> (Vec<(u64, usize, usize)>, std::collections::HashSet<(u64, usize)>) {
    let mut pseudo: std::collections::HashSet<(u64, usize)> = std::collections::HashSet::new();
    use std::collections::HashMap;
    let end = ops.len();
    let mut touches: HashMap<u64, Vec<usize>> = HashMap::new();
    for (i, op) in ops.iter().enumerate() { for q in touched(op) { if q != u64::MAX { touches.entry(q).or_default().push(i); } } }
    // only an unconditioned reset outside every condition block clears a wire on every shot
    // a reset clears on every shot when it is unconditioned at depth 0, or block-conditioned only (no own bit) on a wire
    // whose segment began inside the innermost open block: on shots where the block is off, that wire was never set
    let mut uncond = vec![false; end]; let mut block_start = vec![usize::MAX; end];
    { let mut st: Vec<usize> = Vec::new(); for i in 0..end { let o = &ops[i];
        match o.kind { OperationType::PushCondition => st.push(i), OperationType::PopCondition => { st.pop(); }, _ => {} }
        uncond[i] = o.c_condition == crate::circuit::NO_BIT; block_start[i] = st.last().copied().unwrap_or(usize::MAX); } }
    let clears = |i: usize, seg_start: usize| uncond[i] && (block_start[i] == usize::MAX || seg_start > block_start[i]);
    let mut open: HashMap<u64, usize> = HashMap::new();
    let mut ivs = Vec::new();
    for &(q, op, a) in log {
        if a { assert!(open.insert(q, op).is_none(), "lfw: double alloc of q{q} at op {op}"); } else { let s = open.remove(&q).expect("release unalloc"); ivs.push((s, op, q)); }
    }
    for (q, s) in open { ivs.push((s, end, q)); }
    let mut segs = Vec::new();
    for (s, r, q) in ivs {
        let t = touches.get(&q).map(|v| v.as_slice()).unwrap_or(&[]);
        let lo = t.partition_point(|&x| x < s);
        let hi = t.partition_point(|&x| x < r);
        if hi <= lo { continue; }
        let mut seg_start = if s == 0 { 0 } else { t[lo] };
        for k in lo..hi {
            let i = t[k];
            let reset = matches!(ops[i].kind, OperationType::Hmr | OperationType::R) && ops[i].q_target.0 == q && clears(i, seg_start);
            if reset && k + 1 < hi { segs.push((q, seg_start, i + 1)); seg_start = t[k + 1]; }
        }
        let l = if r == end { end } else { t[hi - 1] + 1 };
        segs.push((q, seg_start, l));
    }
    // touches outside every alloc..release interval: the builder parks some wires (early-measured tape signs, parked
    // bit-0 pairs) by releasing them while they still hold data and keeping their ids out of reuse. Their later touches
    // continue the preceding segment (no |0> gap) up to the HMR/R that really clears them.
    let mut byq: HashMap<u64, Vec<usize>> = HashMap::new();
    for (k, &(q, _, _)) in segs.iter().enumerate() { byq.entry(q).or_default().push(k); }
    for v in byq.values_mut() { v.sort_by_key(|&k| segs[k].1); }
    let mut extra = 0usize;
    for (q, t) in &touches {
        let ks = byq.get(q).cloned().unwrap_or_default();
        let covered = |i: usize, segs: &Vec<(u64, usize, usize)>| ks.iter().any(|&k| segs[k].1 <= i && i < segs[k].2);
        let mut pending_end: Option<(Option<usize>, usize, usize)> = None; // (segment to extend, group start, group end)
        for &i in t {
            if covered(i, &segs) { if let Some((k, st, en)) = pending_end.take() { match k { Some(k) => segs[k].2 = segs[k].2.max(en), None => { segs.push((*q, st, en)); pseudo.insert((*q, st)); } } extra += 1; } continue; }
            let prev = ks.iter().cloned().filter(|&k| segs[k].2 <= i).max_by_key(|&k| segs[k].2);
            let ent = pending_end.get_or_insert((prev, i, i + 1)); ent.2 = i + 1;
            if matches!(ops[i].kind, OperationType::Hmr | OperationType::R) && ops[i].q_target.0 == *q && clears(i, ent.1.min(i)) && block_start[i] == usize::MAX {
                let (k, st, en) = pending_end.take().unwrap(); match k { Some(k) => segs[k].2 = segs[k].2.max(en), None => { segs.push((*q, st, en)); pseudo.insert((*q, st)); } } extra += 1;
            }
        }
        if let Some((k, st, en)) = pending_end.take() { match k { Some(k) => segs[k].2 = segs[k].2.max(en), None => { segs.push((*q, st, en)); pseudo.insert((*q, st)); } } extra += 1; }
    }
    if extra > 0 { eprintln!("LFW parked_extensions={extra} pseudo_segments={}", pseudo.len()); }
    (segs, pseudo)
}

type Cover = (usize, usize, usize, Def, Def); // (erase_at, recompute_at, w, definition at erase, definition at recompute)

/// phase-only AND helper: CCX(a,b,t) on a fresh t; CX(t,u); diagonal CZ/Z gates; CX(t,u); HMR(t)->k; CZ(a,b) if k; ...; R(t).
/// The gates in between see u ^ a.b, so CZ(p,u) becomes CZ(p,u).CCZ(p,a,b) and Z(u) becomes Z(u).CZ(a,b): t is never needed.
/// Bit k (the dropped measurement's outcome) must not be read where the parent would see that outcome: every later read of
/// k must sit inside a block instance (or at top level) in which an unconditioned write to k happened after `from`.
/// The scan ends at an unconditioned top-level write.
fn k_unread(ops: &[Op], from: usize, k: BitId) -> bool {
    use OperationType::*;
    let mut covered: Vec<bool> = vec![false]; // per open condition level, relative to `from` (level 0 = enclosing context)
    for q in &ops[from..] {
        match q.kind {
            PushCondition => { if q.c_condition == k && !covered.iter().any(|&c| c) { return false; } covered.push(false); continue; }
            PopCondition => { if covered.len() > 1 { covered.pop(); } else { covered[0] = false; } continue; }
            _ => {}
        }
        if q.c_condition == k && !covered.iter().any(|&c| c) { return false; }
        if q.kind == BitInvert && q.c_target == k && !covered.iter().any(|&c| c) { return false; }
        if matches!(q.kind, Hmr | BitStore0 | BitStore1) && q.c_target == k && q.c_condition == NO_BIT {
            if covered.len() == 1 && from_depth_zero(&covered) { return true; }
            *covered.last_mut().unwrap() = true;
        }
    }
    true
}
fn from_depth_zero(c: &[bool]) -> bool { c.len() == 1 }
fn peephole_phase_and(ops: &[Op], log: &[(u64, usize, bool)]) -> (Vec<Op>, Vec<(u64, usize, bool)>, usize) {
    use OperationType::*;
    let n = ops.len();
    let (segs0, pseudo) = tight_segments_ex(ops, log);
    let fresh: std::collections::HashSet<(u64, usize)> = segs0.iter().map(|&(q, a, _)| (q, a)).filter(|x| !pseudo.contains(x)).collect();
    let mut depth_at = vec![0u32; n + 1]; { let mut d = 0u32; for i in 0..n { depth_at[i] = d; match ops[i].kind { PushCondition => d += 1, PopCondition => d = d.saturating_sub(1), _ => {} } } }
    let mut drop = vec![false; n]; let mut add: Vec<Vec<Op>> = vec![vec![]; n];
    let (_,nb,_,_) = analyze_ops(ops.iter());
    let mut contexts:Vec<Vec<(u64,u64)>>=Vec::with_capacity(n); let mut masks=Vec::with_capacity(n);
    let mut stack:Vec<Vec<(u64,u64)>>=vec![];let mut base:Vec<(u64,u64)>=vec![];let mut versions=vec![0u64;nb as usize];
    for op in ops {
        contexts.push(base.clone());let mut cond=base.clone();
        if op.c_condition!=NO_BIT {cond.push((op.c_condition.0,versions[op.c_condition.0 as usize]));cond.sort();cond.dedup();}
        masks.push(cond.clone());
        if matches!(op.kind,Hmr|BitStore0|BitStore1|BitInvert){versions[op.c_target.0 as usize]+=1;}
        if op.kind==PushCondition{stack.push(base);base=cond;}if op.kind==PopCondition{base=stack.pop().unwrap();}
    }
    let mut count = 0;
    let mut i = 0;
    while i + 6 < n {
        let o = &ops[i];
        if o.kind == CCX && o.c_condition == NO_BIT && fresh.contains(&(o.q_target.0, i)) {
            let (a, b, t) = (o.q_control1, o.q_control2, o.q_target);
            let c1 = &ops[i + 1];
            if c1.kind == CX && c1.q_control1 == t && c1.c_condition == NO_BIT {
                let u = c1.q_target;
                let mut j = i + 2; let mut diag = Vec::new(); let mut ok = true;
                while j < n && matches!(ops[j].kind, CZ | Z) && ops[j].c_condition == NO_BIT { let d = &ops[j]; if d.q_target == t || d.q_control1 == t || d.q_target == a || d.q_target == b || d.q_control1 == a || d.q_control1 == b { ok = false; break; } diag.push(j); j += 1; }
                if ok && j + 2 < n && ops[j].kind == CX && ops[j].q_control1 == t && ops[j].q_target == u && ops[j].c_condition == NO_BIT
                    && ops[j + 1].kind == Hmr && ops[j + 1].q_target == t && ops[j + 1].c_condition == NO_BIT {
                    let k = ops[j + 1].c_target;
                    let f = &ops[j + 2];
                    let fix_ok = f.kind == CZ && f.c_condition == k && ((f.q_control1 == a && f.q_target == b) || (f.q_control1 == b && f.q_target == a));
                    // k must not be read again before it is rewritten, and t only reset afterwards
                    let mut r_at = None; let mut kk_ok = fix_ok;
                    if fix_ok {
                        // t: untouched until an unconditioned R(t) within 64 ops
                        for m in j + 3..n.min(j + 64) { let q = &ops[m];
                            if q.q_target == t || q.q_control1 == t || q.q_control2 == t { if q.kind == R && q.q_target == t && q.c_condition == NO_BIT { r_at = Some(m); } else { kk_ok = false; } break; } }
                        // k: never read again (no condition, no push) before it is rewritten, scanning to the stream end
                        if !k_unread(ops, j + 3, k) { kk_ok = false; }
                    }
                    if kk_ok && r_at.is_some() && diag.iter().all(|&d| ops[d].q_target != u || ops[d].q_control1 != u) {
                        for d in &diag { let g = ops[*d];
                            let (p, has_u) = if g.kind == Z { (g.q_target, g.q_target == u) } else if g.q_target == u { (g.q_control1, true) } else if g.q_control1 == u { (g.q_target, true) } else { (g.q_target, false) };
                            if has_u { let mut e = Op::empty();
                                if g.kind == Z { e.kind = CZ; e.q_control1 = a; e.q_target = b; } else { e.kind = CCZ; e.q_control1 = a; e.q_control2 = b; e.q_target = p; }
                                add[*d].push(e); }
                        }
                        drop[i] = true; drop[i + 1] = true; drop[j] = true; drop[j + 1] = true; drop[j + 2] = true; drop[r_at.unwrap()] = true;
                        let origin=&masks[j+1];let mut writes:Vec<Vec<(u64,u64)>>=vec![];let mut bad=Vec::new();
                        for m in j+3..n {
                            let x=&ops[m];
                            if x.c_condition==k || (x.kind==BitInvert && x.c_target==k) {
                                let mut read=origin.clone();read.extend(contexts[m].iter().copied());read.sort();read.dedup();
                                if !writes.iter().any(|w|w.iter().all(|v|read.contains(v))){bad.push(m);}
                            }
                            if matches!(x.kind,Hmr|BitStore0|BitStore1)&&x.c_target==k {
                                if x.c_condition!=k {writes.push(masks[m].clone());}
                                if masks[m].iter().all(|v|origin.contains(v)){break;}
                            }
                        }
                        eprintln!("WD_PEEP_DOMINANCE start={} origin={:?} unproved_reads={:?}",i,origin,bad);
                        if !bad.is_empty(){for &m in bad.iter().take(4){eprintln!("WD_PEEP_READ {} {:?} context={:?}",m,ops[m],contexts[m]);}}
                        count += 1; i = j + 3; continue;
                    }
                }
            }
        }
        i += 1;
    }
    let mut out = Vec::with_capacity(n); let mut map = vec![0usize; n + 1];
    for i in 0..n { map[i] = out.len(); if !drop[i] { out.push(ops[i]); } out.extend(add[i].iter().cloned()); }
    map[n] = out.len();
    let nlog = log.iter().map(|&(q, o, a)| (q, map[o], a)).collect();
    (out, nlog, count)
}

/// Allocation audit: the builder sometimes hands out an id that still holds data (lent or parked wires). A small classical
/// 64-lane simulation (measurement outcomes 0; inputs pseudo-random) checks every allocation; any allocation that is not
/// |0> on some lane continues the wire's previous segment, so its release/alloc pair is dropped from the log.
fn audit_allocs(ops: &[Op], log: &[(u64, usize, bool)]) -> Vec<(u64, usize, bool)> {
    use OperationType::*;
    let (total_qubits, num_bits, _nr, regs) = analyze_ops(ops.iter());
    let n = ops.len();
    let mut at: Vec<Vec<usize>> = vec![vec![]; n + 1];
    for (k, &(_, o, a)) in log.iter().enumerate() { if a && o <= n { at[o].push(k); } }
    let mut dirty = vec![false; log.len()];
    for (si, seed0) in [0x9e3779b97f4a7c15u64, 0x243f6a8885a308d3, 0x13198a2e03707344, 0xa4093822299f31d0, 0x082efa98ec4e6c89, 0x452821e638d01377].into_iter().enumerate() {
        let mut rng = seed0 ^ 0x5555_5555_5555_5555;
        let mut q = vec![0u64; total_qubits as usize]; let mut bits = vec![0u64; num_bits as usize + 1];
        let mut seed = seed0;
        for r in &regs { for qb in r { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            match *qb { QubitOrBit::Qubit(x) => q[x.0 as usize] = seed, QubitOrBit::Bit(b) => bits[b.0 as usize] = seed } } }
        let mut stack: Vec<u64> = Vec::new(); let mut base = u64::MAX;
        for i in 0..=n {
            for &k in &at[i] { if q[log[k].0 as usize] != 0 { dirty[k] = true; } }
            if i == n { break; }
            let op = &ops[i];
            let mut cond = base; if op.c_condition != NO_BIT { cond &= bits[op.c_condition.0 as usize]; }
            let (c1, c2, t) = (op.q_control1.0 as usize, op.q_control2.0 as usize, op.q_target.0 as usize);
            match op.kind {
                CCX => { let v = cond & q[c1] & q[c2]; q[t] ^= v; }
                CX => { let v = cond & q[c1]; q[t] ^= v; }
                X => { q[t] ^= cond; }
                Swap => { let d = (q[c1] ^ q[t]) & cond; q[c1] ^= d; q[t] ^= d; }
                Hmr => { let b = op.c_target.0 as usize; rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                         let r = if si < 3 { 0 } else { rng }; bits[b] = (bits[b] & !cond) | (r & cond); q[t] &= !cond; }
                R => { q[t] &= !cond; }
                BitInvert => { bits[op.c_target.0 as usize] ^= cond; }
                BitStore0 => { bits[op.c_target.0 as usize] &= !cond; }
                BitStore1 => { bits[op.c_target.0 as usize] |= cond; }
                PushCondition => { stack.push(base); base &= bits[op.c_condition.0 as usize]; }
                PopCondition => { if let Some(v) = stack.pop() { base = v; } }
                _ => {}
            }
        }
    }
    let mut drop = vec![false; log.len()];
    let mut last_release: std::collections::HashMap<u64, usize> = std::collections::HashMap::new();
    let mut nd = 0usize;
    for (k, &(qq, _, a)) in log.iter().enumerate() {
        if !a { last_release.insert(qq, k); continue; }
        if dirty[k] { nd += 1; if let Some(&r) = last_release.get(&qq) { drop[r] = true; drop[k] = true; } }
    }
    eprintln!("LFW dirty_allocs={nd}");
    let unproved=wd_zero_support(ops,log,&dirty);
    let mut previous_release=std::collections::HashMap::new();let mut merged_unknown=0usize;
    for(k,&(q,_,a))in log.iter().enumerate(){if !a{previous_release.insert(q,k);}else if unproved[k]{if let Some(&r)=previous_release.get(&q){drop[r]=true;drop[k]=true;merged_unknown+=1;}}}
    eprintln!("WD_STRICT merged_unproved_allocations={merged_unknown}");
    log.iter().enumerate().filter(|(k, _)| !drop[*k]).map(|(_, &x)| x).collect()
}

pub fn apply(ops: Vec<Op>, log: &[(u64, usize, bool)], reacq: &[(u64, usize)], cap: usize, force: bool) -> (Vec<Op>, Report) {
    let _ = reacq; let log_m = audit_allocs(&ops, log);
    let (ops, log_owned) = { let (o, l, c) = peephole_phase_and(&ops, &log_m); eprintln!("LFW peephole_phase_and rewrites={c}"); (o, l) };
    let log = &log_owned[..];
    let n = ops.len();
    let (total_qubits, num_bits, _nr, regs) = analyze_ops(ops.iter());
    let nq = total_qubits as usize;
    let mut reg_q = vec![false; nq];
    let mut out_regs: Vec<u64> = Vec::new();
    for r in &regs[..2] { for qb in r { if let QubitOrBit::Qubit(q) = *qb { reg_q[q.0 as usize] = true; out_regs.push(q.0); } } }
    let segs = tight_segments(&ops, log);
    let mut wsegs: Vec<Vec<(usize, usize)>> = vec![vec![]; nq];
    for &(q, a, b) in &segs { wsegs[q as usize].push((a, b)); }
    for v in wsegs.iter_mut() { v.sort(); }
    let mut delta = vec![0i32; n + 1];
    for &(_, a, b) in &segs { delta[a] += 1; delta[b] -= 1; }
    { let mut c = 0i32; let mut mx = 0i32; let mut nmx = 0usize; for i in 0..n { c += delta[i]; if c > mx { mx = c; nmx = 0; } if c == mx { nmx += 1; } } eprintln!("LFW segment_overlap_max={mx} ops_at_max={nmx}"); }
    let cntv: Vec<i32> = { let mut c = 0i32; (0..n).map(|i| { c += delta[i]; c }).collect() };
    let multi = false; // multi-cover selection (research, for caps below 1213) is off in this build
    let mut runs = Vec::new();
    { let mut c = 0; let mut st = None; for i in 0..n { c += delta[i]; if c as usize > cap { if st.is_none() { st = Some(i); } } else if let Some(x) = st.take() { runs.push((x, i)); } } if let Some(x) = st { runs.push((x, n)); } }
    // esc[p]: ops can be inserted before op p, escaping any open condition blocks by Pop.. ops ..re-Push, when every stacked
    // condition bit is unwritten since its push (a re-push then captures the same value)
    let mut depth0 = vec![false; n + 1];
    { let mut st: Vec<(u64, bool)> = Vec::new();
      for i in 0..n { depth0[i] = st.iter().all(|x| !x.1);
        let op = &ops[i];
        match op.kind { OperationType::PushCondition => st.push((op.c_condition.0, false)), OperationType::PopCondition => { st.pop(); }, _ => {} }
        if matches!(op.kind, OperationType::Hmr | OperationType::BitStore0 | OperationType::BitStore1 | OperationType::BitInvert) { for x in st.iter_mut() { if x.0 == op.c_target.0 { x.1 = true; } } } }
      depth0[n] = st.iter().all(|x| !x.1); }
    let mut tl: Vec<Vec<u32>> = vec![vec![]; nq]; let mut gl: Vec<Vec<u32>> = vec![vec![]; nq];
    for (i, op) in ops.iter().enumerate() {
        for q in touched(op) { if q != u64::MAX { let v = &mut tl[q as usize]; if v.last() != Some(&(i as u32)) { v.push(i as u32); } } }
        for q in targets(op) { if q != u64::MAX { gl[q as usize].push(i as u32); } }
    }
    let next_in = |v: &Vec<u32>, i: usize| -> usize { let k = v.partition_point(|&x| (x as usize) < i); if k < v.len() { v[k] as usize } else { n } };
    let prev_in = |v: &Vec<u32>, i: usize| -> Option<usize> { let k = v.partition_point(|&x| (x as usize) < i); if k > 0 { Some(v[k - 1] as usize) } else { None } };
    // tracker: variables are qubits 0..nq and classical bits nq..nq+num_bits
    let nv = nq + num_bits as usize;
    let nqu = nq as u32;
    gl.resize(nv, vec![]);
    for (i, op) in ops.iter().enumerate() {
        if matches!(op.kind, OperationType::Hmr | OperationType::BitStore0 | OperationType::BitStore1 | OperationType::BitInvert) && op.c_target != NO_BIT { gl[nq + op.c_target.0 as usize].push(i as u32); }
    }
    fn reg(refs: &mut Vec<Vec<u32>>, d: &Def, q: u32) { for y in d.wires() { refs[y as usize].push(q); } }
    // the builder's release claim: a wire is |0> before the first touch of each of its segments
    let mut seg_first: Vec<Vec<u32>> = vec![vec![]; n + 1];
    for &(q, a, _) in &segs { if a > 0 { seg_first[a].push(q as u32); } }
    let mut blacklist: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();
    let mut limits: std::collections::HashMap<(usize, usize), usize> = std::collections::HashMap::new();
    let mut pass = 0usize;
    let (mut covers, uncovered, why_tot, nw_tot, nfailed) = loop {
    let mut def: Vec<Option<Def>> = (0..nq).map(|q| if reg_q[q] { None } else { Some(Def::default()) }).collect();
    let mut refs: Vec<Vec<u32>> = vec![vec![]; nv];
    let mut nwhy: Vec<u8> = (0..nq).map(|q| if reg_q[q] { 1 } else { 0 }).collect(); let mut nw_tot = [0usize; 10];
    let mut stack: Vec<u32> = Vec::new(); let mut stack_dirty: Vec<bool> = Vec::new();
    let mut covers: Vec<Cover> = Vec::new();
    let mut uncovered = Vec::new();
    let mut why_tot = [0usize; 8];
    let mut rk = 0usize; let mut need_at = usize::MAX; let mut cur_end = 0usize;
    let mut pending: Vec<(usize, usize, Def, usize, usize)> = Vec::new(); // (erase_at, w, def at erase, deadline, cover end)
    let mut erased = vec![false; nq];
    let mut failed: Vec<(usize, usize)> = Vec::new(); let mut died: Vec<((usize, usize), usize)> = Vec::new(); let mut last_tr: Option<Def> = None;
    for i in 0..n {
        for &w in &seg_first[i] {
            if !erased[w as usize] && !matches!(&def[w as usize], Some(d) if d.is_zero()) {
                let mut rs = std::mem::take(&mut refs[w as usize]); rs.sort_unstable(); rs.dedup();
                for q in rs { if let Some(d) = def[q as usize].as_mut() { if d.mentions(w) {
                    let z: Option<Def> = Some(Def::default());
                    if !(inline_into(d, w, &z) && d.normalize()) { def[q as usize] = None; nwhy[q as usize] = 9; } } } }
                def[w as usize] = Some(Def::default());
            }
        }
        // finalize pending covers: recompute at the first escapable point after the cover end where w's current definition is usable
        let mut fin_now: Vec<usize> = Vec::new();
        let mut k = 0;
        while k < pending.len() {
            let (ps, w, _, dl, cend) = (pending[k].0, pending[k].1, (), pending[k].3, pending[k].4);
            if def[w].is_none() { pending.swap_remove(k); died.push(((w, ps), i - 1)); erased[w] = false; continue; }
            if multi {
                let ok = depth0[i] && match &def[w] { Some(d) => !d.mentions(w as u32) && d.emittable(nqu) && d.wires().iter().all(|&y| y >= nqu || y as usize == w || !erased[y as usize]), None => false };
                let n_er = pending.len() as i32; // still erased, this one included
                let afford = cntv[i] - (n_er - 1) <= cap as i32;
                if ok && (afford || i >= dl) { let p = pending.swap_remove(k); covers.push((p.0, i, w, p.2, def[w].clone().unwrap())); fin_now.push(w); continue; }
                if i >= dl { pending.swap_remove(k); failed.push((w, ps)); erased[w] = false; continue; }
                k += 1; continue;
            }
            if i >= cend {
                let ok = depth0[i] && match &def[w] { Some(d) => !d.mentions(w as u32) && d.emittable(nqu) && d.wires().iter().all(|&y| y >= nqu || y as usize == w || !erased[y as usize]), None => false };
                if ok { let p = pending.swap_remove(k); covers.push((p.0, i, w, p.2, def[w].clone().unwrap())); fin_now.push(w); continue; }
                if i >= dl { pending.swap_remove(k); failed.push((w, ps)); erased[w] = false; continue; }
            }
            k += 1;
        }
        if rk < runs.len() && runs[rk].0 == i { need_at = i; cur_end = runs[rk].1; rk += 1; }
        let mut deficit = if multi { cntv[i] - pending.len() as i32 - cap as i32 } else { 0 };
        while multi && deficit > 0 {
            let mut best: Option<(usize, usize, usize)> = None; // (deadline, cost, w)
            if depth0[i] { for w in 0..nq {
                let Some(v) = &def[w] else { continue };
                if v.is_zero() || v.mentions(w as u32) || !v.emittable(nqu) || erased[w] || blacklist.contains(&(w, i)) { continue; }
                let ws = &wsegs[w]; let kk = ws.partition_point(|x| x.0 <= i); if kk == 0 { continue; } let (sa, sb) = ws[kk - 1]; if !(sa < i && i < sb) { continue; }
                let dl = next_in(&tl[w], i).min(sb - 1).min(*limits.get(&(w, i)).unwrap_or(&usize::MAX));
                if dl <= i { continue; }
                if v.wires().iter().any(|&y| y < nqu && erased[y as usize]) { continue; }
                if covers.iter().rev().take(64).any(|c| c.1 == i && c.4.mentions(w as u32)) { continue; }
                let cost = v.cost(nqu);
                if best.map_or(true, |b| (dl, usize::MAX - cost) > (b.0, usize::MAX - b.1)) { best = Some((dl, cost, w)); }
            } }
            match best { Some((dl, _, w)) => { pending.push((i, w, def[w].clone().unwrap(), dl, dl)); erased[w] = true; deficit -= 1; }
                         None => { uncovered.push(i); break; } }
        }
        if !multi && i == need_at && i < cur_end {
            let mut best: Option<(usize, usize, usize, usize)> = None; // (cover end, cost, w, deadline)
            let mut why = [0usize; 8];
            if depth0[i] { for w in 0..nq {
                let Some(v) = &def[w] else { why[0] += 1; continue };
                if v.is_zero() { why[1] += 1; continue; }
                if v.mentions(w as u32) || !v.emittable(nqu) { why[2] += 1; continue; }
                if erased[w] || blacklist.contains(&(w, i)) { why[7] += 1; continue; }
                let ws = &wsegs[w]; let kk = ws.partition_point(|x| x.0 <= i); if kk == 0 { why[5] += 1; continue; } let (sa, sb) = ws[kk - 1]; if !(sa < i && i < sb) { why[5] += 1; continue; }
                let dl = next_in(&tl[w], i).min(sb - 1).min(*limits.get(&(w, i)).unwrap_or(&usize::MAX));
                if dl <= i { why[4] += 1; continue; }
                if v.wires().iter().any(|&y| y < nqu && erased[y as usize]) { why[3] += 1; continue; }
                if covers.iter().rev().take(64).any(|c| c.1 == i && c.4.mentions(w as u32)) { why[7] += 1; continue; }
                let cost = v.cost(nqu);
                let cend = dl.min(cur_end);
                if best.map_or(true, |b| (cend, usize::MAX - cost) > (b.0, usize::MAX - b.1)) { best = Some((cend, cost, w, dl)); }
            } } else { why[6] += 1; }
            match best {
                Some((cend, _cost, w, dl)) => { pending.push((i, w, def[w].clone().unwrap(), dl, cend)); erased[w] = true; need_at = cend; }
                None => { 
                    for q in 0..nq { if def[q].is_none() { nw_tot[nwhy[q] as usize] += 1; } } uncovered.push(i); need_at = i + 1; for k in 0..8 { why_tot[k] += why[k]; } }
            }
        }
        for w in fin_now { erased[w] = false; }
        // --- update definitions for op i ---
        let op = &ops[i];
        use OperationType::*;
        match op.kind {
            PushCondition => { stack.push(nqu + op.c_condition.0 as u32); stack_dirty.push(false); continue; }
            PopCondition => { stack.pop(); stack_dirty.pop(); continue; }
            _ => {}
        }
        let mut cv: Vec<u32> = stack.clone(); if op.c_condition != NO_BIT { cv.push(nqu + op.c_condition.0 as u32); } cv.sort_unstable(); cv.dedup();
        // a pushed condition holds the bit's value at push time: once that bit is rewritten inside its block, the block's
        // condition is no longer a tracked variable, so every op under it is opaque (two dummy entries force Delta::Opaque)
        let stale = stack_dirty.iter().any(|&d| d);
        if stale { cv.push(u32::MAX - 1); cv.push(u32::MAX - 2); }
        if matches!(op.kind, Hmr | BitStore0 | BitStore1 | BitInvert) && op.c_target != NO_BIT { let bv = nqu + op.c_target.0 as u32; for (k, &sv) in stack.iter().enumerate() { if sv == bv { stack_dirty[k] = true; } } }
        // a classical bit write kills every definition reading that bit
        if matches!(op.kind, Hmr | BitStore0 | BitStore1 | BitInvert) && op.c_target != NO_BIT {
            let bv = nqu + op.c_target.0 as u32;
            let mut rs = std::mem::take(&mut refs[bv as usize]); rs.sort_unstable(); rs.dedup();
            for q in rs { if let Some(d) = &def[q as usize] { if d.mentions(bv) { def[q as usize] = None; nwhy[q as usize] = 7; } } }
        }
        if op.kind == Swap {
            let (a, b) = (op.q_control1.0 as u32, op.q_target.0 as u32);
            let mut rs: Vec<u32> = refs[a as usize].iter().chain(refs[b as usize].iter()).cloned().collect(); rs.sort_unstable(); rs.dedup();
            if !cv.is_empty() {
                // inline a and b into every reader, then both become unknown
                for x in [a, b] { let dx = def[x as usize].clone();
                    for &q in &rs { if q == a || q == b { continue; } let Some(d) = def[q as usize].as_mut() else { continue }; if !d.mentions(x) { continue; }
                        if !inline_into(d, x, &dx) || d.mentions(q) { def[q as usize] = None; nwhy[q as usize] = 4; } else if let Some(dx) = &dx { for y in dx.wires() { refs[y as usize].push(q); } } } }
                def[a as usize] = None; def[b as usize] = None; nwhy[a as usize] = 2; nwhy[b as usize] = 2;
            } else {
                def.swap(a as usize, b as usize); refs.swap(a as usize, b as usize);
                rs.push(a); rs.push(b);
                for q in rs { if let Some(d) = def[q as usize].as_mut() { d.lin.rename(a, b); for (x, y) in d.ands.iter_mut() { x.rename(a, b); y.rename(a, b); } for (m, x, y) in d.cands.iter_mut() { if *m == a { *m = b; } else if *m == b { *m = a; } x.rename(a, b); y.rename(a, b); } for (x, y, z) in d.tris.iter_mut() { x.rename(a, b); y.rename(a, b); z.rename(a, b); } } }
                for q in [a, b] { if let Some(d) = def[q as usize].clone() { reg(&mut refs, &d, q); } }
            }
            continue;
        }
        let x = match op.kind { X | CX | CCX | Hmr | R => op.q_target.0 as u32, _ => continue };
        // the change x_new = x_old ^ delta, when representable: Lin(form) or Pair(form, form)
        enum Delta { Lin(Form), Pair(Form, Form), CPair(u32, Form, Form), Opaque }
        let delta = match (op.kind, cv.len()) {
            (X, 0) => Delta::Lin(Form { w: vec![], c: true }),
            (CX, 0) => Delta::Lin(Form::one(op.q_control1.0 as u32)),
            (CCX, 0) => Delta::Pair(Form::one(op.q_control1.0 as u32), Form::one(op.q_control2.0 as u32)),
            (X, 1) => Delta::Lin(Form::one(cv[0])),
            (CX, 1) => Delta::Pair(Form::one(cv[0]), Form::one(op.q_control1.0 as u32)),
            (CCX, 1) => Delta::CPair(cv[0], Form::one(op.q_control1.0 as u32), Form::one(op.q_control2.0 as u32)),
            _ => Delta::Opaque,
        };
        let dx = def[x as usize].clone();
        let mut rs = std::mem::take(&mut refs[x as usize]); rs.sort_unstable(); rs.dedup();
        let mut keep = Vec::with_capacity(rs.len());
        for q in rs {
            if q == x { continue; }
            let Some(d) = def[q as usize].as_mut() else { continue };
            if !d.mentions(x) { continue; }
            let in_and = d.in_product(x);
            let mut ok; let mut reason = 3u8;
            match &delta {
                Delta::Lin(l) => { if d.lin.has(x) { d.lin.xor(l); } for (p, r) in d.ands.iter_mut() { if p.has(x) { p.xor(l); } if r.has(x) { r.xor(l); } }
                    for (_, p, r) in d.cands.iter_mut() { if p.has(x) { p.xor(l); } if r.has(x) { r.xor(l); } }
                    for (p, r, t) in d.tris.iter_mut() { if p.has(x) { p.xor(l); } if r.has(x) { r.xor(l); } if t.has(x) { t.xor(l); } } for &y in &l.w { refs[y as usize].push(q); } ok = true; }
                Delta::CPair(m, p, r) if !in_and => { d.push_cand(*m, p.clone(), r.clone()); refs[*m as usize].push(q); for &y in p.w.iter().chain(r.w.iter()) { refs[y as usize].push(q); } ok = true; }
                Delta::Pair(p, r) if !in_and => { d.push_and(p.clone(), r.clone()); for &y in p.w.iter().chain(r.w.iter()) { refs[y as usize].push(q); } ok = true; }
                Delta::Pair(p, r) if p.w.len() == 1 && p.w[0] >= nqu && !p.c && r.w.iter().all(|&y| y < nqu) && d.cands.iter().all(|(m, a, b)| !(a.has(x) || b.has(x)) || *m == p.w[0]) && !d.in_tri(x) => {
                    // x_old = x_new ^ m.C with m a condition bit: expand every product holding x (m.m = m keeps it quadratic)
                    let m = p.w[0]; let cf = r.clone();
                    let delta_lin = d.lin.has(x);
                    let ands = std::mem::take(&mut d.ands); let cands = std::mem::take(&mut d.cands);
                    if delta_lin { d.push_and(Form::one(m), cf.clone()); }
                    for (a, b) in ands { let (xa, xb) = (a.has(x), b.has(x));
                        if xa { d.push_cand(m, cf.clone(), b.clone()); } if xb { d.push_cand(m, a.clone(), cf.clone()); } if xa && xb { d.push_and(Form::one(m), cf.clone()); }
                        d.push_and(a, b); }
                    for (mm, a, b) in cands { let (xa, xb) = (a.has(x), b.has(x));
                        if xa { d.push_cand(mm, cf.clone(), b.clone()); } if xb { d.push_cand(mm, a.clone(), cf.clone()); } if xa && xb { d.push_and(Form::one(mm), cf.clone()); }
                        d.push_cand(mm, a, b); }
                    refs[m as usize].push(q); for &y in &cf.w { refs[y as usize].push(q); }
                    ok = true; }
                _ => { ok = inline_into(d, x, &dx); reason = 4; if ok { if let Some(dx) = &dx { for y in dx.wires() { refs[y as usize].push(q); } } } }
            }
            if ok && !d.normalize() { ok = false; reason = 6; }
            if ok { if d.mentions(x) { keep.push(q); } } else { def[q as usize] = None; nwhy[q as usize] = reason; }
        }
        refs[x as usize].extend(keep);
        // inverse relation: after CX(c, x) with x_old = D, c = x_new ^ D (a definition for c when its own is unknown or dearer)
        if op.kind == CX && cv.is_empty() {
            let c = op.q_control1.0 as u32;
            if let Some(dd) = &dx { if !dd.mentions(c) && !dd.mentions(x) {
                let mut nd = dd.clone(); nd.lin.toggle(x);
                let better = match &def[c as usize] { None => true, Some(o) => o.mentions(c) || !o.emittable(nqu) || nd.cost(nqu) < o.cost(nqu) };
                if better && nd.normalize() && !reg_q[c as usize] { reg(&mut refs, &nd, c); def[c as usize] = Some(nd); }
            } }
        }
        // x's own definition
        let xi = x as usize;
        match (op.kind, &delta) {
            (Hmr | R, _) => { if cv.is_empty() { def[xi] = Some(Def::default()); } else { def[xi] = None; nwhy[xi] = 2; } }
            (_, Delta::Lin(l)) => if let Some(d) = def[xi].as_mut() { d.lin.xor(l); for &y in &l.w { refs[y as usize].push(x); } },
            (_, Delta::Pair(p, r)) => if let Some(d) = def[xi].as_mut() { d.push_and(p.clone(), r.clone()); for &y in p.w.iter().chain(r.w.iter()) { refs[y as usize].push(x); } },
            (_, Delta::CPair(m, p, r)) => if let Some(d) = def[xi].as_mut() { d.push_cand(*m, p.clone(), r.clone()); refs[*m as usize].push(x); for &y in p.w.iter().chain(r.w.iter()) { refs[y as usize].push(x); } },
            _ => { def[xi] = None; nwhy[xi] = 2; }
        }
        if let Some(d) = def[xi].as_mut() { if !d.normalize() || d.mentions(x) { def[xi] = None; nwhy[xi] = 6; } }
    }
    // stream end: any pending cover still open fails
    for p in pending.drain(..) { failed.push((p.1, p.0)); }
    eprintln!("LFW pass {pass}: covers={} uncovered={} failed={} died={}", covers.len(), uncovered.len(), failed.len(), died.len());
    if (failed.is_empty() && died.is_empty()) || pass >= 12 { break (covers, uncovered, why_tot, nw_tot, failed.len() + died.len()); }
    blacklist.extend(failed.iter().cloned());
    for (key, lim) in died { let e = limits.entry(key).or_insert(lim); if lim < *e { *e = lim; } }
    pass += 1;
    };
    eprintln!("LFW_NONE_WHY [0?, register, opaque own op, -, inline failed, -, size cap, bit rewritten, self ref, -] = {:?}", nw_tot);
    eprintln!("LFW_WHY total over uncovered decisions [unknown, zero, self/unemittable, form wire targeted before, touched in window, outside seg, empty window, conflict] = {:?}", why_tot);
    let run_ops: usize = runs.iter().map(|r| r.1 - r.0).sum();
    let mut rep = Report { runs: runs.len(), run_ops, covers: covers.len(), ccx_added: 0, uncovered: uncovered.clone(), max_id: 0 };
    if (!uncovered.is_empty() || nfailed > 0) && !force { return (ops, rep); }
    covers.sort_by_key(|c| (c.2, c.0));
    let mut merged: Vec<Cover> = Vec::new();
    for c in covers { merged.push(c); }
    // insertion
    let mbit = BitId(num_bits);
    let mut ins: Vec<Vec<(bool, usize, usize)>> = vec![vec![]; n + 1];
    for (ci, c) in merged.iter().enumerate() { ins[c.0].push((false, ci, c.2)); ins[c.1].push((true, ci, c.2)); }
    let mk = |kind: OperationType, c1: u64, c2: u64, t: u64, cond: BitId| { let mut o = Op::empty(); o.kind = kind; o.q_control1 = QubitId(c1); o.q_control2 = QubitId(c2); o.q_target = QubitId(t); o.c_condition = cond; o };
    // a wire is usable at insertion point p only inside one of its segments (a < p < b); outside it is |0>, so it drops out of the form
    let nqu = nq as u32;
    let live_at = |c: u32, p: usize| -> bool { let ws = &wsegs[c as usize]; let k = ws.partition_point(|x| x.0 < p); k > 0 && p < ws[k - 1].1 };
    let mut dropped = 0usize;
    let form_on = |f: &Form, h: u32, out: &mut Vec<Op>| { for &y in &f.w { if y != h { out.push(mk(OperationType::CX, y as u64, u64::MAX, h as u64, NO_BIT)); } } if f.c { out.push(mk(OperationType::X, u64::MAX, u64::MAX, h as u64, NO_BIT)); } };
    let mut new_ops: Vec<Op> = Vec::with_capacity(n + merged.len() * 16);
    let mut newpos = vec![0usize; n + 1];
    let mut gaps: Vec<Vec<(usize, usize)>> = vec![vec![]; nq];
    let mut gap_open: Vec<usize> = vec![usize::MAX; nq]; let mut gapped_now = vec![false; nq];
    let mut estack: Vec<u64> = Vec::new();
    for i in 0..=n {
        let mut list = std::mem::take(&mut ins[i]);
        list.sort_by_key(|x| x.0); // erases first
        if !list.is_empty() { for _ in 0..estack.len() { let mut o = Op::empty(); o.kind = OperationType::PopCondition; new_ops.push(o); } }
        let had = !list.is_empty();
        for (is_re, ci, w) in list {
            let p = i;
            let mut d = if is_re { merged[ci].4.clone() } else { merged[ci].3.clone() };
            let before = d.wires().len();
            let filt = |f: &mut Form| f.w.retain(|&y| y >= nqu || live_at(y, p));
            filt(&mut d.lin); for (a, b) in d.ands.iter_mut() { filt(a); filt(b); } for (_, a, b) in d.cands.iter_mut() { filt(a); filt(b); } for (a, b, c) in d.tris.iter_mut() { filt(a); filt(b); filt(c); }
            dropped += before - d.wires().len();
            assert!(d.normalize() && d.emittable(nqu), "lfw: definition not emittable after filtering");
            let w64 = w as u64;
            let cond_of = |y: u32| BitId((y - nqu) as u64);
            // linear part and bit pairs: XOR them into w (same ops erase and recompute)
            let lin_ops = |d: &Def, out: &mut Vec<Op>| {
                for &y in &d.lin.w { if y < nqu { out.push(mk(OperationType::CX, y as u64, u64::MAX, w64, NO_BIT)); } else { out.push(mk(OperationType::X, u64::MAX, u64::MAX, w64, cond_of(y))); } }
                if d.lin.c { out.push(mk(OperationType::X, u64::MAX, u64::MAX, w64, NO_BIT)); }
                for (a, b) in &d.ands {
                    let (m, f) = if Def::bitpair(a, b, nqu) { (a.w[0], b) } else if Def::bitpair(b, a, nqu) { (b.w[0], a) } else { continue };
                    let h = f.w[0]; form_on(f, h, out); out.push(mk(OperationType::CX, h as u64, u64::MAX, w64, cond_of(m))); form_on(f, h, out);
                }
            };
            let qq: Vec<&(Form, Form)> = d.ands.iter().filter(|(a, b)| Def::qonly(a, nqu) && Def::qonly(b, nqu)).collect();
            if !is_re {
                lin_ops(&d, &mut new_ops);
                if !qq.is_empty() || !d.cands.is_empty() || !d.tris.is_empty() {
                    let mut h = Op::empty(); h.kind = OperationType::Hmr; h.q_target = QubitId(w64); h.c_target = mbit; new_ops.push(h);
                    for (a, b, c) in &d.tris { let (ha, hb, hc) = Def::hosts3(a, b, c).unwrap();
                        form_on(a, ha, &mut new_ops); form_on(b, hb, &mut new_ops); form_on(c, hc, &mut new_ops);
                        new_ops.push(mk(OperationType::CCZ, ha as u64, hb as u64, hc as u64, mbit));
                        form_on(c, hc, &mut new_ops); form_on(b, hb, &mut new_ops); form_on(a, ha, &mut new_ops); }
                    for (m, a, b) in &d.cands { let (ha, hb) = Def::hosts(a, b).unwrap();
                        form_on(a, ha, &mut new_ops); form_on(b, hb, &mut new_ops);
                        let mut pu = Op::empty(); pu.kind = OperationType::PushCondition; pu.c_condition = cond_of(*m); new_ops.push(pu);
                        new_ops.push(mk(OperationType::CZ, ha as u64, u64::MAX, hb as u64, mbit));
                        let mut po = Op::empty(); po.kind = OperationType::PopCondition; new_ops.push(po);
                        form_on(b, hb, &mut new_ops); form_on(a, ha, &mut new_ops); }
                    for (a, b) in &qq { let (ha, hb) = Def::hosts(a, b).unwrap();
                        form_on(a, ha, &mut new_ops); form_on(b, hb, &mut new_ops);
                        new_ops.push(mk(OperationType::CZ, ha as u64, u64::MAX, hb as u64, mbit));
                        form_on(b, hb, &mut new_ops); form_on(a, ha, &mut new_ops); }
                }
                gap_open[w] = new_ops.len(); gapped_now[w] = true;
            } else {
                gaps[w].push((gap_open[w], new_ops.len())); gapped_now[w] = false;
                lin_ops(&d, &mut new_ops);
                for (a, b) in &qq { let (ha, hb) = Def::hosts(a, b).unwrap();
                    form_on(a, ha, &mut new_ops); form_on(b, hb, &mut new_ops);
                    new_ops.push(mk(OperationType::CCX, ha as u64, hb as u64, w64, NO_BIT)); rep.ccx_added += 1;
                    form_on(b, hb, &mut new_ops); form_on(a, ha, &mut new_ops); }
                for (a, b, c) in &d.tris { let (ha, hb, hc) = Def::hosts3(a, b, c).unwrap();
                    // w ^= a.b.c through a doubly controlled toggle on a borrowed live wire dd (restored)
                    let dd = (0..nqu).find(|&y| y != w as u32 && y != ha && y != hb && y != hc && !gapped_now[y as usize] && live_at(y, p)).expect("lfw: no dirty wire");
                    form_on(a, ha, &mut new_ops); form_on(b, hb, &mut new_ops); form_on(c, hc, &mut new_ops);
                    new_ops.push(mk(OperationType::CCX, hc as u64, dd as u64, w64, NO_BIT));
                    new_ops.push(mk(OperationType::CCX, ha as u64, hb as u64, dd as u64, NO_BIT));
                    new_ops.push(mk(OperationType::CCX, hc as u64, dd as u64, w64, NO_BIT));
                    new_ops.push(mk(OperationType::CCX, ha as u64, hb as u64, dd as u64, NO_BIT)); rep.ccx_added += 4;
                    form_on(c, hc, &mut new_ops); form_on(b, hb, &mut new_ops); form_on(a, ha, &mut new_ops); }
                for (m, a, b) in &d.cands { let (ha, hb) = Def::hosts(a, b).unwrap();
                    form_on(a, ha, &mut new_ops); form_on(b, hb, &mut new_ops);
                    new_ops.push(mk(OperationType::CCX, ha as u64, hb as u64, w64, cond_of(*m))); rep.ccx_added += 1;
                    form_on(b, hb, &mut new_ops); form_on(a, ha, &mut new_ops); }
            }
        }
        if had { for &b in &estack { let mut o = Op::empty(); o.kind = OperationType::PushCondition; o.c_condition = BitId(b); new_ops.push(o); } }
        newpos[i] = new_ops.len();
        if i < n { new_ops.push(ops[i]);
            match ops[i].kind { OperationType::PushCondition => estack.push(ops[i].c_condition.0), OperationType::PopCondition => { estack.pop(); }, _ => {} } }
    }
    eprintln!("LFW dropped_zero_wires={dropped} merged_covers={}", merged.len());
    // pieces: original segments mapped to new indices, split at gaps
    let nn = new_ops.len();
    let mut pieces: Vec<(usize, usize, u64)> = Vec::new();
    for &(q, a, b) in &segs {
        let (na, nb) = (if a == 0 { 0 } else { newpos[a] }, if b == n { nn } else { newpos[b - 1] + 1 });
        let mut st = na;
        let mut gs: Vec<(usize, usize)> = gaps[q as usize].iter().cloned().filter(|g| g.0 > na && g.1 < nb).collect();
        gs.sort();
        for (ge, gr) in gs { pieces.push((st, ge, q)); st = gr; }
        pieces.push((st, nb, q));
    }
    pieces.sort();
    for p in &pieces { assert!(p.0 <= p.1, "lfw: inverted piece {:?}", p); }
    let mut starts_at: Vec<Vec<usize>> = vec![vec![]; nn + 1];
    let mut ends_at: Vec<Vec<usize>> = vec![vec![]; nn + 1];
    for (pi, p) in pieces.iter().enumerate() { starts_at[p.0].push(pi); ends_at[p.1].push(pi); }
    let mut free: BTreeSet<u64> = (0..(if force { nq + 64 } else { cap }) as u64).collect();
    // register ids stay reserved until their register's first piece takes them: the declarations must keep their ids
    let mut reserved: std::collections::HashSet<u64> = out_regs.iter().cloned().collect();
    for r in &reserved { free.remove(r); }
    let mut colour = vec![u64::MAX; pieces.len()];
    let mut cur: Vec<u64> = vec![u64::MAX; nq];
    let mut out: Vec<Op> = Vec::with_capacity(nn + 2048);
    let mut over = false; let mut active_piece = vec![false; nq]; let mut outside = 0usize; let mut end_swaps = 0usize;
    let t_reg = new_ops.iter().position(|o| matches!(o.kind, OperationType::Register | OperationType::AppendToRegister)).unwrap_or(nn);
    assert!(new_ops[t_reg..].iter().all(|o| matches!(o.kind, OperationType::Register | OperationType::AppendToRegister)), "lfw: register declarations are not a trailing block");
    for t in 0..=nn {
        for &pi in &ends_at[t] { free.insert(colour[pi]); active_piece[pieces[pi].2 as usize] = false; }
        for &pi in &starts_at[t] {
            let q = pieces[pi].2; active_piece[q as usize] = true;
            let c = if reserved.remove(&q) { q } else if free.contains(&q) { q } else if let Some(&c) = free.iter().next() { c } else { over = true; u64::MAX };
            free.remove(&c); colour[pi] = c; cur[q as usize] = c;
        }
        if t == t_reg {
            // put every register value back on its own id before the trailing declarations
            let mut phys_of: Vec<u64> = cur.clone();
            let mut log_at: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
            for &r in &out_regs { log_at.insert(phys_of[r as usize], r); }
            for &r in &out_regs {
                let p = phys_of[r as usize];
                if p == r { continue; }
                let mut o = Op::empty(); o.kind = OperationType::Swap; o.q_control1 = QubitId(p); o.q_target = QubitId(r); out.push(o); end_swaps += 1;
                if let Some(&other) = log_at.get(&r) { phys_of[other as usize] = p; log_at.insert(p, other); } else { log_at.remove(&p); }
                phys_of[r as usize] = r; log_at.insert(r, r);
            }
        }
        if t < nn && matches!(new_ops[t].kind, OperationType::Register | OperationType::AppendToRegister) { assert!(t >= t_reg); out.push(new_ops[t]); continue; }
        if t < nn {
            let mut o = new_ops[t];
            for f in [&mut o.q_control1, &mut o.q_control2, &mut o.q_target] { if f.0 != u64::MAX { let c = cur[f.0 as usize]; f.0 = if c == u64::MAX { f.0 } else { c }; } }
            out.push(o);
        }
    }
    eprintln!("LFW outside_touches={outside}");
    assert!(!over, "lfw: recolour ran out of ids");
    eprintln!("LFW end_swaps={end_swaps}");
    let (tq, _, _, _) = analyze_ops(out.iter());
    rep.max_id = tq;
    (out, rep)
}

/// research: final output registers and ancillas of two streams on the same lanes, zero measurement outcomes
pub fn final_check(a: &[Op], b: &[Op], tag: &str) {
    let (qa, ba, _, regs) = analyze_ops(a.iter());
    let (qb, bb, _, _) = analyze_ops(b.iter());
    let nq = qa.max(qb) as usize; let nb = ba.max(bb) as usize + 1;
    let init = |sim: &mut crate::sim::Simulator<ZeroXof>| { let mut seed = 0x9e3779b97f4a7c15u64;
        for r in &regs { for qb in r { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            match *qb { QubitOrBit::Qubit(q) => *sim.qubit_mut(q) = seed, QubitOrBit::Bit(b) => *sim.bit_mut(b) = seed } } } };
    let mut x1 = ZeroXof; let mut s1 = crate::sim::Simulator::new(nq, nb, &mut x1); init(&mut s1); s1.apply_iter(a.iter());
    let mut x2 = ZeroXof; let mut s2 = crate::sim::Simulator::new(nq, nb, &mut x2); init(&mut s2); s2.apply_iter(b.iter());
    let mut bad = 0; for r in &regs[..2] { for qb in r { if let QubitOrBit::Qubit(q) = *qb { if s1.qubit(q) != s2.qubit(q) { bad += 1; } } } }
    eprintln!("LFW_FINAL2 {tag}: bad_output_qubits={bad} phase_a={:x} phase_b={:x}", s1.phase, s2.phase);
}

// Reviewer-only conservative support analysis. No sampled inference and no changes to emitted operations.
fn wd_zero_support(ops:&[Op],log:&[(u64,usize,bool)],dirty:&[bool])->Vec<bool> {
 use OperationType::*;
 type Term=Vec<(u64,u64)>; type Support=Vec<Term>;
 fn product(a:&Support,b:&Support)->Support {
  let mut z=Vec::new(); for x in a {for y in b {let mut t=x.clone();t.extend(y.iter().cloned());t.sort();t.dedup();z.push(t);if z.len()>64{return vec![vec![]]}}} reduce(z)
 }
 fn reduce(mut a:Support)->Support {a.sort_by_key(|x|x.len());let mut z:Support=vec![];for t in a {if !z.iter().any(|u|u.iter().all(|x|t.contains(x))){z.push(t);}if z.len()>64{return vec![vec![]]}}z}
 fn union(mut a:Support,b:Support)->Support {a.extend(b);reduce(a)}
 let(nq,nb,_,regs)=analyze_ops(ops.iter()); let mut q:Vec<Support>=vec![vec![];nq as usize];
 for r in regs {for v in r {if let QubitOrBit::Qubit(x)=v {q[x.0 as usize]=vec![vec![]];}}}
 let mut versions=vec![0u64;nb as usize];let mut stack:Vec<Term>=vec![];let mut base:Term=vec![];
 let mut at=vec![vec![];ops.len()+1];for(k,&(_,i,a))in log.iter().enumerate(){if a&&!dirty[k]{at[i].push(k);}}
 let(mut proved,mut unproved)=(0usize,0usize);let mut unproved_mask=vec![false;log.len()];
 for i in 0..=ops.len(){
  for &k in &at[i] {if i==0{continue;} if q[log[k].0 as usize].is_empty(){proved+=1}else{unproved+=1;unproved_mask[k]=true;if unproved<=12{eprintln!("WD_ZERO_UNPROVEN log={} q={} op={} support={:?}",k,log[k].0,i,q[log[k].0 as usize]);}}}
  if i==ops.len(){break;}let o=&ops[i];let mut cond=base.clone();if o.c_condition!=NO_BIT {cond.push((o.c_condition.0,versions[o.c_condition.0 as usize]));cond.sort();cond.dedup();}
  let cs=vec![cond.clone()];let(a,b,t)=(o.q_control1.0 as usize,o.q_control2.0 as usize,o.q_target.0 as usize);
  match o.kind {
   X=>q[t]=union(q[t].clone(),cs),
   CX=>q[t]=union(q[t].clone(),product(&q[a],&cs)),
   CCX=>q[t]=union(q[t].clone(),product(&product(&q[a],&q[b]),&cs)),
   Swap=>{if cond.is_empty(){q.swap(a,t);}else{let qa=q[a].clone();let qt=q[t].clone();q[a]=union(qa.clone(),product(&qt,&cs));q[t]=union(qt,product(&qa,&cs));}},
   R|Hmr=>{q[t].retain(|term|!cond.iter().all(|x|term.contains(x)));if o.kind==Hmr{versions[o.c_target.0 as usize]+=1;}},
   BitStore0|BitStore1|BitInvert=>versions[o.c_target.0 as usize]+=1,
   PushCondition=>{stack.push(base);base=cond;},PopCondition=>base=stack.pop().unwrap(),_=>{}
  }
 }
 eprintln!("WD_ZERO_SUPPORT proved={} unproved={} (unproved is not a failure witness)",proved,unproved);
 unproved_mask
}
