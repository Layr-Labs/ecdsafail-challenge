//! v2 : the review's four latent guards G1..G4 coded in (SL_COND_NOGUARD=1 turns
//! them off), and its print-only premise census (SL_COND_RVDIAG=1).
//! cond pass: exact op-stream post-passes over Toffolis whose result is consumed only by phases or
//! by a measurement or reset, or that need no Toffoli at all. Research switch `SL_COND` (unset or "0": the gate list
//! byte for byte):
//!   m  a CCX whose AND equals one control's value (the other control holds 1, or both hold one value) -> CX
//!   u  a CCX that XORs a wire's whole AND back out (the wire is 0 after it) -> HMR into a fresh bit + CZ(a, b) under it
//!   f  a CCX whose result is read only by Z gates before its wire is measured, reset, or the same AND is XORed in
//!      again -> Clifford phases on the operands' values (a CZ of two wires holding them, or of affine forms of them);
//!      at a measured end the builder's own fix CZ on the same two values is deleted
//!   s  a CCX every read of which runs under one classical bit c (a measurement made after the CCX) -> moved to
//!      just after c exists (its operands rebuilt there as affine forms, CX only) and built under c; its measured
//!      erase's phase fix is put under c too (technique 4: build the AND only under the bit that decides its read)
//!   r  K3a measurement absorption generalized: a reset end (the wire is 0 there on every correct shot), writes under
//!      conditions, windows followed through swaps; the wire is measured before the writes, which become phases under
//!      the outcome (a measured end hands the moved outcome to its bit and keeps an idle reset)
//! `SL_COND=1` means "mufsr". `SL_COND_FAULT=f|r|u|u2` breaks one site of that lever (u2: every u site) on purpose
//! (diagnostic only).
//! `SL_COND_ALIGN=1` (diagnostic only, never a candidate): the UNCHANGED gate list with an idle reset of a fresh wire
//! wherever u and r would add a measurement, so it draws the candidate's random words in the candidate's order and
//! can be compared with it shot for shot (dcd525d's aligned copy).
//! m and f keep every measurement in place (the checker's random words stay aligned); u and r add one measurement a
//! site, so later random words shift.
//! Values are hash-consed (atoms: opaque, AND, conditioned; XOR = canonical sets of atoms), so equal ids are equal
//! Boolean functions; contexts are sets of classical bit VALUES (a push captures the value, as the simulator does).

use crate::circuit::{BitId, Op, OperationType as K, QubitId, RegisterId};
use std::collections::{HashMap, HashSet};

const NQ: u32 = u32::MAX;
#[derive(Clone, Copy, PartialEq, Eq)]
struct L { kind: u8, c2: u32, c1: u32, t: u32, ct: u32, cc: u32, rt: u32 }
const K_NEG: u8 = 0; const K_APP: u8 = 2; const K_BINV: u8 = 3; const K_BS0: u8 = 4; const K_BS1: u8 = 5;
const K_X: u8 = 6; const K_Z: u8 = 7; const K_CX: u8 = 8; const K_CZ: u8 = 9; const K_SWAP: u8 = 10; const K_R: u8 = 11;
const K_HMR: u8 = 12; const K_CCX: u8 = 13; const K_CCZ: u8 = 14; const K_PUSH: u8 = 15; const K_POP: u8 = 16;

fn d(v: u64) -> u32 { if v == u64::MAX { NQ } else { assert!(v < NQ as u64, "cond_pass: id {v} too large"); v as u32 } }
fn e(v: u32) -> u64 { if v == NQ { u64::MAX } else { v as u64 } }
fn to_l(o: &Op) -> L { L { kind: o.kind as u8, c2: d(o.q_control2.0), c1: d(o.q_control1.0), t: d(o.q_target.0), ct: d(o.c_target.0), cc: d(o.c_condition.0), rt: d(o.r_target.0) } }
fn kind_of(k: u8) -> K {
    match k { 0 => K::Neg, 1 => K::Register, 2 => K::AppendToRegister, 3 => K::BitInvert, 4 => K::BitStore0, 5 => K::BitStore1,
        6 => K::X, 7 => K::Z, 8 => K::CX, 9 => K::CZ, 10 => K::Swap, 11 => K::R, 12 => K::Hmr, 13 => K::CCX, 14 => K::CCZ,
        15 => K::PushCondition, 16 => K::PopCondition, _ => K::DebugPrint }
}
fn from_l(l: &L) -> Op {
    let mut o = Op::empty();
    o.kind = kind_of(l.kind);
    o.q_control2 = QubitId(e(l.c2)); o.q_control1 = QubitId(e(l.c1)); o.q_target = QubitId(e(l.t));
    o.c_target = BitId(e(l.ct)); o.c_condition = BitId(e(l.cc)); o.r_target = RegisterId(e(l.rt));
    o.validate();
    o
}
fn op(kind: u8, c1: u32, t: u32, cc: u32) -> L { L { kind, c2: NQ, c1, t, ct: NQ, cc, rt: NQ } }

// ---- values ----
const ZERO: u32 = 0; const ONE: u32 = 1;
const T_OPQ: u8 = 2; const T_AND: u8 = 3; const T_COND: u8 = 5; const T_SET: u8 = 6;
const XSET_CAP: usize = 96;
struct Vals { node: Vec<(u8, u32, u32)>, h: HashMap<(u8, u32, u32), u32>, store: Vec<Vec<u32>>, hs: HashMap<Vec<u32>, u32> }
impl Vals {
    fn new() -> Self { Vals { node: vec![(0, 0, 0), (1, 0, 0)], h: HashMap::new(), store: Vec::new(), hs: HashMap::new() } }
    fn opq(&mut self) -> u32 { let i = self.node.len() as u32; self.node.push((T_OPQ, i, 0)); i }
    fn mk(&mut self, t: u8, a: u32, b: u32) -> u32 {
        if let Some(&i) = self.h.get(&(t, a, b)) { return i; }
        let i = self.node.len() as u32; self.node.push((t, a, b)); self.h.insert((t, a, b), i); i
    }
    fn and(&mut self, a: u32, b: u32) -> u32 {
        if a == ZERO || b == ZERO { return ZERO; }
        if a == ONE { return b; } if b == ONE { return a; } if a == b { return a; }
        let (x, y) = if a < b { (a, b) } else { (b, a) }; self.mk(T_AND, x, y)
    }
    fn xor(&mut self, a: u32, b: u32) -> u32 {
        if a == ZERO { return b; } if b == ZERO { return a; } if a == b { return ZERO; }
        let one_a = [a]; let one_b = [b];
        let sa: &[u32] = if self.node[a as usize].0 == T_SET { &self.store[self.node[a as usize].1 as usize] } else { &one_a };
        let sb: &[u32] = if self.node[b as usize].0 == T_SET { &self.store[self.node[b as usize].1 as usize] } else { &one_b };
        let mut r: Vec<u32> = Vec::with_capacity(sa.len() + sb.len());
        let (mut i, mut j) = (0, 0);
        while i < sa.len() && j < sb.len() {
            if sa[i] < sb[j] { r.push(sa[i]); i += 1; } else if sa[i] > sb[j] { r.push(sb[j]); j += 1; } else { i += 1; j += 1; }
        }
        r.extend_from_slice(&sa[i..]); r.extend_from_slice(&sb[j..]);
        match r.len() {
            0 => ZERO,
            1 => r[0],
            l if l > XSET_CAP => self.opq(),
            _ => {
                if let Some(&id) = self.hs.get(&r) { return id; }
                let si = self.store.len() as u32; self.store.push(r.clone());
                let id = self.node.len() as u32; self.node.push((T_SET, si, 0)); self.hs.insert(r, id); id
            }
        }
    }
    fn cond(&mut self, ctx: u32, x: u32) -> u32 { if ctx == 0 || x == ZERO { x } else { self.mk(T_COND, ctx, x) } }
}
struct Ctxs { sets: Vec<Vec<u32>>, h: HashMap<Vec<u32>, u32> }
impl Ctxs {
    fn new() -> Self { let mut c = Ctxs { sets: vec![vec![]], h: HashMap::new() }; c.h.insert(vec![], 0); c }
    fn add(&mut self, c: u32, b: u32) -> u32 {
        if b == BV1 { return c; }
        if self.sets[c as usize].contains(&b) { return c; }
        let mut v = self.sets[c as usize].clone(); v.push(b); v.sort_unstable();
        if let Some(&i) = self.h.get(&v) { return i; }
        let i = self.sets.len() as u32; self.sets.push(v.clone()); self.h.insert(v, i); i
    }
}
const BV0: u32 = 0; const BV1: u32 = 1;
const E_OPEN: u8 = 0; const E_CANCEL: u8 = 1; const E_HMR: u8 = 3; const E_R: u8 = 4;

/// A CCX's XOR-write into its target, tracked until the same AND is XORed in again or the wire is measured / reset.
struct Contrib { swapped: bool, op: u32, wire: u32, term: u32, ctx: u32, va: u32, vb: u32, reads: Vec<(u32, u32)>, zonly: bool,
    end_kind: u8, end_op: u32, end_bit: u32,
    /// bits every read so far runs under beyond the CCX's own (None: no read yet); first read; the wire held only this
    /// AND when measured
    inter: Option<Vec<u32>>, first_read: u32, end_sole: bool }

struct Analysis {
    opctx: Vec<u32>, cx: Ctxs, contribs: Vec<Contrib>,
    zhold: HashMap<(u32, u32), (u32, u32)>, endhold: HashMap<u32, (u32, u32)>, fixcz: HashMap<u32, Vec<(u32, u32, u32)>>,
    misc: Vec<(u32, u8, u32)>, unc: Vec<u32>,
    pref: Vec<(u32, Option<Vec<u32>>)>,
    /// per bit value: the op that created it and the slot it was written to; derived = another value was computed from it
    bcreator: Vec<u32>, bslot: Vec<u32>, bderived: Vec<bool>, depth_after: Vec<u8>,
}

fn prefix_held(v: &Vals, val: u32, holders: &HashMap<u32, Vec<u32>>, target: u32) -> Option<Vec<u32>> {
    if val == ZERO {
        return Some(Vec::new());
    }
    let atoms: Vec<u32> = if v.node[val as usize].0 == T_SET {
        v.store[v.node[val as usize].1 as usize].clone()
    } else {
        vec![val]
    };
    let mut used: HashSet<u32> = HashSet::new();
    let mut out = Vec::with_capacity(atoms.len());
    for a in atoms {
        if a == ONE {
            out.push(NQ);
            continue;
        }
        let hs = holders.get(&a)?;
        let w = hs.iter().copied().find(|&w| w != target && !used.contains(&w))?;
        used.insert(w);
        out.push(w);
    }
    Some(out)
}

fn analyze(ops: &[L]) -> Analysis {
    let n = ops.len();
    let mut nq = 0u32; let mut nb = 0u32;
    for o in ops { for q in [o.c2, o.c1, o.t] { if q != NQ { nq = nq.max(q + 1); } } for b in [o.ct, o.cc] { if b != NQ { nb = nb.max(b + 1); } } }
    let mut reg_q = vec![false; nq as usize]; let mut reg_b = vec![false; nb as usize];
    for o in ops { if o.kind == K_APP { if o.t != NQ { reg_q[o.t as usize] = true; } if o.ct != NQ { reg_b[o.ct as usize] = true; } } }
    let mut v = Vals::new();
    let mut cx = Ctxs::new();
    let mut qv: Vec<u32> = (0..nq).map(|q| if reg_q[q as usize] { v.opq() } else { ZERO }).collect();
    let mut nbits: u32 = 2;
    let mut bv: Vec<u32> = vec![BV0; nb as usize];
    for b in 0..nb as usize { if reg_b[b] { bv[b] = nbits; nbits += 1; } }
    let mut holders: HashMap<u32, Vec<u32>> = HashMap::new();
    for q in 0..nq { if qv[q as usize] != ZERO { holders.entry(qv[q as usize]).or_default().push(q); } }
    let mut stack: Vec<u32> = vec![0];
    let mut opctx: Vec<u32> = vec![0; n];
    let mut contribs: Vec<Contrib> = Vec::new();
    let mut open: Vec<Vec<u32>> = vec![Vec::new(); nq as usize];
    let mut zhold = HashMap::new(); let mut endhold = HashMap::new();
    let mut fixcz: HashMap<u32, Vec<(u32, u32, u32)>> = HashMap::new();
    let mut misc = Vec::new(); let mut unc = Vec::new(); let mut pref: Vec<(u32, Option<Vec<u32>>)> = Vec::new();
    let mut bcreator: Vec<u32> = vec![NQ; nbits as usize]; let mut bslot: Vec<u32> = vec![NQ; nbits as usize];
    let mut bderived: Vec<bool> = vec![false; nbits as usize]; let mut depth_after: Vec<u8> = vec![0; n];
    macro_rules! setq { ($q:expr, $val:expr) => {{
        let q = $q as usize; let old = qv[q]; let nv = $val;
        if old != nv {
            if old != ZERO { if let Some(hv) = holders.get_mut(&old) { if let Some(p) = hv.iter().position(|&x| x == q as u32) { hv.swap_remove(p); } if hv.is_empty() { holders.remove(&old); } } }
            if nv != ZERO { holders.entry(nv).or_default().push(q as u32); }
            qv[q] = nv;
        }
    }}}
    let hold = |val: u32, holders: &HashMap<u32, Vec<u32>>| -> u32 { holders.get(&val).and_then(|v| v.first().copied()).unwrap_or(NQ) };
    for (k, o) in ops.iter().enumerate() {
        let k32 = k as u32;
        let top = *stack.last().unwrap();
        let mut ctx = top;
        if o.cc != NQ && o.kind != K_PUSH { ctx = cx.add(ctx, bv[o.cc as usize]); }
        opctx[k] = ctx;
        if (o.kind == K_CZ || o.kind == K_Z) && o.cc != NQ {
            let (x, y) = if o.kind == K_CZ { (qv[o.c1 as usize], qv[o.t as usize]) } else { (qv[o.t as usize], qv[o.t as usize]) };
            fixcz.entry(bv[o.cc as usize]).or_default().push((k32, x, y));
        }
        let mut reads: [u32; 3] = [NQ; 3];
        match o.kind {
            K_CCX => { reads[0] = o.c1; reads[1] = o.c2; }
            K_CX => { reads[0] = o.c1; }
            K_Z => { reads[0] = o.t; }
            K_CZ => { reads[0] = o.c1; reads[1] = o.t; }
            K_CCZ => { reads[0] = o.c1; reads[1] = o.c2; reads[2] = o.t; }
            K_SWAP => { if ctx != 0 { reads[0] = o.c1; reads[1] = o.t; } }
            _ => {}
        }
        for &q in reads.iter() {
            if q == NQ { continue; }
            for &ci in &open[q as usize] {
                let c = &mut contribs[ci as usize];
                if c.first_read == NQ { c.first_read = k32; }
                if c.inter.as_ref().map_or(true, |x| !x.is_empty()) {
                    let own = &cx.sets[c.ctx as usize];
                    let rs: Vec<u32> = cx.sets[ctx as usize].iter().copied().filter(|b| !own.contains(b)).collect();
                    c.inter = Some(match c.inter.take() { None => rs, Some(mut x) => { x.retain(|b| rs.contains(b)); x } });
                }
                if !c.zonly { continue; }
                if o.kind == K_Z && c.reads.len() < 64 {
                    zhold.insert((ci, k32), (hold(c.va, &holders), hold(c.vb, &holders)));
                    c.reads.push((k32, ctx));
                } else { c.zonly = false; c.reads = Vec::new(); }
            }
        }
        match o.kind {
            K_CCX | K_CX | K_X => {
                let t = o.t as usize;
                let (va, vb) = if o.kind == K_CCX { (qv[o.c1 as usize], qv[o.c2 as usize]) } else { (NQ, NQ) };
                let bare = match o.kind { K_CCX => v.and(va, vb), K_CX => qv[o.c1 as usize], _ => ONE };
                let term = v.cond(ctx, bare);
                if o.kind == K_CCX {
                    if bare == ZERO { misc.push((k32, 0, NQ)); }
                    else if bare == va { misc.push((k32, 1, o.c1)); } else if bare == vb { misc.push((k32, 2, o.c2)); }
                }
                if o.kind != K_X {
                    if let Some(p) = open[t].iter().position(|&ci| contribs[ci as usize].term == term) {
                        let ci = open[t].remove(p);
                        let c = &mut contribs[ci as usize]; c.end_kind = E_CANCEL; c.end_op = k32;
                        if o.kind == K_CCX && qv[t] == term { unc.push(k32); }
                    } else if o.kind == K_CCX && term != ZERO {
                        let ci = contribs.len() as u32;
                        contribs.push(Contrib { swapped: false, op: k32, wire: o.t, term, ctx, va, vb, reads: vec![], zonly: true, end_kind: E_OPEN, end_op: NQ, end_bit: NQ, inter: None, first_read: NQ, end_sole: false });
                        open[t].push(ci);
                        if open[t].len() > 512 { let old = open[t].remove(0); let c = &mut contribs[old as usize]; c.zonly = false; c.reads = Vec::new(); }
                    }
                }
                if o.kind == K_CCX && o.cc == NQ && stack.len() > 1 {
                    if term == ZERO {
                        pref.push((k32, None));
                    } else {
                        let prefix = v.xor(qv[t], term);
                        if let Some(ws) = prefix_held(&v, prefix, &holders, o.t) {
                            pref.push((k32, Some(ws)));
                        }
                    }
                }
                let nv = v.xor(qv[t], term); setq!(t, nv);
            }
            K_SWAP => {
                let (a, b) = (o.c1 as usize, o.t as usize);
                if ctx == 0 { let (xa, xb) = (qv[a], qv[b]); setq!(a, xb); setq!(b, xa); open.swap(a, b); for &ci in &open[a] { contribs[ci as usize].wire = a as u32; contribs[ci as usize].swapped = true; } for &ci in &open[b] { contribs[ci as usize].wire = b as u32; contribs[ci as usize].swapped = true; } }
                else { let x = v.opq(); setq!(a, x); let y = v.opq(); setq!(b, y); }
            }
            K_R | K_HMR => {
                let t = o.t as usize;
                let mut newb = NQ;
                if o.kind == K_HMR { newb = nbits; nbits += 1; bv[o.ct as usize] = newb; bcreator.push(k32); bslot.push(o.ct); bderived.push(false); }
                let sole = open[t].len() == 1 && contribs[open[t][0] as usize].term == qv[t];
                for ci in std::mem::take(&mut open[t]) {
                    let c = &mut contribs[ci as usize];
                    c.end_kind = if o.kind == K_HMR { E_HMR } else { E_R }; c.end_op = k32; c.end_bit = newb; c.end_sole = sole && ctx == 0;
                    if c.zonly { endhold.insert(ci, (hold(c.va, &holders), hold(c.vb, &holders))); }
                }
                if ctx == 0 { setq!(t, ZERO); } else { let x = v.opq(); setq!(t, x); }
            }
            K_BS0 | K_BS1 | K_BINV => {
                let b = o.ct as usize; let old = bv[b];
                let cs = &cx.sets[ctx as usize];
                let nv = if ctx == 0 && o.kind == K_BS0 { BV0 } else if ctx == 0 && o.kind == K_BS1 { BV1 }
                    else if cs.len() == 1 && (o.kind == K_BS1 || o.kind == K_BINV) && old == BV0 { cs[0] }
                    else {
                        if old >= 2 { bderived[old as usize] = true; }
                        for &x in cs.iter() { if x >= 2 { bderived[x as usize] = true; } }
                        let id = nbits; nbits += 1; bcreator.push(k32); bslot.push(o.ct); bderived.push(false); id };
                bv[b] = nv;
            }
            K_PUSH => { let c = cx.add(top, bv[o.cc as usize]); stack.push(c); }
            K_POP => { stack.pop(); assert!(!stack.is_empty(), "cond_pass: unbalanced pop"); }
            _ => {}
        }
        depth_after[k] = (stack.len() - 1).min(255) as u8;
    }
    Analysis { opctx, cx, contribs, zhold, endhold, fixcz, misc, unc, pref, bcreator, bslot, bderived, depth_after }
}

/// Affine forms of wires `start` (values at op p) over the wires at each op in `at` (sorted, all > p). None if a member
/// is written nonlinearly, under a condition the CCX's own context does not imply, or measured / reset first.
fn forms_at(ops: &[L], a: &Analysis, p: usize, start: &[u32], at: &[usize]) -> Option<Vec<Vec<(Vec<u32>, bool)>>> {
    let own = &a.cx.sets[a.opctx[p] as usize];
    let mut fs: Vec<(Vec<u32>, bool)> = start.iter().map(|&w| (vec![w], false)).collect();
    let mut out = Vec::new();
    let mut ai = 0;
    let last = *at.last().unwrap();
    for k in p + 1..=last {
        while ai < at.len() && at[ai] == k { out.push(fs.iter().map(|f| { let mut v = f.0.clone(); v.sort_unstable(); (v, f.1) }).collect()); ai += 1; }
        if ai == at.len() { break; }
        let o = &ops[k];
        let uncond = a.cx.sets[a.opctx[k] as usize].iter().all(|b| own.contains(b));
        for f in fs.iter_mut() {
            let inn = |w: u32, f: &Vec<u32>| f.contains(&w);
            match o.kind {
                K_CX => if inn(o.t, &f.0) { if !uncond { return None; } if let Some(q) = f.0.iter().position(|&x| x == o.c1) { f.0.swap_remove(q); } else { f.0.push(o.c1); } },
                K_X => if inn(o.t, &f.0) { if !uncond { return None; } f.1 ^= true; },
                K_CCX | K_R | K_HMR => if inn(o.t, &f.0) { return None; },
                K_SWAP => { let (x, y) = (inn(o.c1, &f.0), inn(o.t, &f.0)); if x || y { if !uncond { return None; }
                    for w in f.0.iter_mut() { if *w == o.c1 { *w = o.t; } else if *w == o.t { *w = o.c1; } } } }
                _ => {}
            }
        }
    }
    if out.len() != at.len() { return None; }
    Some(out)
}

/// Phase (-1)^(Fa * Fb) as CZ / Z / NEG ops under the per-op condition `cc`.
fn phase_ops(fa: &(Vec<u32>, bool), fb: &(Vec<u32>, bool), cc: u32) -> Vec<L> {
    let mut pairs: HashMap<(u32, u32), bool> = HashMap::new();
    let mut singles: HashMap<u32, bool> = HashMap::new();
    for &u in &fa.0 { for &w in &fb.0 { if u == w { *singles.entry(u).or_insert(false) ^= true; } else { let key = if u < w { (u, w) } else { (w, u) }; *pairs.entry(key).or_insert(false) ^= true; } } }
    if fb.1 { for &u in &fa.0 { *singles.entry(u).or_insert(false) ^= true; } }
    if fa.1 { for &w in &fb.0 { *singles.entry(w).or_insert(false) ^= true; } }
    let mut v = Vec::new();
    let mut ps: Vec<_> = pairs.into_iter().filter(|x| x.1).map(|x| x.0).collect(); ps.sort_unstable();
    for (u, w) in ps { v.push(op(K_CZ, u, w, cc)); }
    let mut ss: Vec<_> = singles.into_iter().filter(|x| x.1).map(|x| x.0).collect(); ss.sort_unstable();
    for u in ss { v.push(op(K_Z, NQ, u, cc)); }
    if fa.1 && fb.1 { v.push(L { kind: K_NEG, c2: NQ, c1: NQ, t: NQ, ct: NQ, cc, rt: NQ }); }
    v
}
fn pair_op(u: u32, w: u32, cc: u32) -> L { if u == w { op(K_Z, NQ, u, cc) } else { op(K_CZ, u, w, cc) } }

struct Edits { delete: HashSet<u32>, replace: HashMap<u32, Vec<L>>, after: HashMap<u32, Vec<L>>, before: HashMap<u32, Vec<L>> }
impl Edits {
    fn new() -> Self { Edits { delete: HashSet::new(), replace: HashMap::new(), after: HashMap::new(), before: HashMap::new() } }
    fn touched(&self, k: u32) -> bool { self.delete.contains(&k) || self.replace.contains_key(&k) }
    fn apply(&self, ops: &[L]) -> Vec<L> {
        let mut out = Vec::with_capacity(ops.len() + 1024);
        for (k, o) in ops.iter().enumerate() {
            let k32 = k as u32;
            if let Some(v) = self.before.get(&k32) { out.extend_from_slice(v); }
            if let Some(v) = self.replace.get(&k32) { out.extend_from_slice(v); } else if !self.delete.contains(&k32) { out.push(*o); }
            if let Some(v) = self.after.get(&k32) { out.extend_from_slice(v); }
        }
        out
    }
}

fn weight_of(ops: &[L]) -> f64 {
    let mut depth = 0i32; let mut t = 0f64;
    for o in ops {
        match o.kind {
            K_PUSH => depth += 1, K_POP => depth -= 1,
            K_CCX | K_CCZ => t += 0.5f64.powi(depth + (o.cc != NQ) as i32),
            _ => {}
        }
    }
    t
}
fn max_bit(ops: &[L]) -> u32 { let mut nb = 0u32; for o in ops { for b in [o.ct, o.cc] { if b != NQ { nb = nb.max(b + 1); } } } nb }

/// m, u, f planned on one analysis of `ops`.
fn guards_on() -> bool { !std::env::var("SL_COND_NOGUARD").is_ok_and(|x| x == "1") }
static GUARD_HITS: std::sync::Mutex<[usize; 4]> = std::sync::Mutex::new([0; 4]);
fn guard_hit(i: usize) { GUARD_HITS.lock().unwrap()[i] += 1; }
fn plan_muf(ops: &[L], levers: &str, fault: &str) -> (Edits, [usize; 4], [f64; 4]) {
    let a = analyze(ops);
    let gon = guards_on();
    let wt = |k: u32| 0.5f64.powi(a.cx.sets[a.opctx[k as usize] as usize].len() as i32);
    let mut ed = Edits::new();
    let mut nb = max_bit(ops);
    let mut cnt = [0usize; 4]; let mut sav = [0f64; 4];
    if levers.contains('m') {
        for &(k, how, u) in &a.misc {
            let o = ops[k as usize];
            ed.replace.insert(k, if how == 0 { vec![] } else { vec![op(K_CX, u, o.t, o.cc)] });
            cnt[0] += 1; sav[0] += wt(k);
        }
    }
    if levers.contains('u') {
        let mut faulted = false;
        for &k in &a.unc {
            let o = ops[k as usize];
            if o.cc != NQ || ed.touched(k) { continue; }
            let f = nb; nb += 1;
            let mut fix = op(K_CZ, o.c1, o.c2, f);
            if fault == "u" && !faulted { fix = op(K_Z, NQ, o.c1, f); faulted = true; }
            let mut v = vec![L { kind: K_HMR, c2: NQ, c1: NQ, t: o.t, ct: f, cc: NQ, rt: NQ }, fix];
            if fault == "u2" { v.pop(); } // every u site's phase fix left out
            ed.replace.insert(k, v);
            cnt[1] += 1; sav[1] += wt(k);
            if std::env::var("SL_COND_RVDIAG").is_ok_and(|x| x == "1") { eprintln!("RVU op {} ctx {:?} depth_after {} cc {}", k, a.cx.sets[a.opctx[k as usize] as usize], a.depth_after[k as usize], o.cc as i64); }
        }
    }
    if levers.contains('f') {
        struct Site { ci: u32, wire: u32, op: u32, end: u32, uses: Vec<(u32, u32)>, after: Vec<(u32, Vec<L>)>, replace: Vec<(u32, L)>, delete: Vec<u32>, save: f64, bit: u32 }
        let mut sites: Vec<Site> = Vec::new();
        let mut taken: HashSet<u32> = HashSet::new();
        for (ci, c) in a.contribs.iter().enumerate() {
            let ci = ci as u32;
            if !c.zonly || ed.touched(c.op) { continue; }
            // v2 G2: a contribution a swap moved during its life is not taken (the overlap check keys on one label)
            if gon && c.swapped { guard_hit(1); continue; }
            if !c.reads.iter().all(|&(r, _)| ops[r as usize].t == c.wire) { continue; }
            let p = c.op as usize; let o = ops[p];
            let own = &a.cx.sets[c.ctx as usize];
            let sub = |x: u32| -> bool { let s = &a.cx.sets[x as usize]; own.iter().all(|b| s.contains(b)) };
            if !c.reads.iter().all(|&(_, rc)| sub(rc)) { continue; }
            let e = c.end_op as usize;
            match c.end_kind {
                E_HMR | E_R => { if ops[e].cc != NQ || !sub(a.opctx[e]) || ed.touched(e as u32) { continue; }
                    // v2 G1: the end runs under exactly the CCX's context
                    if gon && a.opctx[e] != c.ctx { guard_hit(0); continue; } }
                E_CANCEL => { if !matches!(ops[e].kind, K_CCX | K_CX) || taken.contains(&(e as u32)) || ed.touched(e as u32) { continue; } }
                _ => continue,
            }
            let mut s = Site { ci, wire: c.wire, op: c.op, end: c.end_op, uses: vec![], after: vec![], replace: vec![], delete: vec![c.op], save: wt(c.op), bit: NQ };
            let mut need: Vec<(usize, u32)> = Vec::new();
            for &(r, _) in &c.reads {
                let z = ops[r as usize];
                match a.zhold.get(&(ci, r)) {
                    Some(&(u, w)) if u != NQ && w != NQ && u != c.wire && w != c.wire => { s.after.push((r, vec![pair_op(u, w, z.cc)])); s.uses.push((u, r)); s.uses.push((w, r)); }
                    _ => need.push((r as usize, z.cc)),
                }
            }
            match c.end_kind {
                E_HMR => {
                    let k = c.end_bit;
                    let mut want: Vec<u32> = own.clone(); want.push(k); want.sort_unstable(); want.dedup();
                    let found = a.fixcz.get(&k).and_then(|v| v.iter().find(|&&(f, x, y)| !taken.contains(&f) && !ed.touched(f)
                        && ((x == c.va && y == c.vb) || (x == c.vb && y == c.va)) && a.cx.sets[a.opctx[f as usize] as usize] == want));
                    if let Some(&(f, _, _)) = found { s.delete.push(f); }
                    else {
                        match a.endhold.get(&ci) {
                            // v2 G3: never the measured wire itself
                            Some(&(u, w)) if gon && u != NQ && w != NQ && (u == c.wire || w == c.wire) => { guard_hit(2); continue; }
                            Some(&(u, w)) if u != NQ && w != NQ => { s.after.push((e as u32, vec![pair_op(u, w, ops[e].ct)])); s.uses.push((u, e as u32)); s.uses.push((w, e as u32)); }
                            _ => need.push((e, ops[e].ct)),
                        }
                    }
                }
                E_R => {
                    let f = nb; s.bit = f;
                    let mut h = ops[e]; h.kind = K_HMR; h.ct = f;
                    s.replace.push((e as u32, h));
                    match a.endhold.get(&ci) {
                        // v2 G3: never the reset wire itself
                        Some(&(u, w)) if gon && u != NQ && w != NQ && (u == c.wire || w == c.wire) => { guard_hit(2); continue; }
                        Some(&(u, w)) if u != NQ && w != NQ => { s.after.push((e as u32, vec![pair_op(u, w, f)])); s.uses.push((u, e as u32)); s.uses.push((w, e as u32)); }
                        _ => need.push((e, f)),
                    }
                }
                _ => { s.delete.push(e as u32); if ops[e].kind == K_CCX { s.save += wt(e as u32); } }
            }
            if !need.is_empty() {
                need.sort_unstable();
                let at: Vec<usize> = need.iter().map(|x| x.0).collect();
                let Some(fs) = forms_at(ops, &a, p, &[o.c1, o.c2], &at) else { continue };
                for (i, &(t, cc)) in need.iter().enumerate() {
                    for w in fs[i][0].0.iter().chain(fs[i][1].0.iter()) { s.uses.push((*w, t as u32)); }
                    s.after.push((t as u32, phase_ops(&fs[i][0], &fs[i][1], cc)));
                }
            }
            if s.bit != NQ { nb += 1; }
            for &x in &s.delete { taken.insert(x); }
            sites.push(s);
        }
        // a fix must not read a wire whose value a kept site changes at that time
        let mut iv: HashMap<u32, Vec<(u32, u32)>> = HashMap::new();
        for s in &sites { iv.entry(s.wire).or_default().push((s.op, s.end)); }
        let mut faulted = false;
        for s in &sites {
            if s.uses.iter().any(|&(w, t)| iv.get(&w).is_some_and(|v| v.iter().any(|&(p, e)| p < t && t <= e))) { continue; }
            for &x in &s.delete { ed.delete.insert(x); }
            for (k, l) in &s.replace { ed.replace.insert(*k, vec![*l]); }
            for (k, v) in &s.after {
                let mut v = v.clone();
                if fault == "f" && !faulted && !v.is_empty() { v.pop(); faulted = true; }
                ed.after.entry(*k).or_default().extend(v);
            }
            cnt[2] += 1; sav[2] += s.save;
            if std::env::var("SL_COND_RVDIAG").is_ok_and(|x| x == "1") {
                let c = &a.contribs[s.ci as usize]; let e = c.end_op as usize;
                let own = &a.cx.sets[c.ctx as usize]; let ce = &a.cx.sets[a.opctx[e] as usize];
                let w0 = ops[c.op as usize].t;
                let eh = a.endhold.get(&s.ci).copied();
                let hw = eh.is_some_and(|(u, w)| u == c.wire || w == c.wire);
                let rx = c.reads.iter().filter(|&&(_, rc)| a.cx.sets[rc as usize].len() > own.len()).count();
                let kind_e = ops[e].kind;
                let mut lab = w0; let mut nsw = 0;
                for j in c.op as usize + 1..e { let x = &ops[j]; if x.kind == K_SWAP { if x.c1 == lab { lab = x.t; nsw += 1; } else if x.t == lab { lab = x.c1; nsw += 1; } } }
                eprintln!("RVF op {} end {} endkind {} opkind_e {} own {:?} ctx_e {:?} ctx_e_eq_own {} w0 {} wire {} swaps {} reads {} reads_extra_ctx {} del {} repl {} after {} endhold {:?} holder_is_wire {} depth_ccx {} depth_e {}",
                    c.op, e, c.end_kind, kind_e, own, ce, ce == own, w0, c.wire, nsw, c.reads.len(), rx, s.delete.len(), s.replace.len(), s.after.len(), eh, hw,
                    a.depth_after[c.op as usize], a.depth_after[e]);
            }
        }
    }
    if levers.contains('s') {
        // copy point of a bit value: the first op at or after its creator with an empty condition stack, the slot not
        // rewritten in between
        let copy_point = |b: u32| -> u32 {
            let k = a.bcreator[b as usize]; let src = a.bslot[b as usize];
            if k == NQ { return NQ; }
            let mut j = k as usize;
            loop {
                if j >= ops.len() { return NQ; }
                if j > k as usize { let o = &ops[j]; if matches!(o.kind, K_HMR | K_BS0 | K_BS1 | K_BINV) && o.ct == src { return NQ; } }
                if a.depth_after[j] == 0 { return j as u32; }
                j += 1;
            }
        };
        let mut faulted = false;
        let mut cands: Vec<(u32, u32, u32, bool, Vec<L>, u32, u32)> = Vec::new();
        let dbg_all = std::env::var("SL_COND_DEBUG").is_ok_and(|x| x == "all");
        let dbg: Option<u32> = std::env::var("SL_COND_DEBUG").ok().and_then(|x| x.parse().ok());
        for c in a.contribs.iter() {
            let p = c.op as usize; let o = ops[p];
            if dbg == Some(c.op) { eprintln!("SL_COND_DEBUG op {} ctx {} inter {:?} first_read {} end {} {} sole {} k {} derived {}", c.op, c.ctx, c.inter, c.first_read as i64, c.end_kind, c.end_op as i64, c.end_sole, c.end_bit as i64, if c.end_bit != NQ { a.bderived[c.end_bit as usize] } else { false });
                if let Some(set) = &c.inter { for &b in set { if b >= 2 { eprintln!("  bit {b} creator {} slot {} copy_point {}", a.bcreator[b as usize] as i64, a.bslot[b as usize] as i64, copy_point(b) as i64); } } } }
            let why = |r: &str| { if dbg_all { eprintln!("SL_COND_S op {} weight-ctx {} end {} sole {} : {r}", c.op, c.ctx, c.end_kind, c.end_sole); } };
            let Some(set) = &c.inter else { continue };
            if set.is_empty() { continue; }
            if o.cc != NQ { why("CCX with a per-op condition"); continue; }
            if ed.touched(c.op) { why("taken by another lever"); continue; }
            if c.end_kind != E_HMR || !c.end_sole { why("end not a measured erase of this AND alone"); continue; }
            let e = c.end_op as usize;
            if ops[e].cc != NQ || a.opctx[e] != 0 || ed.touched(e as u32) { why("erase conditioned or taken"); continue; }
            let k = c.end_bit;
            if a.bderived[k as usize] { why("outcome bit derived"); continue; }
            // the read bit: a value created by an op (not an input), copyable before the first read
            let mut pick: Option<(u32, u32)> = None;
            for &b in set { if b < 2 { continue; } let cp = copy_point(b); if cp != NQ && cp < c.first_read { pick = Some((b, cp)); break; } }
            let Some((cb, cp)) = pick else { why("no copyable read bit before the first read"); continue };
            let sink = cp >= c.op;
            if sink && c.ctx != 0 { why("CCX under a condition and its read bit made after it"); continue; }
            let mut block: Vec<L> = Vec::new();
            let f = NQ; // the fresh slot is assigned once the site is kept
            if sink {
                // the target is not read, measured or swapped before the new place (XOR-writes into it commute with the
                // moved CCX); operands as affine forms there (disjoint, not the target)
                if (p + 1..=cp as usize).any(|j| { let x = &ops[j]; x.c1 == c.wire || x.c2 == c.wire || (x.t == c.wire && !matches!(x.kind, K_X | K_CX | K_CCX)) }) { why("target used before the bit"); continue; }
                let Some(fs) = forms_at(ops, &a, p, &[o.c1, o.c2], &[cp as usize + 1]) else { why("operand forms break before the bit"); continue };
                let (fa, fb) = (&fs[0][0], &fs[0][1]);
                if dbg == Some(c.op) { eprintln!("  forms a {:?} b {:?}", fa, fb); }
                // hosts: Fa is built into ha (a member, preferably not in Fb); Fb is then rewritten over the current wires
                // (ha now holds Fa) and built into a member hb != ha. Members are only read.
                if fa.0.contains(&c.wire) || fb.0.contains(&c.wire) { why("target in a form"); continue; }
                let ha = *fa.0.iter().find(|w| !fb.0.contains(w)).unwrap_or(&fa.0[0]);
                let mut fbc: Vec<u32> = fb.0.clone(); let mut fbk = fb.1;
                if fb.0.contains(&ha) { for &w in fa.0.iter().filter(|&&w| w != ha) { if let Some(i) = fbc.iter().position(|&x| x == w) { fbc.swap_remove(i); } else { fbc.push(w); } } fbk ^= fa.1; }
                let Some(&hb) = fbc.iter().find(|&&w| w != ha) else { why("no host"); continue };
                let mut on: Vec<L> = Vec::new();
                for &w in fa.0.iter().filter(|&&w| w != ha) { on.push(op(K_CX, w, ha, NQ)); } if fa.1 { on.push(op(K_X, NQ, ha, NQ)); }
                for &w in fbc.iter().filter(|&&w| w != hb) { on.push(op(K_CX, w, hb, NQ)); } if fbk { on.push(op(K_X, NQ, hb, NQ)); }
                block.extend(on.iter().copied());
                block.push(L { kind: K_CCX, c2: ha, c1: hb, t: c.wire, ct: NQ, cc: f, rt: NQ });
                block.extend(on.iter().rev().copied());
            }
            cands.push((c.op, cb, cp, sink, block, k, e as u32));
        }
        // the measured erase's phase fix: every op of the stream under the outcome bit (quantum ops get c; no inner
        // measurement, no other lever's op)
        let want: HashSet<u32> = cands.iter().map(|x| x.5).collect();
        let mut kops: HashMap<u32, Vec<u32>> = HashMap::new();
        for j in 0..ops.len() { for &b in &a.cx.sets[a.opctx[j] as usize] { if want.contains(&b) { kops.entry(b).or_default().push(j as u32); } } }
        for (cop, cb, cp, sink, block, k, _e) in cands {
            let o = ops[cop as usize];
            let mut fixes: Vec<u32> = Vec::new(); let mut bad = false;
            for &j in kops.get(&k).map(|v| v.as_slice()).unwrap_or(&[]) {
                match ops[j as usize].kind { K_HMR | K_R => { bad = true; break; } K_PUSH | K_POP | K_BS0 | K_BS1 | K_BINV => {}
                    // v2 G4: a fix must be phase-only
                    kk if gon && !matches!(kk, K_Z | K_CZ | K_CCZ | K_NEG) => { guard_hit(3); bad = true; break; }
                    _ => fixes.push(j) }
                if ed.touched(j) { bad = true; break; }
            }
            if dbg == Some(cop) || dbg_all { eprintln!("SL_COND_S op {cop} fixes {} bad {bad} sink {sink}", fixes.len()); }
            if bad || fixes.is_empty() || ed.touched(cop) { continue; }
            let f = nb; nb += 1;
            let block: Vec<L> = block.into_iter().map(|mut x| { if x.kind == K_CCX { x.cc = f; } x }).collect();
            ed.after.entry(cp).or_default().extend([L { kind: K_BS0, c2: NQ, c1: NQ, t: NQ, ct: f, cc: NQ, rt: NQ },
                L { kind: K_BINV, c2: NQ, c1: NQ, t: NQ, ct: f, cc: a.bslot[cb as usize], rt: NQ }]);
            if sink { ed.delete.insert(cop); ed.after.get_mut(&cp).unwrap().extend(block); }
            else { let mut x = o; x.cc = f; ed.replace.insert(cop, vec![x]); }
            for &j in &fixes {
                if fault == "s" && !faulted { continue; }
                let x = ops[j as usize];
                let v = if x.cc == NQ { let mut y = x; y.cc = f; vec![y] } else {
                    vec![L { kind: K_PUSH, c2: NQ, c1: NQ, t: NQ, ct: NQ, cc: f, rt: NQ }, x, L { kind: K_POP, c2: NQ, c1: NQ, t: NQ, ct: NQ, cc: NQ, rt: NQ }] };
                ed.replace.insert(j, v);
            }
            if fault == "s" { faulted = true; }
            cnt[3] += 1; sav[3] += 0.5;
            if std::env::var("SL_COND_RVDIAG").is_ok_and(|x| x == "1") {
                let mut kinds: std::collections::BTreeMap<u8, usize> = Default::default();
                for &j in &fixes { *kinds.entry(ops[j as usize].kind).or_default() += 1; }
                let writes = fixes.iter().filter(|&&j| matches!(ops[j as usize].kind, K_X | K_CX | K_CCX | K_SWAP | K_R | K_HMR)).count();
                eprintln!("RVS op {} ccxctx {:?} bit {} copy_point {} sink {} outcome {} fixes {} kinds {:?} write_fixes {} first_fix {} last_fix {}", cop, a.cx.sets[a.opctx[cop as usize] as usize], cb, cp, sink, k, fixes.len(), kinds, writes, fixes.first().copied().unwrap_or(NQ) as i64, fixes.last().copied().unwrap_or(NQ) as i64);
            }
        }
    }
    (ed, cnt, sav)
}

/// r: K3a absorption with a reset end (see the module doc). Returns the edits, sites, CCX absorbed, expected saving.
fn plan_r(ops: &[L], fault: &str) -> (Edits, usize, usize, f64) {
    // A window = the X-type writes (X, CX into it, CCX into it; any condition) into a wire's content since its last
    // read, followed through unconditional swaps, ended by an unconditional reset or measurement. The absorbed part is
    // the shortest suffix of it that holds every CCX and starts at a write before which the measurement can be placed
    // (`ip`: an empty condition stack, no op on the wire in between); earlier writes stay as they are.
    let mut nq = 0u32; for o in ops { for q in [o.c1, o.c2, o.t] { if q != NQ { nq = nq.max(q + 1); } } }
    let mut nb = max_bit(ops);
    let mut window: Vec<Vec<u32>> = vec![Vec::new(); nq as usize]; // writes and swaps of the content, in order
    let mut lo_w: Vec<u32> = vec![0; nq as usize]; // first op after the content's last touch before the window
    let mut last_touch: Vec<u32> = vec![NQ; nq as usize];
    let mut depth_before: Vec<u8> = Vec::with_capacity(ops.len());
    let mut plan: Vec<(Vec<u32>, u32, u32)> = Vec::new();
    let mut depth = 0usize;
    let dbg = std::env::var("SL_COND_DEBUG").is_ok_and(|x| x == "r");
    for (k, o) in ops.iter().enumerate() {
        depth_before.push(depth.min(255) as u8);
        let cond = depth > 0 || o.cc != NQ;
        let rd = |q: u32, window: &mut Vec<Vec<u32>>| { if q != NQ { window[q as usize].clear(); } };
        match o.kind {
            K_PUSH => depth += 1,
            K_POP => depth -= 1,
            K_X | K_CX | K_CCX => {
                if o.kind != K_X { rd(o.c1, &mut window); }
                if o.kind == K_CCX { rd(o.c2, &mut window); }
                let t = o.t as usize;
                if window[t].is_empty() { lo_w[t] = if last_touch[t] == NQ { 0 } else { last_touch[t] + 1 }; }
                window[t].push(k as u32);
            }
            K_CZ => { rd(o.c1, &mut window); rd(o.t, &mut window); }
            K_CCZ => { rd(o.c1, &mut window); rd(o.c2, &mut window); rd(o.t, &mut window); }
            K_Z => { rd(o.t, &mut window); }
            K_SWAP => {
                let (a, b) = (o.c1 as usize, o.t as usize);
                if !cond {
                    window.swap(a, b); lo_w.swap(a, b);
                    for q in [a, b] { if !window[q].is_empty() { window[q].push(k as u32); } }
                } else { rd(o.c1, &mut window); rd(o.t, &mut window); }
            }
            K_R | K_HMR => {
                let t = o.t as usize;
                let w = std::mem::take(&mut window[t]);
                let last_ccx = w.iter().rposition(|&j| ops[j as usize].kind == K_CCX);
                if let (false, Some(lc)) = (cond, last_ccx) {
                    // latest start i <= first CCX ... no: the suffix must hold every CCX, so i <= the first CCX's index;
                    // take the latest such i that admits an insertion point
                    let first_ccx = w.iter().position(|&j| ops[j as usize].kind == K_CCX).unwrap();
                    let _ = lc;
                    let mut found: Option<(usize, u32)> = None;
                    let mut i = first_ccx as isize;
                    while i >= 0 {
                        let iu = i as usize;
                        if ops[w[iu] as usize].kind != K_SWAP {
                            let lo = if iu == 0 { lo_w[t] as usize } else { w[iu - 1] as usize + 1 };
                            let mut j = w[iu] as usize;
                            let mut ip = NQ;
                            loop { if depth_before[j] == 0 { ip = j as u32; break; } if j <= lo { break; } j -= 1; }
                            if ip != NQ { found = Some((iu, ip)); break; }
                        }
                        i -= 1;
                    }
                    match found {
                        Some((iu, ip)) => {
                            let writes: Vec<u32> = w[iu..].iter().copied().filter(|&j| ops[j as usize].kind != K_SWAP).collect();
                            plan.push((writes, k as u32, ip));
                        }
                        None => if dbg { eprintln!("SL_COND_R skip end {k}: no insertion point (first write {})", w[0]); },
                    }
                } else if dbg && last_ccx.is_some() { eprintln!("SL_COND_R skip end {k}: conditional end"); }
            }
            _ => {}
        }
        for q in [o.c1, o.c2, o.t] { if q != NQ { last_touch[q as usize] = k as u32; } }
    }
    let mut ed = Edits::new();
    let mut nccx = 0usize;
    let mut faulted = false;
    for (w, e, ip) in &plan {
        if std::env::var("SL_COND_RVDIAG").is_ok_and(|x| x == "1") {
            let nccx = w.iter().filter(|&&j| ops[j as usize].kind == K_CCX).count();
            let ncond = w.iter().filter(|&&j| ops[j as usize].cc != NQ || depth_before[j as usize] > 0).count();
            let mut nsw = 0; let mut lab = ops[w[0] as usize].t;
            for j in *ip as usize..*e as usize { let x = &ops[j]; if x.kind == K_SWAP { if x.c1 == lab { lab = x.t; nsw += 1; } else if x.t == lab { lab = x.c1; nsw += 1; } } }
            eprintln!("RVR end {} endkind {} ip {} first_write {} writes {} ccx {} cond_writes {} swaps {} label_end_ok {}", e, ops[*e as usize].kind, ip, w[0], w.len(), nccx, ncond, nsw, lab == ops[*e as usize].t);
        }
        let t0 = ops[w[0] as usize].t; // the content's label at the absorbed part's first write (nothing touches it from ip)
        let f = nb; nb += 1;
        ed.before.entry(*ip).or_default().push(L { kind: K_HMR, c2: NQ, c1: NQ, t: t0, ct: f, cc: NQ, rt: NQ });
        for &j in w {
            let x = ops[j as usize];
            let mut p = match x.kind {
                K_X => L { kind: K_NEG, c2: NQ, c1: NQ, t: NQ, ct: NQ, cc: NQ, rt: NQ },
                K_CX => op(K_Z, NQ, x.c1, NQ),
                _ => { nccx += 1; op(K_CZ, x.c1, x.c2, NQ) }
            };
            if fault == "r" && !faulted && x.kind == K_CCX { p = op(K_Z, NQ, x.c1, NQ); faulted = true; }
            let v = if x.cc == NQ { p.cc = f; vec![p] } else {
                p.cc = x.cc;
                vec![L { kind: K_PUSH, c2: NQ, c1: NQ, t: NQ, ct: NQ, cc: f, rt: NQ }, p, L { kind: K_POP, c2: NQ, c1: NQ, t: NQ, ct: NQ, cc: NQ, rt: NQ }] };
            let drop2 = (fault == "r2" && !faulted && x.kind == K_CCX) || (fault == "r3" && !faulted && x.kind != K_CCX);
            if drop2 { faulted = true; }
            ed.replace.insert(j, if drop2 { vec![] } else { v });
        }
        let eo = ops[*e as usize];
        if eo.kind == K_HMR {
            // the old outcome bit takes the moved measurement's value; an idle reset keeps the measurement count
            ed.replace.insert(*e, vec![L { kind: K_BS0, c2: NQ, c1: NQ, t: NQ, ct: eo.ct, cc: NQ, rt: NQ },
                L { kind: K_BINV, c2: NQ, c1: NQ, t: NQ, ct: eo.ct, cc: f, rt: NQ }, L { kind: K_R, c2: NQ, c1: NQ, t: eo.t, ct: NQ, cc: NQ, rt: NQ }]);
        }
    }
    let n = plan.len();
    (ed, n, nccx, nccx as f64)
}

pub fn run(ops: Vec<Op>) -> Vec<Op> {
    let sw = std::env::var("SL_COND").unwrap_or_default();
    if sw.is_empty() || sw == "0" { return ops; }
    let levers = if sw == "1" { "mufsr".to_string() } else { sw };
    let fault = std::env::var("SL_COND_FAULT").unwrap_or_default();
    let mut l: Vec<L> = ops.iter().map(to_l).collect();
    drop(ops);
    let w0 = weight_of(&l);
    if std::env::var("SL_COND_ALIGN").is_ok_and(|v| v == "1") {
        let mut nq = 0u32; for o in &l { for q in [o.c1, o.c2, o.t] { if q != NQ { nq = nq.max(q + 1); } } }
        let idle = L { kind: K_R, c2: NQ, c1: NQ, t: nq, ct: NQ, cc: NQ, rt: NQ };
        let mut ed = Edits::new(); let (mut nu, mut nr) = (0, 0);
        if levers.contains('u') { let (e2, _, _) = plan_muf(&l, "u", ""); for k in e2.replace.keys() { ed.before.entry(*k).or_default().push(idle); nu += 1; } }
        if levers.contains('r') { let (e2, _, _, _) = plan_r(&l, ""); for k in e2.before.keys() { ed.before.entry(*k).or_default().push(idle); nr += 1; } }
        l = ed.apply(&l);
        eprintln!("SL_COND ALIGN: unchanged gate list + idle resets of wire {nq} at {nu} u sites and {nr} r windows");
        return l.iter().map(from_l).collect();
    }
    if levers.contains('m') || levers.contains('u') || levers.contains('f') {
        let first: String = levers.chars().filter(|c| "muf".contains(*c)).collect();
        let (ed, cnt, sav) = plan_muf(&l, &first, &fault);
        l = ed.apply(&l);
        eprintln!("SL_COND m: {} CCX -> CX ({:.2} T); u: {} CCX -> HMR + CZ-if ({:.2} T); f: {} ANDs as phases ({:.2} T)", cnt[0], sav[0], cnt[1], sav[1], cnt[2], sav[2]);
    }
    if levers.contains('s') {
        // on the stream after m, u, f: f turns ANDs read only by phases into CZ reads of their operands, which can leave
        // those operands read only under a bit
        let (ed, cnt, sav) = plan_muf(&l, "s", &fault);
        l = ed.apply(&l);
        eprintln!("SL_COND s: {} ANDs built under their read bit ({:.2} T)", cnt[3], sav[3]);
    }
    if levers.contains('r') {
        let (ed, n, nccx, sav) = plan_r(&l, &fault);
        l = ed.apply(&l);
        eprintln!("SL_COND r: {n} absorbed windows (reset or measured end), {nccx} CCX -> CZ-if ({sav:.2} T)");
    }
    { let g = GUARD_HITS.lock().unwrap(); eprintln!("SL_COND guards{}: G1 {} G2 {} G3 {} G4 {}", if guards_on() { "" } else { " (OFF)" }, g[0], g[1], g[2], g[3]); }
    let w1 = weight_of(&l);
    eprintln!("SL_COND static expected Toffoli {w0:.1} -> {w1:.1} ({:.1}){}", w1 - w0, if fault.is_empty() { String::new() } else { format!("; FAULT {fault}") });
    l.iter().map(from_l).collect()
}

pub(super) fn prefix_uncompute(ops: Vec<Op>) -> Vec<Op> {
    let l: Vec<L> = ops.iter().map(to_l).collect();
    drop(ops);
    let a = analyze(&l);
    if a.pref.is_empty() {
        eprintln!("prefix_uncompute: 0 sites");
        return l.iter().map(from_l).collect();
    }
    let bit = max_bit(&l);
    let mut replace: HashMap<u32, Vec<L>> = HashMap::new();
    for (k, ws) in &a.pref {
        let o = l[*k as usize];
        let seq = match ws {
            None => Vec::new(),
            Some(ws) => {
                let mut seq: Vec<L> = Vec::with_capacity(ws.len() * 2 + 2);
                for &w in ws {
                    if w == NQ { seq.push(op(K_X, NQ, o.t, NQ)); } else { seq.push(op(K_CX, w, o.t, NQ)); }
                }
                seq.push(L { kind: K_HMR, c2: NQ, c1: NQ, t: o.t, ct: bit, cc: NQ, rt: NQ });
                seq.push(op(K_CZ, o.c1, o.c2, bit));
                for &w in ws.iter().rev() {
                    if w == NQ { seq.push(op(K_X, NQ, o.t, NQ)); } else { seq.push(op(K_CX, w, o.t, NQ)); }
                }
                seq
            }
        };
        replace.insert(*k, seq);
    }
    let mut out = Vec::with_capacity(l.len() + replace.len() * 4);
    for (i, o) in l.iter().enumerate() {
        if let Some(seq) = replace.get(&(i as u32)) {
            out.extend_from_slice(seq);
        } else {
            out.push(*o);
        }
    }
    let n_drop = a.pref.iter().filter(|(_, w)| w.is_none()).count();
    eprintln!("prefix_uncompute: {} rewrite + {} delete (bit {bit})", a.pref.len() - n_drop, n_drop);
    out.iter().map(from_l).collect()
}
