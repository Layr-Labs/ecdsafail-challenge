//! AND leases: keep an erased AND value alive instead of computing it again (an exact emission-time post-pass).
//!
//! This is a Rust port of track kg's opstream lease pass (Python: `src/opstream/passes/lease.py` and
//! `src/opstream/passes/valnum.py`, branch experiment/kaggle-vqcc-20261027 at commit 1ac00095), run with the
//! settings of the cluster's Q8 run on our 839 stream: atom cap 64, expand 16, max_span 1e6, forget_span 1e6,
//! parking and in-place leases on. Credits: the lease idea is in MonitSharma's PR #714 (exact repeated-AND cache)
//! and Th0rgal's 9ef3139d (24 lease edits, decoded by track t2); the opstream pass is by track kg.
//!
//! Pattern:
//!   i: HMR(t -> b) erases t, which holds a value v; diagonal fixups under b repair the phase;
//!   j: CCX(a, b' -> t') later computes the same value v into a zero wire t'.
//! GF(2) value numbering matches the AND at j with v in one of two ways:
//! - direct: the form of t at i equals the AND form at j (exact on every input);
//! - asserted: the fixups under b assert v (they cancel the kick (-1)^(b v) only if v equals the XOR of their
//!   terms), so on every input where the original circuit is correct, v equals that XOR.
//! Two edits remove the CCX at j:
//! - in place: when no op touches t over [i, j], replace the HMR by BIT_STORE0(b); at j delete the CCX if t' = t,
//!   else SWAP(t, t');
//! - parked: else pick a wire u that is zero and untouched over [i, j] and not a register wire; at i
//!   SWAP(t, u); HMR(t -> b); BIT_STORE0(b), so the HMR measures a zero wire and the draw count stays the same;
//!   at j SWAP(u, t').
//! Both add X(t') when v is the complement of the AND. Every reader of b before its next unconditional write must
//! be a diagonal gate under b, so b = 0 is the b = 0 branch of the original circuit.
//!
//! Determinism: atom ids differ from the Python run (Python numbers atoms in set-iteration order), but every
//! decision depends only on form equality, form sizes and op positions, so the edits are the same. No decision
//! reads a hash-map iteration order: maps are only looked up, inserted into and pruned with `retain`.
//!
//! Knobs: the constants below are the official settings. Environment variables override them for development
//! only (the official build runs with an empty environment): LEASE_PASS (0 = off), LEASE_CAP, LEASE_EXPAND,
//! LEASE_MAX_SPAN, LEASE_FORGET_SPAN, LEASE_MAX_DIRECT, LEASE_PARKING (0/1), LEASE_IN_PLACE (0/1), LEASE_RECORD
//! (a path; writes one JSON line per accepted lease).

use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::rc::Rc;

/// The pass runs in the official build.
pub const ON: bool = true;
/// Accept direct symbolic equality only, never phase-inferred values.
const DIRECT_MATCH_ONLY: bool = true;
/// Atom cap: a form with more atoms becomes one fresh atom.
pub const CAP: usize = 64;
/// Products of forms with at most this many atom pairs are expanded into pair atoms.
pub const EXPAND: usize = 16;
/// Erases older than this many ops are forgotten (memory bound of the lease index).
pub const MAX_SPAN: usize = 1_000_000;
/// Hash-consing entries unused for this many ops are forgotten (memory bound of the value numbering).
pub const FORGET_SPAN: usize = 1_000_000;
/// Direct matching indexes erased forms of at most this many atoms.
pub const MAX_DIRECT: usize = 64;
/// Parked leases (an idle zero wire holds the value) are allowed.
pub const PARKING: bool = true;
/// In-place leases (the erased wire keeps the value) are allowed.
pub const IN_PLACE: bool = false; // 28 Oct: parking only for sends (strict gate L2: 0 rows differ); in-place leases flip phase flags on already-failing shots

#[derive(Clone, Debug)]
pub struct Knobs {
    pub on: bool,
    pub cap: usize,
    pub expand: usize,
    pub max_span: usize,
    pub forget_span: usize,
    pub max_direct: usize,
    pub parking: bool,
    pub in_place: bool,
    pub record: Option<String>,
}

impl Knobs {
    pub fn official() -> Self {
        Knobs { on: ON, cap: CAP, expand: EXPAND, max_span: MAX_SPAN, forget_span: FORGET_SPAN, max_direct: MAX_DIRECT,
                parking: PARKING, in_place: IN_PLACE, record: None }
    }

    /// The official settings with development overrides from the environment.
    pub fn from_env() -> Self {
        fn num(name: &str, default: usize) -> usize {
            std::env::var(name).ok().and_then(|v| v.trim().parse().ok()).unwrap_or(default)
        }
        fn flag(name: &str, default: bool) -> bool {
            std::env::var(name).ok().map(|v| v.trim() != "0").unwrap_or(default)
        }
        let k = Knobs::official();
        Knobs { on: flag("LEASE_PASS", k.on), cap: num("LEASE_CAP", k.cap), expand: num("LEASE_EXPAND", k.expand),
                max_span: num("LEASE_MAX_SPAN", k.max_span), forget_span: num("LEASE_FORGET_SPAN", k.forget_span),
                max_direct: num("LEASE_MAX_DIRECT", k.max_direct), parking: flag("LEASE_PARKING", k.parking),
                in_place: flag("LEASE_IN_PLACE", k.in_place),
                record: std::env::var("LEASE_RECORD").ok().filter(|v| !v.is_empty()) }
    }
}

// ---- deterministic hashing ---------------------------------------------------------------------------------

#[derive(Default, Clone, Copy)]
struct Fx(u64);

impl Fx {
    #[inline]
    fn add(&mut self, w: u64) {
        self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl Hasher for Fx {
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.add(*b as u64);
        }
    }
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

type FxMap<A, B> = HashMap<A, B, BuildHasherDefault<Fx>>;

fn fxmap<A, B>() -> FxMap<A, B> {
    HashMap::with_hasher(BuildHasherDefault::<Fx>::default())
}

// ---- forms: XOR of atoms, as a sorted atom list with a cached hash ------------------------------------------

struct FormData {
    h: u64,
    a: Box<[u32]>,
}

#[derive(Clone)]
struct Form(Rc<FormData>);

impl PartialEq for Form {
    fn eq(&self, o: &Self) -> bool {
        Rc::ptr_eq(&self.0, &o.0) || (self.0.h == o.0.h && self.0.a == o.0.a)
    }
}

impl Eq for Form {}

impl Hash for Form {
    fn hash<H: Hasher>(&self, s: &mut H) {
        s.write_u64(self.0.h);
    }
}

fn hash_atoms(a: &[u32]) -> u64 {
    let mut h: u64 = 0x9e37_79b9_7f4a_7c15 ^ a.len() as u64;
    for &x in a {
        h = (h.rotate_left(5) ^ x as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    h ^ (h >> 29)
}

impl Form {
    /// `a` must be sorted and free of repeats.
    fn new(a: Vec<u32>) -> Form {
        Form(Rc::new(FormData { h: hash_atoms(&a), a: a.into_boxed_slice() }))
    }
    #[inline]
    fn is_empty(&self) -> bool {
        self.0.a.is_empty()
    }
    #[inline]
    fn len(&self) -> usize {
        self.0.a.len()
    }
    #[inline]
    fn atoms(&self) -> &[u32] {
        &self.0.a
    }
    fn xor(&self, o: &Form) -> Form {
        if o.is_empty() {
            return self.clone();
        }
        if self.is_empty() {
            return o.clone();
        }
        Form::new(xor_slices(self.atoms(), o.atoms()))
    }
}

fn xor_slices(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if a[i] < b[j] {
            out.push(a[i]);
            i += 1;
        } else if a[i] > b[j] {
            out.push(b[j]);
            j += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

// ---- value numbering (port of valnum.ValueNumbering at 1ac00095) -------------------------------------------

struct Vn {
    cap: usize,
    expand: usize,
    forget_span: u64,
    n_atoms: u64,
    pair_info: FxMap<u32, (u32, u32)>,
    and2: FxMap<(u32, u32), (u32, u64)>,
    andf: FxMap<(Form, Form), (u32, u64)>,
    holders: FxMap<Form, u32>,
    qf: Vec<Form>,
    qc: Vec<u8>,
    bf: Vec<Form>,
    bcst: Vec<u8>,
    stack: Vec<(Form, u8)>,
    cond: (Form, u8),
    depth: u64,
    index: u64,
    capped: u64,
    forgotten: u64,
    empty: Form,
}

impl Vn {
    fn new(nq: usize, nb: usize, cap: usize, expand: usize, forget_span: usize) -> Vn {
        let empty = Form::new(vec![]);
        Vn { cap, expand, forget_span: forget_span as u64, n_atoms: 0, pair_info: fxmap(), and2: fxmap(), andf: fxmap(),
             holders: fxmap(), qf: vec![empty.clone(); nq], qc: vec![0; nq], bf: vec![empty.clone(); nb],
             bcst: vec![0; nb], stack: vec![], cond: (empty.clone(), 1), depth: 0, index: 0, capped: 0, forgotten: 0,
             empty }
    }

    fn new_atom(&mut self) -> u32 {
        let a = self.n_atoms;
        self.n_atoms += 1;
        assert!(a < u32::MAX as u64, "lease pass: atom ids overflow u32");
        a as u32
    }

    fn single(&mut self) -> Form {
        let a = self.new_atom();
        Form::new(vec![a])
    }

    fn set_input_q(&mut self, w: usize) {
        let f = self.single();
        self.set_q(w, f, 0);
    }

    fn set_input_b(&mut self, b: usize) {
        let f = self.single();
        self.bf[b] = f;
        self.bcst[b] = 0;
    }

    fn cap_form(&mut self, f: Form) -> Form {
        if f.len() > self.cap {
            self.capped += 1;
            return self.single();
        }
        f
    }

    fn and_atoms(&mut self, a: u32, b: u32) -> u32 {
        let key = if a < b { (a, b) } else { (b, a) };
        let index = self.index;
        if let Some(v) = self.and2.get_mut(&key) {
            v.1 = index;
            return v.0;
        }
        if let Some(&(x, y)) = self.pair_info.get(&a) {
            if x == b || y == b {
                return a;
            }
        }
        if let Some(&(x, y)) = self.pair_info.get(&b) {
            if x == a || y == a {
                return b;
            }
        }
        let r = self.new_atom();
        self.and2.insert(key, (r, index));
        self.pair_info.insert(r, key);
        r
    }

    /// The product of the forms (fs, c) and (gs, d).
    fn mul(&mut self, fs: &Form, c: u8, gs: &Form, d: u8) -> (Form, u8) {
        if fs.is_empty() {
            return if c != 0 { (gs.clone(), d) } else { (self.empty.clone(), 0) };
        }
        if gs.is_empty() {
            return if d != 0 { (fs.clone(), c) } else { (self.empty.clone(), 0) };
        }
        if fs == gs {
            return if c == d { (fs.clone(), c) } else { (self.empty.clone(), 0) };
        }
        let mut prod: Vec<u32>;
        if fs.len() * gs.len() <= self.expand {
            let mut acc = Vec::with_capacity(fs.len() * gs.len());
            for &a in fs.atoms() {
                for &b in gs.atoms() {
                    let x = if a == b { a } else { self.and_atoms(a, b) };
                    acc.push(x);
                }
            }
            acc.sort_unstable();
            prod = Vec::with_capacity(acc.len());
            let mut k = 0;
            while k < acc.len() {
                let x = acc[k];
                let mut m = 1;
                while k + m < acc.len() && acc[k + m] == x {
                    m += 1;
                }
                if m % 2 == 1 {
                    prod.push(x);
                }
                k += m;
            }
        } else {
            let key = if fs.atoms() <= gs.atoms() { (fs.clone(), gs.clone()) } else { (gs.clone(), fs.clone()) };
            let index = self.index;
            let r = match self.andf.get_mut(&key) {
                Some(v) => {
                    v.1 = index;
                    v.0
                }
                None => {
                    let r = self.new_atom();
                    self.andf.insert(key, (r, index));
                    r
                }
            };
            prod = vec![r];
        }
        if d != 0 {
            prod = xor_slices(&prod, fs.atoms());
        }
        if c != 0 {
            prod = xor_slices(&prod, gs.atoms());
        }
        let f = self.cap_form(Form::new(prod));
        (f, c & d)
    }

    fn set_q(&mut self, w: usize, fs: Form, c: u8) {
        if self.qf[w] != fs {
            let old = self.qf[w].clone();
            if !old.is_empty() {
                let n = self.holders.get_mut(&old).expect("holders entry");
                *n -= 1;
                if *n == 0 {
                    self.holders.remove(&old);
                }
            }
            if !fs.is_empty() {
                *self.holders.entry(fs.clone()).or_insert(0) += 1;
            }
            self.qf[w] = fs;
        }
        self.qc[w] = c;
    }

    #[inline]
    fn is_zero(&self, w: usize) -> bool {
        self.qf[w].is_empty() && self.qc[w] == 0
    }

    fn condition(&mut self, bc: BitId) -> (Form, u8) {
        let (cfs, ccst) = self.cond.clone();
        if bc != NO_BIT {
            let b = bc.0 as usize;
            let (bf, bcst) = (self.bf[b].clone(), self.bcst[b]);
            return self.mul(&cfs, ccst, &bf, bcst);
        }
        (cfs, ccst)
    }

    fn forget(&mut self) {
        let limit = self.index - self.forget_span;
        let mut dropped = 0u64;
        let pair_info = &mut self.pair_info;
        self.and2.retain(|_, v| {
            if v.1 < limit {
                pair_info.remove(&v.0);
                dropped += 1;
                false
            } else {
                true
            }
        });
        self.andf.retain(|_, v| {
            if v.1 < limit {
                dropped += 1;
                false
            } else {
                true
            }
        });
        self.forgotten += dropped;
    }

    fn step(&mut self, o: &Op) {
        self.index += 1;
        if self.forget_span != 0 && self.index % 65536 == 0 && self.index > self.forget_span {
            self.forget();
        }
        match o.kind {
            K::PushCondition => {
                let b = o.c_condition.0 as usize;
                let (cf, cc) = self.cond.clone();
                let (bf, bcst) = (self.bf[b].clone(), self.bcst[b]);
                self.stack.push((cf.clone(), cc));
                self.cond = self.mul(&cf, cc, &bf, bcst);
                self.depth += 1;
                return;
            }
            K::PopCondition => {
                if let Some(c) = self.stack.pop() {
                    self.cond = c;
                    self.depth -= 1;
                }
                return;
            }
            K::Neg | K::Z | K::CZ | K::CCZ | K::Register | K::AppendToRegister | K::DebugPrint => return,
            _ => {}
        }
        let (cfs, ccst) = self.condition(o.c_condition);
        let konst = cfs.is_empty();
        match o.kind {
            K::CX => {
                let (c1, t) = (o.q_control1.0 as usize, o.q_target.0 as usize);
                if konst {
                    if ccst != 0 {
                        let f = self.qf[t].xor(&self.qf[c1]);
                        let f = self.cap_form(f);
                        let c = self.qc[t] ^ self.qc[c1];
                        self.set_q(t, f, c);
                    }
                } else {
                    let (f1, c1v) = (self.qf[c1].clone(), self.qc[c1]);
                    let (dfs, dc) = self.mul(&cfs, ccst, &f1, c1v);
                    let f = self.qf[t].xor(&dfs);
                    let f = self.cap_form(f);
                    let c = self.qc[t] ^ dc;
                    self.set_q(t, f, c);
                }
            }
            K::CCX => {
                let (c2, c1, t) = (o.q_control2.0 as usize, o.q_control1.0 as usize, o.q_target.0 as usize);
                let (f1, k1, f2, k2) = (self.qf[c1].clone(), self.qc[c1], self.qf[c2].clone(), self.qc[c2]);
                let (afs, ac) = self.mul(&f1, k1, &f2, k2);
                if konst {
                    if ccst != 0 {
                        let f = self.qf[t].xor(&afs);
                        let f = self.cap_form(f);
                        let c = self.qc[t] ^ ac;
                        self.set_q(t, f, c);
                    }
                } else {
                    let (dfs, dc) = self.mul(&cfs, ccst, &afs, ac);
                    let f = self.qf[t].xor(&dfs);
                    let f = self.cap_form(f);
                    let c = self.qc[t] ^ dc;
                    self.set_q(t, f, c);
                }
            }
            K::X => {
                let t = o.q_target.0 as usize;
                let f = self.qf[t].xor(&cfs);
                let f = self.cap_form(f);
                let c = self.qc[t] ^ ccst;
                self.set_q(t, f, c);
            }
            K::Swap => {
                let (a, t) = (o.q_control1.0 as usize, o.q_target.0 as usize);
                if konst {
                    if ccst != 0 {
                        let (fa, ca, fb, cb) = (self.qf[a].clone(), self.qc[a], self.qf[t].clone(), self.qc[t]);
                        self.set_q(a, fb, cb);
                        self.set_q(t, fa, ca);
                    }
                } else {
                    let x = self.qf[a].xor(&self.qf[t]);
                    let xc = self.qc[a] ^ self.qc[t];
                    let (dfs, dc) = self.mul(&cfs, ccst, &x, xc);
                    let fa = self.qf[a].xor(&dfs);
                    let fa = self.cap_form(fa);
                    let ca = self.qc[a] ^ dc;
                    self.set_q(a, fa, ca);
                    let ft = self.qf[t].xor(&dfs);
                    let ft = self.cap_form(ft);
                    let ct = self.qc[t] ^ dc;
                    self.set_q(t, ft, ct);
                }
            }
            K::R | K::Hmr => {
                let t = o.q_target.0 as usize;
                let hmr = o.kind == K::Hmr;
                let m = if hmr { Some(self.single()) } else { None };
                if konst {
                    if ccst != 0 {
                        let e = self.empty.clone();
                        self.set_q(t, e, 0);
                        if let Some(m) = m {
                            let b = o.c_target.0 as usize;
                            self.bf[b] = m;
                            self.bcst[b] = 0;
                        }
                    }
                } else {
                    let (ft, ct) = (self.qf[t].clone(), self.qc[t]);
                    let (nfs, nc) = self.mul(&ft, ct, &cfs, ccst ^ 1);
                    self.set_q(t, nfs, nc);
                    if let Some(m) = m {
                        let b = o.c_target.0 as usize;
                        let x = self.bf[b].xor(&m);
                        let xc = self.bcst[b];
                        let (dfs, dc) = self.mul(&cfs, ccst, &x, xc);
                        let f = self.bf[b].xor(&dfs);
                        self.bf[b] = self.cap_form(f);
                        self.bcst[b] ^= dc;
                    }
                }
            }
            K::BitInvert => {
                let b = o.c_target.0 as usize;
                let f = self.bf[b].xor(&cfs);
                self.bf[b] = self.cap_form(f);
                self.bcst[b] ^= ccst;
            }
            K::BitStore0 => {
                let b = o.c_target.0 as usize;
                if konst {
                    if ccst != 0 {
                        self.bf[b] = self.empty.clone();
                        self.bcst[b] = 0;
                    }
                } else {
                    let (fb, cb) = (self.bf[b].clone(), self.bcst[b]);
                    let (f, c) = self.mul(&fb, cb, &cfs, ccst ^ 1);
                    self.bf[b] = f;
                    self.bcst[b] = c;
                }
            }
            K::BitStore1 => {
                let b = o.c_target.0 as usize;
                if konst {
                    if ccst != 0 {
                        self.bf[b] = self.empty.clone();
                        self.bcst[b] = 1;
                    }
                } else {
                    let (fb, cb) = (self.bf[b].clone(), self.bcst[b]);
                    let (dfs, dc) = self.mul(&fb, cb, &cfs, ccst);
                    let f = fb.xor(&cfs).xor(&dfs);
                    self.bf[b] = self.cap_form(f);
                    self.bcst[b] = cb ^ ccst ^ dc;
                }
            }
            _ => {}
        }
    }
}

// ---- per-bit reads and writes (port of lease.BitIndex) ------------------------------------------------------

fn is_diag(k: K) -> bool {
    matches!(k, K::Neg | K::Z | K::CZ | K::CCZ)
}

fn is_bit_write(k: K) -> bool {
    matches!(k, K::BitStore0 | K::BitStore1 | K::BitInvert | K::Hmr)
}

/// Events per bit, sorted by position: (position << 2) | code. Codes: 0 diagonal reader, 1 other reader,
/// 2 unconditional overwrite at depth 0, 3 other write (conditional, inside a block, or BIT_INVERT).
struct BitIndex {
    off: Vec<usize>,
    ev: Vec<u32>,
}

impl BitIndex {
    fn new(ops: &[Op], nb: usize) -> BitIndex {
        assert!(ops.len() < (1usize << 30), "lease pass: too many ops for the bit index");
        let mut off = vec![0usize; nb + 1];
        for o in ops {
            if o.c_condition != NO_BIT {
                off[o.c_condition.0 as usize + 1] += 1;
            }
            if o.c_target != NO_BIT && is_bit_write(o.kind) {
                off[o.c_target.0 as usize + 1] += 1;
            }
        }
        for b in 0..nb {
            off[b + 1] += off[b];
        }
        let mut fill = off.clone();
        let mut ev = vec![0u32; off[nb]];
        let mut depth: i64 = 0;
        for (j, o) in ops.iter().enumerate() {
            let pos = (j as u32) << 2;
            if o.c_condition != NO_BIT {
                let b = o.c_condition.0 as usize;
                ev[fill[b]] = pos | if is_diag(o.kind) { 0 } else { 1 };
                fill[b] += 1;
            }
            if o.c_target != NO_BIT && is_bit_write(o.kind) {
                let b = o.c_target.0 as usize;
                let uncond = o.c_condition == NO_BIT && depth == 0 && o.kind != K::BitInvert;
                ev[fill[b]] = pos | if uncond { 2 } else { 3 };
                fill[b] += 1;
            }
            match o.kind {
                K::PushCondition => depth += 1,
                K::PopCondition => depth -= 1,
                _ => {}
            }
        }
        BitIndex { off, ev }
    }

    /// (ok, last): ok when, after op i, bit b is read only by diagonal gates until an unconditional overwrite (or
    /// the end); last is the position of the last such reader (i when there is none).
    fn diagonal_readers(&self, i: usize, b: usize) -> (bool, usize) {
        let ev = &self.ev[self.off[b]..self.off[b + 1]];
        let k = ev.partition_point(|&v| ((v >> 2) as usize) <= i);
        let mut last = i;
        for &v in &ev[k..] {
            match v & 3 {
                2 => return (true, last),
                1 | 3 => return (false, last),
                _ => last = (v >> 2) as usize,
            }
        }
        (true, last)
    }
}

// ---- the lease plan (port of lease.plan_iter) ----------------------------------------------------------------

struct Entry {
    i: usize,
    t: usize,
    b: usize,
    last: usize,
    afs: Form,
    ac: u8,
    ok: bool,
    dc: u8,
    dfs: Option<Form>,
    used: bool,
}

type EntryRef = Rc<RefCell<Entry>>;

#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub erase_candidates: u64,
    pub erase_rejected_bit_readers: u64,
    pub asserted_erases: u64,
    pub recompute_candidates: u64,
    pub rejected_erase_used: u64,
    pub in_place: u64,
    pub parked: u64,
    pub match_direct: u64,
    pub match_asserted: u64,
    pub rejected_no_idle_wire: u64,
    pub rejected_touched: u64,
    pub atoms: u64,
    pub capped_forms: u64,
    pub forgotten: u64,
    pub qubits: usize,
    pub bits: usize,
}

pub struct Lease {
    pub in_place: bool,
    pub direct: bool,
    pub erase: usize,
    pub recompute: usize,
    pub wire: usize,
    pub park: usize,
    pub target: usize,
    pub bit: usize,
    pub flip: bool,
}

fn op_swap(a: usize, b: usize) -> Op {
    let mut o = Op::empty();
    o.kind = K::Swap;
    o.q_control1 = QubitId(a as u64);
    o.q_target = QubitId(b as u64);
    o
}

fn op_x(t: usize) -> Op {
    let mut o = Op::empty();
    o.kind = K::X;
    o.q_target = QubitId(t as u64);
    o
}

fn op_bs0(b: usize) -> Op {
    let mut o = Op::empty();
    o.kind = K::BitStore0;
    o.c_target = BitId(b as u64);
    o
}

/// Find the lease sites. Returns (edits sorted by op index, accepted leases, stats).
pub fn plan(ops: &[Op], kn: &Knobs) -> (Vec<(usize, Vec<Op>)>, Vec<Lease>, Stats) {
    let mut nq = 0usize;
    let mut nb = 0usize;
    for o in ops {
        for q in [o.q_control2, o.q_control1, o.q_target] {
            if q != NO_QUBIT {
                nq = nq.max(q.0 as usize + 1);
            }
        }
        for b in [o.c_target, o.c_condition] {
            if b != NO_BIT {
                nb = nb.max(b.0 as usize + 1);
            }
        }
    }
    let bits = BitIndex::new(ops, nb);
    let mut vn = Vn::new(nq.max(1), nb.max(1), kn.cap, kn.expand, kn.forget_span);
    // Input atoms: one per APPEND_TO_REGISTER, in stream order (the registers are the inputs and outputs).
    let mut reg_q = vec![false; nq.max(1)];
    let mut reg_b = vec![false; nb.max(1)];
    for o in ops {
        if o.kind == K::AppendToRegister {
            if o.q_target != NO_QUBIT {
                vn.set_input_q(o.q_target.0 as usize);
                reg_q[o.q_target.0 as usize] = true;
            } else if o.c_target != NO_BIT {
                vn.set_input_b(o.c_target.0 as usize);
                reg_b[o.c_target.0 as usize] = true;
            }
        }
    }

    let mut st = Stats { qubits: nq, bits: nb, ..Stats::default() };
    let mut last_touch = vec![-1i64; nq.max(1)];
    // Accepted lease spans end at increasing recompute positions, so a wire is free over [lo, hi] (hi = now)
    // exactly when its last reserved span ended before lo.
    let mut reserved_end = vec![-1i64; nq.max(1)];
    let mut by_form: FxMap<Form, EntryRef> = fxmap();
    let mut pending: Vec<Option<EntryRef>> = vec![None; nb.max(1)];
    let mut order: VecDeque<(usize, Form)> = VecDeque::new();
    let mut edited = vec![false; ops.len()];
    let mut edits: Vec<(usize, Vec<Op>)> = vec![];
    let mut leases: Vec<Lease> = vec![];

    for (j, o) in ops.iter().enumerate() {
        let k = o.kind;
        let bc = o.c_condition;
        if bc != NO_BIT {
            if let Some(e) = pending[bc.0 as usize].clone() {
                let (ok, last) = {
                    let eb = e.borrow();
                    (eb.ok, eb.last)
                };
                if ok && j <= last {
                    let trivial = vn.depth == 0 && vn.cond.0.is_empty() && vn.cond.1 == 1;
                    if is_diag(k) && trivial {
                        let (tf, tc) = match k {
                            K::Z => {
                                let q = o.q_target.0 as usize;
                                (vn.qf[q].clone(), vn.qc[q])
                            }
                            K::CZ => {
                                let (a, b) = (o.q_control1.0 as usize, o.q_target.0 as usize);
                                let (fa, ca, fb, cb) = (vn.qf[a].clone(), vn.qc[a], vn.qf[b].clone(), vn.qc[b]);
                                vn.mul(&fa, ca, &fb, cb)
                            }
                            K::CCZ => {
                                let (a, b, c) =
                                    (o.q_control2.0 as usize, o.q_control1.0 as usize, o.q_target.0 as usize);
                                let (fa, ca, fb, cb) = (vn.qf[a].clone(), vn.qc[a], vn.qf[b].clone(), vn.qc[b]);
                                let (f1, c1) = vn.mul(&fa, ca, &fb, cb);
                                let (fc, cc) = (vn.qf[c].clone(), vn.qc[c]);
                                vn.mul(&f1, c1, &fc, cc)
                            }
                            _ => (vn.empty.clone(), 1), // NEG
                        };
                        let mut eb = e.borrow_mut();
                        eb.afs = eb.afs.xor(&tf);
                        eb.ac ^= tc;
                    } else {
                        e.borrow_mut().ok = false;
                    }
                    let key = {
                        let eb = e.borrow();
                        if j == eb.last && eb.ok && !eb.afs.is_empty() { Some(eb.afs.clone()) } else { None }
                    };
                    if let Some(key) = key.filter(|_| !DIRECT_MATCH_ONLY) {
                        by_form.insert(key.clone(), e.clone());
                        order.push_back((j, key));
                        st.asserted_erases += 1;
                    }
                }
            }
        }
        if k == K::Hmr || k == K::CCX {
            let top = vn.depth == 0 && bc == NO_BIT && vn.cond.0.is_empty() && vn.cond.1 == 1;
            if k == K::Hmr && top {
                let t = o.q_target.0 as usize;
                let (fs, c) = (vn.qf[t].clone(), vn.qc[t]);
                let b = o.c_target.0 as usize;
                if !fs.is_empty() && !reg_b[b] {
                    let (ok, last) = bits.diagonal_readers(j, b);
                    if ok {
                        let dfs = if fs.len() <= kn.max_direct { Some(fs.clone()) } else { None };
                        let e = Rc::new(RefCell::new(Entry { i: j, t, b, last, afs: vn.empty.clone(), ac: 0, ok: true,
                                                             dc: c, dfs: dfs.clone(), used: false }));
                        pending[b] = Some(e.clone());
                        if dfs.is_some() {
                            by_form.insert(fs.clone(), e);
                            order.push_back((j, fs));
                        }
                        st.erase_candidates += 1;
                    } else {
                        st.erase_rejected_bit_readers += 1;
                    }
                }
            } else if k == K::CCX && top && vn.is_zero(o.q_target.0 as usize) {
                let (c1, c2) = (o.q_control1.0 as usize, o.q_control2.0 as usize);
                let (f1, k1, f2, k2) = (vn.qf[c1].clone(), vn.qc[c1], vn.qf[c2].clone(), vn.qc[c2]);
                let (afs, ac) = vn.mul(&f1, k1, &f2, k2);
                let found = if afs.is_empty() { None } else { by_form.get(&afs).cloned() };
                if let Some(e) = found {
                    let usable = {
                        let eb = e.borrow();
                        !vn.holders.contains_key(&afs) && eb.last < j && !eb.used
                    };
                    if usable {
                        let (i, t, b, direct, value_const) = {
                            let eb = e.borrow();
                            let direct = eb.dfs.as_ref() == Some(&afs);
                            (eb.i, eb.t, eb.b, direct, if direct { eb.dc } else { eb.ac })
                        };
                        let tp = o.q_target.0 as usize;
                        st.recompute_candidates += 1;
                        let flip = value_const != ac;
                        let free = |w: usize, lo: usize, hi: usize, reserved_end: &Vec<i64>| {
                            debug_assert!(reserved_end[w] < hi as i64);
                            reserved_end[w] < lo as i64
                        };
                        if edited[i] {
                            st.rejected_erase_used += 1;
                        } else if kn.in_place && last_touch[t] == i as i64 && free(t, i, j, &reserved_end)
                            && (t == tp || free(tp, j, j, &reserved_end)) {
                            let mut at_j = if t == tp { vec![] } else { vec![op_swap(t, tp)] };
                            if flip {
                                at_j.push(op_x(tp));
                            }
                            edits.push((i, vec![op_bs0(b)]));
                            edits.push((j, at_j));
                            edited[i] = true;
                            edited[j] = true;
                            reserved_end[t] = reserved_end[t].max(j as i64);
                            e.borrow_mut().used = true;
                            st.in_place += 1;
                            if direct { st.match_direct += 1 } else { st.match_asserted += 1 }
                            leases.push(Lease { in_place: true, direct, erase: i, recompute: j, wire: t, park: t,
                                                target: tp, bit: b, flip });
                        } else if kn.parking {
                            let mut u = None;
                            for w in 0..nq {
                                if last_touch[w] < i as i64 && w != t && w != tp && !reg_q[w] && vn.is_zero(w)
                                    && free(w, i, j, &reserved_end) {
                                    u = Some(w);
                                    break;
                                }
                            }
                            match u {
                                None => st.rejected_no_idle_wire += 1,
                                Some(u) => {
                                    let mut at_j = vec![op_swap(u, tp)];
                                    if flip {
                                        at_j.push(op_x(tp));
                                    }
                                    edits.push((i, vec![op_swap(t, u), ops[i], op_bs0(b)]));
                                    edits.push((j, at_j));
                                    edited[i] = true;
                                    edited[j] = true;
                                    reserved_end[u] = reserved_end[u].max(j as i64);
                                    e.borrow_mut().used = true;
                                    st.parked += 1;
                                    if direct { st.match_direct += 1 } else { st.match_asserted += 1 }
                                    leases.push(Lease { in_place: false, direct, erase: i, recompute: j, wire: t,
                                                        park: u, target: tp, bit: b, flip });
                                }
                            }
                        } else {
                            st.rejected_touched += 1;
                        }
                    }
                }
            }
        }
        if o.c_target != NO_BIT && matches!(k, K::Hmr | K::BitStore0 | K::BitStore1 | K::BitInvert) {
            let b = o.c_target.0 as usize;
            let drop = matches!(&pending[b], Some(e) if e.borrow().i != j);
            if drop {
                pending[b] = None;
            }
        }
        for q in [o.q_control2, o.q_control1, o.q_target] {
            if q != NO_QUBIT {
                last_touch[q.0 as usize] = j as i64;
            }
        }
        vn.step(o);
        if (j & 0xFFF) == 0 && order.front().map_or(false, |f| j - f.0 > kn.max_span) {
            while let Some((jj, key)) = order.front() {
                if j - *jj <= kn.max_span {
                    break;
                }
                let gone = matches!(by_form.get(key), Some(e) if e.borrow().i <= *jj);
                if gone {
                    by_form.remove(key);
                }
                order.pop_front();
            }
        }
    }
    st.atoms = vn.n_atoms;
    st.capped_forms = vn.capped;
    st.forgotten = vn.forgotten;
    edits.sort_by_key(|e| e.0);
    (edits, leases, st)
}

/// Apply sorted edits (op index -> replacement ops) in place. The vector grows only by the positive growth of the
/// edits, so the pass never holds a second copy of the stream: the originals move right by that growth, then a
/// forward fill writes the result. The write position never passes the next unread original, because the output
/// position of original op k is k plus the growth of the edits before k, which is at most the positive growth.
pub fn apply_edits(mut ops: Vec<Op>, edits: &[(usize, Vec<Op>)]) -> Vec<Op> {
    if edits.is_empty() {
        return ops;
    }
    let n = ops.len();
    let grow: usize = edits.iter().map(|(_, r)| r.len().saturating_sub(1)).sum();
    let net: i64 = edits.iter().map(|(_, r)| r.len() as i64 - 1).sum();
    ops.resize(n + grow, Op::empty());
    ops.copy_within(0..n, grow);
    let (mut w, mut r, mut at) = (0usize, grow, 0usize);
    for (i, rep) in edits {
        let cnt = i - at;
        ops.copy_within(r..r + cnt, w);
        w += cnt;
        r += cnt;
        assert!(w + rep.len() <= r + 1, "lease pass: in-place apply overran its input");
        ops[w..w + rep.len()].copy_from_slice(rep);
        w += rep.len();
        r += 1;
        at = i + 1;
    }
    let cnt = n - at;
    ops.copy_within(r..r + cnt, w);
    w += cnt;
    assert_eq!(w as i64, n as i64 + net);
    ops.truncate(w);
    ops
}

fn toffolis(ops: &[Op]) -> usize {
    ops.iter().filter(|o| matches!(o.kind, K::CCX | K::CCZ)).count()
}

fn write_record(path: &str, leases: &[Lease]) -> std::io::Result<()> {
    use std::io::Write;
    let mut w = std::io::BufWriter::new(std::fs::File::create(path)?);
    for l in leases {
        // Keys in sorted order, as in the cluster's lease list (lease-839-leases.jsonl.gz); flip is extra.
        if l.in_place {
            writeln!(w, "{{\"bit\": {}, \"erase\": {}, \"flip\": {}, \"kind\": \"in_place\", \"match\": \"{}\", \
                         \"recompute\": {}, \"span\": {}, \"target\": {}, \"wire\": {}}}",
                     l.bit, l.erase, l.flip, if l.direct { "direct" } else { "asserted" }, l.recompute,
                     l.recompute - l.erase, l.target, l.wire)?;
        } else {
            writeln!(w, "{{\"bit\": {}, \"erase\": {}, \"flip\": {}, \"kind\": \"parked\", \"match\": \"{}\", \
                         \"park\": {}, \"recompute\": {}, \"span\": {}, \"target\": {}, \"wire\": {}}}",
                     l.bit, l.erase, l.flip, if l.direct { "direct" } else { "asserted" }, l.park, l.recompute,
                     l.recompute - l.erase, l.target, l.wire)?;
        }
    }
    w.flush()
}

/// Run the pass with explicit knobs.
pub fn run_with(ops: Vec<Op>, kn: &Knobs) -> Vec<Op> {
    if !kn.on {
        eprintln!("LEASE off");
        return ops;
    }
    let t0 = std::time::Instant::now();
    let (edits, leases, st) = plan(&ops, kn);
    let t_plan = t0.elapsed().as_secs_f64();
    if let Some(path) = &kn.record {
        write_record(path, &leases).expect("write the lease record");
    }
    let before = (ops.len(), toffolis(&ops));
    let out = apply_edits(ops, &edits);
    let after = (out.len(), toffolis(&out));
    eprintln!("LEASE knobs cap={} expand={} max_span={} forget_span={} max_direct={} parking={} in_place={}",
              kn.cap, kn.expand, kn.max_span, kn.forget_span, kn.max_direct, kn.parking, kn.in_place);
    eprintln!("LEASE stats {:?}", st);
    eprintln!("LEASE leases={} in_place={} parked={} flips={} ops {} -> {} static Toffoli {} -> {} plan {:.1} s total {:.1} s",
              leases.len(), st.in_place, st.parked, leases.iter().filter(|l| l.flip).count(), before.0, after.0,
              before.1, after.1, t_plan, t0.elapsed().as_secs_f64());
    out
}

/// The emission-time entry point uses source-pinned settings.
pub fn run(ops: Vec<Op>) -> Vec<Op> {
    run_with(ops, &Knobs::official())
}
