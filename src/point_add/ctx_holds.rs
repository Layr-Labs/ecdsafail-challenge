//! O7 (R24): CTX value-numbered AND holds, applied as a stream postpass after R2.
//!
//! Value numbering (VN): every qubit holds a GF(2)-affine form over atoms. Register (input) qubits and
//! every unknown result start as fresh atoms; a CCX XORs an interned product atom of its two control
//! forms into the target. Writes inside a PushCondition scope are muxed at the Pop (a wire whose form
//! changed inside the scope gets a fresh atom); writes under a c_condition get fresh atoms.
//!
//! A chain is a run of CCX ops in one scope instance, under the same c_condition bit version, whose
//! canonical control-form pairs are identical (so their products are equal on every input). A hold
//! covers members m_s..m_e of a chain with a donor wire d that is VN-zero at m_s, untouched by the
//! stream over [m_s, m_e], and not used by another hold over that interval:
//!
//!   m_s = CCX(a,b -> t_s)  becomes  CCX(a,b -> d); CX(d -> t_s)
//!   m_j = CCX(a,b -> t_j)  becomes  CX(d -> t_j)                      (s < j <= e)
//!   after m_e:                      HMR(d -> m); CZ(a_e, b_e | m)      (Push/Pop cc around the CZ if cc)
//!
//! The HMR adds phase m*(a*b), the m-conditioned CZ removes it, and d returns to 0. Each hold is
//! re-proved window-locally (fresh entry atoms for every wire, donor zero) and checked by a 64-lane
//! simulation of its window (all wires, classical bits and phase) against the original window; a hold
//! that fails either check is dropped, and a mismatch on a re-proved hold panics (fail closed).
//!
//! Shortcuts: a CCX whose control forms give a zero product, or a product equal to one control's form,
//! is rewritten to nothing or to a CX (no new HMR). These use global VN facts (not window-local).

use crate::circuit::{analyze_ops, BitId, Op, OperationType as K, QubitId, QubitOrBit, NO_BIT, NO_QUBIT};
use std::collections::{BTreeMap, HashMap};

/// Affine-form atom cap (O7: 12). O9: `O9_CTX_CAP` (recipe) may raise it; a form over the cap becomes a fresh atom
/// (sound: it only forgets information).
fn cap() -> usize { 12 }

const LOOKBACK: u32 = 16_384;
const VERIFY_BATCHES: u64 = 16;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Config {
    /// Holds on chains without a c_condition.
    pub holds: bool,
    /// Holds on chains whose members share a c_condition bit version.
    pub cc_holds: bool,
    /// Zero/copy shortcuts from global VN facts.
    pub shortcuts: bool,
    /// Measurement-based uncompute of a CCX whose target holds exactly its own product (or its
    /// complement): the CCX becomes [X] HMR CZ [X]; no donor.
    pub mbu: bool,
    /// Generalized MBU: the target holds its product XOR a form R that another wire holds now;
    /// CX it into the target, [X], HMR, CZ, [X], CX back. No donor.
    pub mbu_ext: bool,
    /// O9: CCX whose product atom another wire holds exactly -> CX from that wire (no HMR, no donor).
    pub holder: bool,
}

pub(crate) const DEFAULT: Config = Config { holds: true, cc_holds: true, shortcuts: true, mbu: true, mbu_ext: true, holder: true };

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Val {
    c: bool,
    a: Vec<u32>,
}

impl Val {
    fn zero() -> Self {
        Val { c: false, a: Vec::new() }
    }
    fn is_zero(&self) -> bool {
        !self.c && self.a.is_empty()
    }
    fn is_one(&self) -> bool {
        self.c && self.a.is_empty()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Prod {
    Zero,
    /// Product equals control1's form.
    Copy1,
    /// Product equals control2's form.
    Copy2,
    Atom(u32),
}

struct Frame {
    id: u32,
    first: HashMap<u32, Val>,
}

struct Vn {
    /// Optional index from a form's atom set to the wires currently holding it (any constant).
    index: Option<HashMap<Vec<u32>, Vec<u32>>>,
    q: Vec<Val>,
    bver: Vec<u32>,
    next: u32,
    intern: HashMap<(Val, Val), u32>,
    stack: Vec<Frame>,
    scope_ctr: u32,
    zero: Vec<u64>,
}

fn sym_diff(x: &[u32], y: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(x.len() + y.len());
    let (mut i, mut j) = (0, 0);
    while i < x.len() && j < y.len() {
        if x[i] < y[j] {
            out.push(x[i]);
            i += 1;
        } else if y[j] < x[i] {
            out.push(y[j]);
            j += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    out.extend_from_slice(&x[i..]);
    out.extend_from_slice(&y[j..]);
    out
}

impl Vn {
    fn new(nq: usize, nb: usize, fresh_q: &[bool]) -> Self {
        let mut vn = Vn {
            index: None,
            q: vec![Val::zero(); nq],
            bver: vec![0; nb],
            next: 0,
            intern: HashMap::new(),
            stack: Vec::new(),
            scope_ctr: 0,
            zero: vec![u64::MAX; (nq + 63) / 64],
        };
        for q in nq..vn.zero.len() * 64 {
            vn.zero[q / 64] &= !(1u64 << (q % 64));
        }
        for (q, &f) in fresh_q.iter().enumerate() {
            if f {
                let v = vn.fresh();
                vn.q[q] = v;
                vn.zero[q / 64] &= !(1u64 << (q % 64));
            }
        }
        vn
    }

    fn fresh(&mut self) -> Val {
        self.next = self.next.checked_add(1).expect("ctx atom overflow");
        Val { c: false, a: vec![self.next] }
    }

    fn xor(&mut self, u: &Val, v: &Val) -> Val {
        if v.a.is_empty() {
            return Val { c: u.c ^ v.c, a: u.a.clone() };
        }
        if u.a.is_empty() {
            return Val { c: u.c ^ v.c, a: v.a.clone() };
        }
        let a = sym_diff(&u.a, &v.a);
        if a.len() > cap() {
            return self.fresh();
        }
        Val { c: u.c ^ v.c, a }
    }

    fn prod(&mut self, u: &Val, v: &Val) -> Prod {
        if u.is_zero() || v.is_zero() {
            return Prod::Zero;
        }
        if u.a == v.a {
            return if u.c == v.c { Prod::Copy1 } else { Prod::Zero };
        }
        if u.is_one() {
            return Prod::Copy2;
        }
        if v.is_one() {
            return Prod::Copy1;
        }
        let key = if u <= v { (u.clone(), v.clone()) } else { (v.clone(), u.clone()) };
        if let Some(&a) = self.intern.get(&key) {
            return Prod::Atom(a);
        }
        self.next = self.next.checked_add(1).expect("ctx atom overflow");
        let a = self.next;
        self.intern.insert(key, a);
        Prod::Atom(a)
    }

    fn scope(&self) -> u32 {
        self.stack.last().map(|f| f.id).unwrap_or(0)
    }

    fn index_move(&mut self, q: usize, old: &Val, new: &Val) {
        if let Some(ix) = self.index.as_mut() {
            if !old.a.is_empty() {
                if let Some(ws) = ix.get_mut(&old.a) {
                    if let Some(p) = ws.iter().position(|&w| w == q as u32) {
                        ws.swap_remove(p);
                    }
                    if ws.is_empty() {
                        ix.remove(&old.a);
                    }
                }
            }
            if !new.a.is_empty() {
                ix.entry(new.a.clone()).or_default().push(q as u32);
            }
        }
    }

    /// A wire other than `not` whose current form has exactly these atoms.
    fn holder(&self, atoms: &[u32], not: &[usize]) -> Option<(u32, bool)> {
        let ix = self.index.as_ref()?;
        for &w in ix.get(atoms)? {
            if !not.contains(&(w as usize)) && self.q[w as usize].a == atoms {
                return Some((w, self.q[w as usize].c));
            }
        }
        None
    }

    fn set(&mut self, q: usize, v: Val) {
        if self.index.is_some() {
            let old = self.q[q].clone();
            self.index_move(q, &old, &v);
        }
        if let Some(top) = self.stack.last_mut() {
            if !top.first.contains_key(&(q as u32)) {
                top.first.insert(q as u32, self.q[q].clone());
            }
        }
        if v.is_zero() {
            self.zero[q / 64] |= 1u64 << (q % 64);
        } else {
            self.zero[q / 64] &= !(1u64 << (q % 64));
        }
        self.q[q] = v;
    }

    fn set_fresh(&mut self, q: usize) {
        let v = self.fresh();
        self.set(q, v);
    }

    fn bump(&mut self, b: BitId) {
        if b != NO_BIT {
            self.bver[b.0 as usize] = self.bver[b.0 as usize].wrapping_add(1);
        }
    }

    /// Advance over one op. For a CCX, returns the product classification of its controls
    /// (computed before the target write).
    fn step(&mut self, op: &Op) -> Option<Prod> {
        let cc = op.c_condition != NO_BIT;
        match op.kind {
            K::PushCondition => {
                self.scope_ctr += 1;
                self.stack.push(Frame { id: self.scope_ctr, first: HashMap::new() });
            }
            K::PopCondition => {
                let frame = self.stack.pop().expect("balanced condition stack");
                let mut changed: Vec<(u32, Val)> =
                    frame.first.into_iter().filter(|(q, old)| self.q[*q as usize] != *old).collect();
                changed.sort_unstable_by_key(|(q, _)| *q);
                for (q, old) in changed {
                    let v = self.fresh();
                    let qu = q as usize;
                    if let Some(top) = self.stack.last_mut() {
                        top.first.entry(q).or_insert(old);
                    }
                    if v.is_zero() {
                        self.zero[qu / 64] |= 1u64 << (qu % 64);
                    } else {
                        self.zero[qu / 64] &= !(1u64 << (qu % 64));
                    }
                    if self.index.is_some() {
                        let oldv = self.q[qu].clone();
                        self.index_move(qu, &oldv, &v);
                    }
                    self.q[qu] = v;
                }
            }
            K::CCX => {
                let (c1, c2, t) = (op.q_control1.0 as usize, op.q_control2.0 as usize, op.q_target.0 as usize);
                let (u, v) = (self.q[c1].clone(), self.q[c2].clone());
                let p = self.prod(&u, &v);
                if cc {
                    self.set_fresh(t);
                } else {
                    let delta = match p {
                        Prod::Zero => Val::zero(),
                        Prod::Copy1 => u,
                        Prod::Copy2 => v,
                        Prod::Atom(a) => Val { c: false, a: vec![a] },
                    };
                    let nv = self.xor(&self.q[t].clone(), &delta);
                    self.set(t, nv);
                }
                return Some(p);
            }
            K::CX => {
                let (c, t) = (op.q_control1.0 as usize, op.q_target.0 as usize);
                if cc {
                    self.set_fresh(t);
                } else {
                    let nv = self.xor(&self.q[t].clone(), &self.q[c].clone());
                    self.set(t, nv);
                }
            }
            K::X => {
                let t = op.q_target.0 as usize;
                if cc {
                    self.set_fresh(t);
                } else {
                    let mut nv = self.q[t].clone();
                    nv.c = !nv.c;
                    self.set(t, nv);
                }
            }
            K::Swap => {
                let (a, b) = (op.q_control1.0 as usize, op.q_target.0 as usize);
                if cc {
                    self.set_fresh(a);
                    self.set_fresh(b);
                } else {
                    let (va, vb) = (self.q[a].clone(), self.q[b].clone());
                    self.set(a, vb);
                    self.set(b, va);
                }
            }
            K::R | K::Hmr => {
                let t = op.q_target.0 as usize;
                if cc {
                    self.set_fresh(t);
                } else {
                    self.set(t, Val::zero());
                }
                if op.kind == K::Hmr {
                    self.bump(op.c_target);
                }
            }
            K::BitInvert | K::BitStore0 | K::BitStore1 => self.bump(op.c_target),
            K::Z | K::CZ | K::CCZ | K::Neg | K::Register | K::AppendToRegister | K::DebugPrint => {}
        }
        None
    }

    fn control_pair(&self, op: &Op) -> (Val, Val) {
        let u = self.q[op.q_control1.0 as usize].clone();
        let v = self.q[op.q_control2.0 as usize].clone();
        if u <= v {
            (u, v)
        } else {
            (v, u)
        }
    }
}

struct Chain {
    cc: BitId,
    depth: u32,
    members: Vec<u32>,
    /// Global-VN zero snapshot taken before each member.
    snaps: Vec<Vec<u64>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Hold {
    pub members: Vec<u32>,
    pub donor: u32,
    pub cc: BitId,
    pub weight: f64,
    /// Global-VN zero set before the first member (window entry facts for the re-proof).
    pub entry_zero: Vec<u64>,
}

#[derive(Default, Debug)]
pub(crate) struct Stats {
    pub ccx: u64,
    pub shortcut_zero: u64,
    pub shortcut_copy: u64,
    pub shortcut_weight: f64,
    pub chains: u64,
    pub cc_chains: u64,
    pub chain_saving: f64,
    pub holds: u64,
    pub hold_saving: f64,
    pub rejected_local: u64,
    pub rejected_local_saving: f64,
    pub unfunded_saving: f64,
    pub donors: u64,
    pub mbu: u64,
    pub mbu_weight: f64,
    /// Census only: CCX whose target form contains its product atom plus other atoms.
    pub mbu_ext: u64,
    pub mbu_ext1: u64,
    pub mbu_ext1_weight: f64,
    pub extended: u64,
    pub extended_saving: f64,
    pub holder: u64,
    pub holder_weight: f64,
}

pub(crate) struct Plan {
    pub holds: Vec<Hold>,
    /// op index -> shortcut rewrite
    pub shortcuts: Vec<(u32, Prod2)>,
    /// op index -> target complemented (t == product ^ 1)
    pub mbus: Vec<(u32, bool)>,
    /// op index -> (source wire holding the target's non-product part, X fix)
    pub mbu_exts: Vec<(u32, Vec<u32>, bool)>,
    /// O9: op index -> (holder wire, X fix)
    pub holders: Vec<(u32, u32, bool)>,
    pub stats: Stats,
    pub mbit: BitId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Prod2 {
    Drop,
    Cx1,
    Cx2,
}

fn depth_weight(depth: u32, cc: bool) -> f64 {
    0.5f64.powi(depth as i32) * if cc { 0.5 } else { 1.0 }
}

fn register_qubits(ops: &[Op], nq: usize) -> Vec<bool> {
    let (_, _, _, regs) = analyze_ops(ops.iter());
    let mut f = vec![false; nq];
    for r in regs {
        for s in r {
            if let QubitOrBit::Qubit(q) = s {
                f[q.0 as usize] = true;
            }
        }
    }
    f
}

/// Pass 1: global VN, chains, shortcuts, MBU candidates.
fn find_chains(
    ops: &[Op],
    nq: usize,
    nb: usize,
    cfg: &Config,
    stats: &mut Stats,
) -> (Vec<Chain>, Vec<(u32, Prod2)>, Vec<(u32, bool)>, Vec<(u32, Vec<u32>, bool)>, Vec<(u32, u32, bool)>) {
    let inputs = register_qubits(ops, nq);
    let mut vn = Vn::new(nq, nb, &inputs);
    let mut ix: HashMap<Vec<u32>, Vec<u32>> = HashMap::new();
    for q in 0..nq {
        if !vn.q[q].a.is_empty() {
            ix.entry(vn.q[q].a.clone()).or_default().push(q as u32);
        }
    }
    vn.index = Some(ix);
    // key (scope, cc bit, cc version, atom) -> (first member or tagged chain index, last member, first snapshot)
    let mut open: HashMap<(u32, u64, u32, u32), (u32, u32, Vec<u64>)> = HashMap::new();
    let mut chains: Vec<Chain> = Vec::new();
    let mut shortcuts = Vec::new();
    let mut mbus = Vec::new();
    let mut mbu_exts = Vec::new();
    let mut holders = Vec::new();
    for (i, op) in ops.iter().enumerate() {
        let i = i as u32;
        if i & 0xf_ffff == 0 && i > 0 {
            open.retain(|_, e| i - e.1 <= LOOKBACK);
        }
        if op.kind != K::CCX {
            vn.step(op);
            continue;
        }
        stats.ccx += 1;
        let cc = op.c_condition != NO_BIT;
        let depth = vn.stack.len() as u32;
        let snap = vn.zero.clone();
        let scope = vn.scope();
        let told = vn.q[op.q_target.0 as usize].clone();
        let p = vn.step(op).unwrap();
        let a = match p {
            Prod::Atom(a) => a,
            _ => {
                if p == Prod::Zero {
                    stats.shortcut_zero += 1;
                } else {
                    stats.shortcut_copy += 1;
                }
                stats.shortcut_weight += depth_weight(depth, cc);
                if cfg.shortcuts {
                    let r = match p {
                        Prod::Zero => Prod2::Drop,
                        Prod::Copy1 => Prod2::Cx1,
                        _ => Prod2::Cx2,
                    };
                    shortcuts.push((i, r));
                }
                continue;
            }
        };
        if cfg.holder {
            if let Some((w, cw)) = vn.holder(&[a], &[op.q_target.0 as usize]) {
                stats.holder += 1;
                stats.holder_weight += depth_weight(depth, cc);
                holders.push((i, w, cw));
                continue;
            }
        }
        if !cc && told.a.len() > 1 && told.a.binary_search(&a).is_ok() {
            stats.mbu_ext += 1;
            // After the step the target holds R = told ^ product; no other wire changed.
            let r = vn.q[op.q_target.0 as usize].clone();
            let not = [op.q_target.0 as usize];
            if r.a.len() + 1 == told.a.len() {
                if let Some((w, cw)) = vn.holder(&r.a, &not) {
                    stats.mbu_ext1 += 1;
                    stats.mbu_ext1_weight += depth_weight(depth, cc);
                    if cfg.mbu_ext {
                        mbu_exts.push((i, vec![w], r.c ^ cw));
                        continue;
                    }
                }
            }
        }
        if !cc && told.a.len() == 1 && told.a[0] == a {
            stats.mbu += 1;
            stats.mbu_weight += depth_weight(depth, cc);
            if cfg.mbu {
                mbus.push((i, told.c));
                continue;
            }
        }
        let cver = if cc { vn.bver[op.c_condition.0 as usize] } else { 0 };
        let key = (scope, op.c_condition.0, cver, a);
        match open.get_mut(&key) {
            Some(e) if i - e.1 <= LOOKBACK => {
                if e.0 & 0x8000_0000 == 0 {
                    let first = e.0;
                    let first_snap = std::mem::take(&mut e.2);
                    chains.push(Chain { cc: op.c_condition, depth, members: vec![first, i], snaps: vec![first_snap, snap] });
                    e.0 = 0x8000_0000 | (chains.len() as u32 - 1);
                } else {
                    let c = &mut chains[(e.0 & 0x7fff_ffff) as usize];
                    c.members.push(i);
                    c.snaps.push(snap);
                }
                e.1 = i;
            }
            _ => {
                open.insert(key, (i, i, snap));
            }
        }
    }
    assert!(chains.len() < 0x8000_0000);
    for c in &chains {
        let cc = c.cc != NO_BIT;
        stats.chains += 1;
        if cc {
            stats.cc_chains += 1;
        }
        stats.chain_saving += (c.members.len() - 1) as f64 * depth_weight(c.depth, cc);
    }
    let chains = chains
        .into_iter()
        .filter(|c| if c.cc == NO_BIT { cfg.holds } else { cfg.cc_holds })
        .collect();
    (chains, shortcuts, mbus, mbu_exts, holders)
}

fn operands(op: &Op) -> [QubitId; 3] {
    [op.q_control1, op.q_control2, op.q_target]
}

/// Pass 2: touch lists and greedy donor assignment (longest reachable segment first).
fn assign(ops: &[Op], nq: usize, mut chains: Vec<Chain>, stats: &mut Stats) -> Vec<Hold> {
    let mut touches: Vec<Vec<u32>> = vec![Vec::new(); nq];
    for (i, op) in ops.iter().enumerate() {
        for q in operands(op) {
            if q != NO_QUBIT {
                touches[q.0 as usize].push(i as u32);
            }
        }
    }
    chains.sort_by_key(|c| c.members[0]);
    let mut busy: Vec<BTreeMap<u32, u32>> = vec![BTreeMap::new(); nq];
    let mut holds = Vec::new();
    let diag = false;
    for c in &chains {
        let w = depth_weight(c.depth, c.cc != NO_BIT);
        let k = c.members.len();
        let mut s = 0;
        while s + 1 < k {
            let ms = c.members[s];
            let mut best: Option<(usize, u32, u32)> = None; // (e, next_touch, q)
            for (wi, &word) in c.snaps[s].iter().enumerate() {
                let mut bits = word;
                while bits != 0 {
                    let q = wi * 64 + bits.trailing_zeros() as usize;
                    bits &= bits - 1;
                    if q >= nq {
                        continue;
                    }
                    let tl = &touches[q];
                    // A donor must be untouched over [m_s, m_e].
                    let pos = tl.partition_point(|&x| x < ms);
                    let next_touch = if pos < tl.len() { tl[pos] } else { u32::MAX };
                    if next_touch == ms {
                        continue;
                    }
                    // Busy intervals of other holds.
                    if let Some((_, &end)) = busy[q].range(..=ms).next_back() {
                        if end >= ms {
                            continue;
                        }
                    }
                    let next_busy = busy[q].range(ms..).next().map(|(&s0, _)| s0).unwrap_or(u32::MAX);
                    let limit = next_touch.min(next_busy);
                    let mut e = s;
                    while e + 1 < k && c.members[e + 1] < limit {
                        e += 1;
                    }
                    if e > s {
                        let better = match best {
                            None => true,
                            Some((be, bt, bq)) => e > be || (e == be && (limit, q as u32) < (bt, bq)),
                        };
                        if better {
                            best = Some((e, limit, q as u32));
                        }
                    }
                }
            }
            match best {
                Some((e, _, q)) => {
                    busy[q as usize].insert(ms, c.members[e]);
                    holds.push(Hold {
                        members: c.members[s..=e].to_vec(),
                        donor: q,
                        cc: c.cc,
                        weight: w,
                        entry_zero: c.snaps[s].clone(),
                    });
                    s = e + 1;
                }
                None => {
                    stats.unfunded_saving += w;
                    if diag {
                        // O9 diagnostic only: gap to the next member and zero wires available at m_s.
                        let gap = c.members[s + 1] - ms;
                        let nz: u32 = c.snaps[s].iter().map(|x| x.count_ones()).sum();
                        let mut best_free = 0u32;
                        for (wi, &word) in c.snaps[s].iter().enumerate() {
                            let mut bits = word;
                            while bits != 0 {
                                let q = wi * 64 + bits.trailing_zeros() as usize;
                                bits &= bits - 1;
                                if q >= nq { continue; }
                                let tl = &touches[q];
                                let pos = tl.partition_point(|&x| x < ms);
                                let nt = if pos < tl.len() { tl[pos] } else { u32::MAX };
                                best_free = best_free.max(nt.saturating_sub(ms));
                            }
                        }
                        eprintln!("O9_UNFUNDED ms={ms} gap={gap} zero_wires={nz} best_free={best_free} depth={} cc={}", c.depth, c.cc != NO_BIT);
                    }
                    s += 1;
                }
            }
        }
    }
    holds.sort_by_key(|h| h.members[0]);
    holds
}

/// Emit the replacement of original op `i` (op `op`) for one hold, if it is a member.
fn emit_member(h: &Hold, idx: usize, op: &Op, out: &mut Vec<Op>) {
    let d = QubitId(h.donor as u64);
    if idx == 0 {
        let mut first = *op;
        first.q_target = d;
        out.push(first);
        out.push(Op { kind: K::CX, q_control1: d, q_target: op.q_target, ..Op::empty() });
    } else {
        out.push(Op { kind: K::CX, q_control1: d, q_target: op.q_target, ..Op::empty() });
    }
}

fn emit_discharge(h: &Hold, last: &Op, mbit: BitId, out: &mut Vec<Op>) {
    let d = QubitId(h.donor as u64);
    out.push(Op { kind: K::Hmr, q_target: d, c_target: mbit, ..Op::empty() });
    let cz = Op {
        kind: K::CZ,
        q_control1: last.q_control1,
        q_target: last.q_control2,
        c_condition: mbit,
        ..Op::empty()
    };
    if h.cc != NO_BIT {
        out.push(Op { kind: K::PushCondition, c_condition: h.cc, ..Op::empty() });
        out.push(cz);
        out.push(Op { kind: K::PopCondition, ..Op::empty() });
    } else {
        out.push(cz);
    }
}

// ---------------------------------------------------------------------------------------------
// Per-hold verification: window-local re-proof and 64-lane window simulation.

/// Window-local re-proof of one hold over ops[start..=l0] (start <= first member): every wire is a fresh
/// atom at `start` except the wires in `entry_zero` (global-VN zero facts at `start`). Members must share
/// one local scope instance and c_condition version, the donor must be zero at every member and untouched
/// from the first member on, and all members' canonical control pairs must be identical.
fn local_reproof(ops: &[Op], h: &Hold, start: usize, entry_zero: &[u64], nq: usize, nb: usize) -> bool {
    let (f0, l0) = (h.members[0] as usize, *h.members.last().unwrap() as usize);
    assert!(start <= f0);
    let fresh: Vec<bool> = (0..nq).map(|q| (entry_zero[q / 64] >> (q % 64)) & 1 == 0).collect();
    let mut vn = Vn::new(nq, nb, &fresh);
    let mut scope0: Option<u32> = None;
    let mut want: Option<(Val, Val)> = None;
    let cc = h.cc;
    let cver0 = if cc != NO_BIT { Some(0u32) } else { None };
    let mut mi = 0;
    for i in start..=l0 {
        let op = &ops[i];
        if mi < h.members.len() && h.members[mi] as usize == i {
            if op.kind != K::CCX || op.c_condition != cc {
                return false;
            }
            match scope0 {
                None => scope0 = Some(vn.scope()),
                Some(s0) => {
                    if s0 != vn.scope() {
                        return false;
                    }
                }
            }
            if let Some(v0) = cver0 {
                if vn.bver[cc.0 as usize] != v0 {
                    return false;
                }
            }
            if op.q_target.0 as u32 == h.donor || op.q_control1.0 as u32 == h.donor || op.q_control2.0 as u32 == h.donor {
                return false;
            }
            if !vn.q[h.donor as usize].is_zero() {
                return false;
            }
            let pair = vn.control_pair(op);
            if pair.0.is_zero() || pair.1.is_zero() || pair.0.a == pair.1.a || pair.0.is_one() || pair.1.is_one() {
                return false;
            }
            match &want {
                None => want = Some(pair),
                Some(w) => {
                    if *w != pair {
                        return false;
                    }
                }
            }
            mi += 1;
        } else if i > f0 {
            for q in operands(op) {
                if q != NO_QUBIT && q.0 as u32 == h.donor {
                    return false;
                }
            }
        }
        if op.kind == K::PopCondition && vn.stack.is_empty() {
            return false;
        }
        if i >= f0 && op.kind == K::PopCondition && vn.stack.last().map(|f| f.id) == scope0 {
            return false;
        }
        vn.step(op);
    }
    mi == h.members.len()
}

/// Global-VN zero sets before each requested op index (sorted, deduplicated output keyed by index).
fn zero_snapshots(ops: &[Op], nq: usize, nb: usize, want: &[usize]) -> HashMap<usize, Vec<u64>> {
    let mut idx: Vec<usize> = want.to_vec();
    idx.sort_unstable();
    idx.dedup();
    let inputs = register_qubits(ops, nq);
    let mut vn = Vn::new(nq, nb, &inputs);
    let mut out = HashMap::new();
    let mut k = 0;
    for (i, op) in ops.iter().enumerate() {
        while k < idx.len() && idx[k] == i {
            out.insert(i, vn.zero.clone());
            k += 1;
        }
        if k == idx.len() {
            break;
        }
        vn.step(op);
    }
    out
}

fn splitmix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

struct Lanes {
    q: Vec<u64>,
    b: Vec<u64>,
    phase: u64,
}

/// Simulate ops (sim.rs semantics) on 64 lanes, base condition all ones. `tag[i]` keys the random
/// word for an R/HMR so that original ops draw identical words in both versions.
fn sim_lanes(st: &mut Lanes, ops: &[Op], tags: &[u64], seed: u64) {
    let mut stack: Vec<u64> = Vec::new();
    let mut base = u64::MAX;
    for (op, &tag) in ops.iter().zip(tags) {
        let mut cond = base;
        if op.c_condition != NO_BIT && op.kind != K::PushCondition {
            cond &= st.b[op.c_condition.0 as usize];
        }
        let q = |x: QubitId| x.0 as usize;
        match op.kind {
            K::CCX => {
                let v = cond & st.q[q(op.q_control1)] & st.q[q(op.q_control2)];
                st.q[q(op.q_target)] ^= v;
            }
            K::CX => {
                let v = cond & st.q[q(op.q_control1)];
                st.q[q(op.q_target)] ^= v;
            }
            K::Swap => {
                let (a, t) = (q(op.q_control1), q(op.q_target));
                let diff = (st.q[a] ^ st.q[t]) & cond;
                st.q[a] ^= diff;
                st.q[t] ^= diff;
            }
            K::X => st.q[q(op.q_target)] ^= cond,
            K::CCZ => st.phase ^= cond & st.q[q(op.q_target)] & st.q[q(op.q_control1)] & st.q[q(op.q_control2)],
            K::CZ => st.phase ^= cond & st.q[q(op.q_target)] & st.q[q(op.q_control1)],
            K::Z => st.phase ^= cond & st.q[q(op.q_target)],
            K::Neg => st.phase ^= cond,
            K::Hmr => {
                let r = splitmix(seed ^ tag);
                let bt = op.c_target.0 as usize;
                st.b[bt] &= !cond;
                st.b[bt] ^= r & cond;
                st.phase ^= st.q[q(op.q_target)] & r & cond;
                st.q[q(op.q_target)] &= !cond;
            }
            K::R => {
                let r = splitmix(seed ^ tag);
                st.phase ^= st.q[q(op.q_target)] & r & cond;
                st.q[q(op.q_target)] &= !cond;
            }
            K::BitInvert => st.b[op.c_target.0 as usize] ^= cond,
            K::BitStore0 => st.b[op.c_target.0 as usize] &= !cond,
            K::BitStore1 => st.b[op.c_target.0 as usize] |= cond,
            K::PushCondition => {
                stack.push(base);
                base &= st.b[op.c_condition.0 as usize];
            }
            K::PopCondition => {
                base = stack.pop().expect("window scope balance");
            }
            K::Register | K::AppendToRegister | K::DebugPrint => {}
        }
    }
}

/// Window check for one hold: original vs rewritten, identical entry states (donor zero),
/// identical random words for original R/HMR ops. Returns false on any difference.
fn window_check(
    ops: &[Op],
    h: &Hold,
    hid: usize,
    start: usize,
    entry_zero: &[u64],
    nq: usize,
    nb_with_m: usize,
    mbit: BitId,
) -> bool {
    let (f0, l0) = (start, *h.members.last().unwrap() as usize);
    let win = &ops[f0..=l0];
    let orig_tags: Vec<u64> = (f0..=l0).map(|i| (i as u64) << 2).collect();
    let mut rew = Vec::with_capacity(win.len() + 8);
    let mut rew_tags = Vec::with_capacity(win.len() + 8);
    let mut mi = 0;
    for (k, op) in win.iter().enumerate() {
        let i = f0 + k;
        if mi < h.members.len() && h.members[mi] as usize == i {
            let before = rew.len();
            emit_member(h, mi, op, &mut rew);
            for j in before..rew.len() {
                rew_tags.push(((i as u64) << 2) | 1 | ((j - before) as u64) << 40);
            }
            mi += 1;
        } else {
            rew.push(*op);
            rew_tags.push((i as u64) << 2);
        }
    }
    let before = rew.len();
    emit_discharge(h, &win[win.len() - 1], mbit, &mut rew);
    for j in before..rew.len() {
        rew_tags.push(((l0 as u64) << 2) | 2 | ((j - before) as u64) << 40);
    }
    for batch in 0..VERIFY_BATCHES + 2 {
        let seed = splitmix(((hid as u64) << 20) ^ batch ^ 0x0715_c7c7);
        let entry = |x: u64| -> u64 {
            match batch {
                0 => 0,
                1 => u64::MAX,
                _ => splitmix(seed ^ x.wrapping_mul(0x2545_f491_4f6c_dd1d)),
            }
        };
        let mut a = Lanes {
            q: (0..nq as u64).map(|x| entry(x)).collect(),
            b: (0..nb_with_m as u64).map(|x| entry(x | (1 << 50))).collect(),
            phase: 0,
        };
        for q in 0..nq {
            if (entry_zero[q / 64] >> (q % 64)) & 1 == 1 {
                a.q[q] = 0;
            }
        }
        let mut b = Lanes { q: a.q.clone(), b: a.b.clone(), phase: 0 };
        sim_lanes(&mut a, win, &orig_tags, seed);
        sim_lanes(&mut b, &rew, &rew_tags, seed);
        b.b[mbit.0 as usize] = a.b[mbit.0 as usize];
        if a.q != b.q || a.b != b.b || a.phase != b.phase {
            return false;
        }
    }
    true
}

/// Full analysis: chains, donors, per-hold re-proof and window check.
pub(crate) fn plan(ops: &[Op], cfg: &Config) -> Plan {
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    let (nq, nb) = (nq as usize, nb as usize);
    let mbit = BitId(nb as u64);
    let mut stats = Stats::default();
    let (chains, shortcuts, mbus, mbu_exts, holders) = find_chains(ops, nq, nb, cfg, &mut stats);
    let holds = assign(ops, nq, chains, &mut stats);
    let mut admitted = Vec::with_capacity(holds.len());
    let mut pending: Vec<(usize, Hold)> = Vec::new();
    for (hid, h) in holds.into_iter().enumerate() {
        let f0 = h.members[0] as usize;
        if !local_reproof(ops, &h, f0, &h.entry_zero, nq, nb) {
            pending.push((hid, h));
            continue;
        }
        assert!(
            window_check(ops, &h, hid, f0, &h.entry_zero, nq, nb + 1, mbit),
            "CTX window check failed for hold {hid}: {h:?}"
        );
        admitted.push(h);
    }
    // Holds whose member equality rests on facts established shortly before the first member: retry with
    // the proof window started W ops earlier (entry zero facts from a second global VN pass).
    for w in [16usize, 256, 4096] {
        if pending.is_empty() {
            break;
        }
        let starts: Vec<usize> = pending.iter().map(|(_, h)| (h.members[0] as usize).saturating_sub(w)).collect();
        let snaps = zero_snapshots(ops, nq, nb, &starts);
        let mut still = Vec::new();
        for ((hid, h), st) in pending.into_iter().zip(starts) {
            let z = &snaps[&st];
            if local_reproof(ops, &h, st, z, nq, nb) {
                assert!(
                    window_check(ops, &h, hid, st, z, nq, nb + 1, mbit),
                    "CTX extended window check failed for hold {hid} start {st}: {h:?}"
                );
                stats.extended += 1;
                stats.extended_saving += (h.members.len() - 1) as f64 * h.weight;
                admitted.push(h);
            } else {
                still.push((hid, h));
            }
        }
        pending = still;
    }
    for (_, h) in &pending {
        stats.rejected_local += 1;
        stats.rejected_local_saving += (h.members.len() - 1) as f64 * h.weight;
    }
    let mut donors: Vec<u32> = admitted.iter().map(|h| h.donor).collect();
    donors.sort_unstable();
    donors.dedup();
    stats.donors = donors.len() as u64;
    stats.holds = admitted.len() as u64;
    stats.hold_saving = admitted.iter().map(|h| (h.members.len() - 1) as f64 * h.weight).sum();
    Plan { holds: admitted, shortcuts, mbus, mbu_exts, holders, stats, mbit }
}

/// Rewrite the stream with the planned holds and shortcuts.
pub(crate) fn rewrite(ops: Vec<Op>, plan: &Plan) -> Vec<Op> {
    // op index -> (hold id, member index)
    let mut member: HashMap<u32, (u32, u32)> = HashMap::new();
    for (hid, h) in plan.holds.iter().enumerate() {
        for (mi, &m) in h.members.iter().enumerate() {
            assert!(member.insert(m, (hid as u32, mi as u32)).is_none(), "op in two holds");
        }
    }
    let short: HashMap<u32, Prod2> = plan.shortcuts.iter().copied().collect();
    let held: HashMap<u32, (u32, bool)> = plan.holders.iter().map(|&(i, w, c)| (i, (w, c))).collect();
    let mbu: HashMap<u32, bool> = plan.mbus.iter().copied().collect();
    let mbx: HashMap<u32, (&Vec<u32>, bool)> = plan.mbu_exts.iter().map(|(i, s, x)| (*i, (s, *x))).collect();
    let mut out = Vec::with_capacity(ops.len() + 4 * plan.holds.len());
    for (i, op) in ops.into_iter().enumerate() {
        let i32 = i as u32;
        if let Some(&(hid, mi)) = member.get(&i32) {
            let h = &plan.holds[hid as usize];
            emit_member(h, mi as usize, &op, &mut out);
            if mi as usize + 1 == h.members.len() {
                emit_discharge(h, &op, plan.mbit, &mut out);
            }
        } else if let Some(&comp) = mbu.get(&i32) {
            // t holds exactly a*b (or its complement): the CCX clears it. Measure it out instead.
            if comp {
                out.push(Op { kind: K::X, q_target: op.q_target, ..Op::empty() });
            }
            out.push(Op { kind: K::Hmr, q_target: op.q_target, c_target: plan.mbit, ..Op::empty() });
            out.push(Op { kind: K::CZ, q_control1: op.q_control1, q_target: op.q_control2, c_condition: plan.mbit, ..Op::empty() });
            if comp {
                out.push(Op { kind: K::X, q_target: op.q_target, ..Op::empty() });
            }
        } else if let Some(&(src, xfix)) = mbx.get(&i32) {
            // t = a*b ^ R with R held by `src` (constant fixed by xfix).
            let t = op.q_target;
            for &w in src.iter() {
                out.push(Op { kind: K::CX, q_control1: QubitId(w as u64), q_target: t, ..Op::empty() });
            }
            if xfix {
                out.push(Op { kind: K::X, q_target: t, ..Op::empty() });
            }
            out.push(Op { kind: K::Hmr, q_target: t, c_target: plan.mbit, ..Op::empty() });
            out.push(Op { kind: K::CZ, q_control1: op.q_control1, q_target: op.q_control2, c_condition: plan.mbit, ..Op::empty() });
            if xfix {
                out.push(Op { kind: K::X, q_target: t, ..Op::empty() });
            }
            for &w in src.iter() {
                out.push(Op { kind: K::CX, q_control1: QubitId(w as u64), q_target: t, ..Op::empty() });
            }
        } else if let Some(&(w, c)) = held.get(&i32) {
            // O9 holder: wire w holds exactly the product (constant c).
            out.push(Op { kind: K::CX, q_control1: QubitId(w as u64), q_target: op.q_target, c_condition: op.c_condition, ..Op::empty() });
            if c {
                out.push(Op { kind: K::X, q_target: op.q_target, c_condition: op.c_condition, ..Op::empty() });
            }
        } else if let Some(&r) = short.get(&i32) {
            match r {
                Prod2::Drop => {}
                Prod2::Cx1 => out.push(Op { kind: K::CX, q_control1: op.q_control1, q_target: op.q_target, c_condition: op.c_condition, ..Op::empty() }),
                Prod2::Cx2 => out.push(Op { kind: K::CX, q_control1: op.q_control2, q_target: op.q_target, c_condition: op.c_condition, ..Op::empty() }),
            }
        } else {
            out.push(op);
        }
    }
    out
}

pub(crate) fn report(plan: &Plan) {
    let s = &plan.stats;
    eprintln!(
        "CTX_HOLDS ccx={} shortcut_zero={} shortcut_copy={} shortcut_w={:.1} chains={} cc_chains={} chain_saving={:.1} \
         holds={} hold_saving={:.1} rejected_local={} rejected_local_saving={:.1} unfunded={:.1} donors={} shortcuts_applied={} mbu={} mbu_w={:.1} mbu_applied={} mbit={}",
        s.ccx, s.shortcut_zero, s.shortcut_copy, s.shortcut_weight, s.chains, s.cc_chains, s.chain_saving, s.holds,
        s.hold_saving, s.rejected_local, s.rejected_local_saving, s.unfunded_saving, s.donors, plan.shortcuts.len(),
        s.mbu, s.mbu_weight, plan.mbus.len(), plan.mbit.0
    );
    eprintln!(
        "CTX_MBUX candidates={} one_source={} one_source_w={:.1} applied={} extended_holds={} extended_saving={:.1} holder={} holder_w={:.1}",
        s.mbu_ext, s.mbu_ext1, s.mbu_ext1_weight, plan.mbu_exts.len(), s.extended, s.extended_saving, s.holder, s.holder_weight
    );
    let mut spans: Vec<u32> = plan.holds.iter().map(|h| h.members.last().unwrap() - h.members[0]).collect();
    spans.sort_unstable();
    if !spans.is_empty() {
        let qn = |f: f64| spans[((spans.len() - 1) as f64 * f) as usize];
        eprintln!(
            "CTX_HOLDS spans q0={} q25={} q50={} q75={} q90={} q100={}",
            qn(0.0), qn(0.25), qn(0.5), qn(0.75), qn(0.9), qn(1.0)
        );
    }
}

/// Postpass entry point used by `point_add::build()`.
pub(crate) fn apply(ops: Vec<Op>, cfg: &Config) -> Vec<Op> {
    let plan = plan(&ops, cfg);
    report(&plan);
    rewrite(ops, &plan)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ccx(a: u64, b: u64, t: u64) -> Op {
        Op { kind: K::CCX, q_control1: QubitId(a), q_control2: QubitId(b), q_target: QubitId(t), ..Op::empty() }
    }
    fn cx(c: u64, t: u64) -> Op {
        Op { kind: K::CX, q_control1: QubitId(c), q_target: QubitId(t), ..Op::empty() }
    }
    fn reg(r: u64, q: u64) -> Op {
        Op { kind: K::AppendToRegister, q_target: QubitId(q), r_target: crate::circuit::RegisterId(r), ..Op::empty() }
    }
    fn hmr(q: u64, b: u64) -> Op {
        Op { kind: K::Hmr, q_target: QubitId(q), c_target: BitId(b), ..Op::empty() }
    }

    /// Original R/HMR ops draw the same random word in both streams (by ordinal); the hold's new
    /// HMRs (c_target == mbit) draw their own.
    fn tags(ops: &[Op], mbit: BitId) -> Vec<u64> {
        let (mut k, mut j) = (0u64, 0u64);
        ops.iter()
            .map(|o| match o.kind {
                K::Hmr if o.c_target == mbit => {
                    j += 1;
                    (1 << 40) + j
                }
                K::Hmr | K::R => {
                    k += 1;
                    k
                }
                _ => 0,
            })
            .collect()
    }

    /// Exhaustive check of a synthetic stream: original vs rewritten, all register inputs, both
    /// random-word values for every HMR (64 lanes cover each pattern), state, bits and phase.
    fn exhaustive_equal(orig: &[Op], new: &[Op], inputs: &[u64], nq: usize, nb: usize, mbit: BitId) {
        let n = inputs.len();
        assert!(n <= 6);
        for seed in 0..64u64 {
            let mut a = Lanes { q: vec![0; nq], b: vec![0; nb], phase: 0 };
            for (k, &q) in inputs.iter().enumerate() {
                // lane l encodes input pattern l mod 2^n
                let mut w = 0u64;
                for l in 0..64u64 {
                    if (l >> k) & 1 == 1 {
                        w |= 1 << l;
                    }
                }
                a.q[q as usize] = w;
            }
            let mut b = Lanes { q: a.q.clone(), b: a.b.clone(), phase: 0 };
            sim_lanes(&mut a, orig, &tags(orig, mbit), seed);
            sim_lanes(&mut b, new, &tags(new, mbit), seed);
            b.b[mbit.0 as usize] = a.b[mbit.0 as usize];
            assert_eq!(a.q, b.q, "state mismatch");
            assert_eq!(a.b, b.b, "bit mismatch");
            assert_eq!(a.phase, b.phase, "phase mismatch");
        }
    }

    fn toffolis(ops: &[Op]) -> usize {
        ops.iter().filter(|o| o.kind == K::CCX).count()
    }

    #[test]
    fn o7_ctx_basic_hold() {
        // inputs q0,q1 (register), targets q2,q3, idle zero q4; t2 ^= ab twice on different targets.
        let mut ops = vec![reg(0, 0), reg(0, 1)];
        ops.push(ccx(0, 1, 2));
        ops.push(cx(2, 3));
        ops.push(ccx(0, 1, 3));
        ops.push(ccx(0, 1, 2));
        ops.push(hmr(4, 0));
        let holds_only = Config { holds: true, cc_holds: true, shortcuts: false, mbu: false, mbu_ext: false, holder: false };
        let p = plan(&ops, &holds_only);
        assert_eq!(p.holds.len(), 1, "{:?}", p.stats);
        assert_eq!(p.holds[0].members.len(), 3);
        // Under DEFAULT the two later CCXs are exact uncomputes (MBU): same Toffoli count, no donor.
        let pd = plan(&ops, &DEFAULT);
        assert_eq!(toffolis(&rewrite(ops.clone(), &pd)), 1);
        let new = rewrite(ops.clone(), &p);
        assert_eq!(toffolis(&new), 1);
        exhaustive_equal(&ops, &new, &[0, 1], 5, 2, p.mbit);
    }

    #[test]
    fn o7_ctx_copied_controls_and_scope() {
        // controls copied to other wires; chain inside a PushCondition scope; cc chain.
        let mut ops = vec![reg(0, 0), reg(0, 1), reg(0, 2)];
        ops.push(hmr(2, 0)); // bit0 random, q2 -> 0
        ops.push(Op { kind: K::PushCondition, c_condition: BitId(0), ..Op::empty() });
        ops.push(ccx(0, 1, 3));
        ops.push(cx(0, 5));
        ops.push(cx(1, 6));
        ops.push(ccx(5, 6, 4));
        ops.push(cx(0, 5));
        ops.push(cx(1, 6));
        ops.push(Op { kind: K::PopCondition, ..Op::empty() });
        let mut cc1 = ccx(0, 1, 3);
        cc1.c_condition = BitId(0);
        ops.push(cc1);
        ops.push(cc1);
        // O7's DEFAULT (no holder class): two donor holds.
        let o7 = Config { holder: false, ..DEFAULT };
        let p = plan(&ops, &o7);
        assert_eq!(p.holds.len(), 2, "{:?}", p.stats);
        let new = rewrite(ops.clone(), &p);
        assert_eq!(toffolis(&new), toffolis(&ops) - 2);
        exhaustive_equal(&ops, &new, &[0, 1, 2], 9, 2, p.mbit);
        // O9 DEFAULT: q3 holds the product after the first CCX, so the in-scope twin becomes a holder CX.
        let p = plan(&ops, &DEFAULT);
        assert_eq!((p.holds.len(), p.holders.len()), (1, 1), "{:?}", p.stats);
        let new = rewrite(ops.clone(), &p);
        assert_eq!(toffolis(&new), toffolis(&ops) - 2);
        exhaustive_equal(&ops, &new, &[0, 1, 2], 9, 2, p.mbit);
    }

    #[test]
    fn o7_ctx_rejects_modified_control_and_busy_donor() {
        let mut ops = vec![reg(0, 0), reg(0, 1), reg(0, 3)];
        ops.push(ccx(0, 1, 2));
        ops.push(cx(3, 0)); // control changed
        ops.push(ccx(0, 1, 2));
        let p = plan(&ops, &DEFAULT);
        assert_eq!(p.holds.len(), 0);
        // equal products but every other wire is touched: no donor.
        let mut ops = vec![reg(0, 0), reg(0, 1)];
        ops.push(ccx(0, 1, 2));
        ops.push(ccx(0, 1, 2));
        let p = plan(&ops, &DEFAULT);
        assert_eq!(p.holds.len(), 0, "{:?}", p.stats);
    }

    #[test]
    fn o7_ctx_discharge_gadget_exhaustive() {
        // HMR + m-conditioned CZ undoes d = a*b exactly, with and without an enclosing condition,
        // over all (a, b, t, cond) and both measurement outcomes.
        for cc in [false, true] {
            let mut ops = vec![reg(0, 0), reg(0, 1), reg(0, 2), reg(0, 3)];
            ops.push(hmr(4, 1)); // random condition bit; q4 becomes an idle zero wire
            let mut m1 = ccx(0, 1, 2);
            let mut m2 = ccx(0, 1, 3);
            if cc {
                m1.c_condition = BitId(1);
                m2.c_condition = BitId(1);
            }
            ops.push(m1);
            ops.push(m2);
            let p = plan(&ops, &DEFAULT);
            assert_eq!(p.holds.len(), 1, "cc={cc} {:?}", p.stats);
            let new = rewrite(ops.clone(), &p);
            assert_eq!(toffolis(&new), 1);
            exhaustive_equal(&ops, &new, &[0, 1, 2, 3], 5, 3, p.mbit);
        }
    }

    #[test]
    fn o7_ctx_mbu_and_shortcuts_exhaustive() {
        let all = Config { holds: true, cc_holds: true, shortcuts: true, mbu: true, mbu_ext: true, holder: false };
        let x = |q: u64| Op { kind: K::X, q_target: QubitId(q), ..Op::empty() };
        // MBU: compute then uncompute a*b on q2; complemented variant on q3.
        let mut ops = vec![reg(0, 0), reg(0, 1)];
        ops.push(ccx(0, 1, 2));
        ops.push(x(3));
        ops.push(ccx(0, 1, 3));
        ops.push(cx(2, 4));
        ops.push(ccx(0, 1, 2));
        ops.push(ccx(0, 1, 3));
        ops.push(ccx(0, 1, 4)); // q4 == a*b too
        // shortcuts: equal controls (copy) and a zero control (drop)
        ops.push(cx(0, 5));
        ops.push(ccx(0, 5, 6));
        ops.push(ccx(0, 7, 6));
        let p = plan(&ops, &all);
        assert_eq!(p.mbus.len(), 3, "{:?}", p.stats);
        assert_eq!(p.shortcuts.len(), 2, "{:?}", p.stats);
        assert_eq!(p.holds.len(), 1, "{:?}", p.stats); // the two computes share a donor hold
        let new = rewrite(ops.clone(), &p);
        assert_eq!(toffolis(&new), 1);
        exhaustive_equal(&ops, &new, &[0, 1], 8, 1, p.mbit);
    }

    #[test]
    fn o7_ctx_mbu_ext_exhaustive() {
        let all = Config { holds: false, cc_holds: false, shortcuts: false, mbu: false, mbu_ext: true, holder: false };
        let x = |q: u64| Op { kind: K::X, q_target: QubitId(q), ..Op::empty() };
        // q3 = q2 (copy); t=q3 toggled by a*b twice: the second toggle has t = ab ^ F(q2) -> source q2.
        let mut ops = vec![reg(0, 0), reg(0, 1), reg(0, 2), reg(0, 4)];
        ops.push(cx(2, 3));
        ops.push(ccx(0, 1, 3));
        ops.push(ccx(0, 1, 3));
        // complemented copy: q5 = q4 ^ 1 -> source q4 with an X fix.
        ops.push(cx(4, 5));
        ops.push(x(5));
        ops.push(ccx(0, 1, 5));
        ops.push(ccx(0, 1, 5));
        let p = plan(&ops, &all);
        assert_eq!(p.mbu_exts.len(), 2, "{:?} {:?}", p.stats, p.mbu_exts);
        assert!(p.mbu_exts.iter().any(|(_, _, xf)| *xf));
        let new = rewrite(ops.clone(), &p);
        assert_eq!(toffolis(&new), 2);
        exhaustive_equal(&ops, &new, &[0, 1, 2, 4], 6, 1, p.mbit);
    }

    #[test]
    fn o7_ctx_extended_reproof() {
        // Member equality needs a copy made just before the first member (q5 := q0): window-local from the
        // first member fails, the extended window (16 ops earlier) proves it.
        let all = Config { holds: true, cc_holds: true, shortcuts: false, mbu: false, mbu_ext: false, holder: false };
        let mut ops = vec![reg(0, 0), reg(0, 1)];
        ops.push(cx(0, 5));
        ops.push(ccx(0, 1, 2));
        ops.push(ccx(5, 1, 3));
        ops.push(hmr(6, 0));
        let p = plan(&ops, &all);
        assert_eq!(p.holds.len(), 1, "{:?}", p.stats);
        assert_eq!(p.stats.extended, 1, "{:?}", p.stats);
        let new = rewrite(ops.clone(), &p);
        assert_eq!(toffolis(&new), 1);
        exhaustive_equal(&ops, &new, &[0, 1], 7, 2, p.mbit);
    }

    #[test]
    fn o9_ctx_holder_exhaustive() {
        // q2 := a*b (clean target), then a*b toggled into q3 and q4 (inside a condition scope): both become CX(q2 -> .);
        // a complemented holder (q5 = a*b ^ 1) gets the X fix.
        let x = |q: u64| Op { kind: K::X, q_target: QubitId(q), ..Op::empty() };
        let cfg = Config { holds: false, cc_holds: false, shortcuts: false, mbu: false, mbu_ext: false, holder: true };
        let mut ops = vec![reg(0, 0), reg(0, 1), reg(0, 3), reg(0, 6)];
        ops.push(ccx(0, 1, 2));
        ops.push(ccx(0, 1, 3));
        ops.push(hmr(7, 0));
        ops.push(Op { kind: K::PushCondition, c_condition: BitId(0), ..Op::empty() });
        ops.push(ccx(0, 1, 4));
        ops.push(Op { kind: K::PopCondition, ..Op::empty() });
        let mut c1 = ccx(0, 1, 6);
        c1.c_condition = BitId(0);
        ops.push(c1);
        let p = plan(&ops, &cfg);
        assert_eq!(p.holders.len(), 3, "{:?}", p.stats);
        let new = rewrite(ops.clone(), &p);
        assert_eq!(toffolis(&new), 1);
        exhaustive_equal(&ops, &new, &[0, 1, 3, 6], 8, 2, p.mbit);
        // complemented holder
        let mut ops = vec![reg(0, 0), reg(0, 1), reg(0, 3)];
        ops.push(x(5));
        ops.push(ccx(0, 1, 5));
        ops.push(ccx(0, 1, 3));
        let p = plan(&ops, &cfg);
        assert_eq!(p.holders.len(), 1, "{:?}", p.stats);
        assert!(p.holders[0].2);
        let new = rewrite(ops.clone(), &p);
        assert_eq!(toffolis(&new), 1);
        exhaustive_equal(&ops, &new, &[0, 1, 3], 6, 1, p.mbit);
    }
}
