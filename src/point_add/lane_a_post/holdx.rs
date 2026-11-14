//! Lane A hold analysis with an XOR-of-atoms value model (round 105, our own code). A wire's value is a symbolic XOR
//! of atoms, kept as a 128-bit XOR-homomorphic hash: atoms are opaque values (inputs, measurement outcomes, writes the
//! model does not follow) or AND(u, v) of two values, whose hash is a keyed mix of the operands' hashes. X, CX, CCX
//! and Swap at depth 0 without a condition are followed exactly (t ^= ONE, t ^= c, t ^= AND(a, b), exchange), so a
//! register toggled and toggled back returns to the same hash, and a product of restored values gets the same key.
//! Equal hashes are taken as equal expressions (probability of a false match about n^2 / 2^128); the panels check the
//! result. Classical bits get values too (measurement outcomes are opaque atoms), and a write under condition value k
//! is followed symbolically: X: t ^= k; CX: t ^= AND(k, c); CCX: t ^= AND(k, AND(a, b)); Swap: both ^= AND(k, a ^ b);
//! reset: t = AND(k ^ 1, t). With xcond off conditional writes give fresh atoms instead.
//! Truth-model zeros (tz): the tree's truth-table model is stepped on the same ops and a written wire it proves zero is
//! taken as zero (more idle wires). With tz_thread the model runs on a second thread and hands over one flag byte per
//! op; the flags are the same function of the op sequence either way.
//! Merge lane: lane A's rtool holdx.rs with the I/O abstracted (scan closure, op count), knobs from `HoldCfg`, the
//! truth model's per-op zero flags factored out (`tz_flags`). Logic unchanged.
use super::hold::{touched, Analysis, Cand};
use super::HoldCfg;
use crate::circuit::{BitId, Op, OperationType, QubitId, NO_BIT};
use super::FxMap as HashMap;

const NONE: u32 = u32::MAX;
const ONE: u128 = 0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c834;
const TZ_BLOCK: usize = 1 << 16;

#[inline]
fn mix(mut z: u128) -> u128 {
    z = (z ^ (z >> 67)).wrapping_mul(0xbf58_476d_1ce4_e5b9_94d0_49bb_1331_11eb);
    z = (z ^ (z >> 61)).wrapping_mul(0x94d0_49bb_1331_11eb_bf58_476d_1ce4_e5b9);
    z ^ (z >> 59)
}
#[inline]
fn and_hash(x: u128, y: u128) -> u128 {
    if x == 0 || y == 0 || x ^ y == ONE {
        return 0;
    }
    if x == y || y == ONE {
        return x;
    }
    if x == ONE {
        return y;
    }
    let (a, b) = if x < y { (x, y) } else { (y, x) };
    let h = mix(mix(a ^ 0x5851_f42d_4c95_7f2d_1405_7b7e_f767_814f).wrapping_add(b.rotate_left(17)) ^ 0x2545_f491_4f6c_dd1d);
    if h == 0 || h == ONE {
        1
    } else {
        h
    }
}

/// Membership filter over the keys of `ent` (speed only): a clear bit proves a key absent, so the map lookup it would
/// skip could only have failed; a set bit falls through to the map. Rebuilt after every `retain`.
struct Filt {
    w: Vec<u64>,
    mask: u64,
}
impl Filt {
    fn new(lg: u32) -> Self {
        Filt { w: vec![0; 1usize << (lg - 6)], mask: (1u64 << lg) - 1 }
    }
    #[inline]
    fn h(&self, k: u128) -> usize {
        (((k as u64) ^ ((k >> 64) as u64).rotate_left(29)) & self.mask) as usize
    }
    #[inline]
    fn set(&mut self, k: u128) {
        let h = self.h(k);
        self.w[h >> 6] |= 1 << (h & 63);
    }
    #[inline]
    fn may(&self, k: u128) -> bool {
        let h = self.h(k);
        (self.w[h >> 6] >> (h & 63)) & 1 == 1
    }
    fn rebuild<'a>(&mut self, keys: impl Iterator<Item = &'a u128>) {
        self.w.iter_mut().for_each(|x| *x = 0);
        for &k in keys {
            self.set(k);
        }
    }
}

struct Entry {
    holders: Vec<u16>,
    src: u32,
    src_pos: u32,
    src_wire: u16,
    last: u32,
}

/// Synthetic analysis ops with the same analyze_ops result as the whole stream (registers, qubit and bit counts), for
/// the truth model's constructor (lane A's rtool `prescan`).
pub fn prescan<I: Iterator<Item = Op>, F: Fn() -> I>(scan: &F) -> Vec<Op> {
    let mut r = scan();
    let (mut nq, mut nb) = (0u64, 0u64);
    let mut pre: Vec<Op> = Vec::new();
    while let Some(op) = r.next() {
        for q in [op.q_control2.0, op.q_control1.0, op.q_target.0] {
            if q != u64::MAX {
                nq = nq.max(q + 1);
            }
        }
        for b in [op.c_target.0, op.c_condition.0] {
            if b != u64::MAX {
                nb = nb.max(b + 1);
            }
        }
        if op.kind == OperationType::Register || op.kind == OperationType::AppendToRegister {
            pre.push(op);
        }
    }
    let mut x = Op::empty();
    x.kind = OperationType::X;
    x.q_target = QubitId(nq - 1);
    pre.push(x);
    let mut bi = Op::empty();
    bi.kind = OperationType::BitInvert;
    bi.c_target = BitId(nb - 1);
    pre.push(bi);
    let (pq, pb, _, _) = crate::circuit::analyze_ops(pre.iter());
    assert_eq!((pq, pb), (nq, nb));
    pre
}

type TModel = super::super::truth_simplify::TModel;

/// The truth model as the hold pass uses it: stepped on every op, asked whether a wire is zero.
pub trait ZeroModel {
    fn step_op(&mut self, op: &Op);
    fn zero(&self, q: usize) -> bool;
}
impl ZeroModel for TModel {
    #[inline]
    fn step_op(&mut self, op: &Op) {
        self.step(op)
    }
    #[inline]
    fn zero(&self, q: usize) -> bool {
        self.is_zero(q)
    }
}
impl ZeroModel for super::tzmodel::FastModel {
    #[inline]
    fn step_op(&mut self, op: &Op) {
        self.step(op)
    }
    #[inline]
    fn zero(&self, q: usize) -> bool {
        self.is_zero(q)
    }
}
/// The model the chain uses: the inline-storage port when `fast`, else the tree's own.
pub fn new_model(pre: &[Op], fast: bool) -> Box<dyn ZeroModel> {
    if fast {
        Box::new(super::tzmodel::FastModel::new(pre))
    } else {
        Box::new(TModel::new(pre))
    }
}

/// Zero flags after stepping the truth model on `op`: bit k = written wire k (the order of holdx's `wr`) is zero.
#[inline]
pub fn tz_flags<M: ZeroModel + ?Sized>(m: &M, op: &Op) -> u8 {
    use OperationType::*;
    match op.kind {
        X | CX | CCX | Hmr | R => m.zero(op.q_target.0 as usize) as u8,
        Swap => m.zero(op.q_control1.0 as usize) as u8 | (m.zero(op.q_target.0 as usize) as u8) << 1,
        _ => 0,
    }
}

enum Tz {
    Off,
    Inline(Box<dyn ZeroModel>),
    Chan { rx: std::sync::mpsc::Receiver<Vec<u8>>, cur: Vec<u8>, k: usize },
}
impl Tz {
    #[inline]
    fn next(&mut self, op: &Op) -> u8 {
        match self {
            Tz::Off => 0,
            Tz::Inline(m) => {
                m.step_op(op);
                tz_flags(m.as_ref(), op)
            }
            Tz::Chan { rx, cur, k } => {
                if *k == cur.len() {
                    *cur = rx.recv().expect("truth-model thread ended early");
                    *k = 0;
                }
                *k += 1;
                cur[*k - 1]
            }
        }
    }
}

pub fn analyze_xor<I, F>(scan: &F, n: u64, cfg: &HoldCfg) -> Analysis
where
    I: Iterator<Item = Op>,
    F: Fn() -> I + Sync,
{
    if !cfg.tz {
        return analyze_inner(scan, n, cfg, Tz::Off);
    }
    let pre = prescan(scan);
    if !cfg.tz_thread {
        return analyze_inner(scan, n, cfg, Tz::Inline(new_model(&pre, cfg.tz_fast)));
    }
    std::thread::scope(|s| {
        let (tx, rx) = std::sync::mpsc::sync_channel::<Vec<u8>>(64);
        let pre = &pre;
        let fast = cfg.tz_fast;
        let h = s.spawn(move || {
            let t0 = std::time::Instant::now();
            let mut m = new_model(pre, fast);
            let mut blk: Vec<u8> = Vec::with_capacity(TZ_BLOCK);
            for op in scan() {
                m.step_op(&op);
                blk.push(tz_flags(m.as_ref(), &op));
                if blk.len() == TZ_BLOCK {
                    if tx.send(std::mem::replace(&mut blk, Vec::with_capacity(TZ_BLOCK))).is_err() {
                        return t0.elapsed().as_secs_f64();
                    }
                }
            }
            if !blk.is_empty() {
                let _ = tx.send(blk);
            }
            t0.elapsed().as_secs_f64()
        });
        let mut a = analyze_inner(scan, n, cfg, Tz::Chan { rx, cur: vec![], k: 0 });
        let tz_s = h.join().expect("truth-model thread");
        a.log += &format!(" tz_thread_s {:.1}", tz_s);
        a
    })
}

/// extra always-zero wires for the hold pass (our dial applied to this pass; the stream width is 740 + this)
pub const LANE_A_EXTRA_WIRES: usize = 1;
fn analyze_inner<I: Iterator<Item = Op>, F: Fn() -> I>(scan: &F, n: u64, cfg: &HoldCfg, mut tm: Tz) -> Analysis {
    let t_start = std::time::Instant::now();
    let horizon = cfg.horizon;
    let hold_cond = cfg.hold_cond;
    let mut r = scan();
    let (mut nq, mut nb) = (0usize, 0u64);
    let mut input_q: Vec<usize> = vec![];
    let mut n0 = 0u64;
    while let Some(op) = r.next() {
        n0 += 1;
        let mut t = [0usize; 3];
        let k = touched(&op, &mut t);
        for &q in &t[..k] {
            nq = nq.max(q + 1);
        }
        for b in [op.c_target.0, op.c_condition.0] {
            if b != u64::MAX {
                nb = nb.max(b + 1);
            }
        }
        if op.kind == OperationType::AppendToRegister && op.q_target.0 != u64::MAX {
            input_q.push(op.q_target.0 as usize);
        }
    }
    assert_eq!(n0, n);
    nq += LANE_A_EXTRA_WIRES;
    assert!(n < (u32::MAX - 2) as u64);
    let mut fresh_ctr: u128 = 1;
    let mut fresh = || {
        fresh_ctr += 1;
        let h = mix(fresh_ctr ^ 0x6a09_e667_f3bc_c908_bb67_ae85_84ca_a73b);
        if h == 0 || h == ONE {
            2
        } else {
            h
        }
    };
    let xcond = cfg.xcond;
    let tz_on = cfg.tz;
    let mut tz_hits = 0u64;
    let mut bits = vec![0u128; nb as usize + 1];
    let mut kstack: Vec<u128> = vec![];
    let mut kbase: u128 = ONE;
    // classical input bits: every register bit slot (declared by AppendToRegister with a bit target) is unknown
    {
        let mut r = scan();
        while let Some(op) = r.next() {
            if op.kind == OperationType::AppendToRegister && op.c_target.0 != u64::MAX {
                bits[op.c_target.0 as usize] = fresh();
            }
            if op.kind != OperationType::Register && op.kind != OperationType::AppendToRegister {
                break;
            }
        }
    }
    let mut val = vec![0u128; nq];
    for &q in &input_q {
        if q < nq && val[q] == 0 {
            val[q] = fresh();
        }
    }
    let mut open: Vec<u32> = (0..nq).map(|q| if val[q] == 0 { 0 } else { NONE }).collect();
    let mut pending = vec![false; nq];
    let mut pending_list: Vec<usize> = vec![];
    let mut ent: HashMap<u128, Entry> = HashMap::default();
    let mut filt = Filt::new(27);
    let mut intervals = vec![];
    let mut cands: Vec<Cand> = vec![];
    let mut free = vec![];
    let mut pend: Vec<(Cand, u128, u32)> = vec![];
    let mut rel: u32 = 0;
    // in-place holds: release by Hmr(w->m) at depth 0 followed by the matching CZ fix; m must not be read again before
    // it is written. inplace[src] is decided from that.
    let inplace_on = cfg.inplace;
    let mut inplace: Vec<bool> = vec![];
    let mut ip_pend: Option<(u32, u64, u128)> = None; // (src, bit m, key) waiting for the next op
    let mut bit_watch: HashMap<u64, u32> = HashMap::default();
    let (mut depth, mut frame_start) = (0usize, 0u32);
    let mut checked = 0u64;
    let mut r = scan();
    let mut i: u32 = 0;
    while let Some(op) = r.next() {
        use OperationType::*;
        if !pend.is_empty() {
            let mut k = 0;
            while k < pend.len() {
                if pend[k].2 == i {
                    let (mut cd, key, _) = pend.swap_remove(k);
                    if and_hash(val[cd.a as usize], val[cd.b as usize]) == key {
                        cd.oe = i - 1;
                        cands.push(cd);
                    }
                } else {
                    k += 1;
                }
            }
        }
        let mut cz_ok = false;
        if let Some((src, m, key)) = ip_pend.take() {
            if op.kind == CZ && depth == 0 && op.c_condition.0 == m
                && and_hash(val[op.q_control1.0 as usize], val[op.q_target.0 as usize]) == key
            {
                inplace[src as usize] = true;
                bit_watch.insert(m, src);
                cz_ok = true;
            }
        }
        if !cz_ok {
            if op.c_condition != NO_BIT {
                if let Some(src) = bit_watch.remove(&op.c_condition.0) {
                    inplace[src as usize] = false;
                }
            }
        }
        match op.kind {
            BitInvert => {
                if let Some(src) = bit_watch.remove(&op.c_target.0) {
                    inplace[src as usize] = false;
                }
            }
            Hmr | BitStore0 | BitStore1 => {
                bit_watch.remove(&op.c_target.0);
            }
            _ => {}
        }
        if i % (1 << 24) == 0 {
            if i > horizon {
                let lim = i - horizon;
                ent.retain(|_, e| !(e.holders.is_empty() && e.last < lim));
                filt.rebuild(ent.keys());
            }
        }
        let tzf = tm.next(&op);
        match op.kind {
            PushCondition => {
                if depth == 0 {
                    frame_start = i;
                }
                depth += 1;
                kstack.push(kbase);
                kbase = and_hash(kbase, bits[op.c_condition.0 as usize]);
                i += 1;
                continue;
            }
            PopCondition => {
                depth -= 1;
                kbase = kstack.pop().unwrap();
                if depth == 0 {
                    for pd in pend.iter_mut() {
                        if pd.2 == NONE {
                            pd.2 = i + 1;
                        }
                    }
                    for &w in &pending_list {
                        if pending[w] && val[w] == 0 {
                            open[w] = i + 1;
                        }
                        pending[w] = false;
                    }
                    pending_list.clear();
                }
                i += 1;
                continue;
            }
            _ => {}
        }
        let k = if op.c_condition != NO_BIT { and_hash(kbase, bits[op.c_condition.0 as usize]) } else { kbase };
        match op.kind {
            BitInvert => bits[op.c_target.0 as usize] ^= k,
            BitStore0 => {
                let b = op.c_target.0 as usize;
                bits[b] = if k == ONE { 0 } else { and_hash(k ^ ONE, bits[b]) };
            }
            BitStore1 => {
                let b = op.c_target.0 as usize;
                bits[b] = if k == ONE { ONE } else { and_hash(k ^ ONE, bits[b]) ^ k };
            }
            Hmr => bits[op.c_target.0 as usize] = fresh(),
            _ => {}
        }
        let mut tq = [0usize; 3];
        let nt = touched(&op, &mut tq);
        if nt == 0 {
            i += 1;
            continue;
        }
        let ins = if depth == 0 { i } else { frame_start };
        let cond = depth > 0 || op.c_condition != NO_BIT;
        let mut key_here: u128 = 0;
        if op.kind == CCX {
            let (a, b, t) = (tq[0], tq[1], tq[2]);
            let key = and_hash(val[a], val[b]);
            if key != 0 && (!cond || hold_cond) {
                if !cond {
                    checked += 1;
                }
                let found = if filt.may(key) { ent.get_mut(&key) } else { None };
                if let Some(e) = found {
                    e.last = i;
                    if let Some(&h) = e.holders.iter().find(|&&h| h as usize != t) {
                        free.push((i, h));
                    } else if e.src != NONE {
                        if !cond {
                            cands.push(Cand { p: e.src_pos, r: i, oe: i, src: e.src, wire: e.src_wire, tzero: val[t] == 0, cond: false, a: 0, b: 0 });
                        } else {
                            let cd = Cand { p: e.src_pos, r: i, oe: NONE, src: e.src, wire: e.src_wire, tzero: false, cond: true, a: a as u16, b: b as u16 };
                            pend.push((cd, key, if depth == 0 { i + 1 } else { NONE }));
                        }
                    }
                } else if !cond {
                    ent.insert(key, Entry { holders: vec![], src: NONE, src_pos: 0, src_wire: 0, last: i });
                    filt.set(key);
                }
            }
            key_here = key;
        }
        for &w in &tq[..nt] {
            if open[w] != NONE {
                if ins > open[w] {
                    intervals.push((open[w], ins, w as u16));
                }
                open[w] = NONE;
            }
            pending[w] = false;
        }
        let mut wr: [(usize, u128); 2] = [(usize::MAX, 0); 2];
        let mut nw = 0;
        let kk = if cond && !xcond { 0 } else { k };
        match op.kind {
            X => {
                let t = tq[0];
                wr[0] = (t, if kk != 0 { val[t] ^ kk } else { fresh() });
                nw = 1;
            }
            CX => {
                let (c, t) = (tq[0], tq[1]);
                wr[0] = (t, if val[c] == 0 { val[t] } else if kk != 0 { val[t] ^ and_hash(kk, val[c]) } else { fresh() });
                nw = 1;
            }
            CCX => {
                let t = tq[2];
                wr[0] = (t, if key_here == 0 { val[t] } else if kk != 0 { val[t] ^ and_hash(kk, key_here) } else { fresh() });
                nw = 1;
            }
            Swap => {
                let (a, b) = (tq[0], tq[1]);
                if val[a] == val[b] {
                    wr[0] = (a, val[a]);
                    wr[1] = (b, val[b]);
                } else if kk != 0 {
                    let m = and_hash(kk, val[a] ^ val[b]);
                    wr[0] = (a, val[a] ^ m);
                    wr[1] = (b, val[b] ^ m);
                } else {
                    wr[0] = (a, fresh());
                    wr[1] = (b, fresh());
                }
                nw = 2;
            }
            Hmr | R => {
                let t = tq[0];
                wr[0] = (t, if !cond || val[t] == 0 { 0 } else if kk != 0 { and_hash(kk ^ ONE, val[t]) } else { fresh() });
                nw = 1;
            }
            _ => {}
        }
        if tz_on {
            for k in 0..nw {
                if wr[k].1 != 0 && (tzf >> k) & 1 == 1 {
                    wr[k].1 = 0;
                    tz_hits += 1;
                }
            }
        }
        for &(w, nv) in &wr[..nw] {
            if nv != val[w] && nv != 0 && filt.may(nv) {
                if let Some(e) = ent.get_mut(&nv) {
                    e.holders.push(w as u16);
                    e.last = i;
                }
            }
        }
        for &(w, nv) in &wr[..nw] {
            let ov = val[w];
            if ov != 0 && nv != ov && filt.may(ov) {
                if let Some(e) = ent.get_mut(&ov) {
                    if let Some(pos) = e.holders.iter().position(|&h| h as usize == w) {
                        e.holders.swap_remove(pos);
                        if e.holders.is_empty() {
                            e.src = rel;
                            rel += 1;
                            e.src_pos = ins;
                            e.src_wire = w as u16;
                            e.last = i;
                            inplace.push(false);
                            if inplace_on && op.kind == Hmr && !cond {
                                ip_pend = Some((e.src, op.c_target.0, ov));
                            }
                        }
                    }
                }
            }
        }
        for &(w, nv) in &wr[..nw] {
            val[w] = nv;
        }
        for &w in &tq[..nt] {
            if val[w] == 0 {
                if depth == 0 {
                    open[w] = i + 1;
                } else if !pending[w] {
                    pending[w] = true;
                    pending_list.push(w);
                }
            }
        }
        i += 1;
    }
    assert_eq!(depth, 0);
    assert_eq!(i as u64, n);
    for (mut cd, key, e) in pend.drain(..) {
        assert_eq!(e, i);
        if and_hash(val[cd.a as usize], val[cd.b as usize]) == key {
            cd.oe = i - 1;
            cands.push(cd);
        }
    }
    cands.sort_by_key(|c| c.r);
    for w in 0..nq {
        if open[w] != NONE && (n as u32) > open[w] {
            intervals.push((open[w], n as u32, w as u16));
        }
    }
    let log = format!(
        "analyze: ops {} nq {} nb {} intervals {} cands {} free {} releases {} in-place eligible {} truth-zero overrides {} analyze_s {:.1}",
        n, nq, nb, intervals.len(), cands.len(), free.len(), rel, inplace.iter().filter(|&&x| x).count(), tz_hits,
        t_start.elapsed().as_secs_f64()
    );
    Analysis { intervals, cands, free, n, nq, nb, checked, inplace, log }
}
