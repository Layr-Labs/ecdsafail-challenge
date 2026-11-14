//! Lane A's own hold pass (round 105): selection and rewrite. Written from the mechanism in public notes (a product
//! rebuilt by an unconditional Toffoli is kept alive on idle wires instead), not from anyone's code.
//! A wire is idle on [start, end): known zero and untouched. Starts are snapped to positions outside condition
//! frames, ends are the insertion point of the next touch (the outermost frame start if the touch is inside a
//! frame), so every insertion (copy, hop, delivery) is unconditional.
//! Candidate: a depth-0 unconditional CCX(a,b->t) whose product was held earlier and released (last holder
//! written) at insertion point p. Hold interval [p, r]. Feasible iff at every position the number of active holds is
//! at most the number of idle wires there (hops re-pack held values onto idle wires at every boundary).
//! Selection: candidates by increasing r, accepted if the interval still fits (segment tree over compressed
//! coordinates). Free witness: a wire still holds the product at r: CCX -> CX.
//! Rewrite: copy CX(w->h) at p (or, in place, the release Hmr and its CZ fix are dropped and w keeps the product),
//! Swap hops when h's idle interval ends, delivery at r: Swap(h,t) if t is zero, else CX(h->t) then (last use)
//! Hmr(h->m), CZ(a,b if m) with one new classical bit m.
//! Merge lane: lane A's rtool hold.rs `run` split into `select` and `rewrite`, I/O abstracted; the analysis is
//! holdx.rs (XOR keys). Logic unchanged.
use super::counts::Lite as Counts;
use crate::circuit::{BitId, Op, OperationType, QubitId};
use std::cmp::Reverse;
use super::FxMap as HashMap;
use std::collections::{BTreeSet, BinaryHeap};

pub const NONE: u32 = u32::MAX;

#[derive(Clone, Copy)]
pub struct Cand {
    pub p: u32,
    pub r: u32,
    pub oe: u32, // last position the hold must occupy (r, or e-1 for a conditional delivery measured at e)
    pub src: u32,
    pub wire: u16,
    pub tzero: bool,
    pub cond: bool,
    pub a: u16,
    pub b: u16,
}

pub fn touched(op: &Op, out: &mut [usize; 3]) -> usize {
    use OperationType::*;
    match op.kind {
        X | Z | R | Hmr => {
            out[0] = op.q_target.0 as usize;
            1
        }
        CX | CZ | Swap => {
            out[0] = op.q_control1.0 as usize;
            out[1] = op.q_target.0 as usize;
            2
        }
        CCX | CCZ => {
            out[0] = op.q_control1.0 as usize;
            out[1] = op.q_control2.0 as usize;
            out[2] = op.q_target.0 as usize;
            3
        }
        _ => 0,
    }
}

pub struct Analysis {
    pub intervals: Vec<(u32, u32, u16)>,
    pub cands: Vec<Cand>,
    pub free: Vec<(u32, u16)>,
    pub n: u64,
    pub nq: usize,
    pub nb: u64,
    pub checked: u64,
    /// per release id: the release is an Hmr(w->m) directly followed by its matching CZ fix and m is not read again
    /// before it is written, so the hold can stay on w (delete Hmr and CZ) and start at p + 1 (empty: never)
    pub inplace: Vec<bool>,
    pub log: String,
}

struct Seg {
    sz: usize,
    mn: Vec<i32>,
    lz: Vec<i32>,
}
impl Seg {
    fn new(v: &[i32]) -> Self {
        let mut sz = 1;
        while sz < v.len().max(1) {
            sz <<= 1;
        }
        let mut mn = vec![i32::MAX / 2; 2 * sz];
        mn[sz..sz + v.len()].copy_from_slice(v);
        for k in (1..sz).rev() {
            mn[k] = mn[2 * k].min(mn[2 * k + 1]);
        }
        Self { sz, mn, lz: vec![0; 2 * sz] }
    }
    fn upd(&mut self, k: usize, l: usize, r: usize, ql: usize, qr: usize, d: i32) {
        if qr <= l || r <= ql {
            return;
        }
        if ql <= l && r <= qr {
            self.mn[k] += d;
            self.lz[k] += d;
            return;
        }
        let m = (l + r) / 2;
        self.upd(2 * k, l, m, ql, qr, d);
        self.upd(2 * k + 1, m, r, ql, qr, d);
        self.mn[k] = self.mn[2 * k].min(self.mn[2 * k + 1]) + self.lz[k];
    }
    fn qry(&self, k: usize, l: usize, r: usize, ql: usize, qr: usize) -> i32 {
        if qr <= l || r <= ql {
            return i32::MAX / 2;
        }
        if ql <= l && r <= qr {
            return self.mn[k];
        }
        let m = (l + r) / 2;
        self.qry(2 * k, l, m, ql, qr).min(self.qry(2 * k + 1, m, r, ql, qr)) + self.lz[k]
    }
}

/// What the rewrite needs.
pub struct Plan {
    intervals: Vec<(u32, u32, u16)>,
    free: Vec<(u32, u16)>,
    copies: Vec<(u32, u32, u16)>, // (p, src, wire)
    inpl: Vec<(u32, u32, u16)>,   // in-place sources: (p = the Hmr, src, wire)
    deliv: Vec<(u32, u32, bool, bool, bool, u32)>, // (r, src, final, tzero, cond, oe)
    nq: usize,
    nb: u64,
    log: String,
}

pub fn select(mut a: Analysis) -> Plan {
    let t0 = std::time::Instant::now();
    let n = a.n as usize;
    // capacity profile c(i)
    let mut c: Vec<i16> = vec![0; n + 1];
    for &(s, e, _) in &a.intervals {
        c[s as usize] += 1;
        c[e as usize] -= 1;
    }
    let mut run = 0i32;
    for x in c.iter_mut() {
        run += *x as i32;
        assert!(run >= 0 && run < 32000);
        *x = run as i16;
    }
    // compressed coordinates
    let mut xs: Vec<u32> = Vec::with_capacity(2 * a.cands.len() + 2);
    for cd in &a.cands {
        xs.push(cd.p);
        xs.push(cd.p + 1);
        xs.push(cd.oe + 1);
    }
    xs.sort_unstable();
    xs.dedup();
    let m = xs.len().saturating_sub(1);
    let mut cmin = vec![i32::MAX / 2; m];
    for k in 0..m {
        let (lo, hi) = (xs[k] as usize, xs[k + 1] as usize);
        let mut mn = i32::MAX / 2;
        for &x in &c[lo..hi] {
            mn = mn.min(x as i32);
        }
        cmin[k] = mn;
    }
    drop(c);
    let mut seg = Seg::new(&cmin);
    drop(cmin);
    let idx = |x: u32| xs.binary_search(&x).unwrap();
    let mut last_acc: HashMap<u32, u32> = HashMap::default();
    let mut acc: Vec<usize> = vec![];
    for (j, cd) in a.cands.iter().enumerate() {
        let ip = a.inplace.get(cd.src as usize).copied().unwrap_or(false);
        let lo = match last_acc.get(&cd.src) {
            Some(&r0) => r0 + 1,
            None => cd.p + ip as u32,
        };
        if lo > cd.oe {
            // the hold already covers this delivery
            acc.push(j);
            continue;
        }
        // lo may be r0+1 which is a coordinate (it is some candidate's oe+1)
        let (l, rr) = (idx(lo), idx(cd.oe + 1));
        if seg.qry(1, 0, seg.sz, l, rr) >= 1 {
            seg.upd(1, 0, seg.sz, l, rr, -1);
            last_acc.insert(cd.src, cd.oe);
            acc.push(j);
        }
    }
    drop(seg);
    let mut copies: Vec<(u32, u32, u16)> = vec![];
    let mut inpl: Vec<(u32, u32, u16)> = vec![];
    let mut deliv: Vec<(u32, u32, bool, bool, bool, u32)> = vec![];
    {
        let mut first: HashMap<u32, bool> = HashMap::default();
        for &j in &acc {
            let cd = a.cands[j];
            if first.insert(cd.src, true).is_none() {
                if a.inplace.get(cd.src as usize).copied().unwrap_or(false) {
                    inpl.push((cd.p, cd.src, cd.wire));
                } else {
                    copies.push((cd.p, cd.src, cd.wire));
                }
            }
            let fin = last_acc[&cd.src] == cd.oe;
            deliv.push((cd.r, cd.src, fin, cd.tzero, cd.cond, cd.oe));
        }
    }
    copies.sort_unstable();
    inpl.sort_unstable();
    deliv.sort_unstable();
    let log = format!(
        "{} select: candidates {} accepted {} sources {} (in place {}) free {} checked {} select_s {:.1}",
        a.log, a.cands.len(), acc.len(), copies.len() + inpl.len(), inpl.len(), a.free.len(), a.checked,
        t0.elapsed().as_secs_f64()
    );
    a.cands = vec![];
    a.intervals.sort_unstable_by_key(|x| x.0);
    Plan { intervals: a.intervals, free: a.free, copies, inpl, deliv, nq: a.nq, nb: a.nb, log }
}

struct Em<'a, O: FnMut(Op)> {
    out: &'a mut O,
    cnt: Counts,
}
impl<'a, O: FnMut(Op)> Em<'a, O> {
    #[inline]
    fn emit(&mut self, op: Op) {
        self.cnt.add(&op);
        (self.out)(op);
    }
}

pub fn rewrite<C: Iterator<Item = Op>, O: FnMut(Op)>(pl: Plan, input: C, out: &mut O) -> String {
    let Plan { intervals, free, copies, inpl, deliv, nq, nb, log } = pl;
    let t0 = std::time::Instant::now();
    let mbit = BitId(nb);
    let mut held: Vec<u32> = vec![NONE; nq];
    let mut iend: Vec<u32> = vec![0; nq];
    let mut hold_wire: HashMap<u32, u16> = HashMap::default();
    let mut pool: BTreeSet<(u32, u16)> = BTreeSet::new();
    let mut heap: BinaryHeap<Reverse<(u32, u16)>> = BinaryHeap::new();
    let (mut ii, mut ci, mut di, mut fi) = (0usize, 0usize, 0usize, 0usize);
    let mut em = Em { out, cnt: Counts::default() };
    let mut cnt_in = Counts::default();
    let (mut hops, mut ncopy, mut ndel, mut nfin_swap, mut nfin_meas, mut nfree_done) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mk = |kind: OperationType, t: usize, c1: usize, c2: usize| {
        let mut o = Op::empty();
        o.kind = kind;
        o.q_target = QubitId(t as u64);
        if c1 != usize::MAX {
            o.q_control1 = QubitId(c1 as u64);
        }
        if c2 != usize::MAX {
            o.q_control2 = QubitId(c2 as u64);
        }
        o
    };
    let mut i: u32 = 0;
    let mut depth = 0usize;
    let mut ipi = 0usize;
    let mut inpl_wait: Option<usize> = None; // wire held in place whose idle interval starts at the next position
    let mut skip_cz = false;
    // final measurements of conditional deliveries: (e, src, a, b), sorted by e when pushed (e only grows)
    let mut meas: std::collections::VecDeque<(u32, u32, u16, u16)> = std::collections::VecDeque::new();
    let mut ncond = 0u64;
    let do_meas = |em: &mut Em<'_, O>, h: usize, a: usize, b: usize| {
        let mut m = Op::empty();
        m.kind = OperationType::Hmr;
        m.q_target = QubitId(h as u64);
        m.c_target = mbit;
        em.emit(m);
        let mut z = mk(OperationType::CZ, b, a, usize::MAX);
        z.c_condition = mbit;
        em.emit(z);
    };
    for op in input {
        cnt_in.add(&op);
        if depth == 0 {
            // 0. measured ends of conditional deliveries
            while let Some(&(e, src, ca, cb)) = meas.front() {
                if e > i {
                    break;
                }
                assert_eq!(e, i, "measurement point skipped");
                meas.pop_front();
                let h = hold_wire.remove(&src).unwrap() as usize;
                do_meas(&mut em, h, ca as usize, cb as usize);
                held[h] = NONE;
                if iend[h] > i {
                    pool.insert((iend[h], h as u16));
                }
            }
            // 1. interval starts
            while ii < intervals.len() && intervals[ii].0 <= i {
                let (s, e, q) = intervals[ii];
                assert_eq!(s, i, "interval start skipped");
                let q = q as usize;
                iend[q] = e;
                heap.push(Reverse((e, q as u16)));
                if held[q] == NONE {
                    pool.insert((e, q as u16));
                } else {
                    assert_eq!(inpl_wait, Some(q), "held wire {q} starts an interval at {i}");
                    inpl_wait = None;
                }
                ii += 1;
            }
            // 2. interval ends (hops for held wires)
            let mut need: Vec<(usize, u32)> = vec![];
            while let Some(&Reverse((e, q))) = heap.peek() {
                if e > i {
                    break;
                }
                assert_eq!(e, i, "interval end skipped");
                heap.pop();
                let q = q as usize;
                if held[q] != NONE {
                    need.push((q, held[q]));
                } else {
                    pool.remove(&(e, q as u16));
                }
            }
            for (q, src) in need {
                let (e2, h2) = pool.pop_last().unwrap_or_else(|| panic!("no idle wire for hop at {i}"));
                assert!(e2 > i);
                em.emit(mk(OperationType::Swap, h2 as usize, q, usize::MAX));
                held[q] = NONE;
                held[h2 as usize] = src;
                hold_wire.insert(src, h2);
                hops += 1;
            }
            // 3. copies starting here
            while ci < copies.len() && copies[ci].0 <= i {
                let (p, src, wire) = copies[ci];
                assert_eq!(p, i);
                let (e2, h) = pool.pop_last().unwrap_or_else(|| panic!("no idle wire for copy at {i}"));
                assert!(e2 > i);
                em.emit(mk(OperationType::CX, h as usize, wire as usize, usize::MAX));
                held[h as usize] = src;
                hold_wire.insert(src, h);
                ncopy += 1;
                ci += 1;
            }
        } else {
            assert!(ii >= intervals.len() || intervals[ii].0 > i);
            assert!(ci >= copies.len() || copies[ci].0 > i);
        }
        match op.kind {
            OperationType::PushCondition => depth += 1,
            OperationType::PopCondition => depth -= 1,
            _ => {}
        }
        if skip_cz {
            assert_eq!(op.kind, OperationType::CZ);
            skip_cz = false;
            i += 1;
            continue;
        }
        if ipi < inpl.len() && inpl[ipi].0 == i {
            let (_, src, wire) = inpl[ipi];
            ipi += 1;
            assert_eq!(op.kind, OperationType::Hmr);
            assert_eq!(op.q_target.0 as usize, wire as usize);
            assert_eq!(held[wire as usize], NONE);
            held[wire as usize] = src;
            hold_wire.insert(src, wire);
            inpl_wait = Some(wire as usize);
            skip_cz = true;
            ncopy += 1;
            i += 1;
            continue;
        }
        // no original op may touch a held wire
        let mut tq = [0usize; 3];
        let nt = touched(&op, &mut tq);
        for &q in &tq[..nt] {
            assert!(held[q] == NONE, "op {i} touches held wire {q}");
        }
        if di < deliv.len() && deliv[di].0 == i {
            let (_, src, fin, tzero, cond, oe) = deliv[di];
            assert_eq!(op.kind, OperationType::CCX);
            let h = hold_wire[&src] as usize;
            let (ca, cb, t) = (op.q_control1.0 as usize, op.q_control2.0 as usize, op.q_target.0 as usize);
            if cond {
                let mut x = mk(OperationType::CX, t, h, usize::MAX);
                x.c_condition = op.c_condition;
                em.emit(x);
                if fin {
                    if let Some(&(e0, _, _, _)) = meas.back() {
                        assert!(e0 <= oe + 1);
                    }
                    meas.push_back((oe + 1, src, ca as u16, cb as u16));
                }
                ncond += 1;
            } else if fin {
                if tzero {
                    em.emit(mk(OperationType::Swap, t, h, usize::MAX));
                    nfin_swap += 1;
                } else {
                    em.emit(mk(OperationType::CX, t, h, usize::MAX));
                    do_meas(&mut em, h, ca, cb);
                    nfin_meas += 1;
                }
                held[h] = NONE;
                hold_wire.remove(&src);
                assert!(iend[h] > i);
                pool.insert((iend[h], h as u16));
            } else {
                em.emit(mk(OperationType::CX, t, h, usize::MAX));
            }
            ndel += 1;
            di += 1;
        } else if fi < free.len() && free[fi].0 == i {
            let (_, h) = free[fi];
            assert_eq!(op.kind, OperationType::CCX);
            let mut x = mk(OperationType::CX, op.q_target.0 as usize, h as usize, usize::MAX);
            x.c_condition = op.c_condition;
            em.emit(x);
            nfree_done += 1;
            fi += 1;
        } else {
            em.emit(op);
        }
        assert!(di >= deliv.len() || deliv[di].0 > i);
        assert!(fi >= free.len() || free[fi].0 > i);
        i += 1;
    }
    while let Some((e, src, ca, cb)) = meas.pop_front() {
        assert_eq!(e, i);
        let h = hold_wire.remove(&src).unwrap() as usize;
        do_meas(&mut em, h, ca as usize, cb as usize);
        held[h] = NONE;
    }
    assert!(hold_wire.is_empty());
    let cnt_out = em.cnt;
    format!(
        "{} | HOLD before=({}, {}, {:.1}) after=({}, {}, {:.1}) deliveries {} final_swap {} final_meas {} copies {} hops {} free {} cond {} rewrite_s {:.1}",
        log, cnt_in.ops, cnt_in.native, cnt_in.expected(), cnt_out.ops, cnt_out.native, cnt_out.expected(), ndel, nfin_swap,
        nfin_meas, ncopy, hops, nfree_done, ncond, t0.elapsed().as_secs_f64()
    )
}
