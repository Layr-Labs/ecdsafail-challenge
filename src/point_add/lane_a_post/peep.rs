//! Lane A's own pair pass (round 105), written from the rule descriptions in public notes, not from their code.
//! Works on depth-0 unconditional Toffolis. A later CCX_j = CCX(a,b->t) may move back to just after an earlier
//! CCX_i if every op strictly between them commutes with it: no write of a or b, and no touch of t other than an
//! X-type toggle (X, CX or CCX targeting t). Then, with CCX_i:
//!   (a) same controls, same target:            both cancel                                  (-2 T)
//!   (b) same controls, other target t1:          CX(t1->t) CCX(a,b->t1) CX(t1->t)             (-1 T)
//!   (c) same target, one shared control a, CCX_i = CCX(a,c->t):  CX(c->b) CCX(a,b->t) CX(c->b) (-1 T)
//! (b) toggles t and t1 by a.b; (c) toggles t by a.(b xor c); b at i equals b at j since nothing writes it between.
//! Each op takes part in at most one rewrite. Pass 1 decides from the original stream, pass 2 rewrites.
//! Merge lane: lane A's rtool peep.rs with the I/O abstracted (rules a, b, c always on; no env, no debug output).
use super::counts::Lite as Counts;
use crate::circuit::{Op, OperationType, QubitId, NO_BIT};
use super::FxMap as HashMap;

#[derive(Clone, Copy)]
pub struct Dec {
    i: u32,
    j: u32,
    rule: u8,
    x: u16, // (b): t of CCX_j ; (c): b of CCX_j (the control the CX targets)
    y: u16, // (c): c of CCX_i
}

pub struct Plan {
    decs: Vec<Dec>,
    skip: Vec<u32>,
    na: u64,
    nb: u64,
    nc: u64,
    decide_s: f64,
}

/// Pair map: dense (qubit indices below DENSE, so at most DENSE^2 = 1M keys, under the 4M retain threshold: the
/// retain never runs and the dense table is the same map) or hashed.
const DENSE: usize = 1 << 10;
enum PairMap {
    Dense(Vec<(u32, u16)>),
    Hash(HashMap<(u16, u16), (u32, u16)>),
}
impl PairMap {
    fn new(dense: bool) -> Self {
        if dense { PairMap::Dense(vec![(u32::MAX, 0); DENSE * DENSE]) } else { PairMap::Hash(HashMap::default()) }
    }
    #[inline]
    fn get(&self, k: (u16, u16)) -> Option<(u32, u16)> {
        match self {
            PairMap::Dense(v) => {
                let e = v[k.0 as usize * DENSE + k.1 as usize];
                if e.0 == u32::MAX { None } else { Some(e) }
            }
            PairMap::Hash(m) => m.get(&k).copied(),
        }
    }
    #[inline]
    fn insert(&mut self, k: (u16, u16), val: (u32, u16)) {
        match self {
            PairMap::Dense(v) => v[k.0 as usize * DENSE + k.1 as usize] = val,
            PairMap::Hash(m) => {
                m.insert(k, val);
            }
        }
    }
    fn len_over(&self, lim: usize) -> bool {
        match self {
            PairMap::Dense(_) => false,
            PairMap::Hash(m) => m.len() > lim,
        }
    }
    fn retain_from(&mut self, lim: u32) {
        if let PairMap::Hash(m) = self {
            m.retain(|_, v| v.0 >= lim);
        }
    }
}

pub fn decide<I: Iterator<Item = Op>, F: Fn() -> I>(n: u64, scan: &F) -> Plan {
    let t0 = std::time::Instant::now();
    let (ra, rb, rc) = (true, true, true);
    let mut maxq = 0u64;
    for op in scan() {
        for q in [op.q_control2.0, op.q_control1.0, op.q_target.0] {
            if q != u64::MAX {
                maxq = maxq.max(q);
            }
        }
    }
    let dense = (maxq as usize) < DENSE;
    let mut r = scan();
    let n = n as usize;
    let mut used = vec![0u64; n / 64 + 1];
    let is_used = |u: &Vec<u64>, k: u32| (u[k as usize >> 6] >> (k & 63)) & 1 == 1;
    let set_used = |u: &mut Vec<u64>, k: u32| u[k as usize >> 6] |= 1 << (k & 63);
    let nq = 1 << 16;
    let mut lw = vec![u32::MAX; nq]; // last write
    let mut nx = vec![u32::MAX; nq]; // last non-X-type touch
    let get = |v: &Vec<u32>, q: usize| if v[q] == u32::MAX { None } else { Some(v[q]) };
    let mut by_ctrl = PairMap::new(dense);
    let mut by_tc = PairMap::new(dense);
    let mut decs: Vec<Dec> = vec![];
    let mut depth = 0usize;
    let mut i: u32 = 0;
    let (mut na, mut nb, mut nc) = (0u64, 0u64, 0u64);
    while let Some(op) = r.next() {
        use OperationType::*;
        match op.kind {
            PushCondition => depth += 1,
            PopCondition => depth -= 1,
            _ => {}
        }
        let (t, c1, c2) = (op.q_target.0 as usize, op.q_control1.0 as usize, op.q_control2.0 as usize);
        if op.kind == CCX && depth == 0 && op.c_condition == NO_BIT {
            let (a, b) = if c1 < c2 { (c1, c2) } else { (c2, c1) };
            let blk = [get(&lw, a), get(&lw, b), get(&nx, t)].iter().flatten().copied().max();
            let ok = |pi: u32| blk.map_or(true, |bk| bk < pi);
            let mut done = false;
            if ra || rb {
                if let Some((pi, t1)) = by_ctrl.get((a as u16, b as u16)) {
                    if ok(pi) && !is_used(&used, pi) {
                        if t1 as usize == t && ra {
                            decs.push(Dec { i: pi, j: i, rule: 0, x: 0, y: 0 });
                            na += 1;
                            done = true;
                        } else if t1 as usize != t && rb {
                            decs.push(Dec { i: pi, j: i, rule: 1, x: t as u16, y: 0 });
                            nb += 1;
                            done = true;
                        }
                        if done {
                            set_used(&mut used, pi);
                            set_used(&mut used, i);
                        }
                    }
                }
            }
            if !done && rc {
                for (sh, other) in [(a, b), (b, a)] {
                    if let Some((pi, cc)) = by_tc.get((t as u16, sh as u16)) {
                        let cc = cc as usize;
                        if cc != other && cc != t && ok(pi) && !is_used(&used, pi) {
                            decs.push(Dec { i: pi, j: i, rule: 2, x: other as u16, y: cc as u16 });
                            nc += 1;
                            set_used(&mut used, pi);
                            set_used(&mut used, i);
                            done = true;
                            break;
                        }
                    }
                }
            }
            if !done {
                by_ctrl.insert((a as u16, b as u16), (i, t as u16));
                by_tc.insert((t as u16, a as u16), (i, b as u16));
                by_tc.insert((t as u16, b as u16), (i, a as u16));
            }
        }
        // update blockers with this op
        match op.kind {
            X => lw[t] = i,
            CX => {
                lw[t] = i;
                nx[c1] = i;
            }
            CCX => {
                lw[t] = i;
                nx[c1] = i;
                nx[c2] = i;
            }
            Z => nx[t] = i,
            CZ => {
                nx[t] = i;
                nx[c1] = i;
            }
            CCZ => {
                nx[t] = i;
                nx[c1] = i;
                nx[c2] = i;
            }
            Swap => {
                lw[t] = i;
                lw[c1] = i;
                nx[t] = i;
                nx[c1] = i;
            }
            Hmr | R => {
                lw[t] = i;
                nx[t] = i;
            }
            _ => {}
        }
        if i % (1 << 24) == 0 && by_ctrl.len_over(4_000_000) {
            let lim = i.saturating_sub(1 << 22);
            by_ctrl.retain_from(lim);
            by_tc.retain_from(lim);
        }
        i += 1;
    }
    decs.sort_unstable_by_key(|d| d.i);
    let mut skip: Vec<u32> = decs.iter().map(|d| d.j).collect();
    skip.sort_unstable();
    Plan { decs, skip, na, nb, nc, decide_s: t0.elapsed().as_secs_f64() }
}

pub fn rewrite<C: Iterator<Item = Op>, O: FnMut(Op)>(p: &Plan, input: C, out: &mut O) -> String {
    let t0 = std::time::Instant::now();
    let (decs, skip) = (&p.decs, &p.skip);
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
    let (mut cin, mut cout) = (Counts::default(), Counts::default());
    let (mut di, mut si) = (0usize, 0usize);
    let mut i: u32 = 0;
    for op in input {
        cin.add(&op);
        let mut emit = |o: Op| {
            cout.add(&o);
            out(o);
        };
        if si < skip.len() && skip[si] == i {
            si += 1;
        } else if di < decs.len() && decs[di].i == i {
            let d = decs[di];
            di += 1;
            assert_eq!(op.kind, OperationType::CCX);
            let (t1, a, b) = (op.q_target.0 as usize, op.q_control1.0 as usize, op.q_control2.0 as usize);
            match d.rule {
                0 => {}
                1 => {
                    let t = d.x as usize;
                    emit(mk(OperationType::CX, t, t1, usize::MAX));
                    emit(op);
                    emit(mk(OperationType::CX, t, t1, usize::MAX));
                }
                _ => {
                    // op = CCX(s, c -> t) with shared control s; CCX_j = CCX(s, bb -> t)
                    let (bb, cc) = (d.x as usize, d.y as usize);
                    let s = if a == cc { b } else { a };
                    assert!(a == cc || b == cc);
                    emit(mk(OperationType::CX, bb, cc, usize::MAX));
                    emit(mk(OperationType::CCX, t1, s, bb));
                    emit(mk(OperationType::CX, bb, cc, usize::MAX));
                }
            }
        } else {
            emit(op);
        }
        i += 1;
    }
    assert!(di == decs.len() && si == skip.len());
    format!(
        "PEEP before=({}, {}, {:.1}) after=({}, {}, {:.1}) a {} b {} c {} decide_s {:.1} rewrite_s {:.1}",
        cin.ops, cin.native, cin.expected(), cout.ops, cout.native, cout.expected(), p.na, p.nb, p.nc, p.decide_s,
        t0.elapsed().as_secs_f64()
    )
}
