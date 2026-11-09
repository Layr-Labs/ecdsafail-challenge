//! Factor consecutive same-target quadratic updates through affine control changes.
//! At every accepted site the target is never read; all other wire changes stay in order.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
const MAX: usize = 24;
const ONE: u64 = 1u64 << 63;
fn unsigned(op: Op) -> bool {
    op.c_condition == NO_BIT && matches!(op.kind, K::X | K::CX | K::CCX)
}
fn small(k: K, a: QubitId, b: QubitId, t: QubitId) -> Op {
    Op {
        kind: k,
        q_control2: a,
        q_control1: b,
        q_target: t,
        ..Op::empty()
    }
}
#[derive(Clone, Copy)]
struct Function {
    rows: [u64; MAX],
    lin: u64,
    sign: bool,
}
impl Function {
    fn zero() -> Self {
        Self {
            rows: [0; MAX],
            lin: 0,
            sign: false,
        }
    }
    fn add(&mut self, u: u64, v: u64) {
        let (a, b) = (u & !ONE, v & !ONE);
        let mut mix = a | b;
        while mix != 0 {
            let i = mix.trailing_zeros() as usize;
            let bit = 1u64 << i;
            mix ^= bit;
            let mut row = 0;
            if a & bit != 0 {
                row ^= b;
            }
            if b & bit != 0 {
                row ^= a;
            }
            self.rows[i] ^= row & !bit;
        }
        self.lin ^= a & b;
        if u & ONE != 0 {
            self.lin ^= b;
        }
        if v & ONE != 0 {
            self.lin ^= a;
        }
        self.sign ^= (u & v & ONE) != 0;
    }
    fn factors(
        mut self,
        limit: usize,
    ) -> Option<([(usize, usize, u64, u64); MAX / 2], usize, u64, bool, usize)> {
        let mut terms = [(0, 0, 0, 0); MAX / 2];
        let mut r = 0;
        let mut cn = 0;
        loop {
            let mut best = (u32::MAX, 0usize, 0usize);
            for i in 0..MAX {
                let mut candidates = self.rows[i] & (!0u64 << (i + 1));
                while candidates != 0 {
                    let j = candidates.trailing_zeros() as usize;
                    candidates &= candidates - 1;
                    let w = self.rows[i].count_ones() + self.rows[j].count_ones();
                    best = best.min((w, i, j));
                }
            }
            if best.0 == u32::MAX {
                break;
            }
            r += 1;
            if r >= limit {
                return None;
            }
            let (_, i, j) = best;
            let (a, b) = (self.rows[j], self.rows[i]);
            let (ai, bj) = (a ^ (1 << i), b ^ (1 << j));
            assert_eq!(ai & (1 << j), 0);
            assert_eq!(bj & (1 << i), 0);
            terms[r - 1] = (i, j, ai, bj);
            cn += 2 * (ai.count_ones() + bj.count_ones()) as usize + 1;
            self.add(a, b);
            assert_eq!((self.rows[i], self.rows[j]), (0, 0));
        }
        cn += self.lin.count_ones() as usize + usize::from(self.sign);
        Some((terms, r, self.lin, self.sign, cn))
    }
}
struct Bases {
    wire: [QubitId; MAX],
    value: [u64; MAX],
    n: usize,
}
impl Bases {
    fn new() -> Self {
        Self {
            wire: [NO_QUBIT; MAX],
            value: [0; MAX],
            n: 0,
        }
    }
    fn index(&mut self, q: QubitId) -> Option<usize> {
        if let Some(i) = self.wire[..self.n].iter().position(|&other| other == q) {
            return Some(i);
        }
        if self.n == MAX {
            return None;
        }
        let i = self.n;
        self.n += 1;
        self.wire[i] = q;
        self.value[i] = 1 << i;
        Some(i)
    }
}
#[derive(Debug, Default)]
pub(super) struct Counts {
    pub(super) groups: u64,
    pub(super) saved: u64,
    pub(super) added: i64,
    pub(super) max_saving: u64,
    pub(super) multi: u64,
}
pub(super) fn lower(
    input: &[Op],
    out: &mut Vec<Op>,
    stats: &mut Counts,
    window: usize,
    mut credit: usize,
) {
    let mut i = 0;
    while i < input.len() {
        let head = input[i];
        if head.kind != K::CCX || !unsigned(head) {
            out.push(head);
            i += 1;
            continue;
        }
        let t = head.q_target;
        let mut bases = Bases::new();
        let mut f = Function::zero();
        let mut originals = 0usize;
        let mut best = None;
        let mut best_score = (0, 0);
        for k in i..input.len().min(i + window) {
            let g = input[k];
            if !unsigned(g) {
                break;
            }
            match g.kind {
                K::X if g.q_target == t => {}
                K::X => {
                    let Some(d) = bases.index(g.q_target) else {
                        break;
                    };
                    bases.value[d] ^= ONE;
                }
                K::CX if g.q_control1 == t => break,
                K::CX if g.q_target == t => {}
                K::CX => {
                    let Some(a) = bases.index(g.q_control1) else {
                        break;
                    };
                    let Some(d) = bases.index(g.q_target) else {
                        break;
                    };
                    bases.value[d] ^= bases.value[a];
                }
                K::CCX if g.q_target != t => break,
                K::CCX => {
                    let Some(a) = bases.index(g.q_control1) else {
                        break;
                    };
                    let Some(b) = bases.index(g.q_control2) else {
                        break;
                    };
                    f.add(bases.value[a], bases.value[b]);
                    originals += 1;
                    if originals >= 2 {
                        if let Some(dec) = f.factors(originals) {
                            let saved = originals - dec.1;
                            let added = dec.4.saturating_sub(originals);
                            let score = (saved, usize::MAX - added);
                            if added <= 12 * saved && added <= credit && score > best_score {
                                best_score = score;
                                best = Some((k + 1, originals, dec));
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
        if let Some((end, old, (terms, n, mut lin, invert, len))) = best {
            for &(a, b, mut ac, mut bc) in &terms[..n] {
                let saved = out.len();
                while ac != 0 {
                    let j = ac.trailing_zeros() as usize;
                    ac &= ac - 1;
                    out.push(small(K::CX, NO_QUBIT, bases.wire[j], bases.wire[a]));
                }
                while bc != 0 {
                    let j = bc.trailing_zeros() as usize;
                    bc &= bc - 1;
                    out.push(small(K::CX, NO_QUBIT, bases.wire[j], bases.wire[b]));
                }
                let changelen = out.len() - saved;
                out.push(small(K::CCX, bases.wire[a], bases.wire[b], t));
                for j in (saved..saved + changelen).rev() {
                    out.push(out[j]);
                }
            }
            if invert {
                out.push(small(K::X, NO_QUBIT, NO_QUBIT, t));
            }
            while lin != 0 {
                let j = lin.trailing_zeros() as usize;
                lin &= lin - 1;
                out.push(small(K::CX, NO_QUBIT, bases.wire[j], t));
            }
            for &g in &input[i..end] {
                if g.kind != K::CCX {
                    out.push(g);
                }
            }
            credit = credit + old - len;
            stats.groups += 1;
            stats.saved += (old - n) as u64;
            stats.added += len as i64 - old as i64;
            stats.max_saving = stats.max_saving.max((old - n) as u64);
            stats.multi += u64::from(old >= 3);
            i = end;
        } else {
            out.push(head);
            i += 1;
        }
    }
}

// The original two-record trailer is held by the caller and needs two slots.
// All positions that could be overwritten have already been copied into base.
pub(super) fn apply(ops: &mut Vec<Op>) -> Counts {
    const BLOCK: usize = 1 << 14;
    let n = ops.len();
    let cap = ops.capacity();
    let ptr = ops.as_ptr();
    let gap = (cap - n)
        .saturating_sub(2)
        .min(n.div_ceil(256))
        .min(1 << 22);
    ops.resize(n + gap, Op::empty());
    if gap != 0 {
        ops.copy_within(0..n, gap);
    }
    let mut original = Vec::with_capacity(BLOCK);
    let mut lowered = Vec::with_capacity(2 * BLOCK);
    let mut stats = Counts::default();
    let mut write = 0;
    for begin in (0..n).step_by(BLOCK) {
        let end = n.min(begin + BLOCK);
        original.clear();
        original.extend_from_slice(&ops[gap + begin..gap + end]);
        lowered.clear();
        let unlocked = (1024 + ((gap as u128) * (end as u128) / (n as u128)) as usize).min(gap);
        let room = begin + unlocked - write;
        lower(&original, &mut lowered, &mut stats, 64, room);
        assert!(write + lowered.len() <= end + unlocked);
        ops[write..write + lowered.len()].copy_from_slice(&lowered);
        write += lowered.len();
    }
    ops.truncate(write);
    assert_eq!((ops.as_ptr(), ops.capacity()), (ptr, cap));
    stats
}
