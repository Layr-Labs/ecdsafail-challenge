//! Second, generalized round of nasqret's exact Toffoli-pair fold (gate_fold.rs, submission 6d94a56a), run in place
//! on the final op vector after the first round. Every rewrite is the same universal permutation identity as in
//! gate_fold.rs; this pass only widens where those identities are looked for:
//!
//! * shifted block origin (patterns straddling a first-round 16,384 boundary become visible);
//! * a longer lookahead;
//! * gates carrying the same explicit classical condition bit fold exactly like unconditional ones (both execute or
//!   neither does; the frame CNOTs and corrections carry that condition). Bit writes, measurements, condition-stack
//!   operations and every other non-X/CX/CCX instruction still stop the search, so the condition bit is constant
//!   over any window the pass rewrites;
//! * the "sandwich" (identical Toffoli B on both sides of one gate G that changes one of B's controls, or reads B's
//!   target) is also found when the two copies of B are separated by further gates that commute with B, on either
//!   side of G: B M1 G M2 B = M1 (B G B) M2 = M1 G C M2.
//!
//! No wire is allocated, no measurement is introduced, nothing depends on any wire value.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};

#[derive(Clone, Copy, Debug)]
pub struct Cfg {
    pub block: usize,
    pub offset: usize,
    pub lookahead: usize,
    pub cond: bool,
    pub wide_sandwich: bool,
    pub growth_divisor: usize,
}

impl Cfg {
    pub const fn production() -> Self {
        Cfg { block: 16_384, offset: 8_192, lookahead: 12, cond: true, wide_sandwich: true, growth_divisor: 128 }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Counts {
    pub equal_pairs: u64,
    pub sandwiches: u64,
    pub wide_sandwiches: u64,
    pub shared_control: u64,
    pub shared_product: u64,
    pub cond_rewrites: u64,
    /// expected Toffoli saved, counting a conditioned CCX as 1/2 (enclosing condition stacks not weighted)
    pub saved_t: f64,
}

fn eligible(op: Op, cfg: &Cfg) -> bool {
    matches!(op.kind, K::X | K::CX | K::CCX) && (cfg.cond || op.c_condition == NO_BIT)
}

fn controls(op: Op, wire: QubitId) -> bool {
    op.q_control1 == wire || op.q_control2 == wire
}

fn commute(a: Op, b: Op) -> bool {
    !controls(a, b.q_target) && !controls(b, a.q_target)
}

fn same_product(a: Op, b: Op) -> bool {
    controls(b, a.q_control1) && controls(b, a.q_control2)
}

fn cx(control: QubitId, target: QubitId, cond: BitId) -> Op {
    Op { kind: K::CX, q_control1: control, q_target: target, c_condition: cond, ..Op::empty() }
}

fn correction(target: QubitId, factors: [QubitId; 3], cond: BitId) -> Option<Op> {
    let mut a = NO_QUBIT;
    let mut b = NO_QUBIT;
    for w in factors {
        if w == NO_QUBIT || w == a || w == b {
            continue;
        }
        if w == target {
            return None;
        }
        if a == NO_QUBIT {
            a = w;
        } else if b == NO_QUBIT {
            b = w;
        } else {
            return None;
        }
    }
    let kind = if b != NO_QUBIT { K::CCX } else if a != NO_QUBIT { K::CX } else { K::X };
    Some(Op { kind, q_target: target, q_control1: a, q_control2: b, c_condition: cond, ..Op::empty() })
}

/// B G B = G C. B's two copies share one condition cb (or none); G has cg. The correction executes exactly when both
/// G and B execute, which is one bit when cb == cg or one of them is unconditional.
fn sandwich(b: Op, g: Op) -> Option<Op> {
    let cond = if b.c_condition == g.c_condition || g.c_condition == NO_BIT {
        b.c_condition
    } else if b.c_condition == NO_BIT {
        g.c_condition
    } else {
        return None;
    };
    let reads_target = controls(g, b.q_target);
    let writes_control = controls(b, g.q_target);
    match (reads_target, writes_control) {
        (false, true) => {
            let other = if b.q_control1 == g.q_target { b.q_control2 } else { b.q_control1 };
            correction(b.q_target, [other, g.q_control1, g.q_control2], cond)
        }
        (true, false) => {
            let other = if g.q_control1 == b.q_target { g.q_control2 } else { g.q_control1 };
            correction(g.q_target, [b.q_control1, b.q_control2, other], cond)
        }
        _ => None,
    }
}

fn w(op: Op) -> f64 {
    if op.kind != K::CCX { 0.0 } else if op.c_condition == NO_BIT { 1.0 } else { 0.5 }
}

fn credit(stats: &mut Counts, a: Op, saved: f64) {
    if a.c_condition != NO_BIT {
        stats.cond_rewrites += 1;
    }
    stats.saved_t += saved;
}

pub fn lower(block: &[Op], mut emit: impl FnMut(Op), stats: &mut Counts, cfg: &Cfg) {
    let mut expansion = block.len() / cfg.growth_divisor;
    let mut i = 0;
    'scan: while i < block.len() {
        let a = block[i];
        if a.kind == K::CCX && eligible(a, cfg) {
            let mut g_at: Option<usize> = None;
            for j in i + 1..block.len().min(i + 1 + cfg.lookahead) {
                let b = block[j];
                if !eligible(b, cfg) {
                    break;
                }
                let twin = b.kind == K::CCX && b.c_condition == a.c_condition;
                if let Some(k) = g_at {
                    if !cfg.wide_sandwich && j != k + 1 {
                        break;
                    }
                    if twin && a.q_target == b.q_target && same_product(a, b) {
                        let g = block[k];
                        if let Some(c) = sandwich(a, g) {
                            for &m in &block[i + 1..k] {
                                emit(m);
                            }
                            emit(g);
                            emit(c);
                            for &m in &block[k + 1..j] {
                                emit(m);
                            }
                            if k == i + 1 && j == i + 2 {
                                stats.sandwiches += 1;
                            } else {
                                stats.wide_sandwiches += 1;
                            }
                            credit(stats, a, 2.0 * w(a) - w(c));
                            i = j + 1;
                            continue 'scan;
                        }
                        break;
                    }
                    if !commute(a, b) {
                        break;
                    }
                    continue;
                }
                if twin {
                    let same_target = a.q_target == b.q_target;
                    let product = same_product(a, b);
                    if same_target && product {
                        for &m in &block[i + 1..j] {
                            emit(m);
                        }
                        stats.equal_pairs += 1;
                        credit(stats, a, 2.0 * w(a));
                        i = j + 1;
                        continue 'scan;
                    }
                    if expansion > 0 {
                        let frame = if product {
                            Some(cx(a.q_target, b.q_target, a.c_condition))
                        } else if same_target {
                            let (shared, left) = if controls(b, a.q_control1) {
                                (a.q_control1, a.q_control2)
                            } else {
                                (a.q_control2, a.q_control1)
                            };
                            if controls(b, shared) {
                                let right = if b.q_control1 == shared { b.q_control2 } else { b.q_control1 };
                                Some(cx(left, right, a.c_condition))
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        if let Some(c) = frame {
                            for &m in &block[i + 1..j] {
                                emit(m);
                            }
                            emit(c);
                            emit(if product { a } else { b });
                            emit(c);
                            if product {
                                stats.shared_product += 1;
                            } else {
                                stats.shared_control += 1;
                            }
                            credit(stats, a, w(a));
                            expansion -= 1;
                            i = j + 1;
                            continue 'scan;
                        }
                    }
                }
                if !commute(a, b) {
                    if (cfg.wide_sandwich || j == i + 1) && j + 1 < block.len() {
                        g_at = Some(j);
                        continue;
                    }
                    break;
                }
            }
        }
        emit(a);
        i += 1;
    }
}

/// One in-place round over the whole vector: blocks of cfg.block ops, the first of cfg.offset ops (when nonzero).
/// The output shares the input's allocation; the write cursor stays behind the read cursor by the proven maximum
/// growth (at most floor(block length / growth_divisor) added ops per block).
pub fn apply_inplace(mut ops: Vec<Op>, cfg: &Cfg, stats: &mut Counts) -> Vec<Op> {
    let raw_len = ops.len();
    let gap = raw_len / cfg.growth_divisor + 2;
    if gap > ops.capacity() - raw_len {
        ops.reserve_exact(gap);
    }
    ops.resize(raw_len + gap, Op::empty());
    ops.copy_within(0..raw_len, gap);
    let mut block: Vec<Op> = Vec::with_capacity(cfg.block.max(cfg.offset) + 1);
    let mut written = 0usize;
    let mut limit = if cfg.offset > 0 { cfg.offset } else { cfg.block };
    for i in 0..raw_len {
        block.push(ops[gap + i]);
        if block.len() >= limit {
            let available = &mut ops[..gap + i + 1];
            lower(&block, |op| {
                available[written] = op;
                written += 1;
            }, stats, cfg);
            block.clear();
            limit = cfg.block;
        }
    }
    lower(&block, |op| {
        ops[written] = op;
        written += 1;
    }, stats, cfg);
    ops.truncate(written);
    ops
}

/// Production entry (FOLD2 knob; "0" disables): up to `rounds` in-place rounds with alternating block origins, stopping
/// at the first round that changes nothing.
pub fn apply(mut ops: Vec<Op>, rounds: usize) -> Vec<Op> {
    for r in 0..rounds {
        let mut cfg = Cfg::production();
        if r % 2 == 1 {
            cfg.offset = 0;
        }
        let mut stats = Counts::default();
        let before = ops.len();
        ops = apply_inplace(ops, &cfg, &mut stats);
        eprintln!("NCT_FOLD2 round={} {:?} before={} after={}", r + 1, stats, before, ops.len());
        if stats.equal_pairs + stats.sandwiches + stats.wide_sandwiches + stats.shared_control + stats.shared_product == 0 {
            break;
        }
    }
    ops
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ccx(a: u64, b: u64, t: u64) -> Op {
        Op { kind: K::CCX, q_control1: QubitId(a), q_control2: QubitId(b), q_target: QubitId(t), ..Op::empty() }
    }
    fn cxo(a: u64, t: u64) -> Op { cx(QubitId(a), QubitId(t), NO_BIT) }
    fn xo(t: u64) -> Op { Op { kind: K::X, q_target: QubitId(t), ..Op::empty() } }
    fn on(mut op: Op, bit: u64) -> Op { op.c_condition = BitId(bit); op }

    // state: 6 qubit bits (0..6) and 2 classical bits (6, 7)
    fn execute(ops: &[Op], mut state: u32) -> u32 {
        for op in ops {
            if op.kind == K::DebugPrint {
                continue;
            }
            op.validate();
            if op.c_condition != NO_BIT && (state >> (6 + op.c_condition.0)) & 1 == 0 {
                continue;
            }
            let bit = |q: QubitId| q == NO_QUBIT || (state >> q.0) & 1 != 0;
            if bit(op.q_control1) && bit(op.q_control2) {
                state ^= 1 << op.q_target.0;
            }
        }
        state
    }

    fn check_all(ops: &[Op], cfg: &Cfg) -> (Vec<Op>, Counts) {
        let mut stats = Counts::default();
        let mut padded = ops.to_vec();
        padded.resize(ops.len().max(cfg.growth_divisor), Op { kind: K::DebugPrint, ..Op::empty() });
        let out = apply_inplace(padded.clone(), cfg, &mut stats);
        for state in 0..256 {
            assert_eq!(execute(&padded, state), execute(&out, state), "{ops:?} -> {out:?}");
        }
        (out, stats)
    }

    #[test]
    fn fold2_exhaustive_random_words() {
        // pseudo-random words over 6 qubits and 2 condition bits, every rewrite checked on all 256 basis states
        let mut s = 0x1234_5678_9abc_def0u64;
        let mut next = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
        let mut total = Counts::default();
        for _ in 0..20_000 {
            let n = 3 + (next() % 10) as usize;
            let mut word = vec![];
            for _ in 0..n {
                let r = next();
                let q = |k: u64| (r >> (8 * k)) % 6;
                let (a, b, t) = (q(1), q(2), q(3));
                let mut op = match r % 7 {
                    0 => xo(t),
                    1 | 2 => if a != t { cxo(a, t) } else { xo(t) },
                    _ => if a != b && a != t && b != t { ccx(a, b, t) } else { xo(t) },
                };
                if (r >> 40) % 3 == 0 {
                    op = on(op, (r >> 44) % 2);
                }
                word.push(op);
            }
            for cfg in [Cfg::production(), Cfg { offset: 0, lookahead: 32, ..Cfg::production() }, Cfg { cond: false, ..Cfg::production() }] {
                let (_, st) = check_all(&word, &cfg);
                total.equal_pairs += st.equal_pairs;
                total.sandwiches += st.sandwiches;
                total.wide_sandwiches += st.wide_sandwiches;
                total.shared_control += st.shared_control;
                total.shared_product += st.shared_product;
                total.cond_rewrites += st.cond_rewrites;
            }
        }
        assert!(total.equal_pairs > 0 && total.sandwiches > 0 && total.wide_sandwiches > 0);
        assert!(total.shared_control > 0 && total.shared_product > 0 && total.cond_rewrites > 0, "{total:?}");
    }

    #[test]
    fn fold2_barriers() {
        let a = ccx(0, 1, 2);
        for kind in [K::CZ, K::Hmr, K::R, K::PushCondition, K::PopCondition, K::BitInvert, K::BitStore0, K::Register, K::CCZ, K::Swap] {
            let marker = Op { kind, ..Op::empty() };
            let word = vec![a, marker, a];
            let mut st = Counts::default();
            assert_eq!(apply_inplace(word.clone(), &Cfg::production(), &mut st), word);
        }
        // different condition bits never pair
        let word = vec![on(a, 0), on(a, 1)];
        let mut st = Counts::default();
        assert_eq!(apply_inplace(word.clone(), &Cfg::production(), &mut st), word);
    }

    #[test]
    fn fold2_wide_sandwich_and_offset_boundary() {
        let a = ccx(0, 1, 2);
        let word = vec![a, cxo(3, 4), cxo(1, 5), xo(1), cxo(4, 3), a];
        let (out, st) = check_all(&word, &Cfg::production());
        assert_eq!(st.wide_sandwiches, 1, "{out:?}");
        let mut split = vec![Op { kind: K::DebugPrint, ..Op::empty() }; 16_383];
        split.extend([a, a]);
        let mut st = Counts::default();
        let out = apply_inplace(split.clone(), &Cfg::production(), &mut st);
        assert_eq!(st.equal_pairs, 1);
        assert_eq!(out.len(), split.len() - 2);
    }
}
