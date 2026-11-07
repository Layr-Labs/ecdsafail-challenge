//! Exact local rewrites of well-formed, unconditional X, CX and CCX gates on arbitrary wires.
//! All other instructions split the search. An enclosing classical condition is
//! preserved because no rewrite crosses a stack operation.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};

const BLOCK: usize = 16_384;
const LOOKAHEAD: usize = 12;
const GROWTH_DIVISOR: usize = 128;

#[derive(Default, Debug)]
pub(super) struct Counts {
    pub(super) equal_pairs: u64,
    pub(super) sandwiches: u64,
    pub(super) shared_control: u64,
    pub(super) shared_product: u64,
    pub(super) saved_ccx: u64,
}

fn plain(op: Op) -> bool {
    op.c_condition == NO_BIT && matches!(op.kind, K::X | K::CX | K::CCX)
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

fn cx(control: QubitId, target: QubitId) -> Op {
    Op {
        kind: K::CX,
        q_control1: control,
        q_target: target,
        ..Op::empty()
    }
}

// Append the distinct factors of a Boolean monomial. A third distinct
// factor would need a gate outside this pass's alphabet.
fn correction(target: QubitId, factors: [QubitId; 3]) -> Option<Op> {
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
    let kind = if b != NO_QUBIT {
        K::CCX
    } else if a != NO_QUBIT {
        K::CX
    } else {
        K::X
    };
    Some(Op {
        kind,
        q_target: target,
        q_control1: a,
        q_control2: b,
        ..Op::empty()
    })
}

// Conjugate G by an identical Toffoli on each side. The one-way dependency
// adds the Boolean finite difference of G's target update. A dependency in
// both directions, or a three-factor correction, stays untouched.
fn sandwich(b: Op, g: Op) -> Option<Op> {
    let reads_target = controls(g, b.q_target);
    let writes_control = controls(b, g.q_target);
    match (reads_target, writes_control) {
        (false, true) => {
            let other = if b.q_control1 == g.q_target {
                b.q_control2
            } else {
                b.q_control1
            };
            correction(b.q_target, [other, g.q_control1, g.q_control2])
        }
        (true, false) => {
            let other = if g.q_control1 == b.q_target {
                g.q_control2
            } else {
                g.q_control1
            };
            correction(g.q_target, [b.q_control1, b.q_control2, other])
        }
        _ => None,
    }
}

// Move the *original* first Toffoli right through commuting middle gates.
// Its replacement is emitted only after the entire middle has been emitted.
pub(super) fn lower(block: &[Op], mut emit: impl FnMut(Op), stats: &mut Counts) {
    let mut expansion = block.len() / GROWTH_DIVISOR;
    let mut i = 0;
    'scan: while i < block.len() {
        let a = block[i];
        if a.kind == K::CCX && plain(a) {
            if i + 2 < block.len() {
                let g = block[i + 1];
                let b = block[i + 2];
                if plain(g)
                    && b.kind == K::CCX
                    && plain(b)
                    && a.q_target == b.q_target
                    && same_product(a, b)
                {
                    if let Some(c) = sandwich(a, g) {
                        emit(g);
                        emit(c);
                        stats.sandwiches += 1;
                        stats.saved_ccx += 2 - u64::from(c.kind == K::CCX);
                        i += 3;
                        continue;
                    }
                }
            }
            for j in i + 1..block.len().min(i + 1 + LOOKAHEAD) {
                let b = block[j];
                if !plain(b) {
                    break;
                }
                if b.kind == K::CCX {
                    let same_target = a.q_target == b.q_target;
                    let product = same_product(a, b);
                    if same_target && product {
                        for &middle in &block[i + 1..j] {
                            emit(middle);
                        }
                        stats.equal_pairs += 1;
                        stats.saved_ccx += 2;
                        i = j + 1;
                        continue 'scan;
                    }
                    if expansion > 0 {
                        let frame = if product {
                            Some(cx(a.q_target, b.q_target))
                        } else if same_target {
                            let (shared, left) = if controls(b, a.q_control1) {
                                (a.q_control1, a.q_control2)
                            } else {
                                (a.q_control2, a.q_control1)
                            };
                            if controls(b, shared) {
                                let right = if b.q_control1 == shared {
                                    b.q_control2
                                } else {
                                    b.q_control1
                                };
                                Some(cx(left, right))
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        if let Some(c) = frame {
                            for &middle in &block[i + 1..j] {
                                emit(middle);
                            }
                            emit(c);
                            emit(if product { a } else { b });
                            emit(c);
                            if product {
                                stats.shared_product += 1;
                            } else {
                                stats.shared_control += 1;
                            }
                            stats.saved_ccx += 1;
                            expansion -= 1;
                            i = j + 1;
                            continue 'scan;
                        }
                    }
                }
                if !commute(a, b) {
                    break;
                }
            }
        }
        emit(a);
        i += 1;
    }
}

pub(super) struct Folder {
    block: Vec<Op>,
    output: Vec<Op>,
    stats: Counts,
}

impl Folder {
    pub(super) fn new(input_len: usize) -> Self {
        Self {
            block: Vec::with_capacity(BLOCK),
            output: Vec::with_capacity(input_len + input_len / GROWTH_DIVISOR),
            stats: Counts::default(),
        }
    }

    pub(super) fn push(&mut self, op: Op) {
        self.block.push(op);
        if self.block.len() == BLOCK {
            self.flush();
        }
    }

    fn flush(&mut self) {
        let output = &mut self.output;
        lower(&self.block, |op| output.push(op), &mut self.stats);
        self.block.clear();
    }

    pub(super) fn finish(mut self) -> Vec<Op> {
        self.flush();
        eprintln!("NCT_FOLD {:?}", self.stats);
        self.output
    }
}

pub(super) fn apply(ops: Vec<Op>) -> Vec<Op> {
    let mut folder = Folder::new(ops.len());
    for op in ops {
        folder.push(op);
    }
    folder.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ccx(a: u64, b: u64, t: u64) -> Op {
        Op {
            kind: K::CCX,
            q_control1: QubitId(a),
            q_control2: QubitId(b),
            q_target: QubitId(t),
            ..Op::empty()
        }
    }

    fn execute(ops: &[Op], mut state: u32) -> u32 {
        for op in ops {
            if op.kind == K::DebugPrint {
                continue;
            }
            op.validate();
            let bit = |q: QubitId| q == NO_QUBIT || (state >> q.0) & 1 != 0;
            if bit(op.q_control1) && bit(op.q_control2) {
                state ^= 1 << op.q_target.0;
            }
        }
        state
    }

    #[test]
    fn q660_fold_both_control_orders_and_corridors() {
        let a = ccx(0, 1, 2);
        let gap = cx(QubitId(1), QubitId(4));
        let cases = [
            (vec![a, gap, ccx(1, 0, 2)], 2),
            (vec![a, gap, ccx(3, 1, 2)], 1),
            (vec![a, gap, ccx(1, 0, 3)], 1),
            (vec![a, cx(QubitId(3), QubitId(1)), ccx(1, 0, 2)], 1),
            (vec![a, cx(QubitId(0), QubitId(1)), ccx(1, 0, 2)], 2),
            (vec![a, cx(QubitId(2), QubitId(3)), ccx(1, 0, 2)], 1),
            (vec![a, cx(QubitId(2), QubitId(0)), ccx(1, 0, 2)], 0),
        ];
        for (mut ops, saving) in cases {
            ops.resize(
                GROWTH_DIVISOR,
                Op {
                    kind: K::DebugPrint,
                    ..Op::empty()
                },
            );
            let before = ops.iter().filter(|op| op.kind == K::CCX).count();
            let out = apply(ops.clone());
            let after = out.iter().filter(|op| op.kind == K::CCX).count();
            assert_eq!(before - after, saving);
            for state in 0..32 {
                assert_eq!(execute(&ops, state), execute(&out, state));
            }
        }
    }

    #[test]
    fn q660_fold_barriers_and_block_boundary() {
        let a = ccx(0, 1, 2);
        for kind in [
            K::CZ,
            K::Hmr,
            K::R,
            K::PushCondition,
            K::PopCondition,
            K::BitInvert,
            K::Register,
            K::CCZ,
            K::Swap,
        ] {
            let marker = Op {
                kind,
                ..Op::empty()
            };
            let word = vec![a, marker, a];
            assert_eq!(apply(word.clone()), word);
        }
        let guarded = Op {
            c_condition: crate::circuit::BitId(5),
            ..a
        };
        assert_eq!(apply(vec![guarded, guarded]), vec![guarded, guarded]);
        let mut split = vec![
            Op {
                kind: K::DebugPrint,
                ..Op::empty()
            };
            BLOCK - 1
        ];
        split.extend([a, a]);
        assert_eq!(apply(split.clone()), split);
    }
}
