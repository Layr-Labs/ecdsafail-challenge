use super::{State, Value};
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
#[derive(Clone, Copy, Debug)]
pub(crate) struct Witness {
    pub(crate) sign: bool,
    pub(crate) count: usize,
    pub(crate) donor: [QubitId; 3],
}
impl Witness {
    fn new(sign: bool) -> Self {
        Self {
            sign,
            count: 0,
            donor: [NO_QUBIT; 3],
        }
    }
    fn append(&mut self, q: QubitId, complement: bool) -> bool {
        if self.count == 3 || self.donor[..self.count].contains(&q) {
            return false;
        }
        self.donor[self.count] = q;
        self.count += 1;
        self.sign ^= complement;
        true
    }
    pub(crate) fn replace(self, g: Op, bit: BitId, mut emit: impl FnMut(Op)) {
        assert!(g.kind == K::CCX && g.c_condition == NO_BIT);
        emit(Op {
            kind: K::Hmr,
            q_target: g.q_target,
            c_target: bit,
            ..Op::empty()
        });
        emit(Op {
            kind: K::CZ,
            q_control1: g.q_control1,
            q_target: g.q_control2,
            c_condition: bit,
            ..Op::empty()
        });
        if self.sign {
            emit(Op {
                kind: K::Neg,
                c_condition: bit,
                ..Op::empty()
            });
            emit(Op {
                kind: K::X,
                q_target: g.q_target,
                ..Op::empty()
            });
        }
        for &donor in &self.donor[..self.count] {
            assert_ne!(donor, g.q_target);
            emit(Op {
                kind: K::Z,
                q_target: donor,
                c_condition: bit,
                ..Op::empty()
            });
            emit(Op {
                kind: K::CX,
                q_control1: donor,
                q_target: g.q_target,
                ..Op::empty()
            });
        }
        emit(Op {
            kind: K::BitStore0,
            c_target: bit,
            ..Op::empty()
        });
    }
}
impl<const N: usize> State<N> {
    fn holder(&self, v: Value, omit: usize) -> Option<(QubitId, bool)> {
        for inv in [false, true] {
            if let Some(q) = self.witness(v ^ u64::from(inv), omit) {
                return Some((q, inv));
            }
        }
        None
    }
    pub(crate) fn computed_target(&mut self, g: Op) -> Option<Witness> {
        if g.kind != K::CCX || g.c_condition != NO_BIT || !self.stack.is_empty() {
            return None;
        }
        let target = g.q_target.0 as usize;
        let (a, b) = (
            self.q[g.q_control1.0 as usize],
            self.q[g.q_control2.0 as usize],
        );
        let product = self.v.and(a, b);
        if product < 2 {
            return None;
        }
        let post = self.v.xor(self.q[target], product);
        if post <= 1 {
            return Some(Witness::new(post == 1));
        }
        if let Some((q, neg)) = self.holder(post, target) {
            let mut out = Witness::new(false);
            out.append(q, neg);
            return Some(out);
        }
        let canonical = self.v.support(post & !1);
        if canonical.len >= 2 && canonical.len <= 3 {
            let mut out = Witness::new(post & 1 != 0);
            for &name in &canonical.terms[..canonical.len] {
                let Some((q, neg)) = self.holder(name, target) else {
                    break;
                };
                if !out.append(q, neg) {
                    break;
                }
            }
            if out.count == canonical.len {
                return Some(out);
            }
        }
        // Specifically query decompositions relative to the original controls.
        for q in [g.q_control1, g.q_control2] {
            let v = self.q[q.0 as usize];
            let rest = self.v.xor(post, v);
            if let Some((donor, neg)) = self.holder(rest, target) {
                let mut out = Witness::new(false);
                if out.append(q, false) && out.append(donor, neg) {
                    return Some(out);
                }
            }
        }
        None
    }
}

#[derive(Debug, Default)]
pub(crate) struct Counts {
    pub(crate) source: usize,
    pub(crate) output: usize,
    pub(crate) private_bit: u64,
    pub(crate) extra_capacity: usize,
    pub(crate) measured: u64,
    pub(crate) limited: u64,
    pub(crate) direct_fixed: u64,
    pub(crate) direct_guarded_raw: u64,
    pub(crate) by_donors_and_sign: [u64; 8],
}
/// For HMR(t,m), a basis branch picks up (-1)^(m*t) and t becomes zero.
/// If t = a*b + L before the original CCX, the required new target is L.
/// Correct the phase with measured CZ(a,b) and the signed affine form L,
/// then write L with only X/CX and clear the private classical bit.
pub(crate) fn apply(ops: &mut Vec<Op>) -> Counts {
    const BLOCK: usize = 1 << 14;
    let n = ops.len();
    let cap = ops.capacity();
    let ptr = ops.as_ptr();
    let mut facts = State::<96>::new(ops, 65536, true);
    facts.enable_retention();
    let scratch = BitId(facts.bits.len() as u64);
    let gap = (cap - n).saturating_sub(2).min(n.div_ceil(32)).min(1 << 25);
    let mut result = Counts {
        source: n,
        extra_capacity: gap,
        private_bit: scratch.0,
        ..Default::default()
    };
    let mut ordinary = super::Counts::default();
    ops.resize(n + gap, Op::empty());
    if gap != 0 {
        ops.copy_within(0..n, gap);
    }
    let mut write = 0;
    for begin in (0..n).step_by(BLOCK) {
        let end = (begin + BLOCK).min(n);
        let unlocked = (1024 + ((gap as u128) * (end as u128) / (n as u128)) as usize).min(gap);
        for i in begin..end {
            let gate = ops[gap + i];
            let witness = facts.computed_target(gate);
            // Keep logical state synchronized with the original reachable values.
            // The private measurement bit is restored after every replacement.
            let simple = facts.step(gate, &mut ordinary);
            if simple != Some(gate) {
                if let Some(out) = simple {
                    ops[write] = out;
                    write += 1;
                }
            } else if let Some(w) = witness {
                let length = 3 + 2 * w.count + 2 * usize::from(w.sign);
                if write + length <= i + 1 + unlocked {
                    w.replace(gate, scratch, |out| {
                        ops[write] = out;
                        write += 1;
                    });
                    result.measured += 1;
                    result.by_donors_and_sign[2 * w.count + usize::from(w.sign)] += 1;
                } else {
                    result.limited += 1;
                    ops[write] = gate;
                    write += 1;
                }
            } else {
                ops[write] = gate;
                write += 1;
            }
        }
    }
    ops.truncate(write);
    assert_eq!((ptr, cap), (ops.as_ptr(), ops.capacity()));
    result.output = write;
    result.direct_fixed = ordinary.unconditional;
    result.direct_guarded_raw = ordinary.conditional;
    result
}
