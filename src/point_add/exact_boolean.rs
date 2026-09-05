//! Bounded, forward-only computational-value proofs. No phase gate is removed.
//!
//! Entry contract: registered qubits are arbitrary (also entangled), other wires
//! start at zero, as in Simulator::new. R never proves anything about its INPUT.
//! A clean AND t=a*b can be discharged by HMR(t)->m; CZ(a,b) if m, since
//! (-1)^(m*t) * (-1)^(m*a*b) = 1 on the proven subspace. The target may have
//! controlled other gates or accumulated diagonal phases in the meantime.
//! Only its value and both control versions must be unchanged. No AND/affine
//! relation crosses a source measurement/reset, classical instruction, or
//! conditional operation. Constants on untouched wires remain valid.

use crate::circuit::{analyze_ops, BitId, Op, OperationType as K, QubitOrBit, NO_BIT, NO_QUBIT};

#[path = "exact_boolean_tests.rs"]
mod checks;
pub(super) fn selftest() {
    checks::selftest();
}

const UNKNOWN: u8 = 2;

#[derive(Clone, Copy)]
struct Product {
    controls: [usize; 2],
    versions: [u64; 2],
    epoch: u64,
}

#[derive(Default, Debug)]
pub(super) struct Stats {
    pub constant_toffoli: usize,
    pub alias_toffoli: usize,
    pub measured_ands: usize,
    pub removed_ops: usize,
}

// Exact XORs of at most two opaque value atoms, plus a constant. Overflow is
// forgotten, not truncated. Atoms never assert independence: only syntactically
// equal (or complementary) expressions justify a rewrite. Epochs forbid alias
// proofs across the same barriers as AND products.
#[derive(Clone, Copy)]
struct Affine {
    atoms: [u64; 2],
    len: usize,
    flip: u8,
    epoch: u64,
}

impl Affine {
    fn constant(value: u8, epoch: u64) -> Self {
        Self {
            atoms: [0; 2],
            len: 0,
            flip: value,
            epoch,
        }
    }

    fn xor(self, other: Self) -> Option<Self> {
        let mut atoms = [0; 4];
        let mut len = 0;
        for &a in self.atoms[..self.len]
            .iter()
            .chain(&other.atoms[..other.len])
        {
            if let Some(i) = atoms[..len].iter().position(|b| *b == a) {
                len -= 1;
                atoms[i] = atoms[len];
            } else {
                atoms[len] = a;
                len += 1;
            }
        }
        if len > 2 {
            return None;
        }
        atoms[..len].sort_unstable();
        let mut out = Self::constant(self.flip ^ other.flip, self.epoch);
        out.atoms[..len].copy_from_slice(&atoms[..len]);
        out.len = len;
        Some(out)
    }
}

fn affine_value(
    q: usize,
    values: &[u8],
    aliases: &mut [Option<Affine>],
    epoch: u64,
    next_atom: &mut u64,
) -> Affine {
    if values[q] != UNKNOWN {
        return Affine::constant(values[q], epoch);
    }
    if let Some(a) = aliases[q].filter(|a| a.epoch == epoch) {
        return a;
    }
    *next_atom = next_atom.checked_add(1).expect("affine atom exhausted");
    let a = Affine {
        atoms: [*next_atom, 0],
        len: 1,
        flip: 0,
        epoch,
    };
    aliases[q] = Some(a);
    a
}

fn xor(a: u8, b: u8) -> u8 {
    if a == UNKNOWN || b == UNKNOWN {
        UNKNOWN
    } else {
        a ^ b
    }
}

/// `visit` sees each original operation and its replacement, for LOCAL paired
/// diagnostics. Production uses a no-op closure; no per-operation trace is kept.
fn transform(
    ops: Vec<Op>,
    use_aliases: bool,
    mut visit: impl FnMut(&Op, &[Op]),
) -> (Vec<Op>, Stats) {
    // The builder can declare public inputs at the END. Scan all metadata
    // before proving any entry constants; never treat those wires as scratch.
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let mut values = vec![0; nq as usize];
    for wire in regs.into_iter().flatten() {
        if let QubitOrBit::Qubit(q) = wire {
            values[q.0 as usize] = UNKNOWN;
        }
    }
    let mut versions = vec![0u64; values.len()];
    let mut products = vec![None::<Product>; values.len()];
    let mut aliases = vec![None::<Affine>; values.len()];
    let mut next_atom = 0;
    let mut epoch = 0u64;
    let mut depth = 0usize;
    let mut next_bit = nb;
    let mut output = Vec::with_capacity(ops.len());
    let mut stats = Stats::default();
    for source in ops {
        let start = output.len();
        let mut op = source;
        let conditional = depth != 0 || op.c_condition != NO_BIT;
        if conditional
            || matches!(
                op.kind,
                K::PushCondition
                    | K::PopCondition
                    | K::R
                    | K::Hmr
                    | K::BitInvert
                    | K::BitStore0
                    | K::BitStore1
            )
        {
            epoch += 1;
        }
        match op.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth = depth.checked_sub(1).expect("unbalanced conditions"),
            _ => {}
        }
        let mut removed = false;
        if !conditional && matches!(op.kind, K::CX | K::CCX) {
            let a = values[op.q_control1.0 as usize];
            let b = if op.kind == K::CCX {
                values[op.q_control2.0 as usize]
            } else {
                1
            };
            if a == 0 || b == 0 {
                removed = true;
            } else {
                if op.kind == K::CCX && (a == 1 || b == 1) {
                    op.kind = K::CX;
                    if a == 1 {
                        op.q_control1 = op.q_control2;
                    }
                    op.q_control2 = NO_QUBIT;
                }
                if op.kind == K::CX && values[op.q_control1.0 as usize] == 1 {
                    op.kind = K::X;
                    op.q_control1 = NO_QUBIT;
                }
            }
            if source.kind == K::CCX && (removed || op.kind != K::CCX) {
                stats.constant_toffoli += 1;
            }
            if use_aliases && !removed && op.kind == K::CCX {
                let a = affine_value(
                    op.q_control1.0 as usize,
                    &values,
                    &mut aliases,
                    epoch,
                    &mut next_atom,
                );
                let b = affine_value(
                    op.q_control2.0 as usize,
                    &values,
                    &mut aliases,
                    epoch,
                    &mut next_atom,
                );
                if a.len == b.len && a.atoms == b.atoms {
                    if a.flip == b.flip {
                        op.kind = K::CX;
                        op.q_control2 = NO_QUBIT;
                    } else {
                        removed = true;
                    }
                    stats.alias_toffoli += 1;
                }
            }
        }
        match op.kind {
            K::X | K::CX | K::CCX => {
                let t = op.q_target.0 as usize;
                let old_product = products[t].take();
                versions[t] += 1;
                if removed {
                    stats.removed_ops += 1;
                } else if conditional {
                    values[t] = UNKNOWN;
                    aliases[t] = None;
                } else if op.kind == K::CCX {
                    aliases[t] = None;
                    let a = op.q_control1.0 as usize;
                    let b = op.q_control2.0 as usize;
                    let controls = [a.min(b), a.max(b)];
                    let cv = controls.map(|q| versions[q]);
                    if old_product.is_some_and(|p| {
                        p.epoch == epoch && p.controls == controls && p.versions == cv
                    }) {
                        let bit = BitId(next_bit);
                        next_bit = next_bit
                            .checked_add(1)
                            .filter(|b| *b != NO_BIT.0)
                            .expect("classical bit ID exhausted");
                        let mut hmr = Op::empty();
                        hmr.kind = K::Hmr;
                        hmr.q_target = op.q_target;
                        hmr.c_target = bit;
                        let mut fix = Op::empty();
                        fix.kind = K::CZ;
                        fix.q_control1 = op.q_control1;
                        fix.q_target = op.q_control2;
                        fix.c_condition = bit;
                        output.extend([hmr, fix]);
                        values[t] = 0;
                        stats.measured_ands += 1;
                        // This inserted, corrected measurement is an exact local
                        // identity on all other values, unlike a source HMR/R.
                        removed = true;
                    } else {
                        if values[t] == 0 {
                            products[t] = Some(Product {
                                controls,
                                versions: cv,
                                epoch,
                            });
                        }
                        values[t] = UNKNOWN;
                    }
                } else {
                    let expression = if use_aliases {
                        let before = affine_value(t, &values, &mut aliases, epoch, &mut next_atom);
                        let delta = if op.kind == K::X {
                            Affine::constant(1, epoch)
                        } else {
                            affine_value(
                                op.q_control1.0 as usize,
                                &values,
                                &mut aliases,
                                epoch,
                                &mut next_atom,
                            )
                        };
                        before.xor(delta)
                    } else {
                        None
                    };
                    let delta = if op.kind == K::X {
                        1
                    } else {
                        values[op.q_control1.0 as usize]
                    };
                    values[t] = xor(values[t], delta);
                    if let Some(a) = expression.filter(|a| a.len == 0) {
                        values[t] = a.flip;
                    }
                    aliases[t] = expression;
                }
            }
            K::Swap => {
                let a = op.q_control1.0 as usize;
                let b = op.q_target.0 as usize;
                products[a] = None;
                products[b] = None;
                versions[a] += 1;
                versions[b] += 1;
                if conditional {
                    values[a] = UNKNOWN;
                    values[b] = UNKNOWN;
                    aliases[a] = None;
                    aliases[b] = None;
                } else {
                    values.swap(a, b);
                    aliases.swap(a, b);
                }
            }
            K::R | K::Hmr => {
                let t = op.q_target.0 as usize;
                versions[t] += 1;
                products[t] = None;
                aliases[t] = None;
                values[t] = if conditional { UNKNOWN } else { 0 };
            }
            // In particular, never fold Z/CZ/CCZ to nothing or lose a NEG
            // condition, even if all the involved values happen to be constant.
            K::Z
            | K::CZ
            | K::CCZ
            | K::Neg
            | K::BitInvert
            | K::BitStore0
            | K::BitStore1
            | K::PushCondition
            | K::PopCondition
            | K::Register
            | K::AppendToRegister
            | K::DebugPrint => {}
        }
        if !removed {
            output.push(op);
        }
        visit(&source, &output[start..]);
    }
    assert_eq!(depth, 0, "unbalanced conditions");
    (output, stats)
}

pub(super) fn simplify(ops: Vec<Op>) -> Vec<Op> {
    let aliases = std::env::var("MIDQ_EXACT_BOOLEAN_ALIASES").ok().as_deref() == Some("1");
    if std::env::var("MIDQ_EXACT_BOOLEAN_PROFILE").ok().as_deref() == Some("1") {
        return checks::profile(ops, aliases);
    }
    let (output, stats) = transform(ops, aliases, |_, _| {});
    eprintln!("MIDQ_EXACT_BOOLEAN {stats:?}");
    output
}
