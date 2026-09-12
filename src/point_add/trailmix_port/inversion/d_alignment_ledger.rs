//! Diagnostic-only, complete local-iteration cost ledger. No driver dispatch.
use super::*;
use crate::circuit::{Op, NO_BIT};
use std::collections::BTreeMap;

#[derive(Clone, Default)]
struct Guard {
    terms: BTreeMap<usize, bool>,
    impossible: bool,
}
#[derive(Clone)]
enum BitValue {
    Constant(bool),
    Random(usize, bool),
}
#[derive(Clone)]
struct Defined {
    value: BitValue,
    domain: Guard,
}
impl Guard {
    fn implies(&self, other: &Guard) -> bool {
        self.impossible
            || (!other.impossible
                && other
                    .terms
                    .iter()
                    .all(|(k, v)| self.terms.get(k) == Some(v)))
    }
    fn constrain(&mut self, value: &BitValue) {
        match value {
            BitValue::Constant(false) => self.impossible = true,
            BitValue::Constant(true) => {}
            BitValue::Random(id, positive) => {
                if self
                    .terms
                    .insert(*id, *positive)
                    .is_some_and(|old| old != *positive)
                {
                    self.impossible = true;
                }
            }
        }
    }
    fn probability(&self) -> f64 {
        if self.impossible {
            0.0
        } else {
            2f64.powi(-(self.terms.len() as i32))
        }
    }
}

/// Exact expectation of this unoptimized stream's CLASSICAL execution masks.
/// Each HMR defines a fresh independent outcome. Conditional definitions can
/// only be read where their write guard is implied; otherwise return an error.
/// No independent-quantum-control or compiler-saving assumption is made.
pub(super) fn expectations(ops: &[Op]) -> Result<Vec<f64>, String> {
    let mut bits: BTreeMap<u64, Defined> = BTreeMap::new();
    let mut stack = vec![Guard::default()];
    let mut next = 0;
    let mut costs = vec![0.0; ops.len()];
    let read =
        |id: u64, guard: &Guard, bits: &BTreeMap<u64, Defined>| -> Result<BitValue, String> {
            match bits.get(&id) {
                None => Ok(BitValue::Constant(false)),
                Some(v) if guard.implies(&v.domain) => Ok(v.value.clone()),
                Some(_) => Err(format!(
                    "classical bit{id} read outside its conditional-definition domain"
                )),
            }
        };
    for (i, op) in ops.iter().enumerate() {
        if op.kind == OperationType::PopCondition {
            stack.pop().ok_or("empty condition stack")?;
            continue;
        }
        let mut guard = stack.last().ok_or("missing outer guard")?.clone();
        if op.c_condition != NO_BIT {
            let value = read(op.c_condition.0, &guard, &bits).map_err(|s| format!("op{i}: {s}"))?;
            guard.constrain(&value);
        }
        if op.kind == OperationType::PushCondition {
            stack.push(guard);
            continue;
        }
        if guard.impossible {
            continue;
        }
        match op.kind {
            OperationType::CCX | OperationType::CCZ => costs[i] = guard.probability(),
            OperationType::Hmr => {
                bits.insert(
                    op.c_target.0,
                    Defined {
                        value: BitValue::Random(next, true),
                        domain: guard,
                    },
                );
                next += 1;
            }
            OperationType::BitStore0 | OperationType::BitStore1 => {
                bits.insert(
                    op.c_target.0,
                    Defined {
                        value: BitValue::Constant(op.kind == OperationType::BitStore1),
                        domain: guard,
                    },
                );
            }
            OperationType::BitInvert => {
                let value = match read(op.c_target.0, &guard, &bits)? {
                    BitValue::Constant(v) => BitValue::Constant(!v),
                    BitValue::Random(i, p) => BitValue::Random(i, !p),
                };
                bits.insert(
                    op.c_target.0,
                    Defined {
                        value,
                        domain: guard,
                    },
                );
            }
            _ => {}
        }
    }
    if stack.len() != 1 {
        return Err("unbalanced condition stack".into());
    }
    Ok(costs)
}

fn expectation_checks() {
    use crate::circuit::BitId;
    let op = |kind, target, condition| {
        let mut op = Op::empty();
        op.kind = kind;
        op.c_target = BitId(target);
        op.c_condition = if condition == u64::MAX {
            NO_BIT
        } else {
            BitId(condition)
        };
        op
    };
    let h = op(OperationType::Hmr, 0, u64::MAX);
    let push = op(OperationType::PushCondition, 0, 0);
    let pop = op(OperationType::PopCondition, 0, u64::MAX);
    let t = op(OperationType::CCX, 0, u64::MAX);
    assert_eq!(
        expectations(&[h, push, push, t, pop, pop])
            .unwrap()
            .iter()
            .sum::<f64>(),
        0.5
    );
    let invert = op(OperationType::BitInvert, 0, u64::MAX);
    assert_eq!(
        expectations(&[h, push, invert, push, t, pop, pop])
            .unwrap()
            .iter()
            .sum::<f64>(),
        0.0
    );
    let h1 = op(OperationType::Hmr, 1, u64::MAX);
    let t1 = op(OperationType::CCX, 0, 1);
    assert!(expectations(&[h, push, h1, pop, t1]).is_err());
}

struct Stage {
    label: &'static str,
    start: usize,
    end: usize,
    peak: u32,
}
fn stage(
    c: &mut Circuit,
    stages: &mut Vec<Stage>,
    label: &'static str,
    body: impl FnOnce(&mut Circuit),
) {
    c.flush_pending_frees();
    let start = c.b.ops.len();
    // Host-only phase peak observation; backend admission reads active_qubits.
    let saved = (c.b.peak_qubits, c.b.peak_phase, c.b.peak_ops_idx);
    c.b.peak_qubits = c.b.active_qubits;
    body(c);
    c.flush_pending_frees();
    let peak = c.b.peak_qubits;
    if saved.0 > peak {
        c.b.peak_qubits = saved.0;
        c.b.peak_phase = saved.1;
        c.b.peak_ops_idx = saved.2;
    }
    stages.push(Stage {
        label,
        start,
        end: c.b.ops.len(),
        peak,
    });
}

fn rb(ceiling: usize) -> usize {
    (usize::BITS - ceiling.max(1).leading_zeros()) as usize
}

// Exact body of retained_division::add_update, with its existing budget rules.
fn update(c: &mut Circuit, gate: &QReg, a: &[QReg], b: &[QReg], subtract: bool) {
    use crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_hybrid_add_refs;
    use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{ctrl_add, ctrl_sub};
    let ar: Vec<_> = a.iter().collect();
    let br: Vec<_> = b.iter().collect();
    let budget = env_usize("MIDQ_PZ_VENT_QCAP", 0);
    if budget != 0 {
        let vents = budget.saturating_sub(c.b.active_qubits as usize);
        if subtract {
            for q in a {
                c.x(q);
            }
        }
        controlled_hybrid_add_refs(c, gate, &ar, &br, vents);
        if subtract {
            for q in a {
                c.x(q);
            }
        }
    } else if subtract {
        ctrl_sub(c, gate, &ar, &br);
    } else {
        ctrl_add(c, gate, &ar, &br);
    }
}

fn framed_swap(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    counter: &[QReg],
    parity: &QReg,
    role: &QReg,
) {
    let source = if prefix_popcount::enabled(counter) {
        &counter[..prefix_popcount::BITS]
    } else {
        q
    };
    let zero = c.alloc_qreg("d_align.swap.qzero");
    or_is_zero(c, source, &zero);
    for (a, b) in a.iter().zip(b) {
        c.cswap(&zero, a, b);
    }
    for (a, b) in ca.iter().zip(cb) {
        c.cswap(&zero, a, b);
    }
    c.cx(&zero, parity);
    c.cx(&zero, role);
    clear_zero_predicate(c, source, &zero, false);
    c.zero_and_free(zero);
}

fn emit(step: usize, new: bool, inverse: bool, boundary: bool) {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{
        reg_los, reg_widths, shift_bounds,
    };
    let (wa, wb, wca, wcb, wq) = reg_widths(step);
    let n = trailmix_ab_width(wa.max(wb));
    let m = trailmix_cacb_width(wca.max(wcb));
    let (pa, pb, _, _, _) = reg_widths(step.saturating_sub(1));
    let v = n.max(trailmix_ab_width(pa.max(pb)));
    let qwidth = trailmix_q_width_step(wq, wa, wb, wca, wcb);
    assert_eq!(qwidth, 32);
    let (_, _, lca, lcb, _) = reg_los(step);
    let (_, sm) = shift_bounds(step);
    let physical = if new && !inverse && !boundary { v } else { n };
    let mut c = Circuit::new();
    assert!(!c.b.count_only);
    let _passenger = c.alloc_qreg_bits("ledger.external", 256);
    let _sgn = c.alloc_qreg("ledger.sgn");
    let carry = c.alloc_qreg("ledger.borrowed_carry");
    let mut a = c.alloc_qreg_bits("ledger.A", physical);
    let mut b = c.alloc_qreg_bits("ledger.B", physical);
    let ca = c.alloc_qreg_bits("ledger.ca", m);
    let cb = c.alloc_qreg_bits("ledger.cb", m);
    let q = c.alloc_qreg_bits("ledger.q", qwidth);
    let counter = c.alloc_qreg_bits("ledger.counter", trailmix_counter_width());
    let parity = c.alloc_qreg("ledger.parity");
    let srot = c.alloc_qreg_bits("ledger.srot", trailmix_srot_width());
    let offset = c.alloc_qreg("ledger.offset");
    let phi = new.then(|| c.alloc_qreg_bits("ledger.phi", 5));
    let role = new.then(|| c.alloc_qreg("ledger.role"));
    let input_floor = c.b.active_qubits;
    let mut stages = Vec::new();
    if !new {
        stage(&mut c, &mut stages, "original_M_D_swap", |c| {
            shrunken_pz_pass_step(
                c,
                &a,
                &b,
                &ca,
                &cb,
                &q,
                &counter,
                &parity,
                &srot,
                &offset,
                Some(&carry),
                step,
                inverse,
            )
        });
    } else {
        let phi = phi.as_ref().unwrap();
        let role = role.as_ref().unwrap();
        if boundary {
            stage(&mut c, &mut stages, "cut_frame_conversion", |c| {
                let car: Vec<_> = ca.iter().collect();
                let cbr: Vec<_> = cb.iter().collect();
                if inverse {
                    borrow_compare_refs(c, &car, &cbr, role);
                    d_alignment_prep::frame_xor(c, &q, role, phi);
                    rotate_left(c, &b, phi);
                } else {
                    rotate_right(c, &b, phi);
                    d_alignment_prep::frame_xor(c, &q, role, phi);
                    clear_borrow_compare_refs(c, &car, &cbr, role);
                }
            });
        } else if !inverse {
            stage(&mut c, &mut stages, "PREP_forward", |c| {
                d_alignment_prep::apply_profile(
                    c, &a, &b, &ca, &cb, &q, phi, role, &srot, &offset, false,
                )
            });
            stage(&mut c, &mut stages, "release_old_high_lanes", |c| {
                shrunken_pz_resize(c, &mut a, n, "A");
                shrunken_pz_resize(c, &mut b, n, "B");
            });
            let active = compute_active(&mut c, &[]);
            stage(&mut c, &mut stages, "popcount_and_unchanged_M", |c| {
                if prefix_popcount::enabled(&counter) {
                    prefix_popcount::update(c, &counter, role, &active, false);
                }
                let gate = HybridGateControl::new(&active, role);
                multiply_substep_windowed(
                    c,
                    &ca,
                    &cb,
                    &q,
                    &srot,
                    &offset,
                    GateControl::Hybrid(&gate),
                    Some(&carry),
                    lca,
                    lcb,
                    rb(sm),
                );
                gate.release(c);
            });
            c.x(role);
            stage(&mut c, &mut stages, "aligned_D", |c| {
                let gate = HybridGateControl::new(&active, role);
                with_gate_control(c, GateControl::Hybrid(&gate), |c, g| {
                    update(c, g, &a, &b, true);
                    set_bit_at_s_gated(c, &q, phi, g);
                });
                gate.release(c);
            });
            stage(&mut c, &mut stages, "qzero_swap_and_R_flip", |c| {
                framed_swap(c, &a, &b, &ca, &cb, &q, &counter, &parity, role)
            });
            uncompute_active(&mut c, &[], &active);
            c.zero_and_free(active);
        } else {
            stage(&mut c, &mut stages, "undo_qzero_swap_and_R_flip", |c| {
                framed_swap(c, &a, &b, &ca, &cb, &q, &counter, &parity, role)
            });
            let active = compute_active(&mut c, &[]);
            stage(&mut c, &mut stages, "inverse_aligned_D", |c| {
                let gate = HybridGateControl::new(&active, role);
                with_gate_control(c, GateControl::Hybrid(&gate), |c, g| {
                    set_bit_at_s_gated(c, &q, phi, g);
                    update(c, g, &a, &b, false);
                });
                gate.release(c);
            });
            c.x(role);
            stage(
                &mut c,
                &mut stages,
                "inverse_unchanged_M_and_popcount",
                |c| {
                    let gate = HybridGateControl::new(&active, role);
                    multiply_substep_windowed_inv(
                        c,
                        &ca,
                        &cb,
                        &q,
                        &srot,
                        &offset,
                        GateControl::Hybrid(&gate),
                        Some(&carry),
                        lca,
                        lcb,
                        rb(sm),
                    );
                    gate.release(c);
                    if prefix_popcount::enabled(&counter) {
                        prefix_popcount::update(c, &counter, role, &active, true);
                    }
                },
            );
            uncompute_active(&mut c, &[], &active);
            c.zero_and_free(active);
            stage(&mut c, &mut stages, "restore_old_high_lanes", |c| {
                shrunken_pz_resize(c, &mut a, v, "A");
                shrunken_pz_resize(c, &mut b, v, "B");
            });
            stage(&mut c, &mut stages, "PREP_inverse", |c| {
                d_alignment_prep::apply_profile(
                    c, &a, &b, &ca, &cb, &q, phi, role, &srot, &offset, true,
                )
            });
        }
    }
    c.flush_pending_frees();
    let weights = expectations(&c.b.ops);
    let expected = |lo: usize, hi: usize| match &weights {
        Ok(v) => format!("{}", v[lo..hi].iter().sum::<f64>()),
        Err(_) => "null".into(),
    };
    let raw = |lo: usize, hi: usize| {
        c.b.ops[lo..hi]
            .iter()
            .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
            .count()
    };
    let common_lo = if new
        && !boundary
        && std::env::var("MIDQ_D_ALIGN_COMMON_WINDOW").ok().as_deref() == Some("1")
    {
        d_alignment_prep::profile_floor(v, m)
    } else {
        0
    };
    let direction = if inverse { "inverse" } else { "forward" };
    let variant = if new { "framed" } else { "original" };
    let error = weights
        .as_ref()
        .err()
        .map_or(String::from("null"), |e| format!("{e:?}"));
    println!("D_ALIGN_LEDGER {{\"step\":{step},\"variant\":\"{variant}\",\"direction\":\"{direction}\",\"boundary\":{boundary},\"AB\":{n},\"retained_AB\":{v},\"common_lo\":{common_lo},\"cofactor\":{m},\"q\":{qwidth},\"passenger\":256,\"input_floor\":{input_floor},\"output_floor\":{},\"peak\":{},\"cap\":{},\"raw_T\":{},\"unoptimized_expected_T\":{},\"expectation_error\":{error}}}",c.b.active_qubits,c.b.peak_qubits,env_usize("HYBRID_QCAP",0),raw(0,c.b.ops.len()),expected(0,c.b.ops.len()));
    for s in stages {
        println!("D_ALIGN_STAGE {{\"step\":{step},\"variant\":\"{variant}\",\"direction\":\"{direction}\",\"boundary\":{boundary},\"stage\":\"{}\",\"peak\":{},\"raw_T\":{},\"unoptimized_expected_T\":{}}}",s.label,s.peak,raw(s.start,s.end),expected(s.start,s.end));
    }
}

pub(crate) fn run() {
    expectation_checks();
    assert_eq!(qretain::fixed_width(), Some(32));
    assert!(prefix_no_terminal_eligible(0) && lowq_hybrid_gate_hold_enabled());
    assert!(!lowq_inline_active_enabled() && !lowq_recompute_gate_predicate_enabled());
    assert!(std::env::var("MIDQ_RETAIN_DIV_LENGTHS").ok().as_deref() == Some("1"));
    assert!(std::env::var("MIDQ_RETAIN_MUL_LENGTHS").ok().as_deref() == Some("1"));
    assert_eq!(
        env_usize("HYBRID_QCAP", 0),
        1100,
        "ledger fixed at explicit Q1100"
    );
    // Keep one iteration's stream at a time, for exact conditional-cost audit.
    // This is not whole-circuit emission or a field simulation.
    std::env::set_var("POINT_ADD_COUNT_ONLY", "0");
    let selected = std::env::var("MIDQ_D_ALIGNMENT_LEDGER_STEPS").ok();
    let steps: Vec<usize> = selected.map_or_else(
        || (0..MIDQ_PZ_CUT).collect(),
        |v| v.split(',').map(|s| s.parse().unwrap()).collect(),
    );
    for step in steps {
        assert!(step < MIDQ_PZ_CUT);
        for inverse in [false, true] {
            for new in [false, true] {
                emit(step, new, inverse, false);
            }
        }
    }
    for inverse in [false, true] {
        emit(MIDQ_PZ_CUT - 1, true, inverse, true);
    }
    eprintln!("D_ALIGN_LEDGER COMPLETE production_dispatch=false per_iteration_streams_only=true numerical_phase_validation_of_full_iteration=PENDING expectation_before_compiler=true");
}
