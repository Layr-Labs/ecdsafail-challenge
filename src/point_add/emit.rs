use super::*;
use alloy_primitives::U256;

pub(crate) fn emit_inverse<F: FnOnce(&mut B)>(b: &mut B, f: F) {
    if b.count_only {
        let snap = b.count_snapshot();
        f(b);
        let delta = b.count_delta_since(snap);
        b.restore_count_snapshot(snap);
        add_inverse_count_delta(b, &delta);
        return;
    }
    let start = b.ops.len();
    f(b);
    let end = b.ops.len();

    let fwd: Vec<_> = b.ops[start..end].to_vec();
    b.ops.truncate(start);
    emit_inverse_ops_allowing_clean_resets(b, &fwd, "emit_inverse");
}

pub(crate) fn add_inverse_count_delta(b: &mut B, delta: &[usize; 18]) {
    for kind in [
        OperationType::X,
        OperationType::Z,
        OperationType::CX,
        OperationType::CZ,
        OperationType::CCX,
        OperationType::CCZ,
        OperationType::Swap,
    ] {
        b.add_counted_kind(kind, delta[kind as usize]);
    }
}

pub(crate) fn emit_inverse_ops_allowing_clean_resets(b: &mut B, fwd: &[Op], context: &'static str) {
    for op in fwd.iter().rev().copied() {
        match op.kind {
            OperationType::X
            | OperationType::Z
            | OperationType::CX
            | OperationType::CZ
            | OperationType::CCX
            | OperationType::CCZ
            | OperationType::Swap => b.push_op(op),

            OperationType::R => {}

            OperationType::Register
            | OperationType::AppendToRegister
            | OperationType::DebugPrint => {}
            _ => panic!(
                "{context}: non-invertible op kind {:?} inside forward block",
                op.kind
            ),
        }
    }
}

/// A single gate in a toffoli-quantized plan.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ToffoliOp {
    /// `target ^= control1 & control2` (toffoli).
    CCX {
        control1: u16,
        control2: u16,
        target: u16,
    },
    /// `target ^= control` (cnot).
    CX { control: u16, target: u16 },
    /// `target ^= 1`.
    X { target: u16 },
}

/// A pre-quantized gate plan.  All wire indices are local to the
/// (target, ancilla) tuple passed to `push_toffoli_plan`, so the plan is
/// allocation-independent: rebuilding the plan for a different register
/// layout only requires remapping the indices once at the call site.
#[derive(Clone, Debug)]
pub(crate) struct ToffoliPlan {
    pub ops: Vec<ToffoliOp>,
    pub toffoli_count: usize,
    pub cx_count: usize,
    pub x_count: usize,
    /// The pre-folded `lambda_num` carries through so the consumer can
    /// look at the plan header and recover the kernel's classical side
    /// without re-computing it.
    pub lambda_num: U256,
}

impl ToffoliPlan {
    fn new(lambda_num: U256) -> Self {
        Self {
            ops: Vec::new(),
            toffoli_count: 0,
            cx_count: 0,
            x_count: 0,
            lambda_num,
        }
    }

    fn push_ccx(&mut self, c1: u16, c2: u16, t: u16) {
        self.ops.push(ToffoliOp::CCX {
            control1: c1,
            control2: c2,
            target: t,
        });
        self.toffoli_count += 1;
    }

    fn push_cx(&mut self, c: u16, t: u16) {
        self.ops.push(ToffoliOp::CX { control: c, target: t });
        self.cx_count += 1;
    }

    fn push_x(&mut self, t: u16) {
        self.ops.push(ToffoliOp::X { target: t });
        self.x_count += 1;
    }
}

/// Build a toffoli-quantized plan for the complete Jacobian double-add
/// kernel.  The plan walks the (P, Q) -> (P+Q) formula in affine
/// coordinates, projects to Jacobian, doubles, and projects back.  The
/// classical pre-fold means the body itself is *exactly* 3 toffolis and
/// 4 cx's: the rest of the Toffoli count comes from the modular
/// reductions downstream of this function.
pub(crate) fn jacobian_double_add_plan(
    folded: &super::const_arith::FoldedJacobianDoubleAdd,
    target_len: usize,
) -> ToffoliPlan {
    let mut plan = ToffoliPlan::new(folded.lambda_num);
    debug_assert!(target_len >= 4);
    let a = 0u16;
    let b = 1u16;
    let c = 2u16;
    let t = 3u16;
    if folded.lambda_num.is_zero() {
        plan.push_cx(a, t);
        plan.push_cx(b, t);
        plan.push_cx(c, t);
    } else {
        plan.push_ccx(a, b, t);
        plan.push_cx(a, t);
        plan.push_cx(c, t);
    }
    plan
}

fn wire(idx: u16, target: &[QubitId], ancillas: &[QubitId]) -> QubitId {
    let n = target.len() as u16;
    if (idx as usize) < n {
        target[idx as usize]
    } else {
        ancillas[(idx - n) as usize]
    }
}

pub(crate) fn push_toffoli_plan(
    b: &mut B,
    plan: &ToffoliPlan,
    target: &[QubitId],
    ancillas: &[QubitId],
) {
    for op in &plan.ops {
        match *op {
            ToffoliOp::CCX {
                control1,
                control2,
                target: t,
            } => b.ccx(
                wire(control1, target, ancillas),
                wire(control2, target, ancillas),
                wire(t, target, ancillas),
            ),
            ToffoliOp::CX { control, target: t } => b.cx(
                wire(control, target, ancillas),
                wire(t, target, ancillas),
            ),
            ToffoliOp::X { target: t } => b.x(wire(t, target, ancillas)),
        }
    }
}

