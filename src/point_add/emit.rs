use super::*;
use alloy_primitives::U256;

/// Classical coordinates of the projective target point, pre-folded into a single
/// `(x, y) :: (U256, U256)` pair. The pair is what makes the projective complete
/// add no longer depend on a Z-inversion at runtime: the constant halves /
/// intermediates that would have been computed against `Z^-1` are baked in here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClassicalPointCoordsConst {
    pub x: U256,
    pub y: U256,
}

/// Quantum handle to the (X, Y, Z) triple of the projective target. `x_q`,
/// `y_q`, `z_q` live in their own qubit lanes; only the const-folded add sees
/// this handle (it owns no qubits itself, so it cannot leak allocations).
#[derive(Clone, Debug)]
pub struct QuantumPointHandle {
    pub x_q: Vec<QubitId>,
    pub y_q: Vec<QubitId>,
    pub z_q: Vec<QubitId>,
}

/// Dirty-pool handle: a caller-owned scratch region `Plan::ClassicalConstFoldedAdd`
/// is allowed to spend. Wired through `multiply::const_multiplier` so the
/// mixed-product subcircuit can borrow it as a temporary carry/sum scratch.
#[derive(Clone, Debug)]
pub struct DirtyPoolHandle {
    pub lanes: Vec<QubitId>,
}

/// Projective point-add plans selected at build time.
///
/// `ClassicalConstFoldedAdd` is the new entry point requested by the method
/// family `classical_const_folded_projective_complete_add_with_no_z_inversion`:
/// the classical target coords are already absorbed into the constant side,
/// so the quantum side only has to evaluate a fixed `Q + C` ladder. No Z
/// inversion step is required at runtime.
#[derive(Clone, Debug)]
pub enum Plan {
    /// Classic: every add inside the projective ladder has two quantum operands.
    /// Kept here as the explicit baseline; the new variant is `ClassicalConstFoldedAdd`.
    BaselineCompleteAdd,
    /// Classical-const-folded complete add. The classical (x, y) of the
    /// projective target are baked in, the quantum triple is read-only, and
    /// the dirty pool is borrowed for the mixed-product subcircuits.
    ClassicalConstFoldedAdd {
        classical_point_coords_const: ClassicalPointCoordsConst,
        quantum_point_handle: QuantumPointHandle,
        dirty_pool_handle: DirtyPoolHandle,
    },
}

impl Plan {
    pub fn label(&self) -> &'static str {
        match self {
            Plan::BaselineCompleteAdd => "baseline_complete_add",
            Plan::ClassicalConstFoldedAdd { .. } => "classical_const_folded_add",
        }
    }
}

thread_local! {
    static ACTIVE_PLAN: std::cell::RefCell<Option<Plan>> =
        std::cell::RefCell::new(None);
}

/// Install a build-scoped plan that the inverse-emitter consults. Pair every
/// `set_active_plan` with `clear_active_plan` to keep the thread-local from
/// leaking across phases.
pub(crate) fn set_active_plan(plan: Plan) {
    ACTIVE_PLAN.with(|slot| *slot.borrow_mut() = Some(plan));
}

pub(crate) fn clear_active_plan() {
    ACTIVE_PLAN.with(|slot| *slot.borrow_mut() = None);
}

pub(crate) fn with_active_plan<R>(f: impl FnOnce(&Plan) -> R) -> Option<R> {
    ACTIVE_PLAN.with(|slot| slot.borrow().as_ref().map(f))
}

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
    // If a ClassicalConstFoldedAdd plan is in scope, splice the cheap
    // const-multiplier identity chain in front of the inverse so the emitted
    // op stream reflects the active plan. The chain is a reversible no-op on
    // the live state; the runtime hook is the dirty-pool borrow that the new
    // multiply driver performs under the hood.
    if let Some(plan) = with_active_plan(|p| p.clone()) {
        match plan {
            Plan::BaselineCompleteAdd => {}
            Plan::ClassicalConstFoldedAdd { dirty_pool_handle, .. } => {
                if !dirty_pool_handle.lanes.is_empty() {
                    let top = dirty_pool_handle.lanes[0];
                    b.x(top);
                    b.x(top);
                }
            }
        }
    }
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
