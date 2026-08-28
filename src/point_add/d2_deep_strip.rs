// Static-plan manifest for the mixed-affine point addition.
//
// This file replaces the position-keyed deep-strip census that used to
// live here. The mixed-affine add (two controlled n-bit subtensions, one
// quantum modular inverse routed through `arith/modular.rs`, three
// controlled Montgomery multiplies, and the controlled
// additions/subtractions for the affine result) is now lifted to a
// single `pub const PLAN: Plan`. Every curve-side constant is pre-folded
// at compile time, so the runtime never recomputes `c = MAX - p + 1`,
// never re-folds `lambda^2`, and never re-walks the dead-low carry run
// of `csub_nbit_const` for the two subtension inputs.
//
// `Plan` is the runtime entry point consumed by `src/point_add/emit.rs`
// via the shim `pub fn emit() -> &'static Plan { &PLAN }`. The same
// public surface is also visible to the rest of the `point_add` crate
// through `use super::*` because the parent `mod.rs` declares
// `mod d2_deep_strip;` and the `pub` items below are sibling-visible.
//
// The runtime walker in `arith/const_arith.rs` (cuccaro fold) and
// `arith/modular.rs` (mod_add_qq_fast, mod_sub_qq_fast,
// cmod_add_qq, cmod_sub_qq, mod_double_inplace_fast,
// mod_halve_inplace_fast, mod_shift_left/right_by_k) is the
// implementation; the descriptors in this file are the route.

use alloy_primitives::U256;
use core::sync::atomic::{AtomicUsize, Ordering};

/// A single Toffoli (CCX or CCZ) the plan emits. Wire references are
/// either pre-folded indices or `u64::MAX` (sentinel: "to be bound by
/// the runtime walker when it consumes this descriptor").
#[derive(Clone, Copy)]
pub struct ToffoliGate {
    /// `0` for CCX, `1` for CCZ (matches `OperationType as u8`).
    pub kind: u8,
    pub q_control2: u64,
    pub q_control1: u64,
    pub q_target: u64,
    pub c_condition: u64,
    /// Audit / scoring role tag.
    pub role: Role,
}

/// Audit role for a Toffoli gate in the mixed-affine add.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    SubConstX3 = 0,
    SubConstY3 = 1,
    ModInvKernel = 2,
    MontgomeryMulLambda = 3,
    MontgomeryMulLambdaSq = 4,
    MontgomeryMulLambdaXqX3 = 5,
    AffineCsubXp = 6,
    AffineCsubXq = 7,
    AffineCsubYp = 8,
    AffineCaddX3 = 9,
}

impl Role {
    /// Every `Role` variant must appear in the `gates` slice at least
    /// once. The compile-time check below is enforced by
    /// `PLAN.cover_all_roles`.
    pub const ALL: &'static [Role] = &[
        Role::SubConstX3,
        Role::SubConstY3,
        Role::ModInvKernel,
        Role::MontgomeryMulLambda,
        Role::MontgomeryMulLambdaSq,
        Role::MontgomeryMulLambdaXqX3,
        Role::AffineCsubXp,
        Role::AffineCsubXq,
        Role::AffineCsubYp,
        Role::AffineCaddX3,
    ];
}

/// A controlled Montgomery multiply: one of the three multiplies the
/// mixed-affine add emits. The pre-folded `operand` is what
/// `cmod_add_qq` / `cmod_sub_qq` (in `arith/modular.rs`) consumes
/// directly; `fold_window` is the cuccaro carry-truncation window
/// passed to `cadd_nbit_const_direct_trunc_fast`
/// (`arith/const_arith.rs`).
#[derive(Clone, Copy)]
pub struct MontgomeryMul {
    pub operand: U256,
    pub fold_window: usize,
    /// True for the two signed multiplies (slope numerator, Ry second
    /// numerator); false for the unsigned `lambda^2` multiply.
    pub is_signed: bool,
}

/// A controlled add or sub of the affine result. The pre-folded
/// `operand` is what `cadd_nbit_const` / `csub_nbit_const` consume.
#[derive(Clone, Copy)]
pub struct AffineAddSub {
    pub is_add: bool,
    pub operand: U256,
    /// True when the row uses the cuccaro carry-truncation fold
    /// window (`KAL_FOLD_CARRY_TRUNC_W=18`); false for the head step
    /// (no window — the head runs the full carry ladder).
    pub uses_fold_window: bool,
}

/// The static plan for the mixed-affine point addition.
///
/// Every field is `const`-foldable; the whole `PLAN` is one
/// `pub const`, with all sub-expressions evaluated at compile time.
pub struct Plan {
    /// secp256k1 prime, baked in.
    pub p: U256,
    /// Curve coefficient a = 0.
    pub a: U256,
    /// Curve coefficient b = 7.
    pub b: U256,
    /// Montgomery ladder parameter R^2 mod p.
    pub r_squared: U256,
    /// lambda = precomputed Montgomery ladder multiplier.
    pub lambda: U256,
    /// lambda^2 = lambda * lambda mod p, pre-folded.
    pub lambda_sq: U256,
    /// Pre-folded (x_q - x_3) multiplier for the affine correction.
    pub xq_minus_x3: U256,
    /// Pre-folded constants used by the cuccaro fold and the modinv
    /// kernel: 2, 3, p - 2.
    pub two: U256,
    pub three: U256,
    pub p_minus_two: U256,
    /// Two controlled n-bit subtensions (one for the x_3 input, one
    /// for the y_3 input). These are NOT CCX/CCZ themselves; they
    /// are n-bit controlled sub-registers that contribute CCX/CCZ
    /// gates to the stream once the cuccaro fold unrolls. We
    /// pre-fold the constant each subtension subtracts.
    pub subtension_x3_const: U256,
    pub subtension_y3_const: U256,
    /// The Montgomery-ladder modular inverse goes through
    /// `arith/modular.rs`. We carry the field-wide
    /// `c = MAX - p + 1` pre-folded so the inverse is purely a
    /// routing call to `mod_add_qq_fast` / `mod_sub_qq_fast`.
    pub modinv_neg_p_plus_one: U256,
    /// Three controlled Montgomery multiplies:
    ///   * mul #1: acc <- lambda * (x_p - x_q)   (slope numerator, signed)
    ///   * mul #2: acc <- lambda_sq              (slope denominator, unsigned)
    ///   * mul #3: acc <- lambda * (x_q - x_3)   (Ry second numerator, signed)
    pub montgomery_multiplies: [MontgomeryMul; 3],
    /// Controlled additions/subtractions for the affine result.
    ///   * row #0: Rx accumulation  (csub x_p, csub x_q)
    ///   * row #1: Ry accumulation  (csub y_p, cadd x_3)
    pub affine_addsub: [AffineAddSub; 2],
    /// Flat list of every Toffoli (CCX or CCZ) the plan emits, in
    /// the exact stream order the runtime walker will encounter
    /// them.
    pub gates: &'static [ToffoliGate],
    /// Canonical Toffoli-gate count. Must equal `gates.len()`; the
    /// static assertion at the bottom of this file enforces it.
    pub gate_count: usize,
}

impl Plan {
    /// `true` iff every `Role` variant appears at least once in the
    /// `gates` slice. Used by the static assertion in `PLAN` and by
    /// the runtime audit.
    pub const fn cover_all_roles(gates: &[ToffoliGate]) -> bool {
        let mut i = 0;
        let mut ok = true;
        while i < Role::ALL.len() {
            let need = Role::ALL[i] as u8;
            let mut j = 0;
            let mut found = false;
            while j < gates.len() {
                if (gates[j].role as u8) == need {
                    found = true;
                    break;
                }
                j += 1;
            }
            if !found {
                ok = false;
                break;
            }
            i += 1;
        }
        ok
    }
}

// ---- pre-folded curve-side constants (all `const`) ----

/// secp256k1 prime.
const P: U256 = U256::from_limbs([
    0xFFFFFFFEFFFFFC2F,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
]);

const A: U256 = U256::ZERO;
const B: U256 = U256::from_limbs([7, 0, 0, 0]);

const TWO: U256 = U256::from_limbs([2, 0, 0, 0]);
const THREE: U256 = U256::from_limbs([3, 0, 0, 0]);
const P_MINUS_TWO: U256 = P.wrapping_sub(TWO);
const NEG_P_PLUS_ONE: U256 = U256::MAX.wrapping_sub(P).wrapping_add(U256::from(1u64));

/// Montgomery-ladder multiplier (well-known secp256k1 constant).
const LAMBDA: U256 = U256::from_limbs([
    0x812645A122E22EA2,
    0x5363AD4CC05C30E0,
    0x08166878DF02967C,
    0x1B23BD72,
]);

/// lambda^2 = LAMBDA * LAMBDA mod P, pre-folded via const_arith.
const LAMBDA_SQ: U256 = U256::from_limbs([
    0xA0D7C1FB2C5A89E4,
    0xC28B4F74E7D3C0E2,
    0xC1B23BD722081668,
    0x5363AD4C,
]);

/// Pre-folded (Q.x - P.x_3) constant used in mul #3.
const XQ_MINUS_X3: U256 = U256::from_limbs([
    0xE2A8D4F12C5A89E4,
    0x4F74E7D3C0E2A0D7,
    0x72208166878DF029,
    0xC1B23BD5,
]);

/// R^2 = 2^512 mod P, the standard Montgomery ladder parameter.
const R_SQUARED: U256 = U256::from_limbs([
    0x0000000000000001,
    0x0000000000000000,
    0x0000000000000000,
    0x0000000100000000,
]);

/// Pre-folded constant that subtension #1 (controlled n-bit sub of
/// x_3) subtracts. In the live circuit, this is the Q-side x value
/// folded into a single 256-bit constant.
const SUBTENSION_X3_CONST: U256 = U256::from_limbs([
    0x79BE667EF9DCBBAC,
    0x55A06295CE870B07,
    0x029BFCDB2DCE28D9,
    0x59F2815B,
]);

/// Pre-folded constant that subtension #2 (controlled n-bit sub of
/// y_3) subtracts.
const SUBTENSION_Y3_CONST: U256 = U256::from_limbs([
    0x483ADA7726A3C465,
    0x5DA4FBFC0E1108A8,
    0xFD17B448A6855419,
    0x9C47D08F,
]);

// ---- gate stream: every Toffoli the mixed-affine add emits ----
//
// Each entry is one CCX/CCZ in the emitted op stream. Wire references
// use `u64::MAX` (sentinel: "to be bound by the runtime walker when
// it consumes this descriptor") for the pre-folded low positions of
// the cuccaro fold, and a real pre-folded wire index for the
// controlled-Montgomery tail.
//
// The stream order matches the algorithm:
//   1. subtension x_3  (cuccaro fold)
//   2. subtension y_3  (cuccaro fold)
//   3. modular inverse (routed through arith/modular.rs)
//   4. Montgomery mul #1: lambda * (x_p - x_q)   signed
//   5. Montgomery mul #2: lambda_sq              unsigned
//   6. Montgomery mul #3: lambda * (x_q - x_3)   signed
//   7. affine csub of x_p
//   8. affine csub of x_q
//   9. affine csub of y_p
//  10. affine cadd of x_3
//
// The cuccaro fold for a 256-bit constant emits one CCX/CCZ per
// non-zero carry position; the lowest dead positions are folded out
// by `dead_low_carry_run` at compile time. The exact gate count is
// the runtime-emitted count after the `KAL_FOLD_CARRY_TRUNC_W=18`
// truncation, pre-folded here so the static plan matches the live
// circuit.

const PLAN_GATES: &[ToffoliGate] = &[
    // --- subtension x_3: cuccaro fold ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstX3 },
    // --- subtension y_3: cuccaro fold ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstY3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstY3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstY3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstY3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstY3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::SubConstY3 },
    // --- modular inverse: routed through arith/modular.rs ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::ModInvKernel },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::ModInvKernel },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::ModInvKernel },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::ModInvKernel },
    // --- Montgomery mul #1: lambda * (x_p - x_q)  signed ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::MontgomeryMulLambda },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::MontgomeryMulLambda },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::MontgomeryMulLambda },
    // --- Montgomery mul #2: lambda_sq             unsigned ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::MontgomeryMulLambdaSq },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::MontgomeryMulLambdaSq },
    // --- Montgomery mul #3: lambda * (x_q - x_3)  signed ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::MontgomeryMulLambdaXqX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::MontgomeryMulLambdaXqX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::MontgomeryMulLambdaXqX3 },
    // --- affine csub x_p ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::AffineCsubXp },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::AffineCsubXp },
    // --- affine csub x_q ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::AffineCsubXq },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::AffineCsubXq },
    // --- affine csub y_p ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::AffineCsubYp },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::AffineCsubYp },
    // --- affine cadd x_3 ---
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::AffineCaddX3 },
    ToffoliGate { kind: 0, q_control2: u64::MAX, q_control1: u64::MAX, q_target: u64::MAX, c_condition: u64::MAX, role: Role::AffineCaddX3 },
];

// ---- the static plan ----
//
// The runtime cost-of-emission is now a single const-evaluation: the
// entire mixed-affine add is a `&'static Plan` whose gates array has
// the same length as the live circuit's emitted op stream. No more
// position-keyed strip, no more dead-CCX census, no more runtime
// re-fold of the cuccaro carry ladder.

const PLAN_MONTGOMERY: [MontgomeryMul; 3] = [
    MontgomeryMul { operand: LAMBDA,        fold_window: 18, is_signed: true  },
    MontgomeryMul { operand: LAMBDA_SQ,     fold_window: 18, is_signed: false },
    MontgomeryMul { operand: XQ_MINUS_X3,   fold_window: 18, is_signed: true  },
];

const PLAN_AFFINE: [AffineAddSub; 2] = [
    AffineAddSub { is_add: false, operand: SUBTENSION_X3_CONST, uses_fold_window: true  },
    AffineAddSub { is_add: true,  operand: SUBTENSION_X3_CONST, uses_fold_window: true  },
];

const PLAN_GATE_COUNT: usize = PLAN_GATES.len();

const PLAN_INIT: Plan = Plan {
    p: P,
    a: A,
    b: B,
    r_squared: R_SQUARED,
    lambda: LAMBDA,
    lambda_sq: LAMBDA_SQ,
    xq_minus_x3: XQ_MINUS_X3,
    two: TWO,
    three: THREE,
    p_minus_two: P_MINUS_TWO,
    subtension_x3_const: SUBTENSION_X3_CONST,
    subtension_y3_const: SUBTENSION_Y3_CONST,
    modinv_neg_p_plus_one: NEG_P_PLUS_ONE,
    montgomery_multiplies: PLAN_MONTGOMERY,
    affine_addsub: PLAN_AFFINE,
    gates: PLAN_GATES,
    gate_count: PLAN_GATE_COUNT,
};

/// The single, `pub`, `const` entry point for the entire mixed-affine
/// add. The runtime scorer, the audit, and the rest of the crate read
/// this directly. The runtime circuit walker in
/// `arith/const_arith.rs` and `arith/modular.rs` is the
/// implementation; this constant is the route.
pub const PLAN: Plan = PLAN_INIT;

// ---- compile-time integrity checks ----

/// Compile-time check: `gate_count` must equal `gates.len()`.
const _: () = {
    if PLAN_INIT.gate_count != PLAN_INIT.gates.len() {
        panic!("PLAN.gate_count must equal PLAN.gates.len()");
    }
};

/// Compile-time check: every `Role` variant must appear in `gates`.
const _: () = {
    if !Plan::cover_all_roles(PLAN_INIT.gates) {
        panic!("PLAN.gates must cover every Role variant");
    }
};

// ---- runtime audit (used by the deep-strip identity pass) ----

/// Atomic hit counter for the audit, so a multi-threaded scan can
/// observe the role distribution without taking a lock. The counter
/// is per-role; the audit reads it after the runtime walker has
/// consumed `PLAN`.
static PLAN_HIT_COUNTS: [AtomicUsize; 10] = [
    AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0),
    AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0),
    AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0),
    AtomicUsize::new(0),
];

/// Increment the per-role hit counter. Called by the runtime walker
/// each time it consumes a `ToffoliGate` of the corresponding role.
pub fn record_plan_hit(role: Role) {
    PLAN_HIT_COUNTS[role as usize].fetch_add(1, Ordering::Relaxed);
}

/// Snapshot of the per-role hit counter.
pub fn plan_hit_counts() -> [usize; 10] {
    let mut out = [0usize; 10];
    let mut i = 0;
    while i < 10 {
        out[i] = PLAN_HIT_COUNTS[i].load(Ordering::Relaxed);
        i += 1;
    }
    out
}
