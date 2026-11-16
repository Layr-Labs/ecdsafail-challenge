//! Argon-audit levers (lane struct764 / scorched / argon). One name per lever, all default ON. Each lever's OFF value must
//! reproduce the parent stream exactly (switch with a sed on the const, see argon/work/pre_*.sh). The official build reads
//! nothing from the environment for these.
/// E3a: seed_inv_zw's (1 + ZW_STREAM)-control zero test through `mask::mc_xor` with the clean lane `bit` as a temp.
pub const E3A_ZW_TEST: bool = true;
/// E3b: the 256-control `xor_eq(z, 0, flag)` at the ends of seed_fwd (temp k) and the start of seed_inv_zw (temp bit).
pub const E3B_XOR_EQ: bool = true;
/// E3c: seed_inv_zw's w-control `test_top` through mc_xor with temp bit.
pub const E3C_TEST_TOP: bool = true;
/// E2c: seed_inv_zw emits the forward modular subtraction (complement, ctrl_modadd, complement) instead of replaying the
/// recorded inverse of the add, so ms.k is erased by `measured_erase` (not the 83-CCX compare).
pub const E2C_DIRECT_SUB: bool = true;
/// E7: `sub_small` takes the pooled / Gidney fold (complemented window) when the pool allows, instead of the recorded inverse.
pub const E7_SUBFOLD: bool = true;
/// E9: sq_horner_c drops the last halve_c and the double_c that follows it (exact inverse pair).
pub const E9_HALVE: bool = true;
/// E2f: `add_small` for the fold t += ctrl * C (lo = 0) runs as ONE exact add of 977 into t[0..10) plus a carry lane, one carry
/// increment of t[10..45), a recompute of the carry lane, and the 2^32 increment of t[32..67): about 457 CCX with a clean lane
/// (`FOLD_CLEAN`), 597 with a borrowed one, against 700 for the five NAF digits (each digit's 36-lane increment).
/// Differs from the NAF fold only on inputs where a carry crosses the 35-lane window (about 2^-35 per fold, as before).
pub const E2F_FOLD: bool = true;
thread_local! {
    /// A clean |0> lane offered to the next `add_small` fold (set by the caller around one `ctrl_modadd`).
    pub static FOLD_CLEAN: std::cell::Cell<Option<crate::circuit::QubitId>> = std::cell::Cell::new(None);
}
