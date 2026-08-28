use super::*;

use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::OnceLock;

fn inverse_cse_cache() -> &'static Mutex<HashMap<&'static str, Vec<Op>>> {
    static CACHE: OnceLock<Mutex<HashMap<&'static str, Vec<Op>>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

pub(crate) fn clear_inverse_cse_cache() {
    if let Ok(mut g) = inverse_cse_cache().lock() {
        g.clear();
    }
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
}

pub(crate) fn emit_inverse_cached<F: FnOnce(&mut B)>(
    b: &mut B,
    key: &'static str,
    f: F,
) {
    if b.count_only {
        if let Ok(g) = INVERSE_CSE_CACHE.lock() {
            if let Some(cached_ops) = g.get(key) {
                let mut delta = [0usize; 18];
                for op in cached_ops.iter() {
                    delta[op.kind as usize] += 1;
                }
                add_inverse_count_delta(b, &delta);
                return;
            }
        }
        let snap = b.count_snapshot();
        f(b);
        let delta = b.count_delta_since(snap);
        b.restore_count_snapshot(snap);
        add_inverse_count_delta(b, &delta);
        return;
    }

    if let Ok(g) = INVERSE_CSE_CACHE.lock() {
        if let Some(cached_ops) = g.get(key) {
            for &op in cached_ops.iter() {
                match op.kind {
                    OperationType::X
                    | OperationType::Z
                    | OperationType::CX
                    | OperationType::CZ
                    | OperationType::CCX
                    | OperationType::CCZ
                    | OperationType::Swap => b.push_op(op),
                    _ => {}
                }
            }
            return;
        }
    }

    let start = b.ops.len();
    f(b);
    let end = b.ops.len();

    let fwd: Vec<Op> = b.ops[start..end].to_vec();
    b.ops.truncate(start);

    let mut inv: Vec<Op> = Vec::with_capacity(fwd.len());
    for op in fwd.iter().rev().copied() {
        match op.kind {
            OperationType::X
            | OperationType::Z
            | OperationType::CX
            | OperationType::CZ
            | OperationType::CCX
            | OperationType::CCZ
            | OperationType::Swap => {
                b.push_op(op);
                inv.push(op);
            }
            OperationType::R => {}
            OperationType::Register
            | OperationType::AppendToRegister
            | OperationType::DebugPrint => {}
            _ => panic!(
                "emit_inverse_cached: non-invertible op kind {:?} inside forward block (key {})",
                op.kind, key
            ),
        }
    }

    if let Ok(mut g) = INVERSE_CSE_CACHE.lock() {
        g.insert(key, inv);
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
