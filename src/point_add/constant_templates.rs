//! Exact finite-word constant binders; public ecdsa.fail resource research.
use super::*;
pub(crate) fn square_compare(
    c: &mut Builder,
    u: &[QubitId],
    v: &[QubitId],
    seed: Option<QubitId>,
) -> bool {
    if std::env::var_os("CONST_SQUARE_TRANSPORT").is_none()
        || c.current_phase() != "square"
        || u.len() != 14
        || v.len() != 14
        || seed == Some(v[0])
    {
        return false;
    }
    let room = super::pingpong::heo_hooks::cap().saturating_sub(c.active_qubits() as usize);
    if room != 12 {
        return false;
    }
    assert!(!seed.is_some_and(|q| u.contains(&q)));
    let at = c.op_count();
    // The operand variant never reads or writes its legacy dirty argument.
    super::dirty_boundary_probe::hybrid(c, u, v, seed, u[0], 1, false);
    eprintln!(
        "CONST_SQUARE_COMPARE\t{at}\t14\t{room}\t1\t{}",
        seed.is_some() as u8
    );
    true
}
pub(crate) fn try_ladder(
    c: &mut Builder,
    b: &[QubitId],
    source: QubitId,
    bits: &[bool],
    dead: usize,
    host: Option<QubitId>,
    room: usize,
) -> bool {
    if b.len() > 64 {
        return false;
    }
    let mode = std::env::var("CONST_BINDER_MODE").unwrap_or_default();
    let packed = mode == "packed";
    if !packed && mode != "suffix" {
        return false;
    }
    let pattern = bits
        .iter()
        .enumerate()
        .fold(0u64, |v, (i, &x)| v | ((x as u64) << i));
    let f = (1u64 << 32) + 977;
    let (label, bytes): (&str, &[u8]) =
        if b.len() == 58 && dead == 0 && host.is_none() && room == 55 && pattern == f {
            (
                "square",
                if packed {
                    include_bytes!("constant_data/square-packed-forward.bin")
                } else {
                    include_bytes!("constant_data/square-suffix-forward.bin")
                },
            )
        } else if b.len() == 57
            && dead == 3
            && host.is_some()
            && room == 50
            && pattern == (0u64.wrapping_sub(f >> 1) & ((1u64 << 57) - 1))
        {
            (
                "halve",
                if packed {
                    include_bytes!("constant_data/halve-packed-forward.bin")
                } else {
                    include_bytes!("constant_data/halve-suffix-forward.bin")
                },
            )
        } else {
            return false;
        };
    assert!(!b.contains(&source));
    assert!(host.is_none_or(|h| h != source && !b.contains(&h)));
    let base = c.active_qubits();
    let at = c.op_count();
    let regs = vec![b.to_vec(), vec![source], host.into_iter().collect()];
    let (_, t, peak) = super::fold_template::emit_bound(c, bytes, Some(&regs));
    assert_eq!(c.active_qubits(), base);
    eprintln!(
        "CONST_DEPLOY\t{label}\t{mode}\t{at}\t{room}\t{t}\t{}",
        peak - regs.iter().map(Vec::len).sum::<usize>() as u32
    );
    true
}
