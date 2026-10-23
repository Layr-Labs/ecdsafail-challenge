
use crate::circuit::{Op, OperationType, NO_QUBIT};

fn toffoli_ops(ops: &[Op]) -> usize {
    ops.iter()
        .filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ))
        .count()
}

fn densify(ops: &mut [Op]) {
    let mut ids = Vec::new();
    for op in ops.iter() {
        for q in [op.q_control2.0, op.q_control1.0, op.q_target.0] {
            if q != NO_QUBIT.0 {
                ids.push(q);
            }
        }
    }
    if ids.is_empty() {
        return;
    }
    ids.sort_unstable();
    ids.dedup();
    let max = *ids.last().unwrap();
    if max > 1_000_000 || ids.len() as u64 == max + 1 {
        return;
    }
    let mut present = vec![false; max as usize + 1];
    for &q in &ids {
        present[q as usize] = true;
    }
    let mut holes: Vec<u64> = (0..=max).filter(|&q| !present[q as usize]).collect();
    let mut live = ids;
    while let (Some(&hole), Some(&donor)) = (holes.first(), live.last()) {
        if donor <= hole {
            break;
        }
        for op in ops.iter_mut() {
            for q in [&mut op.q_control2.0, &mut op.q_control1.0, &mut op.q_target.0] {
                if *q == donor {
                    *q = hole;
                }
            }
        }
        eprintln!("post_restore densify {donor} -> {hole}");
        live.pop();
        holes.remove(0);
    }
}

pub(super) fn run(mut ops: Vec<Op>) -> Vec<Op> {
    let (n0, t0) = (ops.len(), toffoli_ops(&ops));
    ops = super::truth_simplify::simplify_products(ops);
    ops = super::affine_simplify::simplify(ops);
    ops = super::quadratic_simplify::simplify(ops);
    ops = super::truth_simplify::simplify(ops);
    ops = super::classical_factors_xor::simplify_classical(ops);
    ops = super::classical_wide::simplify_classical(ops);
    ops = super::affine_simplify::simplify(ops);
    eprintln!(
        "post_restore ops {n0} -> {} toffoli-ops {t0} -> {}",
        ops.len(),
        toffoli_ops(&ops)
    );
    densify(&mut ops);
    ops
}
