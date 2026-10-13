//! Submission: Frogtail with even-tick digit erasure and average-T carry cleanup.
//! The source-pinned circuit is independent of environment selectors.
mod frogtail_batch;
mod public_square_port;
mod affine_simplify;
mod quadratic_simplify;
mod truth_simplify;
mod two_holder;

fn counts(ops: &[crate::circuit::Op]) -> (usize, u64, f64) {
    use crate::circuit::OperationType as K;
    let mut weight = 1.0;
    let mut stack = vec![];
    let mut native = 0;
    let mut expected = 0.0;
    for (i, op) in ops.iter().enumerate() {
        match op.kind {
            K::PushCondition => {
                stack.push(weight);
                if i > 0 && ops[i - 1].kind == K::Hmr && ops[i - 1].c_target == op.c_condition {
                    weight *= 0.5;
                }
            },
            K::PopCondition => weight = stack.pop().expect("balanced condition stack"),
            K::CCX | K::CCZ => {
                native += 1;
                expected += weight * if op.c_condition == crate::circuit::NO_BIT { 1.0 } else { 0.5 };
            },
            _ => {},
        }
    }
    assert!(stack.is_empty());
    (ops.len(), native, expected)
}

pub fn build() -> Vec<crate::circuit::Op> {
    let mut ops = frogtail_batch::build();
    let before = counts(&ops);
    if std::env::var_os("PROFILE_RAW").is_some() {
        eprintln!("PROFILE_RAW counts={before:?}");
        return ops;
    }
    for pass in 1..=32 {
        let previous = counts(&ops);
        ops = truth_simplify::simplify_products(ops);
        let (next, stats) = two_holder::simplify(ops);
        ops = next;
        eprintln!("TWO_HOLDER_R1 pass={pass} stats={stats:?}");
        let after = counts(&ops);
        eprintln!("POSTPASS_R2 pass={pass} before={previous:?} after={after:?}");
        if previous == after { break; }
    }
    eprintln!("POSTPASS_R2 raw={before:?} final={:?}", counts(&ops));
    ops
}
