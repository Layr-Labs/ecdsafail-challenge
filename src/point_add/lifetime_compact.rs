//! Exact scratch-wire reuse across unconditional demolition/reset boundaries.
//! Must run after all stream-bound transforms. Register wires stay fixed.
use crate::circuit::{Op, OperationType as K, QubitId, NO_QUBIT, NO_BIT};
use std::collections::BTreeSet;

pub fn compact(mut ops: Vec<Op>) -> Vec<Op> {
    let n = ops.iter().flat_map(|o| [o.q_control1, o.q_control2, o.q_target])
        .filter(|q| *q != NO_QUBIT).map(|q| q.0 as usize + 1).max().unwrap_or(0);
    let mut fixed = vec![false; n];
    for o in &ops {
        if o.kind == K::AppendToRegister && o.q_target != NO_QUBIT {
            fixed[o.q_target.0 as usize] = true;
        }
    }
    let mut free: BTreeSet<usize> = (0..n).filter(|&q| !fixed[q]).collect();
    let mut mapping: Vec<Option<usize>> = (0..n).map(|q| fixed[q].then_some(q)).collect();
    let mut depth = 0usize;
    let mut high = 0usize;
    let mut released = 0usize;
    for o in &mut ops {
        let logical_target = o.q_target;
        let releases = matches!(o.kind, K::Hmr | K::R) && depth == 0 && o.c_condition == NO_BIT;
        for q in [&mut o.q_control1, &mut o.q_control2, &mut o.q_target] {
            if *q == NO_QUBIT { continue; }
            let l = q.0 as usize;
            let p = match mapping[l] {
                Some(p) => p,
                None => { let p = free.pop_first().expect("physical wire pool exhausted"); mapping[l] = Some(p); p }
            };
            *q = QubitId(p as u64);
            high = high.max(p + 1);
        }
        if releases && logical_target != NO_QUBIT && !fixed[logical_target.0 as usize] {
            let p = mapping[logical_target.0 as usize].take().unwrap();
            assert!(free.insert(p));
            released += 1;
        }
        if o.kind == K::PushCondition { depth += 1; }
        if o.kind == K::PopCondition { depth = depth.checked_sub(1).expect("unbalanced conditions"); }
    }
    assert_eq!(depth, 0, "unbalanced conditions");
    eprintln!("lifetime_compact: wires {} -> {}, reset boundaries {}", n, high, released);
    ops
}
