
use crate::circuit::{Op, NO_QUBIT};

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
    let holes: Vec<u64> = (0..=max).filter(|&q| !present[q as usize]).collect();
    let mut hi = ids.len();
    for &hole in &holes {
        while hi > 0 && ids[hi - 1] <= hole {
            hi -= 1;
        }
        if hi == 0 {
            break;
        }
        hi -= 1;
        let donor = ids[hi];
        for op in ops.iter_mut() {
            for q in [&mut op.q_control2.0, &mut op.q_control1.0, &mut op.q_target.0] {
                if *q == donor {
                    *q = hole;
                }
            }
        }
        eprintln!("post_restore densify {donor} -> {hole}");
    }
}

pub(super) fn run(mut ops: Vec<Op>) -> Vec<Op> {
    densify(&mut ops);
    ops
}
