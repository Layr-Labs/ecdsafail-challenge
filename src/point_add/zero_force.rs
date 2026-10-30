//! zero_force: an X measurement (Hmr) of a wire whose value is the same constant on every shot kicks back no phase
//! that depends on the state (phase (-1)^(b V), V constant), so its outcome b can be fixed to 0: the list then runs the
//! b = 0 branch of the original on every shot, and every op under b (the phase fix for b = 1) never runs. The Hmr
//! becomes R (wire 0) or X (wire 1) and a BitStore0 of b, both under the Hmr's own condition. Constant = pscan.rs's value numbering gives the measured value the id ZERO or ONE, a proof on
//! every input (equal ids are equal Boolean functions). Only measurements whose fix region holds Toffoli are forced.
//! Runs on the final stream (after the bound tables), before the nonce tail.
use crate::circuit::{Op, OperationType as K};

pub(super) fn run(ops: Vec<Op>) -> Vec<Op> {
    let sites: Vec<(usize, bool, f64)> = super::pscan::const_measurements(&ops).into_iter().filter(|s| s.2 > 0.0).collect();
    let mut wt = 0f64;
    for &(k, one, w) in &sites {
        eprintln!("ZERO_FORCE hmr {k} wire {} bit {} value {} weight {w:.4}", ops[k].q_target.0, ops[k].c_target.0, one as u8);
        wt += w;
    }
    eprintln!("ZERO_FORCE sites {} weight {wt:.3}", sites.len());
    let mut out: Vec<Op> = Vec::with_capacity(ops.len() + sites.len());
    let mut si = 0;
    for (i, o) in ops.into_iter().enumerate() {
        if si < sites.len() && sites[si].0 == i {
            si += 1;
            assert_eq!(o.kind, K::Hmr);
            // value 0: R (no phase, wire already 0). value 1: R would kick back a random phase, so X (same condition)
            // returns the wire to 0 instead.
            let mut r = o; r.kind = if sites[si - 1].1 { K::X } else { K::R }; r.c_target = crate::circuit::NO_BIT;
            let mut z = Op::empty(); z.kind = K::BitStore0; z.c_target = o.c_target; z.c_condition = o.c_condition;
            r.validate(); z.validate();
            out.push(r); out.push(z);
        } else { out.push(o); }
    }
    out
}
