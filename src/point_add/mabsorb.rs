//! K3a measurement absorption: an exact, generic op-stream post-pass (`K3A_MABSORB=1`; off = byte-identical).
//!
//! An X-basis measurement turns every X-type write into its target into a phase:
//! `CCX(a,b,t); ...; Hmr(t)->m` equals `Hmr(t)->m'` placed BEFORE the write, the write replaced by
//! `CZ(a,b) if m'`, and `m <- m'` where the old `Hmr` stood.  It holds whenever `t` is never READ between the
//! write and the measurement (it may be XOR-written: `X` -> `Neg if m'`, `CX(c,t)` -> `Z(c) if m'`,
//! `CCX(a,b,t)` -> `CZ(a,b) if m'`), because the measurement's phase kick `(-1)^(m*t_final)` factorises over
//! the writes and each factor is applied with the operands' values AT THAT WRITE.  `t` is |0> after the moved
//! measurement, which is what the old one left.  Each rewritten CCX saves one Toffoli.
//!
//! Scope (conservative): every write in the window and both measurements sit at condition depth 0 and carry
//! no per-op condition; the new bit `m'` is fresh (bits are unscored).
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};

pub fn absorb(ops: Vec<Op>) -> Vec<Op> {
    let n = ops.len();
    let mut nb: u64 = 0;
    let mut nq: u64 = 0;
    for op in &ops {
        for b in [op.c_target, op.c_condition] {
            if b != NO_BIT { nb = nb.max(b.0 + 1); }
        }
        for q in [op.q_control1, op.q_control2, op.q_target] {
            if q != NO_QUBIT { nq = nq.max(q.0 + 1); }
        }
    }
    // window[t] = indices of X-type writes into t since its last read; ok[t] = window still valid
    let mut window: Vec<Vec<usize>> = vec![Vec::new(); nq as usize];
    let mut ok: Vec<bool> = vec![true; nq as usize];
    let mut depth = 0usize;
    // rewrites: (writes, hmr index)
    let mut plan: Vec<(Vec<usize>, usize)> = Vec::new();
    let read = |q: QubitId, window: &mut Vec<Vec<usize>>, ok: &mut Vec<bool>| {
        if q != NO_QUBIT {
            window[q.0 as usize].clear();
            ok[q.0 as usize] = true;
        }
    };
    for (i, op) in ops.iter().enumerate() {
        match op.kind {
            K::PushCondition => { depth += 1; continue; }
            K::PopCondition => { depth -= 1; continue; }
            _ => {}
        }
        let t = op.q_target;
        match op.kind {
            K::X | K::CX | K::CCX => {
                if op.kind != K::X { read(op.q_control1, &mut window, &mut ok); }
                if op.kind == K::CCX { read(op.q_control2, &mut window, &mut ok); }
                let ti = t.0 as usize;
                if depth > 0 || op.c_condition != NO_BIT { ok[ti] = false; }
                window[ti].push(i);
            }
            K::CZ => { read(op.q_control1, &mut window, &mut ok); read(t, &mut window, &mut ok); }
            K::CCZ => { read(op.q_control1, &mut window, &mut ok); read(op.q_control2, &mut window, &mut ok); read(t, &mut window, &mut ok); }
            K::Z => { read(t, &mut window, &mut ok); }
            K::Swap => { read(op.q_control1, &mut window, &mut ok); read(t, &mut window, &mut ok); }
            K::Hmr | K::R => {
                let ti = t.0 as usize;
                let has_ccx = window[ti].iter().any(|&j| ops[j].kind == K::CCX);
                if op.kind == K::Hmr && has_ccx && ok[ti] && depth == 0 && op.c_condition == NO_BIT {
                    plan.push((std::mem::take(&mut window[ti]), i));
                }
                window[ti].clear();
                ok[ti] = true;
            }
            _ => {}
        }
    }
    if plan.is_empty() {
        eprintln!("k3a_mabsorb: 0 sites");
        return ops;
    }
    // index rewrites
    let mut before: std::collections::HashMap<usize, Op> = std::collections::HashMap::new(); // insert op before index
    let mut replace: std::collections::HashMap<usize, Vec<Op>> = std::collections::HashMap::new();
    let mut saved = 0usize;
    for (k, (writes, h)) in plan.iter().enumerate() {
        let fresh = BitId(nb + k as u64);
        let t = ops[*h].q_target;
        let m = ops[*h].c_target;
        let mut hm = Op::empty();
        hm.kind = K::Hmr; hm.q_target = t; hm.c_target = fresh;
        hm.validate();
        before.insert(writes[0], hm);
        for &j in writes {
            let w = ops[j];
            let mut p = Op::empty();
            p.c_condition = fresh;
            match w.kind {
                K::X => { p.kind = K::Neg; }
                K::CX => { p.kind = K::Z; p.q_target = w.q_control1; }
                K::CCX => { p.kind = K::CZ; p.q_control1 = w.q_control1; p.q_target = w.q_control2; saved += 1; }
                _ => unreachable!(),
            }
            p.validate();
            replace.insert(j, vec![p]);
        }
        // old measurement: m <- fresh (t is already |0>)
        let mut s0 = Op::empty(); s0.kind = K::BitStore0; s0.c_target = m; s0.validate();
        let mut inv = Op::empty(); inv.kind = K::BitInvert; inv.c_target = m; inv.c_condition = fresh; inv.validate();
        replace.insert(*h, vec![s0, inv]);
    }
    let mut out = Vec::with_capacity(n + 2 * plan.len());
    for (i, op) in ops.into_iter().enumerate() {
        if let Some(h) = before.remove(&i) { out.push(h); }
        match replace.remove(&i) {
            Some(v) => out.extend(v),
            None => out.push(op),
        }
    }
    eprintln!("k3a_mabsorb: {} sites, {} CCX -> CZ-if", plan.len(), saved);
    out
}
