use crate::circuit::{Op, OperationType as K, QubitId, NO_QUBIT};

const DEAD: u8 = 0;
const LIVE: u8 = 1;
const TOP: u8 = 2;

fn x_into(st: &mut [u8], t: u64, base: bool) {
    let s = st[t as usize];
    st[t as usize] = if !base {
        TOP
    } else if s == DEAD {
        LIVE
    } else if s == LIVE {
        DEAD
    } else {
        TOP
    };
}

fn step(st: &mut [u8], k: K, c1: u64, c2: u64, t: u64, base: bool) {
    if t == NO_QUBIT.0 {
        return;
    }
    match k {
        K::X => x_into(st, t, base),
        K::CX => match st[c1 as usize] {
            DEAD => {}
            LIVE => x_into(st, t, base),
            _ => st[t as usize] = TOP,
        },
        K::CCX => {
            let (a, b) = (st[c1 as usize], st[c2 as usize]);
            if a == DEAD || b == DEAD {
            } else if a == LIVE && b == LIVE {
                x_into(st, t, base);
            } else {
                st[t as usize] = TOP;
            }
        }
        K::Swap => st.swap(c1 as usize, t as usize),
        K::R | K::Hmr => st[t as usize] = if base { DEAD } else { TOP },
        _ => {}
    }
}

pub(super) fn run(ops: Vec<Op>) -> Vec<Op> {
    let nq = ops
        .iter()
        .flat_map(|o| [o.q_control2.0, o.q_control1.0, o.q_target.0])
        .filter(|&q| q != NO_QUBIT.0)
        .map(|q| q + 1)
        .max()
        .unwrap_or(1) as usize;
    let mut st = vec![DEAD; nq];
    for o in &ops {
        if o.kind == K::AppendToRegister && o.q_target != NO_QUBIT {
            st[o.q_target.0 as usize] = TOP;
        }
    }
    let mut depth = 0usize;
    let (mut n_del, mut n_cx) = (0usize, 0usize);
    let mut out: Vec<Op> = Vec::with_capacity(ops.len());
    for o in ops {
        match o.kind {
            K::PushCondition => {
                depth += 1;
                out.push(o);
                continue;
            }
            K::PopCondition => {
                depth = depth.saturating_sub(1);
                out.push(o);
                continue;
            }
            _ => {}
        }
        let base = depth == 0 && o.c_condition == crate::circuit::NO_BIT;
        let (c1, c2, t) = (o.q_control1.0, o.q_control2.0, o.q_target.0);
        if o.kind == K::CCX {
            let (a, b) = (st[c1 as usize], st[c2 as usize]);
            if a == DEAD || b == DEAD {
                n_del += 1;
                continue;
            }
            if a == LIVE || b == LIVE {
                let c = if a == LIVE { c2 } else { c1 };
                let mut r = o;
                r.kind = K::CX;
                r.q_control1 = QubitId(c);
                r.q_control2 = NO_QUBIT;
                r.validate();
                n_cx += 1;
                step(&mut st, K::CX, c, 0, t, base);
                out.push(r);
                continue;
            }
        }
        step(&mut st, o.kind, c1, c2, t, base);
        out.push(o);
    }
    eprintln!("LATE_CONST del={n_del} cx={n_cx} ops={} qubits={nq}", out.len());
    out
}
