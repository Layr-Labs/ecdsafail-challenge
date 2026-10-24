
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};

const Z: u8 = 0;
const O: u8 = 1;
const U: u8 = 2;

#[derive(Clone, Copy, PartialEq)]
enum Mask {
    All,
    None,
    Part,
}

fn combine(m: Mask, s: u8) -> Mask {
    match (m, s) {
        (Mask::None, _) | (_, Z) => Mask::None,
        (Mask::All, O) => Mask::All,
        _ => Mask::Part,
    }
}

fn flip(s: u8) -> u8 {
    match s {
        Z => O,
        O => Z,
        _ => U,
    }
}

fn x_op(t: u64, cc: BitId) -> Op {
    let mut o = Op::empty();
    o.kind = K::X;
    o.q_target = QubitId(t);
    o.c_condition = cc;
    o.validate();
    o
}

fn cx_op(c: u64, t: u64, cc: BitId) -> Op {
    let mut o = Op::empty();
    o.kind = K::CX;
    o.q_control1 = QubitId(c);
    o.q_target = QubitId(t);
    o.c_condition = cc;
    o.validate();
    o
}

fn z_op(t: u64, cc: BitId) -> Op {
    let mut o = Op::empty();
    o.kind = K::Z;
    o.q_target = QubitId(t);
    o.c_condition = cc;
    o.validate();
    o
}

fn cz_op(a: u64, b: u64, cc: BitId) -> Op {
    let mut o = Op::empty();
    o.kind = K::CZ;
    o.q_control1 = QubitId(a);
    o.q_target = QubitId(b);
    o.c_condition = cc;
    o.validate();
    o
}

fn neg_op(cc: BitId) -> Op {
    let mut o = Op::empty();
    o.kind = K::Neg;
    o.c_condition = cc;
    o.validate();
    o
}

pub(super) fn run(ops: Vec<Op>) -> Vec<Op> {
    let mut nq = 0u64;
    let mut nb = 0u64;
    for o in &ops {
        for q in [o.q_control2.0, o.q_control1.0, o.q_target.0] {
            if q != NO_QUBIT.0 {
                nq = nq.max(q + 1);
            }
        }
        for b in [o.c_target.0, o.c_condition.0] {
            if b != NO_BIT.0 {
                nb = nb.max(b + 1);
            }
        }
    }
    let mut q_in = vec![false; nq as usize];
    let mut b_in = vec![false; nb as usize];
    for o in &ops {
        if o.kind != K::AppendToRegister {
            continue;
        }
        let r = o.r_target.0;
        if (r == 0 || r == 1) && o.q_target.0 != NO_QUBIT.0 {
            q_in[o.q_target.0 as usize] = true;
        }
        if (r == 2 || r == 3) && o.c_target.0 != NO_BIT.0 {
            b_in[o.c_target.0 as usize] = true;
        }
    }
    let mut qs = vec![Z; nq as usize];
    let mut bs = vec![Z; nb as usize];
    for (i, inn) in q_in.iter().enumerate() {
        if *inn {
            qs[i] = U;
        }
    }
    for (i, inn) in b_in.iter().enumerate() {
        if *inn {
            bs[i] = U;
        }
    }

    let n_in = ops.len();
    let mut stack = vec![Mask::All];
    let mut out: Vec<Op> = Vec::with_capacity(ops.len());
    let mut drop_ccx = 0u64;
    let mut down_ccx = 0u64;
    let mut drop_ccz = 0u64;
    let mut down_ccz = 0u64;
    let mut drop_cx = 0u64;

    for o in ops {
        match o.kind {
            K::PushCondition => {
                let bit = bs[o.c_condition.0 as usize];
                let top = *stack.last().unwrap();
                stack.push(combine(top, bit));
                out.push(o);
                continue;
            }
            K::PopCondition => {
                stack.pop();
                if stack.is_empty() {
                    stack.push(Mask::All);
                }
                out.push(o);
                continue;
            }
            K::AppendToRegister | K::Register | K::DebugPrint => {
                out.push(o);
                continue;
            }
            _ => {}
        }

        let top = *stack.last().unwrap();
        let eff = if o.c_condition.0 == NO_BIT.0 {
            top
        } else {
            combine(top, bs[o.c_condition.0 as usize])
        };
        if eff == Mask::None {
            match o.kind {
                K::CCX => drop_ccx += 1,
                K::CCZ => drop_ccz += 1,
                K::CX => drop_cx += 1,
                _ => {}
            }
            continue;
        }

        let cc = o.c_condition;
        let dirty = |cur: u8| if eff == Mask::All { cur } else { U };

        match o.kind {
            K::X => {
                let t = o.q_target.0 as usize;
                qs[t] = dirty(flip(qs[t]));
                out.push(o);
            }
            K::CX => {
                let c = o.q_control1.0 as usize;
                let t = o.q_target.0 as usize;
                match qs[c] {
                    Z => drop_cx += 1,
                    O => {
                        qs[t] = dirty(flip(qs[t]));
                        out.push(x_op(o.q_target.0, cc));
                    }
                    _ => {
                        qs[t] = U;
                        out.push(o);
                    }
                }
            }
            K::CCX => {
                let s2 = qs[o.q_control2.0 as usize];
                let s1 = qs[o.q_control1.0 as usize];
                let t = o.q_target.0 as usize;
                if s2 == Z || s1 == Z {
                    drop_ccx += 1;
                } else if s2 == O && s1 == O {
                    qs[t] = dirty(flip(qs[t]));
                    down_ccx += 1;
                    out.push(x_op(o.q_target.0, cc));
                } else if s2 == O {
                    qs[t] = U;
                    down_ccx += 1;
                    out.push(cx_op(o.q_control1.0, o.q_target.0, cc));
                } else if s1 == O {
                    qs[t] = U;
                    down_ccx += 1;
                    out.push(cx_op(o.q_control2.0, o.q_target.0, cc));
                } else {
                    qs[t] = U;
                    out.push(o);
                }
            }
            K::CCZ => {
                let ids = [o.q_control2.0, o.q_control1.0, o.q_target.0];
                let st = [qs[ids[0] as usize], qs[ids[1] as usize], qs[ids[2] as usize]];
                if st.contains(&Z) {
                    drop_ccz += 1;
                    continue;
                }
                let unk: Vec<u64> = ids
                    .into_iter()
                    .zip(st)
                    .filter(|&(_, s)| s == U)
                    .map(|(id, _)| id)
                    .collect();
                match unk.len() {
                    0 => {
                        down_ccz += 1;
                        out.push(neg_op(cc));
                    }
                    1 => {
                        down_ccz += 1;
                        out.push(z_op(unk[0], cc));
                    }
                    2 => {
                        down_ccz += 1;
                        out.push(cz_op(unk[0], unk[1], cc));
                    }
                    _ => out.push(o),
                }
            }
            K::Swap => {
                let a = o.q_control1.0 as usize;
                let t = o.q_target.0 as usize;
                if eff == Mask::All {
                    qs.swap(a, t);
                } else {
                    qs[a] = U;
                    qs[t] = U;
                }
                out.push(o);
            }
            K::R => {
                let t = o.q_target.0 as usize;
                qs[t] = if eff == Mask::All { Z } else { U };
                out.push(o);
            }
            K::Hmr => {
                let t = o.q_target.0 as usize;
                qs[t] = if eff == Mask::All { Z } else { U };
                bs[o.c_target.0 as usize] = U;
                out.push(o);
            }
            K::BitStore0 => {
                bs[o.c_target.0 as usize] = if eff == Mask::All { Z } else { U };
                out.push(o);
            }
            K::BitStore1 => {
                bs[o.c_target.0 as usize] = if eff == Mask::All { O } else { U };
                out.push(o);
            }
            K::BitInvert => {
                let b = o.c_target.0 as usize;
                bs[b] = dirty(flip(bs[b]));
                out.push(o);
            }
            K::Z => {
                if qs[o.q_target.0 as usize] == Z {
                    continue;
                }
                out.push(o);
            }
            K::CZ => {
                let a = qs[o.q_control1.0 as usize];
                let t = qs[o.q_target.0 as usize];
                if a == Z || t == Z {
                    continue;
                }
                if a == O && t == O {
                    out.push(neg_op(cc));
                } else if a == O {
                    out.push(z_op(o.q_target.0, cc));
                } else if t == O {
                    out.push(z_op(o.q_control1.0, cc));
                } else {
                    out.push(o);
                }
            }
            _ => out.push(o),
        }
    }

    eprintln!(
        "dead_ancilla: ops {n_in} -> {} drop_ccx {drop_ccx} down_ccx {down_ccx} drop_ccz {drop_ccz} down_ccz {down_ccz} drop_cx {drop_cx}",
        out.len()
    );
    out
}
