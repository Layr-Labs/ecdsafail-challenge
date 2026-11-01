use crate::circuit::{Op, OperationType as K, NO_QUBIT};
use std::collections::HashMap;

type Key = [u64; 5];

fn qubits(o: &Op) -> impl Iterator<Item = u64> + '_ {
    [o.q_control2, o.q_control1, o.q_target]
        .into_iter()
        .filter(|q| *q != NO_QUBIT)
        .map(|q| q.0)
}

fn key(o: &Op) -> Key {
    match o.kind {
        K::CCX => {
            let (a, b) = (o.q_control1.0.min(o.q_control2.0), o.q_control1.0.max(o.q_control2.0));
            [K::CCX as u64, a, b, o.q_target.0, o.c_condition.0]
        }
        _ => {
            let mut s = [o.q_control2.0, o.q_control1.0, o.q_target.0];
            s.sort_unstable();
            [K::CCZ as u64, s[0], s[1], s[2], o.c_condition.0]
        }
    }
}

fn commutes(k: &Key, o: &Op, q: u64) -> bool {
    let xw = matches!(o.kind, K::X | K::CX | K::CCX) && o.q_target.0 == q;
    let read = match o.kind {
        K::X | K::CX | K::CCX => o.q_target.0 != q,
        K::Z | K::CZ | K::CCZ => true,
        _ => return false,
    };
    if k[0] == K::CCX as u64 && k[3] == q { xw } else { read }
}

fn once(v: Vec<Op>) -> (Vec<Op>, usize) {
    let mut keep = vec![true; v.len()];
    let mut cand: HashMap<Key, usize> = HashMap::new();
    let mut byq: HashMap<u64, Vec<Key>> = HashMap::new();
    for (j, o) in v.iter().enumerate() {
        match o.kind {
            K::PushCondition | K::PopCondition | K::BitInvert | K::BitStore0 | K::BitStore1 | K::Hmr => {
                cand.clear();
                byq.clear();
                continue;
            }
            K::Neg | K::DebugPrint | K::Register | K::AppendToRegister => continue,
            _ => {}
        }
        let tk = matches!(o.kind, K::CCX | K::CCZ).then(|| key(o));
        if let Some(k) = tk {
            if let Some(i) = cand.remove(&k) {
                keep[i] = false;
                keep[j] = false;
                continue;
            }
        }
        for q in qubits(o) {
            if let Some(ks) = byq.get_mut(&q) {
                ks.retain(|k| cand.contains_key(k) && (commutes(k, o, q) || cand.remove(k).is_none()));
            }
        }
        if let Some(k) = tk {
            cand.insert(k, j);
            for &q in &k[1..4] {
                byq.entry(q).or_default().push(k);
            }
        }
    }
    let removed = keep.iter().filter(|x| !**x).count();
    let out = v.into_iter().zip(keep).filter_map(|(o, k)| k.then_some(o)).collect();
    (out, removed)
}

pub(super) fn run(mut v: Vec<Op>) -> Vec<Op> {
    let mut total = 0usize;
    let mut rounds = 0u32;
    loop {
        let (next, n) = once(v);
        v = next;
        total += n;
        rounds += 1;
        if n == 0 || rounds == 64 {
            break;
        }
    }
    eprintln!("TOF_CANCEL: removed {total} self-inverse Toffoli ops in {rounds} round(s)");
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{BitId, Op, OperationType, QubitId, NO_BIT, NO_QUBIT};

    fn ccx(a: u64, b: u64, t: u64) -> Op {
        let mut o = Op::empty();
        o.kind = OperationType::CCX;
        o.q_control2 = QubitId(a);
        o.q_control1 = QubitId(b);
        o.q_target = QubitId(t);
        o
    }
    fn ccz(a: u64, b: u64, c: u64) -> Op {
        let mut o = Op::empty();
        o.kind = OperationType::CCZ;
        o.q_control2 = QubitId(a);
        o.q_control1 = QubitId(b);
        o.q_target = QubitId(c);
        o
    }
    fn x(t: u64) -> Op {
        let mut o = Op::empty();
        o.kind = OperationType::X;
        o.q_target = QubitId(t);
        o
    }
    fn cx(c: u64, t: u64) -> Op {
        let mut o = Op::empty();
        o.kind = OperationType::CX;
        o.q_control1 = QubitId(c);
        o.q_target = QubitId(t);
        o
    }
    fn z(t: u64) -> Op {
        let mut o = Op::empty();
        o.kind = OperationType::Z;
        o.q_target = QubitId(t);
        o
    }

    fn kinds(v: &[Op]) -> Vec<OperationType> {
        v.iter().map(|o| o.kind).collect()
    }

    #[test]
    fn adjacent_ccx_pair_cancels() {
        let out = run(vec![ccx(1, 2, 3), ccx(2, 1, 3)]);
        assert!(out.is_empty());
    }

    #[test]
    fn adjacent_ccz_pair_cancels_under_permutation() {
        let out = run(vec![ccz(5, 6, 7), ccz(7, 5, 6)]);
        assert!(out.is_empty());
    }

    #[test]
    fn x_on_ccx_target_commutes() {
        let out = run(vec![ccx(1, 2, 3), x(3), ccx(1, 2, 3)]);
        assert_eq!(kinds(&out), vec![OperationType::X]);
        assert_eq!(out[0].q_target, QubitId(3));
    }

    #[test]
    fn x_on_ccx_control_is_barrier() {
        let a = ccx(1, 2, 3);
        let out = run(vec![a.clone(), x(1), a.clone()]);
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn z_on_ccx_control_commutes() {
        let out = run(vec![ccx(1, 2, 3), z(1), ccx(1, 2, 3)]);
        assert_eq!(kinds(&out), vec![OperationType::Z]);
    }

    #[test]
    fn z_on_ccx_target_is_barrier() {
        let a = ccx(1, 2, 3);
        let out = run(vec![a.clone(), z(3), a.clone()]);
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn nested_uncompute_cancels_in_two_rounds() {
        let out = run(vec![ccx(1, 2, 3), ccx(3, 4, 5), ccx(3, 4, 5), ccx(1, 2, 3)]);
        assert!(out.is_empty());
    }

    #[test]
    fn cx_into_ccx_target_commutes() {
        let out = run(vec![ccx(1, 2, 3), cx(8, 3), ccx(1, 2, 3)]);
        assert_eq!(kinds(&out), vec![OperationType::CX]);
    }

    #[test]
    fn cx_using_ccx_target_as_control_is_barrier() {
        let a = ccx(1, 2, 3);
        let out = run(vec![a.clone(), cx(3, 8), a.clone()]);
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn commuting_toffolis_all_cancel() {
        let out = run(vec![ccx(1, 2, 3), ccx(4, 5, 6), ccx(1, 2, 3), ccx(4, 5, 6)]);
        assert!(out.is_empty());
    }

    #[test]
    fn unrelated_x_preserved() {
        let out = run(vec![x(9), ccx(1, 2, 3), ccx(1, 2, 3), x(9)]);
        assert_eq!(kinds(&out), vec![OperationType::X, OperationType::X]);
    }

    #[test]
    fn different_condition_does_not_cancel() {
        let mut a = ccx(1, 2, 3);
        let mut b = ccx(1, 2, 3);
        a.c_condition = BitId(10);
        b.c_condition = NO_BIT;
        let out = run(vec![a, b]);
        assert_eq!(out.len(), 2);
        let _ = NO_QUBIT;
    }
}
