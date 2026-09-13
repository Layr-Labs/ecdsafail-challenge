//! Exact NCT factoring; no ancillas and no assumptions about input states.
//! Two commuting Toffolis with one shared control and a common target obey
//! ab XOR ac = a(b XOR c). Conjugate one Toffoli by CX(b,c).
//! The moved gate crosses only independently checked commuting NCT gates.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};

fn reads(op: &Op, q: QubitId) -> bool {
    (matches!(op.kind, K::CX | K::CCX) && op.q_control1 == q)
        || (op.kind == K::CCX && op.q_control2 == q)
}
fn commutes(a: &Op, b: &Op) -> bool {
    !reads(a, b.q_target) && !reads(b, a.q_target)
}
fn factor(a: &Op, b: &Op) -> Option<[Op; 3]> {
    if a.kind != K::CCX || b.kind != K::CCX || a.q_target != b.q_target {
        return None;
    }
    for (common, left) in [(a.q_control1, a.q_control2), (a.q_control2, a.q_control1)] {
        let right = if b.q_control1 == common { b.q_control2 }
            else if b.q_control2 == common { b.q_control1 } else { continue; };
        if left == right { return None; }
        let mut cx = Op::empty(); cx.kind = K::CX;
        cx.q_control1 = left; cx.q_target = right;
        let mut ccx = *b; ccx.q_control1 = common; ccx.q_control2 = right;
        cx.validate(); ccx.validate();
        return Some([cx, ccx, cx]);
    }
    None
}

pub(super) fn apply(ops: &mut Vec<Op>, window: usize) -> usize {
    assert!(ops.iter().all(|op| matches!(op.kind, K::X | K::CX | K::CCX) && op.c_condition == NO_BIT));
    let mut live: Vec<Op> = Vec::with_capacity(ops.len());
    let mut removed_t = 0;
    for op in ops.drain(..) {
        let mut found = None;
        if op.kind == K::CCX {
            for j in (live.len().saturating_sub(window)..live.len()).rev() {
                if let Some(replacement) = factor(&live[j], &op) {
                    found = Some((j, replacement)); break;
                }
                if !commutes(&op, &live[j]) { break; }
            }
        }
        if let Some((j, [first, middle, last])) = found {
            live[j] = first;
            live.insert(j + 1, middle);
            live.insert(j + 2, last);
            removed_t += 1;
        } else { live.push(op); }
    }
    *ops = live;
    removed_t
}

#[cfg(test)]
mod tests {
    use super::*;
    fn gate(k: K, a: u64, b: u64, t: u64) -> Op {
        let mut op = Op::empty(); op.kind = k; op.q_target = QubitId(t);
        if k != K::X { op.q_control1 = QubitId(a); }
        if k == K::CCX { op.q_control2 = QubitId(b); }
        op.validate(); op
    }
    fn eval(ops: &[Op], mut state: u64) -> u64 {
        for op in ops {
            let on = match op.kind {
                K::X => true,
                K::CX => state >> op.q_control1.0 & 1 != 0,
                K::CCX => (state >> op.q_control1.0 & 1) & (state >> op.q_control2.0 & 1) != 0,
                _ => panic!("not NCT"),
            };
            if on { state ^= 1 << op.q_target.0; }
        }
        state
    }
    #[test]
    fn elementary_all_control_orders_all_inputs() {
        for a in 0..4 { for b in 0..4 { for c in 0..4 { for t in 0..4 {
            if [a,b,c,t].iter().enumerate().any(|(i,q)| [a,b,c,t][i+1..].contains(q)) { continue; }
            for swap_a in [false,true] { for swap_b in [false,true] {
                let old = vec![gate(K::CCX,if swap_a{b}else{a},if swap_a{a}else{b},t),
                    gate(K::CCX,if swap_b{c}else{a},if swap_b{a}else{c},t)];
                let mut new=old.clone(); assert_eq!(apply(&mut new,32),1);
                for input in 0..16 { assert_eq!(eval(&old,input),eval(&new,input)); }
            }}
        }}}}
    }
    #[test]
    fn randomized_circuits_all_64_inputs_and_inverse() {
        let mut seed=0xfef05498b1243698u64;
        fn rnd(s: &mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
        let mut savings=0;
        for case in 0..4096 {
            let mut old=Vec::new();
            for _ in 0..96 {
                let mut wires=[0u64,1,2,3,4,5];
                for i in (1..6).rev(){let j=(rnd(&mut seed)%((i+1)as u64))as usize;wires.swap(i,j);}
                let kind=match rnd(&mut seed)%4 {0=>K::X,1=>K::CX,_=>K::CCX};
                old.push(gate(kind,wires[0],wires[1],wires[2]));
            }
            let mut new=old.clone(); savings+=apply(&mut new,1+(case%97));
            assert!(new.iter().filter(|o|o.kind==K::CCX).count()<=old.iter().filter(|o|o.kind==K::CCX).count());
            let inverse:Vec<_>=new.iter().copied().rev().collect();
            for input in 0..64 {
                assert_eq!(eval(&old,input),eval(&new,input),"case={case} input={input}");
                assert_eq!(eval(&inverse,eval(&new,input)),input);
            }
        }
        assert!(savings>1000);eprintln!("Q794_TFACTOR_PASS random_circuits=4096 exhaustive_inputs=262144 savings={savings}");
    }
}
