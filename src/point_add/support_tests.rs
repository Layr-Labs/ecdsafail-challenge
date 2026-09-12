//! Real HIR emitter and trusted simulator checks for exact-support lowering.
use super::*;
use super::super::clean_and::SupportLowering;
use crate::sim::Simulator;
use sha3::digest::XofReader;

type K = OperationType;
fn gate(kind: K, a: usize, b: usize, target: usize) -> Op {
    let mut op = Op::empty();
    op.kind = kind;
    op.q_target = QubitId(target as u64);
    if matches!(kind, K::CX | K::CZ | K::CCX) { op.q_control1 = QubitId(a as u64); }
    if kind == K::CCX { op.q_control2 = QubitId(b as u64); }
    op
}
fn bit(kind: K) -> Op { let mut op = Op::empty(); op.kind = kind; op.c_target = BitId(0); op }
fn emit(state: &mut State, ops: &[Op]) {
    for op in ops { *state.raw(op.kind) = *op; }
    state.flush_raw();
}
struct Outcome(u8);
impl XofReader for Outcome { fn read(&mut self, bytes: &mut [u8]) { bytes.fill(self.0); } }
fn simulate(ops: &[Op], initial: &[u64], classical: u64, outcome: u8) -> (Vec<u64>, Vec<u64>, u64) {
    let mut rng = Outcome(outcome);
    let mut sim = Simulator::new(initial.len(), 4, &mut rng);
    sim.qubits.copy_from_slice(initial);
    sim.bits[0] = classical;
    sim.apply_iter(ops.iter());
    (sim.qubits.iter().map(|v| v & 1).collect(), sim.bits[..2].iter().map(|v| v & 1).collect(), sim.phase & 1)
}

#[test]
fn support_real_emitter_all_control_relations_conditions_and_arbitrary_targets() {
    // Separate physical controls; correlated values are prepared reversibly.
    // Relations: zero, both one, equal, complement, left one, right one,
    // independent (must remain CCX), complemented independent (also remains).
    for relation in 0..8 {
        let (prepare, inputs, expected) = match relation {
            0 => (vec![gate(K::CX,4,0,2)], vec![3,4,5], [1,0,0]),
            1 => (vec![gate(K::X,0,0,1),gate(K::X,0,0,2)], vec![3,4,5], [0,1,0]),
            2 => (vec![gate(K::CX,4,0,1),gate(K::CX,4,0,2)], vec![3,4,5], [0,0,1]),
            3 => (vec![gate(K::CX,4,0,1),gate(K::CX,4,0,2),gate(K::X,0,0,2)], vec![3,4,5], [1,0,0]),
            4 => (vec![gate(K::X,0,0,1),gate(K::CX,4,0,2)], vec![3,4,5], [0,0,1]),
            5 => (vec![gate(K::CX,4,0,1),gate(K::X,0,0,2)], vec![3,4,5], [0,0,1]),
            6 => (vec![], vec![1,2,3,4,5], [0,0,0]),
            _ => (vec![gate(K::X,0,0,2)], vec![1,2,3,4,5], [0,0,0]),
        };
        // No condition; direct/stack known true; direct/stack known false;
        // direct/stack unknown. Unknown conditions are never optimized here.
        for condition in 0..7 {
            let mut base = prepare.clone();
            if condition == 1 || condition == 2 { base.push(bit(K::BitStore1)); }
            if condition == 3 || condition == 4 { base.push(bit(K::BitStore0)); }
            let stacked = matches!(condition,2|4|6);
            if stacked { let mut push=Op::empty();push.kind=K::PushCondition;push.c_condition=BitId(0);base.push(push); }
            let mut ccx=gate(K::CCX,1,2,3);
            if matches!(condition,1|3|5) { ccx.c_condition=BitId(0); }
            base.push(ccx);
            if stacked { let mut pop=Op::empty();pop.kind=K::PopCondition;base.push(pop); }
            // These later gates must not inherit any preceding lowering action.
            base.push(gate(K::X,0,0,5));
            base.push(gate(K::CZ,3,0,5));
            let expected=if condition<=2 {expected} else {[0,0,0]};
            let mut full=State::new(6,2,&inputs,&[0],true,0);
            emit(&mut full,&base);
            assert_eq!([full.proof.support_dead,full.proof.support_x,full.proof.support_cx],expected,"relation={relation} condition={condition}");
            assert_eq!(full.proof.rewrites,0);
            assert_eq!(full.proof.support_lowering,SupportLowering::Keep);
            assert!(full.proof.balanced());
            full.assert_accounting(base.len(),0);
            for op in &full.out {op.validate();}
            let mut counted=State::new(6,2,&inputs,&[0],false,0);
            emit(&mut counted,&base);
            counted.assert_accounting(base.len(),0);
            assert_eq!(counted.input_hist,full.input_hist);
            assert_eq!(counted.output_hist,full.output_hist);
            assert_eq!(counted.output_ops,full.out.len());
            for mask in 0..(1<<inputs.len()) {
                let mut initial=vec![0;6];
                for (j,&q) in inputs.iter().enumerate(){initial[q]=(mask>>j)&1;}
                for c in [0,1] {for m in [0,255] {
                    assert_eq!(simulate(&base,&initial,c,m),simulate(&full.out,&initial,c,m),"relation={relation} condition={condition} mask={mask} c={c} m={m}");
                }}
            }
        }
    }
}

#[test]
fn support_preserves_old_cleanup_priority_and_updates_original_semantics_once() {
    for retain in [false,true] {
        let mut state=State::new(4,2,&[],&[],retain,0);
        let first=[gate(K::X,0,0,1),gate(K::X,0,0,2),gate(K::CCX,1,2,3)];
        emit(&mut state,&first);
        assert_eq!(state.proof.support_x,1);
        assert!(!state.proof.qubit_is_zero(3));
        emit(&mut state,&[gate(K::X,0,0,3)]);
        assert!(state.proof.qubit_is_zero(3),"lowered X must not be applied twice to proof state");
        state.assert_accounting(4,0);
        // A target equal to the product keeps the incumbent cleanup path.
        emit(&mut state,&[gate(K::X,0,0,3),gate(K::CCX,1,2,3)]);
        assert_eq!(state.proof.rewrites,1);
        assert_eq!(state.proof.support_x,1);
        assert_eq!(state.proof.support_lowering,SupportLowering::Keep);
        assert!(state.proof.qubit_is_zero(3));
        state.assert_accounting(6,0);
        if retain {
            let base=[first[0],first[1],first[2],gate(K::X,0,0,3),gate(K::X,0,0,3),gate(K::CCX,1,2,3)];
            for m in [0,255] {assert_eq!(simulate(&base,&[0;4],0,m),simulate(&state.out,&[0;4],0,m));}
        }
    }
}

#[test]
fn support_preserves_q0_specialization_boundary_and_rejects_aliases() {
    let mut state=State::new(4,2,&[2,3],&[],true,0);
    emit(&mut state,&[gate(K::X,0,0,0),gate(K::CCX,0,2,3)]);
    assert_eq!(state.proof.support_cx,0);
    assert_eq!(state.out.last().unwrap().kind,K::CCX);
    assert_eq!(state.outer_lowered,1);
    for (a,b,t) in [(1,1,3),(1,2,1),(1,2,2)] {
        assert!(std::panic::catch_unwind(|| {
            let mut state=State::new(4,2,&[1,2,3],&[],true,0);
            emit(&mut state,&[gate(K::CCX,a,b,t)]);
        }).is_err());
    }
}

#[test]
fn support_full_accounting_includes_declarations_without_counting_them_as_input() {
    let mut state=State::new(4,2,&[2,3],&[],true,0);
    declare_register(&mut state.out,0,&[QubitId(2)],&[]);
    let declarations=state.out.len();
    assert!(declarations>0);
    emit(&mut state,&[gate(K::CCX,1,2,3)]);
    assert_eq!(state.proof.support_dead,1);
    assert_eq!(state.input_ops,1);
    assert_eq!(state.output_ops,0);
    state.assert_accounting(1,declarations);
}
