//! Retain seven exact prefix products through a delimited two-use interval.
//! Both complete 65-record signatures include the overwrite-before-read HMR
//! suffix for bit zero. Eligibility additionally requires seven clean inputs.
use super::{OperationType as K, PendingHmr, Reader, State};
const BANK540: &[u8] = include_bytes!("prefix_retention_bank540.hir");
const BANK531: &[u8] = include_bytes!("prefix_retention_bank531.hir");

pub(super) fn try_apply(state: &mut State, reader: &mut Reader<'_>, qs: usize, cs: usize) -> bool {
    let remaining = &reader.data[reader.at..];
    let (bank, used) = if remaining.starts_with(BANK540) { (540, BANK540.len()) }
        else if remaining.starts_with(BANK531) { (531, BANK531.len()) }
        else { return false; };
    let mut mapped: Vec<_> = (bank..bank+9).chain(559..566).chain([558,576,577])
        .map(|q| state.qmap[qs+q].0).collect();
    mapped.sort_unstable();
    if mapped.windows(2).any(|w| w[0] == w[1]) { return false; }
    assert!(matches!(state.pending_hmr, PendingHmr::None));
    state.flush_raw();
    state.prefix_hits += 1;
    if !(559..566).all(|q| state.proof.qubit_is_zero(state.qmap[qs+q].0 as usize)) {
        state.prefix_unknown += 1;
        return false;
    }
    let q = |i: usize| state.qmap[qs+i];
    let inputs: Vec<_> = (bank..bank+8).map(q).collect();
    let products: Vec<_> = (559..566).map(q).collect();
    let (factor,pool,control,target) = (q(bank+8),q(577),q(558),q(576));
    let bit = state.cmap[cs];
    for j in 0..7 {
        let op=state.raw(K::CCX);
        op.q_control1=if j==0 { inputs[0] } else { products[j-1] };
        op.q_control2=inputs[j+1]; op.q_target=products[j];
    }
    let op=state.raw(K::CCX);op.q_control1=factor;op.q_control2=products[6];op.q_target=pool;
    for &input in &inputs { state.raw(K::X).q_target=input; }
    let op=state.raw(K::CCX);op.q_control1=control;op.q_control2=pool;op.q_target=target;
    for &input in &inputs { state.raw(K::X).q_target=input; }
    let op=state.raw(K::CCX);op.q_control1=factor;op.q_control2=products[6];op.q_target=pool;
    // This surviving measurement kills the classical output difference from
    // the seven removed measurements before any read of their reused bit.
    let op=state.raw(K::Hmr);op.q_target=products[6];op.c_target=bit;
    state.raw(K::PushCondition).c_condition=bit;
    let op=state.raw(K::CZ);op.q_control1=inputs[7];op.q_target=products[5];
    state.raw(K::PopCondition);
    reader.at += used;
    state.prefix_rewrites += 1;
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{BitId,QubitId,NO_BIT};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Outcome(u8);
    impl XofReader for Outcome { fn read(&mut self,b:&mut[u8]) { b.fill(self.0); } }
    fn original(state:&mut State,fixture:&[u8]) {
        let mut r=Reader{data:fixture,at:0};let mut count=0;
        while r.at<r.data.len() {
            let tag=r.byte();let cw=r.uvar();let e=r.uvar();assert_eq!(e,1);
            let cond=if cw==1 {BitId(r.uvar() as u64)} else {assert_eq!(cw,0);NO_BIT};
            if tag==11 {assert_eq!(r.uvar(),0);}
            let nq=r.uvar();assert!(nq<=3);let mut q=[QubitId(0);3];
            for item in &mut q[..nq] {*item=QubitId(r.uvar() as u64);}
            let nc=r.uvar();assert!(nc<=1);let c=if nc==1 {BitId(r.uvar() as u64)} else {NO_BIT};
            if cw==1 {state.raw(K::PushCondition).c_condition=cond;}
            state.emit_leaf(if tag==11 {4} else {tag},&q,nq,c,if tag==11 {0} else {nc});
            if cw==1 {state.raw(K::PopCondition);}
            count+=1;
        }
        assert_eq!(count,65);state.flush_raw();
    }
    #[test]
    fn both_exact_prefix_fixtures_outputs_phase_and_classical_suffix() {
        for (fixture,bank) in [(BANK540,540),(BANK531,531)] {
            let inputs:Vec<_>=(bank..bank+9).chain([558,576,577]).collect();
            for enclosed in [false,true] {
                let mut old=State::new(578,2,&inputs,&[1],true,0);
                let mut new=State::new(578,2,&inputs,&[1],true,0);
                if enclosed {old.raw(K::PushCondition).c_condition=BitId(1);new.raw(K::PushCondition).c_condition=BitId(1);}
                original(&mut old,fixture);
                let mut reader=Reader{data:fixture,at:0};assert!(try_apply(&mut new,&mut reader,0,0));
                assert_eq!(reader.at,fixture.len());assert_eq!(new.prefix_rewrites,1);
                if enclosed {old.raw(K::PopCondition);new.raw(K::PopCondition);}
                old.flush_raw();new.flush_raw();assert!(old.proof.balanced()&&new.proof.balanced());
                for op in old.out.iter().chain(&new.out) {op.validate();}
                for data in 0..4096 {for active in [0,1] {for initial_bit in [0,1] {for outcome in [0,255] {
                    let mut r1=Outcome(outcome);let mut a=Simulator::new(578,4,&mut r1);
                    let mut r2=Outcome(outcome);let mut b=Simulator::new(578,4,&mut r2);
                    for (j,&q) in inputs.iter().enumerate() {a.qubits[q]=(data>>j)&1;b.qubits[q]=(data>>j)&1;}
                    a.bits[0]=initial_bit;b.bits[0]=initial_bit;a.bits[1]=active;b.bits[1]=active;
                    a.apply_iter(old.out.iter());b.apply_iter(new.out.iter());
                    for (x,y) in a.qubits.iter().zip(&b.qubits) {assert_eq!(x&1,y&1);}
                    assert_eq!(a.phase&1,b.phase&1);assert_eq!(a.bits[0]&1,b.bits[0]&1);
                }}}}
            }
            let mut dirty_inputs=inputs.clone();dirty_inputs.push(559);
            let mut dirty=State::new(578,2,&dirty_inputs,&[],true,0);let mut r=Reader{data:fixture,at:0};
            assert!(!try_apply(&mut dirty,&mut r,0,0));assert_eq!(r.at,0);assert_eq!(dirty.prefix_unknown,1);
            // Every byte, including the suffix, is part of the eligibility key.
            for at in 0..fixture.len() {let mut bad=fixture.to_vec();bad[at]^=1;
                let mut s=State::new(578,2,&inputs,&[],true,0);let mut r=Reader{data:&bad,at:0};
                assert!(!try_apply(&mut s,&mut r,0,0));assert_eq!(r.at,0);
            }
        }
    }
    #[test]
    fn shifted_qmap_cmap_and_global_alias_rejection() {
        let inputs:Vec<_>=(531..540).chain([558,576,577]).collect();
        let shifted:Vec<_>=inputs.iter().map(|q|q+1).collect();
        let mut a=State::new(578,2,&inputs,&[],true,0);
        let mut b=State::new(579,3,&shifted,&[],true,0);
        let mut ra=Reader{data:BANK531,at:0};let mut rb=Reader{data:BANK531,at:0};
        assert!(try_apply(&mut a,&mut ra,0,0));assert!(try_apply(&mut b,&mut rb,1,1));
        a.flush_raw();b.flush_raw();assert_eq!(a.out.len(),b.out.len());
        for (mut x,y) in a.out.into_iter().zip(b.out) {
            for q in [&mut x.q_target,&mut x.q_control1,&mut x.q_control2] {
                if *q!=crate::circuit::NO_QUBIT {q.0+=1;}
            }
            for c in [&mut x.c_target,&mut x.c_condition] {if *c!=NO_BIT {c.0+=1;}}
            assert_eq!(x,y);
        }
        let mut alias=State::new(578,2,&inputs,&[],true,0);
        alias.qmap[577]=alias.qmap[576];
        let mut r=Reader{data:BANK531,at:0};assert!(!try_apply(&mut alias,&mut r,0,0));assert_eq!(r.at,0);
    }

}
