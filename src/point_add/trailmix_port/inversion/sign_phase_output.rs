//! Convert ONLY a declared pure-output Sign-oracle span into its phase.
//! The caller must isolate the inner comparator center (not the full wrapper,
//! whose code/park permutations legitimately read and write Sign).
use crate::circuit::{Op,OperationType as K,QubitId,NO_QUBIT};
pub fn phase_output(ops:&mut[Op],sign:QubitId)->usize {
    let mut converted=0;
    for op in ops {
        assert!(matches!(op.kind,K::X|K::CX|K::CCX));
        assert_ne!(op.q_control1,sign,"phase-oracle target read as control");
        assert_ne!(op.q_control2,sign,"phase-oracle target read as control");
        if op.q_target!=sign {continue;}
        match op.kind {
            K::X=>{op.kind=K::Neg;op.q_target=NO_QUBIT;},
            K::CX=>{op.kind=K::Z;op.q_target=op.q_control1;op.q_control1=NO_QUBIT;},
            K::CCX=>{op.kind=K::CZ;op.q_target=op.q_control2;op.q_control2=NO_QUBIT;},
            _=>unreachable!()
        }
        op.validate();converted+=1;
    }
    assert!(converted>0,"missing declared Sign output");converted
}
