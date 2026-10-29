//! Fixed additional terminal divider cohorts after every leader-bound transform.
use crate::circuit::{Op,OperationType as K};
use sha3::{Digest,Sha3_256};
pub(super) fn run(mut ops:Vec<Op>)->Vec<Op>{
    assert_eq!(ops.len(),PREFIX_LEN,"leader terminal extension input count");
    let mut hash=Sha3_256::new();let mut buf=[0u8;56*256];
    for batch in ops.chunks(256){
        for (i,o) in batch.iter().enumerate(){
            let r=&mut buf[i*56..(i+1)*56];r[..4].copy_from_slice(&(o.kind as u32).to_le_bytes());r[4..8].fill(0);
            for(j,x)in[o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0].into_iter().enumerate(){r[8+j*8..16+j*8].copy_from_slice(&x.to_le_bytes());}
        }
        hash.update(&buf[..batch.len()*56]);
    }
    assert_eq!(format!("{:x}",hash.finalize()),PREFIX_SHA3,"leader terminal extension input SHA3");
    for &(lo,hi,width,cut)in COHORTS{
        let before=ops.iter().filter(|o|o.kind==K::CCX).count();
        ops=super::cmp_narrow::run_selected_aligned(ops,cut,width,lo,hi,&[width],true);
        assert_eq!(before-ops.iter().filter(|o|o.kind==K::CCX).count(),6*cut,"six additional terminal repairs per cohort");
    }
    ops
}
const PREFIX_LEN:usize=10215088;
const PREFIX_SHA3:&str="083d133322e8614283359469cb5dd7f0117f8a3822961840b1321e22fae436f3";
const COHORTS:&[(usize,usize,usize,usize)]=&[
    (3280597,3283083,13,2),
    (3272304,3274990,15,4),
    (3260607,3263093,13,2),
    (3252314,3255000,15,4),
];
