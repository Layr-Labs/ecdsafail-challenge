//! Three source-bound exact-prefix proved rows, restricted to one computational stream.
//! CCX and its affine CX/X replacement are identical phase-free basis maps
//! on every reachable branch; no measurement or scratch event is changed.
use crate::circuit::{Op,OperationType,QubitId,NO_BIT};
use sha3::{Digest,Sha3_256};
pub(super) fn apply(mut ops:Vec<Op>) -> Vec<Op> {
    assert_eq!(ops.len(), 9445266, "LF exact3 source length mismatch");
    let mut h=Sha3_256::new();
    for o in &ops[..ops.len()-96] {
        h.update((o.kind as u32).to_le_bytes());h.update(0u32.to_le_bytes());
        for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0] {h.update(v.to_le_bytes());}
    }
    let digest=format!("{:x}",h.finalize());
    assert_eq!(digest,"610e5bfb1c54474945c87c980d7e3b6a97db8c271da8df035b5eafc800bf17f8", "LF exact3 computational stream mismatch");
    let mut rows:Vec<(usize,u64,u64,u64,bool,Vec<u64>)>=include_str!("leapfrog_data/q1239_selected_exact3.txt").lines().map(|l| {
        let f:Vec<&str>=l.split_whitespace().collect();
        (f[0].parse().unwrap(),f[1].parse().unwrap(),f[2].parse().unwrap(),f[3].parse().unwrap(),f[4]=="1",f[5].split(',').map(|x|x.parse().unwrap()).collect())
    }).collect();
    rows.sort_by_key(|r|std::cmp::Reverse(r.0));
    for (site,c1,c2,t,one,ws) in rows {
        let o=ops[site];
        assert!(o.kind==OperationType::CCX && o.q_control1.0==c1 && o.q_control2.0==c2 && o.q_target.0==t && o.c_condition==NO_BIT);
        let mut rep=Vec::new();
        if one {let mut o=Op::empty();o.kind=OperationType::X;o.q_target=QubitId(t);rep.push(o);}
        for w in ws {assert_ne!(w,t);let mut o=Op::empty();o.kind=OperationType::CX;o.q_control1=QubitId(w);o.q_target=QubitId(t);rep.push(o);}
        ops.splice(site..site+1,rep);
    }
    ops
}
