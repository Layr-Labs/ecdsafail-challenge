//! Three source-bound exact-prefix proved rows, restricted to one computational stream.
//! CCX and its affine CX/X replacement are identical phase-free basis maps
//! on every reachable branch; no measurement or scratch event is changed.
use crate::circuit::{Op,OperationType,QubitId,NO_BIT};
use sha3::{Digest,Sha3_256};
pub(super) fn apply(mut ops:Vec<Op>) -> Vec<Op> {
    // Guard: the state-producing prefix through the last row site (111,717 records) must be byte-identical to the
    // stream the rows were proved on (same SHA3-256 as the 7e2647 / afbbdb2 / 6c70b7 pre-rewrite prefixes).
    assert!(ops.len() > 111717, "LF exact3 stream too short");
    let mut h=Sha3_256::new();
    for o in &ops[..111717] {
        h.update((o.kind as u32).to_le_bytes());h.update(0u32.to_le_bytes());
        for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0] {h.update(v.to_le_bytes());}
    }
    let digest=format!("{:x}",h.finalize());
    assert_eq!(digest,"afdcbc3c58c02c97e6ff61cdcbf1dbc8995d2d14a64997927b5949a637ea4db7", "LF exact3 proof prefix mismatch");
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
