// Content-anchored inherited census rows; each neighbourhood must match uniquely.
use crate::circuit::Op;
use sha3::{Digest, Sha3_256};
use std::collections::HashMap;
const ANCHORS: &str = include_str!("census_anchors.txt");
fn rec(o: &Op) -> [u64;7] {
    [o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]
}
fn hash(ops: &[Op]) -> String {
    let mut h=Sha3_256::new();
    for o in ops {h.update((o.kind as u32).to_le_bytes());h.update([0u8;4]);
        for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0] {h.update(v.to_le_bytes());}}
    format!("{:x}",h.finalize())
}
pub(super) fn run(ops: Vec<Op>) -> Vec<Op> {
    let mut rows=super::census_cut::rows();rows.sort_by_key(|r|r.0);
    let a:Vec<Vec<&str>>=ANCHORS.lines().map(|l|l.split_whitespace().collect()).collect();
    assert_eq!(a.len(),rows.len(),"census one anchor per inherited row");
    let mut by_gate:HashMap<[u64;7],Vec<usize>>=HashMap::new();
    for (e,f) in a.iter().enumerate() {
        assert_eq!(f.len(),10);assert_eq!(f[0].parse::<usize>().unwrap(),rows[e].0);
        let mut r=[0u64;7];for j in 0..7 {r[j]=f[j+3].parse().unwrap();}
        by_gate.entry(r).or_default().push(e);
    }
    let mut pos=vec![Vec::<usize>::new();rows.len()];
    for (i,o) in ops.iter().enumerate() {
        if let Some(es)=by_gate.get(&rec(o)) {for &e in es {
            let k:usize=a[e][1].parse().unwrap();
            if i>=k && i+k<ops.len() && hash(&ops[i-k..i+k+1])==a[e][2] {pos[e].push(i);}
        }}
    }
    let mut mapped=Vec::new();let mut last=None;
    for (e,(old,f)) in rows.into_iter().enumerate() {
        assert_eq!(pos[e].len(),1,"census changed/ambiguous neighbourhood row {} at {}",e,old);
        let i=pos[e][0];assert!(last.is_none_or(|p|p<i),"census row order changed");last=Some(i);
        mapped.push((i,f));
    }
    eprintln!("CENSUS_ANCHORED rows={} moved={}",mapped.len(),mapped.iter().zip(&a).filter(|((i,_),f)|*i!=f[0].parse::<usize>().unwrap()).count());
    super::census_cut::run_rows(ops,mapped)
}
