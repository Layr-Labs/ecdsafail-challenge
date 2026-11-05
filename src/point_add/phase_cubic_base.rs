//! S0 donor research runtime for checked local phase-edit certificates.
//! Default off. Data, including complete original windows, comes from the phase
// Entry-specific stream configuration.
use crate::circuit::{BitId,Op,OperationType as K,QubitId,RegisterId};
use std::collections::HashMap;
const NONE:u64=u64::MAX;
fn make(v:&[u64])->Op {
    assert_eq!(v.len(),6);
    let mut o=Op::empty();
    o.kind=match v[0] {0=>K::Neg,6=>K::X,7=>K::Z,8=>K::CX,9=>K::CZ,14=>K::CCZ,_=>panic!("phase_cubic: invalid emitted kind")};
    o.q_control2=QubitId(v[1]);o.q_control1=QubitId(v[2]);o.q_target=QubitId(v[3]);
    o.c_target=BitId(v[4]);o.c_condition=BitId(v[5]);o.r_target=RegisterId(NONE);
    o.validate();o
}
fn row(o:&Op)->[u64;6] {[o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0]}
pub fn run(ops:Vec<Op>)->Vec<Op> {
    if !std::env::var("SL_PHASE_CUBIC").is_ok_and(|v|v=="1") {return ops;}
    let fault=std::env::var("SL_PHASE_CUBIC_FAULT").ok().and_then(|v|v.parse::<usize>().ok()).unwrap_or(0);
    let mut edits:HashMap<usize,Vec<Op>>=HashMap::new();
    let mut id=0usize;let mut start=0usize;let mut read=0usize;let mut fix=0usize;let mut end=0usize;
    let mut old:Vec<[u64;6]>=Vec::new();let mut add:Vec<Op>=Vec::new();let mut kept=0usize;
    for line in include_str!("phase_cubic_data.txt").lines() {
        let words:Vec<&str>=line.split_whitespace().collect();if words.is_empty()||words[0].starts_with('#'){continue;}
        match words[0] {
            "BEGIN"=> {let v:Vec<usize>=words[1..].iter().map(|v|v.parse().unwrap()).collect();
                id=v[0];start=v[1];read=v[2];fix=v[3];end=v[4];old.clear();add.clear();}
            "OLD"=> {let v:Vec<u64>=words[1..].iter().map(|v|v.parse().unwrap()).collect();old.push(v.try_into().unwrap());}
            "ADD"=> {let v:Vec<u64>=words[1..].iter().map(|v|v.parse().unwrap()).collect();add.push(make(&v));}
            "END"=> {
                assert_eq!(old.len(),end-start,"phase_cubic: certificate extent");
                for (j,v) in old.iter().enumerate(){assert_eq!(&row(&ops[start+j]),v,"phase_cubic: changed certificate window {} at {}",id,start+j);}
                assert_eq!(ops[start].kind,K::CCX);assert_eq!(ops[read].kind,K::CZ);assert_eq!(ops[fix].kind,K::CZ);
                assert!(!edits.contains_key(&start)&&!edits.contains_key(&fix)&&!edits.contains_key(&read));
                edits.insert(start,vec![]);edits.insert(fix,vec![]);
                let mut v=vec![ops[read].clone()];if fault!=id {v.extend(add.clone());}
                edits.insert(read,v);kept+=1;
                eprintln!("PHASE_CUBIC id={} site={} read={} fix={} added={}{}",id,start,read,fix,add.len(),if fault==id{" FAULT"}else{""});
            }
            _=>panic!("phase_cubic: invalid certificate line"),
        }
    }
    eprintln!("PHASE_CUBIC rewrites={kept}");
    let mut out=Vec::with_capacity(ops.len()+64);
    for (j,o) in ops.into_iter().enumerate(){if let Some(v)=edits.remove(&j){out.extend(v);}else{out.push(o);}}
    out
}
