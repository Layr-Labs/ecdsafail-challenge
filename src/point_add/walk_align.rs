//! Research-only measurement coupling to a fixed parent circuit. Anchors are
//! semantic compare-erasure sites, never input-dependent. Only resets proven
//! to act on zero wires may be inserted or deleted between anchors.
use crate::circuit::{Op,OperationType as K,RegisterId,QubitId,NO_BIT,NO_QUBIT};
use std::collections::HashMap;
thread_local!{
 static KEYS:std::cell::RefCell<Vec<String>>=const{std::cell::RefCell::new(Vec::new())};
 static COUNTS:std::cell::RefCell<HashMap<String,usize>>=std::cell::RefCell::new(HashMap::new());
}
pub(crate) fn on()->bool {std::env::var_os("WALK_ALIGN_RECORD").is_some()||std::env::var_os("WALK_ALIGN").is_some()}
pub(crate) fn marker(key:String)->Option<Op>{
 if !on(){return None;}
 let n=COUNTS.with(|cs|{let mut cs=cs.borrow_mut();let n=cs.entry(key.clone()).or_default();let old=*n;*n+=1;old});
 let id=KEYS.with(|v|{let mut v=v.borrow_mut();let id=v.len();v.push(format!("{key}#{n}"));id});
 let mut op=Op::empty();op.kind=K::DebugPrint;op.r_target=RegisterId(4+id as u64);Some(op)
}
pub(crate) fn is_marker(op:&Op)->bool {on()&&op.kind==K::DebugPrint&&op.r_target.0>=4&&op.r_target.0<u64::MAX-1}

pub(crate) fn is_and_marker(op:&Op)->bool {op.kind==K::DebugPrint&&op.r_target.0==3&&op.q_control1!=NO_QUBIT}

fn adjust(out:&mut Vec<Option<Op>>,count:&mut usize,target:usize,eligible:&mut Vec<usize>,zero_at:&mut Option<(usize,QubitId)>,name:&str,protected:usize,mbus:&mut Vec<(usize,usize,Op)>)->(usize,usize){
 let mut removed=0;let mut added=0;
 if *count>target {
   let mut need=*count-target;
   while need>eligible.len(){
    let(h,z,gate)=mbus.pop().unwrap_or_else(||panic!("measurement surplus at {name}: need {need}, zero resets {}, no exact MBU",eligible.len()));
    assert!(h>=protected);assert_eq!(out[h].unwrap().kind,K::Hmr);assert!(matches!(out[z].unwrap().kind,K::CZ|K::Z));
    out[h]=Some(gate);out[z]=None;*count-=1;need-=1;
    eprintln!("WALK_UNITARY_MBU\t{name}\t{h}");
   }
   assert!(eligible.len()>=need,"measurement surplus at {name}: need {need}, proven-zero resets {}",eligible.len());
   for _ in 0..need {let at=eligible.pop().unwrap();assert_eq!(out[at].unwrap().kind,K::R);out[at]=None;*count-=1;removed+=1;}
 }else if *count<target {
   let need=target-*count;let(at,q)=zero_at.expect("no unconditionally zero wire for padding");assert!(at>=protected,"padding would shift an earlier anchor at {name}");
   let mut op=Op::empty();op.kind=K::R;op.q_target=q;op.validate();
   out.splice(at..at,std::iter::repeat_n(Some(op),need));*count+=need;added+=need;
   *zero_at=Some((at+need,q));
 }
 eligible.clear();mbus.clear();(added,removed)
}
pub(crate) fn finish(ops:Vec<Op>)->Vec<Op>{
 if !on(){return ops;}
 let keys=KEYS.with(|v|v.borrow().clone());
 let mut table=HashMap::new();let align=std::env::var("WALK_ALIGN").ok();let mut total=None;
 if let Some(path)=&align {
   for line in (if path=="@parent"{include_str!("walk_data/anchors.tsv").to_string()}else{std::fs::read_to_string(path).unwrap()}).lines(){
     let f:Vec<_>=line.split('\t').collect();
     if f.first()==Some(&"WALK_ANCHOR"){assert_eq!(f.len(),3);assert!(table.insert(f[1].to_string(),f[2].parse::<usize>().unwrap()).is_none());}
     if f.first()==Some(&"WALK_ANCHOR_TOTAL"){total=Some(f[1].parse::<usize>().unwrap());}
   }
 }
 let(nq,_,_,regs)=crate::circuit::analyze_ops(ops.iter());let mut zero=vec![true;nq as usize];
 for r in &regs {for q in r {if let crate::circuit::QubitOrBit::Qubit(q)=q {zero[q.0 as usize]=false;}}}
 let mut zero_at=zero.iter().position(|&z|z).map(|q|(0,QubitId(q as u64)));
 let mut out=Vec::with_capacity(ops.len());let mut count=0;let mut eligible=Vec::new();let mut depth=0usize;let mut anchored=0;let mut added=0;let mut removed=0;
 let mut expect_hmr=false;let mut protected=0usize;let mut mbus=Vec::new();let mut pending_and:Option<Op>=None;let mut pending_h:Option<(usize,Op)>=None;
 for op in ops {
   if is_and_marker(&op){assert!(pending_and.is_none());pending_and=Some(op);continue;}
   if let Some((h,mark))=pending_h.take(){
    if op.c_condition==mark.c_target && ((op.kind==K::CZ&&((op.q_control1==mark.q_control1&&op.q_target==mark.q_control2)||(op.q_control1==mark.q_control2&&op.q_target==mark.q_control1)))||(op.kind==K::Z&&mark.q_control1==mark.q_control2&&op.q_target==mark.q_control1)){
     let mut gate=Op::empty();gate.kind=if mark.q_control1==mark.q_control2{K::CX}else{K::CCX};gate.q_target=mark.q_target;gate.q_control1=mark.q_control1;if gate.kind==K::CCX{gate.q_control2=mark.q_control2;}gate.validate();mbus.push((h,out.len(),gate));
    }
   }
   if let Some(mark)=pending_and.take(){if op.kind==K::Hmr&&op.q_target==mark.q_target&&op.c_target==mark.c_target&&op.c_condition==NO_BIT{pending_h=Some((out.len(),mark));}}
   if is_marker(&op) {
      let key=&keys[(op.r_target.0-4) as usize];
      if let Some(q)=zero.iter().position(|&z|z){zero_at=Some((out.len(),QubitId(q as u64)));}
      if align.is_some(){
        if let Some(&target)=table.get(key){let(a,r)=adjust(&mut out,&mut count,target,&mut eligible,&mut zero_at,key,protected,&mut mbus);added+=a;removed+=r;anchored+=1;}
        else {eprintln!("WALK_ANCHOR_UNMATCHED\t{key}\t{count}");}
      }
      eprintln!("WALK_ANCHOR\t{key}\t{count}");expect_hmr=true;continue;
   }
   if expect_hmr {assert_eq!(op.kind,K::Hmr,"measurement marker was separated from HMR");expect_hmr=false;protected=out.len()+1;}
   let t=op.q_target.0 as usize;
   match op.kind {
    K::PushCondition=>depth+=1,
    K::PopCondition=>depth-=1,
    K::R|K::Hmr=>{
      if op.kind==K::R && zero[t]{eligible.push(out.len());}
      count+=1;
      if depth==0 && op.c_condition==NO_BIT {zero[t]=true;zero_at=Some((out.len()+1,op.q_target));}
    },
    K::X|K::CX|K::CCX=>{zero[t]=false;},
    K::Swap=>{zero[t]=false;zero[op.q_control1.0 as usize]=false;},
    _=>{}
   }
   out.push(Some(op));
 }
 assert_eq!(depth,0);assert!(!expect_hmr);
 if let Some(q)=zero.iter().position(|&z|z){zero_at=Some((out.len(),QubitId(q as u64)));}
 if align.is_some(){let(a,r)=adjust(&mut out,&mut count,total.expect("parent measurement total"),&mut eligible,&mut zero_at,"END",protected,&mut mbus);added+=a;removed+=r;}
 eprintln!("WALK_ANCHOR_TOTAL\t{count}");eprintln!("WALK_ALIGN_RESULT anchors={anchored} resets_added={added} proven_zero_resets_removed={removed}");
 out.into_iter().flatten().collect()
}
