//! Exact folded-control lowering of read-only metadata routing templates.
//! Gather replacements preserve the selected leaf on the caller's domain;
//! surrounding literal inverses restore arbitrary data and all dirty lenders.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{Op,OperationType as K,NO_QUBIT};
#[derive(Clone)]enum Meaning{Gate(Vec<(usize,bool)>,usize),Gather{word:Vec<usize>,offset:usize,root:usize,support:(usize,usize)}}
#[derive(Clone)]struct Macro{ops:Vec<Op>,meaning:Meaning}
thread_local!{static ACTIVE:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};static BANK:std::cell::RefCell<Vec<Macro>>=const{std::cell::RefCell::new(Vec::new())};}
pub(super) fn active()->bool{ACTIVE.with(|x|x.get())}
pub(super) fn begin_gate(c:&Circuit,cs:&[(&QReg,bool)],out:&QReg)->Option<usize>{(active()&&out.id()>=21&&cs.iter().any(|(q,_)|q.id()<21)).then_some(c.b.ops.len())}
pub(super) fn end_gate(c:&Circuit,at:Option<usize>,cs:&[(&QReg,bool)],out:&QReg){if let Some(at)=at{BANK.with(|b|b.borrow_mut().push(Macro{ops:c.b.ops[at..].to_vec(),meaning:Meaning::Gate(cs.iter().map(|(q,v)|(q.id()as usize,*v)).collect(),out.id()as usize)}));}}
pub(super) fn gather(c:&Circuit,ops:&[Op],word:&[QReg],offset:usize,root:&QReg){if active(){BANK.with(|b|b.borrow_mut().push(Macro{ops:ops.to_vec(),meaning:Meaning::Gather{word:word.iter().map(|q|q.id()as usize).collect(),offset,root:root.id()as usize,support:c.q797_a_support.unwrap_or((0,256))}}));}}
fn gate(c:&mut Circuit,q:&[QReg],cs:&[(usize,bool)],target:usize,polarity:usize,pool:&[usize]){
    assert!(target>=21);let mut mask=0usize;let mut value=0usize;let mut external=Vec::new();let mut seen=std::collections::BTreeMap::new();
    for &(id,b)in cs{if let Some(old)=seen.insert(id,b){if old!=b{return;}}if id<21{mask|=1<<id;if b^(polarity>>id&1!=0){value|=1<<id;}}else if !external.iter().any(|(x,_)|*x==id){external.push((id,b));}}
    let d:Vec<_>=pool.iter().copied().filter(|&id|id!=target&&!external.iter().any(|&(x,_)|id==x)).map(|id|q[id-1].borrowed_alias()).collect();let prefix:Vec<_>=external.iter().map(|&(id,b)|(&q[id-1],b)).collect();
    if mask==0{super::length_recompute::mixed_mcx(c,&prefix,&q[target-1],&d);}else{assert!(d.len()>=20,"folded control lender count {}",d.len());super::q792_fold20_predicate_r01::toggle(c,&q[..20],mask,value,&prefix,&q[target-1],&d);}
}
fn gather_lower(c:&mut Circuit,q:&[QReg],word:&[usize],offset:usize,root:usize,support:(usize,usize),pool:&[usize]){
    assert!(word.len()>=256);let mut bank:Vec<Option<usize>>=vec![None;256];let mut used=std::collections::BTreeSet::new();
    for v in 0..256{if v+offset<word.len()&&((support.0..support.1).contains(&v)||v==255)&&!(offset==3&&v==255){let id=word[v+offset];bank[v]=Some(id);assert!(used.insert(id));}}
    let free:Vec<_>=word.iter().copied().filter(|v|!used.contains(v)).collect();let mut free=free.into_iter();for x in &mut bank{if x.is_none(){*x=Some(free.next().unwrap());}}
    let bank:Vec<_>=bank.into_iter().map(|id|&q[id.unwrap()-1]).collect();let d:Vec<_>=pool.iter().map(|&id|q[id-1].borrowed_alias()).collect();let addr=&d[..8];let rest=&d[8..];
    super::q792_fold20_address_r01::translation(c,addr,&bank);super::q792_fold20_address_r01::read_a(c,&q[..20],addr,rest);super::q792_fold20_address_r01::translation(c,addr,&bank);super::q792_fold20_address_r01::read_a(c,&q[..20],addr,rest);
    let root=&q[root-1];if root.id()!=bank[0].id(){c.cx(root,bank[0]);c.cx(bank[0],root);c.cx(root,bank[0]);}
}
fn key(op:&Op)->(u8,u64,u64,u64){(op.kind as u8,op.q_target.0,op.q_control1.0,op.q_control2.0)}
fn lower(source:&[Op],n:usize,pool:&[usize])->Vec<Op>{
    let macros=BANK.with(|b|b.borrow().clone());let mut index=std::collections::BTreeMap::new();
    for m in macros{if m.ops.is_empty(){continue;}for inverse in [false,true]{let mut m=m.clone();if inverse{m.ops.reverse();}index.entry(key(&m.ops[0])).or_insert_with(Vec::new).push((m,inverse));}}
    for values in index.values_mut(){values.sort_by_key(|(m,_)|std::cmp::Reverse(m.ops.len()));values.dedup_by(|(a,ai),(b,bi)|ai==bi&&a.ops==b.ops);}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let q=c.alloc_qreg_bits("fold20.passive.template",n-1);let mut polarity=0usize;let mut at=0;let mut matched=0;let mut gathers=0;
    while at<source.len(){let op=&source[at];if let Some((m,inverse))=index.get(&key(op)).and_then(|xs|xs.iter().find(|(m,_)|source[at..].starts_with(&m.ops))){
        let start=c.b.ops.len();match &m.meaning{Meaning::Gate(cs,target)=>gate(&mut c,&q,cs,*target,polarity,pool),Meaning::Gather{word,offset,root,support}=>{assert_eq!(polarity,0);gather_lower(&mut c,&q,word,*offset,*root,*support,pool);gathers+=1;}}
        if *inverse{c.b.ops[start..].reverse();}at+=m.ops.len();matched+=1;continue;
    }
    assert!(matches!(op.kind,K::X|K::CX|K::CCX));let target=op.q_target.0 as usize;let controls:Vec<_>=[op.q_control1,op.q_control2].into_iter().filter(|&v|v!=NO_QUBIT).map(|v|(v.0 as usize,true)).collect();
    if target<21{assert!(op.kind==K::X,"passive template changed metadata at {at}: {op:?}");polarity^=1<<target;}
    else{gate(&mut c,&q,&controls,target,polarity,pool);}at+=1;
    }
    assert_eq!(polarity,0);let mut ops=c.into_builder().ops;super::shared_optimize::cancel_nct(&mut ops,2048,8);super::shared_optimize::cancel_nct_live(&mut ops,2048);eprintln!("FOLD20_PASSIVE_LOWER old={} new={} macros={matched} gathers={gathers}",source.len(),ops.len());ops
}
pub(super) fn emit(circ:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,it:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],j:usize,kind:usize){
    assert_eq!(m.len(),20);assert_eq!(h.len(),23);let mut temp=Circuit::new();temp.b.count_only=false;temp.b.fiat_hash=None;temp.q797_a_support=circ.q797_a_support;
    let rank=temp.alloc_qreg_bits("r",5);let a=temp.alloc_qreg_bits("a",6);let c=temp.alloc_qreg_bits("c",6);let sm=temp.alloc_qreg_bits("sm",4);let p1v=temp.alloc_qreg("p1");let p2v=temp.alloc_qreg("p2");let itv=temp.alloc_qreg("it");let w1v=temp.alloc_qreg_bits("w1",259);let w2v=temp.alloc_qreg_bits("w2",259);let hv=temp.alloc_qreg_bits("h",23);let n=temp.b.next_qubit as usize;
    BANK.with(|b|b.borrow_mut().clear());ACTIVE.with(|x|x.set(true));
    super::q793_step_r03::passive20_template(&mut temp,&rank,&a,&c,&sm,&p1v,&p2v,&itv,&w1v,&w2v,&hv,j,kind);
    ACTIVE.with(|x|x.set(false));let pool:Vec<_>=hv.iter().chain(std::iter::once(&itv)).map(|q|q.id()as usize).collect();let ops=lower(&temp.into_builder().ops,n,&pool);
    let refs:Vec<_>=m.iter().chain([p1,p2,it]).chain(w1).chain(w2).chain(h).collect();assert_eq!(refs.len(),n-1);
    for mut op in ops{for wire in [&mut op.q_target,&mut op.q_control1,&mut op.q_control2]{if *wire!=NO_QUBIT{let id=refs[wire.0 as usize].id();assert_ne!(id,u32::MAX,"passive selected absent rail");wire.0=id as u64;}}circ.b.ops.push(op);}
}
