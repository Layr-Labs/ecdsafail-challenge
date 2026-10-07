//! Applied ONLY at counter module predicate boundaries, before internal X frames.
//! During counter, Sign is arbitrary on phase00 and equals P1*P2 elsewhere.
//! Thus Sign XOR P2 is zero under P1, and Sign XOR P1 is zero under P2.
//! Normalize only inside the primitive, then restore the original Sign literally.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
struct Loan{owner:usize,p1:QReg,p2:QReg,sign:QReg}
thread_local!{static LOAN:std::cell::RefCell<Option<Loan>>=const{std::cell::RefCell::new(None)};}
pub(super) fn begin(c:&mut Circuit,p1:&QReg,p2:&QReg,sign:&QReg){LOAN.with(|v|{let mut v=v.borrow_mut();assert!(v.is_none());*v=Some(Loan{owner:c as *mut Circuit as usize,p1:p1.borrowed_alias(),p2:p2.borrowed_alias(),sign:sign.borrowed_alias()});});}
pub(super) fn end(){LOAN.with(|v|{assert!(v.borrow_mut().take().is_some());});}
pub(super) fn try_gate(c:&mut Circuit,cs:&[(&QReg,bool)],target:&QReg,dirty:&[QReg])->bool{LOAN.with(|v|{let v=v.borrow();let Some(l)=v.as_ref()else{return false;};if l.owner!=c as *mut Circuit as usize||cs.len()<4||target.id()==l.sign.id()||cs.iter().any(|(q,_)|q.id()==l.sign.id())||dirty.iter().any(|q|q.id()==l.sign.id()){return false;}
 let Some((guard,other))=[(&l.p1,&l.p2),(&l.p2,&l.p1)].into_iter().find(|(g,_)|cs.iter().any(|(q,b)|q.id()==g.id()&&*b))else{return false;};
 if target.id()==l.p1.id()||target.id()==l.p2.id(){return false;}
 let Some(d)=dirty.iter().find(|q|q.id()!=guard.id()&&q.id()!=other.id()&&q.id()!=target.id()&&!cs.iter().any(|(x,_)|x.id()==q.id()))else{return false;};
 let others:Vec<_>=cs.iter().copied().filter(|(q,_)|q.id()!=guard.id()).collect();let mut ids:Vec<_>=cs.iter().map(|(q,_)|q.id()).collect();ids.sort_unstable();if ids.windows(2).any(|x|x[0]==x[1]){return false;}
 c.cx(other,&l.sign);super::conditional_mcx::guarded(c,guard,&others,target,&l.sign,false,d);c.cx(other,&l.sign);true
})}

pub(super) fn mixed_mcx(c:&mut Circuit,cs:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]){if !try_gate(c,cs,target,dirty){super::length_recompute::mixed_mcx(c,cs,target,dirty);}}
pub(super) fn table(c:&mut Circuit,word:&[&QReg],truth:Vec<bool>,prefix:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]){
 let enabled=LOAN.with(|v|v.borrow().as_ref().is_some_and(|l|l.owner==c as *mut Circuit as usize&&prefix.iter().any(|(q,b)|*b&&(q.id()==l.p1.id()||q.id()==l.p2.id()))));
 if !enabled{super::q792_fold20_r01::table(c,word,truth,prefix,target,dirty);return;}
 let at=c.b.ops.len();super::q792_fold20_r01::table(c,word,truth.clone(),prefix,target,dirty);let baseline=c.b.ops.split_off(at);
 let(pol,monomials)=super::metadata_muxlease::swap_terms(truth,word.len());for m in monomials{let mut cs=prefix.to_vec();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,q)|(*q,pol>>i&1==0)));mixed_mcx(c,&cs,target,dirty);}
 let score=|ops:&[crate::circuit::Op]|(ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count(),ops.len());let proposed=score(&c.b.ops[at..]);let old=score(&baseline);if proposed>=old||proposed.1>old.1+old.1/10+8{c.b.ops.truncate(at);c.b.ops.extend(baseline);}
}
