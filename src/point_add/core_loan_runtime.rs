use super::*;
include!("core_loan_certificate.rs");
#[cfg(test)]thread_local!{static FORCE:std::cell::Cell<Option<bool>>=const{std::cell::Cell::new(None)};}
#[cfg(test)]pub(super)fn force(v:Option<bool>){FORCE.with(|x|x.set(v));}
pub(super)fn selected(c:&Builder,mw:usize,fin:usize,ttm:bool,loan:bool,no_esh:bool)->bool{
 if fin!=0||!no_esh||mw!=56{return false;}
 let global_route=super::super::super::phase_fit::cap()<1234&&cells::cap()<1234;
 if loan&&!global_route{return false;}
 #[cfg(test)]if let Some(v)=FORCE.with(|x|x.get()){return v;}
 let room=cells::cap().saturating_sub(c.active_qubits()as usize)+usize::from(ttm);
 super::super::super::phase_fit::cap()<1234&&room<=10
}
fn feature(q:&[QubitId],mask:u64)->Lin{let mut v=Lin::k(mask&1!=0);for i in 1..q.len(){if mask>>i&1!=0{v=v.x(&l(q[i]));}}v}
fn offset(c:&mut Builder,features:&[QubitId],held:&[QubitId]){for(i,&mask)in CORE_LOAN_OFFSETS.iter().enumerate(){lin_xor_into(c,&feature(features,mask),held[i]);}}
fn basis(c:&mut Builder,features:&[QubitId],held:&[QubitId],inverse:bool){if inverse{offset(c,features,held);}if inverse{for &(a,b)in CORE_LOAN_BASIS_CX.iter().rev(){c.cx(held[a],held[b]);}}else{for &(a,b)in CORE_LOAN_BASIS_CX{c.cx(held[a],held[b]);}}if !inverse{offset(c,features,held);}}
fn phase(c:&mut Builder,features:&[QubitId],terms:&[(usize,usize)]){for &(a,b)in terms{match(a,b){(0,0)=>{let q=features[1];c.cz(q,q);c.x(q);c.cz(q,q);c.x(q);},(a,0)|(0,a)=>c.cz(features[a],features[a]),(a,b)=>c.cz(features[a],features[b]),}}}
#[allow(clippy::too_many_arguments)]
pub(super)fn fold(c:&mut Builder,acc:&[QubitId],e:[QubitId;3],nm:[QubitId;3],k1:QubitId,k2:QubitId,cw:[QubitId;6],recs:Vec<Rec>,a4:&Lin,a5:&Lin,drop:usize)->Vec<usize>{
 let [c1,c2,c3,c4,c5,c6]=cw;let mut held=vec![c1,c2,c3,c4];for r in &recs{held.push(match r{Rec::And(q,..)|Rec::Maj(q,..)=>*q,Rec::UndoC5=>c5,Rec::UndoC6=>c6});}assert_eq!(held.len(),31);assert_eq!(held.iter().map(|q|q.0).collect::<std::collections::BTreeSet<_>>().len(),31);
 c.cx(c5,acc[5]);lin_xor_into(c,a5,acc[5]);c.cx(c4,acc[4]);lin_xor_into(c,a4,acc[4]);c.cx(c3,acc[3]);c.cx(c2,acc[2]);c.cx(e[2],acc[2]);c.cx(c1,acc[1]);c.cx(e[1],acc[1]);c.cx(e[0],acc[0]);
 let features:Vec<_>=std::iter::once(k1).chain(e).chain(nm).chain([k1,k2]).chain(acc[..6].iter().copied()).chain(held.iter().copied()).collect();assert_eq!(features.len(),46);
 basis(c,&features,&held,false);
 let target=super::super::super::phase_fit::cap().min(cells::cap());
 let loan_count=10usize.saturating_sub(target.saturating_sub(c.active_qubits()as usize)).clamp(1,11);
 for &(index,terms)in &CORE_LOAN_ERASE[..loan_count]{let q=held[index];let bit=c.alloc_bit();c.hmr(q,bit);c.release_clean(q);c.push_condition(bit);phase(c,&features,terms);c.pop_condition();c.free_bit(bit);}
 let active=c.active_qubits();
 let fields:Vec<_>=CORE_LOAN_FIELDS.iter().map(|&mask|feature(&features,mask)).collect();let add=field_map(&fields[..6],&fields[6..13],&fields[13],&fields[14..],acc.len());
 let(plan,lean,drops)=super::super::super::pingpong::with_phase_cap(Some(target),||fold_plan_d(c,acc.len(),"core-loan",drop));assert!(!lean,"Core loan must have room without ordinary lean45");
 let before=c.op_count();ladder_d(c,acc,&add,6,held[19],&plan,&drops);
 for &(index,linear,products)in CORE_LOAN_REBUILD{if !CORE_LOAN_ERASE[..loan_count].iter().any(|&(i,_)|i==index){continue;}let q=held[index];assert!(c.n2_take(q),"Measured helper must be free after ladder");for &(a,b)in products{lin_and_into(c,q,&feature(&features,a),&feature(&features,b));}lin_xor_into(c,&feature(&features,linear),q);}
 basis(c,&features,&held,true);
 c.cx(e[0],acc[0]);c.cx(e[1],acc[1]);c.cx(c1,acc[1]);c.cx(e[2],acc[2]);c.cx(c2,acc[2]);c.cx(c3,acc[3]);lin_xor_into(c,a4,acc[4]);c.cx(c4,acc[4]);lin_xor_into(c,a5,acc[5]);c.cx(c5,acc[5]);
 fold_undo_recs_t(c,recs,acc,a4,a5,[c4,c5,c6],&mut None);fold_undo_low_c(c,acc,e,[c1,c2,c3,c4],None);LOAN_ACTIVE.with(|x|x.set(false));
 eprintln!("CORE_LOAN_FOLD\t{}\t{before}\t{active}\t{target}\t{loan_count}\t{plan:?}",c.current_phase());plan
}
