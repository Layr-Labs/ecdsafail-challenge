use super::*;
include!("fin1_fold_certificate.rs");
#[cfg(test)]thread_local!{static FORCE:std::cell::Cell<Option<bool>>=const{std::cell::Cell::new(None)};}
#[cfg(test)]pub(super)fn force(v:Option<bool>){FORCE.with(|x|x.set(v));}
pub(super)fn selected(mw:usize,fin:usize,ttm:bool,no_esh:bool)->bool{
 if mw!=56||fin!=1||ttm||!no_esh{return false;}
 #[cfg(test)]if let Some(v)=FORCE.with(|x|x.get()){return v;}
 super::super::super::phase_fit::cap()<1234&&cells::cap()<1234
}
fn form(q:&[QubitId],mask:u64)->Lin{let mut v=Lin::k(mask&1!=0);for i in 1..q.len(){if mask>>i&1!=0{v=v.x(&l(q[i]));}}v}
fn offsets(c:&mut Builder,q:&[QubitId],held:&[QubitId]){for(i,&mask)in F1_OFFSETS.iter().enumerate(){lin_xor_into(c,&form(q,mask),held[i]);}}
fn basis(c:&mut Builder,q:&[QubitId],held:&[QubitId],inverse:bool){if inverse{offsets(c,q,held);for &(a,b)in F1_CX.iter().rev(){c.cx(held[a],held[b]);}}else{for &(a,b)in F1_CX{c.cx(held[a],held[b]);}offsets(c,q,held);}}
fn phase(c:&mut Builder,q:&[QubitId],terms:&[(usize,usize)]){for &(a,b)in terms{match(a,b){(0,0)=>{c.cz(q[1],q[1]);c.x(q[1]);c.cz(q[1],q[1]);c.x(q[1]);},(a,0)|(0,a)=>c.cz(q[a],q[a]),(a,b)=>c.cz(q[a],q[b]),}}}
#[allow(clippy::too_many_arguments)]
pub(super)fn fold(c:&mut Builder,acc:&[QubitId],e:[QubitId;3],nm:[QubitId;3],k1:QubitId,k2:QubitId,cw:[QubitId;5],recs:Vec<Rec>,a4:&Lin,a5:&Lin,drop:usize)->Vec<usize>{
 let[c1,c3,c4,c5,c6]=cw;let mut held=vec![c1,c3,c4];for r in &recs{held.push(match r{Rec::And(q,..)|Rec::Maj(q,..)=>*q,Rec::UndoC5=>c5,Rec::UndoC6=>c6});}assert_eq!(held.len(),30);assert_eq!(held.iter().map(|q|q.0).collect::<std::collections::BTreeSet<_>>().len(),30);
 let input:Vec<_>=acc[..6].iter().copied().chain(e).chain(nm).chain([k1,k2]).collect();let q:Vec<_>=std::iter::once(k1).chain(input.iter().copied()).chain(held.iter().copied()).collect();assert_eq!(q.len(),45);
 basis(c,&q,&held,false);
 for &(index,terms)in F1_ERASE{let bit=c.alloc_bit();let target=held[index];c.hmr(target,bit);c.release_clean(target);c.push_condition(bit);if let Some(terms)=terms{phase(c,&q,terms);}else{assert_eq!(index,F1_C3);let aux=maj_wire(c,&l(input[1]),&l(input[7]),&l(held[F1_C1]));lin_cz(c,&Lin::of(&[input[2],aux]),&Lin::of(&[input[8],aux]));c.cz(aux,aux);maj_wire_erase(c,aux,&l(input[1]),&l(input[7]),&l(held[F1_C1]));}c.pop_condition();c.free_bit(bit);}
 let target=super::super::super::phase_fit::cap().min(cells::cap());let fields:Vec<_>=F1_FIELDS.iter().map(|&mask|form(&q,mask)).collect();let add=field_map(&fields[..6],&fields[6..13],&fields[13],&fields[14..],acc.len());let active=c.active_qubits();let(plan,lean,drops)=super::super::super::pingpong::with_phase_cap(Some(target),||fold_plan_d(c,acc.len(),"fin1-core-loan",drop));assert!(!lean);ladder_d(c,acc,&add,6,held[19],&plan,&drops);
 for &(index,linear,products)in F1_REBUILD{let target=held[index];assert!(c.n2_take(target));if index==F1_C3{let aux=maj_wire(c,&l(input[1]),&l(input[7]),&l(held[F1_C1]));lin_and_into(c,target,&Lin::of(&[input[2],aux]),&Lin::of(&[input[8],aux]));c.cx(aux,target);maj_wire_erase(c,aux,&l(input[1]),&l(input[7]),&l(held[F1_C1]));}else{for &(a,b)in products{lin_and_into(c,target,&form(&q,a),&form(&q,b));}lin_xor_into(c,&form(&q,linear),target);}}
 basis(c,&q,&held,true);fold_undo_recs_t(c,recs,acc,a4,a5,[c4,c5,c6],&mut None);let c2=maj_wire(c,&l(acc[1]),&l(e[1]),&l(c1));fold_undo_low_c(c,acc,e,[c1,c2,c3,c4],None);LOAN_ACTIVE.with(|x|x.set(false));eprintln!("FIN1_CORE_LOAN_FOLD\t{}\t{active}\t{target}\t{plan:?}",c.current_phase());plan
}
