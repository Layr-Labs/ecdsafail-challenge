//! Fixed-point existing exact passes, then shared-control Toffoli merging.
use crate::circuit::{Op,OperationType as K,NO_BIT,NO_QUBIT};
fn nonlinear(o:&Op)->bool{matches!(o.kind,K::CCX|K::CCZ)}
fn pure(o:&Op)->bool{o.c_condition==NO_BIT&&matches!(o.kind,K::X|K::CX|K::CCX|K::Z|K::CZ|K::CCZ|K::Neg|K::Swap)}
fn diag(o:&Op)->bool{matches!(o.kind,K::Z|K::CZ|K::CCZ|K::Neg)}
fn controls(o:&Op,q:crate::circuit::QubitId)->bool{o.q_control1==q||o.q_control2==q}
fn touch(o:&Op,q:crate::circuit::QubitId)->bool{q!=NO_QUBIT&&(o.q_target==q||controls(o,q))}
fn commute(a:&Op,b:&Op)->bool{
    if !pure(a)||!pure(b){return false;}
    if a.kind==K::Swap||b.kind==K::Swap{return [a.q_target,a.q_control1,a.q_control2].into_iter().all(|q|!touch(b,q));}
    if diag(a)&&diag(b){return true;}
    if diag(a){return !touch(a,b.q_target);}
    if diag(b){return !touch(b,a.q_target);}
    !controls(a,b.q_target)&&!controls(b,a.q_target)
}
fn merge(mut ops:Vec<Op>)->Vec<Op>{
    let before=ops.iter().filter(|o|nonlinear(o)).count();let mut out=Vec::with_capacity(ops.len());let mut depth=0usize;let mut hits=0;
    for o in ops.drain(..){
        if o.kind==K::PushCondition{depth+=1;}if o.kind==K::PopCondition{depth=depth.checked_sub(1).unwrap();}
        if depth==0&&o.kind==K::CCX&&o.c_condition==NO_BIT{
            let mut found=None;
            for j in (out.len().saturating_sub(256)..out.len()).rev(){let a:&Op=&out[j];
                if !pure(a){break;}
                if a.kind==K::CCX&&a.q_target==o.q_target{
                    let mut pairs=vec![];for shared in [a.q_control1,a.q_control2]{
                        if controls(&o,shared){let b=if a.q_control1==shared{a.q_control2}else{a.q_control1};let c=if o.q_control1==shared{o.q_control2}else{o.q_control1};pairs.push((shared,b,c));}
                    }
                    if let Some(&(shared,b,c))=pairs.first(){if out[j+1..].iter().all(|g|commute(a,g)){found=Some((j,shared,b,c));break;}}
                }
            }
            if let Some((j,shared,b,c))=found{out.remove(j);if b!=c{
                let mut x=Op::empty();x.kind=K::CX;x.q_control1=b;x.q_target=c;
                let mut t=o;t.q_control1=shared;t.q_control2=c;
                out.extend([x,t,x]);
            }hits+=1;continue;}
        }out.push(o);
    }
    eprintln!("C86_MERGE hits={hits} nonlinear_before={before} nonlinear_after={}",out.iter().filter(|o|nonlinear(o)).count());out
}
pub(crate) fn apply(mut ops:Vec<Op>)->Vec<Op>{
    for round in 0..4{let before=(ops.len(),ops.iter().filter(|o|nonlinear(o)).count());
        ops=super::truth_simplify::simplify_products(ops);
        ops=super::affine_simplify::simplify(ops);
        ops=super::quadratic_simplify::simplify(ops);
        ops=super::truth_simplify::simplify(ops);
        ops=super::interned_witness::witnesses(ops);
        ops=super::mabsorb::absorb(ops);
        ops=merge(ops);
        let after=(ops.len(),ops.iter().filter(|o|nonlinear(o)).count());eprintln!("C86_FIXED round={round} before={before:?} after={after:?}");
        if before==after{break;}
    }ops
}
#[cfg(test)]mod tests{
 use super::*;use crate::circuit::QubitId;
 fn run(g:&Op,mut x:u64,mut p:bool)->(u64,bool){let a=g.q_control2.0;let b=g.q_control1.0;let t=g.q_target.0;
  let bit=|q:u64|(x>>q)&1;match g.kind{K::X=>x^=1<<t,K::CX=>x^=bit(b)<<t,K::CCX=>x^=(bit(a)&bit(b))<<t,K::Z=>p^=bit(t)!=0,K::CZ=>p^=(bit(b)&bit(t))!=0,K::CCZ=>p^=(bit(a)&bit(b)&bit(t))!=0,K::Neg=>p=!p,K::Swap=>{if bit(b)!=bit(t){x^=(1<<b)|(1<<t);}},_=>unreachable!()}(x,p)
 }
 fn gates()->Vec<Op>{let mut gs=vec![Op::empty()];for k in [K::X,K::Z,K::CX,K::CZ,K::Swap,K::CCX,K::CCZ]{
  for t in 0..4{for b in 0..4{for a in 0..4{let mut o=Op::empty();o.kind=k;o.q_target=QubitId(t);
   if matches!(k,K::CX|K::CZ|K::Swap|K::CCX|K::CCZ){if b==t{continue;}o.q_control1=QubitId(b);}else if b!=0{continue;}
   if matches!(k,K::CCX|K::CCZ){if a==t||a==b{continue;}o.q_control2=QubitId(a);}else if a!=0{continue;}gs.push(o);
  }}}}gs
 }
 #[test]fn c86_commutation_predicate_exhaustive(){let gs=gates();for a in &gs{for b in &gs{if commute(a,b){for x in 0..16{let(y,p)=run(a,x,false);let left=run(b,y,p);let(y,p)=run(b,x,false);assert_eq!(left,run(a,y,p));}}}}}
 #[test]fn c86_shared_control_identity_exhaustive(){let mut a=Op::empty();a.kind=K::CCX;a.q_control1=QubitId(0);a.q_control2=QubitId(1);a.q_target=QubitId(3);let mut b=a;b.q_control2=QubitId(2);
  let v=vec![a,b];let out=merge(v.clone());assert_eq!(out.iter().filter(|o|o.kind==K::CCX).count(),1);
  for x in 0..16{let mut l=(x,false);for g in &v{l=run(g,l.0,l.1);}let mut r=(x,false);for g in &out{r=run(g,r.0,r.1);}assert_eq!(l,r);}
 }
}
