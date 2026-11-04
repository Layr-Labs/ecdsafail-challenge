use super::*;
use circuit::OperationType as K;
fn gate(k:K,a:u64,b:u64,t:u64)->Op{let mut o=Op::empty();o.kind=k;
 if t!=u64::MAX{o.q_target=QubitId(t);}if b!=u64::MAX{o.q_control1=QubitId(b);}if a!=u64::MAX{o.q_control2=QubitId(a);}o}
fn ccx(a:u64,b:u64,t:u64)->Op{gate(K::CCX,a,b,t)}
fn prefix()->Vec<Op>{let mut v=vec![];for r in 0..4{let mut o=Op::empty();o.kind=K::Register;o.r_target=RegisterId(r);v.push(o);}
 for q in 0..2{let mut o=Op::empty();o.kind=K::AppendToRegister;o.r_target=RegisterId(0);o.q_target=QubitId(q);v.push(o);}v}
fn run(ops:&[Op],input:u64,m:u64)->(Vec<u64>,u64){
 let(nq,nb,_,_)=circuit::analyze_ops(ops.iter());
 // The independent scalar interpreter explicitly supplies every HMR outcome.
 let(mut q,mut bits,mut phase,mut stack)=(vec![0u64;nq as usize],vec![0u64;nb as usize],0u64,vec![]);
 q[0]=input&1;q[1]=(input>>1)&1;
 for o in ops{if o.kind==K::PushCondition{stack.push(bits[o.c_condition.0 as usize]);continue;}if o.kind==K::PopCondition{stack.pop();continue;}
 let active=stack.iter().all(|&v|v!=0)&&(o.c_condition==circuit::NO_BIT||bits[o.c_condition.0 as usize]!=0);if !active{continue;}
 let t=o.q_target.0 as usize;let b=o.q_control1.0 as usize;let a=o.q_control2.0 as usize;
 match o.kind{K::X=>q[t]^=1,K::CX=>q[t]^=q[b],K::CCX=>q[t]^=q[a]&q[b],K::Z=>phase^=q[t],K::CZ=>phase^=q[b]&q[t],K::CCZ=>phase^=q[a]&q[b]&q[t],K::Neg=>phase^=1,
 K::Swap=>q.swap(b,t),K::Hmr=>{phase^=q[t]*m;q[t]=0;bits[o.c_target.0 as usize]=m;},K::R=>{assert_eq!(q[t],0);},K::BitStore0=>bits[o.c_target.0 as usize]=0,K::BitStore1=>bits[o.c_target.0 as usize]=1,K::BitInvert=>bits[o.c_target.0 as usize]^=1,_=>{}}
 }(q,phase)
}
#[test]fn c86_catalog_scalar_and_phase(){let ops=vec![ccx(0,1,2),ccx(0,1,2)];let out=c86_frontier::apply(ops);assert!(out.is_empty());
 let ops=vec![ccx(0,1,2),gate(K::Z,u64::MAX,u64::MAX,2),ccx(0,1,2)];let out=c86_frontier::apply(ops.clone());
 assert_eq!(out.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count(),0);
 for x in 0..4{assert_eq!(run(&ops,x,0),run(&out,x,0));}
}
fn lease_fixture(fix:bool)->Vec<Op>{let mut v=prefix();v.push(ccx(0,1,2));let mut h=gate(K::Hmr,u64::MAX,u64::MAX,2);h.c_target=BitId(0);v.push(h);
 if fix{let mut z=gate(K::CZ,u64::MAX,0,1);z.c_condition=BitId(0);v.push(z);}v.push(ccx(0,1,2));v}
#[test]fn c86_lease_all_inputs_and_phase(){let ops=lease_fixture(true);let out=c86_leases::apply(ops.clone());assert_eq!(out.iter().filter(|o|o.kind==K::CCX).count(),1);
 for x in 0..4{for m in 0..2{assert_eq!(run(&ops,x,m),run(&out,x,m));}}
}
#[test]fn c86_lease_missing_phase_negative(){let ops=lease_fixture(false);assert_eq!(c86_leases::apply(ops.clone()),ops);}
#[test]fn c86_lease_public_receipt_negative(){let mut ops=lease_fixture(true);let mut a=Op::empty();a.kind=K::AppendToRegister;a.r_target=RegisterId(2);a.c_target=BitId(0);ops.insert(4,a);assert_eq!(c86_leases::apply(ops.clone()),ops);}
#[test]fn c86_hold_exact_all_inputs(){let mut ops=prefix();ops.push(ccx(0,1,2));let mut h=gate(K::Hmr,u64::MAX,u64::MAX,2);h.c_target=BitId(0);ops.push(h);
 let mut z=gate(K::CZ,u64::MAX,0,1);z.c_condition=BitId(0);ops.push(z);ops.push(ccx(0,1,2));
 // A spare zero wire is present in the stream but never probabilistically assumed zero.
 let r=gate(K::R,u64::MAX,u64::MAX,3);ops.push(r);
 let out=c86_hold::hold_pass(ops.clone());for x in 0..4{for m in 0..2{let(a,p)=run(&ops,x,m);let(b,q)=run(&out,x,m);assert_eq!((a,p),(b,q));}}
}
