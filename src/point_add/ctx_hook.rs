use crate::circuit::{analyze_ops,Op};
#[path="rowhunter_ctx_holds.rs"] mod ctx_holds;
pub fn apply(ops:Vec<Op>,width:usize)->Vec<Op>{
 let (nq,nb,_,_)=analyze_ops(ops.iter());assert_eq!(nq as usize,width);
 assert!(ops.len()<0x8000_0000);let fresh=nb as u64;
 let out=ctx_holds::apply(ops,&ctx_holds::DEFAULT);
 let (after,_,_,_)=analyze_ops(out.iter());assert_eq!(after,nq);
 // The context pass allocates one fresh classical measurement bit and no quantum wires.
 eprintln!("NCOMPILE_ALIAS private=[{}, {}, {}]",fresh,fresh.checked_add(1).unwrap(),fresh.checked_add(2).unwrap());
 out
}
