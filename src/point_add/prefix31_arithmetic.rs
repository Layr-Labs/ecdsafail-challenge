// Exact canonical arithmetic modulo 31. The addend may also represent 31.
use super::*;
fn mcx(c:&mut Builder,cs:&[QubitId],out:QubitId){
 match cs.len(){0=>c.x(out),1=>c.cx(cs[0],out),2=>c.ccx(cs[0],cs[1],out),n=>{
  let q=c.alloc_qubit();c.ccx(cs[0],cs[1],q);let mut rest=vec![q];rest.extend(&cs[2..n]);mcx(c,&rest,out);c.ccx(cs[0],cs[1],q);c.release_clean(q);
 }}
}
fn inc(c:&mut Builder,r:&[QubitId],q:QubitId){
 if r.len()==1{c.cx(q,r[0]);return;}
 let mut cs=vec![q];for i in 0..r.len()-2{let t=c.alloc_qubit();c.ccx(cs[i],r[i],t);cs.push(t);}
 c.ccx(*cs.last().unwrap(),r[r.len()-2],r[r.len()-1]);
 for i in(1..cs.len()).rev(){c.cx(cs[i],r[i]);c.ccx(cs[i-1],r[i-1],cs[i]);c.release_clean(cs[i]);}c.cx(q,r[0]);
}
pub(super) fn add(c:&mut Builder,a:&[QubitId],b:&[QubitId]){
 assert_eq!(a.len(),5);assert_eq!(b.len(),5);
 let z=c.alloc_qubit();let h=c.alloc_qubit();let mut ax=a.to_vec();ax.push(z);let mut bx=b.to_vec();bx.push(h);
 super::super::super::super::lowroom::ttk_add(c,&ax,&bx);
 c.release_clean(z);let q=c.alloc_qubit();c.cx(h,q);c.cx(q,h);c.release_clean(h);mcx(c,b,q);inc(c,b,q);
 super::super::super::super::width_composition::xor_lt_seed(c,b,a,None,q);
 c.release_clean(q);
}
fn nonzero(c:&mut Builder,r:&[QubitId],q:QubitId){c.x(q);c.x_all(r);mcx(c,r,q);c.x_all(r);}
pub(super) fn neg(c:&mut Builder,r:&[QubitId],ctrl:QubitId){
 let nz=c.alloc_qubit();nonzero(c,r,nz);let q=c.alloc_qubit();c.ccx(ctrl,nz,q);for &v in r{c.cx(q,v);}c.ccx(ctrl,nz,q);c.release_clean(q);nonzero(c,r,nz);c.release_clean(nz);
}
pub(super) fn residue(c:&mut Builder,word:&[QubitId],implicit:Option<QubitId>,out:&[QubitId],inverse:bool){
 let start=c.op_count();let mut bits=Vec::new();let lo=implicit.map(|p|{let q=c.alloc_qubit();c.x(q);c.cx(p,q);bits.push(q);q});bits.extend(word);let width=bits.len();let sign=*bits.last().unwrap();let mut pad=Vec::new();while bits.len()%5!=0{let q=c.alloc_qubit();bits.push(q);pad.push(q);}
 for part in bits.chunks(5){add(c,part,out);}
 let mut sub=c.alloc_qubits(5);let pos=width%5;let keep=sub[pos];sub[pos]=sign;let at=c.op_count();add(c,&sub,out);c.prefix_reverse(at);sub[pos]=keep;for q in sub{c.release_clean(q);}
 for q in pad{c.release_clean(q);}if let(Some(q),Some(p))=(lo,implicit){c.cx(p,q);c.x(q);c.release_clean(q);}if inverse{c.prefix_reverse(start);}
}
pub(super) fn selftest(){
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};let mut h=Shake256::default();h.update(b"mod31-arithmetic");let mut rng=h.finalize_xof();
 for mode in 0..2{let mut c=Builder::new();let a=c.alloc_qubits(5);let b=c.alloc_qubits(5);let q=c.alloc_qubit();let start=c.op_count();if mode==0{add(&mut c,&a,&b);}else{neg(&mut c,&b,q);}let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let cases:Vec<_>=(0..32u64).flat_map(|a|(0..31u64).flat_map(move|b|(0..2u64).map(move|q|(a,b,q)))).collect();
 for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(av,bv,qv))in batch.iter().enumerate(){set(&mut sim,&a,av,lane);set(&mut sim,&b,bv,lane);set(&mut sim,&[q],qv,lane);}sim.apply_iter(ops[start..].iter());for(lane,&(av,bv,qv))in batch.iter().enumerate(){let want=if mode==0{(av+bv)%31}else if qv==0{bv}else{(31-bv)%31};assert_eq!(get(&sim,&b,lane),want,"mode={mode} a={av} b={bv} q={qv}");assert_eq!(get(&sim,&a,lane),av);assert_eq!(get(&sim,&[q],lane),qv);}let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};for i in 0..nq{let w=QubitId(i as u64);if !a.contains(&w)&&!b.contains(&w)&&w!=q{assert_eq!(sim.qubit(w)&mask,0,"scratch mode={mode}");}}assert_eq!(sim.phase&mask,0);}
 println!("MOD31_ARITH PASS mode={mode} cases={} T={}",cases.len(),ccx(&ops[start..]));}
}
