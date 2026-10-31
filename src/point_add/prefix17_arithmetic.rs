// Exact canonical arithmetic modulo17; every scratch wire is coherently cleared.
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
fn inc17(c:&mut Builder,r:&[QubitId],q:QubitId,inverse:bool){
 let start=c.op_count();inc(c,&r[..4],q);c.ccx(q,r[4],r[0]);c.x_all(&r[..4]);let mut cs=vec![q];cs.extend(&r[..4]);mcx(c,&cs,r[4]);c.x_all(&r[..4]);if inverse{c.prefix_reverse(start);}
}
fn add_nibble(c:&mut Builder,a:&[QubitId],b:&[QubitId],inverse:bool){
 assert_eq!(a.len(),4);assert_eq!(b.len(),5);let start=c.op_count();let z=c.alloc_qubit();let mut ax=a.to_vec();ax.push(z);
 super::super::super::super::lowroom::ttk_add(c,&ax,b);
 let q=c.alloc_qubit();c.cx(b[4],q);c.x_all(&b[..4]);mcx(c,b,q);c.x_all(&b[..4]);
 c.cx(q,b[4]);let p=c.op_count();inc(c,&b[..4],q);c.prefix_reverse(p);
 super::super::super::super::width_composition::xor_lt_seed(c,b,&ax,None,q);
 c.release_clean(q);c.release_clean(z);if inverse{c.prefix_reverse(start);}
}
pub(super) fn add(c:&mut Builder,a:&[QubitId],b:&[QubitId]){add_nibble(c,&a[..4],b,false);inc17(c,b,a[4],true);}
pub(super) fn residue(c:&mut Builder,word:&[QubitId],implicit:Option<QubitId>,out:&[QubitId],inverse:bool){
 let start=c.op_count();let mut bits=Vec::new();let lo=implicit.map(|p|{let q=c.alloc_qubit();c.x(q);c.cx(p,q);bits.push(q);q});bits.extend(word);let width=bits.len();let sign=*bits.last().unwrap();let mut pad=Vec::new();while bits.len()%4!=0{let q=c.alloc_qubit();bits.push(q);pad.push(q);}
 for(j,part)in bits.chunks(4).enumerate(){add_nibble(c,part,out,j%2!=0);}
 let mut sub=c.alloc_qubits(4);let pos=width%4;let keep=sub[pos];sub[pos]=sign;add_nibble(c,&sub,out,width/4%2==0);sub[pos]=keep;for q in sub{c.release_clean(q);}
 for q in pad{c.release_clean(q);}if let(Some(q),Some(p))=(lo,implicit){c.cx(p,q);c.x(q);c.release_clean(q);}if inverse{c.prefix_reverse(start);}
}
pub(super) fn selftest(){
 use sha3::{Shake256,digest::{Update,ExtendableOutput}};let mut h=Shake256::default();h.update(b"mod17-add");let mut rng=h.finalize_xof();
 for mode in 0..3{let mut c=Builder::new();let a=c.alloc_qubits(5);let b=c.alloc_qubits(5);let q=c.alloc_qubit();let start=c.op_count();if mode==0{add_nibble(&mut c,&a[..4],&b,false);}else if mode==1{inc17(&mut c,&b,q,false);}else{add(&mut c,&a,&b);}let(nq,nb)=c.i13_dims();let ops=c.take_ops();let mut sim=crate::sim::Simulator::new(nq,nb,&mut rng);let cases:Vec<_>=(0..if mode==0{16}else{17}).flat_map(|a|(0..17).flat_map(move|b|(0..2).map(move|q|(a,b,q)))).collect();
 for batch in cases.chunks(64){sim.clear_for_shot();for(lane,&(av,bv,qv))in batch.iter().enumerate(){set(&mut sim,&a,av,lane);set(&mut sim,&b,bv,lane);set(&mut sim,&[q],qv,lane);}sim.apply_iter(ops[start..].iter());for(lane,&(av,bv,qv))in batch.iter().enumerate(){assert_eq!(get(&sim,&b,lane),(bv+if mode==1{qv}else{av})%17,"mode={mode} a={av} b={bv} q={qv}");assert_eq!(get(&sim,&a,lane),av);assert_eq!(get(&sim,&[q],lane),qv);}let mask=if batch.len()==64{u64::MAX}else{(1u64<<batch.len())-1};for i in 0..nq{let w=QubitId(i as u64);if !a.contains(&w)&&!b.contains(&w)&&w!=q{assert_eq!(sim.qubit(w)&mask,0,"scratch mode={mode}");}}assert_eq!(sim.phase&mask,0);}
 println!("MOD17_ADD PASS mode={mode} cases={} T={}",cases.len(),ccx(&ops[start..]));}
}
