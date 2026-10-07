//! Independent 257-bit integer oracle, canonical modular halving and MBU cleanup.
use crate::point_add::trailmix_port::{circuit::Circuit,mod_arith};
use crate::{circuit::{OperationType as K,NO_BIT},sim::Simulator};
use sha3::digest::XofReader;
struct Fixed(u64);fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){for x in b{*x=rnd(&mut self.0)as u8;}}}
pub fn run(){
 std::env::set_var("LOWQ_Q792_EEA","1");let p=[0xfffffffefffffc2fu64,u64::MAX,u64::MAX,u64::MAX];
 let mut rows=vec![[0;4],[1,0,0,0],[2,0,0,0],[p[0]-1,p[1],p[2],p[3]],[p[0]-2,p[1],p[2],p[3]]];
 for i in 0..256{let mut x=[0u64;4];x[i/64]=1u64<<(i%64);rows.push(x);let mut y=x;for w in &mut y{let(old,borrow)=w.overflowing_sub(1);*w=old;if !borrow{break;}}rows.push(y);}
 let mut seed=0x7924a1fe00u64;for _ in 0..4096{let mut x=std::array::from_fn(|_|rnd(&mut seed));if x.iter().rev().cmp(p.iter().rev()).is_ge(){x[3]=0;}rows.push(x);}
 let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let acc=c.alloc_qreg_bits("input",257);let passengers=c.alloc_qreg_bits("arbitrary.passenger",16);mod_arith::mod_halve_canonical_mbu(&mut c,&acc);assert_eq!(c.b.active_qubits,273);let b=c.into_builder();let mut lanes=0;
 for batch in 0..rows.len().div_ceil(64){let mut f=Fixed(0x79200bbu64^batch as u64);let mut sim=Simulator::new(b.next_qubit as usize,b.next_bit as usize,&mut f);let mut expected=vec![0u64;b.next_qubit as usize];let mut seed=0x111792aa00^batch as u64;for q in &passengers{let v=rnd(&mut seed);sim.qubits[q.id()as usize]=v;expected[q.id()as usize]=v;}
  for lane in 0..64{let x=rows[(batch*64+lane)%rows.len()];let mut y=[x[0],x[1],x[2],x[3],0];if x[0]&1!=0{let mut carry=0u128;for i in 0..4{let v=y[i]as u128+p[i]as u128+carry;y[i]=v as u64;carry=v>>64;}y[4]=carry as u64;}for i in 0..4{y[i]=(y[i]>>1)|(y[i+1]<<63);}y[4]>>=1;
   for i in 0..257{if i<256{sim.qubits[acc[i].id()as usize]|=((x[i/64]>>(i%64))&1)<<lane;}expected[acc[i].id()as usize]|=((y[i/64]>>(i%64))&1)<<lane;}}
  for op in &b.ops{if op.kind==K::R{let mask=if op.c_condition==NO_BIT{u64::MAX}else{sim.bit(op.c_condition)};assert_eq!(sim.qubit(op.q_target)&mask,0,"halve dirty reset batch={batch}");}sim.apply_iter(std::iter::once(op));}assert_eq!(sim.phase,0);assert_eq!(sim.qubits,expected,"halve oracle batch={batch}");lanes+=64;
 }
 eprintln!("FOLD20_HALVE_NATIVE_PASS cases={} lanes={lanes} peak={} ops={} independent_integer_oracle=true every_reset_checked=true phase=0",rows.len(),b.peak_qubits,b.ops.len());
}
