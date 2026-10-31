use super::builder::{B,test_cmp_mbu};
use crate::circuit::{analyze_ops,OperationType as K,QubitId,BitId,Op};
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Fixed(u8);impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(self.0);}}

#[test]
fn c43_cmp_predicate_exact(){
 let mut checked=0;let mut negative=0;
 for (n,k) in [(1,1),(2,1),(3,3),(4,6),(5,22),(6,31)] {
  for inv in [false,true] {for guard in 0..4 {
   test_cmp_mbu(true);let mut b=B::new();let u=b.alloc_n(n);let pred=b.alloc();
   let out=b.alloc();let tmp=b.alloc_n(n-1);
   b.begin();b.cmp_compute(&u,k,pred,&tmp);b.cx(pred,out);b.cmp_erase(&u,k,pred,&tmp);
   let r=b.end();let price=b.measure(&r,inv);b.play(&r,inv);
   if guard==0 {eprintln!("C43_CMP n={n} k={k} inverse={inv} expected={price}");}
   let mut ops=vec![];
   if guard!=0 {
    ops.push(Op{kind:K::PushCondition,c_condition:BitId(0),..Op::empty()});
    ops.push(Op{kind:K::PushCondition,c_condition:BitId(1),..Op::empty()});
    ops.push(Op{kind:K::BitInvert,c_target:BitId(0),..Op::empty()});
   }
   ops.extend(b.ops.iter().copied());
   if guard!=0 {for _ in 0..2 {ops.push(Op{kind:K::PopCondition,..Op::empty()});}}
   let(nq,nb,_,_)=analyze_ops(ops.iter());
   for byte in [0,255,170,85] {
    let mut tape=Fixed(byte);let mut s=Simulator::new(nq as usize,(nb as usize).max(2),&mut tape);
    for lane in 0..64 {for j in 0..n {if lane>>j&1!=0{s.qubits[u[j].0 as usize]|=1<<lane;}}}
    s.qubits[out.0 as usize]=0xabcdef1234567890;
    let (a,z)=match guard {0=>(u64::MAX,u64::MAX),1=>(0,u64::MAX),2=>(u64::MAX,u64::MAX),_=>(0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc)};
    s.bits[0]=a;s.bits[1]=z;let active=a&z;let initial=s.qubits.clone();let mut want=initial.clone();
    for lane in 0..64 {if (lane&((1usize<<n)-1))<(k as usize) && active>>lane&1!=0 {want[out.0 as usize]^=1<<lane;}}
    s.apply_iter(ops.iter());assert_eq!(s.qubits,want,"n{n} k{k} inverse{inv} guard{guard} tape{byte}");assert_eq!(s.phase,0);
    checked+=64;
    if guard==0 && byte==255 {
     let bad:Vec<_>=ops.iter().copied().filter(|o|o.kind!=K::Neg).collect();
     let mut tape=Fixed(byte);let mut z=Simulator::new(nq as usize,(nb as usize).max(2),&mut tape);z.qubits=initial;
     z.apply_iter(bad.iter());negative+=z.phase.count_ones() as usize;
    }
   }
  }}
 }
 assert!(negative>0);test_cmp_mbu(true);
 eprintln!("C43_CMP_EXACT cases={checked} missing_constant_phase_detected={negative}");
}

fn cap_program(compact:bool,new:bool,inverse:bool)->(B,super::lilypad::PWalk,Vec<QubitId>,QubitId){
 use super::lilypad::{PWalk,PScr};
 test_cmp_mbu(new);let mut b=B::new();let h=b.alloc_n(7);let log=b.alloc_n(8);
 let e=b.alloc();let sg=b.alloc();let d=if compact {b.alloc_n(1)}else{vec![]};
 let tmp=if compact {vec![]}else{b.alloc_n(8)};
 let sp=if compact {b.alloc_n(4)}else{vec![]};
 let mut clean=vec![e];clean.extend(&d);clean.extend(&tmp);clean.extend(&sp);
 let sc=PScr{e,sg,d,tmp,sp,pool:vec![]};
 let w=PWalk{a:vec![],bb:vec![],q:vec![],h,capq:11,log};
 b.begin();super::lilypad::cap_logic(&mut b,&w,&sc);let r=b.end();
 let price=b.measure(&r,inverse);b.play(&r,inverse);
 let want=if new {if compact{27.5}else{17.5}}else{if compact{33.0}else{21.0}};
 assert_eq!(price,want);(b,w,clean,sg)
}

#[test]
fn c43_cap_mbu_exact(){
 let mut supported=0usize;let mut outside=0usize;
 for compact in [false,true] {
  let (old,w,clean,sg)=cap_program(compact,false,false);
  let (new,_,_,_)=cap_program(compact,true,false);
  let (old_inv,_,_,_)=cap_program(compact,false,true);
  let (new_inv,_,_,_)=cap_program(compact,true,true);
  for byte in [0,255,170,85] {
   for batch in 0..1024 {
    let run=|b:&B,initial:&[u64]|{
     let(nq,nb,_,_)=analyze_ops(b.ops.iter());let mut tape=Fixed(byte);
     let mut s=Simulator::new(nq as usize,(nb as usize).max(1),&mut tape);
     s.qubits.clone_from_slice(initial);s.apply_iter(b.ops.iter());(s.qubits,s.phase)
    };
    let mut initial=vec![0;old.width()as usize];
    for lane in 0..64 {
     let v=batch*64+lane;
     for (j,q)in w.h.iter().chain(w.log.iter()).chain(std::iter::once(&sg)).enumerate(){if v>>j&1!=0 {initial[q.0 as usize]|=1<<lane;}}
    }
    let(oq,op)=run(&old,&initial);let(nq,np)=run(&new,&initial);
    let mut good=!op;for q in &clean {good&=!oq[q.0 as usize];}
    for (a,z)in oq.iter().zip(&nq){assert_eq!((a^z)&good,0,"cap compact{compact} tape{byte} batch{batch}");}
    assert_eq!(np&good,0);
    let(oi,op)=run(&old_inv,&oq);let(ni,np)=run(&new_inv,&oq);
    for ((a,z),want)in oi.iter().zip(&ni).zip(&initial){assert_eq!((a^want)&good,0);assert_eq!((z^want)&good,0);}
    assert_eq!(op&good,0);assert_eq!(np&good,0);
    supported+=good.count_ones()as usize;outside+=64-good.count_ones()as usize;
   }
  }
 }
 test_cmp_mbu(true);
 eprintln!("C43_CAP_MBU_EXACT supported={supported} outside_old_clean_contract={outside} layouts=2 tapes=4 forward_inverse=PASS");
}
