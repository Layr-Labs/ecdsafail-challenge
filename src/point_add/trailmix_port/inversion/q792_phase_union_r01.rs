//! Diagnostic only: direction-free numeric quotient/remainder representation exchange.
//! H=F B^-1 for x<2^(n-1), H=F otherwise. The packed Q792 adapters are not changed.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::OperationType as K;

fn controlled_add(c:&mut Circuit,x:&[QReg],r:&[QReg],carry:Option<&QReg>,controls:&[&QReg],dirty:&[&QReg],inverse:bool){
 let owned=c.b.next_qubit;let at=c.b.ops.len();super::metadata_arithmetic5::add(c,x,r,carry,inverse);let ops=c.b.ops.split_off(at);
 let refs:Vec<_>=x.iter().chain(r).chain(carry).collect();let find=|id:u64|*refs.iter().find(|q|q.id()as u64==id).unwrap();
 for op in ops{let mut cs=controls.to_vec();match op.kind{
  K::X=>{}, K::CX=>cs.push(find(op.q_control1.0)), K::CCX=>{cs.push(find(op.q_control1.0));cs.push(find(op.q_control2.0));}, _=>unreachable!(),
 }let target=find(op.q_target.0);assert!(!cs.iter().any(|q|q.id()==target.id()));
  crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder(c,&cs,target,dirty);
 }assert_eq!(owned,c.b.next_qubit);
}

fn emit(c:&mut Circuit,x:&[QReg],r:&[QReg],q:&QReg,dirty:&[&QReg]){
 let n=x.len();assert_eq!(n,r.len());assert!(n>=3&&dirty.len()>=2);let owned=c.b.next_qubit;
 // x's high bit is a stable control because the prefix adds only its lower n-1 bits.
 let high=&x[n-1];c.x(high);
 controlled_add(c,&x[..n-1],&r[..n-1],Some(&r[n-1]),&[q,high],dirty,false);
 c.x(high);
 // A: q ^= [r>=x]. The subtraction/addition pair returns the residual literally.
 c.x(q);super::metadata_arithmetic5::add(c,x,r,None,true);super::metadata_arithmetic5::add(c,x,r,Some(q),false);
 // B: subtract q*x modulo 2^n. The q control is not a residual carry target.
 controlled_add(c,x,r,None,&[q],dirty,true);
 assert_eq!(owned,c.b.next_qubit);
}

pub fn run(){
 use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x26)}}
 let mut cases=0usize;let mut rdomain=0usize;let mut tdomain=0usize;
 for n in 3..=8{
  let mut c=Circuit::new();let x=c.alloc_qreg_bits("x",n);let r=c.alloc_qreg_bits("r",n);let q=c.alloc_qreg("numeric-decision");let d=c.alloc_qreg_bits("existing-dirty",2);let owned=c.b.next_qubit;
  emit(&mut c,&x,&r,&q,&d.iter().collect::<Vec<_>>());let ops=c.into_builder().ops;for o in &ops{o.validate();}
  let size=1usize<<(2*n+3);let m=1usize<<n;let mask=m-1;
  for first in (0..size).step_by(64){let before:Vec<_>=(0..owned).map(|bit|(0..64).fold(0u64,|v,l|v|((((first+l)>>bit&1)as u64)<<l))).collect();let mut after=before.clone();
   for l in 0..64{let z=first+l;let xx=z&mask;let rr=z>>n&mask;let qq=z>>(2*n)&1;
    // Independent low-x extension by paired intervals; high-x uses the explicit map.
    let out=if xx<m/2{if qq==0&&rr>=xx{m+rr-xx}else if qq==1&&rr<m-xx{rr+xx}else{qq*m+rr}}
      else{let b=qq^usize::from(rr>=xx);b*m+rr.wrapping_sub(b*xx)%m};
    if xx!=0&&qq*m+rr<2*xx{let value=qq*m+rr;assert_eq!(out,(value/xx)*m+value%xx);rdomain+=1;}
    if xx<m/2&&rr<xx{assert_eq!(out,rr+qq*xx);tdomain+=1;}
    for bit in 0..=n{let id=n+bit;after[id]=(after[id]&!(1<<l))|(((out>>bit&1)as u64)<<l);}
   }
   let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"union n={n} first={first}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before,"literal inverse");assert_eq!(sim.phase,0);cases+=64;
  }
 }
 let n=256;let mut c=Circuit::new();let x=c.alloc_qreg_bits("x",n);let r=c.alloc_qreg_bits("r",n);let q=c.alloc_qreg("numeric-decision");let d=c.alloc_qreg_bits("existing-dirty",2);let owned=c.b.next_qubit;
 emit(&mut c,&x,&r,&q,&d.iter().collect::<Vec<_>>());let ops=c.into_builder().ops;for o in &ops{o.validate();}
 for batch in 0..32{let mut seed=0x792fabc912u64^batch;let before:Vec<_>=(0..owned).map(|_|{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed}).collect();let mut after=before.clone();
  for l in 0..64{let xx:Vec<_>=x.iter().map(|p|before[p.id()as usize]>>l&1!=0).collect();let mut rr:Vec<_>=r.iter().map(|p|before[p.id()as usize]>>l&1!=0).collect();let mut decision=before[q.id()as usize]>>l&1!=0;
   if decision&&!xx[n-1]{let mut carry=false;for b in 0..n{let a=xx[b];let v=rr[b];rr[b]=a^v^carry;carry=(a&&v)||(a&&carry)||(v&&carry);}}
   let ge=(0..n).rev().find(|&b|rr[b]!=xx[b]).map_or(true,|b|rr[b]);decision^=ge;
   if decision{let mut borrow=false;for b in 0..n{let a=rr[b];let v=xx[b];rr[b]=a^v^borrow;borrow=(!a&&(v||borrow))||(v&&borrow);}}
   for b in 0..n{let id=r[b].id()as usize;after[id]=(after[id]&!(1<<l))|((rr[b]as u64)<<l);}let id=q.id()as usize;after[id]=(after[id]&!(1<<l))|((decision as u64)<<l);
  }
  let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"union width256 batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);cases+=64;
 }
 let t=ops.iter().filter(|o|o.kind==K::CCX).count();
 eprintln!("PHASE_UNION_NATIVE_WIDTH256 T={t} ops={} allocated_by_union=0 extra_direction_bit=false arbitrary_dirty_lenders=2",ops.len());
 eprintln!("PHASE_UNION_NATIVE_PASS lanes={cases} R_domain_lanes={rdomain} T_domain_lanes={tdomain} exhaustive_widths=3..8 width256_lanes=2048 phase=0 inverse=true source_and_dirty_restored=true production_changed=false whole_gain=unmeasured");
}
