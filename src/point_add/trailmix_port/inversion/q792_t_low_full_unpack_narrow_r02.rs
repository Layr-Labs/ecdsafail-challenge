//! Calendar-pruned reconstruction of overwritten even-T target bits.
//! On g: S<=2, 0<=A<=39, M<=256, C>=1, SM[0..4]=0; rank5 is unfolded.
//! A1 logical t2=0 replaces its arbitrary global-A passenger. A0 is odd.
//! q0 has already been popped into its provided wire. Physical q1 is read
//! once only for S0, with C2's passenger replaced by logical head1.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn normalize<'a>(cs:&[(&'a QReg,bool)])->Option<Vec<(&'a QReg,bool)>>{let mut out:Vec<(&QReg,bool)>=Vec::new();for &(q,v) in cs{if let Some(&(_,old))=out.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return None;}}else{out.push((q,v));}}Some(out)}
fn gate(c:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,d:&[QReg]){if let Some(cs)=normalize(cs){super::length_recompute::mixed_mcx(c,&cs,out,d);}}
pub(super) fn emit(c:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],w1:&[QReg],w2:&[QReg],q0:&QReg,g:&QReg,d:&[QReg],j:usize,inverse:bool,c1:bool){
 assert_eq!(rank.len(),5);assert_eq!(sm.len(),4);assert!(d.len()>=18);let owned=c.b.next_qubit;let at=c.b.ops.len();
 // Use the original calendar A support through the quotient scope. A local
 // arithmetic width is not a bound on the packed quotient address M=A+C.
 let endpoint_possible=super::q792_t_narrow_support_r01::quotient_support(c).map_or(true,|(_,hi)|hi.saturating_mul(2).saturating_sub(7)>=256);
 for shift in 0..=2{if shift%2!=j%2{continue;}let c0=((j>>1)^(j&1))^(shift>>1);let base=vec![(g,true),(&w1[0],false),(&cl[0],c0!=0)];
  let r:Vec<_>=(0..3).map(|k|&w2[(259+k-shift)%259]).collect();let v:Vec<_>=(0..3).map(|k|&w2[258-shift-k]).collect();
  // At the high-A S1/S2 boundary a v input is the zero phase-cargo host.
  // Temporarily park that passenger in SM3; no q1 routing occurs in these
  // shifts. Restore it before arithmetic, so this is not an extra live loan.
  if shift==0&&!c1{
   if endpoint_possible{
    super::q794_t10_quotient::endpoint(c,rank,a,cl,&[(g,true)],&sm[3],d);
    let mut direct=base.clone();direct.extend([(&w1[1],true),(&sm[3],true),(&w2[2],true)]);gate(c,&direct,&sm[2],d);
   }
   let mut cs=base.clone();cs.push((&w1[1],true));if endpoint_possible{cs.push((&sm[3],false));}let ceq=super::q792_t10_dirtyq1_r01::ceq(rank,cl,2);let mut bank=vec![cs.clone()];
   for cube in ceq{let mut correction=cs.clone();correction.extend(cube);if let Some(correction)=normalize(&correction){gate(c,&correction,&sm[2],d);bank.push(correction);}}
   // C1 has virtual q1=0; its physical A+1 site may hold global cargo.
   for cube in super::q792_t10_dirtyq1_r01::ceq(rank,cl,1){let mut correction=cs.clone();correction.extend(cube);if let Some(correction)=normalize(&correction){bank.push(correction);}}
   super::q793_t10_routes_v10::digit_xor(c,rank,a,cl,w1,&sm[2],d,0,&bank,g,&sm[0]);
  }
  // The eleven conceptual inputs have fixed t0=0. q1 appears exactly once
  // in S0/output2, and q2 never occurs: both are dealt with below.
  let inputs=[Some(&w1[1]),Some(&w1[2]),Some(r[0]),Some(r[1]),Some(r[2]),Some(v[0]),Some(v[1]),Some(v[2]),Some(q0),None,None];
  for out in 0..3-shift{
   let mut anf:Vec<_>=(0..2048usize).map(|code|{let t=2*(code&3);let r=code>>2&7;let v=code>>5&7;let q=code>>8&7;((v.wrapping_mul(7usize.wrapping_sub(t*r)).wrapping_sub((q<<shift)*t))>>(out+shift)&1)!=0}).collect();
   for bit in 0..11{for value in 0..2048{if value>>bit&1!=0{anf[value]^=anf[value^(1<<bit)];}}}
   for(term,on)in anf.into_iter().enumerate(){if !on{continue;}if term>>9!=0{assert_eq!((shift,out,term),(0,2,513));continue;}let mut cs=base.clone();if endpoint_possible&&shift==0&&term&12!=0{cs.push((&sm[3],false));}cs.extend((0..9).filter(|&i|term>>i&1!=0).map(|i|(inputs[i].unwrap(),true)));gate(c,&cs,&sm[out],d);if term&2!=0{let mut correction=cs;correction.extend(a.iter().enumerate().map(|(b,q)|(q,b==0)));gate(c,&correction,&sm[out],d);}}
  }
  if endpoint_possible&&shift==0&&!c1{super::q794_t10_quotient::endpoint(c,rank,a,cl,&[(g,true)],&sm[3],d);}

  for out in 0..3-shift{c.cx(&sm[out],r[shift+out]);let mut cs=base.clone();cs.push((r[shift+out],true));gate(c,&cs,&sm[out],d);c.cx(&sm[out],r[shift+out]);}
 }
 if inverse{c.b.ops[at..].reverse();}assert_eq!(c.b.next_qubit,owned);
}
pub fn run(){
 use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x39)}}
 let root=std::path::PathBuf::from(std::env::var_os("Q792_T_LOW_UNPACK_CASES_DIR").expect("case dir"));let mut total=0;let changed_q=std::env::var_os("Q792_T_LOW_UNPACK_CHANGED_Q").is_some();
 for j in 0..4{let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let q=c.alloc_qreg_bits("physical T narrow low unpack r02",557);
  emit(&mut c,&q[..5],&q[5..11],&q[11..17],&q[17..21],&q[21..277],&q[277..536],&q[536],&q[537],&q[538..],j,false,false);let ops=c.into_builder().ops;for op in &ops{op.validate();}
  let data=std::fs::read(root.join(if changed_q{format!("t-low-unpack-changed-q-clock{j}-cases.bin")}else{format!("t-low-unpack-clock{j}-cases.bin")})).unwrap();assert_eq!(data.len()%(144*64),0);
  for(batch,rows)in data.chunks_exact(144*64).enumerate(){let mut before=vec![0u64;557];let mut after=before.clone();for(lane,row)in rows.chunks_exact(144).enumerate(){for w in 0..557{before[w]|=u64::from(row[w/8]>>(w%8)&1)<<lane;after[w]|=u64::from(row[72+w/8]>>(w%8)&1)<<lane;}}
   let mut f=Fixed;let mut sim=Simulator::new(557,0,&mut f);sim.qubits.copy_from_slice(&before);if changed_q{sim.apply_iter(ops.iter().rev());}else{sim.apply_iter(ops.iter());}assert_eq!(sim.qubits,after,"physical unpack j={j} batch={batch}");assert_eq!(sim.phase,0);if changed_q{sim.apply_iter(ops.iter());}else{sim.apply_iter(ops.iter().rev());}assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
  }
  eprintln!("T_LOW_NARROW_UNPACK_PASS j={j} T={} N={} cases={} inverse=true phase=0",ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len(),data.len()/144);
 }eprintln!("T_LOW_NARROW_UNPACK_TOTAL_PASS lanes={total} conditional_SM_loans=3 paid_q1_address=true whole_Q792=false");
}
