use super::*;
#[path="tests_positive_phase_polynomial.rs"]
mod phase_kernel;

fn scramble(mut z:u64)->u64{z=(z^(z>>30)).wrapping_mul(0xbf58476d1ce4e5b9);z=(z^(z>>27)).wrapping_mul(0x94d049bb133111eb);z^(z>>31)}
fn samples(m:usize)->Vec<U256>{
 let one=U256::from(1);let mask=(one<<m)-one;let mut values=vec![U256::ZERO,one,U256::from(2),U256::from(3),U256::from(4),mask,mask-one];
 for i in 0..m{let p=one<<i;for v in [p,p-one,(p+one)&mask]{if !values.contains(&v){values.push(v);}}}
 for low in [0u64,1,2,u64::MAX]{for high in [0u64,1,2,u64::MAX]{let v=(U256::from(low)+(U256::from(high)<<64))&mask;if !values.contains(&v){values.push(v);}}}
 let mut at=0u64;while values.len()<512{let lo=scramble(at^0x9174a85029bfec63);let hi=scramble(at^0x6408bfe7aaf90151);let top=scramble(at^0x214b61c93505dc84);let v=(U256::from(lo)+(U256::from(hi)<<64)+(U256::from(top)<<128))&mask;if !values.contains(&v){values.push(v);}at+=1;}
 values
}
// Independent full-width schoolbook integer reference (up to258 output bits).
fn square_plus_two(x:U256,width:usize)->Vec<bool>{
 let a=x.as_limbs();let mut words=[0u64;8];
 for i in 0..4{for j in 0..4{
  let term=a[i]as u128*a[j]as u128;let k=i+j;let z=words[k]as u128+(term as u64)as u128;words[k]=z as u64;
  let mut carry=(term>>64)+(z>>64);let mut k=k+1;
  while carry!=0{let z=words[k]as u128+carry;words[k]=z as u64;carry=z>>64;k+=1;}
 }}
 let mut carry=2u128;let mut k=0;while carry!=0{let z=words[k]as u128+carry;words[k]=z as u64;carry=z>>64;k+=1;}
 (0..width).map(|i|((words[i/64]>>(i%64))&1)!=0).collect()
}
fn large_circuit(m:usize,policy:&str,cap:usize,inject_dirty_loan:bool)->(Vec<crate::circuit::Op>,Vec<QubitId>,Vec<QubitId>,usize){
 let mut c=Builder::new();let abi=c.alloc_qubits(512);let classical=c.alloc_bits(512);let x=abi[256..256+m].to_vec();
 let mut output=abi[..(2*m).min(256)].to_vec();if 2*m>256{output.extend(c.alloc_qubits(2*m-256));}
 let mut loan_count=0;
 crate::point_add::pingpong::with_phase_cap(Some(cap),||with_square(&mut c,&x,policy,|c,product|{
  for (&a,&b)in product.iter().zip(&output){c.cx(a,b);}
  // Physically lease every currently free/loaned wire. R before use checks
  // its promised zero through a fresh independent phase coefficient.
  loan_count=c.y42_alloc_state().0.len();let borrowed=c.alloc_qubits(loan_count);
  for(i,&q)in borrowed.iter().enumerate(){if inject_dirty_loan&&i==0{c.x(q);}c.free(q);c.reacquire(q);c.cx(x[0],q);c.cx(x[0],q);}
  for &q in borrowed.iter().rev(){c.free(q);}
 }));
 c.declare_qubit_register(&abi);c.declare_qubit_register(&output);c.declare_bit_register(&classical);
 (c.take_ops(),x,output,loan_count)
}
fn initial(nq:usize,nb:usize,x:&[QubitId],output:&[QubitId],values:&[U256],pattern:u64)->(Vec<u64>,Vec<u64>,Vec<u64>){
 let mut q=vec![0u64;nq];let mut b=vec![0u64;nb];
 for i in 0..512{q[i]=scramble(i as u64^pattern.wrapping_mul(0x731954ec39217ab5));b[i]=scramble(i as u64^pattern.wrapping_mul(0xc6147a8934c00273));}
 for &id in x{q[id.0 as usize]=0;}
 for &id in output.iter().filter(|id|id.0>=512){q[id.0 as usize]=scramble(id.0^pattern);}
 for(lane,value)in values.iter().enumerate(){for(i,&id)in x.iter().enumerate(){q[id.0 as usize]|=u64::from(value.bit(i))<<lane;}}
 let mut expected=q.clone();for(lane,value)in values.iter().enumerate(){for(i,bit)in square_plus_two(*value,output.len()).iter().enumerate(){if *bit{expected[output[i].0 as usize]^=1u64<<lane;}}}
 (q,b,expected)
}
#[test]fn uniform_positive_large_native_contracts(){
 prepare();let mut cases=0usize;
 for m in [64,65,66,128,129]{let values=samples(m);for policy in ["SQ_A_POLICY","SQ_B_POLICY","SQ_C_POLICY"]{for cap in [1267]{
  let(ops,x,output,loans)=large_circuit(m,policy,cap,false);let(nq,nb,_,_)=analyze_ops(ops.iter());
  assert!(loans>0);
  for pattern in 0..32{for chunk in values.chunks(64){let(q,b,expected)=initial(nq as usize,nb as usize,&x,&output,chunk,pattern);let mut tape=Tape{seed:pattern,at:0};let mut sim=Simulator::new(nq as usize,nb as usize,&mut tape);sim.qubits.clone_from(&q);sim.bits.clone_from(&b);sim.apply_iter(ops.iter());
   let mask=if chunk.len()==64{u64::MAX}else{(1u64<<chunk.len())-1};
   for(i,(&got,&want))in sim.qubits.iter().zip(&expected).enumerate(){assert_eq!(got&mask,want&mask,"large-q m={m} policy={policy} cap={cap} pattern={pattern} q={i}");}
   for i in 0..512{assert_eq!(sim.bits[i]&mask,b[i]&mask,"classicalABI i={i}");}
   assert_eq!(sim.phase&mask,0,"large-phase m={m} policy={policy} cap={cap} pattern={pattern}");cases+=chunk.len();
  }}
  eprintln!("POSITIVE_LARGE_NATIVE m={m} policy={policy} cap={cap} samples={} MR_patterns=32 borrowed_wires={loans} ops={} touched_q={nq} all_q_and_classical_ABI_and_phase=PASS scored=false",values.len(),ops.len());
 }}}
 eprintln!("POSITIVE_LARGE_SUITE native_cases={cases} score=NONE");
}
#[test]fn uniform_positive_large_all_measurement_outcomes(){
 prepare();let mut proved=0;
 for m in [64,65,66,128,129]{let values=samples(m);for policy in ["SQ_A_POLICY","SQ_B_POLICY","SQ_C_POLICY"]{for cap in [1267]{
  let(ops,x,output,_)=large_circuit(m,policy,cap,false);let(nq,nb,_,_)=analyze_ops(ops.iter());
  for pattern in [0,1]{for(batch,chunk)in values.chunks(64).enumerate(){let(q,b,expected)=initial(nq as usize,nb as usize,&x,&output,chunk,pattern);
   let a=phase_kernel::audit(&ops,&q,&b).unwrap_or_else(|e|panic!("positive exact symbolic m={m} policy={policy} cap={cap} pattern={pattern} batch={batch}: {e}"));
   assert_eq!(a.qubits,expected);proved+=chunk.len();
  }}eprintln!("POSITIVE_EXACT_ALL_MR m={m} policy={policy} cap={cap} fixed_inputs=512 dirty_ABI_patterns=2 exact_ALL_MR=PASS");
 }}}
 eprintln!("POSITIVE_EXACT_ALL_MR_SUITE proved_fixed_input_layout_cases={proved} inconclusive_fixtures=0 global_input_proof=false score=NONE");
}
#[test]fn uniform_positive_large_dirty_loan_phase_fault(){
 prepare();let values=vec![U256::ZERO;64];let(ops,x,output,loans)=large_circuit(64,"SQ_B_POLICY",1267,true);assert!(loans>0);let(nq,nb,_,_)=analyze_ops(ops.iter());let(q,b,expected)=initial(nq as usize,nb as usize,&x,&output,&values,0);
 let e=phase_kernel::audit(&ops,&q,&b).unwrap_err();assert!(e.starts_with("nonzero phase polynomial"),"{e}");
 let mut tape=Tape{seed:0,at:0};let mut sim=Simulator::new(nq as usize,nb as usize,&mut tape);sim.qubits.clone_from(&q);sim.bits.clone_from(&b);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,expected);assert_eq!(sim.phase,0);
 eprintln!("POSITIVE_LARGE_FAULT clean_values_and_zero_MR_native_pass_but_ALL_MR_phase_rejects=true");
}
#[test]fn inspect_positive_large_first_phase_measurement(){
 prepare();let(ops,_,_,_)=large_circuit(128,"SQ_A_POLICY",1200,false);let mut measurement=0;
 for(at,op)in ops.iter().enumerate(){if matches!(op.kind,crate::circuit::OperationType::R|crate::circuit::OperationType::Hmr){
  if measurement==3862{eprintln!("FIRST_PHASE_MEASUREMENT id={measurement} at={at} kind={:?} q={} c_target={} c_condition={}",op.kind,op.q_target.0,op.c_target.0,op.c_condition.0);
   for i in at.saturating_sub(8)..(at+9).min(ops.len()){let o=&ops[i];eprintln!("FIRST_PHASE_NEIGHBOR at={i} kind={:?} a={} b={} t={} cb={} cond={}",o.kind,o.q_control1.0,o.q_control2.0,o.q_target.0,o.c_target.0,o.c_condition.0);}
  }measurement+=1;
 }}
}

#[test]fn inspect_positive_cross2_remaining_phase(){
 prepare();let m=128;let values=samples(m);let(ops,x,output,_)=large_circuit(m,"SQ_A_POLICY",1200,false);let(nq,nb,_,_)=analyze_ops(ops.iter());
 for (batch,chunk)in values.chunks(64).enumerate(){let(q,b,expected)=initial(nq as usize,nb as usize,&x,&output,chunk,1);
  let mut tape=Tape{seed:1,at:0};let mut sim=Simulator::new(nq as usize,nb as usize,&mut tape);sim.qubits.clone_from(&q);sim.bits.clone_from(&b);sim.apply_iter(ops.iter());
  eprintln!("REMAINING_PHASE batch={batch} input_start={} native_phase={:#x}",batch*64,sim.phase);
  match phase_kernel::audit(&ops,&q,&b){Ok(a)=>{assert_eq!(a.qubits,expected);eprintln!("REMAINING_PHASE_ALL_MR batch={batch} PASS");},Err(e)=>{
   eprintln!("REMAINING_PHASE_ALL_MR batch={batch} ERROR {e}");
   for(lane,v)in chunk.iter().enumerate(){eprintln!("REMAINING_PHASE_INPUT batch={batch} lane={lane} value={v:#x}");}
   if let Some(first)=e.split("first Some(([").nth(1){let ids=first.split(']').next().unwrap();let wanted:Vec<usize>=ids.split(',').map(|v|v.trim().parse().unwrap()).collect();let mut mr=0;
    for(at,o)in ops.iter().enumerate(){if matches!(o.kind,crate::circuit::OperationType::R|crate::circuit::OperationType::Hmr){if wanted.contains(&mr){eprintln!("REMAINING_PHASE_MAP mr={mr} op={at} kind={:?} q={}",o.kind,o.q_target.0);for i in at.saturating_sub(5)..(at+8).min(ops.len()){let r=&ops[i];eprintln!("REMAINING_PHASE_NEIGHBOR at={i} kind={:?} a={} b={} t={} cb={} cond={}",r.kind,r.q_control1.0,r.q_control2.0,r.q_target.0,r.c_target.0,r.c_condition.0);}}mr+=1;}}
   }
  }}
 }
}
