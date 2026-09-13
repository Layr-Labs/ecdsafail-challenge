//! Physical lifecycle with independent inverse oracle and persistent passengers.
use super::*;
use crate::circuit::NO_BIT;
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Fixed(u64);impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){for x in b{*x=rnd(&mut self.0)as u8;}}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],i:usize,lane:usize,v:bool){let bit=1u64<<lane;w[i]=(w[i]&!bit)|if v{bit}else{0};}
fn checked<R:XofReader>(sim:&mut Simulator<R>,ops:&[Op],stage:&str){for op in ops{assert!(!matches!(op.kind,OperationType::PushCondition|OperationType::PopCondition));if op.kind==OperationType::R{let mask=if op.c_condition==NO_BIT{u64::MAX}else{sim.bit(op.c_condition)};assert_eq!(sim.qubit(op.q_target)&mask,0,"dirty reset at {stage}");}sim.apply_iter(std::iter::once(op));}assert_eq!(sim.phase,0,"phase {stage}");}
fn compare<R:XofReader>(sim:&Simulator<R>,want:&[u64],stage:&str,batch:usize){assert_eq!(sim.phase,0,"phase {stage}");for(q,&v)in want.iter().enumerate(){assert_eq!(sim.qubits[q],v,"stage={stage} batch={batch} wire={q}");}}
fn expected(rows:&[&[u8]],batch:usize,mapping:&[usize],offset:usize,passenger:&[QReg],initial:&[u64])->Vec<u64>{
 let mut want=vec![0;initial.len()];for q in passenger{want[q.id()as usize]=initial[q.id()as usize];}let ts=super::super::q792_fold20_rank_r01::triples();
 for lane in 0..64{let row=rows[(batch*64+lane)%rows.len()];let val=|first:usize,n:usize|->usize{(0..n).map(|i|(((row[offset+(first+i)/8]>>((first+i)%8))&1)as usize)<<i).sum()};let r=val(0,5);let a=val(5,6);let cl=val(11,6);let sm=val(17,4);let code=if r==29&&a==63{47|cl<<10|(sm&3)<<16}else{super::super::q792_fold20_rank_r01::encode(r,a,cl,sm,&ts)};
  for(i,&q)in mapping.iter().enumerate(){if q==u32::MAX as usize{assert!([279,280,281].contains(&i));continue;}let b=if i<20{code>>i&1!=0}else{let old=if i<22{i+1}else{i+2};row[offset+old/8]>>(old%8)&1!=0};put(&mut want,q,lane,b);}}
 let cargo=mapping[23+if offset==64{0}else{255}];assert_eq!(want[cargo],u64::MAX);want[cargo]=initial[passenger[0].id()as usize];let second=mapping[282+if offset==64{2}else{257}];assert_eq!(want[second],0);want[second]=initial[passenger[1].id()as usize];want
}

pub fn run(){run_inner(false);}
pub fn run_boundaries(){run_inner(true);}
fn run_inner(boundary_only:bool){
 let data=std::fs::read(std::env::var("LOWQ_RANK5_LIFECYCLE_CAPSULE").expect("explicit capsule")).unwrap();assert_eq!(&data[..8],b"R5LIFE01");let count=u32::from_le_bytes(data[8..12].try_into().unwrap())as usize;assert_eq!(data.len(),12+count*200);assert!(count>0);let rows:Vec<_>=data[12..].chunks_exact(200).collect();let batches=count.div_ceil(64);
 let mut circ=Circuit::new();let dx=circ.alloc_qreg_bits("input",257);let input_ids:Vec<_>=dx.iter().map(|q|q.id()as usize).collect();let passenger=circ.alloc_qreg_bits("passenger",256);
 let core=initialize(&mut circ,dx,&passenger[0],&passenger[1]);let initial_map=ids(&core);let initialization=std::mem::take(&mut circ.b.ops);
 let mut terminal=release_terminal(&mut circ,core);release_terminal_padding(&mut circ,&mut terminal);let terminal_ids:Vec<_>=terminal.work2.iter().chain(&terminal.history).chain(std::iter::once(&terminal.iteration)).map(|q|q.id()as usize).collect();let release=std::mem::take(&mut circ.b.ops);
 toggle_inverse_sign(&mut circ,&terminal);let to_inverse=std::mem::take(&mut circ.b.ops);toggle_inverse_sign(&mut circ,&terminal);let from_inverse=std::mem::take(&mut circ.b.ops);
 restore_terminal_padding(&mut circ,&mut terminal);let core=rebuild_terminal(&mut circ,terminal,&passenger[0],&passenger[1]);let rebuilt_map=ids(&core);let rebuild=std::mem::take(&mut circ.b.ops);let dx=finish(&mut circ,core);let output_ids:Vec<_>=dx.iter().map(|q|q.id()as usize).collect();let finishing=std::mem::take(&mut circ.b.ops);
 let peak=792;assert!(dual_phase());assert_eq!(circ.b.active_qubits,513);assert_eq!(circ.b.peak_qubits,peak);assert_eq!(circ.b.next_qubit,peak);let owned=circ.b.next_qubit as usize;let bits=circ.b.next_bit as usize;
 eprintln!("Q792_LIFECYCLE_BUILT inputs={count} physical={owned} peak={} bits={bits} init_ops={} release_ops={} to_inverse_ops={} from_inverse_ops={} rebuild_ops={} finish_ops={}",circ.b.peak_qubits,initialization.len(),release.len(),to_inverse.len(),from_inverse.len(),rebuild.len(),finishing.len());
 let mut initial=Vec::new();for batch in 0..batches{let mut seed=0x51ef46b9ac287d03u64^batch as u64;let mut state=vec![0;owned];for q in &passenger{state[q.id()as usize]=rnd(&mut seed);}for lane in 0..64{let row=rows[(batch*64+lane)%count];for bit in 0..256{put(&mut state,input_ids[bit],lane,row[bit/8]>>(bit%8)&1!=0);}}initial.push(state);}
 let mut randoms:Vec<_>=(0..batches).map(|b|Fixed(0x14e5a67db802c39f^b as u64)).collect();let mut sims:Vec<_>=randoms.iter_mut().map(|r|Simulator::new(owned,bits,r)).collect();
 for batch in 0..batches{sims[batch].qubits=initial[batch].clone();checked(&mut sims[batch],&initialization,"initialize");compare(&sims[batch],&expected(&rows,batch,&initial_map,64,&passenger,&initial[batch]),"initialized scalar",batch);}
 let mut forward_ops=0u64;let mut forward_t=0u64;
 let mut cache=crate::point_add::q793_runtime_r01::Cache::default();cache.synchronize();
 for inverse in [false,true]{let mapping=if inverse{&rebuilt_map}else{&initial_map};
  if !boundary_only{for z in 0..super::super::shared_step::SCHEDULE_BLOCKS{let block=if inverse{super::super::shared_step::SCHEDULE_BLOCKS-1-z}else{z};let mut logical:Vec<_>=(0..4).map(|j|cache.get((block,j))).collect();let missing:Vec<_>=(0..4).filter(|&j|logical[j].is_none()).collect();let built=std::thread::scope(|scope|{let handles:Vec<_>=missing.iter().map(|&j|(j,scope.spawn(move||template(block,j)))).collect();handles.into_iter().map(|(j,h)|(j,h.join().unwrap())).collect::<Vec<_>>()});for(j,ops)in built{cache.insert((block,j),&ops);logical[j]=Some(ops);}let templates:Vec<_>=logical.into_iter().map(|ops|remap(ops.unwrap(),mapping,&passenger,inverse)).collect();let first=block*super::super::shared_step::SCHEDULE_BLOCK;let end=(first+super::super::shared_step::SCHEDULE_BLOCK).min(1616);
   for i in 0..end-first{let step=if inverse{end-1-i}else{first+i};let ops=&templates[(step+1)%4];if !inverse{forward_ops+=ops.len()as u64;forward_t+=ops.iter().filter(|o|o.kind==OperationType::CCX).count()as u64;}for sim in &mut sims{sim.apply_iter(ops.iter());assert_eq!(sim.phase,0);}}
   for(batch,sim)in sims.iter().enumerate(){for q in &passenger[if dual_phase(){2}else{1}..]{assert_eq!(sim.qubits[q.id()as usize],initial[batch][q.id()as usize],"passenger inverse={inverse} block={block}");}}eprintln!("Q792_LIFECYCLE_BLOCK inverse={inverse} block={block} PASS");
  }
  }else{for batch in 0..batches{sims[batch].qubits=expected(&rows,batch,mapping,if inverse{64}else{132},&passenger,&initial[batch]);}}
  if !inverse{for batch in 0..batches{
   let terminal_state=expected(&rows,batch,&initial_map,132,&passenger,&initial[batch]);compare(&sims[batch],&terminal_state,"terminal before release",batch);checked(&mut sims[batch],&release,"release");let mut released=terminal_state;
   for q in 0..owned{if !terminal_ids.contains(&q)&&!passenger.iter().any(|p|p.id()as usize==q){released[q]=0;}}for p in &passenger[..if dual_phase(){2}else{1}]{released[p.id()as usize]=initial[batch][p.id()as usize];}compare(&sims[batch],&released,"released terminal",batch);
   checked(&mut sims[batch],&to_inverse,"canonical inverse");let mut canonical=released.clone();for lane in 0..64{let row=rows[(batch*64+lane)%count];for i in 0..256{put(&mut canonical,terminal_ids[i],lane,row[32+i/8]>>(i%8)&1!=0);}}compare(&sims[batch],&canonical,"independent modular inverse",batch);
   checked(&mut sims[batch],&from_inverse,"restore coefficient");compare(&sims[batch],&released,"restored terminal",batch);checked(&mut sims[batch],&rebuild,"rebuild");compare(&sims[batch],&expected(&rows,batch,&rebuilt_map,132,&passenger,&initial[batch]),"rebuilt terminal",batch);
  }}
 }
 for batch in 0..batches{compare(&sims[batch],&expected(&rows,batch,&rebuilt_map,64,&passenger,&initial[batch]),"reversed initial",batch);checked(&mut sims[batch],&finishing,"finish");let mut want=vec![0;owned];for q in &passenger{want[q.id()as usize]=initial[batch][q.id()as usize];}for lane in 0..64{let row=rows[(batch*64+lane)%count];for i in 0..256{put(&mut want,output_ids[i],lane,row[i/8]>>(i%8)&1!=0);}}compare(&sims[batch],&want,"original denominator and zero ancillas",batch);}
 let lifecycle_ops=initialization.len()+release.len()+to_inverse.len()+from_inverse.len()+rebuild.len()+finishing.len();
 let marker=if boundary_only{"Q792_LIFECYCLE_BOUNDARIES_PASS"}else{"Q792_LIFECYCLE_PASS"};
 eprintln!("{marker} boundary_only={boundary_only} inputs={count} lanes={} peak_qubits={peak} forward_ops={forward_ops} forward_T={forward_t} lifecycle_ops={lifecycle_ops}; actual init/release/independent inverse/sign/rebuild/finish, all256 passengers and every reset checked; full forward/reverse only when boundary_only=false, otherwise scalar boundary states injected explicitly; NOT whole point-add or official acceptance",64*batches);
}
