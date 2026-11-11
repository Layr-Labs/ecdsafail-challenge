//! M19 sound source builder, with streamed emission to bound host RAM.
//! Only emits circuit operations; does not access evaluator, scores, or inputs.
//! The unchanged benchmark evaluates the resulting ops.bin in a separate process.
use quantum_ecc::circuit::{Op,OperationType,BitId,QubitId,RegisterId,NO_BIT,NO_QUBIT};
use std::{fs::{self,File},io::{Read,Write,BufReader,BufWriter},path::Path};
#[path="sound_addsub_inverse.rs"] mod inverse;
#[path="sound_comp_mbu.rs"] mod mbu;
mod m19_sites;
use inverse::payload::point::{self,Micro,NONE,CLASS_X,CLASS_CX,CLASS_CCX,CLASS_SWAP};
static MEASURE:std::sync::atomic::AtomicU16=std::sync::atomic::AtomicU16::new(14952);
static GLOBAL:std::sync::atomic::AtomicU16=std::sync::atomic::AtomicU16::new(1639);
fn expand(m:Micro,out:&mut Vec<Op>){
    let mut o=Op::empty();
    match m.kind {
        0|7|9=>{o.kind=match m.kind{0=>OperationType::Neg,7=>OperationType::Z,9=>OperationType::CZ,_=>unreachable!()};if m.kind!=0{o.q_target=QubitId(m.t as u64);}if m.kind==9{o.q_control1=QubitId(m.a as u64);}if m.cond!=NONE{o.c_condition=BitId(m.cond as u64);}o.validate();out.push(o);},
        6|8|10|13=>{o=inverse::Gate{kind:m.kind,a:m.a,b:m.b,t:m.t}.op();if m.cond!=NONE{o.c_condition=BitId(m.cond as u64);}o.validate();out.push(o);},
        CLASS_X=>{o.kind=OperationType::BitInvert;o.c_target=BitId(m.t as u64);o.validate();out.push(o);},
        CLASS_CX=>{assert_ne!(m.a,m.t);o.kind=OperationType::BitInvert;o.c_target=BitId(m.t as u64);o.c_condition=BitId(m.a as u64);o.validate();out.push(o);},
        CLASS_CCX=>{assert!(m.a!=m.b&&m.a!=m.t&&m.b!=m.t);
            o.kind=OperationType::PushCondition;o.c_condition=BitId(m.a as u64);o.validate();out.push(o);
            o=Op::empty();o.kind=OperationType::BitInvert;o.c_target=BitId(m.t as u64);o.c_condition=BitId(m.b as u64);o.validate();out.push(o);
            o=Op::empty();o.kind=OperationType::PopCondition;o.validate();out.push(o);
        },
        CLASS_SWAP=>{assert_ne!(m.a,m.t);for(a,t)in [(m.a,m.t),(m.t,m.a),(m.a,m.t)]{o=Op::empty();o.kind=OperationType::BitInvert;o.c_target=BitId(t as u64);o.c_condition=BitId(a as u64);o.validate();out.push(o);}},
        mbu::MBU_AND|mbu::MBU_COPY|mbu::MBU_ONE=>{
            let bit=BitId(MEASURE.load(std::sync::atomic::Ordering::Relaxed)as u64);
            // Entry/exit invariant: bit=0. Inactive conditional-HMR lanes keep
            // zero, so the outcome-conditioned CZ already includes the old guard.
            let guard=GLOBAL.load(std::sync::atomic::Ordering::Relaxed);o.kind=OperationType::Hmr;o.q_target=QubitId(m.t as u64);o.c_target=bit;if guard!=NONE{o.c_condition=BitId(guard as u64);}o.validate();out.push(o);
            o=Op::empty();o.kind=OperationType::CZ;o.q_control1=QubitId(m.a as u64);o.q_target=QubitId(m.b as u64);o.c_condition=bit;o.validate();out.push(o);
            if m.kind==mbu::MBU_COPY{
                assert_ne!(m.cond,m.t);o=Op::empty();o.kind=OperationType::Z;o.q_target=QubitId(m.cond as u64);o.c_condition=bit;o.validate();out.push(o);
                o=Op::empty();o.kind=OperationType::CX;o.q_control1=QubitId(m.cond as u64);o.q_target=QubitId(m.t as u64);if guard!=NONE{o.c_condition=BitId(guard as u64);}o.validate();out.push(o);
            }else if m.kind==mbu::MBU_ONE{
                o=Op::empty();o.kind=OperationType::Neg;o.c_condition=bit;o.validate();out.push(o);
                o=Op::empty();o.kind=OperationType::X;o.q_target=QubitId(m.t as u64);if guard!=NONE{o.c_condition=BitId(guard as u64);}o.validate();out.push(o);
            }
            o=Op::empty();o.kind=OperationType::BitStore0;o.c_target=bit;o.validate();out.push(o);
        },
        _=>panic!("unknown micro"),
    }
}
fn ports()->Vec<Op>{let mut out=vec![];for id in 0..4{let mut o=Op::empty();o.kind=OperationType::Register;o.r_target=RegisterId(id);out.push(o);for i in 0..256 {let mut o=Op::empty();o.kind=OperationType::AppendToRegister;o.r_target=RegisterId(id);if id<2{o.q_target=QubitId(id*256+i);}else{o.c_target=BitId((id-2)*256+i);}o.validate();out.push(o);}}out}
fn record(o:&Op)->[u8;56]{let mut r=[0;56];r[..4].copy_from_slice(&(o.kind as u32).to_le_bytes());for(i,v)in[o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0].into_iter().enumerate(){r[8+8*i..16+8*i].copy_from_slice(&v.to_le_bytes());}r}

fn read_micro(r:&mut impl Read)->Micro {let mut b=[0;12];r.read_exact(&mut b).unwrap();Micro::read(&b)}
fn flush_ops<W:Write>(ops:&mut Vec<Op>,w:&mut W,count:&mut u64){for op in ops.iter(){w.write_all(&record(op)).unwrap();*count+=1;}ops.clear();}
fn make_stream(){
 let raw=Path::new("m19-native.micro");
 let generic=Path::new("m19-generic.micro");
 let n=point::generate(raw);
 assert_eq!((n.qubits,n.bits,n.macros,n.classical_end,n.quantum_end),(1643,14952,105951985,37825859,68126126));
 assert_eq!(n.toffolis,4537437);
 let o=mbu::optimize(raw,generic,Path::new("m19-and-erase-proofs.bin"),n.qubits,n.classical_end,n.quantum_end);
 assert_eq!((o.replacements,o.zeros,o.copies,o.ones,o.epochs,o.global_condition),(1792348,1778707,7475,6166,0,1639));
 // Proof graph and runtime snapshots have been dropped before expansion.
 let records=135536615u64;
 let mut w=BufWriter::with_capacity(4*1024*1024,File::create("ops.bin").unwrap());
 w.write_all(b"QECCOPSZ").unwrap();w.write_all(&records.to_le_bytes()).unwrap();
 let mut z=zstd::stream::write::Encoder::new(w,1).unwrap();
 let mut r=BufReader::with_capacity(4*1024*1024,File::open(generic).unwrap());
 let mut ops=ports();let mut count=0;let mut at=0;
 for &(lo,hi,flag,center,central_count) in m19_sites::SITES {
  assert!(at<=lo&&lo<hi);
  while at<lo {expand(read_micro(&mut r),&mut ops);at+=1;if ops.len()>=32768{flush_ops(&mut ops,&mut z,&mut count);}}
  let mut phase=Vec::with_capacity((hi-lo)as usize);
  for i in lo..hi {
   let mut m=read_micro(&mut r);
   if (center..center+central_count).contains(&i){
    assert_eq!((m.t,m.cond),(flag,1639));
    m=match m.kind {6=>Micro{kind:0,a:0,b:0,t:0,cond:m.cond},8=>Micro{kind:7,a:0,b:0,t:m.a,cond:m.cond},13=>Micro{kind:9,a:m.a,b:0,t:m.b,cond:m.cond},_=>panic!("cleanup center changed")};
   }else{
    let mut touched=vec![m.t];if matches!(m.kind,8|10|13|24|25|26){touched.push(m.a);}if matches!(m.kind,13|24|25|26){touched.push(m.b);}if m.kind==25{touched.push(m.cond);}assert!(!touched.contains(&flag));
   }
   phase.push(m);
  }
  let mut op=Op::empty();op.kind=OperationType::Hmr;op.q_target=QubitId(flag as u64);op.c_target=BitId(14953);op.c_condition=BitId(1639);op.validate();ops.push(op);
  op=Op::empty();op.kind=OperationType::PushCondition;op.c_condition=BitId(14953);op.validate();ops.push(op);
  for m in phase{expand(m,&mut ops);}
  op=Op::empty();op.kind=OperationType::PopCondition;op.validate();ops.push(op);
  op=Op::empty();op.kind=OperationType::BitStore0;op.c_target=BitId(14953);op.validate();ops.push(op);
  flush_ops(&mut ops,&mut z,&mut count);at=hi;
 }
 while at<n.macros {expand(read_micro(&mut r),&mut ops);at+=1;if ops.len()>=32768{flush_ops(&mut ops,&mut z,&mut count);}}
 flush_ops(&mut ops,&mut z,&mut count);assert_eq!(count,records);
 let mut extra=[0;1];assert_eq!(r.read(&mut extra).unwrap(),0);
 z.finish().unwrap().flush().unwrap();
 println!("M19 SOURCE BUILD OK: records={count}, qubits=1643; streamed ops.bin for the unchanged evaluator");
 // Only throwaway generator intermediates in the sandbox working directory.
 for p in [raw,generic,Path::new("m19-and-erase-proofs.bin")]{fs::remove_file(p).unwrap();}
}
pub fn build()->Vec<Op>{
 // The generic harness Vec interface would need >7 GiB for these 135M records.
 // Emit the same public QECCOPSZ format directly, then finish the untrusted
 // builder process. benchmark.sh checks its exit status and scores ops.bin.
 make_stream();std::process::exit(0)
}
