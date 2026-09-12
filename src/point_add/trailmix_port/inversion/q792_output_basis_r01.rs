//! GPU-selected output XOR bases; exact dirty-output conjugation, no new wire.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
pub(super)fn emit(c:&mut Circuit,word:&[&QReg],truth:Vec<bool>,prefix:&[(&QReg,bool)],out:&[&QReg],dirty:&[QReg]){
 assert_eq!(word.len(),4);assert_eq!(prefix.len(),7);assert_eq!(truth.iter().enumerate().fold(0u64,|a,(i,&v)|a|((v as u64)<<i)),0x7c00);
 let (ops,active):(&[(usize,usize)],usize)=match out.len(){
 2=>( &[(0, 1), (1, 0)], 1),
 8=>( &[(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6)], 7),
 _=>panic!("unscored output basis")};
 let mut ids:Vec<_>=word.iter().map(|q|q.id()).chain(prefix.iter().map(|(q,_)|q.id())).chain(out.iter().map(|q|q.id())).chain(dirty.iter().map(QReg::id)).collect();ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));let n=c.b.next_qubit;
 for &(a,b)in ops.iter().rev(){c.cx(out[a],out[b]);}
 super::q792_fold20_r01::table(c,word,truth,prefix,out[active],dirty);
 for &(a,b)in ops{c.cx(out[a],out[b]);}assert_eq!(c.b.next_qubit,n);
}
pub fn run(){
 use crate::{sim::Simulator,circuit::OperationType as K};use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x39)}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 let mut lanes=0;for width in [2,8]{let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let w=c.alloc_qreg_bits("word",4);let p=c.alloc_qreg_bits("prefix",7);let o=c.alloc_qreg_bits("outputs",width);let d=c.alloc_qreg_bits("dirty",16);let n=c.b.next_qubit;
 let word:Vec<_>=w.iter().collect();let prefix:Vec<_>=p.iter().enumerate().map(|(i,q)|(q,i%3!=1)).collect();let outs:Vec<_>=o.iter().collect();emit(&mut c,&word,(0..16).map(|x|(10..15).contains(&x)).collect(),&prefix,&outs,&d);let ops=c.into_builder().ops;assert!(ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)));assert_eq!(ops.iter().filter(|o|o.kind==K::CCX).count(),64);
 for pattern in 0..2{for first in (0..(1usize<<(11+width))).step_by(64){let mut seed=0xb50c_7923_0011u64^(first as u64)^pattern;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();for (i,q)in w.iter().chain(&p).chain(&o).enumerate(){before[q.id()as usize]=(0..64).fold(0,|a,l|a|((((first+l)>>i&1)as u64)<<l));}let mut after=before.clone();for l in 0..64{let x=(first+l)&15;if(10..15).contains(&x)&&prefix.iter().all(|&(q,v)|(before[q.id()as usize]>>l&1!=0)==v){for q in &o{after[q.id()as usize]^=1u64<<l;}}}let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;}}
 }eprintln!("GPU_OUTPUT_FANOUT_PASS lanes={lanes} full_truth_prefix_outputs=true arbitrary_dirty=true phase=0 inverse=true no_extra_qubits=true");
}
