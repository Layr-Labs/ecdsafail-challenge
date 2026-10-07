//! Paid T-only triangle chart on the existing five rank rails.
//!
//! A>=5 and A+C+S<=256 imply a+b<=62, with a=C>>2,b=S>>2.
//! Fold a>=32 by (a,b)->(63-a,63-b). The result uses a5+b6;
//! folded outputs have a+b>=64 and unfolded outputs have a+b<=62.
//! The missing diagonal63 is essential. The fifth input rank bit is funded
//! by the caller's existing third loan; this chart needs NO fourth clean loan.
//!
//! Output rank is [A_high0,A_high1,folded_C6,folded_S6,folded_S7].
//! C[2..6] and SM[0..4] hold the folded low quarter fields. C[0..2]
//! are unchanged. This exposes literal A8; C/S are payload until inverse.
//! All five auxiliary wires may be arbitrary and are restored.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
const P0:[usize;32]=[0,8,16,24,4,12,20,31,28,27,26,23,15,1,9,17,25,5,13,21,29,19,22,2,10,18,6,14,30,3,11,7];
const P1:[usize;32]=[0,8,16,27,4,12,26,31,28,20,22,24,15,1,9,17,23,5,13,19,29,21,25,2,10,18,6,14,30,3,11,7];
fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|cc|(0..4).filter(move|&s|a+cc+s<=4).map(move|s|[a,cc,s]))).collect()}
fn cycles(p:&[usize])->Vec<Vec<usize>>{
 let mut seen=[false;32];let mut out=Vec::new();for a in 0..32{if seen[a]{continue;}let mut row=Vec::new();let mut b=a;while !seen[b]{seen[b]=true;row.push(b);b=p[b];}assert_eq!(b,a);out.push(row);}out
}
fn flip_low(c:&mut Circuit,cl:&[QReg],sm:&[QReg],flag:&QReg,mode:Option<(&QReg,bool)>,dirty:&[QReg]){
 for q in cl[2..6].iter().chain(sm){let mut cs=vec![(flag,true)];cs.extend(mode);mixed_mcx(c,&cs,q,dirty);}
}
fn fold_flag(c:&mut Circuit,rank:&[QReg],flag:&QReg,dirty:&[QReg]){
 let mut anf:Vec<_>=triples().iter().map(|t|t[1]>=2).collect();for k in 0..5{for z in 0..32{if z>>k&1!=0{anf[z]^=anf[z^(1<<k)];}}}
 for (z,on) in anf.into_iter().enumerate(){if on{let cs:Vec<_>=rank.iter().enumerate().filter(|(i,_)|z>>i&1!=0).map(|(_,q)|(q,true)).collect();mixed_mcx(c,&cs,flag,dirty);}}
}
fn carry(c:&mut Circuit,cl:&[QReg],sm:&[QReg],flag:&QReg,dirty:&[QReg]){
 // a_low+b_low>=16. Generate/propagate cubes are disjoint, hence XOR.
 for k in 0..4{for j in k+1..4{c.cx(&cl[j+2],&sm[j]);}let mut cs=vec![(&cl[k+2],true),(&sm[k],true)];cs.extend(sm[k+1..].iter().map(|q|(q,true)));mixed_mcx(c,&cs,flag,dirty);for j in (k+1..4).rev(){c.cx(&cl[j+2],&sm[j]);}}
}
fn edge(c:&mut Circuit,rank:&[QReg],left:usize,right:usize,flag:Option<&QReg>,mode:Option<(&QReg,bool)>,dirty:&[QReg]){
 let diff=left^right;let pivot=diff.trailing_zeros()as usize;let base=if left>>pivot&1==0{left}else{right};
 let others:Vec<_>=(0..5).filter(|&i|i!=pivot&&diff>>i&1!=0).collect();for &i in &others{c.cx(&rank[pivot],&rank[i]);}
 // Only the permutation center is controlled; its affine frame restores.
 let mut cs:Vec<_>=flag.into_iter().map(|q|(q,true)).collect();cs.extend(mode);cs.extend((0..5).filter(|&i|i!=pivot).map(|i|(&rank[i],base>>i&1!=0)));mixed_mcx(c,&cs,&rank[pivot],dirty);
 for &i in others.iter().rev(){c.cx(&rank[pivot],&rank[i]);}
}
pub(super) fn emit(c:&mut Circuit,rank:&[QReg],cl:&[QReg],sm:&[QReg],mode:Option<(&QReg,bool)>,aux:&[QReg],inverse:bool){
 assert_eq!(rank.len(),5);assert_eq!(cl.len(),6);assert_eq!(sm.len(),4);assert!(aux.len()>=5);
 let mut ids:Vec<_>=rank.iter().chain(cl).chain(sm).chain(aux).map(QReg::id).collect();ids.extend(mode.map(|(q,_)|q.id()));ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
 let at=c.b.ops.len();let n=c.b.next_qubit;let flag=&aux[0];let dirty=&aux[1..];
 // The fold predicate remains unconditional. Its dirty offset cancels in
 // two mode-controlled low-field writes; no extra clean flag is assumed.
 flip_low(c,cl,sm,flag,mode,dirty);fold_flag(c,rank,flag,dirty);flip_low(c,cl,sm,flag,mode,dirty);fold_flag(c,rank,flag,dirty);
 for row in cycles(&P0){for &y in &row[1..]{edge(c,rank,row[0],y,None,mode,dirty);}}
 let mut inv=[0;32];for i in 0..32{inv[P0[i]]=i;}let delta:Vec<_>=(0..32).map(|i|P1[inv[i]]).collect();let rows=cycles(&delta);
 for reflect in 0..2{
  let involution=|c:&mut Circuit|{for row in &rows{for i in 0..row.len(){let j=(reflect+row.len()-i)%row.len();if i<j{edge(c,rank,row[i],row[j],Some(flag),mode,dirty);}}}};
  involution(c);carry(c,cl,sm,flag,dirty);involution(c);carry(c,cl,sm,flag,dirty);
 }
 if inverse{c.b.ops[at..].reverse();}assert_eq!(n,c.b.next_qubit);
}

pub fn run(){
 use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x71)}}
 for controlled in [false,true]{
  let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;
  let rank=c.alloc_qreg_bits("rank",5);let cl=c.alloc_qreg_bits("C",6);let sm=c.alloc_qreg_bits("SM",4);let aux=c.alloc_qreg_bits("arbitrary",5);let mode=c.alloc_qreg("mode");let n=c.b.next_qubit;
  emit(&mut c,&rank,&cl,&sm,controlled.then_some((&mode,false)),&aux,false);let ops=c.into_builder().ops;
  let wires:Vec<_>=rank.iter().chain(cl[2..].iter()).chain(sm.iter()).chain(aux.iter()).chain(std::iter::once(&mode)).map(|q|q.id()as usize).collect();assert_eq!(wires.len(),19);
  let ts=triples();let mut total=0;
  for base in (0..1usize<<19).step_by(64){
   let mut before=vec![0u64;n as usize];let mut after=before.clone();
   for lane in 0..64{let v=base+lane;let r=v&31;let mut low=v>>5&15;let mut mid=v>>9&15;let enabled=!controlled||v>>18&1==0;let mut expected=v;
    if enabled{if ts[r][1]>=2{low^=15;mid^=15;}let table=if low+mid>=16{&P1}else{&P0};expected=(v&!8191)|table[r]|(low<<5)|(mid<<9);}
    for (i,&wire) in wires.iter().enumerate(){before[wire]|=((v>>i&1)as u64)<<lane;after[wire]|=((expected>>i&1)as u64)<<lane;}
    // Unused C0/C1 are arbitrary too and never touched.
    for (i,q) in cl[..2].iter().enumerate(){let b=((v>>(i+3)&1)as u64)<<lane;before[q.id()as usize]|=b;after[q.id()as usize]|=b;}
   }
   let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"triangle controlled={controlled} base={base}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
  }
  eprintln!("T_UPPER_TRIANGLE_NATIVE_PASS controlled={controlled} lanes={total} T={} ops={} physical={n} inverse=true phase=0 arbitrary_aux_restored=true",ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len());
 }
}
