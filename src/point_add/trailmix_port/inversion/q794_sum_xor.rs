//! Full four-root XOR selection with one shared dirty carry echo.
//! Input c is prepared a+c mod64. All helpers arbitrary and returned.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_arithmetic5 as arithmetic,metadata_muxlease as mux};
pub(super) fn high(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],roots:&[&QReg],helpers:&[QReg]){
 assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(roots.len(),4);assert!(helpers.len()>=8);
 let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(helpers).map(QReg::id).collect();ids.extend(roots.iter().map(|q|q.id()));ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"sum XOR aliases");
 let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
 let ctrl:Vec<_>=rank.iter().collect();
 // Complete high selection to the commuting group of XOR translations.
 for bit in 0..2{let truth:Vec<_>=ts.iter().map(|t|((t[0]+t[1])>>bit)&1!=0).collect();for i in 0..4{let j=i^(1<<bit);if i<j{mux::truth_swap(circ,&ctrl,truth.clone(),roots[i],roots[j],helpers);}}}
 let d=&helpers[0];let rest=&helpers[1..];let dc:Vec<_>=rank.iter().chain(std::iter::once(d)).collect();
 let derivative:Vec<_>=(0..64).map(|x|x&32!=0&&(ts[x&31][0]+ts[x&31][1])&1!=0).collect();
 // Difference between h and h+1 is low-bit XOR plus high-bit XOR iff h odd.
 // The two copies cancel the unknown incoming d without a clean cache.
 for _ in 0..2{
  arithmetic::add(circ,a,c,None,true);arithmetic::add(circ,a,c,Some(d),false);
  circ.cswap(d,roots[0],roots[1]);circ.cswap(d,roots[2],roots[3]);
  mux::truth_swap(circ,&dc,derivative.clone(),roots[0],roots[2],rest);
  mux::truth_swap(circ,&dc,derivative.clone(),roots[1],roots[3],rest);
 }
}

pub(crate) fn check(){
 use crate::{sim::Simulator,circuit::OperationType as K};use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x39)}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){w[q.id()as usize]=(w[q.id()as usize]&!(1u64<<l))|((v as u64)<<l);}
 let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let word=circ.alloc_qreg_bits("roots",4);let helper=circ.alloc_qreg_bits("dirty",8);let passenger=circ.alloc_qreg("passenger");let owned=circ.b.next_qubit;
 let roots:Vec<_>=word.iter().collect();high(&mut circ,&rank,&a,&c,&roots,&helper);let route=circ.b.ops.clone();assert_eq!(route.iter().filter(|o|o.kind==K::CCX).count(),648);
 circ.cx(&word[0],&passenger);circ.cx(&passenger,&word[0]);circ.cx(&word[0],&passenger);circ.b.ops.extend(route.into_iter().rev());assert_eq!(circ.b.next_qubit,owned);let ops=circ.b.ops;
 assert!(ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)));
 let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
 let mut count=0;
 for r in 0..32{for av in 0..64{for d in 0..2{let mut seed=0x913b04u64^((r as u64)<<32)^((av as u64)<<20)^d;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
  for cv in 0..64{for i in 0..5{put(&mut before,&rank[i],cv,r>>i&1!=0);}for i in 0..6{put(&mut before,&a[i],cv,av>>i&1!=0);put(&mut before,&c[i],cv,((av+cv)&63)>>i&1!=0);}put(&mut before,&helper[0],cv,d!=0);}
  let mut want=before.clone();for cv in 0..64{let idx=(ts[r][0]+ts[r][1]+((av+cv)>>6))&3;let v=before[word[idx].id()as usize]>>cv&1!=0;let p=before[passenger.id()as usize]>>cv&1!=0;put(&mut want,&word[idx],cv,p);put(&mut want,&passenger,cv,v);}
  let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);sim.qubits=before.clone();sim.apply_iter(ops.iter());assert_eq!(sim.qubits,want,"sumXOR r{r} a{av} d{d}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);count+=64;
 }}}
 eprintln!("Q794_SUM_XOR_PASS lanes={count} high_T=648; all32ranks all6bitaddends bothdirtycarryvalues, arbitraryDATA/lenders, closedselectedexchange, inverse/phase/noallocation");
}
