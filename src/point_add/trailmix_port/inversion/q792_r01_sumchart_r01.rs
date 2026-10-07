//! R01 scan chart: literal M_high=(A+C)>>6 on two rank wires.
//! M+S<=256: only M=128,S=128 needs a ninth high-rank state. Its
//! Ah=2,C_high=0,carry=0 endpoint stores the surplus code in known-zero SM0.
//! A_low and Csum_low stay unchanged, so carry=[A_low>Csum_low] uncomputes.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
// Lowered from the ancilla-free V2 quantum comparator documented in
// trailmix_port/arith/khattar_gidney.rs (Vandaele Fig. 5); specialized
// to six bits and exhaustively reverified here.
// Exact ancilla-free comparator: out ^= [Alo > Mlo]. Both operands
// restore for every 6-bit pair and arbitrary incoming out. The V-shaped
// CCX chain costs 2*n-1 = 11 Toffolis, without any clean or dirty lender.
fn carry(c:&mut Circuit,a:&[QReg],cl:&[QReg],out:&QReg,_d:&[QReg],positive:bool){
 assert_eq!(a.len(),6);assert_eq!(cl.len(),6);
 if !positive{c.x(out);}
 for q in cl{c.x(q);}
 for i in 1..6{c.cx(&a[i],&cl[i]);}
 c.cx(&a[5],out);
 for i in (2..6).rev(){c.cx(&a[i-1],&a[i]);}
 for i in 0..5{c.ccx(&a[i],&cl[i],&a[i+1]);}
 c.ccx(&a[5],&cl[5],out);
 for i in (0..5).rev(){c.ccx(&a[i],&cl[i],&a[i+1]);}
 for i in 2..6{c.cx(&a[i-1],&a[i]);}
 for i in (1..6).rev(){c.cx(&a[i],&cl[i]);}
 for q in cl.iter().rev(){c.x(q);}
}
fn permutation(carry:usize)->(Vec<usize>,[bool;64]){
 let ts=super::q792_fold20_rank_r01::triples();let mut p:Vec<_>=(0..64).collect();let(mut assigned,mut used)=([false;64],[false;64]);
 for(r,t)in ts.iter().enumerate(){let h=t[0]+t[1]+carry;let sh=t[2];if h>3||h+sh>4{continue;}
  for z in 0..2{if h+sh==4&&z!=0{continue;}let mut nz=z;let slot=match h{0=>sh,1=>sh+4*t[0],2=>{if sh==2{if t[0]==2{assert_eq!(carry,0);nz=1;6}else{6+t[0]}}else{2*t[0]+sh}},3=>2*t[0]+sh,_=>unreachable!()};assert!(slot<8);let x=r+32*z;let y=h+4*slot+32*nz;assert!(!assigned[x]&&!used[y],"sum chart collision carry={carry} x={x} y={y}");p[x]=y;assigned[x]=true;used[y]=true;
  }
 }
 let active=assigned;
 for x in 0..64{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=p[y];}p[y]=x;assigned[y]=true;used[x]=true;}}
 let mut check=p.clone();check.sort_unstable();assert_eq!(check,(0..64).collect::<Vec<_>>());(p,active)
}
fn optimized_pair()->(Vec<usize>,Vec<usize>){
 let(p0,_)=permutation(0);let(p1,assigned)=permutation(1);
 // The carry-one map is prescribed only on assigned inputs. Complete the
 // difference P1 P0^-1 directly, closing each forced path into its own cycle.
 // This maximizes its cycle count and minimizes paid transpositions while
 // retaining every active P1 image. P0 and both complete extensions remain
 // bijections on the entire six-bit chart.
 let mut delta=vec![usize::MAX;64];let mut used=[false;64];
 for x in 0..64{if assigned[x]{let from=p0[x];let to=p1[x];assert_eq!(delta[from],usize::MAX);assert!(!used[to]);delta[from]=to;used[to]=true;}}
 for x in 0..64{if delta[x]!=usize::MAX&&!used[x]{let mut y=x;while delta[y]!=usize::MAX{y=delta[y];}delta[y]=x;used[x]=true;}}
 for x in 0..64{if delta[x]==usize::MAX{assert!(!used[x]);delta[x]=x;used[x]=true;}}
 let mut check=delta.clone();check.sort_unstable();assert_eq!(check,(0..64).collect::<Vec<_>>());
 let p1_new:Vec<_>=(0..64).map(|x|delta[p0[x]]).collect();
 for x in 0..64{if assigned[x]{assert_eq!(p1_new[x],p1[x]);}}
 (p0,p1_new)
}
const P0_AFFINE:&[(usize,&[usize],usize)]=&[
 (14,&[1,6,10,16,32],11),
 (2,&[1,4,8,16,32],29),
 (53,&[2,5,8,17,33],22),
 (12,&[1,2,12,16,32],27),
 (47,&[3,5,9,16,33],8),
 (6,&[1,6,8,16,32],6),
 (38,&[1,6,8,16,34],13),
 (5,&[2,5,8,16],2),
 (28,&[1,2,12,20],10),
 (10,&[1,4,10,16],4),
 (15,&[3,5,9,16],3),
 (13,&[2,21,9,32],5),
 (16,&[1,2,4,8],13),
 (24,&[1,2,4,24],12),
 (8,&[1,18,4],3),
 (20,&[1,8,20],7),
 (12,&[1,16],3),
 (14,&[12,16],3),
 (7,&[6,24],3),
];
const DELTA_AFFINE:&[(usize,&[usize],usize)]=&[
 (7,&[3,5,8,16,32],15),
 (19,&[3,4,8,17,32],13),
 (1,&[18,4,8,32],6),
 (1,&[2,4,48],7),
 (1,&[18,20,24],6),
 (2,&[1,8,16],1),
 (26,&[1,10,18],5),
 (1,&[16],0),
];
fn check_affine(p:&[usize],commands:&[(usize,&[usize],usize)]){
 let mut actual:Vec<_>=(0..64).collect();
 for &(diff,masks,values) in commands{
  assert!((1..64).contains(&diff));
  for &mask in masks{assert_eq!((mask&diff).count_ones()&1,0);}
  for x in &mut actual{if masks.iter().enumerate().all(|(i,&m)|((*x&m).count_ones()as usize&1)==(values>>i&1)){*x^=diff;}}
 }
 assert_eq!(actual,p);
}
fn linear_rank(rows:&[usize])->usize{
 let mut pivots=[0usize;6];let mut rank=0;
 for &row in rows{let mut x=row;for bit in (0..6).rev(){if x>>bit&1!=0{if pivots[bit]==0{pivots[bit]=x;rank+=1;break;}x^=pivots[bit];}}}
 rank
}
fn affine_gate(c:&mut Circuit,w:&[&QReg],guard:Option<&QReg>,d:&[QReg],diff:usize,masks:&[usize],values:usize){
 let pivot=diff.trailing_zeros()as usize;let mut rows=vec![1<<pivot];rows.extend(masks);
 assert_eq!(linear_rank(&rows),rows.len());
 for bit in 0..6{if bit!=pivot{let row=(1<<bit)|((diff>>bit&1)<<pivot);let mut test=rows.clone();test.push(row);if linear_rank(&test)>rows.len(){rows.push(row);}}}
 assert_eq!(rows.len(),6);
 let mut ops=Vec::new();
 for bit in 0..6{
  let at=(bit..6).find(|&r|rows[r]>>bit&1!=0).unwrap();
  if at!=bit{for (src,dst) in [(at,bit),(bit,at),(at,bit)]{rows[dst]^=rows[src];ops.push((src,dst));}}
  for row in 0..6{if row!=bit&&rows[row]>>bit&1!=0{rows[row]^=rows[bit];ops.push((bit,row));}}
 }
 assert_eq!(rows,(0..6).map(|i|1<<i).collect::<Vec<_>>());
 for &(src,dst) in ops.iter().rev(){c.cx(w[src],w[dst]);}
 let mut cs:Vec<_>=guard.into_iter().map(|q|(q,true)).collect();
 cs.extend(masks.iter().enumerate().map(|(i,_)|(w[i+1],values>>i&1!=0)));
 mixed_mcx(c,&cs,w[0],d);
 for &(src,dst) in &ops{c.cx(w[src],w[dst]);}
}
pub(super) fn emit(c:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,d:&[QReg]){
 let w:Vec<_>=rank.iter().chain(std::iter::once(&sm[0])).collect();
 let(p0,p1)=optimized_pair();let mut inv0=[0;64];for x in 0..64{inv0[p0[x]]=x;}
 let delta:Vec<_>=(0..64).map(|y|p1[inv0[y]]).collect();
 static VERIFIED:std::sync::OnceLock<()> = std::sync::OnceLock::new();
 VERIFIED.get_or_init(||{check_affine(&p0,P0_AFFINE);check_affine(&delta,DELTA_AFFINE);});
 for &(diff,masks,values) in P0_AFFINE{affine_gate(c,&w,None,d,diff,masks,values);}
 // The active normal-R guard is known one, so X(g) provides a clean carry
 // target. Both complete chart permutations remain bijective off-domain.
 c.x(g);carry(c,a,cl,g,d,true);
 for &(diff,masks,values) in DELTA_AFFINE{affine_gate(c,&w,Some(g),d,diff,masks,values);}
 carry(c,a,cl,g,d,true);c.x(g);
}
pub(super) fn sh(code:usize)->usize{let h=code&3;let slot=code>>2;match h{0|1=>slot&3,2=>if slot<6{slot&1}else{2},3=>slot&1,_=>unreachable!()}}

/// Exhaust the physical chart and carry operands with arbitrary borrowed rails.
/// Separately validate the numeric interpretation on every admitted scalar tuple.
pub fn run(){
 use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let rank=c.alloc_qreg_bits("rank",5);let a=c.alloc_qreg_bits("Alo",6);let cl=c.alloc_qreg_bits("Mlo",6);let sm=c.alloc_qreg_bits("SM",4);let g=c.alloc_qreg("guard");let d=c.alloc_qreg_bits("borrowed",20);let n=c.b.next_qubit;
 emit(&mut c,&rank,&a,&cl,&sm,&g,&d);assert_eq!(n,c.b.next_qubit);let ops=c.into_builder().ops;let(pair0,pair1)=optimized_pair();let maps=[pair0,pair1];let mut lanes=0u64;
 for pattern in 0..2{for first in (0..1usize<<18).step_by(64){let mut seed=0x792501ca17u64^first as u64^((pattern as u64)<<40);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
  for lane in 0..64{let code=first+lane;let r=code&63;let av=code>>6&63;let cv=code>>12&63;let guard=(lane+pattern)&1;let expected=maps[usize::from((av>cv)==(guard==1))][r];
   for(w,rk)in[(&mut before,r),(&mut after,expected)]{for(i,q)in rank.iter().chain(std::iter::once(&sm[0])).enumerate(){let b=1u64<<lane;w[q.id()as usize]=(w[q.id()as usize]&!b)|(((rk>>i&1)as u64)<<lane);}for(qs,v)in[(&a,av),(&cl,cv)]{for(i,q)in qs.iter().enumerate(){let b=1u64<<lane;w[q.id()as usize]=(w[q.id()as usize]&!b)|(((v>>i&1)as u64)<<lane);}}}
   let b=1u64<<lane;for w in [&mut before,&mut after]{w[g.id()as usize]=(w[g.id()as usize]&!b)|((guard as u64)<<lane);}
  }
  let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"sumchart first={first} pattern={pattern}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
 }}
 let ts=super::q792_fold20_rank_r01::triples();let mut scalar=0;for av in 0..254{for cv in 0..254-av{for sv in 0..=256-av-cv{if sv>255{continue;}let r=ts.iter().position(|t|*t==[av>>6,cv>>6,sv>>6]).unwrap();let sum=av+cv;let sm=sv>>2&15;let out=maps[usize::from((av&63)>(sum&63))][r+32*(sm&1)];assert_eq!(out&3,sum>>6);assert_eq!(sh(out&31),sv>>6);let logical_sm0=(out>>5)^usize::from((out&31==26||out&31==30)&&(out>>5!=0));assert_eq!(logical_sm0,sm&1);scalar+=1;}}}
 eprintln!("FOLD20_SUMCHART_PASS lanes={lanes} scalar={scalar} ops={} T={} inverse=true dirty_restored=true extra_qubits=0",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
}
