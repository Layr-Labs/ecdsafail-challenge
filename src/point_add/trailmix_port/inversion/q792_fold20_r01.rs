//! Own 20-bit folded metadata readout. No clean scratch; whole Q792 unproved.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
const LOW:[usize;10]=[0,1,2,4,5,8,13,14,17,23];
const EDGE:[usize;10]=[3,6,9,11,15,18,20,24,26,29];
const PEAK:[usize;12]=[7,10,12,16,19,21,22,25,27,28,30,31];

pub(super) fn table(c:&mut Circuit,word:&[&QReg],truth:Vec<bool>,prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
 let at=c.b.ops.len();table_inner(c,word,truth.clone(),prefix,out,dirty);super::q792_shared_capture_r01::record(c,word,&truth,prefix,out,at);
}
fn table_inner(c:&mut Circuit,word:&[&QReg],truth:Vec<bool>,prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let at=c.b.ops.len();
    table_direct(c,word,truth.clone(),prefix,out,dirty);
    if prefix.len()<2 || dirty.len()<word.len().max(prefix.len()+1) || !truth.iter().any(|&v|v){return;}
    // Each factor is a pure target XOR. ABAB cancels the arbitrary lender:
    // d ^= F; out ^= d*P; d ^= F; out ^= d*P gives out ^= F*P.
    // Compare both choices of producer using actual emitted NCT operations.
    let mut best=c.b.ops.split_off(at);
    let score=|ops:&[crate::circuit::Op]|(ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count(),ops.len());
    let d=&dirty[0];let rest=&dirty[1..];
    for producer in 0..2{
        let a=c.b.ops.len();
        if producer==0{table_direct(c,word,truth.clone(),&[],d,rest);}else{mixed_mcx(c,prefix,d,rest);}
        let first=c.b.ops.split_off(a);
        if producer==0{let mut cs=prefix.to_vec();cs.push((d,true));mixed_mcx(c,&cs,out,rest);}else{table_direct(c,word,truth.clone(),&[(d,true)],out,rest);}
        let second=c.b.ops.split_off(a);
        let mut candidate=Vec::with_capacity(2*(first.len()+second.len()));
        for _ in 0..2{candidate.extend_from_slice(&first);candidate.extend_from_slice(&second);}
        if candidate.len()<=best.len() && score(&candidate)<score(&best){best=candidate;}
    }
    c.b.ops.extend(best);
}
fn table_direct(c:&mut Circuit,word:&[&QReg],truth:Vec<bool>,prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let (pol,terms)=super::metadata_muxlease::swap_terms(truth.clone(),word.len());
    let start=c.b.ops.len();let positive:Vec<_>=prefix.iter().map(|&(q,_)|(q,true)).collect();for &(q,b)in prefix{if !b{c.x(q);}}
    for(i,q)in word.iter().enumerate(){if pol>>i&1!=0{c.x(q);}}
    for m in terms{let mut cs=positive.clone();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));mixed_mcx(c,&cs,out,dirty);}
    for(i,q)in word.iter().enumerate().rev(){if pol>>i&1!=0{c.x(q);}}
    for &(q,b)in prefix.iter().rev(){if !b{c.x(q);}}let baseline=c.b.ops.split_off(start);
    if let Some(mut cubes)=super::q792_esop_r01::plan(word.len(),&truth,prefix.len()){
        for &(q,b)in prefix{if !b{c.x(q);}}let mut frame=0usize;
        while !cubes.is_empty(){let pick=(0..cubes.len()).min_by_key(|&i|{let(m,v)=cubes[i];((frame^(m^v))&m).count_ones()}).unwrap();let(m,v)=cubes.remove(pick);let toggles=(frame^(m^v))&m;for(i,q)in word.iter().enumerate(){if toggles>>i&1!=0{c.x(q);}}frame^=toggles;
            let mut cs=positive.clone();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));mixed_mcx(c,&cs,out,dirty);
        }for(i,q)in word.iter().enumerate(){if frame>>i&1!=0{c.x(q);}}for &(q,b)in prefix.iter().rev(){if !b{c.x(q);}}
        if c.b.ops.len()-start>=baseline.len(){c.b.ops.truncate(start);c.b.ops.extend(baseline);}
    }else{c.b.ops.extend(baseline);}
    super::q792_gpu_affine_r01::improve(c,word,&truth,prefix,out,dirty,start);
    super::q792_gpu_nonlinear_r01::improve(c,word,&truth,prefix,out,dirty,start);
}
fn branch(c:&mut Circuit,m:&[QReg],out:&QReg,dirty:&[QReg]){
    let word=[&m[8],&m[9],&m[14],&m[15],&m[18],&m[19]];
    table(c,&word,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[],out,dirty);
}
/// XOR all 21 original metadata bits into arbitrary target bits. Borrowed
/// targets are an interface for testing/readout, not 21 additional clean rails.
/// Production callers can consume one predicate instead of this entire bank.
pub(super) fn read_bank(c:&mut Circuit,m:&[QReg],g:&QReg,out:&[QReg],dirty:&[QReg]){
    assert_eq!(m.len(),20);assert_eq!(out.len(),21);assert!(dirty.len()>=16);
    let owned=c.b.next_qubit;let tag:Vec<_>=m[..4].iter().collect();let d=&dirty[0];let rest=&dirty[1..];
    let t15:Vec<_>=std::iter::once((g,true)).chain(m[..4].iter().map(|q|(q,true))).collect();
    // Unreflected ordinary low fields, with the disjoint tag15 replacement.
    for bit in 0..16{c.ccx(g,&m[4+bit],&out[5+bit]);}
    let mut term=t15.clone();term.extend([(&m[5],true),(&m[4],false)]);mixed_mcx(c,&term,&out[5],rest);
    for bit in 2..6{
        let mut cs=t15.clone();cs.push((&m[4+bit],true));mixed_mcx(c,&cs,&out[5+bit],rest);
        let mut cs=t15.clone();cs.push((&m[5],true));mixed_mcx(c,&cs,&out[5+bit],rest);
    }
    for bit in 2..4{let mut cs=t15.clone();cs.extend([(&m[5],true),(&m[16+bit],true)]);mixed_mcx(c,&cs,&out[17+bit],rest);}
    for bit in 0..5{
        let truth=(0..16).map(|t|{let r=if t<10{LOW[t]}else if t<15{EDGE[2*(t-10)]}else{0};r>>bit&1!=0}).collect();
        table(c,&tag,truth,&[(g,true)],&out[bit],rest);
        let mut prefix=t15.clone();prefix.push((&m[5],false));
        table(c,&m[6..10].iter().collect::<Vec<_>>(),(0..16).map(|i|i<12&&PEAK[i]>>bit&1!=0).collect(),&prefix,&out[bit],rest);
        if 29>>bit&1!=0{let mut cs=t15.clone();cs.push((&m[5],true));mixed_mcx(c,&cs,&out[bit],rest);}
    }
    // Shared dirty echo of the six-bit side test. Its incoming arbitrary
    // value cancels across the two consumers; all metadata and scratch return.
    let consume=|c:&mut Circuit|{
        for bit in 0..5{
            let truth=(0..16).map(|t|t>=10&&t<15&&(EDGE[2*(t-10)]^EDGE[2*(t-10)+1])>>bit&1!=0).collect();
            table(c,&tag,truth,&[(g,true),(d,true)],&out[bit],rest);
        }
        for bit in 0..16{table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&[(g,true),(d,true)],&out[5+bit],rest);}
    };
    consume(c);branch(c,m,d,rest);consume(c);branch(c,m,d,rest);
    assert_eq!(c.b.next_qubit,owned);
}
fn scalar(code:usize)->usize{
    let tag=code&15;let low=code>>4;let a=low&63;let c=low>>6&63;let sm=low>>12&15;
    let (r,a,c,sm)=if tag<10{(LOW[tag],a,c,sm)}else if tag<15{
        let side=usize::from((a>>4)+(c>>4)+(sm>>2)>=5);let z=if side==0{low}else{low^65535};
        (EDGE[2*(tag-10)+side],z&63,z>>6&63,z>>12&15)
    }else if a&2!=0{(29,63,c,sm&3)}else{(if a>>2<12{PEAK[a>>2]}else{0},a&1,c,sm)};
    r|a<<5|c<<11|sm<<17
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;
    let m=c.alloc_qreg_bits("fold20.metadata",20);let g=c.alloc_qreg("guard");let out=c.alloc_qreg_bits("arbitrary_readout_targets",21);let dirty=c.alloc_qreg_bits("borrowed",16);
    let n=c.b.next_qubit;read_bank(&mut c,&m,&g,&out,&dirty);assert_eq!(n,c.b.next_qubit);
    let ops=c.into_builder().ops;for op in &ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
    eprintln!("FOLD20_BANK_BUILT metadata=20 allocated_scratch=0 interface={n} ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
    let mut lanes=0u64;
    for guard in 0..2{for pattern in 0..2{for first in (0..1usize<<20).step_by(64){
        let mut seed=0x792f_20ab_1457u64^(first as u64)^((pattern as u64)<<32)^((guard as u64)<<40);
        let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();
        for bit in 0..20{before[m[bit].id()as usize]=(0..64).fold(0u64,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}
        before[g.id()as usize]=if guard==0{0}else{u64::MAX};
        let mut after=before.clone();if guard!=0{for l in 0..64{let value=scalar(first+l);for bit in 0..21{after[out[bit].id()as usize]^=((value>>bit&1)as u64)<<l;}}}
        let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.phase=0;sim.apply_iter(ops.iter());
        assert_eq!(sim.qubits,after,"readout first={first} guard={guard} pattern={pattern}");assert_eq!(sim.phase,0);
        sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before,"inverse");assert_eq!(sim.phase,0);lanes+=64;
    }}eprintln!("FOLD20_GUARD_PASS guard={guard} lanes={lanes}");}
    eprintln!("FOLD20_NATIVE_PASS metadata=20 lanes={lanes} phase=0 inverse=true all_physical_codes=true scratch_restored=true whole_Q792=false");
}


pub fn run_factor(){
 use crate::{sim::Simulator,circuit::OperationType as K};use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
 let mut total=0usize;let mut gain=0usize;
 for n in [4usize,5,6]{for k in [2usize,5,9]{for family in 0..8usize{
  let truth:Vec<_>=(0..1usize<<n).map(|x|match family{
   0=>x.count_ones()%2!=0,1=>x.count_ones()>=3,2=>(x&3)+(x>>2&3)+(x>>4&3)>=5,
   _=>{let z=(x as u64).wrapping_mul(0x9e3779b97f4a7c15).rotate_left((family*7)as u32);z.count_ones()%2!=0}
  }).collect();
  let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;
  let w=c.alloc_qreg_bits("word",n);let p=c.alloc_qreg_bits("prefix",k);let out=c.alloc_qreg("out");let d=c.alloc_qreg_bits("dirty",20);let owned=c.b.next_qubit;
  let word:Vec<_>=w.iter().collect();let prefix:Vec<_>=p.iter().enumerate().map(|(i,q)|(q,i%3!=1)).collect();
  table_direct(&mut c,&word,truth.clone(),&prefix,&out,&d);let old=c.b.ops.split_off(0);
  table(&mut c,&word,truth.clone(),&prefix,&out,&d);assert_eq!(owned,c.b.next_qubit);let ops=c.into_builder().ops;
  let count=|ops:&[crate::circuit::Op]|ops.iter().filter(|o|o.kind==K::CCX).count();assert!(ops.len()<=old.len());assert!(count(&ops)<=count(&old));gain+=count(&old)-count(&ops);
  for pattern in 0..2{for first in (0..1usize<<(n+k)).step_by(64){
   let mut seed=0x792fac701u64^first as u64^((family as u64)<<32)^((pattern as u64)<<48);
   let mut before:Vec<_>=(0..owned).map(|_|{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed}).collect();
   for(bit,q)in w.iter().chain(&p).enumerate(){before[q.id()as usize]=(0..64).fold(0u64,|v,l|v|((((first+l)>>bit&1)as u64)<<l));}
   let mut after=before.clone();for lane in 0..64{let x=first+lane;if truth[x&((1<<n)-1)]&&(0..k).all(|i|((x>>(n+i)&1)!=0)==(i%3!=1)){after[out.id()as usize]^=1u64<<lane;}}
   let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"factor n={n} k={k} f={family} first={first}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
  }}
 }}}
 assert!(gain>0);eprintln!("FOLD20_TABLE_FACTOR_PASS lanes={total} aggregate_component_T_saved={gain} arbitrary_dirty=true phase=0 inverse=true");
}
