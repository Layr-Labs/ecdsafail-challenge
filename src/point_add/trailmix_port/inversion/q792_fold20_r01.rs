//! Own 20-bit folded metadata readout. No clean scratch; whole Q792 unproved.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
const LOW:[usize;10]=[0,1,2,4,5,8,13,14,17,23];
const EDGE:[usize;10]=[3,6,9,11,15,18,20,24,26,29];
const PEAK:[usize;12]=[7,10,12,16,19,21,22,25,27,28,30,31];

pub(super) fn table(c:&mut Circuit,word:&[&QReg],truth:Vec<bool>,prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
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
