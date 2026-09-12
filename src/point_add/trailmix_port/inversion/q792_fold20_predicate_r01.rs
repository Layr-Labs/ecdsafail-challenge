//! Fused metadata conjunctions: consume 20 bits directly into one data target.
//! No decoded metadata bank or clean scratch is allocated.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{length_recompute::mixed_mcx,q792_fold20_r01::table};
const LOW:[usize;10]=[0,1,2,4,5,8,13,14,17,23];
const EDGE:[usize;10]=[3,6,9,11,15,18,20,24,26,29];
const PEAK:[usize;12]=[7,10,12,16,19,21,22,25,27,28,30,31];
/// Mask/value refer to the original21 fields [rank5,A6,C6,SM4]. External
/// controls and target/lenders must be distinct from the20 metadata rails.
pub(super) fn toggle(c:&mut Circuit,m:&[QReg],mask:usize,value:usize,prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    assert_eq!(m.len(),20);assert!(dirty.len()>=20);assert_eq!(mask&value,value);assert!(mask<1<<21);
    let n=c.b.next_qubit;let rm=mask&31;let rv=value&31;let lm=mask>>5;let lv=value>>5;
    let rmatch=|r:usize|r&rm==rv;let tag:Vec<_>=m[..4].iter().collect();let d=&dirty[0];let rest=&dirty[1..];
    let normal=(0..16).map(|t|t<15&&rmatch(if t<10{LOW[t]}else{EDGE[2*(t-10)]})).collect::<Vec<_>>();
    let low_controls=|reflected:bool|{let mut cs=prefix.to_vec();cs.extend((0..16).filter(|&i|lm>>i&1!=0).map(|i|(&m[4+i],(lv>>i&1!=0)^reflected)));cs};
    table(c,&tag,normal.clone(),&low_controls(false),out,dirty);
    let consume=|c:&mut Circuit|{
        for reflected in [false,true]{let mut cs=low_controls(reflected);cs.push((d,true));let truth=(0..16).map(|t|(10..15).contains(&t)&&rmatch(EDGE[2*(t-10)+usize::from(reflected)])).collect();table(c,&tag,truth,&cs,out,rest);}
    };
    let compute=|c:&mut Circuit|{let word=[&m[8],&m[9],&m[14],&m[15],&m[18],&m[19]];table(c,&word,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[],d,rest);};
    consume(c);compute(c);consume(c);compute(c);
    // tag15 active peak: A_low1..5 are logical zeros, while their physical
    // locations store the twelve-way peak index. A0/C/SM remain literal.
    if lv&62==0{
        let mut cs=prefix.to_vec();cs.extend(m[..4].iter().map(|q|(q,true)));cs.push((&m[5],false));
        if lm&1!=0{cs.push((&m[4],lv&1!=0));}
        cs.extend((6..16).filter(|&i|lm>>i&1!=0).map(|i|(&m[4+i],lv>>i&1!=0)));
        table(c,&m[6..10].iter().collect::<Vec<_>>(),(0..16).map(|i|i<12&&rmatch(PEAK[i])).collect(),&cs,out,dirty);
    }
    // Canonical terminal: rank29/A63, history in literal C6 and SM_low2.
    if rmatch(29)&&lv&lm&63==lm&63&&lv&(3<<14)==0{
        let mut cs=prefix.to_vec();cs.extend(m[..4].iter().map(|q|(q,true)));cs.push((&m[5],true));
        cs.extend((6..14).filter(|&i|lm>>i&1!=0).map(|i|(&m[4+i],lv>>i&1!=0)));mixed_mcx(c,&cs,out,dirty);
    }
    assert_eq!(c.b.next_qubit,n);
}
pub(super) fn rank_low(c:&mut Circuit,m:&[QReg],rank_truth:u32,lm:usize,lv:usize,prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    assert_eq!(m.len(),20);assert!(dirty.len()>=20);assert_eq!(lm&lv,lv);assert!(lm<1<<16);
    let n=c.b.next_qubit;
    let rmatch=|r:usize|rank_truth>>r&1!=0;let tag:Vec<_>=m[..4].iter().collect();let d=&dirty[0];let rest=&dirty[1..];
    let normal=(0..16).map(|t|t<15&&rmatch(if t<10{LOW[t]}else{EDGE[2*(t-10)]})).collect::<Vec<_>>();
    let low_controls=|reflected:bool|{let mut cs=prefix.to_vec();cs.extend((0..16).filter(|&i|lm>>i&1!=0).map(|i|(&m[4+i],(lv>>i&1!=0)^reflected)));cs};
    table(c,&tag,normal.clone(),&low_controls(false),out,dirty);
    let consume=|c:&mut Circuit|{
        for reflected in [false,true]{let mut cs=low_controls(reflected);cs.push((d,true));let truth=(0..16).map(|t|(10..15).contains(&t)&&rmatch(EDGE[2*(t-10)+usize::from(reflected)])).collect();table(c,&tag,truth,&cs,out,rest);}
    };
    let compute=|c:&mut Circuit|{let word=[&m[8],&m[9],&m[14],&m[15],&m[18],&m[19]];table(c,&word,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[],d,rest);};
    consume(c);compute(c);consume(c);compute(c);
    // tag15 active peak: A_low1..5 are logical zeros, while their physical
    // locations store the twelve-way peak index. A0/C/SM remain literal.
    if lv&62==0{
        let mut cs=prefix.to_vec();cs.extend(m[..4].iter().map(|q|(q,true)));cs.push((&m[5],false));
        if lm&1!=0{cs.push((&m[4],lv&1!=0));}
        cs.extend((6..16).filter(|&i|lm>>i&1!=0).map(|i|(&m[4+i],lv>>i&1!=0)));
        table(c,&m[6..10].iter().collect::<Vec<_>>(),(0..16).map(|i|i<12&&rmatch(PEAK[i])).collect(),&cs,out,dirty);
    }
    // Canonical terminal: rank29/A63, history in literal C6 and SM_low2.
    if rmatch(29)&&lv&lm&63==lm&63&&lv&(3<<14)==0{
        let mut cs=prefix.to_vec();cs.extend(m[..4].iter().map(|q|(q,true)));cs.push((&m[5],true));
        cs.extend((6..14).filter(|&i|lm>>i&1!=0).map(|i|(&m[4+i],lv>>i&1!=0)));mixed_mcx(c,&cs,out,dirty);
    }
    assert_eq!(c.b.next_qubit,n);
}
fn decoded(code:usize)->Option<usize>{
    let tag=code&15;let low=code>>4;let a=low&63;let cl=low>>6&63;let sm=low>>12&15;
    let(r,a,cl,sm)=if tag<10{(LOW[tag],a,cl,sm)}else if tag<15{let side=usize::from((a>>4)+(cl>>4)+(sm>>2)>=5);let v=low^if side!=0{65535}else{0};(EDGE[2*(tag-10)+side],v&63,v>>6&63,v>>12&15)}else if a&2!=0{(29,63,cl,sm&3)}else{if a>>2>=12{return None;}(PEAK[a>>2],a&1,cl,sm)};
    Some(r|a<<5|cl<<11|sm<<17)
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut requests:Vec<(usize,usize)>=(0..21).flat_map(|i|[(1<<i,0),(1<<i,1<<i)]).collect();
    requests.extend([(31,29),(63<<5,0),(63<<11,1<<11),(15<<17,0),((1<<21)-1,29|63<<5),((1<<21)-1,0)]);
    let mut total=0u64;let mut max_t=0;
    for (request,&(mask,value))in requests.iter().enumerate(){
        let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("metadata20",20);let g=c.alloc_qreg("external_guard");let data=c.alloc_qreg("external_data_control");let out=c.alloc_qreg("arbitrary_target");let dirty=c.alloc_qreg_bits("arbitrary_lenders",20);let n=c.b.next_qubit;
        toggle(&mut c,&m,mask,value,&[(&g,true),(&data,false)],&out,&dirty);assert_eq!(n,c.b.next_qubit);let ops=c.into_builder().ops;for op in &ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}let t=ops.iter().filter(|o|o.kind==K::CCX).count();max_t=max_t.max(t);
        for first in (0..1usize<<20).step_by(64){
            let mut seed=0x792e_f103_bu64^first as u64^((request as u64)<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();for bit in 0..20{before[m[bit].id()as usize]=(0..64).fold(0u64,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}
            let mut after=before.clone();for lane in 0..64{if let Some(logical)=decoded(first+lane){if logical&mask==value&&(before[g.id()as usize]>>lane&1)!=0&&(before[data.id()as usize]>>lane&1)==0{after[out.id()as usize]^=1u64<<lane;}}else{before[g.id()as usize]&=!(1u64<<lane);after[g.id()as usize]&=!(1u64<<lane);}}
            let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"predicate request={request} first={first}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
        eprintln!("FOLD20_PREDICATE_PASS request={request} mask={mask} value={value} T={t} ops={}",ops.len());
    }
    eprintln!("FOLD20_PREDICATE_NATIVE_PASS metadata=20 lanes={total} requests={} max_T={max_t} scratch_allocated=0 phase=0 inverse=true whole_Q792=false",requests.len());
}
