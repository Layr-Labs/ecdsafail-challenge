//! Folded high-index permutations on exactly twenty metadata wires.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="q792_fold20_rank_plan_r01.rs"] mod plan;
/// Exchange two affine cubes pointwise. The varying coordinates are omitted
/// from the controls; their possible XOR translation is handled by the basis.
fn exchange(c:&mut Circuit,m:&[QReg],g:&QReg,dirty:&[QReg],left:usize,right:usize,free:usize){
    let delta=left^right;let fixed=((1usize<<20)-1)^free;
    let pivot=(delta&fixed).trailing_zeros()as usize;assert!(pivot<20);
    let base=if left>>pivot&1==0{left}else{right};
    for i in 0..20{if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
    let mut cs=vec![(g,true)];cs.extend((0..20).filter(|&i|i!=pivot&&fixed>>i&1!=0).map(|i|(&m[i],base>>i&1!=0)));
    mixed_mcx(c,&cs,&m[pivot],dirty);
    for i in (0..20).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],g:&QReg,dirty:&[QReg],axis:usize,inverse:bool){
    assert_eq!(m.len(),20);assert!(dirty.len()>=20);
    let plans=[plan::AXIS0,plan::AXIS1,plan::AXIS2,plan::AXIS3];let at=c.b.ops.len();let n=c.b.next_qubit;
    for &(x,y,free)in plans[axis]{exchange(c,m,g,dirty,x,y,free);}
    if inverse{c.b.ops[at..].reverse();}assert_eq!(n,c.b.next_qubit);
}
pub(super) fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
pub(super) fn decode(code:usize,ts:&[[usize;3]])->Option<(usize,usize,usize,usize)>{
    let tag=code&15;let low=code>>4;let mut a=low&63;let mut c=low>>6&63;let mut sm=low>>12&15;
    let r=if tag<10{ts.iter().enumerate().filter(|(_,t)|t.iter().sum::<usize>()<=2).nth(tag)?.0}
    else if tag<15{let side=usize::from((a>>4)+(c>>4)+(sm>>2)>=5);if side!=0{a^=63;c^=63;sm^=15;}
        ts.iter().enumerate().filter(|(_,t)|t.iter().sum::<usize>()==3).nth(2*(tag-10)+side)?.0}
    else{if a&2!=0{return None;}let r=ts.iter().enumerate().filter(|(_,t)|t.iter().sum::<usize>()==4).nth(a>>2)?.0;a&=1;r};
    let raw=[64*ts[r][0]+a,64*ts[r][1]+c,64*ts[r][2]+4*sm];
    if raw[0]>254||raw.iter().sum::<usize>()>257{return None;}
    Some((r,a,c,sm))
}
pub(super) fn encode(r:usize,a:usize,c:usize,sm:usize,ts:&[[usize;3]])->usize{
    let sum=ts[r].iter().sum::<usize>();let index=ts[..r].iter().filter(|t|if sum<=2{t.iter().sum::<usize>()<=2}else{t.iter().sum::<usize>()==sum}).count();
    if sum<=2{return index|(a|c<<6|sm<<12)<<4;}
    if sum==3{return (10+index/2)|((a|c<<6|sm<<12)^if index&1!=0{65535}else{0})<<4;}
    assert!(a+c+4*sm<=1);15|((a|index<<2)|c<<6)<<4
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    use std::collections::BTreeMap;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let ts=triples();let mut total=0u64;let mut enabled=0u64;
    for axis in 0..4{
        let mut groups:BTreeMap<Vec<usize>,Vec<(usize,usize)>>=BTreeMap::new();
        for (r,t)in ts.iter().enumerate(){let key=if axis<3{t.iter().enumerate().filter(|(i,_)|*i!=axis).map(|(_,v)|*v).collect()}else{vec![t[0],t[1]+t[2]]};groups.entry(key).or_default().push((if axis<3{t[axis]}else{t[1]},r));}
        let mut successors=[0usize;32];for row in groups.values_mut(){row.sort();for i in 0..row.len(){successors[row[i].1]=row[(i+1)%row.len()].1;}}
        let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("fold20.metadata",20);let g=c.alloc_qreg("guard");let dirty=c.alloc_qreg_bits("arbitrary_lenders",20);let n=c.b.next_qubit;
        emit(&mut c,&m,&g,&dirty,axis,false);let ops=c.into_builder().ops;for op in &ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        eprintln!("FOLD20_RANK_BUILT axis={axis} metadata=20 scratch_allocated=0 ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
        let mut active_axis=0;
        for pattern in 0..3{for first in (0..1usize<<20).step_by(64){
            let mut seed=0x792c_e7af_1234u64^(first as u64)^((axis as u64)<<40)^((pattern as u64)<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();
            for bit in 0..20{before[m[bit].id()as usize]=(0..64).fold(0u64,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}
            before[g.id()as usize]=0;let mut after=before.clone();
            for lane in 0..64{
                if pattern==0{continue;}let code=first+lane;
                if let Some((r,a,cl,sm))=decode(code,&ts){let nr=successors[r];let sum=64*ts[nr].iter().sum::<usize>()+a+cl+4*sm;
                    if 64*ts[nr][0]+a>254||sum>257{continue;}
                    assert_eq!(encode(r,a,cl,sm,&ts),code,"canonical original code");
                    let next=encode(nr,a,cl,sm,&ts);for w in [&mut before,&mut after]{w[g.id()as usize]|=1u64<<lane;}
                    for bit in 0..20{let mask=1u64<<lane;after[m[bit].id()as usize]=(after[m[bit].id()as usize]&!mask)|(((next>>bit&1)as u64)<<lane);}
                    enabled+=1;active_axis+=1;
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"rank axis={axis} first={first} pattern={pattern}");assert_eq!(sim.phase,0);
            sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("FOLD20_RANK_AXIS_PASS axis={axis} active_lanes={active_axis} inverse=true phase=0");
    }
    eprintln!("FOLD20_RANK_NATIVE_PASS metadata=20 lanes={total} active={enabled} scratch_allocated=0 whole_Q792=false");
}
