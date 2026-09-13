//! Unconditional A<=3 chart: rank5, literal A2/C6/SM4 and three zero rails.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn trans(c:&mut Circuit,w:&[&QReg],d:&[QReg],x:usize,y:usize){
    if x==y{return;}let delta=x^y;let p=delta.trailing_zeros()as usize;let base=if x>>p&1==0{x}else{y};
    for i in 0..w.len(){if i!=p&&delta>>i&1!=0{c.cx(w[p],w[i]);}}
    let mut cs=Vec::new();cs.extend((0..w.len()).filter(|&i|i!=p).map(|i|(w[i],base>>i&1!=0)));mixed_mcx(c,&cs,w[p],d);
    for i in (0..w.len()).rev(){if i!=p&&delta>>i&1!=0{c.cx(w[p],w[i]);}}
}
fn swaps()->Vec<(usize,usize)>{
    let ts=super::q792_fold20_rank_r01::triples();let mut pairs=Vec::new();
    for(r,t)in ts.iter().enumerate(){if t[0]!=0{continue;}let x=super::q792_fold20_rank_r01::encode(r,0,0,0,&ts);let tag=x&15;let ahi=(x>>6)&15;pairs.push((tag|ahi<<4,r));}
    let mut perm:Vec<_>=(0..256).collect();let mut assigned=[false;256];let mut used=[false;256];
    for &(x,y)in &pairs{assert!(!assigned[x]&&!used[y]);assigned[x]=true;used[y]=true;perm[x]=y;}
    // Close every open partial-permutation path with one edge.
    for x in 0..256{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=perm[y];}assert!(!assigned[y]&&!used[x]);perm[y]=x;assigned[y]=true;used[x]=true;}}
    let mut seen=[false;256];let mut out=Vec::new();for root in 0..256{if seen[root]{continue;}seen[root]=true;let mut y=perm[root];while y!=root{assert!(!seen[y]);seen[y]=true;out.push((root,y));y=perm[y];}}
    for &(x,y)in &pairs{let mut z=x;for &(a,b)in &out{if z==a{z=b}else if z==b{z=a}}assert_eq!(z,y);}
    out
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],d:&[QReg],inverse:bool){
    assert_eq!(m.len(),20);assert!(d.len()>=20);let at=c.b.ops.len();let owned=c.b.next_qubit;
    let ts=super::q792_fold20_rank_r01::triples();let mut reflected=Vec::new();for(r,t)in ts.iter().enumerate(){if t[0]!=0||t.iter().sum::<usize>()!=3{continue;}let x=super::q792_fold20_rank_r01::encode(r,0,0,0,&ts);if x>>6&15==15{reflected.push(x&15);}}
    for tag in reflected{let mut cs:Vec<_>=(0..4).map(|i|(&m[i],tag>>i&1!=0)).collect();cs.extend(m[6..10].iter().map(|q|(q,true)));for q in m[5..6].iter().chain(&m[10..20]){c.cx(&m[4],q);}mixed_mcx(c,&cs,&m[4],d);for q in m[5..6].iter().chain(&m[10..20]).rev(){c.cx(&m[4],q);}}
    let word:Vec<_>=m[..4].iter().chain(&m[6..10]).collect();for(x,y)in swaps(){trans(c,&word,d,x,y);}
    if inverse{c.b.ops[at..].reverse();}assert_eq!(owned,c.b.next_qubit);
}
pub(super) fn rank(m:&[QReg])->Vec<QReg>{m[..4].iter().chain(std::iter::once(&m[6])).map(QReg::borrowed_alias).collect()}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x32)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let ts=super::q792_fold20_rank_r01::triples();let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let d=c.alloc_qreg_bits("d",20);let n=c.b.next_qubit;emit(&mut c,&m,&d,false);assert_eq!(c.b.next_qubit,n);let ops=c.into_builder().ops;let mut active=0;
    for first in (0..1usize<<20).step_by(64){let mut seed=0x792a51u64^first as u64;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();for bit in 0..20{before[bit]=(0..64).fold(0,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}let mut after=before.clone();let mut care=0u64;
        for lane in 0..64{let Some((r,a,cl,sm))=super::q792_fold20_rank_r01::decode(first+lane,&ts)else{continue;};if ts[r][0]!=0||a>3{continue;}let next=(r&15)|((r>>4)<<6)|(a<<4)|(cl<<10)|(sm<<16);care|=1u64<<lane;active+=1;for bit in 0..20{let mask=1u64<<lane;after[bit]=(after[bit]&!mask)|(((next>>bit&1)as u64)<<lane);}}
        let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());for bit in 0..20{assert_eq!((sim.qubits[bit]^after[bit])&care,0,"Asmall first={first} bit={bit}");}assert_eq!(&sim.qubits[20..],&before[20..]);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
    }eprintln!("FOLD20_ASMALL_NATIVE_PASS lanes=1048576 active={active} rank5_Alo2_Clo6_SM4_zero3=true ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
}
