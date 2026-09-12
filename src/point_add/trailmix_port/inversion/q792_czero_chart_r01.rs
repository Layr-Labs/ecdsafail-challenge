//! Unconditional reversible C0 chart. On C0: A8/S6 and six zero scratch rails.
//! On other metadata it is an arbitrary reversible extension, restored around
//! the sole phase00 comparator center. No clean qubit is allocated.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn trans(c:&mut Circuit,w:&[&QReg],d:&[QReg],x:usize,y:usize){
    if x==y{return;}let delta=x^y;let p=delta.trailing_zeros()as usize;let base=if x>>p&1==0{x}else{y};
    for i in 0..w.len(){if i!=p&&delta>>i&1!=0{c.cx(w[p],w[i]);}}
    let cs:Vec<_>=(0..w.len()).filter(|&i|i!=p).map(|i|(w[i],base>>i&1!=0)).collect();mixed_mcx(c,&cs,w[p],d);
    for i in (0..w.len()).rev(){if i!=p&&delta>>i&1!=0{c.cx(w[p],w[i]);}}
}
fn swaps()->Vec<(usize,usize)>{
    let ts=super::q792_fold20_rank_r01::triples();let mut pairs=Vec::new();
    for(r,t)in ts.iter().enumerate(){if t[1]!=0{continue;}let x=super::q792_fold20_rank_r01::encode(r,0,0,0,&ts);let tag=x&15;let cl=if tag==15{x>>6&15}else{x>>10&63};pairs.push((tag|cl<<4,t[0]|t[2]<<2));}
    let mut perm:Vec<_>=(0..1024).collect();let mut assigned=vec![false;1024];let mut used=assigned.clone();for &(x,y)in &pairs{assert!(!assigned[x]&&!used[y]);assigned[x]=true;used[y]=true;perm[x]=y;}
    for x in 0..1024{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=perm[y];}perm[y]=x;assigned[y]=true;used[x]=true;}}
    let mut seen=vec![false;1024];let mut out=Vec::new();for root in 0..1024{if seen[root]{continue;}seen[root]=true;let mut y=perm[root];while y!=root{assert!(!seen[y]);seen[y]=true;out.push((root,y));y=perm[y];}}
    for &(x,y)in &pairs{let mut z=x;for &(a,b)in &out{if z==a{z=b}else if z==b{z=a}}assert_eq!(z,y);}out
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],d:&[QReg],inverse:bool){
    assert_eq!(m.len(),20);assert!(d.len()>=16);let at=c.b.ops.len();
    // For C0 the reflected side is exactly C_low63 on an edge tag.
    let tag:Vec<_>=m[..4].iter().collect();let cs:Vec<_>=m[10..16].iter().map(|q|(q,true)).collect();
    for q in m[5..10].iter().chain(&m[16..20]){c.cx(&m[4],q);}super::q792_fold20_r01::table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&cs,&m[4],d);for q in m[5..10].iter().chain(&m[16..20]).rev(){c.cx(&m[4],q);}
    // Peak original A[2..6] and C are zero; move its index into C[0..4].
    for i in 0..4{let mut cs:Vec<_>=m[..4].iter().map(|q|(q,true)).collect();c.cx(&m[6+i],&m[10+i]);cs.push((&m[10+i],true));mixed_mcx(c,&cs,&m[6+i],d);c.cx(&m[6+i],&m[10+i]);}
    let word:Vec<_>=m[..4].iter().chain(&m[10..16]).collect();for(x,y)in swaps(){trans(c,&word,d,x,y);}if inverse{c.b.ops[at..].reverse();}
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x29)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let d=c.alloc_qreg_bits("dirty",20);let n=c.b.next_qubit;emit(&mut c,&m,&d,false);let ops=c.into_builder().ops;let ts=super::q792_fold20_rank_r01::triples();let mut cases=Vec::new();
    for code in 0..1<<20{if let Some((r,a,cl,sm))=super::q792_fold20_rank_r01::decode(code,&ts){if cl==0&&ts[r][1]==0&&super::q792_fold20_rank_r01::encode(r,a,cl,sm,&ts)==code{cases.push((code,ts[r][0]|ts[r][2]<<2|a<<4|sm<<16));}}}
    eprintln!("FOLD20_CZERO_BUILT metadata=20 scratch_zero=6 ops={} T={} cases={}",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count(),cases.len());let mut total=0;
    for pattern in 0..2{for first in (0..cases.len()).step_by(64){let mut seed=0x792c0010u64^first as u64^(pattern<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
        for lane in 0..64{let(x,y)=cases[(first+lane)%cases.len()];for bit in 0..20{let mask=1u64<<lane;before[bit]=(before[bit]&!mask)|(((x>>bit&1)as u64)<<lane);after[bit]=(after[bit]&!mask)|(((y>>bit&1)as u64)<<lane);}}
        let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}eprintln!("FOLD20_CZERO_NATIVE_PASS lanes={total} metadata20=true scratch_zero=6 inverse=true phase=0");
}
