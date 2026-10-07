//! Guarded twenty-wire S0 chart: A8/C8 plus four zero cargo rails.
//! The caller supplies a guard which implies S0 and the admitted folded state.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn trans(c:&mut Circuit,w:&[&QReg],g:&QReg,d:&[QReg],x:usize,y:usize){
    if x==y{return;}let delta=x^y;let p=delta.trailing_zeros()as usize;let base=if x>>p&1==0{x}else{y};
    for i in 0..w.len(){if i!=p&&delta>>i&1!=0{c.cx(w[p],w[i]);}}
    let mut cs=vec![(g,true)];cs.extend((0..w.len()).filter(|&i|i!=p).map(|i|(w[i],base>>i&1!=0)));mixed_mcx(c,&cs,w[p],d);
    for i in (0..w.len()).rev(){if i!=p&&delta>>i&1!=0{c.cx(w[p],w[i]);}}
}
fn swaps()->Vec<(usize,usize)>{
    let ts=super::q792_fold20_rank_r01::triples();let mut pairs=Vec::new();
    for(r,t)in ts.iter().enumerate(){if t[2]!=0{continue;}let x=super::q792_fold20_rank_r01::encode(r,0,0,0,&ts);
        let tag=x&15;let sm=if tag==15{(x>>6)&15}else{x>>16&15};pairs.push((tag|sm<<4,t[0]|t[1]<<2));}
    let mut perm:Vec<_>=(0..256).collect();let mut assigned=[false;256];let mut used=[false;256];
    for &(x,y)in &pairs{assert!(!assigned[x]&&!used[y]);assigned[x]=true;used[y]=true;perm[x]=y;}
    // Close every open partial-permutation path with one edge.
    for x in 0..256{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=perm[y];}assert!(!assigned[y]&&!used[x]);perm[y]=x;assigned[y]=true;used[x]=true;}}
    let mut seen=[false;256];let mut out=Vec::new();for root in 0..256{if seen[root]{continue;}seen[root]=true;let mut y=perm[root];while y!=root{assert!(!seen[y]);seen[y]=true;out.push((root,y));y=perm[y];}}
    for &(x,y)in &pairs{let mut z=x;for &(a,b)in &out{if z==a{z=b}else if z==b{z=a}}assert_eq!(z,y);}
    out
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],g:&QReg,d:&[QReg],inverse:bool){
    assert_eq!(m.len(),20);assert!(d.len()>=20);let at=c.b.ops.len();let owned=c.b.next_qubit;
    // Canonical terminal/history0 is a disjoint endpoint; it exposes A255/C0.
    let ts=super::q792_fold20_rank_r01::triples();let terminal=15|(2<<4);let legacy=super::q792_fold20_rank_r01::encode(29,63,0,0,&ts);
    trans(c,&m.iter().collect::<Vec<_>>(),g,d,terminal,legacy);
    // Reflected S0 rows are exactly tags11 and14 with SM15. Keep side until packing.
    for tag in [11usize,14]{let mut cs=vec![(g,true)];cs.extend((0..4).map(|i|(&m[i],tag>>i&1!=0)));cs.extend(m[16..20].iter().map(|q|(q,true)));
        // Conjugate one predicate write by a CX fanout; controls are disjoint.
        for q in &m[5..16]{c.cx(&m[4],q);}mixed_mcx(c,&cs,&m[4],d);for q in m[5..16].iter().rev(){c.cx(&m[4],q);}}
    // Peak low A[2..6] contains only the peak index; SM is zero. Exchange roles.
    for i in 0..4{let mut cs=vec![(g,true)];cs.extend(m[..4].iter().map(|q|(q,true)));c.cx(&m[6+i],&m[16+i]);cs.push((&m[16+i],true));mixed_mcx(c,&cs,&m[6+i],d);c.cx(&m[6+i],&m[16+i]);}
    let word:Vec<_>=m[..4].iter().chain(&m[16..20]).collect();for(x,y)in swaps(){trans(c,&word,g,d,x,y);}
    if inverse{c.b.ops[at..].reverse();}assert_eq!(owned,c.b.next_qubit);
}
pub(super) fn aa(m:&[QReg])->Vec<QReg>{m[4..10].iter().chain(&m[..2]).map(QReg::borrowed_alias).collect()}
pub(super) fn cc(m:&[QReg])->Vec<QReg>{m[10..16].iter().chain(&m[2..4]).map(QReg::borrowed_alias).collect()}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x43)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let g=c.alloc_qreg("g");let d=c.alloc_qreg_bits("dirty",20);let n=c.b.next_qubit;
    emit(&mut c,&m,&g,&d,false);let ops=c.into_builder().ops;let ts=super::q792_fold20_rank_r01::triples();let mut total=0;let mut active=0;
    eprintln!("FOLD20_SZERO_BUILT metadata=20 cargo_zero=4 ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
    for pattern in 0..3{for first in (0..1usize<<20).step_by(64){let mut seed=0x792e1710u64^first as u64^(pattern<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();
        for bit in 0..20{before[m[bit].id()as usize]=(0..64).fold(0,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}before[g.id()as usize]=0;let mut after=before.clone();
        for lane in 0..64{if pattern==0{continue;}let code=first+lane;let raw=if code==47{Some((255,0))}else{super::q792_fold20_rank_r01::decode(code,&ts).and_then(|(r,a,c,s)|if ts[r][2]==0&&s==0{Some((a+64*ts[r][0],c+64*ts[r][1]))}else{None})};
            let Some((a,cl))=raw else{continue;};for w in [&mut before,&mut after]{w[g.id()as usize]|=1<<lane;}let next=(a>>6)|((cl>>6)<<2)|((a&63)<<4)|((cl&63)<<10);
            for bit in 0..20{let mask=1u64<<lane;after[m[bit].id()as usize]=(after[m[bit].id()as usize]&!mask)|(((next>>bit&1)as u64)<<lane);}active+=1;
        }
        let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"S0 first={first} pattern={pattern}");assert_eq!(sim.phase,0);
        sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}eprintln!("FOLD20_SZERO_NATIVE_PASS lanes={total} active={active} metadata=20 cargo_zero=4 inverse=true phase=0 whole_Q792=false");
}
