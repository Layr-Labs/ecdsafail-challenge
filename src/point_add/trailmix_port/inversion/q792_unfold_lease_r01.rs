//! In-place twenty-to-twenty-one decoding, funded by one explicitly leased
//! zero bit. The caller must park/return that bit without increasing Q.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q792_fold20_r01::table,length_recompute::mixed_mcx};
const LOW:[usize;10]=[0,1,2,4,5,8,13,14,17,23];
const EDGE:[usize;10]=[3,6,9,11,15,18,20,24,26,29];
const PEAK:[usize;12]=[7,10,12,16,19,21,22,25,27,28,30,31];
pub(super) fn permutation(c:&mut Circuit,w:&[&QReg],g:&QReg,d:&[QReg],pairs:&[(usize,usize)]){permutation_prefix(c,w,&[(g,true)],d,pairs);}
fn permutation_prefix(c:&mut Circuit,w:&[&QReg],prefix:&[(&QReg,bool)],d:&[QReg],pairs:&[(usize,usize)]){
    let n=1<<w.len();let mut p:Vec<_>=(0..n).collect();let mut assigned=vec![false;n];let mut used=assigned.clone();
    for &(x,y)in pairs{assert!(!assigned[x]&&!used[y]);p[x]=y;assigned[x]=true;used[y]=true;}
    for x in 0..n{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=p[y];}p[y]=x;assigned[y]=true;used[x]=true;}}
    let mut seen=vec![false;n];for root in 0..n{if seen[root]{continue;}seen[root]=true;let mut y=p[root];while y!=root{assert!(!seen[y]);seen[y]=true;let delta=root^y;let pivot=delta.trailing_zeros()as usize;let base=if root>>pivot&1==0{root}else{y};
        for i in 0..w.len(){if i!=pivot&&delta>>i&1!=0{c.cx(w[pivot],w[i]);}}
        let mut cs=prefix.to_vec();cs.extend((0..w.len()).filter(|&i|i!=pivot).map(|i|(w[i],base>>i&1!=0)));mixed_mcx(c,&cs,w[pivot],d);
        for i in (0..w.len()).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(w[pivot],w[i]);}}y=p[y];
    }}
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],lease:&QReg,g:&QReg,d:&[QReg],inverse:bool){
    assert_eq!(m.len(),20);assert!(d.len()>=16);let at=c.b.ops.len();let n=c.b.next_qubit;let flag=&d[0];let rest=&d[1..];let tag:Vec<_>=m[..4].iter().collect();let coarse=[&m[8],&m[9],&m[14],&m[15],&m[18],&m[19]];
    // Exact product echo: either factor can be computed into the arbitrary
    // lender. Choose the smaller emitted circuit, retaining both full truths.
    let echo_start=c.b.ops.len();
    for _ in 0..2{table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&[],flag,rest);table(c,&coarse,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[(g,true),(flag,true)],lease,rest);}
    let old_echo=c.b.ops.split_off(echo_start);
    for _ in 0..2{table(c,&coarse,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[],flag,rest);table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&[(g,true),(flag,true)],lease,rest);}
    if c.b.ops.len()-echo_start>=old_echo.len(){c.b.ops.truncate(echo_start);c.b.ops.extend(old_echo);}
    for q in &m[4..]{c.ccx(g,lease,q);}
    let rank:Vec<_>=m[..4].iter().chain(std::iter::once(lease)).collect();let mut pairs:Vec<_>=LOW.iter().enumerate().map(|(i,&r)|(i,r)).collect();pairs.extend(EDGE.iter().enumerate().map(|(i,&r)|(10+i/2+(i%2)*16,r)));pairs.push((15,PEAK[0]));permutation(c,&rank,g,d,&pairs);
    // Terminal uses the A1 marker. Handle it separately, then every peak
    // conversion preserves A0 and has A1=0, exposing a nine-bit permutation.
    let word:Vec<_>=rank.iter().copied().chain(m[4..10].iter()).collect();permutation(c,&word,g,d,&[(PEAK[0]|(2<<5),29|(63<<5))]);
    let peak_word:Vec<_>=rank.iter().copied().chain(m[6..10].iter()).collect();let pairs:Vec<_>=PEAK.iter().enumerate().map(|(i,&r)|(PEAK[0]|(i<<5),r)).collect();
    // A1 remains unchanged under this permutation. Its 0 cofactor may be
    // included directly in every transposition without a new clean flag.
    permutation_prefix(c,&peak_word,&[(g,true),(&m[5],false)],d,&pairs);
    if inverse{c.b.ops[at..].reverse();}assert_eq!(c.b.next_qubit,n);
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x37)}}fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("fold20",20);let lease=c.alloc_qreg("funded-zero-only-under-guard");let g=c.alloc_qreg("guard");let d=c.alloc_qreg_bits("dirty",20);let n=c.b.next_qubit;emit(&mut c,&m,&lease,&g,&d,false);let ops=c.into_builder().ops;let ts=super::q792_fold20_rank_r01::triples();let mut cases=Vec::new();
    for code in 0..1<<20{if let Some((r,a,cl,sm))=super::q792_fold20_rank_r01::decode(code,&ts){if super::q792_fold20_rank_r01::encode(r,a,cl,sm,&ts)==code{cases.push((code,r,a,cl,sm));}}}for h in 0..256{cases.push((47|(h<<10),29,63,h&63,h>>6));}
    let mut total=0;for guard in [false,true]{for batch in 0..cases.len().div_ceil(64){let mut seed=0x792dec0deu64^batch as u64;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();for lane in 0..64{let(code,r,a,cl,sm)=cases[(batch*64+lane)%cases.len()];let result=(r&15)|(a<<4)|(cl<<10)|(sm<<16)|((r>>4)<<20);for bit in 0..20{let mask=1u64<<lane;before[bit]=(before[bit]&!mask)|(((code>>bit&1)as u64)<<lane);after[bit]=(after[bit]&!mask)|((((if guard{result}else{code})>>bit&1)as u64)<<lane);}}
        before[21]=if guard{u64::MAX}else{0};after[21]=before[21];if guard{before[20]=0;after[20]=(0..64).fold(0,|v,l|v|(((cases[(batch*64+l)%cases.len()].1>>4)as u64)<<l));}
        let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"unfold guard={guard} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}eprintln!("FOLD20_LEASED_UNFOLD_PASS lanes={total} cases={} ops={} T={} zero_lease_required=true scratch_allocated=0 wholeQ792=false",cases.len(),ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
}
