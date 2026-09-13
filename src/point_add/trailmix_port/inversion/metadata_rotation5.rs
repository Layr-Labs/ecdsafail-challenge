//! Physical Work2 +/-1 rotations selected by existing phase bits.
//! Common reflection plus one of two directional reflections; no clean flag.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
fn pairs(n:usize,offset:usize)->Vec<(usize,usize)> {(0..n).filter_map(|i|{let j=(offset+n-i)%n;if i<j{Some((i,j))}else{None}}).collect()}
fn reflection(circ:&mut Circuit,word:&[QReg],guard:&QReg,offset:usize) {
    for (i,j) in pairs(word.len(),offset){circ.cx(&word[j],&word[i]);circ.ccx(guard,&word[i],&word[j]);circ.cx(&word[j],&word[i]);}
}
fn selected_reflection(circ:&mut Circuit,word:&[QReg],p1:&QReg,p2:&QReg,flag:&QReg,offset:usize,phase2:bool) {
    let pairs=pairs(word.len(),offset);
    if !phase2{circ.x(p2);}
    // Dirty echo over a whole reflection. The CNOT conjugations commute
    // with the flag update; cancel the middle pair before emitting gates.
    for &(i,j) in &pairs{circ.cx(&word[j],&word[i]);}
    for &(i,j) in &pairs{circ.ccx(flag,&word[i],&word[j]);}
    circ.ccx(p1,p2,flag);
    for &(i,j) in &pairs{circ.ccx(flag,&word[i],&word[j]);}
    for &(i,j) in &pairs{circ.cx(&word[j],&word[i]);}
    circ.ccx(p1,p2,flag);
    if !phase2{circ.x(p2);}
}
pub(super) fn rotate(circ:&mut Circuit,rank:&[QReg],a:&[QReg],p1:&QReg,p2:&QReg,word:&[QReg],helpers:&[QReg],post:bool) {
    assert_eq!(word.len(),259);assert!(helpers.len()>=16);let start=circ.b.ops.len();
    let terminal:Vec<_>=(0..5).map(|i|(&rank[i],29>>i&1!=0)).chain(a.iter().map(|q|(q,true))).collect();
    // Terminal canonical phase00 must skip the R pre-shift. Its marker
    // temporarily toggles P1; the post-shift is already off in phase00.
    if !post{mixed_mcx(circ,&terminal,p1,helpers);circ.x(p1);}
    reflection(circ,word,p1,0);
    selected_reflection(circ,word,p1,p2,&helpers[0],258,false);
    selected_reflection(circ,word,p1,p2,&helpers[0],1,true);
    if !post{circ.x(p1);mixed_mcx(circ,&terminal,p1,helpers);}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;
    for post in [false,true] {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let _c=circ.alloc_qreg_bits("c",6);let _sm=circ.alloc_qreg_bits("sm",4);let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let _sign=circ.alloc_qreg("sign");let _iter=circ.alloc_qreg("iter");let _w1=circ.alloc_qreg_bits("w1",259);let word=circ.alloc_qreg_bits("w2",259);assert_eq!(circ.b.next_qubit,543);let helpers=circ.alloc_qreg_bits("dirty",24);let owned=circ.b.next_qubit;
        rotate(&mut circ,&rank,&a,&p1,&p2,&word,&helpers,post);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_ROTATION5_BUILT post={post} T={} ops={} owned=543 borrowed=24",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        let mut cases=Vec::new();for r in 0..32{for al in 0..64{for phase in 0..4{let terminal=ts[r][0]*64+al==255;if terminal&&(r!=29||phase!=0){continue;}cases.push((r,al,phase,terminal));}}}
        for pattern in 0..8 {for batch in 0..cases.len().div_ceil(64){
            let mut seed=0x935e71c04da2bf68u64^batch as u64^((pattern as u64)<<32);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {let (r,al,phase,terminal)=cases[(batch*64+lane)%cases.len()];
                for i in 0..5 {for w in [&mut before,&mut after]{put(w,&rank[i],lane,r>>i&1!=0);}}
                for i in 0..6 {for w in [&mut before,&mut after]{put(w,&a[i],lane,al>>i&1!=0);}}
                for w in [&mut before,&mut after]{put(w,&p1,lane,phase&2!=0);put(w,&p2,lane,phase&1!=0);}
                let on=!terminal&&((phase>=2)==post);
                if on {for i in 0..259 {let from=if phase%2==0{(i+1)%259}else{(i+258)%259};let value=before[word[from].id()as usize]>>lane&1!=0;put(&mut after,&word[i],lane,value);}}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"rotation post={post} pattern={pattern} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }
    eprintln!("CODEC_ROTATION5_PASS lanes={total}; both directions, all phases, terminal marker, dirty data and inverse; complete arithmetic integration and whole Q799 missing");
}
