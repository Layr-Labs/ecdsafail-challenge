//! Native phase update followed by C recoding under the actual entry Sign.
//! Input: post-arithmetic/post-counter active state; j is post-step clock mod4.
//! Does not include the later S-zero phase flips, cycle exit or terminal history.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_phase115_programs.rs"] mod rank_programs;

fn triples()->Vec<[usize;3]> {
    (0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()
}
fn mcx_cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
/// Toggle one target by B times an exact five-bit rank function, using an
/// arbitrary borrowed helper only when the dirty echo beats direct cubes.
fn rank_toggle(circ:&mut Circuit,rank:&[QReg],cubes:&[(u16,u16)],base:&[(&QReg,bool)],out:&QReg,helpers:&[QReg]){
    if super::metadata_muxlease::active("Q793_RANK_ECHO_ENTRY")&&helpers.len()>=2{
        let truth:Vec<_>=(0..32u16).map(|x|cubes.iter().fold(false,|v,&(m,b)|v^((x&m)==b))).collect();
        let (polarity,terms)=super::metadata_muxlease::swap_terms(truth,5);
        let direct:usize=cubes.iter().map(|(m,_)|mcx_cost(base.len()+m.count_ones()as usize)).sum();
        let echo=2*terms.iter().map(|m|mcx_cost(m.count_ones()as usize)).sum::<usize>()+2*mcx_cost(base.len()+1);
        if echo<direct{let d=&helpers[0];let dirty=&helpers[1..];for &(q,_)in base{assert_ne!(q.id(),d.id());}
            let compute=|circ:&mut Circuit|{for i in 0..5{if polarity>>i&1!=0{circ.x(&rank[i]);}}for &m in &terms{let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)).collect();match cs.len(){0=>circ.x(d),1=>circ.cx(cs[0].0,d),_=>mixed_mcx(circ,&cs,d,dirty)}}for i in (0..5).rev(){if polarity>>i&1!=0{circ.x(&rank[i]);}}};
            let consume=|circ:&mut Circuit|{let mut cs=base.to_vec();cs.push((d,true));mixed_mcx(circ,&cs,out,dirty);};consume(circ);compute(circ);consume(circ);compute(circ);return;}
    }
    for &(m,v)in cubes{let mut cs=base.to_vec();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,out,helpers);}
}
fn empty_q(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&[QReg],extra:&[(&QReg,bool)],out:&QReg,helpers:&[QReg],p1:&QReg) {
    if super::metadata_muxlease::active("Q795_ENTRY_FACTOR"){
        // Exact refactoring of both old rank predicates, retaining the Q795
        // correction's P1=false guard even when the high decoder is shared.
        for(r,t)in triples().iter().enumerate(){
            let high=rank_programs::C_EQUAL[0].iter().fold(false,|x,&(m,v)|x^((r as u16&m)==v));
            assert_eq!(high,t[1]==0);assert_eq!(r<4,t[0]==0&&t[1]==0);
        }
        let mut base=extra.to_vec();base.extend(c.iter().map(|q|(q,false)));rank_toggle(circ,rank,rank_programs::C_EQUAL[0],&base,out,helpers);
        let mut cs=extra.to_vec();
        if super::metadata_muxlease::active("Q795_PHASE_LOAN"){
            if cs.iter().any(|(q,v)|q.id()==p1.id()&&*v){return;}
            if !cs.iter().any(|(q,_)|q.id()==p1.id()){cs.push((p1,false));}
        }
        cs.extend(rank[2..5].iter().chain(a).chain(c).map(|q|(q,false)));cs.push((&w1[2],true));mixed_mcx(circ,&cs,out,helpers);return;
    }
    for (r,t) in triples().iter().enumerate() {
        if t[1]!=0 {continue;}
        let mut cs=extra.to_vec();cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));cs.extend(c.iter().map(|q|(q,false)));
        mixed_mcx(circ,&cs,out,helpers);
        // Raw C0 also codes the sole full quotient256, at rawA0. Its leading
        // quotient bit Work1[2] distinguishes it from the empty quotient.
        if t[0]==0 {
            if super::metadata_muxlease::active("Q795_PHASE_LOAN"){
                if cs.iter().any(|(q,v)|q.id()==p1.id()&&*v){continue;}
                if !cs.iter().any(|(q,_)|q.id()==p1.id()){cs.push((p1,false));}
            }
            cs.extend(a.iter().map(|q|(q,false)));cs.push((&w1[2],true));
            mixed_mcx(circ,&cs,out,helpers);
        }
    }
}
pub(super) fn entry(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize) {
    entry_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,helpers,j,0,256);
}
pub(super) fn entry_with_support(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,lo:usize,hi:usize) {
    assert!(j<4 && helpers.len()>=23);let start=circ.b.ops.len();
    // In pre-existing phase11, Sign xor P1=0; treating C as a quotient
    // during the first pair therefore cancels even though C stores LR.
    for q in [sign,p1] {empty_q(circ,rank,a,c,w1,&[(q,true)],p2,helpers,p1);}
    mixed_mcx(circ,&[(p1,true),(p2,true)],sign,helpers);
    empty_q(circ,rank,a,c,w1,&[(p1,false),(p2,true)],sign,helpers,p1);
    // Sign now marks entry exactly, including trueS256. No leased guard.
    super::metadata_entry_head5::transfer_with_support(circ,rank,a,c,sm,p1,p2,sign,w2,w1,helpers,j,false,lo,hi);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],i:usize,lane:usize,v:bool){let bit=1u64<<lane;w[i]=(w[i]&!bit)|if v{bit}else{0};}
pub fn run() {
    let supported=std::env::var("LOWQ_CODEC_ENTRY_SUPPORTED").ok().as_deref()==Some("1");
    let path=std::env::var("LOWQ_ENTRY_BOUNDARY_CAPSULE").expect("explicit scalar entry capsule");
    let data=std::fs::read(path).expect("read entry capsule");assert_eq!(&data[..8],if supported{b"R5ENTS01"}else{b"R5ENTRY1"});
    let rowlen=if supported{138}else{137};let offset=if supported{2}else{1};
    let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
    assert_eq!(data.len(),12+count*rowlen);assert!(count>0&&count<=1_000_000);
    let mut total=0;
    for block in 0..if supported{26}else{1} {for j in 0..4 {
        let (lo,hi)=if supported{super::metadata_entry_head5::A_SUPPORTS[block]}else{(0,256)};
        let rows:Vec<_>=data[12..].chunks_exact(rowlen).filter(|r|{
            if supported {let t=u16::from_le_bytes(r[..2].try_into().unwrap())as usize;(t-1)/64==block&&t%4==j}
            else {r[0]as usize==j}
        }).collect();

        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let _iter=circ.alloc_qreg("iter");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);assert_eq!(circ.b.next_qubit,543);
        let helpers=circ.alloc_qreg_bits("borrowed",24);let owned=circ.b.next_qubit;
        entry_with_support(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&w1,&w2,&helpers,j,lo,hi);assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_ENTRY_BOUNDARY5_BUILT j={j} T={} ops={} owned_inversion_wires=543 borrowed=24 block={block} lo={lo} hi={hi}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        for pattern in 0..2 {for batch in 0..rows.len().div_ceil(64) {
            let mut seed=0x79eb650f12a4dc38u64^batch as u64^((pattern as u64)<<32);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let row=rows[(batch*64+lane)%rows.len()];
                for (w,record) in [(&mut before,&row[offset..offset+68]),(&mut after,&row[offset+68..offset+136])] {
                    for i in 0..543 {put(w,i,lane,record[i/8]>>(i%8)&1!=0);}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after {let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("entry boundary j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        // Already-terminal phase00/Sign0 is identity for arbitrary history,
        // work data, and dirty helpers. The full terminal lifecycle is separate.
        for batch in 0..8 {
            let mut seed=0x8a145de782039b6fu64^batch;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64 {
                for i in 0..5 {put(&mut before,rank[i].id()as usize,lane,29>>i&1!=0);}
                for q in &a {put(&mut before,q.id()as usize,lane,true);}
                for q in [&p1,&p2,&sign] {put(&mut before,q.id()as usize,lane,false);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
        eprintln!("CODEC_ENTRY_BOUNDARY5_CASE j={j} scalar_records={} PASS",rows.len());
    }}
    eprintln!("CODEC_ENTRY_BOUNDARY5_PASS lanes={total} scalar_records={count}; actual entry guard, Q256 distinction, dirty restoration and literal inverse; cycle exit and whole Q799 missing");
}
