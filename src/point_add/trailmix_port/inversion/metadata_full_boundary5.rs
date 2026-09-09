//! Full rank5 post-arithmetic boundary, with actual phase entry/exit and S-zero flips.
//! Already-terminal history has been incremented on quarter steps by the caller.
//! At j0 an already-terminal history must be nonzero; newly completed history is0.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_remainder5_programs.rs"] mod programs;
fn s_zero_phase_flips(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],helpers:&[QReg],j:usize) {
    if j%2!=0{return;}
    // For phases01/10, S1=(j/2) xor C0. Swap these phases only at S0.
    // The surrounding CNOTs put phase parity in P1, so phases00/11 are identity.
    circ.cx(p2,p1);
    for &(m,v) in programs::EQUAL[4] {
        let mut cs=vec![(p1,true),(sign,false),(&c[0],j==2)];
        cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
        mixed_mcx(circ,&cs,p2,helpers);
    }
    if j==0 {
        // At the first trueS256 ascent, entry phase update already changed
        // phase00 to01. Cancel this odd-phase swap as well as the even one.
        let mut peak=vec![(p1,true),(sign,false)];peak.extend(rank.iter().map(|q|(q,false)));peak.extend(a.iter().map(|q|(q,false)));peak.extend(c.iter().map(|q|(q,false)));peak.extend(sm.iter().map(|q|(q,false)));peak.push((&w1[2],false));
        mixed_mcx(circ,&peak,p2,helpers);
    }
    circ.cx(p2,p1);
    if j!=0{return;}
    // For phases00/11 the two low S bits are0 at j0. Flip both phase bits
    // using their invariant parity, with reversible corrections for exceptions.
    circ.cx(p1,p2);
    let base=vec![(p2,false),(sign,false)];
    for &(m,v) in programs::EQUAL[4] {
        let mut cs=base.clone();cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
        mixed_mcx(circ,&cs,p1,helpers);
    }
    // First R-ascent trueS256: rawA0,C0 and Work1[2] padding0. Its phase
    // stays unchanged. The phase11 trueS256 entry has Sign1 and was already excluded.
    let mut peak=base.clone();peak.extend(rank.iter().map(|q|(q,false)));peak.extend(a.iter().map(|q|(q,false)));peak.extend(c.iter().map(|q|(q,false)));peak.extend(sm.iter().map(|q|(q,false)));peak.push((&w1[2],false));
    mixed_mcx(circ,&peak,p1,helpers);
    // Terminal history lives in C_low6/S_mid[0..2], not an old shift byte.
    // Under S_upper0 only its low6 can be nonzero. Exclude rank29,A_low63,
    // C_low!=0 by XOR of all-C and C-zero cubes. Newly completed history0
    // still flips phase11->00; already-terminal j0 history was incremented.
    let mut terminal=base;terminal.extend((0..5).map(|i|(&rank[i],29>>i&1!=0)));terminal.extend(a.iter().map(|q|(q,true)));terminal.extend(sm.iter().map(|q|(q,false)));
    mixed_mcx(circ,&terminal,p1,helpers);terminal.extend(c.iter().map(|q|(q,false)));mixed_mcx(circ,&terminal,p1,helpers);
    circ.cx(p1,p2);
}
pub(super) fn boundary(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,lo:usize,hi:usize) {
    assert!(j<4&&helpers.len()>=24);let start=circ.b.ops.len();
    super::metadata_entry_boundary5::entry_with_support(circ,rank,a,c,sm,p1,p2,sign,w1,w2,helpers,j,lo,hi);
    if j==0 {super::metadata_exit_boundary5::exit(circ,rank,a,c,sm,p1,p2,sign,iteration,w1,w2,helpers,lo,hi);}
    s_zero_phase_flips(circ,rank,a,c,sm,p1,p2,sign,w1,helpers,j);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],i:usize,lane:usize,v:bool){let bit=1u64<<lane;w[i]=(w[i]&!bit)|if v{bit}else{0};}
pub fn run() {
    let supported=true;
    let path=std::env::var("LOWQ_FULL_BOUNDARY_CAPSULE").expect("explicit scalar entry capsule");
    let data=std::fs::read(path).expect("read entry capsule");assert_eq!(&data[..8],if supported{b"R5BOUND1"}else{b"R5ENTRY1"});
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
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let iter=circ.alloc_qreg("iter");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);assert_eq!(circ.b.next_qubit,543);
        let helpers=circ.alloc_qreg_bits("borrowed",24);let owned=circ.b.next_qubit;
        boundary(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&iter,&w1,&w2,&helpers,j,lo,hi);assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_FULL_BOUNDARY5_BUILT j={j} T={} ops={} owned_inversion_wires=543 borrowed=24 block={block} lo={lo} hi={hi}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
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
                let history=if j==0 {1+(batch as usize*64+lane)%255}else{(batch as usize*64+lane)%256};
                for i in 0..6 {put(&mut before,c[i].id()as usize,lane,history>>i&1!=0);}
                for i in 0..4 {put(&mut before,sm[i].id()as usize,lane,history>>(i+6)&1!=0);}
                put(&mut before,w1[256].id()as usize,lane,false);
                for q in [&p1,&p2,&sign] {put(&mut before,q.id()as usize,lane,false);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
        eprintln!("CODEC_FULL_BOUNDARY5_CASE j={j} scalar_records={} PASS",rows.len());
    }}
    eprintln!("CODEC_FULL_BOUNDARY5_PASS lanes={total} scalar_records={count}; phase entry, funded exit, S-zero flips, wrap exceptions, terminal history identity, dirty restoration and literal inverse; whole Q799 missing");
}
