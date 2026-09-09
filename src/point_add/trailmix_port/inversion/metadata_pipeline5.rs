//! C/S counter and full post-arithmetic boundary pipeline on the543 owned wires.
//! Input metadata is at entry clock; work words and Sign are post-arithmetic.
//! Terminal history is incremented here; physical arithmetic/rotations are separate.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
pub(super) fn pipeline(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,iteration:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],post_j:usize,lo:usize,hi:usize) {
    assert!(post_j<4&&helpers.len()>=24);let start=circ.b.ops.len();
    super::metadata_terminal5::emit(circ,rank,a,c,sm,helpers,post_j==0,false);
    super::metadata_phase_counter5::emit(circ,rank,a,c,sm,p1,p2,helpers,(post_j+3)%4);
    super::metadata_full_boundary5::boundary(circ,rank,a,c,sm,p1,p2,sign,iteration,w1,w2,helpers,post_j,lo,hi);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],i:usize,lane:usize,v:bool){let bit=1u64<<lane;w[i]=(w[i]&!bit)|if v{bit}else{0};}
pub fn run() {
    let supported=true;
    let path=std::env::var("LOWQ_METADATA_PIPELINE_CAPSULE").expect("explicit scalar entry capsule");
    let data=std::fs::read(path).expect("read entry capsule");assert_eq!(&data[..8],if supported{b"R5METAP1"}else{b"R5ENTRY1"});
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
        pipeline(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&iter,&w1,&w2,&helpers,j,lo,hi);assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_METADATA_PIPELINE5_BUILT j={j} T={} ops={} owned_inversion_wires=543 borrowed=24 block={block} lo={lo} hi={hi}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
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
                let history=if j==0 {(batch as usize*64+lane)%255}else{(batch as usize*64+lane)%256};
                for i in 0..6 {put(&mut before,c[i].id()as usize,lane,history>>i&1!=0);}
                for i in 0..4 {put(&mut before,sm[i].id()as usize,lane,history>>(i+6)&1!=0);}
                put(&mut before,w1[256].id()as usize,lane,false);
                for q in [&p1,&p2,&sign] {put(&mut before,q.id()as usize,lane,false);}
            }
            let mut after=before.clone();
            if j==0 {for lane in 0..64 {let history=1+(batch as usize*64+lane)%255;
                for i in 0..6 {put(&mut after,c[i].id()as usize,lane,history>>i&1!=0);}
                for i in 0..4 {put(&mut after,sm[i].id()as usize,lane,history>>(i+6)&1!=0);}
            }}
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
        eprintln!("CODEC_METADATA_PIPELINE5_CASE j={j} scalar_records={} PASS",rows.len());
    }}
    eprintln!("CODEC_METADATA_PIPELINE5_PASS lanes={total} scalar_records={count}; actual counter guards, terminal history increment, complete phase boundary, wrap exceptions, dirty restoration and literal inverse; arithmetic work words supplied externally, whole Q799 missing");
}
