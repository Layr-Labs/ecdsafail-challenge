//! Sequential1616-step native core with retained dirty helpers and full reversal.
//! Initial/final encoding is supplied by scalar capsules; lifecycle is not claimed.
use crate::point_add::trailmix_port::circuit::Circuit;
use crate::circuit::{Op,OperationType};
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],i:usize,lane:usize,v:bool){let bit=1u64<<lane;w[i]=(w[i]&!bit)|if v{bit}else{0};}
fn build(block:usize,j:usize)->Vec<Op> {
    let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
    let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let iter=circ.alloc_qreg("iter");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);assert_eq!(circ.b.next_qubit,543);
    let helpers=circ.alloc_qreg_bits("borrowed",24);assert_eq!(circ.b.next_qubit,567);
    super::metadata_full_step5::step(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&iter,&w1,&w2,&helpers,j,block);assert_eq!(circ.b.next_qubit,567);
    let b=circ.into_builder();for op in &b.ops {op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
    b.ops
}
pub fn run() {
    let path=std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").expect("explicit scalar step capsule");let data=std::fs::read(path).unwrap();assert_eq!(&data[..8],b"R5FSTEP1");
    let count=u32::from_le_bytes(data[8..12].try_into().unwrap())as usize;assert_eq!(data.len(),12+138*count);assert!(count>0&&count%1616==0);
    let rows:Vec<_>=data[12..].chunks_exact(138).collect();let inputs=count/1616;let batches=inputs.div_ceil(64);
    for row in 0..count {assert_eq!(u16::from_le_bytes(rows[row][..2].try_into().unwrap())as usize,row%1616+1);}
    let mut states=Vec::new();
    for batch in 0..batches {
        let mut seed=0x17b46d580a9c23efu64^batch as u64;let mut state:Vec<_>=(0..567).map(|_|rnd(&mut seed)).collect();
        for lane in 0..64 {let row=rows[((batch*64+lane)%inputs)*1616];for i in 0..543 {put(&mut state,i,lane,row[2+i/8]>>(i%8)&1!=0);}}
        states.push(state);
    }
    let initial=states.clone();let mut total_ops=0u64;let mut total_t=0u64;let mut step_lanes=0usize;
    for inverse in [false,true] {
        for z in 0..26 {let block=if inverse{25-z}else{z};let templates:Vec<_>=(0..4).map(|j|build(block,j)).collect();
            let first=64*block;let end=(first+64).min(1616);
            for zstep in 0..end-first {let step=if inverse{end-1-zstep}else{first+zstep};let ops=&templates[(step+1)%4];
                if !inverse{total_ops+=ops.len()as u64;total_t+=ops.iter().filter(|o|o.kind==OperationType::CCX).count()as u64;}
                for batch in 0..batches {
                    let mut f=Fixed;let mut sim=Simulator::new(567,0,&mut f);sim.qubits=std::mem::take(&mut states[batch]);
                    if inverse{sim.apply_iter(ops.iter().rev());}else{sim.apply_iter(ops.iter());}
                    assert_eq!(sim.phase,0,"core phase block={block} step={step} inverse={inverse}");
                    let mut expected=initial[batch].clone();
                    for lane in 0..64 {let row=rows[((batch*64+lane)%inputs)*1616+step];let offset=if inverse{2}else{70};for i in 0..543 {put(&mut expected,i,lane,row[offset+i/8]>>(i%8)&1!=0);}}
                    if sim.qubits!=expected {let diffs:Vec<_>=sim.qubits.iter().zip(&expected).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("core step={step} batch={batch} inverse={inverse} diffs={diffs:?}");}
                    states[batch]=sim.qubits;step_lanes+=64;
                }
            }
            eprintln!("CODEC_CORE5_BLOCK inverse={inverse} block={block} first={first} end={end} trajectory_lanes={} PASS",batches*64);
        }
    }
    assert_eq!(states,initial);
    eprintln!("CODEC_CORE5_PASS inputs={inputs} trajectory_lanes={} steps=1616 step_lanes={step_lanes} forward_ops={total_ops} forward_T={total_t} four_traversal_ops={} four_traversal_T={}; sequential state and24 dirty helpers retained, full literal inverse; initialization and final lifecycle supplied externally, whole Q799 missing",batches*64,4*total_ops,4*total_t);
}
