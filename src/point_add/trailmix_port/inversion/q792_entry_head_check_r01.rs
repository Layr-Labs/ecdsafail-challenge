use super::*;
use crate::{circuit::OperationType,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let lo:usize=std::env::var("LOWQ_CODEC_A_LO").ok().map(|s|s.parse().unwrap()).unwrap_or(0);
    let hi:usize=std::env::var("LOWQ_CODEC_A_HI").ok().map(|s|s.parse().unwrap()).unwrap_or(256);
    assert!(lo<hi&&hi<=256);
    let count_only=std::env::var("LOWQ_CODEC_RESOURCE_ONLY").ok().as_deref()==Some("1");
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();let mut total=0;let mut wraps=0;
    for j in 0..4 {for inverse in [false,true] {
        let mut circ=Circuit::new();let m=circ.alloc_qreg_bits("fold20",20);
        let p1=circ.alloc_qreg("phase1");let p2=circ.alloc_qreg("phase2");let guard=circ.alloc_qreg("independent_guard");let source=circ.alloc_qreg_bits("source",259);let prefix=circ.alloc_qreg_bits("dirty_word",259);let helpers=circ.alloc_qreg_bits("dirty_helpers",20);let owned=circ.b.next_qubit;
        transfer_with_support(&mut circ,&m,&p1,&p2,&guard,&source,&prefix,&helpers,j,inverse,lo,hi);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("FOLD20_ENTRY_HEAD_BUILT j={j} inverse={inverse} T={} ops={} metadata_wires=20 component_wires={owned}",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());if count_only{continue;}
        let mut cases=Vec::new();
        for av in lo..hi.min(255) {for st in 1..=256 {
            let sr=st%256;
            if sr%4!=(4-j)%4 {continue;}
            for delta in 0..3 {
                if av+st+delta>=257 {continue;}
                let cv=257-av-st-delta;
                if cv>255 {continue;}
                let r=triples.iter().position(|q|*q==[av>>6,0,sr>>6]).unwrap();
                let to=triples.iter().position(|q|*q==[av>>6,cv>>6,sr>>6]).unwrap();
                let sl=(sr%64)>>2;let ell=cv+st;
                for on in [false,true] {cases.push((r,to,av,sl,ell,cv,on));}
            }
        }}
        let batches=(cases.len()+63)/64;
        for batch in 0..batches {
            let mut seed=0x73591b2df68a40ceu64^batch as u64^((j as u64)<<32)^((inverse as u64)<<40);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {
                let (r,to,av,sl,ell,cv,on)=cases[(batch*64+lane)%cases.len()];
                put(&mut before,&guard,lane,on);put(&mut after,&guard,lane,on);
                if !on{continue;}
                let (rin,rout,cin,cout)=if inverse{(to,r,cv&63,0)}else{(r,to,0,cv&63)};
                let from=super::super::q792_fold20_rank_r01::encode(rin,av&63,cin,sl,&triples);let to=super::super::q792_fold20_rank_r01::encode(rout,av&63,cout,sl,&triples);for i in 0..20{put(&mut before,&m[i],lane,from>>i&1!=0);put(&mut after,&m[i],lane,to>>i&1!=0);}
                for w in [&mut before,&mut after]{put(w,&p1,lane,true);put(w,&p2,lane,true);for i in av+2..259-ell {put(w,&source[i],lane,false);}put(w,&source[259-ell],lane,true);}
                if ell==257&&cv==1{wraps+=1;}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("transfer j={j} inverse={inverse} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
        eprintln!("FOLD20_ENTRY_HEAD_CASE j={j} inverse={inverse} semantic_records={} PASS",cases.len());
    }}
    if count_only{eprintln!("FOLD20_ENTRY_HEAD_COUNT_ONLY correctness_unchecked");return;}
    eprintln!("FOLD20_ENTRY_HEAD_PASS lanes={total} S256_lanes={wraps}; two addressed head bits and rank packing, both directions, all lenders restored; caller boundary and full Q799 missing");
}
