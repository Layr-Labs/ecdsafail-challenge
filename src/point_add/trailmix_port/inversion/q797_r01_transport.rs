//! Native R01 transport prerequisite with a second phase-rail cargo.
use crate::point_add::trailmix_port::circuit::Circuit;
#[path="metadata_phase115_programs.rs"] mod rank_programs;
pub fn run() {
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],i:usize,l:usize,v:bool){let b=1u64<<l;w[i]=(w[i]&!b)|if v{b}else{0};}
    let data=std::fs::read(std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").unwrap()).unwrap();assert_eq!(&data[..8],b"R5FSTEP1");
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut lanes=0;let mut active=0;
    for block in 0..26 {for post_j in 0..4 {
        let j=(post_j+3)%4;let mut programs=Vec::new();
        for cargo in [false,true] {
            let mut circ=Circuit::new();circ.q797_a_support=Some(super::metadata_entry_head5::A_SUPPORTS[block]);
            let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
            let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("borrowed_phase");let _it=circ.alloc_qreg("it");
            let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("other_borrowed",23);assert_eq!(circ.b.next_qubit,565);
            super::metadata_rotation5::rotate(&mut circ,&rank,&a,&p1,&p2,&w2,&helpers,false);
            if cargo {
                let base=vec![(&p1,false),(&p2,true)];let mut terms=vec![base.clone()];
                for &(m,v) in rank_programs::C_EQUAL[0] {
                    let mut term=base.clone();term.extend(c.iter().map(|q|(q,false)));
                    term.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
                    terms.push(term);
                }
                super::q797_cargo_moves::adjacent_a_terms(&mut circ,&rank,&a,&w2,1,2,&terms,&helpers);
            }
            super::metadata_remainder015_funded::signless(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&w1,&w2,&helpers,j,259-super::shared_step::SCHEDULE_SUPPORTS[block].0);
            let mut ops=std::mem::take(&mut circ.b.ops);super::shared_optimize::cancel_nct(&mut ops,2048,8);super::shared_optimize::cancel_nct_live(&mut ops,2048);circ.b.ops=ops;
            assert_eq!(circ.b.next_qubit,565);let b=circ.into_builder();
            for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}programs.push(b.ops);
        }
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|r|{let t=u16::from_le_bytes(r[..2].try_into().unwrap())as usize;(t-1)/64==block&&t%4==post_j}).collect();
        for pattern in 0..4 {for batch in 0..rows.len().div_ceil(64) {
            let mut seed=0x797a01012345u64^(batch as u64)^((pattern as u64)<<32);
            let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64 {let record=&rows[(batch*64+lane)%rows.len()][2..70];for i in 0..542{let old=if i<23{i}else{i+1};put(&mut before,i,lane,record[old/8]>>(old%8)&1!=0);}}
            let mut f=Fixed;let mut reference=Simulator::new(565,0,&mut f);reference.qubits.copy_from_slice(&before);reference.apply_iter(programs[0].iter());assert_eq!(reference.phase,0);
            let mut after=reference.qubits;
            for lane in 0..64 {
                if before[21]>>lane&1!=0||before[22]>>lane&1==0{continue;}
                let r=(0..5).map(|i|(((before[i]>>lane)&1)as usize)<<i).sum::<usize>();
                let al=(0..6).map(|i|(((before[5+i]>>lane)&1)as usize)<<i).sum::<usize>();
                let cl=(0..6).map(|i|(((before[11+i]>>lane)&1)as usize)<<i).sum::<usize>();
                let empty=64*triples[r][1]+cl==0;let a=64*triples[r][0]+al;
                let input=if empty{24+a}else{283+a};let output=if empty{24+a}else{283+a+2};
                assert_eq!(before[input]>>lane&1,u64::from(empty),"entry cargo slot");assert_eq!(after[output]>>lane&1,u64::from(empty),"output cargo slot");
                let cargo=rnd(&mut seed)&1!=0;put(&mut before,input,lane,cargo);put(&mut after,output,lane,cargo);active+=1;
            }
            let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(programs[1].iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("R01 cargo block={block} j={j} batch={batch} pattern={pattern} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(programs[1].iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
        }}
        eprintln!("Q797_R01_CARGO_BLOCK block={block} j={j} base_ops={} cargo_ops={} physical=565 PASS",programs[0].len(),programs[1].len());
    }}
    eprintln!("Q797_R01_CARGO_PASS lanes={lanes} active={active}; C0 coefficient-head loan or C>0 moving gap, full R01 and dirty restoration; not full Q797");
}
