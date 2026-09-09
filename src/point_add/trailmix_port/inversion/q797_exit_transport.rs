//! Native cycle-exit cargo transport check for the public reversible benchmark.
use crate::point_add::trailmix_port::circuit::Circuit;
pub fn run() {
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],i:usize,l:usize,v:bool){let b=1u64<<l;w[i]=(w[i]&!b)|if v{b}else{0};}
    fn bits(w:&[u64],first:usize,n:usize,l:usize)->usize{(0..n).map(|i|(((w[first+i]>>l)&1)as usize)<<i).sum()}
    let data=std::fs::read(std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").unwrap()).unwrap();assert_eq!(&data[..8],b"R5FSTEP1");
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut lanes=0;let mut active=0;
    for block in 0..26 {
        let (lo,hi)=super::metadata_entry_head5::A_SUPPORTS[block];let mut programs=Vec::new();
        for mode in 0..3 {
            let mut circ=Circuit::new();circ.q797_a_support=Some((lo,hi));
            let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
            let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("borrowed_phase");let it=circ.alloc_qreg("it");
            let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("other_borrowed",if mode==0{24}else{23});
            if mode==0 {super::q798_step::before_exit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&it,&w1,&w2,&helpers,0,block);}
            else if mode==1 {super::metadata_exit_boundary5::exit_signless(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&it,&w1,&w2,&helpers,lo,hi);}
            else {super::metadata_exit_boundary5::exit_phase_cargo(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&it,&w1,&w2,&helpers,lo,hi);}
            assert_eq!(circ.b.next_qubit,if mode==0{566}else{565});let b=circ.into_builder();
            for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}programs.push(b.ops);
        }
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|r|{let t=u16::from_le_bytes(r[..2].try_into().unwrap())as usize;(t-1)/64==block&&t%4==0}).collect();
        for pattern in 0..4 {for batch in 0..rows.len().div_ceil(64) {
            let mut seed=0x797e01782345u64^(batch as u64)^((pattern as u64)<<32);
            let mut input:Vec<_>=(0..566).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64 {let record=&rows[(batch*64+lane)%rows.len()][2..70];for i in 0..542{let old=if i<23{i}else{i+1};put(&mut input,i,lane,record[old/8]>>(old%8)&1!=0);}}
            let mut f=Fixed;let mut prefix=Simulator::new(566,0,&mut f);prefix.qubits.copy_from_slice(&input);prefix.apply_iter(programs[0].iter());assert_eq!(prefix.phase,0);
            let mut before=prefix.qubits[..565].to_vec();
            let mut f=Fixed;let mut reference=Simulator::new(565,0,&mut f);reference.qubits.copy_from_slice(&before);reference.apply_iter(programs[1].iter());assert_eq!(reference.phase,0);let mut after=reference.qubits;
            for lane in 0..64 {
                let r=bits(&before,0,5,lane);let al=bits(&before,5,6,lane);let cl=bits(&before,11,6,lane);let sm=bits(&before,17,4,lane);
                if before[21]>>lane&1==0||before[22]>>lane&1==0||sm!=0||triples[r][2]!=0||(r==0&&al==0&&cl==0){continue;}
                let cv=64*triples[r][1]+cl;assert!((1..256).contains(&cv));let target=283+259-cv;
                let rnew=bits(&after,0,5,lane);let anew=64*triples[rnew][0]+bits(&after,5,6,lane);let output=24+anew;
                assert_eq!(before[target]>>lane&1,1,"input residual head");assert_eq!(after[output]>>lane&1,1,"output coefficient head");
                let cargo=rnd(&mut seed)&1!=0;put(&mut before,target,lane,cargo);put(&mut after,output,lane,cargo);active+=1;
            }
            let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(programs[2].iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("exit cargo block={block} batch={batch} pattern={pattern} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(programs[2].iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
        }}
        eprintln!("Q797_EXIT_CARGO_BLOCK block={block} base_ops={} cargo_ops={} physical=565 PASS",programs[1].len(),programs[2].len());
    }
    eprintln!("Q797_EXIT_CARGO_PASS lanes={lanes} active={active}; residual head through length update and metadata cleanup, dirty restoration; not full Q797");
}
