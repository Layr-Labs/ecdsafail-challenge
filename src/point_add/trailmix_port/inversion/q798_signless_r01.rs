//! Native compact R01+Q01 regression against the existing exact pair.
use crate::point_add::trailmix_port::circuit::Circuit;
pub fn run() {
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:usize,l:usize,v:bool){let b=1u64<<l;w[q]=(w[q]&!b)|if v{b}else{0};}
    for name in ["Q799_MUX_LEASE","Q799_MUX_QUOTIENT","Q799_XOR_LO","Q799_PREFIX_TREE","Q799_T11_FIRST","Q799_HEAD_TREE"] {std::env::set_var(name,"1");}
    let data=std::fs::read(std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").expect("scalar capsule")).unwrap();
    assert_eq!(&data[..8],b"R5FSTEP1");let count=u32::from_le_bytes(data[8..12].try_into().unwrap())as usize;
    assert_eq!(data.len(),12+count*138);
    let mut lanes=0usize;
    for block in 0..26 {for post_j in 0..4 {
        let n=259-super::shared_step::SCHEDULE_SUPPORTS[block].0;let j=(post_j+3)%4;
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|r|(u16::from_le_bytes(r[..2].try_into().unwrap())as usize-1)/64==block && u16::from_le_bytes(r[..2].try_into().unwrap())as usize%4==post_j).collect();
        let mut programs=Vec::new();
        for new in [false,true] {
            let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
            let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=if new{None}else{Some(circ.alloc_qreg("sign"))};let _it=circ.alloc_qreg("it");
            let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("borrowed",24);
            assert_eq!(circ.b.next_qubit,if new{566}else{567});
            super::metadata_rotation5::rotate(&mut circ,&rank,&a,&p1,&p2,&w2,&helpers,false);
            if new{super::metadata_remainder015_funded::signless(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&w1,&w2,&helpers,j,n);}else{super::metadata_remainder015_funded::phase01_with_support(&mut circ,&rank,&a,&c,&sm,&p1,&p2,sign.as_ref().unwrap(),&w1,&w2,&helpers,j,n);super::metadata_arithmetic5_phased::phase01(&mut circ,&rank,&a,&c,&p1,&p2,sign.as_ref().unwrap(),&w1,&helpers);}
            assert_eq!(circ.b.next_qubit,if new{566}else{567});
            let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
            programs.push(b.ops);
        }
        for pattern in 0..4 {for batch in 0..rows.len().div_ceil(64) {
            let mut seed=79810+batch as u64+((pattern as u64)<<32);let mut before:Vec<_>=(0..567).map(|_|rnd(&mut seed)).collect();
            for l in 0..64 {let row=&rows[(batch*64+l)%rows.len()][2..70];for q in 0..543{put(&mut before,q,l,row[q/8]>>(q%8)&1!=0);}}
            let compact:Vec<_>=before.iter().enumerate().filter(|(q,_)|*q!=23).map(|(_,v)|*v).collect();
            let mut f=Fixed;let mut reference=Simulator::new(567,0,&mut f);reference.qubits.copy_from_slice(&before);reference.apply_iter(programs[0].iter());
            let on=!before[21]&before[22];assert_eq!(reference.qubits[23]&on,0,"R01 Sign output block={block} j={post_j} batch={batch}");
            let mut f=Fixed;let mut actual=Simulator::new(566,0,&mut f);actual.qubits.copy_from_slice(&compact);actual.apply_iter(programs[1].iter());
            let expected:Vec<_>=reference.qubits.iter().enumerate().filter(|(q,_)|*q!=23).map(|(_,v)|*v).collect();
            for q in 0..566 {assert_eq!(actual.qubits[q],expected[q],"R01 compact block={block} j={post_j} batch={batch} pattern={pattern} wire={q}");}
            assert_eq!(actual.phase,0);actual.apply_iter(programs[1].iter().rev());assert_eq!(actual.qubits,compact);assert_eq!(actual.phase,0);lanes+=64;
        }}
        eprintln!("SIGNLESS_R01_BLOCK_PASS block={block} j={post_j} records={} old_ops={} new_ops={} new_T={} owned=542 borrowed=24",rows.len(),programs[0].len(),programs[1].len(),programs[1].iter().filter(|o|o.kind==K::CCX).count());
    }}
    eprintln!("SIGNLESS_R01_PASS lanes={lanes}; actual 542-wire R01 component, no whole Q798 claim");
}


