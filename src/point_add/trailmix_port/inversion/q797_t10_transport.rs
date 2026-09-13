//! Existing signless T10 with a second parked phase-loan cargo; no new arithmetic.
//! Physical prerequisite for a borrowed phase rail; not a whole Q797 claim.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_phase115_programs.rs"] mod programs;
fn enable(circ:&mut Circuit,rank:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]) {
    for &(m,v) in programs::C_EQUAL[0] {
        let mut cs=vec![(p1,true),(p2,false)];
        cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));
        cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
        mixed_mcx(circ,&cs,g,dirty);
    }
}
fn loan(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&[QReg],g:&QReg,dirty:&[QReg]) {
    let(q,ops)=super::q798_handoffs::gather_a(circ,rank,a,w1,1,dirty);
    circ.cx(q,g);circ.cx(g,q);circ.cx(q,g);circ.b.ops.extend(ops.into_iter().rev());
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize) {
    assert!(helpers.len()>=23);let start=circ.b.ops.len();let sign=&helpers[0];let dirty=&helpers[1..];
    loan(circ,rank,a,w1,sign,dirty);circ.ccx(p1,p2,sign);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    super::metadata_arithmetic5_encoded::phase10_with_support(circ,rank,a,c,p1,p2,sign,w1,w2,dirty,n);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    circ.ccx(p1,p2,sign);loan(circ,rank,a,w1,sign,dirty);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);circ.b.ops.extend(tail);
}
pub fn run() {
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],i:usize,l:usize,v:bool){let b=1u64<<l;w[i]=(w[i]&!b)|if v{b}else{0};}
    let data=std::fs::read(std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").unwrap()).unwrap();
    assert_eq!(&data[..8],b"R5FSTEP1");
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut lanes=0;let mut active=0;
    for block in 0..26 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let _sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("borrowed_phase");let _it=circ.alloc_qreg("it");
        let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("other_borrowed",23);
        assert_eq!(circ.b.next_qubit,565);let n=super::shared_step::SCHEDULE_SUPPORTS[block].1;
        emit(&mut circ,&rank,&a,&c,&p1,&p2,&w1,&w2,&helpers,n);
        assert_eq!(circ.b.next_qubit,565);let b=circ.into_builder();
        for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|r|(u16::from_le_bytes(r[..2].try_into().unwrap())as usize-1)/64==block).collect();
        for pattern in 0..4 {for batch in 0..rows.len().div_ceil(64) {
            let mut seed=0x797c1054321u64^(batch as u64)^((pattern as u64)<<32);
            let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64 {
                let record=&rows[(batch*64+lane)%rows.len()][2..70];
                for i in 0..542{let old=if i<23{i}else{i+1};put(&mut before,i,lane,record[old/8]>>(old%8)&1!=0);}
            }
            let mut after=before.clone();
            for lane in 0..64 {
                let r=(0..5).map(|i|(((before[i]>>lane)&1)as usize)<<i).sum::<usize>();
                let al=(0..6).map(|i|(((before[5+i]>>lane)&1)as usize)<<i).sum::<usize>();
                let cl=(0..6).map(|i|(((before[11+i]>>lane)&1)as usize)<<i).sum::<usize>();
                if before[21]>>lane&1==0 || before[22]>>lane&1!=0{continue;}
                let width=64*triples[r][0]+al+2;assert!(width<=n);
                let cv=64*triples[r][1]+cl;
                let slot=if cv==1{width+1}else{width};let head=w1[slot].id()as usize;
                assert_eq!(before[head]>>lane&1!=0,cv!=1,"cargo slot promise");
                let popped=if cv==0{257}else{width+cv-1};let qbit=before[w1[popped].id()as usize]>>lane&1!=0;
                put(&mut after,w1[popped].id()as usize,lane,false);
                let cargo=rnd(&mut seed)&1!=0;put(&mut before,head,lane,cargo);put(&mut after,head,lane,cargo);
                let mut carry=false;
                for i in 0..if qbit{width}else{0} {
                    let av=before[w1[i].id()as usize]>>lane&1!=0;let bv=before[w2[i].id()as usize]>>lane&1!=0;
                    put(&mut after,w2[i].id()as usize,lane,av^bv^carry);carry=(av&&bv)||((av^bv)&&carry);
                }
                assert!(!carry);active+=1;
            }
            let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("C1 cargo block={block} batch={batch} pattern={pattern} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
        }}
        eprintln!("Q797_T10_CARGO_BLOCK block={block} ops={} T={} physical=565 PASS",b.ops.len(),b.ops.iter().filter(|o|o.kind==K::CCX).count());
    }
    eprintln!("Q797_T10_CARGO_PASS lanes={lanes} active={active}; one borrowed phase rail plus23 other helpers, head-or-C1-gap cargo retained; not full step or Q797 lifecycle");
}
