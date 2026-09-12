use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Outcomes(u64);
impl XofReader for Outcomes{fn read(&mut self,b:&mut[u8]){
    if self.0<=255{b.fill(self.0 as u8);}else{for byte in b{
        self.0^=self.0<<13;self.0^=self.0>>7;self.0^=self.0<<17;*byte=self.0 as u8;
    }}
}}
fn decode(data:&[u8],lower:bool)->(usize,Vec<Op>){
    let mut r=Reader{data,at:0};let nq=r.uvar();assert_eq!(r.uvar(),0);let count=r.uvar();
    let shift_width=if nq==283{9}else{3};let input_width=nq-shift_width-4;
    let inputs:Vec<_>=(1..=input_width).collect();
    let mut s=State::new(nq+1,0,&inputs,&[],true,0);
    let mut plain=Vec::new();
    for _ in 0..count{
        let tag=r.byte();assert_eq!(r.uvar(),0);assert_eq!(r.uvar(),1);
        let qlen=r.uvar();assert!(qlen<=3);let mut qs=[NO_QUBIT;3];
        for q in qs.iter_mut().take(qlen){*q=QubitId((r.uvar()+1) as u64);}
        assert_eq!(r.uvar(),0);
        if lower{s.emit_leaf(tag,&qs,qlen,NO_BIT,0);}else{
            let mut o=Op::empty();
            match tag{
                1=>{o.kind=OperationType::X;o.q_target=qs[0];},
                3=>{o.kind=OperationType::CX;o.q_control1=qs[0];o.q_target=qs[1];},
                5=>{o.kind=OperationType::CCX;o.q_control2=qs[0];o.q_control1=qs[1];o.q_target=qs[2];},
                7=>{o.kind=OperationType::Swap;o.q_control1=qs[0];o.q_target=qs[1];},
                _=>panic!("unexpected noncoherent shift tag"),
            }
            o.validate();plain.push(o);
        }
    }
    assert_eq!(r.at,data.len());
    if lower{s.flush_raw();assert!(s.proof.balanced());(nq,s.out)}else{(nq,plain)}
}
fn check(old:&[u8],new:&[u8],wide:bool,lower:bool){
    let(nq,a)=decode(old,lower);let(nqb,b)=decode(new,lower);assert_eq!(nq,nqb);
    let(_,oracle)=decode(old,false);
    if lower{
        let mut ao=a.clone();let mut bo=b.clone();
        peephole::cancel_identical_pairs(&mut ao);peephole::cancel_identical_pairs(&mut bo);
        let cost=|v:&[Op]|v.iter().filter(|o|matches!(o.kind,OperationType::CCX|OperationType::CCZ)).count();
        eprintln!("SHIFT_LOCAL_COST nq={nq} old_lowered={} new_lowered={} old_after_peephole={} new_after_peephole={}",cost(&a),cost(&b),cost(&ao),cost(&bo));
    }
    let inputs=if wide{270}else{10};let batches=if wide{128}else{16};
    let mut random=0x592d_1836_ffe3_182au64;
    for batch in 0..batches{
        let mut initial=vec![0u64;nq+1];initial[0]=0x96e3_217a_550c_382f;
        for q in 0..inputs{
            if wide{
                random^=random<<13;random^=random>>7;random^=random<<17;initial[q+1]=random;
                if q>=261&&batch<2{initial[q+1]=if batch==0{0}else{u64::MAX};}
            }else{
                initial[q+1]=(0..64).fold(0,|v,lane|v|((((batch*64+lane)>>q)&1)as u64)<<lane);
            }
        }
        if wide{initial[1]=0xaaaa_aaaa_aaaa_aaaa;initial[2]=0xcccc_cccc_cccc_cccc;}
        for outcome in [0,255,0x55,0x9a62_8331_760e_abcdu64]{
            let mut ra=Outcomes(outcome);let mut rb=Outcomes(outcome);
            let mut sa=Simulator::new(nq+1,2,&mut ra);let mut sb=Simulator::new(nq+1,2,&mut rb);
            sa.qubits=initial.clone();sb.qubits=initial.clone();sa.phase=0x5749_2629_83f4_9473;sb.phase=sa.phase;
            sa.apply_iter(a.iter());sb.apply_iter(b.iter());
            let mut reference_rng=Outcomes(0);let mut reference=Simulator::new(nq+1,2,&mut reference_rng);
            reference.qubits=initial.clone();reference.phase=0x5749_2629_83f4_9473;reference.apply_iter(oracle.iter());
            assert_eq!(sa.qubits,reference.qubits,"old implementation versus coherent oracle");
            assert_eq!(sa.phase,reference.phase,"old phase versus coherent oracle");
            assert_eq!(sb.qubits,reference.qubits,"new implementation versus coherent oracle");
            assert_eq!(sb.phase,reference.phase,"new phase versus coherent oracle");
            assert_eq!(sa.qubits,sb.qubits,"batch={batch}, outcome={outcome}, lower={lower}");
            assert_eq!(sa.phase,sb.phase,"phase batch={batch}, outcome={outcome}, lower={lower}");
            assert!(sa.qubits[inputs+1..].iter().all(|&v|v==0));
            if !lower{assert_eq!(sa.stats.toffoli_gates-sb.stats.toffoli_gates,if wide{18*64}else{6*64});}
        }
    }
}

macro_rules! pair{($dir:literal,$name:literal)=>{(include_bytes!(concat!($dir,"/old-",$name,".hir")).as_slice(),include_bytes!(concat!($dir,"/new-",$name,".hir")).as_slice())};}
#[test]
fn directional_shift_small_exhaustive(){
    for(a,b)in[pair!("shift_fixtures/small","pre"),pair!("shift_fixtures/small","post"),pair!("shift_fixtures/small","pre-inverse"),pair!("shift_fixtures/small","post-inverse")]{check(a,b,false,false);check(a,b,false,true);}
}
#[test]
fn directional_shift_full_width_phase_and_cleanup(){
    for(a,b)in[pair!("shift_fixtures","pre"),pair!("shift_fixtures","post"),pair!("shift_fixtures","pre-inverse"),pair!("shift_fixtures","post-inverse")]{check(a,b,true,false);check(a,b,true,true);}
}
