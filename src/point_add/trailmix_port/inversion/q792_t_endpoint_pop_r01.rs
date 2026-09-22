//! T-only M255/M256 omitted quotient acquisition, before numeric low unpack.
//! Supports original unfolded rank5 and A<=252, including narrow A0/A1.
//! P1 and carry are zero under g; source head remains literal1. Work1[A+1]
//! holds global cargo, Work2[A+2] holds the carry passenger, and the retained
//! ordinary phase passengers are Work1[A+2]/Work2[A+3]. No mask is borrowed.
//! Even t exchanges its packed q0 into P1, leaving the slot0. Odd t computes
//! q0 from the exact modulo8 invariant without changing coefficient data.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{length_recompute::mixed_mcx,metadata_muxlease as mux};
fn gate(c:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,d:&[QReg]){mixed_mcx(c,cs,out,d);}
fn flag255(c:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],g:&QReg,out:&QReg,d:&[QReg]){
    super::metadata_arithmetic5_encoded::add(c,a,cl,None,false);
    let ts=super::q792_fold20_rank_r01::triples();let truth=ts.iter().map(|t|t[0]+t[1]==3).collect();
    let(pol,terms)=mux::swap_terms(truth,5);
    for term in terms{let mut cs=vec![(g,true)];cs.extend(cl.iter().map(|q|(q,true)));
        cs.extend((0..5).filter(|&i|term>>i&1!=0).map(|i|(&rank[i],pol>>i&1==0)));gate(c,&cs,out,d);
    }
    super::metadata_arithmetic5_encoded::add(c,a,cl,None,true);
}
fn class(c:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,e:&QReg,out:&QReg,d:&[QReg],which:usize){
    // On M255 the possible rank codes are11,20,26,29. Thus rank4=0
    // singles out Ah0, and rank4=rank0=1 singles out Ah3.
    let mut cs=vec![(g,true),(e,true),(&rank[4],which==2)];
    if which==2{cs.push((&rank[0],true));}
    cs.extend(a.iter().enumerate().filter(|&(i,_)|which!=1||i!=0).map(|(i,q)|(q,which==2&&(60>>i&1!=0))));
    gate(c,&cs,out,d);
}
fn center(c:&mut Circuit,rank:&[QReg],a:&[QReg],sm:&[QReg],g:&QReg,e:&QReg,p:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg],j:usize,m256:bool){
    let shift=if m256{0}else{j&1};let slot=&w2[if m256{1}else{2-shift}];
    // Exact swap extension: initially P1=0 on g, so the q slot is cleared.
    c.cx(slot,p);gate(c,&[(g,true),(e,true),(&w1[0],false),(p,true)],slot,d);c.cx(slot,p);
    let odd=[(g,true),(e,true),(&w1[0],true)];
    if m256||shift==1{
        let mut cs=odd.to_vec();cs.push((&w2[0],false));gate(c,&cs,p,d);return;
    }
    let v0=&w2[258];let v1=&w2[257];let b0=&w2[0];let b1=&w2[1];let b2=&w2[2];let t1=&w1[1];let t2=&w1[2];let q1=&w1[255];let q2=&w1[254];
    // Three conditionally-zero metadata rails hold only narrow endpoint
    // cofactors. Their arbitrary off-endpoint values are never consumed.
    class(c,rank,a,g,e,&sm[0],d,0);class(c,rank,a,g,e,&sm[1],d,1);class(c,rank,a,g,e,&sm[2],d,2);
    // v1: !u0. v2: !u0 XOR t1. The first pair cancels on v3.
    for v in [v0,v1]{let mut cs=odd.to_vec();cs.extend([(v,true),(b0,false)]);gate(c,&cs,p,d);}
    let mut v2=odd.to_vec();v2.extend([(v0,false),(v1,true),(t1,true)]);gate(c,&v2,p,d);
    v2.push((&sm[0],true));gate(c,&v2,p,d); // logical t1=0 on A0.
    let mut v3=odd.to_vec();v3.extend([(v0,true),(v1,true)]);
    // For v3, d=((7-3u)t+2q1+4q2)%8 lies in0..5. q0=d2 XOR d0*d1.
    // Its seven exact product terms below avoid a full mod4/mod8 conversion.
    for term in [vec![(b0,true)],vec![(b2,true)],vec![(q2,true)],vec![(b1,true),(q1,true)],
                 vec![(t1,true),(b0,false),(q1,false)],vec![(t1,true),(b0,true),(b1,true)],vec![(t2,true),(b0,false)]]{
        let mut cs=v3.clone();cs.extend(term);gate(c,&cs,p,d);
    }
    // A0: t1=0 and u2=0. Physical t1/global and u2/carry passengers are
    // independent. A0/A1: logical t2=0 even when its physical rail is cargo.
    for term in [vec![(t1,true),(b0,false),(q1,false)],vec![(t1,true),(b0,true),(b1,true)],vec![(b2,true)]]{
        let mut cs=v3.clone();cs.push((&sm[0],true));cs.extend(term);gate(c,&cs,p,d);
    }
    let mut cs=v3.clone();cs.extend([(&sm[1],true),(t2,true),(b0,false)]);gate(c,&cs,p,d);
    // C3/A252: q2 is the known quotient head1, replaced by a phase passenger.
    let mut cs=v3;cs.extend([(&sm[2],true),(q2,false)]);gate(c,&cs,p,d);
    class(c,rank,a,g,e,&sm[2],d,2);class(c,rank,a,g,e,&sm[1],d,1);class(c,rank,a,g,e,&sm[0],d,0);
}
pub(super) fn pop(c:&mut Circuit,rank:&[QReg],a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,p1:&QReg,carry:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg],j:usize){
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(cl.len(),6);assert_eq!(sm.len(),4);assert!(w1.len()>=256&&w2.len()>=259&&d.len()>=19);assert!(j<4);
    flag255(c,rank,a,cl,g,carry,d);center(c,rank,a,sm,g,carry,p1,w1,w2,d,j,false);flag255(c,rank,a,cl,g,carry,d);
    if j&1==0{
        super::q794_t10_quotient::endpoint(c,rank,a,cl,&[(g,true)],carry,d);
        center(c,rank,a,sm,g,carry,p1,w1,w2,d,j,true);
        super::q794_t10_quotient::endpoint(c,rank,a,cl,&[(g,true)],carry,d);
    }
}

pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    let root=std::path::PathBuf::from(std::env::var("T_ENDPOINT_POP_CASE_DIR").expect("T_ENDPOINT_POP_CASE_DIR"));let mut total=0;
    for j in 0..4{
        let data=std::fs::read(root.join(format!("clock{j}.bin"))).unwrap();assert_eq!(data.len()%(144*64),0);
        let mut c=Circuit::new();let qs=c.alloc_qreg_bits("T omitted-q0 physical",559);
        pop(&mut c,&qs[..5],&qs[5..11],&qs[11..17],&qs[17..21],&qs[537],&qs[536],&qs[538],&qs[21..277],&qs[277..536],&qs[539..],j);
        assert_eq!(c.b.next_qubit,559);let builder=c.into_builder();for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        let nt=builder.ops.iter().filter(|op|op.kind==K::CCX).count();eprintln!("T_ENDPOINT_POP_BUILT j={j} T={nt} ops={}",builder.ops.len());
        for (batch,chunk) in data.chunks_exact(144*64).enumerate(){
            let mut before=vec![0u64;559];let mut expected=before.clone();
            for (lane,row) in chunk.chunks_exact(144).enumerate(){for bit in 0..559{
                before[bit]|=(((row[bit/8]>>(bit%8))&1)as u64)<<lane;
                expected[bit]|=(((row[72+bit/8]>>(bit%8))&1)as u64)<<lane;
            }}
            let mut f=Fixed;let mut sim=Simulator::new(559,0,&mut f);sim.qubits.copy_from_slice(&before);sim.phase=0x937c1546a123b9ff;sim.apply_iter(builder.ops.iter());
            if sim.qubits!=expected{let diffs:Vec<_>=sim.qubits.iter().zip(&expected).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,format!("{:016x}",a^b))).collect();panic!("T_ENDPOINT_POP forward j={j} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0x937c1546a123b9ff);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before,"T_ENDPOINT_POP inverse j={j} batch={batch}");assert_eq!(sim.phase,0x937c1546a123b9ff);
        }
        if let Some(dir)=std::env::var_os("T_ENDPOINT_POP_EXPORT_DIR"){
            use std::io::Write;let mut out=std::fs::File::create_new(std::path::PathBuf::from(dir).join(format!("clock{j}-ops.bin"))).unwrap();
            for op in &builder.ops{let k=match op.kind{K::X=>0u32,K::CX=>1,K::CCX=>2,_=>unreachable!()};for v in [k,op.q_target.0 as u32,op.q_control1.0 as u32,op.q_control2.0 as u32]{out.write_all(&v.to_le_bytes()).unwrap();}}
        }
        let count=data.len()/144;total+=count;println!("{{\"kind\":\"physical T omitted endpoint q0 pop\",\"clock\":{j},\"T\":{nt},\"ops\":{},\"cases\":{count},\"new_Q\":0,\"mask_loan\":false,\"whole_step_proven\":false}}",builder.ops.len());
    }
    eprintln!("T_ENDPOINT_POP_NATIVE_PASS cases={total} actual_global_phase_carry_passengers=true even_slot_cleared=true odd_post_update_qzero=true inverse_phase=true");
}
