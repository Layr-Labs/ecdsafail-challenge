//! Development-only complete native inversion lifecycle, using real production
//! initialization/release/rebuild/finish and the actual forward/reverse emitter.
//! Reusable primitive templates bound RAM; this is not a point-add score.
use super::*;
use crate::circuit::{Op,QubitId,NO_BIT};
use crate::sim::Simulator;
use ruint::aliases::U256;
use sha3::digest::XofReader;
struct Fixed(u64);
impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){for x in b {*x=rnd(&mut self.0) as u8;}}}
fn rnd(s:&mut u64)->u64 {*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(words:&mut[u64],q:usize,lane:usize,bit:bool) {
    words[q]=(words[q]&!(1u64<<lane))|(u64::from(bit)<<lane);
}
fn ids(core:&Core)->Vec<usize> {
    let mut result:Vec<_>=core.work1.iter().chain(&core.work2).chain(&core.l_t).chain(&core.l_s).chain(&core.l_q).map(|q|q.id() as usize).collect();
    result.extend([core.phase1.id() as usize,core.phase2.id() as usize,core.sign.id() as usize,core.iteration.id() as usize]);
    assert_eq!(result.len(),546);result
}
fn fill_core(words:&mut[u64],mapping:&[usize],lane:usize,record:&[u8]) {
    assert_eq!(record.len(),525);
    for i in 0..518 {assert!(record[i]<=1);put(words,mapping[i],lane,record[i]!=0);}
    for j in 0..3 {for bit in 0..8 {put(words,mapping[518+j*8+bit],lane,(record[518+j]>>bit)&1!=0);}}
    for j in 0..4 {assert!(record[521+j]<=1);put(words,mapping[542+j],lane,record[521+j]!=0);}
}
fn assert_words<R:XofReader>(sim:&Simulator<R>,expected:&[u64],stage:&str,batch:usize) {
    assert_eq!(sim.phase,0,"lifecycle phase at {stage},batch={batch}");
    for (q,&word) in expected.iter().enumerate(){assert_eq!(sim.qubit(QubitId(q as u64)),word,"lifecycle {stage},batch={batch},wire={q}");}
}
fn checked_apply<R:XofReader>(sim:&mut Simulator<R>,ops:&[Op],stage:&str) {
    // These lifecycle kernels use per-op classical conditions, never a stack.
    // Check every reset's clean precondition; R must not hide garbage.
    for op in ops {
        assert!(!matches!(op.kind,OperationType::PushCondition|OperationType::PopCondition));
        if op.kind==OperationType::R {
            let mask=if op.c_condition==NO_BIT {u64::MAX}else{sim.bit(op.c_condition)};
            assert_eq!(sim.qubit(op.q_target)&mask,0,"dirty reset at {stage}: {:?}",op.q_target);
        }
        sim.apply_iter(std::iter::once(op));
    }
    assert_eq!(sim.phase,0,"lifecycle phase after {stage}");
}
fn templates(circ:&mut Circuit,core:&Core,passenger:&[QReg],reverse:bool)->Vec<Vec<Op>> {
    let mut result=Vec::new();let live=circ.b.active_qubits;
    let cancel=std::env::var("LOWQ_TEMPLATE_CANCEL").ok().as_deref()==Some("1");
    let mut total_before=0usize;let mut total_after=0usize;let mut total_t=0usize;
    let parity=shift_parity_loan_enabled();
    let representatives=if parity {vec![1usize,2,4]}else{vec![1usize,4]};
    for group in 0..26 {for &offset in &representatives {
        let step=group*64+offset;
        let count_before=circ.b.current_ops_len();
        emit_shared_step(circ,core,passenger,step,reverse);
        let emitted_len=circ.b.current_ops_len()-count_before;
        let mut ops=std::mem::take(&mut circ.b.ops);
        assert!(!ops.is_empty() && ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
        assert_eq!(emitted_len,ops.len(),"reverse emission accounting");
        assert_eq!(circ.b.active_qubits,live);
        let repeats=(if group==25 {4}else{16})*(if offset==4 {1}else if !parity {3}else if offset==1 {2}else{1});
        total_before+=repeats*ops.len();
        if cancel {let window=std::env::var("LOWQ_CANCEL_WINDOW").ok().and_then(|v|v.parse::<usize>().ok()).unwrap_or(512);let passes=std::env::var("LOWQ_CANCEL_PASSES").ok().and_then(|v|v.parse::<usize>().ok()).unwrap_or(4);super::super::shared_optimize::cancel_nct(&mut ops,window,passes);}
        total_after+=repeats*ops.len();total_t+=repeats*ops.iter().filter(|op|op.kind==OperationType::CCX).count();
        result.push(ops);
    }}
    eprintln!("shared lifecycle template census reverse={reverse} cancel={cancel} traversal_ops_before={total_before} traversal_ops_after={total_after} traversal_T={total_t}");
    result
}
pub fn run() {
    assert!(shared_length_enabled(),"explicit LOWQ_SHARED_LENGTH=1 required");
    assert!(std::env::var_os("POINT_ADD_COUNT_ONLY").is_none());
    assert!(std::env::var_os("POINT_ADD_STREAM_OPS_PATH").is_none());
    let began=std::time::Instant::now();
    let path=std::env::var("LOWQ_FULL_INVERSION_CAPSULE").expect("explicit independent capsule");
    let data=std::fs::read(path).expect("read capsule");assert_eq!(&data[..8],b"LQINV1\0\0");
    let count=u32::from_le_bytes(data[8..12].try_into().unwrap()) as usize;
    assert!(count>0 && count<=65536);assert_eq!(data.len(),12+count*1050);
    let mut circ=Circuit::new();
    let dx=circ.alloc_qreg_bits("lifecycle.input",257);let input_ids:Vec<_>=dx.iter().map(|q|q.id() as usize).collect();
    let passenger=circ.alloc_qreg_bits("lifecycle.passenger",256);
    let core=initialize(&mut circ,dx);assert!(core.l_rp.is_empty());
    let initial_map=ids(&core);let initialization=std::mem::take(&mut circ.b.ops);
    let forward=templates(&mut circ,&core,&passenger,false);
    let terminal=release_terminal(&mut circ,core);canonicalize_terminal_work2(&mut circ,&terminal);
    let terminal_ids:Vec<_>=terminal.work2.iter().chain(&terminal.l_s).chain(std::iter::once(&terminal.iteration)).map(|q|q.id() as usize).collect();
    let release=std::mem::take(&mut circ.b.ops);
    toggle_inverse_sign(&mut circ,&terminal);let to_inverse=std::mem::take(&mut circ.b.ops);
    toggle_inverse_sign(&mut circ,&terminal);restore_terminal_work2_rotation(&mut circ,&terminal);
    let from_inverse=std::mem::take(&mut circ.b.ops);
    let core=rebuild_terminal(&mut circ,terminal);let rebuilt_map=ids(&core);
    let rebuild=std::mem::take(&mut circ.b.ops);
    let reverse=templates(&mut circ,&core,&passenger,true);
    let dx=finish(&mut circ,core);let output_ids:Vec<_>=dx.iter().map(|q|q.id() as usize).collect();
    let finishing=std::mem::take(&mut circ.b.ops);
    assert_eq!(circ.b.active_qubits,513);assert_eq!(circ.b.peak_qubits,802);assert_eq!(circ.b.next_qubit,802);
    let owned=circ.b.next_qubit as usize;let bits=circ.b.next_bit as usize;
    let p=U256::from_limbs([0xfffffffefffffc2f,u64::MAX,u64::MAX,u64::MAX]);
    let parity=shift_parity_loan_enabled();
    let template_index=|step:usize|if parity {3*((step-1)/64)+match step%4 {0=>2,2=>1,_=>0}}else{2*((step-1)/64)+usize::from(step%4==0)};
    eprintln!("shared lifecycle templates ready inputs={count} physical=802 peak=802 classical_bits={bits} init_ops={} release_ops={} rebuild_ops={} finish_ops={} elapsed={:.3}",initialization.len(),release.len(),rebuild.len(),finishing.len(),began.elapsed().as_secs_f64());
    for batch in 0..count.div_ceil(64) {
        let mut random=0x8b24cef8316aa97du64^batch as u64;
        let mut before=vec![0u64;owned];for q in &passenger {before[q.id() as usize]=rnd(&mut random);}
        let mut original=Vec::new();
        for lane in 0..64 {
            let record=&data[12+((batch*64+lane)%count)*1050..][..525];
            let mut normalized=U256::ZERO;for bit in 0..256 {normalized.set_bit(bit,record[259+258-bit]!=0);}
            let x=if record[524]!=0 {p-normalized}else{normalized};original.push(x);
            for bit in 0..256 {put(&mut before,input_ids[bit],lane,x.bit(bit));}
        }
        let mut fixed=Fixed(0xba7e501728fe69c1^batch as u64);let mut sim=Simulator::new(owned,bits,&mut fixed);
        sim.qubits.copy_from_slice(&before);
        checked_apply(&mut sim,&initialization,"initialization");
        let expected_core=|mapping:&[usize],terminal:bool| {
            let mut expected=vec![0u64;owned];for q in &passenger {expected[q.id() as usize]=before[q.id() as usize];}
            for lane in 0..64 {
                let row=&data[12+((batch*64+lane)%count)*1050..][..1050];
                fill_core(&mut expected,mapping,lane,if terminal {&row[525..]}else{&row[..525]});
            }
            expected
        };
        assert_words(&sim,&expected_core(&initial_map,false),"initialized scalar state",batch);
        for step in 1..=1616 {sim.apply_iter(forward[template_index(step)].iter());}
        assert_words(&sim,&expected_core(&initial_map,true),"terminal before release",batch);
        checked_apply(&mut sim,&release,"terminal release");
        let mut released=expected_core(&initial_map,true);
        for q in 0..owned {if !terminal_ids.contains(&q) && !passenger.iter().any(|r|r.id() as usize==q) {released[q]=0;}}
        assert_words(&sim,&released,"released terminal",batch);
        checked_apply(&mut sim,&to_inverse,"canonical inverse sign");
        let mut canonical=released.clone();
        for lane in 0..64 {
            let row=&data[12+((batch*64+lane)%count)*1050+525..][..525];
            let mut coefficient=U256::ZERO;for bit in 0..256 {coefficient.set_bit(bit,row[259+bit]!=0);}
            let inverse=if row[524]==0 {p-coefficient}else{coefficient};
            for bit in 0..256 {put(&mut canonical,terminal_ids[bit],lane,inverse.bit(bit));}
        }
        assert_words(&sim,&canonical,"canonical inverse value",batch);
        checked_apply(&mut sim,&from_inverse,"restore inverse sign");assert_words(&sim,&released,"restored coefficient",batch);
        checked_apply(&mut sim,&rebuild,"terminal rebuild");assert_words(&sim,&expected_core(&rebuilt_map,true),"rebuilt terminal",batch);
        for step in (1..=1616).rev() {sim.apply_iter(reverse[template_index(step)].iter());}
        assert_words(&sim,&expected_core(&rebuilt_map,false),"reversed initial state",batch);
        checked_apply(&mut sim,&finishing,"finish");
        let mut expected=vec![0u64;owned];for q in &passenger {expected[q.id() as usize]=before[q.id() as usize];}
        for lane in 0..64 {for bit in 0..256 {put(&mut expected,output_ids[bit],lane,original[lane].bit(bit));}}
        assert_words(&sim,&expected,"original denominator and all clean ancillas",batch);
        eprintln!("shared lifecycle PASS batch={batch} inputs={} all data/passenger/phase/reset checks elapsed={:.3}",(64*(batch+1)).min(count),began.elapsed().as_secs_f64());
    }
    eprintln!("shared native inversion lifecycle PASS {count} independent inputs, initialization/full forward/release/sign/rebuild/actual inverse emitter/finish, Q802; NOT whole point-add or official9024 verification; elapsed={:.3}",began.elapsed().as_secs_f64());
}

/// Serialization microbenchmark only: one real64-step primitive group.
/// Has no point-add ABI and must never be scored/published as a whole circuit.
pub fn compression_probe_ops()->Vec<Op> {
    assert!(optimized_shared_configuration());
    let mut circ=Circuit::new();let dx=circ.alloc_qreg_bits("compression.dx",257);
    let passenger=circ.alloc_qreg_bits("compression.passenger",256);let core=initialize(&mut circ,dx);
    circ.b.ops.clear();let mut bodies=Vec::new();
    for step in [769usize,770,772] {
        emit_shared_step(&mut circ,&core,&passenger,step,false);
        bodies.push(std::mem::take(&mut circ.b.ops));
    }
    let size=16*(2*bodies[0].len()+bodies[1].len()+bodies[2].len());let mut ops=Vec::with_capacity(size);
    for _ in 0..16 {for i in [0usize,1,0,2] {ops.extend_from_slice(&bodies[i]);}}
    assert_eq!(ops.len(),size);for op in &ops {op.validate();}
    eprintln!("COMPRESSION_PROBE actual_group12_ops={size}; serialization-only artifact, no point-add ABI or score");ops
}
