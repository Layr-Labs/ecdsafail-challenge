use super::*;

#[test]
fn final_recipe_pins_keep_l2_overrides() {
    install_defaults();
    assert_eq!(crate::point_add::configuration::var("LFX_XTICKS").unwrap(), "12");
    assert_eq!(crate::point_add::configuration::var("LF_MERGED_WIN").unwrap(), "60");
    assert_eq!(env_raw("PP_WALK_MAX_QUBITS").unwrap(), "1290");
    assert_eq!(env_raw("PP_REPLAY_FOLD_WINDOW").unwrap(), "64");
    assert!(env_raw("TAIL_NONCE").is_none());
    assert!(config_os("BACK_SEAM_FUSE").is_none());
}

#[test]
fn explicit_settings_survive_recipe_defaults() {
    // Complete the shared recipe before this test flushes its own pins.
    install_defaults();
    crate::point_add::configuration::insert("LF_ADAPTER_TEST", "user");
    pin("LF_ADAPTER_TEST", "first");
    pin("LF_ADAPTER_TEST", "last");
    flush_pins();
    assert_eq!(crate::point_add::configuration::var("LF_ADAPTER_TEST").unwrap(), "user");
}

#[test]
fn ordered_payload_program_preserves_field_arithmetic_phase_and_scratch() {
    install_defaults();
    use alloy_primitives::U256;
    use crate::point_add::arithmetic_blocks::{Direction,Program};
    use sha3::digest::{ExtendableOutput,Update};
    for text in [
        "add:direct,half:direct",
        "fused",
        "add:power2,half:power2",
        "half_u:direct,double_u:power2,add:direct,half:direct",
        "double:direct,half:direct,add:power2,half:direct",
        "swap:direct,swap:direct,add:direct,half:direct",
        "double:direct,add:power2,add:power2,half:direct,half:power2",
    ] {
    for sign_value in [false,true] {
        for direction in [Direction::Forward,Direction::Inverse] {
            let mut c=Builder::new();
            let source=c.alloc_qubits(N);
            let target=c.alloc_qubits(N);
            let sign=c.alloc_qubit();
            if text=="fused" {
                pingpong::heo_hooks::emit_fused_test(&mut c,sign,&source,&target,direction);
            } else {
                let program=Program::parse(text).unwrap();
                pingpong::heo_hooks::emit_program(&mut c,sign,&source,&target,&program,direction);
            }
            let ops=c.take_ops();
            let (nq,nb,_,_)=crate::circuit::analyze_ops(ops.iter());
            for seed in [0u8,91] {
                let mut h=sha3::Shake256::default();h.update(&[seed]);let mut xof=h.finalize_xof();
                let mut sim=crate::sim::Simulator::new(nq as usize,nb as usize,&mut xof);
                let mut wants=Vec::new();
                for lane in 0..64 {
                    let a=U256::from((lane*53+7)as u64);
                    let b=U256::from((lane*97+19)as u64);
                    for (reg,val) in [(&source,a),(&target,b)] {
                        for (bit,q) in reg.iter().enumerate(){if val.bit(bit){sim.qubits[q.0 as usize]|=1u64<<lane;}}
                    }
                    if sign_value {sim.qubits[sign.0 as usize]|=1u64<<lane;}
                    let signed_a=if sign_value {SECP256K1_P-a}else{a};
                    let want=match direction {
                        Direction::Forward=>(b+signed_a).reduce_mod(SECP256K1_P).mul_mod((SECP256K1_P+U256::from(1))/U256::from(2),SECP256K1_P),
                        Direction::Inverse=>{let dbl=b.mul_mod(U256::from(2),SECP256K1_P);if dbl>=signed_a{dbl-signed_a}else{SECP256K1_P-(signed_a-dbl)}}
                    };
                    wants.push((a,want));
                }
                use crate::circuit::{OperationType,BitId,NO_BIT};
                // Guard each operation so reset checks retain conditional state.
                let mut conditions=Vec::new();let mut condition=u64::MAX;
                sim.bits.push(0);let guard=BitId(nb);
                for op in &ops {
                    if op.kind==OperationType::PushCondition {
                        conditions.push(condition);condition &= sim.bit(op.c_condition);continue;
                    }
                    if op.kind==OperationType::PopCondition {
                        condition=conditions.pop().expect("balanced conditions");continue;
                    }
                    let enabled=condition & if op.c_condition==NO_BIT{u64::MAX}else{sim.bit(op.c_condition)};
                    if op.kind==OperationType::R {assert_eq!(sim.qubit(op.q_target)&enabled,0,"dirty reset in {text}");}
                    let mut guarded=*op;guarded.c_condition=guard;
                    *sim.bit_mut(guard)=enabled;sim.apply_iter(std::iter::once(&guarded));
                }
                assert!(conditions.is_empty());
                assert_eq!(sim.qubit(sign),if sign_value{u64::MAX}else{0},"sign control in {text}");
                assert_eq!(sim.phase,0,"phase sign={sign_value} seed={seed}");
                for (lane,(a,b)) in wants.into_iter().enumerate(){
                    for (reg,want) in [(&source,a),(&target,b)] {
                        let mut got=U256::ZERO;
                        for (bit,q) in reg.iter().enumerate(){if (sim.qubits[q.0 as usize]>>lane)&1==1{got|=U256::from(1)<<bit;}}
                        assert_eq!(got,want,"sign={sign_value} seed={seed} lane={lane}");
                    }
                }
                for (q,bits) in sim.qubits.iter().enumerate(){if q>=2*N+1{assert_eq!(*bits,0,"scratch q{q}");}}
            }
        }
    }
    }
}

#[test]
fn only_the_exact_direct_half_add_program_selects_fusion() {
    use crate::point_add::arithmetic_blocks::Program;
    assert!(pingpong::heo_hooks::can_fuse(&Program::parse("add:direct,half:direct").unwrap()));
    for text in ["half:direct,add:direct","add:power2,half:direct","add:direct,half:power2","double:direct,add:direct,half:direct"] {
        assert!(!pingpong::heo_hooks::can_fuse(&Program::parse(text).unwrap()),"{text}");
    }
}

fn run_checked<R: sha3::digest::XofReader>(sim: &mut crate::sim::Simulator<'_,R>, ops: &[Op]) {
    use crate::circuit::{BitId,OperationType,NO_BIT};
    let guard=BitId(sim.bits.len()as u64);sim.bits.push(0);
    let mut stack=Vec::new();let mut condition=u64::MAX;
    for op in ops {
        match op.kind {
            OperationType::PushCondition=>{stack.push(condition);condition &= sim.bit(op.c_condition);continue;},
            OperationType::PopCondition=>{condition=stack.pop().expect("balanced condition stack");continue;},
            _=>{},
        }
        let enabled=condition & if op.c_condition==NO_BIT{u64::MAX}else{sim.bit(op.c_condition)};
        if op.kind==OperationType::R {assert_eq!(sim.qubit(op.q_target)&enabled,0,"dirty pre-reset state");}
        let mut guarded=*op;guarded.c_condition=guard;*sim.bit_mut(guard)=enabled;
        sim.apply_iter(std::iter::once(&guarded));
    }
    assert!(stack.is_empty());
}

fn put_field(qubits: &mut[u64],reg:&[QubitId],value:U256,lane:usize) {
    for(bit,q)in reg.iter().enumerate(){if value.bit(bit){qubits[q.0 as usize]|=1u64<<lane;}}
}
fn get_field(qubits:&[u64],reg:&[QubitId],lane:usize)->U256 {
    reg.iter().enumerate().fold(U256::ZERO,|value,(bit,q)|
        value | (U256::from((qubits[q.0 as usize]>>lane)&1)<<bit))
}

/// The reference uses overflow-safe modular addition and an exact odd-modulus half.
fn reference_cell(a:U256,b:U256,negative:bool,direction:crate::point_add::arithmetic_blocks::Direction)->U256 {
    use crate::point_add::arithmetic_blocks::Direction;
    let minus=|x:U256|if x==U256::ZERO{x}else{SECP256K1_P-x};
    match direction {
        Direction::Forward=>{
            let sum=b.add_mod(if negative{minus(a)}else{a},SECP256K1_P);
            if sum.bit(0){(sum>>1)+(SECP256K1_P>>1)+U256::from(1)}else{sum>>1}
        },
        Direction::Inverse=>b.add_mod(b,SECP256K1_P)
            .add_mod(if negative{a}else{minus(a)},SECP256K1_P),
    }
}

#[test]
fn fullwidth_entropy_inputs_cover_mixed_signs_and_odd_half_corrections() {
    install_defaults();
    use crate::point_add::arithmetic_blocks::{Direction,Program};
    use sha3::digest::{ExtendableOutput,Update,XofReader};
    let mut input_hash=sha3::Shake256::default();input_hash.update(b"leapfrog-adapter-fullwidth-inputs-v1");
    let mut input_reader=input_hash.finalize_xof();let mut rows=Vec::new();
    for lane in 0..128 {
        let mut bytes=[0u8;32];input_reader.read(&mut bytes);let a=U256::from_le_bytes(bytes).reduce_mod(SECP256K1_P);
        input_reader.read(&mut bytes);let b=U256::from_le_bytes(bytes).reduce_mod(SECP256K1_P);
        rows.push((a,b,lane%2==1));
    }
    assert!(rows.iter().any(|(a,_,_)|a.bit(255)));
    assert!(rows.iter().any(|(a,_,_)|!a.bit(255)));
    let odd=rows.iter().filter(|(a,b,negative)|{
        let signed=if *negative&&*a!=U256::ZERO{SECP256K1_P-*a}else{*a};
        b.add_mod(signed,SECP256K1_P).bit(0)
    }).count();
    assert!(odd>32&&odd<96,"both half branches must have substantial coverage");
    for text in ["fused","add:direct,half:direct","add:power2,half:power2",
        "half_u:direct,double_u:power2,add:direct,half:direct",
        "double:direct,half:direct,add:power2,half:direct",
        "swap:direct,swap:direct,add:direct,half:direct",
        "double:direct,add:power2,add:power2,half:direct,half:power2"] {
        for direction in [Direction::Forward,Direction::Inverse] {
            let mut c=Builder::new();let source=c.alloc_qubits(N);let target=c.alloc_qubits(N);let sign=c.alloc_qubit();
            if text=="fused"{pingpong::heo_hooks::emit_fused_test(&mut c,sign,&source,&target,direction);}
            else{let program=Program::parse(text).unwrap();pingpong::heo_hooks::emit_program(&mut c,sign,&source,&target,&program,direction);}
            let ops=c.take_ops();let(nq,nb,_,_)=crate::circuit::analyze_ops(ops.iter());
            for seed in [0u8,91] {for(batch,inputs)in rows.chunks(64).enumerate(){
                let mut hash=sha3::Shake256::default();hash.update(b"leapfrog-adapter-fullwidth-measurements-v1");
                hash.update(&[seed,batch as u8]);let mut xof=hash.finalize_xof();
                let mut sim=crate::sim::Simulator::new(nq as usize,nb as usize,&mut xof);let mut signs=0;
                for(lane,(a,b,negative))in inputs.iter().enumerate(){
                    put_field(&mut sim.qubits,&source,*a,lane);put_field(&mut sim.qubits,&target,*b,lane);
                    if *negative{signs|=1u64<<lane;}
                }
                sim.qubits[sign.0 as usize]=signs;run_checked(&mut sim,&ops);
                assert_eq!(sim.qubit(sign),signs,"sign text={text} direction={direction:?}");
                assert_eq!(sim.phase,0,"phase text={text} direction={direction:?} seed={seed} batch={batch}");
                for(lane,(a,b,negative))in inputs.iter().enumerate(){
                    assert_eq!(get_field(&sim.qubits,&source,lane),*a,"source {text} lane={lane}");
                    assert_eq!(get_field(&sim.qubits,&target,lane),reference_cell(*a,*b,*negative,direction),
                        "target {text} direction={direction:?} seed={seed} batch={batch} lane={lane}");
                }
                for(q,bits)in sim.qubits.iter().enumerate(){if q>=2*N+1{assert_eq!(*bits,0,"scratch {text} q{q}");}}
            }}
        }
    }
}

#[test]
fn saved_fold_window_witness_exposes_the_dropped_carry_condition() {
    install_defaults();
    use sha3::digest::{ExtendableOutput,Update};
    let width=64;let cut=U256::from(1)<<width;let correction=modular::f();
    // The low window wraps. The retained high register receives no carry.
    let input=cut-U256::from(1);
    assert!(input>=cut-correction);
    for lowering in [crate::point_add::arithmetic_blocks::Lowering::Direct,crate::point_add::arithmetic_blocks::Lowering::Power2] {
        let mut c=Builder::new();let target=c.alloc_qubits(N);let ctrl=c.alloc_qubit();
        lowering.with_scope(||const_arith::cadd_const_trunc(&mut c,&target[..width],correction,ctrl,false));
        c.declare_qubit_register(&target);c.declare_qubit_register(&[ctrl]);
        let ops=c.take_ops();let(nq,nb,_,_)=crate::circuit::analyze_ops(ops.iter());
        for seed in [0u8,91] {
            let mut h=sha3::Shake256::default();h.update(&[seed]);let mut xof=h.finalize_xof();
            let mut sim=crate::sim::Simulator::new(nq as usize,nb as usize,&mut xof);
            put_field(&mut sim.qubits,&target,input,0);sim.qubits[ctrl.0 as usize]=1;
            run_checked(&mut sim,&ops);let got=get_field(&sim.qubits,&target,0);
            assert_eq!(got,correction-U256::from(1));
            assert_eq!(input+correction-got,cut,"saved truncation witness must retain its exact missing carry");
            assert_ne!(got,input+correction,"this boundary is an inherited approximation counterexample");
            assert_eq!(sim.phase,0);assert_eq!(sim.qubit(ctrl),1);
            for(q,bits)in sim.qubits.iter().enumerate(){if q>N{assert_eq!(*bits,0,"scratch q{q}");}}
        }
    }
}

#[test]
fn saved_compare_window_witness_exposes_the_phase_prediction_mismatch() {
    install_defaults();
    use sha3::digest::{ExtendableOutput,Update};
    let mut c=Builder::new();let a=c.alloc_qubits(N);let b=c.alloc_qubits(N);let truth=c.alloc_qubit();
    // Full comparison 0<1 is true. Equal top windows predict false.
    compare::erase_with_compare(&mut c,truth,&a[N-20..],&b[N-20..],None);
    c.declare_qubit_register(&a);c.declare_qubit_register(&b);
    let ops=c.take_ops();let(nq,nb,_,_)=crate::circuit::analyze_ops(ops.iter());
    assert!(U256::ZERO<U256::from(1));
    assert_eq!(U256::ZERO>>(N-20),U256::from(1)>>(N-20));
    for seed in [0u8,91] {
        let mut h=sha3::Shake256::default();h.update(&[seed]);let mut xof=h.finalize_xof();
        let mut sim=crate::sim::Simulator::new(nq as usize,nb as usize,&mut xof);
        sim.qubits[b[0].0 as usize]=u64::MAX;sim.qubits[truth.0 as usize]=u64::MAX;
        run_checked(&mut sim,&ops);
        assert_ne!(sim.phase,0,"the saved false prediction must expose a measurement-dependent phase");
        assert_eq!(sim.phase,sim.bits[0],"phase debt equals the uncorrected measurement outcome");
        assert_eq!(sim.qubit(truth),0);assert_eq!(sim.qubit(b[0]),u64::MAX);
        for(q,bits)in sim.qubits.iter().enumerate(){if q>=2*N{assert_eq!(*bits,0,"scratch q{q}");}}
    }
}

#[test]
fn saved_fused_odd_half_witness_retains_the_exact_fold_borrow_error() {
    install_defaults();
    use crate::point_add::arithmetic_blocks::Direction;
    use sha3::digest::{ExtendableOutput,Update};
    let mut c=Builder::new();let source=c.alloc_qubits(N);let target=c.alloc_qubits(N);let sign=c.alloc_qubit();
    pingpong::heo_hooks::emit_fused_test(&mut c,sign,&source,&target,Direction::Forward);
    let ops=c.take_ops();let(nq,nb,_,_)=crate::circuit::analyze_ops(ops.iter());
    let input=U256::from(1);assert!(input.bit(0));assert!(input<modular::f());
    let reference=reference_cell(U256::ZERO,input,false,Direction::Forward);
    for seed in [0u8,91] {
        let mut h=sha3::Shake256::default();h.update(&[seed]);let mut xof=h.finalize_xof();
        let mut sim=crate::sim::Simulator::new(nq as usize,nb as usize,&mut xof);
        put_field(&mut sim.qubits,&target,input,0);run_checked(&mut sim,&ops);
        let got=get_field(&sim.qubits,&target,0);
        assert_eq!(got,reference+(U256::from(1)<<63),"the64-bit fold loses a borrow before the half");
        assert_ne!(got,reference,"saved inherited approximation counterexample");
        assert_eq!(sim.phase&1,0);assert_eq!(sim.qubit(sign)&1,0);
        assert_eq!(get_field(&sim.qubits,&source,0),U256::ZERO);
        for(q,bits)in sim.qubits.iter().enumerate(){if q>=2*N+1{assert_eq!(*bits&1,0,"scratch q{q}");}}
    }
}
