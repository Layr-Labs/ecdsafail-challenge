use super::*;
use crate::point_add::arithmetic_blocks::Lowering;
use crate::point_add::path_test_support::{ccx_count, lock, run};

#[test]
fn constant_lowerings_exhaust_values_controls_phases_and_scratch() {
    let _guard = lock();
    for width in [1usize,2,5] {
        let mask = (1u64 << width) - 1;
        for mode in [Lowering::Direct, Lowering::Power2] {
            for k in 0..=mask {
                for subtract in [false,true] {
                    let mut plain = Builder::new();
                    let data = plain.alloc_qubits(width);
                    mode.with_scope(|| {
                        if subtract { sub_const(&mut plain,&data,U256::from(k)); }
                        else { add_const(&mut plain,&data,U256::from(k)); }
                    });
                    plain.declare_qubit_register(&data);
                    let plain_ops = plain.take_ops();
                    let plain_rows: Vec<_> = (0..=mask).map(|x|vec![x]).collect();
                    run(&plain_ops,&plain_rows,&[data.clone()],|r|vec![
                        if subtract {r[0].wrapping_sub(k)&mask} else {(r[0]+k)&mask}
                    ],&[data]);
                    let mut c = Builder::new();
                    let value = c.alloc_qubits(width);
                    let ctrl = c.alloc_qubit();
                    mode.with_scope(|| {
                        if subtract { csub_const_trunc(&mut c,&value,U256::from(k),ctrl); }
                        else { cadd_const_trunc(&mut c,&value,U256::from(k),ctrl,false); }
                    });
                    c.declare_qubit_register(&value);
                    c.declare_qubit_register(&[ctrl]);
                    let ops = c.take_ops();
                    let rows: Vec<_> = (0..=mask).flat_map(|x|(0..2).map(move|b|vec![x,b])).collect();
                    let outputs = vec![value.clone(),vec![ctrl]];
                    run(&ops,&rows,&[value,vec![ctrl]],|r| {
                        let delta = k * r[1];
                        vec![if subtract {r[0].wrapping_sub(delta)&mask} else {(r[0]+delta)&mask},r[1]]
                    },&outputs);
                }
            }
        }
    }
}

#[test]
fn power2_lowering_changes_actual_carry_composition() {
    let _guard = lock();
    let mut counts = Vec::new();
    for mode in [Lowering::Direct,Lowering::Power2] {
        let mut c = Builder::new();
        let value = c.alloc_qubits(8);
        let ctrl = c.alloc_qubit();
        mode.with_scope(|| cadd_const_trunc(&mut c,&value,U256::from(11),ctrl,false));
        counts.push(ccx_count(&c.take_ops()));
    }
    assert!(counts[1] > counts[0], "power2 must emit a different carry composition");
}

#[test]
fn low_zero_host_proof_survives_both_lowerings() {
    let _guard = lock();
    for mode in [Lowering::Direct,Lowering::Power2] {
      for k in (1..64u64).step_by(2) {
        let mut c = Builder::new();
        let value = c.alloc_qubits(6);
        let ctrl = c.alloc_qubit();
        mode.with_scope(|| csub_const_trunc_ctrl_low0(&mut c,&value,U256::from(k),ctrl));
        let ops = c.take_ops();
        let rows: Vec<_> = (0..64).map(|x|vec![x,x&1]).collect();
        let outputs = vec![value.clone(),vec![ctrl]];
        run(&ops,&rows,&[value,vec![ctrl]],|r|vec![r[0].wrapping_sub(k*r[1])&63,r[1]],&outputs);
      }
    }
}

#[test]
fn low_zero_host_carry_free_constants_preserve_the_top_bit_update() {
    let _guard = lock();
    for width in [3usize,6,63] {
        let mask = (1u64<<width)-1;
        let top = 1u64<<(width-1);
        for k in [1,top+1] {
            let mut c = Builder::new();
            let value = c.alloc_qubits(width);
            let ctrl = c.alloc_qubit();
            Lowering::Direct.with_scope(|| csub_const_trunc_ctrl_low0(&mut c,&value,U256::from(k),ctrl));
            c.declare_qubit_register(&value);
            c.declare_qubit_register(&[ctrl]);
            let ops = c.take_ops();
            assert_eq!(ccx_count(&ops),0,"carry-free subtraction uses only Clifford gates");
            let inputs: Vec<u64> = if width<=6 {(0..=mask).collect()}
                else {vec![0,1,2,3,top,top+1,mask-1,mask]};
            // Only these rows satisfy the low-bit premise: acc[0] == ctrl.
            let rows: Vec<_> = inputs.into_iter().map(|x|vec![x,x&1]).collect();
            let outputs = vec![value.clone(),vec![ctrl]];
            run(&ops,&rows,&[value,vec![ctrl]],|r|vec![r[0].wrapping_sub(k*r[1])&mask,r[1]],&outputs);
        }
    }
}

#[test]
fn signed_power2_bounds_dense_negations_and_keeps_sparse_compositions() {
    let _guard = lock();
    fn count(k: U256, subtract: bool, controlled: bool, mode: Lowering) -> usize {
        let mut c = Builder::new();
        let value = c.alloc_qubits(256);
        let ctrl = c.alloc_qubit();
        mode.with_scope(|| match (subtract,controlled) {
            (true,true) => csub_const_trunc(&mut c,&value,k,ctrl),
            (false,true) => cadd_const_trunc(&mut c,&value,k,ctrl,false),
            (true,false) => sub_const(&mut c,&value,k),
            (false,false) => add_const(&mut c,&value,k),
        });
        ccx_count(&c.take_ops())
    }
    for controlled in [false,true] {
        let one_sub = count(U256::from(1),true,controlled,Lowering::Power2);
        assert!(one_sub <= 256,
            "subtracting one must use at most one carry ladder");
        for k in [U256::MAX,U256::MAX-U256::from(2),(U256::from(1)<<255)-U256::from(488),
            U256::from_limbs([0xaaaa_aaaa_aaaa_aaaa;4])] {
            assert!(count(k,false,controlled,Lowering::Power2) <= 8*256,
                "the signed split must use at most eight carry ladders");
        }
        let f = U256::from((1u64<<32)+977);
        let field_split = count(f,false,controlled,Lowering::Power2);
        let field_direct = count(f,false,controlled,Lowering::Direct);
        assert!(field_split > field_direct,
            "the sparse field correction must retain a distinct composition");
        println!("signed_power2 width=256 controlled={controlled} subtract_one_ccx={one_sub} field_direct_ccx={field_direct} field_split_ccx={field_split}");
    }
}

#[test]
fn full_width_signed_constants_preserve_controls_phase_and_scratch() {
    use crate::circuit::{analyze_ops,OperationType};
    use sha3::digest::{ExtendableOutput,Update};
    let _guard = lock();
    let values = [U256::ZERO,U256::from(1),U256::MAX,U256::MAX-U256::from(1),
        U256::from_limbs([0xaaaa_aaaa_aaaa_aaaa;4]),U256::from(1)<<255];
    let constants = [U256::from(1),U256::MAX,U256::MAX-U256::from(2),
        (U256::from(1)<<255)-U256::from(488),U256::from_limbs([0xaaaa_aaaa_aaaa_aaaa;4])];
    for k in constants { for subtract in [false,true] { for mode in [Lowering::Direct,Lowering::Power2] {
        let mut c = Builder::new();
        let value = c.alloc_qubits(256);
        let ctrl = c.alloc_qubit();
        mode.with_scope(|| {
            if subtract { csub_const_trunc(&mut c,&value,k,ctrl); }
            else { cadd_const_trunc(&mut c,&value,k,ctrl,false); }
        });
        c.declare_qubit_register(&value);
        c.declare_qubit_register(&[ctrl]);
        let ops = c.take_ops();
        let (nq,nb,_,_) = analyze_ops(ops.iter());
        for seed in [0u8,91] {
            let mut h = sha3::Shake256::default(); h.update(&[seed]);
            let mut xof = h.finalize_xof();
            let mut sim = crate::sim::Simulator::new(nq as usize,nb as usize,&mut xof);
            for (i,x) in values.iter().enumerate() { for gate in 0..2 {
                let lane = 2*i+gate;
                for (bit,q) in value.iter().enumerate() {
                    if x.bit(bit) { sim.qubits[q.0 as usize] |= 1<<lane; }
                }
                if gate==1 { sim.qubits[ctrl.0 as usize] |= 1<<lane; }
            }}
            let mask = (1u64<<(2*values.len()))-1;
            for op in &ops {
                if op.kind==OperationType::R { assert_eq!(sim.qubit(op.q_target)&mask,0,"dirty reset"); }
                sim.apply_iter(std::iter::once(op));
            }
            assert_eq!(sim.phase&mask,0,"phase mode={mode:?} k={k} subtract={subtract}");
            for (i,x) in values.iter().enumerate() { for gate in 0..2 {
                let lane = 2*i+gate;
                let mut got = U256::ZERO;
                for (bit,q) in value.iter().enumerate() {
                    if (sim.qubit(*q)>>lane)&1==1 { got |= U256::from(1)<<bit; }
                }
                let want = if gate==0 {*x} else if subtract {x.wrapping_sub(k)} else {x.wrapping_add(k)};
                assert_eq!(got,want,"mode={mode:?} k={k} subtract={subtract} gate={gate}");
                assert_eq!((sim.qubit(ctrl)>>lane)&1,gate as u64);
            }}
            for bits in &sim.qubits[257..] { assert_eq!(bits&mask,0,"dirty scratch"); }
        }
    }}}
}
