use quantum_ecc::circuit::{
    analyze_ops, BitId, Op, OperationType, OpsAnalyzer, QubitId, QubitOrBit, RegisterId, NO_BIT,
    NO_QUBIT, NO_REG,
};
use quantum_ecc::sim::{SimExecState, Simulator};
use sha3::{
    digest::{ExtendableOutput, Update},
    Shake256,
};

fn mk_op(kind: OperationType) -> Op {
    let mut op = Op::empty();
    op.kind = kind;
    op
}

#[test]
fn op_try_validate_accepts_valid_and_rejects_aliasing_and_bad_shape() {
    let mut ccx = mk_op(OperationType::CCX);
    ccx.q_control2 = QubitId(0);
    ccx.q_control1 = QubitId(1);
    ccx.q_target = QubitId(2);
    assert!(ccx.try_validate().is_ok());

    let mut hmr = mk_op(OperationType::Hmr);
    hmr.q_target = QubitId(3);
    hmr.c_target = BitId(1);
    assert!(hmr.try_validate().is_ok());

    let mut r = mk_op(OperationType::R);
    r.q_target = QubitId(4);
    assert!(r.try_validate().is_ok());

    let mut push = mk_op(OperationType::PushCondition);
    push.c_condition = BitId(2);
    assert!(push.try_validate().is_ok());

    let mut append_q = mk_op(OperationType::AppendToRegister);
    append_q.r_target = RegisterId(0);
    append_q.q_target = QubitId(5);
    assert!(append_q.try_validate().is_ok());

    // Aliasing: CCX q1 q1 q2
    let mut aliased = ccx;
    aliased.q_control2 = QubitId(1);
    aliased.q_control1 = QubitId(1);
    assert!(aliased.try_validate().is_err());

    // Missing required operand: CCX with q_control2 == NO_QUBIT
    let mut missing_c2 = ccx;
    missing_c2.q_control2 = NO_QUBIT;
    assert!(missing_c2.try_validate().is_err());

    // Bad shape: PushCondition with c_condition == NO_BIT
    let mut bad_push = mk_op(OperationType::PushCondition);
    bad_push.c_condition = NO_BIT;
    assert!(bad_push.try_validate().is_err());

    // Bad shape: AppendToRegister with both qubit and bit set
    let mut bad_append = append_q;
    bad_append.c_target = BitId(0);
    assert!(bad_append.try_validate().is_err());
}

#[test]
fn ops_analyzer_matches_analyze_ops_and_caps_registers() {
    let mut ops = Vec::new();
    for r in 0..4u64 {
        let mut reg = mk_op(OperationType::Register);
        reg.r_target = RegisterId(r);
        ops.push(reg);
    }
    let mut app0 = mk_op(OperationType::AppendToRegister);
    app0.r_target = RegisterId(0);
    app0.q_target = QubitId(7);
    ops.push(app0);

    let mut app2 = mk_op(OperationType::AppendToRegister);
    app2.r_target = RegisterId(2);
    app2.c_target = BitId(11);
    ops.push(app2);

    let mut ccx = mk_op(OperationType::CCX);
    ccx.q_control2 = QubitId(1);
    ccx.q_control1 = QubitId(2);
    ccx.q_target = QubitId(9);
    ccx.c_condition = BitId(15);
    ops.push(ccx);

    let expected = analyze_ops(ops.iter());
    let mut analyzer = OpsAnalyzer::new();
    for op in &ops {
        analyzer.observe(op).expect("valid op");
    }
    let actual = analyzer.finish();
    assert_eq!(actual, expected);
    assert_eq!(actual.0, 10);
    assert_eq!(actual.1, 16);
    assert_eq!(actual.2, 4);
    assert_eq!(actual.3[0], vec![QubitOrBit::Qubit(QubitId(7))]);
    assert_eq!(actual.3[2], vec![QubitOrBit::Bit(BitId(11))]);

    // OpsAnalyzer rejects r_target >= MAX_REGISTERS
    let mut big_reg = mk_op(OperationType::Register);
    big_reg.r_target = RegisterId(OpsAnalyzer::MAX_REGISTERS);
    let mut capped = OpsAnalyzer::new();
    assert!(capped.observe(&big_reg).is_err());

    // Legacy analyze_ops remains unchanged and accepts r_target = 2000 without panicking
    let mut legacy_reg = mk_op(OperationType::Register);
    legacy_reg.r_target = RegisterId(2000);
    let (_q, _b, num_regs, regs) = analyze_ops(std::iter::once(&legacy_reg));
    assert_eq!(num_regs, 2001);
    assert_eq!(regs.len(), 2001);
    let _ = NO_REG;
}

#[test]
fn apply_chunk_preserves_nested_condition_stack_across_arbitrary_splits() {
    let mut ops = Vec::new();

    let mut push0 = mk_op(OperationType::PushCondition);
    push0.c_condition = BitId(0);
    ops.push(push0);

    let mut x0 = mk_op(OperationType::X);
    x0.q_target = QubitId(0);
    ops.push(x0);

    let mut push1 = mk_op(OperationType::PushCondition);
    push1.c_condition = BitId(1);
    ops.push(push1);

    let mut ccx = mk_op(OperationType::CCX);
    ccx.q_control2 = QubitId(0);
    ccx.q_control1 = QubitId(1);
    ccx.q_target = QubitId(2);
    ccx.c_condition = BitId(2);
    ops.push(ccx);

    let mut push2 = mk_op(OperationType::PushCondition);
    push2.c_condition = BitId(2);
    ops.push(push2);

    let mut hmr = mk_op(OperationType::Hmr);
    hmr.q_target = QubitId(2);
    hmr.c_target = BitId(3);
    ops.push(hmr);

    let mut cz = mk_op(OperationType::CZ);
    cz.q_control1 = QubitId(0);
    cz.q_target = QubitId(1);
    cz.c_condition = BitId(3);
    ops.push(cz);

    let mut swp = mk_op(OperationType::Swap);
    swp.q_control1 = QubitId(1);
    swp.q_target = QubitId(3);
    ops.push(swp);

    let mut r_op = mk_op(OperationType::R);
    r_op.q_target = QubitId(3);
    ops.push(r_op);

    let mut b_inv = mk_op(OperationType::BitInvert);
    b_inv.c_target = BitId(4);
    ops.push(b_inv);

    let mut b_s1 = mk_op(OperationType::BitStore1);
    b_s1.c_target = BitId(5);
    ops.push(b_s1);

    let mut b_s0 = mk_op(OperationType::BitStore0);
    b_s0.c_target = BitId(4);
    ops.push(b_s0);

    let mut neg = mk_op(OperationType::Neg);
    neg.c_condition = BitId(3);
    ops.push(neg);

    ops.push(mk_op(OperationType::PopCondition));

    let mut cx = mk_op(OperationType::CX);
    cx.q_control1 = QubitId(0);
    cx.q_target = QubitId(1);
    ops.push(cx);

    ops.push(mk_op(OperationType::PopCondition));

    let mut z = mk_op(OperationType::Z);
    z.q_target = QubitId(1);
    ops.push(z);

    ops.push(mk_op(OperationType::PopCondition));

    let mut hasher = Shake256::default();
    hasher.update(b"apply-chunk-test-seed");
    let base_xof = hasher.finalize_xof();

    let init_qubits = vec![
        0xF0F0_0F0F_AAAA_5555u64,
        0x3333_CCCC_1234_5678u64,
        0xDEAD_BEEF_CAFE_BABEu64,
        0x0123_4567_89AB_CDEFu64,
    ];
    let init_bits = vec![
        0xFFFF_0000_FFFF_0000u64,
        0x0F0F_F0F0_0F0F_F0F0u64,
        0x5555_5555_AAAA_AAAAu64,
        0,
        0x1111_2222_3333_4444u64,
        0,
    ];

    let mut xof_ref = base_xof.clone();
    let mut sim_ref = Simulator::new(4, 6, &mut xof_ref);
    sim_ref.qubits = init_qubits.clone();
    sim_ref.bits = init_bits.clone();
    sim_ref.apply_iter(ops.iter());

    for chunk_size in [1usize, 2, 3, 7, ops.len()] {
        let mut xof_c = base_xof.clone();
        let mut sim_c = Simulator::new(4, 6, &mut xof_c);
        sim_c.qubits = init_qubits.clone();
        sim_c.bits = init_bits.clone();
        let mut state = SimExecState::new();
        for chunk in ops.chunks(chunk_size) {
            sim_c.apply_chunk(&mut state, chunk.iter());
        }
        assert_eq!(sim_c.qubits, sim_ref.qubits, "chunk_size={chunk_size}");
        assert_eq!(sim_c.bits, sim_ref.bits, "chunk_size={chunk_size}");
        assert_eq!(sim_c.phase, sim_ref.phase, "chunk_size={chunk_size}");
        assert_eq!(sim_c.stats, sim_ref.stats, "chunk_size={chunk_size}");
    }
}
