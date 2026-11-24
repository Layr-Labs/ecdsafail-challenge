use quantum_ecc::circuit::{
    analyze_ops, BitId, Op, OperationType, OpsAnalyzer, QubitId, QubitOrBit, RegisterId, NO_BIT,
    NO_QUBIT, NO_REG,
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
