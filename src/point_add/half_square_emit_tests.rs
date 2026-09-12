use crate::circuit::{Op, OperationType, QubitId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct ZeroXof;

impl XofReader for ZeroXof {
    fn read(&mut self, out: &mut [u8]) {
        out.fill(0);
    }
}

#[derive(Default)]
struct Emitter {
    ops: Vec<Op>,
}

impl Emitter {
    fn gate(&mut self, kind: OperationType, c2: QubitId, c1: QubitId, target: QubitId) {
        let mut op = Op::empty();
        op.kind = kind;
        op.q_control2 = c2;
        op.q_control1 = c1;
        op.q_target = target;
        op.validate();
        self.ops.push(op);
    }

    fn cx(&mut self, control: QubitId, target: QubitId) {
        self.gate(OperationType::CX, QubitId(u64::MAX), control, target);
    }

    fn ccx(&mut self, c1: QubitId, c2: QubitId, target: QubitId) {
        assert!(c1 != c2 && c1 != target && c2 != target);
        self.gate(OperationType::CCX, c1, c2, target);
    }

    /// Literal native translation of the incumbent exact backend's
    /// `append_controlled_add_mod2_with_carry_flag`.
    fn cadd_with_flag(
        &mut self,
        control: QubitId,
        addend: &[QubitId],
        acc: &[QubitId],
        carry: QubitId,
        flag: QubitId,
    ) {
        assert_eq!(addend.len(), acc.len());
        let n = acc.len();
        assert!(n >= 1);
        for i in 0..n {
            self.cx(carry, addend[i]);
            self.cx(carry, acc[i]);
            self.ccx(acc[i], addend[i], carry);
        }
        self.ccx(control, carry, flag);
        for i in (0..n).rev() {
            self.ccx(acc[i], addend[i], carry);
            self.cx(carry, acc[i]);
            self.ccx(control, addend[i], acc[i]);
            self.cx(carry, addend[i]);
        }
    }

    /// Literal reverse of [`Self::cadd_with_flag`].
    fn csub_with_flag(
        &mut self,
        control: QubitId,
        addend: &[QubitId],
        acc: &[QubitId],
        carry: QubitId,
        flag: QubitId,
    ) {
        assert_eq!(addend.len(), acc.len());
        let n = acc.len();
        assert!(n >= 1);
        for i in 0..n {
            self.cx(carry, addend[i]);
            self.ccx(control, addend[i], acc[i]);
            self.cx(carry, acc[i]);
            self.ccx(acc[i], addend[i], carry);
        }
        self.ccx(control, carry, flag);
        for i in (0..n).rev() {
            self.ccx(acc[i], addend[i], carry);
            self.cx(carry, acc[i]);
            self.cx(carry, addend[i]);
        }
    }

    /// Emit `product ^= left*right`. `product` must start at zero for the
    /// arithmetic interpretation. Every row's carry-out lands in the next
    /// untouched product bit, so no zero-padding register or overflow ancilla
    /// is needed.
    fn product(
        &mut self,
        left: &[QubitId],
        right: &[QubitId],
        product: &[QubitId],
        carry: QubitId,
        copied: Option<QubitId>,
        inverse: bool,
    ) {
        let n = left.len();
        assert_eq!(right.len(), n);
        assert_eq!(product.len(), 2 * n);
        assert!(n >= 1);
        for row in 0..n {
            let i = if inverse { n - 1 - row } else { row };
            let control = if let Some(copy) = copied {
                self.cx(left[i], copy);
                copy
            } else {
                left[i]
            };
            let acc = &product[i..i + n];
            let flag = product[i + n];
            if inverse {
                self.csub_with_flag(control, right, acc, carry, flag);
            } else {
                self.cadd_with_flag(control, right, acc, carry, flag);
            }
            if let Some(copy) = copied {
                self.cx(left[i], copy);
            }
        }
    }
}

fn set_word<R: XofReader>(sim: &mut Simulator<'_, R>, reg: &[QubitId], value: u64) {
    for (i, q) in reg.iter().enumerate() {
        sim.qubits[q.0 as usize] = (value >> i) & 1;
    }
}

fn get_word<R: XofReader>(sim: &Simulator<'_, R>, reg: &[QubitId]) -> u64 {
    reg.iter().enumerate().fold(0, |value, (i, q)| {
        value | ((sim.qubits[q.0 as usize] & 1) << i)
    })
}

fn qrange(start: usize, len: usize) -> Vec<QubitId> {
    (start..start + len).map(|q| QubitId(q as u64)).collect()
}

fn count(ops: &[Op], kind: OperationType) -> usize {
    ops.iter().filter(|op| op.kind == kind).count()
}

#[test]
fn exact_low_ancilla_products_exhaustive_half_widths_1_through_6() {
    let mut multiply_cases = 0usize;
    let mut square_cases = 0usize;
    for n in 1..=6usize {
        let left = qrange(0, n);
        let right = qrange(n, n);
        let product = qrange(2 * n, 2 * n);
        let carry = QubitId((4 * n) as u64);
        let copied = QubitId((4 * n + 1) as u64);

        let mut mul = Emitter::default();
        mul.product(&left, &right, &product, carry, None, false);
        let forward_mul_ops = mul.ops.len();
        mul.product(&left, &right, &product, carry, None, true);
        for x in 0..1u64 << n {
            for y in 0..1u64 << n {
                let mut rng = ZeroXof;
                let mut sim = Simulator::new(4 * n + 2, 1, &mut rng);
                set_word(&mut sim, &left, x);
                set_word(&mut sim, &right, y);
                sim.apply_iter(mul.ops[..forward_mul_ops].iter());
                assert_eq!(get_word(&sim, &left), x);
                assert_eq!(get_word(&sim, &right), y);
                assert_eq!(get_word(&sim, &product), x * y);
                assert_eq!(sim.qubits[carry.0 as usize], 0);
                sim.apply_iter(mul.ops[forward_mul_ops..].iter());
                assert_eq!(get_word(&sim, &left), x);
                assert_eq!(get_word(&sim, &right), y);
                assert_eq!(get_word(&sim, &product), 0);
                assert_eq!(sim.qubits[carry.0 as usize], 0);
                multiply_cases += 1;
            }
        }

        let mut square = Emitter::default();
        square.product(&left, &left, &product, carry, Some(copied), false);
        let forward_square_ops = square.ops.len();
        square.product(&left, &left, &product, carry, Some(copied), true);
        for x in 0..1u64 << n {
            let mut rng = ZeroXof;
            let mut sim = Simulator::new(4 * n + 2, 1, &mut rng);
            set_word(&mut sim, &left, x);
            sim.apply_iter(square.ops[..forward_square_ops].iter());
            assert_eq!(get_word(&sim, &left), x);
            assert_eq!(get_word(&sim, &product), x * x);
            assert_eq!(sim.qubits[carry.0 as usize], 0);
            assert_eq!(sim.qubits[copied.0 as usize], 0);
            sim.apply_iter(square.ops[forward_square_ops..].iter());
            assert_eq!(get_word(&sim, &left), x);
            assert_eq!(get_word(&sim, &product), 0);
            assert_eq!(sim.qubits[carry.0 as usize], 0);
            assert_eq!(sim.qubits[copied.0 as usize], 0);
            square_cases += 1;
        }
    }
    println!("HALF_SQUARE_EMIT_ORACLE half_widths=1..6 total_widths=2,4,6,8,10,12 multiply_cases={multiply_cases} square_cases={square_cases} value=pass round_trip=pass carry_out=0 copied_control_out=0 phase=exact_unitary");
}

#[test]
fn q833_exact_nonmod_emitter_count_and_mapping() {
    const H: usize = 128;
    let a = qrange(257, H);
    let b = qrange(257 + H, H);
    let product = qrange(513, 2 * H);
    let carry = QubitId(769); // S[0]
    let copied = QubitId(770); // S[1]

    let mut square = Emitter::default();
    square.product(&a, &a, &product, carry, Some(copied), false);
    let square_forward_ccx = count(&square.ops, OperationType::CCX);
    let square_forward_cx = count(&square.ops, OperationType::CX);
    square.product(&a, &a, &product, carry, Some(copied), true);
    let square_roundtrip_ccx = count(&square.ops, OperationType::CCX);
    let square_roundtrip_cx = count(&square.ops, OperationType::CX);

    let mut multiply = Emitter::default();
    multiply.product(&b, &a, &product, carry, None, false);
    let multiply_forward_ccx = count(&multiply.ops, OperationType::CCX);
    let multiply_forward_cx = count(&multiply.ops, OperationType::CX);
    multiply.product(&b, &a, &product, carry, None, true);
    let multiply_roundtrip_ccx = count(&multiply.ops, OperationType::CCX);
    let multiply_roundtrip_cx = count(&multiply.ops, OperationType::CX);

    // Each row uses the incumbent exact controlled-add primitive's 3H+1 CCX.
    assert_eq!(square_forward_ccx, H * (3 * H + 1));
    assert_eq!(multiply_forward_ccx, H * (3 * H + 1));
    assert_eq!(square_roundtrip_ccx, 2 * square_forward_ccx);
    assert_eq!(multiply_roundtrip_ccx, 2 * multiply_forward_ccx);
    assert_eq!(square_forward_cx, H * (4 * H + 2));
    assert_eq!(multiply_forward_cx, H * 4 * H);
    assert_eq!(square_roundtrip_cx, 2 * square_forward_cx);
    assert_eq!(multiply_roundtrip_cx, 2 * multiply_forward_cx);
    assert_eq!(count(&square.ops, OperationType::CCZ), 0);
    assert_eq!(count(&multiply.ops, OperationType::CCZ), 0);

    let nonmod = 2 * square_roundtrip_ccx + multiply_roundtrip_ccx;
    let nonmod_cx = 2 * square_roundtrip_cx + multiply_roundtrip_cx;
    let exact_modular = 770 * 1_531 + 3 * 2_813;
    let candidate = exact_modular + nonmod;
    let incumbent = 2_223_879;
    assert_eq!(square_forward_ccx, 49_280);
    assert_eq!(nonmod, 295_680);
    assert_eq!(nonmod_cx, 394_240);
    assert_eq!(candidate, 1_482_989);
    assert!(candidate < incumbent);

    let touched_max = square.ops.iter().chain(&multiply.ops)
        .flat_map(|op| [op.q_control2.0, op.q_control1.0, op.q_target.0])
        .filter(|&q| q != u64::MAX)
        .max().unwrap();
    assert_eq!(touched_max, copied.0);
    assert!(square.ops.iter().chain(&multiply.ops).all(|op| {
        [op.q_control2.0, op.q_control1.0, op.q_target.0].into_iter()
            .filter(|&q| q != u64::MAX)
            .all(|q| (257..=770).contains(&q))
    }));
    println!("HALF_SQUARE_EMIT_COUNT square_forward_ccx={square_forward_ccx} square_roundtrip_ccx={square_roundtrip_ccx} multiply_forward_ccx={multiply_forward_ccx} multiply_roundtrip_ccx={multiply_roundtrip_ccx} nonmod_ccx={nonmod} nonmod_cx={nonmod_cx} ccz=0 exact_modular_ccx=1187309 candidate_ccx={candidate} incumbent_ccx=2223879 strict_win={} pct={:.6} mapping=Y257..512,A513..768,S0=769,S1=770 lease_S18_S65_untouched=true", incumbent-candidate, 100.0*(incumbent-candidate) as f64/incumbent as f64);
}
