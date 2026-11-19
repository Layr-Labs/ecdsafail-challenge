use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_REG};
use super::peephole;

fn optional_bit(x: u32) -> BitId {
    if x == peephole::NONE { NO_BIT } else { BitId(x as u64) }
}

fn operation([kind, a, b, c]: [u32; 4]) -> Op {
    use OperationType::*;
    let qa = QubitId(a as u64);
    let qb = QubitId(b as u64);
    let mut op = Op::empty();
    op.kind = match kind {
        6 => { op.q_target = qa; op.c_condition = optional_bit(b); X }
        8 => { op.q_control1 = qa; op.q_target = qb; op.c_condition = optional_bit(c); CX }
        13 => { op.q_control2 = qa; op.q_control1 = qb; op.q_target = QubitId(c as u64); CCX }
        _ => panic!("peephole_hook: unexpected rewritten row kind {kind}"),
    };
    op
}

struct OpRows<'a>(&'a mut Vec<Op>, Vec<(usize, [[u32; 4]; 3])>);
impl peephole::Rows for OpRows<'_> {
    fn len(&self) -> usize { self.0.len() }
    fn get(&self, i: usize) -> [u32; 4] {
        use OperationType::*;
        let o = self.0[i];
        let bit = |x: BitId| if x == NO_BIT { peephole::NONE } else { assert!(x.0 < u32::MAX as u64, "peephole: bit id exceeds u32"); x.0 as u32 };
        let qb = |q: QubitId| { assert!(q.0 < 1024, "peephole: qubit id exceeds 1024"); q.0 as u32 };
        match o.kind {
            DebugPrint => if o.r_target == NO_REG { [peephole::TOMB, peephole::NONE, peephole::NONE, peephole::NONE] } else { [peephole::BLOCK, peephole::NONE, peephole::NONE, peephole::NONE] },
            Neg => [0, bit(o.c_condition), peephole::NONE, peephole::NONE],
            Register => [1, o.r_target.0 as u32, peephole::NONE, peephole::NONE],
            AppendToRegister => if o.c_target != NO_BIT { [18, o.r_target.0 as u32, bit(o.c_target), peephole::NONE] } else { [2, o.r_target.0 as u32, qb(o.q_target), peephole::NONE] },
            BitInvert => [3, bit(o.c_target), bit(o.c_condition), peephole::NONE],
            BitStore0 => [4, bit(o.c_target), bit(o.c_condition), peephole::NONE],
            BitStore1 => [5, bit(o.c_target), bit(o.c_condition), peephole::NONE],
            X => [6, qb(o.q_target), bit(o.c_condition), peephole::NONE],
            Z => [7, qb(o.q_target), bit(o.c_condition), peephole::NONE],
            CX => [8, qb(o.q_control1), qb(o.q_target), bit(o.c_condition)],
            CZ => [9, qb(o.q_control1), qb(o.q_target), bit(o.c_condition)],
            Swap => [10, qb(o.q_control1), qb(o.q_target), bit(o.c_condition)],
            R => [11, qb(o.q_target), bit(o.c_condition), peephole::NONE],
            Hmr => { assert!(o.c_condition == NO_BIT); [12, qb(o.q_target), bit(o.c_target), peephole::NONE] }
            CCX => if o.c_condition == NO_BIT {
                [13, qb(o.q_control2), qb(o.q_control1), qb(o.q_target)]
            } else {
                [19, qb(o.q_control2), qb(o.q_control1), qb(o.q_target)]
            },
            CCZ => [14, qb(o.q_control2), qb(o.q_control1), qb(o.q_target)],
            PushCondition => [15, bit(o.c_condition), peephole::NONE, peephole::NONE],
            PopCondition => [16, peephole::NONE, peephole::NONE, peephole::NONE],
        }
    }
    fn set(&mut self, i: usize, r: [u32; 4]) {
        self.0[i] = if r[0] == peephole::TOMB {
            let mut o = Op::empty();
            o.kind = OperationType::DebugPrint;
            o
        } else {
            operation(r)
        };
    }
    fn expand(&mut self, i: usize, block: [[u32; 4]; 3]) {
        let mut o = Op::empty();
        o.kind = OperationType::DebugPrint;
        o.r_target = RegisterId(1);
        self.0[i] = o;
        assert!(self.1.last().map_or(true, |l| l.0 < i));
        self.1.push((i, block));
    }
    fn block(&self, i: usize) -> [[u32; 4]; 3] {
        let j = self.1.binary_search_by_key(&i, |e| e.0).expect("peephole block");
        self.1[j].1
    }
}

fn materialize(ops: &mut Vec<Op>, blocks: &[(usize, [[u32; 4]; 3])]) {
    let n = ops.len();
    let mut w = 0usize;
    let mut bi = 0usize;
    let mut q: std::collections::VecDeque<Op> = std::collections::VecDeque::new();
    for r in 0..n {
        let o = ops[r];
        if o.kind == OperationType::DebugPrint {
            if o.r_target != NO_REG {
                assert_eq!(blocks[bi].0, r);
                for row in blocks[bi].1 { q.push_back(operation(row)); }
                bi += 1;
            }
        } else {
            q.push_back(o);
        }
        while w <= r {
            match q.pop_front() {
                Some(x) => { ops[w] = x; w += 1; }
                None => break,
            }
        }
    }
    assert_eq!(bi, blocks.len());
    ops.truncate(w);
    if !q.is_empty() {
        ops.reserve_exact(q.len());
        ops.extend(q);
    }
}

pub fn apply(mut ops: Vec<Op>) -> Vec<Op> {
    let (blocks, st) = {
        let mut v = OpRows(&mut ops, Vec::new());
        let st = peephole::pass_cfg(&mut v, 64, 4);
        (v.1, st)
    };
    materialize(&mut ops, &blocks);
    eprintln!("PEEPHOLE std removed={} {:?}", st.removed_ccx(), st);
    ops
}

pub fn apply_deep(mut ops: Vec<Op>, max_passes: usize) -> Vec<Op> {
    for p in 0..max_passes {
        let (blocks, st) = {
            let mut v = OpRows(&mut ops, Vec::new());
            let st = peephole::pass_cfg(&mut v, 1024, 16);
            (v.1, st)
        };
        materialize(&mut ops, &blocks);
        eprintln!("PEEPHOLE deep pass={} removed={} {:?}", p + 1, st.removed_ccx(), st);
        if st.removed_ccx() == 0 {
            break;
        }
    }
    ops
}
