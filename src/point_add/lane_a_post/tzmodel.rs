//! Merge lane (round 105): the tree's truth-table value model (truth_simplify.rs `Truth` and `Support::step`) with the
//! atom list stored inline (no heap allocation per value), for the hold pass's truth-model zeros only. Same tables,
//! same canonical form, same order of fresh atoms, so `is_zero` answers equal the original model's on every op; the
//! streamed driver checks that op by op (`stool tzcheck`) and the full-size streamed runs check it end to end.
//! Our code, a port of the tree's model; the rewrite proofs of the truth round are not part of it.
use crate::circuit::{analyze_ops, Op, OperationType, QubitOrBit, NO_BIT};

const CAP: usize = 6;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct T {
    n: u8,
    a: [u64; CAP], // sorted atom ids in a[..n]; a[n..] = 0
    table: u64,
}

#[inline]
fn row_mask(count: usize) -> u64 {
    if count == CAP {
        u64::MAX
    } else {
        (1u64 << (1usize << count)) - 1
    }
}

/// rows with bit `p` of the row index clear
const COF: [u64; CAP] = [
    0x5555_5555_5555_5555,
    0x3333_3333_3333_3333,
    0x0f0f_0f0f_0f0f_0f0f,
    0x00ff_00ff_00ff_00ff,
    0x0000_ffff_0000_ffff,
    0x0000_0000_ffff_ffff,
];

impl T {
    #[inline]
    fn constant(v: bool) -> T {
        T { n: 0, a: [0; CAP], table: v as u64 }
    }
    #[inline]
    fn is_zero(&self) -> bool {
        self.n == 0 && self.table == 0
    }
    #[inline]
    fn is_one(&self) -> bool {
        self.n == 0 && self.table == 1
    }
    #[inline]
    fn complement(&self) -> T {
        T { n: self.n, a: self.a, table: self.table ^ row_mask(self.n as usize) }
    }
    #[inline]
    fn complements(&self, o: &T) -> bool {
        self.n == o.n && self.a == o.a && self.table ^ o.table == row_mask(self.n as usize)
    }
    /// truth_simplify's `Truth::canonical`: drop inessential atoms (keep the zero cofactor). Bit-parallel form of
    /// the same row loops: the cofactor test reads rows with bit p clear, the reduction compacts them.
    fn canonical(mut n: usize, mut a: [u64; CAP], mut table: u64) -> T {
        table &= row_mask(n);
        let mut p = 0;
        while p < n {
            let bit = 1usize << p;
            let essential = (table ^ (table >> bit)) & COF[p] & row_mask(n) != 0;
            if essential {
                p += 1;
                continue;
            }
            table = compact(table, p);
            for k in p..n - 1 {
                a[k] = a[k + 1];
            }
            a[n - 1] = 0;
            n -= 1;
        }
        T { n: n as u8, a, table }
    }
}

/// Rows with bit p clear, packed: out[r] = t[r with a 0 inserted at bit p] (the zero cofactor of variable p).
#[inline]
fn compact(t: u64, p: usize) -> u64 {
    let mut x = t & COF[p];
    for q in p..CAP - 1 {
        x = (x | (x >> (1u32 << q))) & COF[q + 1];
    }
    x
}

/// A table over m <= 5 variables with a new variable inserted at position p (the table does not depend on it).
#[inline]
fn insert(t: u64, p: usize) -> u64 {
    let s = 1u32 << p;
    let mut x = t;
    let mut q = CAP - 2; // shifts 16, 8, ... down to s
    loop {
        let sh = 1u32 << q;
        if sh < s {
            break;
        }
        x = (x | (x << sh)) & COF[q];
        if q == 0 {
            break;
        }
        q -= 1;
    }
    x | (x << s)
}

/// The table of `v` over the union variables, `pos` its own atoms' union positions (increasing), k union size.
#[inline]
fn expand(v: &T, pos: &[usize; CAP], k: usize) -> u64 {
    let mut t = v.table & row_mask(v.n as usize);
    let mut j = 0;
    for p in 0..k {
        if j < v.n as usize && pos[j] == p {
            j += 1;
        } else {
            t = insert(t, p);
        }
    }
    t
}

pub struct FastModel {
    qubits: Vec<T>,
    bits: Vec<T>,
    base: T,
    stack: Vec<T>,
    next_atom: u64,
}

impl FastModel {
    pub fn new(ops: &[Op]) -> Self {
        let (nq, nb, _, registers) = analyze_ops(ops.iter());
        let mut qin = vec![false; nq as usize];
        let mut bin = vec![false; nb as usize];
        for register in registers {
            for slot in register {
                match slot {
                    QubitOrBit::Qubit(q) => qin[q.0 as usize] = true,
                    QubitOrBit::Bit(b) => bin[b.0 as usize] = true,
                }
            }
        }
        let mut s = FastModel {
            qubits: vec![T::constant(false); nq as usize],
            bits: vec![T::constant(false); nb as usize],
            base: T::constant(true),
            stack: Vec::new(),
            next_atom: 0,
        };
        for (q, input) in qin.into_iter().enumerate() {
            if input {
                s.qubits[q] = s.fresh();
            }
        }
        for (b, input) in bin.into_iter().enumerate() {
            if input {
                s.bits[b] = s.fresh();
            }
        }
        s
    }
    #[inline]
    pub fn is_zero(&self, q: usize) -> bool {
        self.qubits[q].is_zero()
    }
    #[inline]
    fn fresh(&mut self) -> T {
        let id = self.next_atom;
        self.next_atom = id.checked_add(1).expect("truth atom identifier overflow");
        let mut a = [0; CAP];
        a[0] = id;
        T { n: 1, a, table: 2 }
    }
    fn combine(&mut self, x: &T, y: &T, is_and: bool) -> T {
        // sorted union of the two atom lists
        let (xn, yn) = (x.n as usize, y.n as usize);
        let mut u = [0u64; 2 * CAP];
        let (mut i, mut j, mut k) = (0, 0, 0);
        while i < xn || j < yn {
            let v = if j >= yn || (i < xn && x.a[i] < y.a[j]) {
                i += 1;
                x.a[i - 1]
            } else if i >= xn || y.a[j] < x.a[i] {
                j += 1;
                y.a[j - 1]
            } else {
                i += 1;
                j += 1;
                x.a[i - 1]
            };
            u[k] = v;
            k += 1;
        }
        if k > CAP {
            return self.fresh();
        }
        let mut a = [0u64; CAP];
        a[..k].copy_from_slice(&u[..k]);
        let pos = |v: &T| {
            let mut p = [0usize; CAP];
            for t in 0..v.n as usize {
                p[t] = a[..k].binary_search(&v.a[t]).unwrap();
            }
            p
        };
        let (xp, yp) = (pos(x), pos(y));
        let (ex, ey) = (expand(x, &xp, k), expand(y, &yp, k));
        let table = (if is_and { ex & ey } else { ex ^ ey }) & row_mask(k);
        T::canonical(k, a, table)
    }
    #[inline]
    fn xor(&mut self, x: &T, y: &T) -> T {
        if x == y {
            return T::constant(false);
        }
        if x.is_zero() {
            return *y;
        }
        if y.is_zero() {
            return *x;
        }
        if x.is_one() {
            return y.complement();
        }
        if y.is_one() {
            return x.complement();
        }
        self.combine(x, y, false)
    }
    #[inline]
    fn and(&mut self, x: &T, y: &T) -> T {
        if x.is_zero() || y.is_zero() || x.complements(y) {
            return T::constant(false);
        }
        if x.is_one() {
            return *y;
        }
        if y.is_one() || x == y {
            return *x;
        }
        self.combine(x, y, true)
    }
    pub fn step(&mut self, op: &Op) {
        use OperationType::*;
        if op.kind == PushCondition {
            self.stack.push(self.base);
            let (b, c) = (self.base, self.bits[op.c_condition.0 as usize]);
            self.base = self.and(&b, &c);
            return;
        }
        if op.kind == PopCondition {
            if let Some(saved) = self.stack.pop() {
                self.base = saved;
            }
            return;
        }
        let mut cond = self.base;
        if op.c_condition != NO_BIT {
            let c = self.bits[op.c_condition.0 as usize];
            cond = self.and(&cond, &c);
        }
        match op.kind {
            CCX => {
                let a = self.qubits[op.q_control1.0 as usize];
                let b = self.qubits[op.q_control2.0 as usize];
                let product = self.and(&a, &b);
                let toggle = self.and(&cond, &product);
                let t = op.q_target.0 as usize;
                let old = self.qubits[t];
                self.qubits[t] = self.xor(&old, &toggle);
            }
            CX => {
                let t = op.q_target.0 as usize;
                let c = self.qubits[op.q_control1.0 as usize];
                let toggle = self.and(&cond, &c);
                let old = self.qubits[t];
                self.qubits[t] = self.xor(&old, &toggle);
            }
            X => {
                let t = op.q_target.0 as usize;
                let old = self.qubits[t];
                self.qubits[t] = self.xor(&old, &cond);
            }
            Swap => {
                let (a, b) = (op.q_control1.0 as usize, op.q_target.0 as usize);
                let (qa, qb) = (self.qubits[a], self.qubits[b]);
                let d = self.xor(&qa, &qb);
                let toggle = self.and(&cond, &d);
                let left = self.xor(&qa, &toggle);
                let right = self.xor(&qb, &toggle);
                self.qubits[a] = left;
                self.qubits[b] = right;
            }
            Hmr => {
                let t = op.q_target.0 as usize;
                let bit = op.c_target.0 as usize;
                let outcome = self.fresh();
                let ob = self.bits[bit];
                let d = self.xor(&ob, &outcome);
                let toggle = self.and(&cond, &d);
                self.bits[bit] = self.xor(&ob, &toggle);
                let qt = self.qubits[t];
                self.qubits[t] = self.and(&qt, &cond.complement());
            }
            R => {
                let t = op.q_target.0 as usize;
                let qt = self.qubits[t];
                self.qubits[t] = self.and(&qt, &cond.complement());
            }
            BitInvert => {
                let bit = op.c_target.0 as usize;
                let ob = self.bits[bit];
                self.bits[bit] = self.xor(&ob, &cond);
            }
            BitStore0 => {
                let bit = op.c_target.0 as usize;
                let ob = self.bits[bit];
                self.bits[bit] = self.and(&ob, &cond.complement());
            }
            BitStore1 => {
                let bit = op.c_target.0 as usize;
                let ob = self.bits[bit];
                self.bits[bit] = self.and(&ob.complement(), &cond.complement()).complement();
            }
            _ => {}
        }
    }
}
