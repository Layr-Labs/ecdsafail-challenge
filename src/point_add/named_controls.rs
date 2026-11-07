//! Substitute a CCX or CCZ only when its Boolean control product is proved.
//! Declared inputs are arbitrary and other qubits and bits start at zero.
//! A name denotes an immutable Boolean function of those inputs and measurement
//! outcomes. The low bit denotes complement. A forgotten expression becomes
//! an opaque atom; names are never reused, and hash matches need full keys.
use crate::circuit::{analyze_ops, Op, OperationType as K, QubitId, QubitOrBit, NO_BIT, NO_QUBIT};

type Value = u64; // low bit is the complement; 0/1 are the constants

#[derive(Clone, Copy)]
struct Sum<const N: usize> {
    terms: [Value; N],
    len: usize,
}
impl<const N: usize> Sum<N> {
    fn empty() -> Self {
        Self {
            terms: [0; N],
            len: 0,
        }
    }
    fn atom(v: Value) -> Self {
        let mut s = Self::empty();
        s.terms[0] = v;
        s.len = 1;
        s
    }
}

#[inline]
fn mix(v: u64) -> u64 {
    let v = (v ^ (v >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    let v = (v ^ (v >> 27)).wrapping_mul(0x94d049bb133111eb);
    v ^ (v >> 31)
}
struct Values<const N: usize> {
    next: Value,
    mask: usize,
    products: Vec<(Value, Value, Value)>,
    large_xors: Vec<(Value, Value, Value)>,
    sums: Vec<(Value, Sum<N>)>,
}
impl<const N: usize> Values<N> {
    fn new(slots: usize) -> Self {
        assert!(N >= 2 && slots.is_power_of_two());
        Self {
            next: 2,
            mask: slots - 1,
            products: vec![(0, 0, 0); slots],
            large_xors: vec![(0, 0, 0); slots],
            sums: vec![(0, Sum::empty()); slots],
        }
    }
    fn fresh(&mut self) -> Value {
        // Opaque names have their low address bits zero. Sum names hold their
        // table slot there. The unique serial is disjoint from both and never wraps.
        let serial = self.next;
        self.next = self
            .next
            .checked_add(1)
            .expect("symbolic value serial exhausted");
        serial
            .checked_mul(2 * (self.mask as u64 + 1))
            .expect("symbolic value id overflow")
    }
    fn support(&self, v: Value) -> Sum<N> {
        let (id, s) = self.sums[(v as usize >> 1) & self.mask];
        if id == v {
            s
        } else {
            Sum::atom(v)
        }
    }
    fn pair(&mut self, a: Value, b: Value, and: bool) -> Value {
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        let slot = mix(a ^ b.rotate_left(23)) as usize & self.mask;
        let ent = if and {
            self.products[slot]
        } else {
            self.large_xors[slot]
        };
        if ent.0 == a && ent.1 == b && ent.2 != 0 {
            return ent.2;
        }
        let id = self.fresh();
        if and {
            self.products[slot] = (a, b, id);
        } else {
            self.large_xors[slot] = (a, b, id);
        }
        id
    }
    #[inline]
    fn and(&mut self, a: Value, b: Value) -> Value {
        if a == 0 || b == 0 || a == (b ^ 1) {
            0
        } else if a == 1 || a == b {
            b
        } else if b == 1 {
            a
        } else {
            self.pair(a, b, true)
        }
    }
    fn xor(&mut self, a: Value, b: Value) -> Value {
        let invert = (a ^ b) & 1;
        let (a, b) = (a & !1, b & !1);
        if a == 0 {
            return b ^ invert;
        }
        if b == 0 {
            return a ^ invert;
        }
        if a == b {
            return invert;
        }
        let a_sum = self.support(a);
        let b_sum = self.support(b);
        let (mut i, mut j) = (0, 0);
        let mut result = Sum::empty();
        let mut hash = 0x6a09e667f3bcc909u64;
        while i < a_sum.len || j < b_sum.len {
            let o = if j == b_sum.len || i < a_sum.len && a_sum.terms[i] < b_sum.terms[j] {
                i += 1;
                a_sum.terms[i - 1]
            } else if i == a_sum.len || b_sum.terms[j] < a_sum.terms[i] {
                j += 1;
                b_sum.terms[j - 1]
            } else {
                i += 1;
                j += 1;
                continue;
            };
            if result.len == N {
                return self.pair(a, b, false) ^ invert;
            }
            result.terms[result.len] = o;
            result.len += 1;
            hash = hash.rotate_left(11) ^ mix(o);
        }
        match result.len {
            0 => invert,
            1 => result.terms[0] ^ invert,
            _ => {
                let slot = mix(hash) as usize & self.mask;
                let (previous, cached) = self.sums[slot];
                if previous != 0
                    && cached.len == result.len
                    && cached.terms[..cached.len] == result.terms[..result.len]
                {
                    return previous ^ invert;
                }
                let id = self.fresh() | ((slot as u64) << 1);
                self.sums[slot] = (id, result);
                id ^ invert
            }
        }
    }
}

#[derive(Default, Debug)]
pub(super) struct Counts {
    pub dropped: u64,
    pub constants: u64,
    pub equal: u64,
    pub held: u64,
    pub unconditional: u64,
    pub conditional: u64,
    pub processed: usize,
}
pub(super) struct State<const N: usize> {
    v: Values<N>,
    q: Vec<Value>,
    bits: Vec<Value>,
    base: Value,
    stack: Vec<Value>,
    holder: Vec<(Value, usize, usize)>,
    use_holder: bool,
}
impl<const N: usize> State<N> {
    pub(super) fn new(ops: &[Op], slots: usize, use_holder: bool) -> Self {
        let mut depth = 0usize;
        let mut peak = 0;
        let (nq, nb, _, regs) = analyze_ops(ops.iter().inspect(|o| match o.kind {
            K::PushCondition => {
                depth += 1;
                peak = peak.max(depth);
            }
            K::PopCondition => depth = depth.checked_sub(1).expect("unbalanced condition stack"),
            _ => {}
        }));
        let mut state = Self {
            v: Values::new(slots),
            q: vec![0; nq as usize],
            bits: vec![0; nb as usize],
            base: 1,
            stack: Vec::with_capacity(peak),
            holder: vec![(0, usize::MAX, usize::MAX); slots],
            use_holder,
        };
        for slot in regs.into_iter().flatten() {
            match slot {
                QubitOrBit::Qubit(q) if state.q[q.0 as usize] == 0 => {
                    let x = state.v.fresh();
                    state.put(q.0 as usize, x);
                }
                QubitOrBit::Bit(b) if state.bits[b.0 as usize] == 0 => {
                    state.bits[b.0 as usize] = state.v.fresh()
                }
                _ => {}
            }
        }
        state
    }
    fn put(&mut self, i: usize, v: Value) {
        self.q[i] = v;
        if self.use_holder && v > 1 {
            let slot = mix(v) as usize & self.v.mask;
            let (old, a, _) = self.holder[slot];
            if old != v || a != i {
                self.holder[slot] = (v, i, if old == v { a } else { usize::MAX });
            }
        }
    }
    fn witness(&self, v: Value, t: usize) -> Option<QubitId> {
        if !self.use_holder || v <= 1 {
            return None;
        }
        let (old, a, b) = self.holder[mix(v) as usize & self.v.mask];
        if old != v {
            return None;
        }
        [a, b]
            .into_iter()
            .find(|&i| i != usize::MAX && i != t && self.q[i] == v)
            .map(|i| QubitId(i as u64))
    }
    #[inline]
    pub(super) fn step(&mut self, op: Op, stats: &mut Counts) -> Option<Op> {
        stats.processed += 1;
        let cond = if op.c_condition == NO_BIT {
            self.base
        } else {
            self.v.and(self.base, self.bits[op.c_condition.0 as usize])
        };
        let t = op.q_target.0 as usize;
        let mut out = Some(op);
        match op.kind {
            K::CCX | K::CCZ => {
                let a = self.q[op.q_control1.0 as usize];
                let b = self.q[op.q_control2.0 as usize];
                let prod = self.v.and(a, b);
                if prod == 0 || cond == 0 {
                    stats.dropped += 1;
                    out = None;
                } else {
                    let donor = if prod == 1 {
                        stats.constants += 1;
                        Some(NO_QUBIT)
                    } else if prod == a {
                        if b == 1 {
                            stats.constants += 1;
                        } else {
                            stats.equal += 1;
                        }
                        Some(op.q_control1)
                    } else if prod == b {
                        if a == 1 {
                            stats.constants += 1;
                        } else {
                            stats.equal += 1;
                        }
                        Some(op.q_control2)
                    } else if let Some(q) = self.witness(prod, t) {
                        stats.held += 1;
                        Some(q)
                    } else {
                        None
                    };
                    if let Some(control) = donor {
                        let kind = match (op.kind, control == NO_QUBIT) {
                            (K::CCX, true) => K::X,
                            (K::CCX, false) => K::CX,
                            (_, true) => K::Z,
                            _ => K::CZ,
                        };
                        out = Some(Op {
                            kind,
                            q_control1: control,
                            q_control2: NO_QUBIT,
                            ..op
                        });
                    }
                }
                if out.is_none_or(|v| !matches!(v.kind, K::CCX | K::CCZ)) {
                    if self.stack.is_empty() && op.c_condition == NO_BIT {
                        stats.unconditional += 1;
                    } else {
                        stats.conditional += 1;
                    }
                }
                if op.kind == K::CCX {
                    let d = self.v.and(cond, prod);
                    let val = self.v.xor(self.q[t], d);
                    self.put(t, val);
                }
            }
            K::X | K::CX => {
                let d = if op.kind == K::X {
                    cond
                } else {
                    self.v.and(cond, self.q[op.q_control1.0 as usize])
                };
                let val = self.v.xor(self.q[t], d);
                self.put(t, val);
            }
            K::Swap if cond != 0 => {
                let a = op.q_control1.0 as usize;
                let (u, v) = (self.q[a], self.q[t]);
                if cond == 1 {
                    self.put(a, v);
                    self.put(t, u);
                } else {
                    let x = self.v.xor(u, v);
                    let d = self.v.and(cond, x);
                    let p = self.v.xor(u, d);
                    let r = self.v.xor(v, d);
                    self.put(a, p);
                    self.put(t, r);
                }
            }
            K::Hmr | K::R => {
                if op.kind == K::Hmr {
                    let bit = op.c_target.0 as usize;
                    let m = self.v.fresh();
                    if cond == 1 {
                        self.bits[bit] = m;
                    } else if cond != 0 {
                        let old = self.bits[bit];
                        let x = self.v.xor(old, m);
                        let d = self.v.and(cond, x);
                        self.bits[bit] = self.v.xor(old, d);
                    }
                }
                let val = self.v.and(self.q[t], cond ^ 1);
                self.put(t, val);
            }
            K::BitInvert => {
                let b = op.c_target.0 as usize;
                self.bits[b] = self.v.xor(self.bits[b], cond);
            }
            K::BitStore0 => {
                let b = op.c_target.0 as usize;
                self.bits[b] = self.v.and(self.bits[b], cond ^ 1);
            }
            K::BitStore1 => {
                let b = op.c_target.0 as usize;
                self.bits[b] = self.v.and(self.bits[b] ^ 1, cond ^ 1) ^ 1;
            }
            K::PushCondition => {
                self.stack.push(self.base);
                self.base = cond;
            }
            K::PopCondition => self.base = self.stack.pop().expect("unbalanced condition stack"),
            _ => {}
        }
        out
    }
}

/// The write cursor never passes the read cursor. All symbol tables, wire
/// states and stack capacity are allocated before rewriting the first gate.
pub(super) fn apply_in_place(ops: &mut Vec<Op>) -> Counts {
    let mut state = State::<64>::new(ops, 32_768, true);
    let mut counts = Counts::default();
    let mut write = 0;
    for read in 0..ops.len() {
        let op = ops[read];
        if let Some(replacement) = state.step(op, &mut counts) {
            ops[write] = replacement;
            write += 1;
        }
    }
    ops.truncate(write);
    counts
}
