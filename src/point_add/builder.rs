//! Builder: qubit pool, op emission and a small gate IR that can be emitted forward or inverted.
//!
//! Gates are always emitted through `g()`. While a recording is open, they go to the recording instead of the
//! op stream; `play(rec, inverse)` emits a recording forward or as its exact inverse. The only non-self-inverse
//! gates are the measurement-based AND pair: `AndC` (Toffoli into a fresh |0> target, 1 Toffoli) and `AndU`
//! (X-basis measurement of the target plus a classically conditioned CZ fix-up, 0 Toffoli). They invert into
//! each other.

use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_QUBIT, NO_REG};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum G {
    X(QubitId),
    Cx(QubitId, QubitId),
    Ccx(QubitId, QubitId, QubitId),
    Cz(QubitId, QubitId),
    Swap(QubitId, QubitId),
    /// t ^= a & b with t known to be |0> (compute).
    AndC(QubitId, QubitId, QubitId),
    /// t = a & b -> |0> by measurement (uncompute).
    AndU(QubitId, QubitId, QubitId),
    /// X conditioned on a classical bit.
    XIf(QubitId, BitId),
    /// Z conditioned on a classical bit.
    ZIf(QubitId, BitId),
    RowAdd(u32, bool),
}

// Local serialization uses the exact harness record framing. No gate is
// omitted or rewritten: the normal builder and this writer share raw().
struct Stream {
    out: zstd::stream::write::Encoder<'static, std::io::BufWriter<std::fs::File>>,
    count: u64,
}

#[cfg(test)]
mod exact_stream_test {
    use super::*;
    #[test]
    fn serializer_matches_unchanged_harness_bytes() {
        let mut b = B::new();
        let t = b.alloc_n(30);
        let s = b.alloc_n(30);
        let tail = b.alloc_n(40);
        let g = b.alloc();
        let c0 = b.alloc();
        let h = b.alloc();
        let anc = b.alloc_n(39);
        let carries = b.alloc_n(9);
        b.declare_qubits(0, &t);
        let bits = b.declare_bits(2, 30);
        b.x_if(t[0], bits[0]);
        super::super::frogdrop::cadd_tail_and(&mut b, g, &t, &s, &tail, c0, h, &anc, &carries);
        b.swap(t[0], s[0]);
        b.z_if(t[0], bits[1]);
        let prefix = std::env::temp_dir().join(format!("lowq-exact-serializer-{}", std::process::id()));
        let flat = prefix.with_extension("flat.bin");
        let streaming = prefix.with_extension("stream.bin");
        assert!(!flat.exists() && !streaming.exists());
        crate::write_ops(&b.ops, &flat).unwrap();
        let mut writer = Stream::at(&streaming);
        for op in &b.ops { writer.push(op); }
        assert_eq!(writer.finish(), b.ops.len() as u64);
        assert_eq!(std::fs::read(&flat).unwrap(), std::fs::read(&streaming).unwrap());
        std::fs::remove_file(flat).unwrap();
        std::fs::remove_file(streaming).unwrap();
        eprintln!("EXACT_STREAM_SERIALIZER_PASS physical_ops={} all_fields=true trusted_write_ops=true", b.ops.len());
    }
}
impl Stream {
    fn new() -> Option<Self> {
        let path = std::env::var_os("LOWQ_EXACT_STREAM_PATH")?;
        Some(Self::at(std::path::Path::new(&path)))
    }
    fn at(path: &std::path::Path) -> Self {
        use std::io::Write;
        let mut out = std::io::BufWriter::with_capacity(1 << 20, std::fs::File::create(path).unwrap());
        out.write_all(b"QECCOPSZ").unwrap();
        out.write_all(&0u64.to_le_bytes()).unwrap();
        let out = zstd::stream::write::Encoder::new(out, 3).unwrap();
        Self { out, count: 0 }
    }
    fn push(&mut self, op: &Op) {
        use std::io::Write;
        let mut bytes = [0u8; 56];
        bytes[..4].copy_from_slice(&(op.kind as u32).to_le_bytes());
        for (i, v) in [op.q_control2.0, op.q_control1.0, op.q_target.0,
                       op.c_target.0, op.c_condition.0, op.r_target.0].iter().enumerate() {
            bytes[8 + 8*i..16 + 8*i].copy_from_slice(&v.to_le_bytes());
        }
        self.out.write_all(&bytes).unwrap();
        self.count += 1;
    }
    fn finish(self) -> u64 {
        use std::io::{Seek, SeekFrom, Write};
        let mut out = self.out.finish().unwrap();
        out.flush().unwrap();
        out.seek(SeekFrom::Start(8)).unwrap();
        out.write_all(&self.count.to_le_bytes()).unwrap();
        out.flush().unwrap();
        self.count
    }
}

#[derive(Clone)]
struct DeferredRow { row:super::row_add::Row,inverse:bool,masks:Vec<BitId> }

pub struct B {
    pub ops: Vec<Op>,
    stream: Option<Stream>,
    next_q: u64,
    free_q: BTreeSet<u64>,
    pub live: u64,
    pub peak: u64,
    bit: BitId,
    rec: Vec<Vec<G>>,
    pub tof: u64,
    pub peak_op: usize,
    pub allow_booth: bool,
    next_bit: u64,
    rows: Vec<super::row_add::Row>,
    defer_mode:u8, defer_tape:Vec<DeferredRow>,
}

impl B {
    pub fn new() -> Self {
        let mut b = B { ops: Vec::new(), stream: Stream::new(), next_q: 0, free_q: BTreeSet::new(), live: 0, peak: 0, bit: NO_BIT,
                        rec: Vec::new(), tof: 0, next_bit: 10_000, rows: Vec::new(), peak_op: 0, allow_booth: true, defer_mode:0, defer_tape:Vec::new() };
        b.bit = BitId(0);
        b
    }

    pub fn finish_stream(&mut self) -> Option<u64> {
        self.stream.take().map(Stream::finish)
    }

    // ---------------------------------------------------------------- qubits
    pub fn alloc(&mut self) -> QubitId {
        let id = if let Some(&q) = self.free_q.iter().next() {
            self.free_q.remove(&q);
            q
        } else {
            self.next_q += 1;
            self.next_q - 1
        };
        self.live += 1;
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
        QubitId(id)
    }
    pub fn alloc_n(&mut self, n: usize) -> Vec<QubitId> {
        (0..n).map(|_| self.alloc()).collect()
    }
    /// Release a qubit that is |0> on every shot.
    pub fn free(&mut self, q: QubitId) {
        assert!(self.rec.is_empty(), "free inside a recording");
        assert!(self.free_q.insert(q.0), "double free q{}", q.0);
        self.live -= 1;
    }
    pub fn free_n(&mut self, qs: &[QubitId]) {
        for &q in qs {
            self.free(q);
        }
    }
    pub fn width(&self) -> u64 {
        self.next_q
    }

    // ---------------------------------------------------------------- registers
    pub fn declare_qubits(&mut self, reg: u64, qs: &[QubitId]) {
        self.raw(Op { kind: OperationType::Register, r_target: RegisterId(reg), ..Op::empty() });
        for &q in qs {
            self.raw(Op { kind: OperationType::AppendToRegister, q_target: q, r_target: RegisterId(reg),
                          ..Op::empty() });
        }
    }
    pub fn declare_bits(&mut self, reg: u64, n: usize) -> Vec<BitId> {
        self.raw(Op { kind: OperationType::Register, r_target: RegisterId(reg), ..Op::empty() });
        let bs: Vec<BitId> = (0..n).map(|i| BitId(1 + reg * 1000 + i as u64)).collect();
        for &b in &bs {
            self.raw(Op { kind: OperationType::AppendToRegister, c_target: b, r_target: RegisterId(reg),
                          ..Op::empty() });
        }
        bs
    }

    // ---------------------------------------------------------------- emission
    fn raw(&mut self, op: Op) {
        debug_assert!({ op.validate(); true });
        let _ = NO_REG;
        if let Some(stream) = &mut self.stream { stream.push(&op); } else { self.ops.push(op); }
    }
    fn emit(&mut self, g: G, inverse: bool) {
        let e = |kind, t: QubitId, c1: QubitId, c2: QubitId| Op { kind, q_target: t, q_control1: c1, q_control2: c2,
                                                             ..Op::empty() };
        match g {
            G::RowAdd(id, inv) => { let row=self.rows[id as usize].clone(); super::row_add::emit(self,&row,inv ^ inverse); },
            G::X(t) => self.raw(e(OperationType::X, t, NO_QUBIT, NO_QUBIT)),
            G::Cx(c, t) => self.raw(e(OperationType::CX, t, c, NO_QUBIT)),
            G::Cz(a, b) => self.raw(e(OperationType::CZ, b, a, NO_QUBIT)),
            G::Swap(a, b) => self.raw(e(OperationType::Swap, b, a, NO_QUBIT)),
            G::Ccx(a, b, t) => {
                self.tof += 1;
                self.raw(e(OperationType::CCX, t, a, b))
            }
            G::XIf(t, c) => self.raw(Op { kind: OperationType::X, q_target: t, c_condition: c, ..Op::empty() }),
            G::ZIf(t, c) => self.raw(Op { kind: OperationType::Z, q_target: t, c_condition: c, ..Op::empty() }),
            G::AndC(a, b, t) | G::AndU(a, b, t) => {
                let compute = matches!(g, G::AndC(..)) != inverse;
                if compute {
                    self.tof += 1;
                    self.raw(e(OperationType::CCX, t, a, b));
                } else {
                    let m = self.bit;
                    self.raw(Op { kind: OperationType::Hmr, q_target: t, c_target: m, ..Op::empty() });
                    self.raw(Op { kind: OperationType::CZ, q_target: b, q_control1: a, c_condition: m,
                                  ..Op::empty() });
                }
            }
        }
    }
    /// Emit one gate (or record it if a recording is open).
    pub fn g(&mut self, g: G) {
        if let Some(r) = self.rec.last_mut() {
            r.push(g);
        } else {
            self.emit(g, false);
        }
    }
    pub fn begin(&mut self) {
        self.rec.push(Vec::new());
    }
    pub fn end(&mut self) -> Vec<G> {
        self.rec.pop().expect("no recording")
    }
    /// Emit a recording forward or as its inverse (into the enclosing recording if one is open).
    pub fn play(&mut self, r: &[G], inverse: bool) {
        if inverse {
            for &g in r.iter().rev() {
                let gi = match g {
                    G::AndC(a, b, t) => G::AndU(a, b, t),
                    G::AndU(a, b, t) => G::AndC(a, b, t),
                    G::RowAdd(id, inv) => G::RowAdd(id, !inv),
                    other => other,
                };
                self.g(gi);
            }
        } else {
            for &g in r {
                self.g(g);
            }
        }
    }

    pub fn deferred_forward(&mut self) { assert!(self.rec.is_empty()&&self.defer_tape.is_empty()); self.defer_mode=1; }
    pub fn deferred_suspend(&mut self) { assert!(self.rec.is_empty()&&self.defer_mode==1); self.defer_mode=0; }
    pub fn deferred_inverse(&mut self) { assert!(self.rec.is_empty()); self.defer_mode=2; }
    pub fn deferred_finish(&mut self) { assert!(self.rec.is_empty()&&self.defer_tape.is_empty()); self.defer_mode=0; }
    pub fn deferred_row_enter(&mut self,row:&super::row_add::Row,inverse:bool,nf:usize)->Option<(bool,Vec<BitId>)> {
        if nf==0||self.defer_mode==0 { return None; }
        assert!(self.rec.is_empty());
        if self.defer_mode==1 {
            // Reserve existing scratch slots before obtaining fresh persistent bits.
            let _scratch_reservation=self.fresh_bits(2);
            let masks=self.fresh_bits(nf);
            self.defer_tape.push(DeferredRow{row:row.clone(),inverse,masks:masks.clone()});
            Some((true,masks))
        } else {
            let old=self.defer_tape.pop().expect("inverse row without forward occurrence");
            assert_eq!(old.row,*row,"physical row geometry does not match tape");
            assert_ne!(old.inverse,inverse,"direction did not reverse");
            assert_eq!(old.masks.len(),nf);
            Some((false,old.masks))
        }
    }
    pub fn deferred_tape_rows(&self)->usize { self.defer_tape.len() }
    pub fn row_add(&mut self,row:super::row_add::Row){let id=self.rows.len()as u32;self.rows.push(row);self.g(G::RowAdd(id,false));}
    pub fn row_measure(&mut self,q:QubitId){self.raw(Op{kind:OperationType::Hmr,q_target:q,c_target:BitId(self.next_bit),..Op::empty()});}
    pub fn row_condition(&mut self,push:bool){self.raw(Op{kind:if push{OperationType::PushCondition}else{OperationType::PopCondition},c_condition:if push{BitId(self.next_bit)}else{NO_BIT},..Op::empty()});}
    // Slot0 keeps the enclosing boundary mask. Slot1 is reserved for nested
    // source-copy HMR; AndU's bit0 is separate from both row slots.
    pub fn row_measure_slot(&mut self,q:QubitId,slot:u64){assert!(slot<2);self.raw(Op{kind:OperationType::Hmr,q_target:q,c_target:BitId(self.next_bit+slot),..Op::empty()});}
    pub fn row_condition_slot(&mut self,push:bool,slot:u64){assert!(slot<2);self.raw(Op{kind:if push{OperationType::PushCondition}else{OperationType::PopCondition},c_condition:if push{BitId(self.next_bit+slot)}else{NO_BIT},..Op::empty()});}
    // ---------------------------------------------------------------- gate helpers
    pub fn x(&mut self, t: QubitId) {
        self.g(G::X(t));
    }
    pub fn cx(&mut self, c: QubitId, t: QubitId) {
        self.g(G::Cx(c, t));
    }
    pub fn ccx(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::Ccx(a, b, t));
    }
    pub fn cz(&mut self, a: QubitId, b: QubitId) {
        self.g(G::Cz(a, b));
    }
    pub fn swap(&mut self, a: QubitId, b: QubitId) {
        self.g(G::Swap(a, b));
    }
    pub fn and_c(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::AndC(a, b, t));
    }
    pub fn and_u(&mut self, a: QubitId, b: QubitId, t: QubitId) {
        self.g(G::AndU(a, b, t));
    }
    pub fn x_if(&mut self, t: QubitId, c: BitId) {
        self.g(G::XIf(t, c));
    }
    pub fn z_if(&mut self, t: QubitId, c: BitId) {
        self.g(G::ZIf(t, c));
    }
    /// X-basis measurement of q into classical bit c (q -> |0>). Not invertible; never inside a recording.
    pub fn hmr_to(&mut self, q: QubitId, c: BitId) {
        assert!(self.rec.is_empty());
        self.raw(Op { kind: OperationType::Hmr, q_target: q, c_condition: NO_BIT, c_target: c, ..Op::empty() });
    }
    /// Take a specific free qubit back out of the pool.
    pub fn acquire(&mut self, q: QubitId) {
        assert!(self.free_q.remove(&q.0), "acquire of a busy qubit q{}", q.0);
        self.live += 1;
        if self.live > self.peak {
            self.peak = self.live;
            self.peak_op = self.ops.len();
        }
    }
    pub fn fresh_bits(&mut self, n: usize) -> Vec<BitId> {
        let v: Vec<BitId> = (0..n).map(|i| BitId(self.next_bit + i as u64)).collect();
        self.next_bit += n as u64;
        v
    }
    /// Emit a recording controlled on `c`: every gate gets the extra control, except AND compute/uncompute pairs
    /// (their target is clean on both sides whatever happens in between). `tmp` = clean helper not in `r`.
    pub fn play_ctrl(&mut self, r: &[G], c: QubitId, tmp: QubitId) {
        for &g in r {
            match g {
                G::RowAdd(id,inv) => {
                    let mut row=self.rows[id as usize].clone();
                    assert!(!row.signed_binary,"outer-control replay must use allow_booth=false fallback");
                    assert!(!row.bank.contains(&tmp)&&!row.t.contains(&tmp)&&!row.s.contains(&tmp)&&!row.tail.contains(&tmp)&&tmp!=row.c0&&tmp!=row.h&&row.mux.is_none_or(|m|m.sigma!=tmp));
                    let oldg=row.g;self.and_c(c,oldg,tmp);row.g=tmp;
                    let newid=self.rows.len()as u32;self.rows.push(row);self.g(G::RowAdd(newid,inv));
                    self.and_u(c,oldg,tmp);
                },
                G::X(t) => self.cx(c, t),
                G::Cx(a, t) => self.ccx(c, a, t),
                G::Ccx(a, b2, t) => {
                    self.and_c(c, a, tmp);
                    self.ccx(tmp, b2, t);
                    self.and_u(c, a, tmp);
                }
                G::Swap(a, b2) => self.cswap(c, a, b2),
                G::AndC(..) | G::AndU(..) => self.g(g),
                other => panic!("play_ctrl: unsupported gate {:?}", other),
            }
        }
    }
    /// play_ctrl with the AND pairs controlled too (AND compute and uncompute both become controlled Toffolis):
    /// exact identity on control-0 shots whatever the recording's AND nesting.
    pub fn play_ctrl_full(&mut self, r: &[G], c: QubitId, tmp: QubitId) {
        for &g in r {
            match g {
                G::RowAdd(id,inv) => {
                    let mut row=self.rows[id as usize].clone();
                    assert!(!row.signed_binary,"outer-control replay must use allow_booth=false fallback");
                    assert!(!row.bank.contains(&tmp)&&!row.t.contains(&tmp)&&!row.s.contains(&tmp)&&!row.tail.contains(&tmp)&&tmp!=row.c0&&tmp!=row.h&&row.mux.is_none_or(|m|m.sigma!=tmp));
                    let oldg=row.g;self.and_c(c,oldg,tmp);row.g=tmp;
                    let newid=self.rows.len()as u32;self.rows.push(row);self.g(G::RowAdd(newid,inv));
                    self.and_u(c,oldg,tmp);
                },
                G::X(t) => self.cx(c, t),
                G::Cx(a, t) => self.ccx(c, a, t),
                G::Ccx(a, b2, t) | G::AndC(a, b2, t) | G::AndU(a, b2, t) => {
                    self.and_c(c, a, tmp);
                    self.ccx(tmp, b2, t);
                    self.and_u(c, a, tmp);
                }
                G::Swap(a, b2) => self.cswap(c, a, b2),
                other => panic!("play_ctrl_full: unsupported gate {:?}", other),
            }
        }
    }
    /// Controlled swap (Fredkin), 1 Toffoli.
    pub fn cswap(&mut self, c: QubitId, a: QubitId, b: QubitId) {
        self.cx(b, a);
        self.ccx(c, a, b);
        self.cx(b, a);
    }
}
