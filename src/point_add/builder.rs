//! The circuit builder: wire and bit allocation, the gate vocabulary every
//! construction in this tree emits through, and the phase report.
//!
//! Everything here is book-keeping over one `Vec<Op>`. The two censuses it
//! carries only observe that vector -- see [`record`](super::record) -- so no
//! knob reachable from this file can move the op stream.

use crate::circuit::{BitId, Op, OperationType, QubitId, QubitOrBit, RegisterId, NO_BIT};

use super::record::{At, CcxCensus, PeakCensus, ReplaySites};

/// Width of [`Builder::phase_kind_ops`]: one slot per [`OperationType`], so
/// `op.kind as usize` indexes it directly. `DebugPrint` is the last variant.
const OP_KINDS: usize = OperationType::DebugPrint as usize + 1;

pub struct Builder {
    ops: Vec<Op>,
    /// Ops of each kind emitted since the last [`Builder::set_phase`]; only the
    /// two Toffoli kinds are reported, but indexing by `kind` is cheaper than
    /// branching on it.
    phase_kind_ops: [usize; OP_KINDS],
    next_qubit: u32,
    next_bit: u32,
    free_bits: Vec<u32>,
    next_register: u32,
    free_qubits: Vec<u32>,
    active_qubits: u32,
    peak_qubits: u32,
    phase: &'static str,
    peak_census: PeakCensus,
    ccx_census: CcxCensus,
    replay_sites: ReplaySites,
}

impl Builder {
    pub fn new() -> Self {
        Self {
            ops: Vec::new(),
            phase_kind_ops: [0; OP_KINDS],
            next_qubit: 0,
            next_bit: 0,
            free_bits: Vec::new(),
            next_register: 0,
            free_qubits: Vec::new(),
            active_qubits: 0,
            peak_qubits: 0,
            phase: "init",
            peak_census: PeakCensus::new(),
            ccx_census: CcxCensus::new(),
            replay_sites: ReplaySites::new(),
        }
    }
    pub fn take_ops(&mut self) -> Vec<Op> {
        std::mem::take(&mut self.ops)
    }
    fn push_op(&mut self, op: Op) {
        // Tripwire, live only while tracing: every gate the score counts must
        // have been attributed by `ccx_census` first. CCX is the only scored
        // kind emitted today, so this is what a new CCZ path would trip.
        if self.ccx_census.watching() && CcxCensus::scored(op.kind) {
            assert!(
                self.ccx_census.covers(self.ops.len()),
                "{:?} at op {} reached push_op without CcxCensus::on_gate",
                op.kind,
                self.ops.len()
            );
        }
        self.phase_kind_ops[op.kind as usize] += 1;
        self.ops.push(op);
    }
    /// Close the current phase: report its Toffoli count and peak width on
    /// stdout -- which is what `build_circuit` prints -- and start a new one.
    pub fn set_phase(&mut self, p: &'static str) {
        self.peak_qubits = 0;
        self.phase_kind_ops = [0; OP_KINDS];
        self.phase = p;
    }

    /// Where the build is, for the recorders in [`record`].
    fn at(&self) -> At {
        At {
            phase: self.phase,
            op: self.ops.len(),
            active: self.active_qubits,
        }
    }
    /// Attach build-time context to the next Toffoli emitted; see
    /// [`CcxCensus::note`].
    pub fn ccx_note(&mut self, note: u64) {
        self.ccx_census.note(note);
    }

    /// Book-keeping only -- emits no ops. Called by both routes that raise
    /// `active_qubits`: a fresh `alloc_qubit` and a `reacquire` of a parked one.
    fn note_peak(&mut self) {
        self.peak_qubits = self.peak_qubits.max(self.active_qubits);
    }

    #[track_caller]
    pub fn alloc_qubit(&mut self) -> QubitId {
        self.active_qubits += 1;
        self.note_peak();
        let qid = if let Some(q) = self.free_qubits.pop() {
            QubitId(q.into())
        } else {
            let q = self.next_qubit;
            self.next_qubit += 1;
            QubitId(q.into())
        };
        if self.peak_census.enabled() {
            let (at, caller) = (self.at(), std::panic::Location::caller());
            self.peak_census
                .on_alloc(at, qid.0, caller.file(), caller.line());
        }
        qid
    }
    #[track_caller]
    pub fn alloc_qubits(&mut self, n: usize) -> Vec<QubitId> {
        if self.peak_census.enabled() {
            let c = std::panic::Location::caller();
            self.peak_census.batch(Some((c.file(), c.line())));
            let out = (0..n).map(|_| self.alloc_qubit()).collect();
            self.peak_census.batch(None);
            out
        } else {
            (0..n).map(|_| self.alloc_qubit()).collect()
        }
    }
    pub fn alloc_bit(&mut self) -> BitId {
        if let Some(b) = self.free_bits.pop() {
            return BitId(b.into());
        }
        let b = self.next_bit;
        self.next_bit += 1;
        BitId(b.into())
    }
    /// Return a classical bit to the pool.
    ///
    /// Unlike [`Builder::free`] for a qubit this emits nothing -- a bit carries no
    /// state the simulator has to clear, because every allocation site's first
    /// op on a bit *writes* it (`hmr`'s target, or a `bit_store`), never reads
    /// it. That is the whole safety condition, and it is what makes reuse
    /// invisible to the op stream: freeing a bit changes only which id later
    /// allocations get.
    ///
    /// The caller owns the lifetime: free only after the last op that reads the
    /// bit, and never while it is the live `push_condition`.
    pub fn free_bit(&mut self, b: BitId) {
        self.free_bits
            .push(b.0.try_into().expect("bit id fits in u32"));
    }
    pub fn free_bit_vec(&mut self, bs: &[BitId]) {
        for &b in bs {
            self.free_bit(b);
        }
    }
    pub fn alloc_bits(&mut self, n: usize) -> Vec<BitId> {
        (0..n).map(|_| self.alloc_bit()).collect()
    }
    pub fn free(&mut self, q: QubitId) {
        self.r(q);
        self.release_clean(q);
    }
    /// Return a qubit that the caller has unitarily restored to |0> without
    /// emitting a reset. This preserves the measurement stream when a clean
    /// temporary is parked and reused inside one reversible cell.
    pub fn release_clean(&mut self, q: QubitId) {
        self.free_qubits
            .push(q.0.try_into().expect("qubit id fits in u32"));
        if self.active_qubits > 0 {
            self.active_qubits -= 1;
        }
        let at = self.at();
        self.peak_census.on_free(at, q.0);
    }
    pub fn free_vec(&mut self, qs: &[QubitId]) {
        for &q in qs {
            self.free(q);
        }
    }
    pub fn reacquire(&mut self, q: QubitId) {
        let pos = self
            .free_qubits
            .iter()
            .position(|&free_q| u64::from(free_q) == q.0)
            .unwrap_or_else(|| {
                panic!(
                    "reacquire qubit {:?} that is not currently free (phase '{}', ops {})",
                    q,
                    self.phase,
                    self.ops.len()
                )
            });
        self.free_qubits.swap_remove(pos);
        self.active_qubits += 1;
        self.note_peak();

        if self.peak_census.enabled() {
            let at = self.at();
            self.peak_census.on_alloc(at, q.0, "reacquire", 0);
        }
    }
    /// Declare a register over `members`, in order.
    ///
    /// The op stream tells a qubit member from a bit member only by which target
    /// field is set, so one routine serves both and the two spellings below just
    /// tag their elements.
    fn declare_register(&mut self, members: impl Iterator<Item = QubitOrBit>) {
        let r = RegisterId(self.next_register.into());
        self.next_register += 1;
        for m in members {
            let mut op = Op::empty();
            op.kind = OperationType::AppendToRegister;
            match m {
                QubitOrBit::Qubit(q) => op.q_target = q,
                QubitOrBit::Bit(b) => op.c_target = b,
            }
            op.r_target = r;
            self.push_op(op);
        }
        let mut op = Op::empty();
        op.kind = OperationType::Register;
        op.r_target = r;
        self.push_op(op);
    }
    pub fn declare_qubit_register(&mut self, qs: &[QubitId]) {
        self.declare_register(qs.iter().copied().map(QubitOrBit::Qubit));
    }
    pub fn declare_bit_register(&mut self, bs: &[BitId]) {
        self.declare_register(bs.iter().copied().map(QubitOrBit::Bit));
    }
    pub fn x(&mut self, q: QubitId) {
        let mut op = Op::empty();
        op.kind = OperationType::X;
        op.q_target = q;
        self.push_op(op);
    }

    /// `x(q)`, applied only on the branch where classical bit `c` is set.
    pub fn x_if_bit(&mut self, q: QubitId, c: BitId) {
        self.push_condition(c);
        self.x(q);
        self.pop_condition();
    }
    pub fn cx(&mut self, ctrl: QubitId, tgt: QubitId) {
        assert_ne!(ctrl, tgt, "invalid CX with aliased control/target {ctrl:?}",);
        let mut op = Op::empty();
        op.kind = OperationType::CX;
        op.q_control1 = ctrl;
        op.q_target = tgt;
        self.push_op(op);
    }
    #[track_caller]
    pub fn ccx(&mut self, c1: QubitId, c2: QubitId, tgt: QubitId) {
        if c1 == c2 {
            if c1 != tgt {
                self.cx(c1, tgt);
            }
            return;
        }
        assert!(
            c1 != tgt && c2 != tgt,
            "invalid CCX with target aliased to a control: {c1:?}, {c2:?}, {tgt:?}"
        );
        let mut op = Op::empty();
        op.kind = OperationType::CCX;
        op.q_control2 = c1;
        op.q_control1 = c2;
        op.q_target = tgt;

        // Attribution for the dead-CCX hunt. `ccx` is #[track_caller], so
        // Location::caller() here is the construction that wanted the Toffoli,
        // not a helper inside this file.
        if self.ccx_census.watching() {
            let at = self.at();
            self.ccx_census
                .on_gate(at, OperationType::CCX, std::panic::Location::caller());
        }

        self.push_op(op);
    }
    /// `CZ(a, b)`, degenerating to `Z(a)` when both operands are the same wire --
    /// which is what `Addend::One` leans on in the constant ladder, where a hard
    /// one has no wire of its own and collapses onto the other operand. `cond`
    /// gates the gate on a classical bit; `NO_BIT` means unconditional.
    pub fn cz_if(&mut self, a: QubitId, b: QubitId, cond: BitId) {
        let mut op = Op::empty();
        if a == b {
            op.kind = OperationType::Z;
            op.q_target = a;
        } else {
            op.kind = OperationType::CZ;
            op.q_control1 = a;
            op.q_target = b;
        }
        op.c_condition = cond;
        self.push_op(op);
    }
    pub fn cz(&mut self, a: QubitId, b: QubitId) {
        self.cz_if(a, b, NO_BIT);
    }
    pub fn push_condition(&mut self, cond: BitId) {
        let mut op = Op::empty();
        op.kind = OperationType::PushCondition;
        op.c_condition = cond;
        self.push_op(op);
    }
    pub fn pop_condition(&mut self) {
        let mut op = Op::empty();
        op.kind = OperationType::PopCondition;
        self.push_op(op);
    }
    pub fn swap(&mut self, a: QubitId, b: QubitId) {
        if a == b {
            return;
        }
        let mut op = Op::empty();
        op.kind = OperationType::Swap;
        op.q_control1 = a;
        op.q_target = b;
        self.push_op(op);
    }
    fn r(&mut self, q: QubitId) {
        let mut op = Op::empty();
        op.kind = OperationType::R;
        op.q_target = q;
        self.push_op(op);
    }
    pub fn hmr(&mut self, q: QubitId, c: BitId) {
        let mut op = Op::empty();
        op.kind = OperationType::Hmr;
        op.q_target = q;
        op.c_target = c;
        self.push_op(op);
    }

    /// `Z(q)` under `cond`: the degenerate [`Builder::cz_if`] above.
    pub fn z_if(&mut self, q: QubitId, cond: BitId) {
        self.cz_if(q, q, cond);
    }

    pub fn bit_store0(&mut self, dst: BitId) {
        let mut op = Op::empty();
        op.kind = OperationType::BitStore0;
        op.c_target = dst;
        self.push_op(op);
    }

    pub fn bit_store1(&mut self, dst: BitId) {
        let mut op = Op::empty();
        op.kind = OperationType::BitStore1;
        op.c_target = dst;
        self.push_op(op);
    }

    fn bit_invert(&mut self, dst: BitId) {
        let mut op = Op::empty();
        op.kind = OperationType::BitInvert;
        op.c_target = dst;
        self.push_op(op);
    }

    pub fn bit_copy(&mut self, dst: BitId, a: BitId) {
        self.bit_store0(dst);
        self.push_condition(a);
        self.bit_store1(dst);
        self.pop_condition();
    }

    pub fn bit_xor_into(&mut self, dst: BitId, a: BitId) {
        self.push_condition(a);
        self.bit_invert(dst);
        self.pop_condition();
    }

    pub fn bit_and_xor_into(&mut self, dst: BitId, a: BitId, b: BitId) {
        self.push_condition(a);
        self.push_condition(b);
        self.bit_invert(dst);
        self.pop_condition();
        self.pop_condition();
    }
    /// `X` on every wire in `qs`.
    pub fn x_all(&mut self, qs: &[QubitId]) {
        for &q in qs {
            self.x(q);
        }
    }

    /// `CX` from one control onto every wire in `qs`.
    pub fn cx_all(&mut self, ctrl: QubitId, qs: &[QubitId]) {
        for &q in qs {
            self.cx(ctrl, q);
        }
    }

    /// Copy `src` onto `dst`, wire for wire. Self-inverse. Slice the wider side
    /// at the call site: matching the widths here keeps the zip from quietly
    /// dropping a tail.
    pub fn cx_pairs(&mut self, src: &[QubitId], dst: &[QubitId]) {
        assert_eq!(src.len(), dst.len(), "cx_pairs: width mismatch");
        for (&s, &d) in src.iter().zip(dst) {
            self.cx(s, d);
        }
    }

    /// Live wires right now. The walk reads it to decide how much ladder it can
    /// afford against `PP_WALK_MAX_QUBITS`.
    pub fn active_qubits(&self) -> u32 {
        self.active_qubits
    }

    /// Record one replay repair site; see [`ReplaySites::record`].
    pub fn record_replay_site(&mut self, kind: char, round: usize, pos: usize, width: usize) {
        let at = self.at();
        self.replay_sites.record(at, kind, round, pos, width);
    }

    /// Emit all three recorders' output. Called once, at the end of
    /// `build_point_add`.
    pub fn finalize_records(&mut self) {
        self.peak_census.finalize();
        self.ccx_census.finalize();
        self.replay_sites.finalize();
    }
}
