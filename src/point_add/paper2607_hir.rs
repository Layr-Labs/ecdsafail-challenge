use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_QUBIT};

const MAGIC: &[u8; 8] = b"P26HIR1\0";
const COMPRESSED_HIR: &[u8] = include_bytes!("paper2607_runtime.hir.zst");

#[path = "predicate_offsets.rs"]
mod predicate_offsets;

struct Reader<'a> {
    data: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn byte(&mut self) -> u8 {
        let value = *self.data.get(self.at).expect("truncated paper-2607 HIR");
        self.at += 1;
        value
    }

    fn uvar(&mut self) -> usize {
        let mut value = 0usize;
        let mut shift = 0usize;
        loop {
            let byte = self.byte();
            value |= usize::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return value;
            }
            shift += 7;
            assert!(
                shift < usize::BITS as usize,
                "oversized paper-2607 HIR varint"
            );
        }
    }
}

#[derive(Clone, Copy, Default)]
struct Summary {
    output_ops: usize,
    h: usize,
    measure: usize,
    reset: usize,
    toffoli: usize,
}

impl Summary {
    fn add(&mut self, other: Self) {
        self.output_ops = self.output_ops.checked_add(other.output_ops).unwrap();
        self.h = self.h.checked_add(other.h).unwrap();
        self.measure = self.measure.checked_add(other.measure).unwrap();
        self.reset = self.reset.checked_add(other.reset).unwrap();
        self.toffoli = self.toffoli.checked_add(other.toffoli).unwrap();
    }
}

#[derive(Clone, Copy)]
struct Node {
    start: usize,
    end: usize,
}

struct Graph<'a> {
    data: &'a [u8],
    nodes: Vec<Node>,
    root: usize,
    root_qubits: usize,
    root_bits: usize,
    summaries: Vec<Summary>,
}

fn skip_vector(reader: &mut Reader<'_>) {
    let width = reader.uvar();
    for _ in 0..width {
        reader.uvar();
    }
}

fn condition_overhead(reader: &mut Reader<'_>) -> usize {
    let width = reader.uvar();
    let expected = reader.uvar();
    if width == 0 {
        assert_eq!(expected, 1, "invalid unconditional HIR sentinel");
    } else {
        assert!(
            width < usize::BITS as usize && expected < (1usize << width),
            "invalid paper-2607 HIR condition"
        );
    }
    let zeros = if width == 0 {
        0
    } else {
        width - expected.count_ones() as usize
    };
    for _ in 0..width {
        reader.uvar();
    }
    2 * width + 2 * zeros
}

fn parse_graph(data: &[u8]) -> Graph<'_> {
    assert!(data.len() >= MAGIC.len() && &data[..MAGIC.len()] == MAGIC);
    let mut reader = Reader {
        data,
        at: MAGIC.len(),
    };
    assert_eq!(reader.uvar(), 1, "unsupported paper-2607 HIR version");
    let root = reader.uvar();
    let node_count = reader.uvar();
    assert!(root < node_count);
    let mut nodes = Vec::with_capacity(node_count);
    for _ in 0..node_count {
        let len = reader.uvar();
        let end = reader
            .at
            .checked_add(len)
            .expect("HIR node length overflow");
        assert!(end <= data.len(), "truncated paper-2607 HIR node");
        nodes.push(Node {
            start: reader.at,
            end,
        });
        reader.at = end;
    }
    assert_eq!(reader.at, data.len(), "trailing paper-2607 HIR bytes");

    let mut summaries = Vec::with_capacity(node_count);
    let mut widths = Vec::with_capacity(node_count);
    for (node_id, node) in nodes.iter().copied().enumerate() {
        let mut body = Reader {
            data: &data[node.start..node.end],
            at: 0,
        };
        let num_qubits = body.uvar();
        let num_bits = body.uvar();
        widths.push((num_qubits, num_bits));
        let mut summary = Summary::default();
        let op_count = body.uvar();
        for _ in 0..op_count {
            let tag = body.byte();
            summary.output_ops += condition_overhead(&mut body);
            if tag == 11 {
                let child = body.uvar();
                assert!(child < node_id, "paper-2607 HIR is not child-before-parent");
                summary.add(summaries[child]);
            } else {
                match tag {
                    1..=7 => {
                        summary.output_ops += 1;
                        if matches!(tag, 5 | 6) {
                            summary.toffoli += 1;
                        }
                    }
                    8 => {
                        summary.output_ops += 1;
                        summary.h += 1;
                    }
                    9 => summary.measure += 1,
                    10 => summary.reset += 1,
                    _ => panic!("unknown paper-2607 HIR tag {tag}"),
                }
            }
            skip_vector(&mut body);
            skip_vector(&mut body);
        }
        assert_eq!(
            body.at,
            body.data.len(),
            "trailing bytes in HIR node {node_id}"
        );
        summaries.push(summary);
    }
    let (root_qubits, root_bits) = widths[root];
    let root_summary = summaries[root];
    assert_eq!(root_summary.h, root_summary.measure, "unpaired H/measure");
    assert_eq!(root_summary.h, root_summary.reset, "unpaired H/reset");
    Graph {
        data,
        nodes,
        root,
        root_qubits,
        root_bits,
        summaries,
    }
}

#[derive(Clone, Copy)]
enum PendingHmr {
    None,
    H(QubitId),
    Measure(QubitId, BitId),
}

struct State {
    out: Vec<Op>,
    pending_raw: Option<Op>,
    retain_output: bool,
    proof: super::clean_and::Proof,
    measurement_bit: BitId,
    predicate_bit: BitId,
    predicate_blocks: usize,
    input_ops: usize,
    output_ops: usize,
    input_hist: [usize; 18],
    output_hist: [usize; 18],
    outer_toggles: usize,
    outer_lowered: usize,
    examples: Vec<(usize, Op)>,
    qmap: Vec<QubitId>,
    cmap: Vec<BitId>,
    pending_hmr: PendingHmr,
}

impl State {
    fn new(
        nq: usize,
        nb: usize,
        qinputs: &[usize],
        cinputs: &[usize],
        retain_output: bool,
        capacity: usize,
    ) -> Self {
        Self {
            out: Vec::with_capacity(if retain_output { capacity } else { 0 }),
            pending_raw: None,
            retain_output,
            proof: super::clean_and::Proof::new(nq, nb + 2, qinputs, cinputs),
            measurement_bit: BitId(nb as u64),
            predicate_bit: BitId(nb as u64 + 1),
            predicate_blocks: 0,
            input_ops: 0,
            output_ops: 0,
            input_hist: [0; 18],
            output_hist: [0; 18],
            outer_toggles: 0,
            outer_lowered: 0,
            examples: Vec::new(),
            qmap: (0..nq).map(|q| QubitId(q as u64)).collect(),
            cmap: (0..nb).map(|c| BitId(c as u64)).collect(),
            pending_hmr: PendingHmr::None,
        }
    }
    fn write(&mut self, op: Op) {
        self.output_ops += 1;
        self.output_hist[op.kind as usize] += 1;
        if self.retain_output {
            self.out.push(op);
        }
    }
    fn flush_raw(&mut self) {
        let Some(op) = self.pending_raw.take() else {
            return;
        };
        self.input_ops += 1;
        self.input_hist[op.kind as usize] += 1;
        if op.q_target == QubitId(0) {
            assert_eq!(op.kind, OperationType::X, "unexpected outer-control target");
            self.outer_toggles += 1;
        }
        if matches!(op.kind, OperationType::CCX | OperationType::CCZ)
            && (op.q_control1 == QubitId(0) || op.q_control2 == QubitId(0))
        {
            self.outer_lowered += 1;
        }
        if self.proof.step(&op) {
            if self.examples.len() < 32 {
                self.examples.push((self.input_ops - 1, op));
            }
            for new in super::clean_and::replacement(&op, self.measurement_bit) {
                self.write(new);
            }
        } else {
            self.write(op);
        }
    }
    fn raw(&mut self, kind: OperationType) -> &mut Op {
        self.flush_raw();
        let mut op = Op::empty();
        op.kind = kind;
        self.pending_raw = Some(op);
        self.pending_raw.as_mut().unwrap()
    }

    fn emit_condition(&mut self, start: usize, width: usize, expected: usize) {
        if width == 0 {
            assert_eq!(expected, 1);
            return;
        }
        for i in 0..width {
            let bit = self.cmap[start + i];
            if (expected >> i) & 1 == 0 {
                self.raw(OperationType::BitInvert).c_target = bit;
            }
            self.raw(OperationType::PushCondition).c_condition = bit;
        }
    }

    fn unemit_condition(&mut self, start: usize, width: usize, expected: usize) {
        for i in (0..width).rev() {
            let bit = self.cmap[start + i];
            self.raw(OperationType::PopCondition);
            if (expected >> i) & 1 == 0 {
                self.raw(OperationType::BitInvert).c_target = bit;
            }
        }
    }

    fn emit_leaf(&mut self, tag: u8, q: &[QubitId; 3], qlen: usize, c: BitId, clen: usize) {
        match tag {
            8 => {
                assert!(matches!(self.pending_hmr, PendingHmr::None));
                assert_eq!(qlen, 1);
                self.pending_hmr = PendingHmr::H(q[0]);
                return;
            }
            9 => {
                let PendingHmr::H(hq) = self.pending_hmr else {
                    panic!("measurement without preceding H")
                };
                assert_eq!(qlen, 1);
                assert_eq!(q[0], hq);
                assert_eq!(clen, 1);
                self.pending_hmr = PendingHmr::Measure(hq, c);
                return;
            }
            10 => {
                let PendingHmr::Measure(hq, bit) = self.pending_hmr else {
                    panic!("reset without preceding H/measurement")
                };
                assert_eq!(qlen, 1);
                assert_eq!(q[0], hq);
                let op = self.raw(OperationType::Hmr);
                op.q_target = hq;
                op.c_target = bit;
                self.pending_hmr = PendingHmr::None;
                return;
            }
            _ => assert!(
                matches!(self.pending_hmr, PendingHmr::None),
                "incomplete HMR"
            ),
        }
        match tag {
            1 | 2 => {
                assert_eq!(qlen, 1);
                self.raw(if tag == 1 {
                    OperationType::X
                } else {
                    OperationType::Z
                })
                .q_target = q[0];
            }
            3 | 4 | 7 => {
                assert_eq!(qlen, 2);
                let kind = match tag {
                    3 => OperationType::CX,
                    4 => OperationType::CZ,
                    _ => OperationType::Swap,
                };
                let op = self.raw(kind);
                op.q_control1 = q[0];
                op.q_target = q[1];
            }
            5 | 6 => {
                assert_eq!(qlen, 3);
                let op = self.raw(if tag == 5 {
                    OperationType::CCX
                } else {
                    OperationType::CCZ
                });
                op.q_control2 = q[0];
                op.q_control1 = q[1];
                op.q_target = q[2];
            }
            _ => panic!("unknown paper-2607 HIR primitive tag {tag}"),
        }
        assert_eq!(clen, 0, "unexpected classical target on unitary primitive");
    }
}

// Luongo et al. arXiv:2407.20167, single-bit measurement uncomputation.
// This is ONLY the final comparator of a forward modular addition. The same
// comparator at the beginning of subtraction computes a flag and is excluded.
fn predicate_cleanup(
    reader: &mut Reader<'_>, state: &mut State, node_id: usize,
    qstart: usize, ctrl: usize,
) -> usize {
    let (left_start, right_start, carry, flag) = match node_id {
        2262 => (512, 256, 768, 769), // forward multiplication
        2265 => (256, 0, 513, 514),   // forward squaring, copied control
        2267 => (257, 1, 513, 514),   // forward runtime-coordinate addition
        _ => panic!("unapproved arithmetic predicate node"),
    };
    let n = 256;
    let mut original: Vec<(u8, Vec<usize>)> = Vec::with_capacity(8 * n + 5);
    let mut add = |tag, wires: &[usize]| original.push((tag, wires.to_vec()));
    for i in 0..n { add(1, &[right_start + i]); }
    add(1, &[carry]);
    for i in 0..n {
        let (a, b, c) = (left_start + i, right_start + i,
            if i == 0 { carry } else { left_start + i - 1 });
        add(3, &[a,b]); add(3, &[a,c]); add(5, &[c,b,a]);
    }
    add(1, &[left_start+n-1]);
    add(5, &[ctrl,left_start+n-1,flag]);
    add(1, &[left_start+n-1]);
    for i in (0..n).rev() {
        let (a, b, c) = (left_start + i, right_start + i,
            if i == 0 { carry } else { left_start + i - 1 });
        add(5, &[c,b,a]); add(3, &[a,c]); add(3, &[a,b]);
    }
    add(1, &[carry]);
    for i in 0..n { add(1, &[right_start+i]); }
    // Validate the entire source block, including unconditionality and wire
    // order, before emitting a single replacement operation. No fuzzy matches.
    for (tag, wires) in &original {
        assert_eq!(reader.byte(), *tag, "predicate source gate mismatch");
        assert_eq!(reader.uvar(), 0, "conditional predicate source");
        assert_eq!(reader.uvar(), 1);
        assert_eq!(reader.uvar(), wires.len());
        for &q in wires { assert_eq!(reader.uvar(), q, "predicate source wire mismatch"); }
        assert_eq!(reader.uvar(), 0);
    }
    let bit = state.predicate_bit;
    let flag_q = state.qmap[qstart+flag];
    let hmr = state.raw(OperationType::Hmr);
    hmr.q_target = flag_q; hmr.c_target = bit;
    state.raw(OperationType::PushCondition).c_condition = bit;
    for (tag, wires) in &original {
        let is_output = *tag == 5 && wires[2] == flag;
        let len = if is_output { 2 } else { wires.len() };
        let mut mapped = [NO_QUBIT; 3];
        for i in 0..len { mapped[i] = state.qmap[qstart+wires[i]]; }
        // Replacing the sole flag toggle by CZ computes the phase of the
        // predicate without touching the measured/reset flag. The surrounding
        // carry compute/uncompute is executed only for measurement outcome 1.
        state.emit_leaf(if is_output { 4 } else { *tag }, &mapped, len, NO_BIT, 0);
    }
    state.raw(OperationType::PopCondition);
    state.predicate_blocks += 1;
    original.len()
}

fn expand_node(
    graph: &Graph<'_>,
    state: &mut State,
    node_id: usize,
    qstart: usize,
    qlen: usize,
    cstart: usize,
    clen: usize,
) {
    let node = graph.nodes[node_id];
    let mut reader = Reader {
        data: &graph.data[node.start..node.end],
        at: 0,
    };
    assert_eq!(reader.uvar(), qlen, "bad HIR qubit map for node {node_id}");
    assert_eq!(reader.uvar(), clen, "bad HIR bit map for node {node_id}");
    let op_count = reader.uvar();
    let cleanups = match node_id {
        2262 => predicate_offsets::NODE_2262,
        2265 => predicate_offsets::NODE_2265,
        2267 => predicate_offsets::NODE_2267,
        _ => &[],
    };
    let mut cleanup_index = 0;
    let mut op_index = 0;
    while op_index < op_count {
        if let Some(&(offset, ctrl)) = cleanups.get(cleanup_index) {
            assert!(reader.at <= offset, "missed exact predicate boundary");
            if reader.at == offset {
                op_index += predicate_cleanup(&mut reader, state, node_id, qstart, ctrl);
                cleanup_index += 1;
                continue;
            }
        }
        op_index += 1;
        let tag = reader.byte();
        let condition_width = reader.uvar();
        let expected = reader.uvar();
        if condition_width == 0 {
            assert_eq!(expected, 1);
        } else {
            assert!(condition_width < usize::BITS as usize);
            assert!(expected < (1usize << condition_width));
        }
        let condition_start = state.cmap.len();
        for _ in 0..condition_width {
            let local = reader.uvar();
            assert!(local < clen);
            state.cmap.push(state.cmap[cstart + local]);
        }
        state.emit_condition(condition_start, condition_width, expected);

        if tag == 11 {
            let child = reader.uvar();
            assert!(child < node_id);
            let child_qstart = state.qmap.len();
            let child_qlen = reader.uvar();
            for _ in 0..child_qlen {
                let local = reader.uvar();
                assert!(local < qlen);
                state.qmap.push(state.qmap[qstart + local]);
            }
            let child_cstart = state.cmap.len();
            let child_clen = reader.uvar();
            for _ in 0..child_clen {
                let local = reader.uvar();
                assert!(local < clen);
                state.cmap.push(state.cmap[cstart + local]);
            }
            expand_node(
                graph,
                state,
                child,
                child_qstart,
                child_qlen,
                child_cstart,
                child_clen,
            );
            state.qmap.truncate(child_qstart);
            state.cmap.truncate(child_cstart);
        } else {
            let mut qargs = [NO_QUBIT; 3];
            let leaf_qlen = reader.uvar();
            assert!(leaf_qlen <= qargs.len());
            for target in qargs.iter_mut().take(leaf_qlen) {
                let local = reader.uvar();
                assert!(local < qlen);
                *target = state.qmap[qstart + local];
            }
            let leaf_clen = reader.uvar();
            assert!(leaf_clen <= 1);
            let c = if leaf_clen == 1 {
                let local = reader.uvar();
                assert!(local < clen);
                state.cmap[cstart + local]
            } else {
                NO_BIT
            };
            assert!(condition_width == 0 || !matches!(tag, 8 | 9 | 10));
            state.emit_leaf(tag, &qargs, leaf_qlen, c, leaf_clen);
        }

        state.unemit_condition(condition_start, condition_width, expected);
        state.cmap.truncate(condition_start);
    }
    assert_eq!(cleanup_index, cleanups.len(), "missing predicate source block");
    assert_eq!(op_index, op_count);
    assert_eq!(
        reader.at,
        reader.data.len(),
        "trailing bytes in HIR node {node_id}"
    );
}

fn declare_register(out: &mut Vec<Op>, register: u64, qubits: &[QubitId], bits: &[BitId]) {
    for &qubit in qubits {
        let mut op = Op::empty();
        op.kind = OperationType::AppendToRegister;
        op.q_target = qubit;
        op.r_target = RegisterId(register);
        out.push(op);
    }
    for &bit in bits {
        let mut op = Op::empty();
        op.kind = OperationType::AppendToRegister;
        op.c_target = bit;
        op.r_target = RegisterId(register);
        out.push(op);
    }
    let mut op = Op::empty();
    op.kind = OperationType::Register;
    op.r_target = RegisterId(register);
    out.push(op);
}

fn eliminate_constant_outer_control(ops: &mut Vec<Op>, control: QubitId) {
    let mut removed_control_toggles = 0usize;
    let mut lowered_toffolis = 0usize;
    ops.retain_mut(|op| {
        if op.q_target == control {
            assert_eq!(
                op.kind,
                OperationType::X,
                "paper outer control is unexpectedly used as a target"
            );
            removed_control_toggles += 1;
            return false;
        }
        match op.kind {
            OperationType::CX | OperationType::CZ if op.q_control1 == control => {
                op.kind = if op.kind == OperationType::CX {
                    OperationType::X
                } else {
                    OperationType::Z
                };
                op.q_control1 = NO_QUBIT;
            }
            OperationType::CCX | OperationType::CCZ
                if op.q_control1 == control || op.q_control2 == control =>
            {
                let other = if op.q_control1 == control {
                    op.q_control2
                } else {
                    op.q_control1
                };
                op.kind = if op.kind == OperationType::CCX {
                    OperationType::CX
                } else {
                    OperationType::CZ
                };
                op.q_control2 = NO_QUBIT;
                op.q_control1 = other;
                lowered_toffolis += 1;
            }
            OperationType::Swap if op.q_control1 == control || op.q_target == control => {
                panic!("paper outer control is unexpectedly swapped")
            }
            _ => {
                assert_ne!(
                    op.q_control1, control,
                    "paper outer control has an unsupported control use"
                );
                assert_ne!(
                    op.q_control2, control,
                    "paper outer control has an unsupported control use"
                );
            }
        }
        for qubit in [&mut op.q_control2, &mut op.q_control1, &mut op.q_target] {
            if *qubit != NO_QUBIT {
                assert!(qubit.0 > control.0);
                qubit.0 -= 1;
            }
        }
        true
    });
    assert_eq!(
        removed_control_toggles, 2,
        "paper outer control must be initialized and cleaned exactly once"
    );
    eprintln!("PAPER2607_CONST_CTRL: removed_qubits=1 lowered_toffolis={lowered_toffolis}");
}

pub(super) fn build() -> Vec<Op> {
    let decoded = zstd::stream::decode_all(COMPRESSED_HIR).expect("decode paper-2607 HIR");
    let graph = parse_graph(&decoded);
    assert_eq!(graph.root_bits % 5, 0);
    let n = graph.root_bits / 5;
    assert!(
        graph.root_qubits > 1 + 3 * n,
        "paper-2607 HIR must include the outer control, X/Y/A, and workspace"
    );
    let declarations = 4 * (n + 1);
    let summary = graph.summaries[graph.root];
    let qinputs: Vec<_> = (1..=2 * n).collect();
    let cinputs: Vec<_> = (0..2 * n).collect();
    let mut state = State::new(
        graph.root_qubits,
        graph.root_bits,
        &qinputs,
        &cinputs,
        true,
        summary.output_ops + declarations + summary.toffoli,
    );
    let tx: Vec<_> = (1..=n).map(|index| QubitId(index as u64)).collect();
    let ty: Vec<_> = (n + 1..=2 * n).map(|index| QubitId(index as u64)).collect();
    let ox: Vec<_> = (0..n).map(|index| BitId(index as u64)).collect();
    let oy: Vec<_> = (n..2 * n).map(|index| BitId(index as u64)).collect();
    declare_register(&mut state.out, 0, &tx, &[]);
    declare_register(&mut state.out, 1, &ty, &[]);
    declare_register(&mut state.out, 2, &[], &ox);
    declare_register(&mut state.out, 3, &[], &oy);
    expand_node(
        &graph,
        &mut state,
        graph.root,
        0,
        graph.root_qubits,
        0,
        graph.root_bits,
    );
    state.flush_raw();
    assert!(matches!(state.pending_hmr, PendingHmr::None));
    assert!(state.proof.balanced());
    assert_eq!(state.predicate_blocks, 1284);
    assert_eq!(state.input_ops, summary.output_ops + 3 * state.predicate_blocks);
    assert_eq!(
        state.out.len(),
        summary.output_ops + declarations + state.proof.rewrites as usize + 3 * state.predicate_blocks
    );
    eprintln!(
        "CLEAN_AND_MBU: rewrites={} extra_bits=1 cache_evictions={}",
        state.proof.rewrites,
        state.proof.evictions()
    );
    eprintln!("PREDICATE_MBU: blocks={} conditional_toffoli={} extra_bits=1", state.predicate_blocks, 512 * state.predicate_blocks);
    if std::env::var_os("PAPER2607_KEEP_CONTROL").is_none() {
        eliminate_constant_outer_control(&mut state.out, QubitId(0));
    }
    eprintln!(
        "PAPER2607_HIR: n={n} qubits={} bits={} ops={} toffoli={}",
        graph.root_qubits,
        graph.root_bits,
        state.out.len(),
        summary.toffoli,
    );
    state.out
}

#[cfg(test)]
mod mbu_tests {
    use super::*;
    #[test]
    fn hir_emission_applies_proved_cleanup() {
        let mut state = State::new(4, 0, &[1, 2], &[], true, 0);
        let q = [QubitId(1), QubitId(2), QubitId(3)];
        state.emit_leaf(5, &q, 3, NO_BIT, 0);
        state.emit_leaf(5, &q, 3, NO_BIT, 0);
        state.flush_raw();
        assert_eq!(
            state
                .out
                .iter()
                .filter(|o| o.kind == OperationType::Hmr)
                .count(),
            1
        );
    }
    #[test]
    fn predicate_emitter_full_width_both_measurements() {
        use crate::sim::Simulator;
        use sha3::digest::XofReader;
        struct Outcome(u8);
        impl XofReader for Outcome { fn read(&mut self, b: &mut [u8]) { b.fill(self.0); } }
        let fixture = include_bytes!("predicate_comparator_test.hir");
        let inputs: Vec<_> = (0..513).collect();
        let mut state = State::new(518, 256, &inputs, &[], true, 0);
        let mut reader = Reader { data: fixture, at: 0 };
        assert_eq!(predicate_cleanup(&mut reader, &mut state, 2267, 0, 0), 2053);
        state.flush_raw();
        assert_eq!(reader.at, fixture.len());
        assert_eq!(state.out.len(), 2056);
        assert!(state.proof.balanced());
        for op in &state.out { op.validate(); }
        // Exercise each bit position as the decisive comparison bit, equality,
        // both control values and both measurement outcomes, using the trusted
        // simulator and the actual 256-bit emitted replacement.
        for decisive in 0..256 {
            for order in 0..3 {
                for ctrl in 0..2 {
                    for outcome in [0, 255] {
                        let mut rng = Outcome(outcome);
                        let mut sim = Simulator::new(518, 258, &mut rng);
                        sim.qubits[0] = ctrl;
                        sim.qubits[1+decisive] = u64::from(order != 2);
                        sim.qubits[257+decisive] = u64::from(order != 0);
                        let mut expected = sim.qubits.clone();
                        sim.qubits[514] = ctrl & u64::from(order == 0);
                        sim.apply_iter(state.out.iter());
                        expected[514] = 0;
                        for (got, want) in sim.qubits.iter().zip(expected) { assert_eq!(got & 1, want); }
                        assert_eq!(sim.phase & 1, 0, "bit={decisive} order={order} ctrl={ctrl} m={outcome}");
                    }
                }
            }
        }
    }
}
