//! Exact parent-level half-square replacement for the fixed Q833 HIR.
//!
//! The transform is part of the production path. It runs after the pinned
//! directional-shift transform, extracts byte-identical exact D/H
//! micro-nodes from the incumbent square/inverse-square nodes, creates three
//! serialized factor nodes, and replaces only the exact root calls 2312..2314.
use super::{Reader, MAGIC};
use sha3::{Digest, Sha3_256};

const OLD_ROOT: usize = 2269;
const OLD_NODE_COUNT: usize = 2270;
const DOUBLE_NODE: usize = 2269;
const HALVE_NODE: usize = 2270;
const LOW_FACTOR_NODE: usize = 2271;
const CROSS_FACTOR_NODE: usize = 2272;
const HIGH_FACTOR_NODE: usize = 2273;
const NEW_ROOT: usize = 2274;
const NEW_NODE_COUNT: usize = 2275;

#[derive(Clone, Copy)]
struct Marker {
    ordinal: usize,
    start: usize,
    end: usize,
    source_bit: usize,
}

struct Interval {
    raw: Vec<u8>,
    op_count: usize,
}

fn put_uvar(mut value: usize, out: &mut Vec<u8>) {
    while value >= 128 {
        out.push((value as u8 & 127) | 128);
        value >>= 7;
    }
    out.push(value as u8);
}

fn sha3_hex(data: &[u8]) -> String {
    Sha3_256::digest(data)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn node_bodies(data: &[u8]) -> Vec<&[u8]> {
    assert!(data.starts_with(MAGIC));
    let mut reader = Reader { data, at: MAGIC.len() };
    assert_eq!(reader.uvar(), 1);
    assert_eq!(reader.uvar(), OLD_ROOT);
    assert_eq!(reader.uvar(), OLD_NODE_COUNT);
    let mut bodies = Vec::with_capacity(OLD_NODE_COUNT);
    for _ in 0..OLD_NODE_COUNT {
        let len = reader.uvar();
        let start = reader.at;
        let end = start.checked_add(len).expect("half-square node length overflow");
        bodies.push(data.get(start..end).expect("truncated half-square source node"));
        reader.at = end;
    }
    assert_eq!(reader.at, data.len());
    bodies
}

fn copy_markers(body: &[u8], node_id: usize) -> Vec<Marker> {
    let mut reader = Reader { data: body, at: 0 };
    let qlen = reader.uvar();
    let clen = reader.uvar();
    let op_count = reader.uvar();
    assert_eq!((qlen, clen), (518, 256));
    let mut markers = Vec::with_capacity(512);
    for ordinal in 0..op_count {
        let start = reader.at;
        let tag = reader.byte();
        let condition_width = reader.uvar();
        let expected = reader.uvar();
        for _ in 0..condition_width {
            assert!(reader.uvar() < clen);
        }
        if tag == 11 {
            assert!(reader.uvar() < node_id);
            let nq = reader.uvar();
            for _ in 0..nq {
                assert!(reader.uvar() < qlen);
            }
            let nc = reader.uvar();
            for _ in 0..nc {
                assert!(reader.uvar() < clen);
            }
        } else {
            let nq = reader.uvar();
            assert!(nq <= 3);
            let mut qargs = [usize::MAX; 3];
            for q in qargs.iter_mut().take(nq) {
                *q = reader.uvar();
                assert!(*q < qlen);
            }
            let nc = reader.uvar();
            assert!(nc <= 1);
            for _ in 0..nc {
                assert!(reader.uvar() < clen);
            }
            if tag == 3
                && condition_width == 0
                && expected == 1
                && nq == 2
                && nc == 0
                && qargs[0] < 256
                && qargs[1] == 512
            {
                markers.push(Marker {
                    ordinal,
                    start,
                    end: reader.at,
                    source_bit: qargs[0],
                });
            }
        }
    }
    assert_eq!(reader.at, body.len());
    markers
}

fn extract_interval(
    body: &[u8],
    node_id: usize,
    source_bits: impl Iterator<Item = usize>,
    expected_ops: usize,
    expected_bytes: usize,
    expected_sha3: &str,
) -> Interval {
    let markers = copy_markers(body, node_id);
    assert_eq!(markers.len(), 512);
    let expected: Vec<_> = source_bits.flat_map(|bit| [bit, bit]).collect();
    assert_eq!(markers.iter().map(|marker| marker.source_bit).collect::<Vec<_>>(), expected);
    for row in 0..256 {
        assert!(markers[2 * row].ordinal + 1 < markers[2 * row + 1].ordinal);
    }
    let op_count = markers[2].ordinal - markers[1].ordinal - 1;
    let raw = body[markers[1].end..markers[2].start].to_vec();
    for row in 0..255 {
        let start = markers[2 * row + 1].end;
        let end = markers[2 * row + 2].start;
        assert_eq!(markers[2 * row + 2].ordinal - markers[2 * row + 1].ordinal - 1, op_count);
        assert_eq!(&body[start..end], raw.as_slice(), "non-identical shift row {row}");
    }
    assert_eq!(op_count, expected_ops);
    assert_eq!(raw.len(), expected_bytes);
    assert_eq!(sha3_hex(&raw), expected_sha3);
    Interval { raw, op_count }
}

struct Body {
    records: Vec<u8>,
    count: usize,
}

impl Body {
    fn new(capacity: usize) -> Self {
        Self { records: Vec::with_capacity(capacity), count: 0 }
    }

    fn leaf(&mut self, tag: u8, qargs: &[usize]) {
        assert!(matches!(tag, 3 | 5));
        self.records.push(tag);
        put_uvar(0, &mut self.records);
        put_uvar(1, &mut self.records);
        put_uvar(qargs.len(), &mut self.records);
        for &q in qargs {
            put_uvar(q, &mut self.records);
        }
        put_uvar(0, &mut self.records);
        self.count += 1;
    }

    fn cx(&mut self, control: usize, target: usize) {
        self.leaf(3, &[control, target]);
    }

    fn ccx(&mut self, c1: usize, c2: usize, target: usize) {
        assert!(c1 != c2 && c1 != target && c2 != target);
        self.leaf(5, &[c1, c2, target]);
    }

    fn call(&mut self, child: usize, qmap: &[usize], cmap: &[usize]) {
        self.records.push(11);
        put_uvar(0, &mut self.records);
        put_uvar(1, &mut self.records);
        put_uvar(child, &mut self.records);
        put_uvar(qmap.len(), &mut self.records);
        for &q in qmap {
            put_uvar(q, &mut self.records);
        }
        put_uvar(cmap.len(), &mut self.records);
        for &c in cmap {
            put_uvar(c, &mut self.records);
        }
        self.count += 1;
    }

    fn finish(self, qlen: usize, clen: usize) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.records.len() + 16);
        put_uvar(qlen, &mut out);
        put_uvar(clen, &mut out);
        put_uvar(self.count, &mut out);
        out.extend_from_slice(&self.records);
        out
    }
}

fn interval_body(interval: &Interval) -> Vec<u8> {
    let mut out = Vec::with_capacity(interval.raw.len() + 16);
    put_uvar(518, &mut out);
    put_uvar(256, &mut out);
    put_uvar(interval.op_count, &mut out);
    out.extend_from_slice(&interval.raw);
    out
}

fn cadd_with_flag(body: &mut Body, control: usize, addend: &[usize], acc: &[usize], carry: usize, flag: usize) {
    assert_eq!(addend.len(), acc.len());
    assert!(!acc.is_empty());
    for (&a, &b) in addend.iter().zip(acc) {
        body.cx(carry, a);
        body.cx(carry, b);
        body.ccx(b, a, carry);
    }
    body.ccx(control, carry, flag);
    for (&a, &b) in addend.iter().zip(acc).rev() {
        body.ccx(b, a, carry);
        body.cx(carry, b);
        body.ccx(control, a, b);
        body.cx(carry, a);
    }
}

fn csub_with_flag(body: &mut Body, control: usize, addend: &[usize], acc: &[usize], carry: usize, flag: usize) {
    assert_eq!(addend.len(), acc.len());
    assert!(!acc.is_empty());
    for (&a, &b) in addend.iter().zip(acc) {
        body.cx(carry, a);
        body.ccx(control, a, b);
        body.cx(carry, b);
        body.ccx(b, a, carry);
    }
    body.ccx(control, carry, flag);
    for (&a, &b) in addend.iter().zip(acc).rev() {
        body.ccx(b, a, carry);
        body.cx(carry, b);
        body.cx(carry, a);
    }
}

fn multiply(body: &mut Body, left: &[usize], right: &[usize], inverse: bool) {
    assert_eq!(left.len(), 128);
    assert_eq!(right.len(), 128);
    let product: Vec<_> = (513..=768).collect();
    for row in 0..128 {
        let i = if inverse { 127 - row } else { row };
        let control = left[i];
        let acc = &product[i..i + 128];
        let flag = product[i + 128];
        if inverse {
            csub_with_flag(body, control, right, acc, 769, flag);
        } else {
            cadd_with_flag(body, control, right, acc, 769, flag);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NativeGate {
    Cx(usize, usize),
    Ccx(usize, usize, usize),
}

#[derive(Default)]
struct NativeEmitter {
    gates: Vec<NativeGate>,
}

impl NativeEmitter {
    fn cx(&mut self, control: usize, target: usize) {
        assert_ne!(control, target);
        self.gates.push(NativeGate::Cx(control, target));
    }

    fn ccx(&mut self, a: usize, b: usize, target: usize) {
        assert!(a != b && a != target && b != target);
        self.gates.push(NativeGate::Ccx(a, b, target));
    }

    fn maj(&mut self, addend: usize, acc: usize, previous: usize) {
        self.cx(addend, acc);
        self.cx(addend, previous);
        self.ccx(previous, acc, addend);
    }

    fn uma(&mut self, addend: usize, acc: usize, previous: usize) {
        self.ccx(previous, acc, addend);
        self.cx(addend, previous);
        self.cx(previous, acc);
    }

    fn add_mod_forward(
        &mut self,
        lower: &[usize],
        top: Option<usize>,
        acc: &[usize],
        helper: usize,
    ) {
        assert!(!lower.is_empty());
        assert_eq!(acc.len(), lower.len() + 1);
        for i in 0..lower.len() {
            let previous = if i == 0 { helper } else { lower[i - 1] };
            self.maj(lower[i], acc[i], previous);
        }
        if let Some(top) = top {
            self.cx(top, acc[acc.len() - 1]);
        }
        self.cx(lower[lower.len() - 1], acc[acc.len() - 1]);
        for i in (0..lower.len()).rev() {
            let previous = if i == 0 { helper } else { lower[i - 1] };
            self.uma(lower[i], acc[i], previous);
        }
    }

    fn sub_mod(
        &mut self,
        lower: &[usize],
        top: Option<usize>,
        acc: &[usize],
        helper: usize,
    ) {
        let start = self.gates.len();
        self.add_mod_forward(lower, top, acc, helper);
        self.gates[start..].reverse();
    }

    fn square_compute(&mut self, input: &[usize], product: &[usize], s0: usize, s1: usize) {
        assert_square_layout(input, product, s0, s1);
        let n = input.len();
        self.sub_mod(input, None, &product[..n + 1], s0);
        for i in 0..n - 1 {
            self.cx(product[n + i], product[n + i + 1]);
            for j in i + 1..n {
                self.cx(input[i], input[j]);
            }
            self.cx(input[i], s1);
            let mut lower = input[i + 1..].to_vec();
            lower.push(s1);
            self.sub_mod(
                &lower,
                Some(input[i]),
                &product[2 * i + 1..n + i + 2],
                s0,
            );
            self.cx(input[i], s1);
            for j in (i + 1..n).rev() {
                self.cx(input[i], input[j]);
            }
        }
        self.cx(input[n - 1], product[2 * n - 1]);
    }
}

fn assert_square_layout(input: &[usize], product: &[usize], s0: usize, s1: usize) {
    assert!(square_layout_is_valid(input, product, s0, s1));
}

fn square_layout_is_valid(input: &[usize], product: &[usize], s0: usize, s1: usize) -> bool {
    if input.is_empty() || product.len() != 2 * input.len() {
        return false;
    }
    let mut all: Vec<_> = input.iter().chain(product).copied().chain([s0, s1]).collect();
    let original_len = all.len();
    all.sort_unstable();
    all.dedup();
    all.len() == original_len
}

fn ci_square_gates(
    input: &[usize],
    product: &[usize],
    s0: usize,
    s1: usize,
    inverse: bool,
) -> Vec<NativeGate> {
    let mut emitter = NativeEmitter::default();
    emitter.square_compute(input, product, s0, s1);
    if inverse {
        emitter.gates.reverse();
    }
    emitter.gates
}

fn ci_square(body: &mut Body, input: &[usize], inverse: bool) {
    let product: Vec<_> = (513..=768).collect();
    for gate in ci_square_gates(input, &product, 769, 770, inverse) {
        match gate {
            NativeGate::Cx(control, target) => body.cx(control, target),
            NativeGate::Ccx(a, b, target) => body.ccx(a, b, target),
        }
    }
}

fn double_halve_map() -> Vec<usize> {
    (257..=512)
        .chain(513..=768)
        .chain([773, 769, 770, 771, 772, 774])
        .collect()
}

fn csub_map() -> Vec<usize> {
    [0].into_iter()
        .chain(513..=768)
        .chain(1..=256)
        .chain(769..=773)
        .collect()
}

fn factor_body(left: &[usize], right: &[usize], square: bool, shifts: usize) -> Vec<u8> {
    let mut body = Body::new(8_000_000);
    if square {
        ci_square(&mut body, left, false);
    } else {
        multiply(&mut body, left, right, false);
    }
    let dh_qmap = double_halve_map();
    let m_arith: Vec<_> = (1024..=1279).collect();
    for _ in 0..shifts {
        body.call(DOUBLE_NODE, &dh_qmap, &m_arith);
    }
    body.call(2258, &csub_map(), &m_arith);
    for _ in 0..shifts {
        body.call(HALVE_NODE, &dh_qmap, &m_arith);
    }
    if square {
        ci_square(&mut body, left, true);
    } else {
        multiply(&mut body, left, right, true);
    }
    body.finish(835, 1280)
}

struct CallRecord {
    child: usize,
    condition_width: usize,
    expected: usize,
    condition_map: Vec<usize>,
    qmap: Vec<usize>,
    cmap: Vec<usize>,
}

fn read_record(reader: &mut Reader<'_>, qlen: usize, clen: usize) -> Option<CallRecord> {
    let tag = reader.byte();
    let condition_width = reader.uvar();
    let expected = reader.uvar();
    let condition_map: Vec<_> = (0..condition_width).map(|_| reader.uvar()).collect();
    if tag == 11 {
        let child = reader.uvar();
        let nq = reader.uvar();
        let qmap: Vec<_> = (0..nq).map(|_| reader.uvar()).collect();
        let nc = reader.uvar();
        let cmap: Vec<_> = (0..nc).map(|_| reader.uvar()).collect();
        assert!(qmap.iter().all(|&q| q < qlen));
        assert!(cmap.iter().all(|&c| c < clen));
        Some(CallRecord { child, condition_width, expected, condition_map, qmap, cmap })
    } else {
        let nq = reader.uvar();
        for _ in 0..nq {
            assert!(reader.uvar() < qlen);
        }
        let nc = reader.uvar();
        for _ in 0..nc {
            assert!(reader.uvar() < clen);
        }
        None
    }
}

fn assert_call(call: &CallRecord, child: usize, qmap: &[usize], cmap: &[usize]) {
    assert_eq!(call.child, child);
    assert_eq!((call.condition_width, call.expected), (0, 1));
    assert!(call.condition_map.is_empty());
    assert_eq!(call.qmap, qmap);
    assert_eq!(call.cmap, cmap);
}

fn root_body(source: &[u8]) -> Vec<u8> {
    let mut reader = Reader { data: source, at: 0 };
    let qlen = reader.uvar();
    let clen = reader.uvar();
    let op_count = reader.uvar();
    assert_eq!((qlen, clen, op_count), (835, 1280, 5143));
    let header_end = reader.at;
    let square_map: Vec<_> = (257..=774).collect();
    let subtract_map = csub_map();
    let arithmetic_cbits: Vec<_> = (1024..=1279).collect();
    let identity_q: Vec<_> = (0..835).collect();
    let identity_c: Vec<_> = (0..1280).collect();
    let replacement_children = [LOW_FACTOR_NODE, CROSS_FACTOR_NODE, HIGH_FACTOR_NODE];
    let mut out = Vec::with_capacity(source.len() + 20_000);
    out.extend_from_slice(&source[..header_end]);
    for ordinal in 0..op_count {
        let start = reader.at;
        let call = read_record(&mut reader, qlen, clen);
        if (2312..=2314).contains(&ordinal) {
            let call = call.as_ref().expect("square-minus atomic interval must contain calls");
            match ordinal {
                2312 => assert_call(call, 2265, &square_map, &arithmetic_cbits),
                2313 => assert_call(call, 2258, &subtract_map, &arithmetic_cbits),
                2314 => assert_call(call, 2266, &square_map, &arithmetic_cbits),
                _ => unreachable!(),
            }
            let mut replacement = Body::new(8_000);
            replacement.call(replacement_children[ordinal - 2312], &identity_q, &identity_c);
            out.extend_from_slice(&replacement.records);
        } else {
            out.extend_from_slice(&source[start..reader.at]);
        }
    }
    assert_eq!(reader.at, source.len());
    out
}

pub(super) fn replace(data: &[u8]) -> Vec<u8> {
    let bodies = node_bodies(data);
    let double = extract_interval(
        bodies[2265],
        2265,
        (0..256).rev(),
        8308,
        75_624,
        "a2100b5a65c338bc0897da444d308cdbc0122ca5c4e360974d7c63ea92d62ea2",
    );
    let halve = extract_interval(
        bodies[2266],
        2266,
        0..256,
        10_729,
        97_066,
        "87c9a42d9b413be809dde34e84380b8f52032d6c28fd5a632869761ff0092af8",
    );
    let low: Vec<_> = (257..=384).collect();
    let high: Vec<_> = (385..=512).collect();
    let new_nodes = [
        interval_body(&double),
        interval_body(&halve),
        factor_body(&low, &low, true, 0),
        factor_body(&high, &low, false, 129),
        factor_body(&high, &high, true, 256),
    ];
    let rewritten_root = root_body(bodies[OLD_ROOT]);

    let total_new_bytes: usize = new_nodes.iter().map(Vec::len).sum();
    let mut out = Vec::with_capacity(data.len() + total_new_bytes + rewritten_root.len());
    out.extend_from_slice(MAGIC);
    put_uvar(1, &mut out);
    put_uvar(NEW_ROOT, &mut out);
    put_uvar(NEW_NODE_COUNT, &mut out);
    for body in &bodies[..OLD_ROOT] {
        put_uvar(body.len(), &mut out);
        out.extend_from_slice(body);
    }
    for body in &new_nodes {
        put_uvar(body.len(), &mut out);
        out.extend_from_slice(body);
    }
    put_uvar(rewritten_root.len(), &mut out);
    out.extend_from_slice(&rewritten_root);
    assert_eq!(new_nodes.len(), 5);
    eprintln!("HALF_SQUARE_FOLD: exact extracted nodes D={DOUBLE_NODE} H={HALVE_NODE} factors={LOW_FACTOR_NODE},{CROSS_FACTOR_NODE},{HIGH_FACTOR_NODE} root={NEW_ROOT}");
    out
}

pub(super) fn maybe_replace(data: Vec<u8>) -> Vec<u8> {
    replace(&data)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{Op, OperationType, QubitId};
    use crate::point_add::paper2607_hir::{
        expand_node, parse_graph, shift_controls, PendingHmr, State, COMPRESSED_HIR,
    };
    use crate::sim::Simulator;
    use ruint::aliases::U256;
    use sha3::digest::XofReader;

    struct ZeroXof;

    impl XofReader for ZeroXof {
        fn read(&mut self, out: &mut [u8]) {
            out.fill(0);
        }
    }

    fn native_ops(gates: &[NativeGate]) -> Vec<Op> {
        gates.iter().map(|gate| {
            let mut op = Op::empty();
            match *gate {
                NativeGate::Cx(control, target) => {
                    op.kind = OperationType::CX;
                    op.q_control1 = QubitId(control as u64);
                    op.q_target = QubitId(target as u64);
                }
                NativeGate::Ccx(a, b, target) => {
                    op.kind = OperationType::CCX;
                    op.q_control2 = QubitId(a as u64);
                    op.q_control1 = QubitId(b as u64);
                    op.q_target = QubitId(target as u64);
                }
            }
            op.validate();
            op
        }).collect()
    }

    fn count_gate(gates: &[NativeGate], ccx: bool) -> usize {
        gates.iter().filter(|gate| matches!((gate, ccx),
            (NativeGate::Ccx(..), true) | (NativeGate::Cx(..), false))).count()
    }

    fn set_small(sim: &mut Simulator<'_, ZeroXof>, start: usize, n: usize, value: u64) {
        for bit in 0..n {
            sim.qubits[start + bit] = (value >> bit) & 1;
        }
    }

    fn get_small(sim: &Simulator<'_, ZeroXof>, start: usize, n: usize) -> u64 {
        (0..n).fold(0, |value, bit| value | ((sim.qubits[start + bit] & 1) << bit))
    }

    fn set_u256_all_lanes(sim: &mut Simulator<'_, PatternXof>, start: usize, value: U256) {
        for bit in 0..256 {
            sim.qubits[start + bit] = if value.bit(bit) { u64::MAX } else { 0 };
        }
    }

    fn assert_u256_all_lanes(
        sim: &Simulator<'_, PatternXof>,
        start: usize,
        value: U256,
        context: &str,
    ) {
        for bit in 0..256 {
            assert_eq!(
                sim.qubits[start + bit],
                if value.bit(bit) { u64::MAX } else { 0 },
                "{context} bit {bit}",
            );
        }
    }

    struct PatternXof {
        seed: [u8; 8],
        reads: u64,
    }

    impl PatternXof {
        fn new(seed: [u8; 8]) -> Self {
            Self { seed, reads: 0 }
        }
    }

    impl XofReader for PatternXof {
        fn read(&mut self, out: &mut [u8]) {
            let fixed = self.seed.iter().all(|&byte| byte == self.seed[0]);
            let word = if fixed {
                u64::from_le_bytes(self.seed)
            } else {
                u64::from_le_bytes(self.seed)
                    .rotate_left(((self.reads * 17) & 63) as u32)
                    ^ self.reads.wrapping_mul(0x9e37_79b9_7f4a_7c15)
            };
            let bytes = word.to_le_bytes();
            for (index, byte) in out.iter_mut().enumerate() {
                *byte = bytes[index % bytes.len()];
            }
            self.reads += 1;
        }
    }

    fn expanded_factor_ops(graph: &crate::point_add::paper2607_hir::Graph<'_>, node: usize) -> Vec<Op> {
        let qinputs: Vec<_> = (0..=512).collect();
        let cinputs: Vec<_> = (0..512).collect();
        let mut state = State::new(
            835,
            1280,
            &qinputs,
            &cinputs,
            true,
            graph.summaries[node].output_ops + 4096,
        );
        state.retention.enabled = false;
        state.family24_enabled = false;
        state.family36_enabled = false;
        state.family63_enabled = false;
        state.motif_enabled = false;
        expand_node(graph, &mut state, node, 0, 835, 0, 1280);
        state.flush_raw();
        assert!(matches!(state.pending_hmr, PendingHmr::None));
        assert!(state.proof.balanced());
        state.assert_accounting(graph.summaries[node].output_ops, 0);

        let mut measured = vec![false; 1282];
        for op in &state.out {
            if op.kind == OperationType::Hmr {
                assert_ne!(op.c_target, crate::circuit::NO_BIT);
                measured[op.c_target.0 as usize] = true;
            }
            if op.c_condition != crate::circuit::NO_BIT {
                assert!(measured[op.c_condition.0 as usize],
                    "factor node {node} consumes classical bit {} before a local measurement",
                    op.c_condition.0);
            }
            for q in [op.q_control2, op.q_control1, op.q_target] {
                if q != crate::circuit::NO_QUBIT {
                    assert!(q.0 <= 774, "factor node {node} escapes declared support at q{}", q.0);
                }
            }
        }
        state.out
    }

    fn doubled_mod(mut value: U256, shifts: usize, p: U256) -> U256 {
        for _ in 0..shifts {
            value = value.add_mod(value, p);
        }
        value
    }

    #[test]
    fn integrated_ci_square_gate_value_cleanup_alias_and_support() {
        let mut cases = 0usize;
        for n in 1..=7 {
            let input: Vec<_> = (0..n).collect();
            let product: Vec<_> = (n..3 * n).collect();
            let s0 = 3 * n;
            let s1 = 3 * n + 1;
            let forward = ci_square_gates(&input, &product, s0, s1, false);
            let inverse = ci_square_gates(&input, &product, s0, s1, true);
            assert_eq!(count_gate(&forward, true), n * (n + 3) - 2);
            assert_eq!(count_gate(&forward, false), 3 * n * n + 10 * n - 7);
            assert_eq!(inverse, forward.iter().copied().rev().collect::<Vec<_>>());
            let forward_ops = native_ops(&forward);
            let inverse_ops = native_ops(&inverse);
            for x in 0..1u64 << n {
                let mut rng = ZeroXof;
                let mut sim = Simulator::new(3 * n + 2, 1, &mut rng);
                set_small(&mut sim, 0, n, x);
                sim.apply_iter(forward_ops.iter());
                assert_eq!(get_small(&sim, 0, n), x);
                assert_eq!(get_small(&sim, n, 2 * n), x * x);
                assert_eq!((sim.qubits[s0], sim.qubits[s1], sim.phase), (0, 0, 0));
                sim.apply_iter(inverse_ops.iter());
                assert_eq!(get_small(&sim, 0, n), x);
                assert_eq!(get_small(&sim, n, 2 * n), 0);
                assert_eq!((sim.qubits[s0], sim.qubits[s1], sim.phase), (0, 0, 0));
                cases += 1;
            }
        }
        assert_eq!(cases, 254);

        let rejected = [
            (vec![0, 1], vec![2, 3, 4, 5], 0, 7),
            (vec![0, 1], vec![2, 3, 4, 5], 2, 7),
            (vec![0, 1], vec![2, 3, 4, 5], 6, 6),
            (vec![0, 1], vec![1, 3, 4, 5], 6, 7),
        ];
        for (input, product, s0, s1) in rejected {
            assert!(!square_layout_is_valid(&input, &product, s0, s1));
        }

        let product: Vec<_> = (513..=768).collect();
        for input in [(257..=384).collect::<Vec<_>>(), (385..=512).collect()] {
            let forward = ci_square_gates(&input, &product, 769, 770, false);
            let inverse = ci_square_gates(&input, &product, 769, 770, true);
            assert_eq!((count_gate(&forward, true), count_gate(&forward, false)),
                (16_766, 50_425));
            assert_eq!((count_gate(&inverse, true), count_gate(&inverse, false)),
                (16_766, 50_425));
            let mut allowed = input.clone();
            allowed.extend_from_slice(&product);
            allowed.extend([769, 770]);
            allowed.sort_unstable();
            for gate in forward.iter().chain(&inverse) {
                let wires: Vec<_> = match *gate {
                    NativeGate::Cx(a, b) => vec![a, b],
                    NativeGate::Ccx(a, b, c) => vec![a, b, c],
                };
                assert!(wires.into_iter().all(|wire| allowed.binary_search(&wire).is_ok()));
            }
        }
        println!("HALF_SQUARE_CI_INTEGRATED widths=1..7 cases=254 n128_forward_ccx=16766 n128_forward_cx=50425 n128_roundtrip_ccx=33532 n128_roundtrip_cx=100850 support=selected_half,A,S0,S1 alias_rejection=pass cleanup=pass phase=exact");
    }

    #[test]
    fn complete_factor_nodes_modulus_adjacency_cleanup_and_classical_provenance() {
        let p = U256::from_str_radix(
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
            16,
        ).unwrap();
        let limb_max = U256::from(u128::MAX);
        assert!(limb_max.wrapping_mul(limb_max) < p);

        let original = zstd::stream::decode_all(COMPRESSED_HIR).unwrap();
        let shifted = shift_controls::replace(&original);
        let transformed = replace(&shifted);
        let graph = parse_graph(&transformed);
        let patterns = [
            [0u8; 8],
            [0xffu8; 8],
            [0xa5, 0x5a, 0xc3, 0x3c, 0x96, 0x69, 0xf0, 0x0f],
        ];
        let cases = [
            (0u64, U256::ZERO, U256::ZERO, U256::ZERO),
            (1, U256::from(1), U256::from(1), p.wrapping_sub(U256::from(1))),
            (1, limb_max, limb_max, U256::ZERO),
            (1, U256::from(0x0123_4567_89ab_cdefu64),
                U256::from(0xfedc_ba98_7654_3210u64),
                U256::from(0x55aa_aa55_5aa5_a55au64)),
            (0, limb_max, limb_max, p.wrapping_sub(U256::from(2))),
        ];
        let factors = [
            (LOW_FACTOR_NODE, 0usize, 0usize),
            (CROSS_FACTOR_NODE, 1usize, 129usize),
            (HIGH_FACTOR_NODE, 2usize, 256usize),
        ];
        let mut checked = 0usize;
        for (node, kind, shifts) in factors {
            let ops = expanded_factor_ops(&graph, node);
            for pattern in patterns {
                for (control, low, high, output) in cases {
                    let factor = match kind {
                        0 => low.wrapping_mul(low),
                        1 => low.wrapping_mul(high),
                        2 => high.wrapping_mul(high),
                        _ => unreachable!(),
                    };
                    let term = doubled_mod(factor, shifts, p);
                    let expected = if control == 0 {
                        output
                    } else if output >= term {
                        output.wrapping_sub(term)
                    } else {
                        p.wrapping_sub(term.wrapping_sub(output))
                    };
                    let y = low | (high << 128);
                    let mut rng = PatternXof::new(pattern);
                    let mut sim = Simulator::new(835, 1282, &mut rng);
                    let control_mask = if control == 0 { 0 } else { u64::MAX };
                    sim.qubits[0] = control_mask;
                    set_u256_all_lanes(&mut sim, 1, output);
                    set_u256_all_lanes(&mut sim, 257, y);
                    sim.apply_iter(ops.iter());
                    assert_eq!(sim.qubits[0], control_mask, "node {node} control");
                    assert_u256_all_lanes(&sim, 1, expected, &format!("node {node} modular output"));
                    assert_u256_all_lanes(&sim, 257, y, &format!("node {node} input preservation"));
                    assert_u256_all_lanes(&sim, 513, U256::ZERO, &format!("node {node} product cleanup"));
                    assert!(sim.qubits[769..=774].iter().all(|&bit| bit == 0),
                        "node {node} scratch cleanup");
                    assert_eq!(sim.phase, 0, "node {node} exact phase across all simulator lanes");
                    checked += 64;
                }
            }
        }
        assert_eq!(checked, 2_880);
        println!("HALF_SQUARE_FACTOR_NODES factors=3 input_tuples=5 measurement_streams=3 executions=45 packed_lane_executions=2880 streams=fixed0,fixed1,varying modulus=secp256k1 max_limb_square_below_p=pass local_measurement_provenance=pass support=q0..q774 output=exact_modular_subtract input=preserved product=clean scratch=clean phase=exact");
    }

    #[test]
    fn production_transform_has_exact_atomic_raw_counts() {
        let original = zstd::stream::decode_all(COMPRESSED_HIR).unwrap();
        let shifted = shift_controls::replace(&original);
        let transformed = replace(&shifted);
        let graph = parse_graph(&transformed);
        assert_eq!((graph.root, graph.nodes.len(), graph.root_qubits, graph.root_bits),
            (NEW_ROOT, NEW_NODE_COUNT, 835, 1280));
        assert_eq!((graph.summaries[DOUBLE_NODE].toffoli, graph.summaries[DOUBLE_NODE].output_ops),
            (1_531, 9_330));
        assert_eq!((graph.summaries[HALVE_NODE].toffoli, graph.summaries[HALVE_NODE].output_ops),
            (1_531, 11_751));
        assert_eq!(graph.summaries[LOW_FACTOR_NODE].toffoli, 36_345);
        assert_eq!(graph.summaries[CROSS_FACTOR_NODE].toffoli, 496_371);
        assert_eq!(graph.summaries[HIGH_FACTOR_NODE].toffoli, 820_217);
        assert_eq!(graph.summaries[LOW_FACTOR_NODE].toffoli
            + graph.summaries[CROSS_FACTOR_NODE].toffoli
            + graph.summaries[HIGH_FACTOR_NODE].toffoli, 1_352_933);
        assert_eq!(graph.summaries[LOW_FACTOR_NODE].output_ops, 149_211);
        assert_eq!(graph.summaries[CROSS_FACTOR_NODE].output_ops, 2_963_910);
        assert_eq!(graph.summaries[HIGH_FACTOR_NODE].output_ops, 5_545_947);
        assert_eq!(graph.summaries[graph.root].toffoli, 69_183_152);
        assert_eq!(graph.summaries[graph.root].output_ops, 397_712_522);
        assert_eq!(transformed.len(), 1_281_656_352);
        assert_eq!(sha3_hex(&transformed),
            "1403b2684340ce98ff90ec9939f082c7832e785331b4a8b58aa32c0c932b4dd8");
        for (node_id, direct_ops) in [
            (LOW_FACTOR_NODE, 134_383),
            (CROSS_FACTOR_NODE, 229_891),
            (HIGH_FACTOR_NODE, 134_895),
        ] {
            let node = graph.nodes[node_id];
            let mut direct = Reader { data: &graph.data[node.start..node.end], at: 0 };
            assert_eq!((direct.uvar(), direct.uvar(), direct.uvar()), (835, 1280, direct_ops));
        }

        let root_node = graph.nodes[graph.root];
        let mut reader = Reader { data: &graph.data[root_node.start..root_node.end], at: 0 };
        assert_eq!((reader.uvar(), reader.uvar(), reader.uvar()), (835, 1280, 5143));
        let identity_q: Vec<_> = (0..835).collect();
        let identity_c: Vec<_> = (0..1280).collect();
        let mut replacement_children = Vec::new();
        for ordinal in 0..5143 {
            let call = read_record(&mut reader, 835, 1280);
            if (2312..=2314).contains(&ordinal) {
                let call = call.unwrap();
                assert_eq!((call.condition_width, call.expected), (0, 1));
                assert!(call.condition_map.is_empty());
                assert_eq!(call.qmap, identity_q);
                assert_eq!(call.cmap, identity_c);
                replacement_children.push(call.child);
            }
        }
        assert_eq!(reader.at, reader.data.len());
        assert_eq!(replacement_children,
            [LOW_FACTOR_NODE, CROSS_FACTOR_NODE, HIGH_FACTOR_NODE]);
        println!("HALF_SQUARE_PRODUCTION_HIR root={} nodes={} root_t={} root_ops={} factors={},{},{} factor_t={},{},{} archive_bytes={} archive_sha3_256={} atomic_ops=2312,2313,2314 status=pass",
            graph.root, graph.nodes.len(), graph.summaries[graph.root].toffoli,
            graph.summaries[graph.root].output_ops,
            LOW_FACTOR_NODE, CROSS_FACTOR_NODE, HIGH_FACTOR_NODE,
            graph.summaries[LOW_FACTOR_NODE].toffoli,
            graph.summaries[CROSS_FACTOR_NODE].toffoli,
            graph.summaries[HIGH_FACTOR_NODE].toffoli,
            transformed.len(), sha3_hex(&transformed));
    }
}
