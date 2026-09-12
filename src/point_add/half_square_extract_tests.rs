use super::{expand_node, parse_graph, shift_controls, Graph, Node, PendingHmr, Reader, State, Summary, COMPRESSED_HIR};
use crate::circuit::{BitId, Op, OperationType, QubitId, NO_BIT, NO_QUBIT};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::digest::XofReader;
use sha3::{Digest, Sha3_256};

#[derive(Clone, Copy, Debug)]
struct Marker {
    ordinal: usize,
    start: usize,
    end: usize,
    source_bit: usize,
}

#[derive(Clone)]
struct RepeatedInterval {
    raw: Vec<u8>,
    op_count: usize,
    instances: usize,
    first_op: usize,
    end_op: usize,
    sha3_256: String,
    summary: Summary,
}

fn scan_copy_markers(graph: &Graph<'_>, node_id: usize) -> (usize, usize, Vec<Marker>) {
    let node = graph.nodes[node_id];
    let body = &graph.data[node.start..node.end];
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
            let child = reader.uvar();
            assert!(child < node_id);
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
    (qlen, clen, markers)
}

fn assert_atomic_parent_triple(graph: &Graph<'_>) {
    let node = graph.nodes[2269];
    let mut reader = Reader { data: &graph.data[node.start..node.end], at: 0 };
    assert_eq!((reader.uvar(), reader.uvar()), (835, 1280));
    let op_count = reader.uvar();
    assert!(op_count > 2314);
    let mut found = Vec::with_capacity(3);
    for ordinal in 0..op_count {
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
            if (2312..=2314).contains(&ordinal) {
                found.push((ordinal, child, condition_width, expected, condition_map, qmap, cmap));
            }
        } else {
            let nq = reader.uvar();
            for _ in 0..nq {
                reader.uvar();
            }
            let nc = reader.uvar();
            for _ in 0..nc {
                reader.uvar();
            }
            assert!(!(2312..=2314).contains(&ordinal), "atomic interval contains a leaf");
        }
    }
    assert_eq!(reader.at, reader.data.len());
    assert_eq!(found.len(), 3);
    let square_map: Vec<_> = (257..=774).collect();
    let csub_map: Vec<_> = [0].into_iter()
        .chain(513..=768)
        .chain(1..=256)
        .chain(769..=773)
        .collect();
    let arithmetic_cbits: Vec<_> = (1024..=1279).collect();
    for (index, expected_child, expected_map) in [
        (0usize, 2265usize, &square_map),
        (1, 2258, &csub_map),
        (2, 2266, &square_map),
    ] {
        let (ordinal, child, width, expected, condition_map, qmap, cmap) = &found[index];
        assert_eq!(*ordinal, 2312 + index);
        assert_eq!(*child, expected_child);
        assert_eq!((*width, *expected), (0, 1));
        assert!(condition_map.is_empty());
        assert_eq!(qmap, expected_map);
        assert_eq!(cmap, &arithmetic_cbits);
    }
}

fn summarize_raw(graph: &Graph<'_>, raw: &[u8], op_count: usize) -> Summary {
    let mut reader = Reader { data: raw, at: 0 };
    let mut summary = Summary::default();
    for _ in 0..op_count {
        let tag = reader.byte();
        let condition_width = reader.uvar();
        let expected = reader.uvar();
        assert!(condition_width < usize::BITS as usize);
        assert!(condition_width == 0 || expected < (1usize << condition_width));
        let zeros = if condition_width == 0 {
            assert_eq!(expected, 1);
            0
        } else {
            condition_width - expected.count_ones() as usize
        };
        summary.output_ops += 2 * condition_width + 2 * zeros;
        for _ in 0..condition_width {
            reader.uvar();
        }
        if tag == 11 {
            let child = reader.uvar();
            summary.add(graph.summaries[child]);
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
                _ => panic!("unknown interval tag {tag}"),
            }
        }
        let nq = reader.uvar();
        for _ in 0..nq {
            reader.uvar();
        }
        let nc = reader.uvar();
        for _ in 0..nc {
            reader.uvar();
        }
    }
    assert_eq!(reader.at, raw.len());
    summary
}

fn sha3_hex(data: &[u8]) -> String {
    Sha3_256::digest(data)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn repeated_shift_interval(
    graph: &Graph<'_>,
    node_id: usize,
    source_bits: impl Iterator<Item = usize>,
) -> RepeatedInterval {
    let node = graph.nodes[node_id];
    let body = &graph.data[node.start..node.end];
    let (_, _, markers) = scan_copy_markers(graph, node_id);
    assert_eq!(markers.len(), 512);
    let expected: Vec<_> = source_bits.flat_map(|bit| [bit, bit]).collect();
    assert_eq!(markers.iter().map(|marker| marker.source_bit).collect::<Vec<_>>(), expected);
    for row in 0..256 {
        assert!(markers[2 * row].ordinal + 1 < markers[2 * row + 1].ordinal);
    }

    let first_start = markers[1].end;
    let first_end = markers[2].start;
    let first_op = markers[1].ordinal + 1;
    let end_op = markers[2].ordinal;
    let op_count = end_op - first_op;
    let raw = body[first_start..first_end].to_vec();
    assert!(!raw.is_empty());
    for row in 0..255 {
        let start = markers[2 * row + 1].end;
        let end = markers[2 * row + 2].start;
        assert_eq!(markers[2 * row + 2].ordinal - markers[2 * row + 1].ordinal - 1, op_count);
        assert_eq!(&body[start..end], raw.as_slice(), "shift interval differs at row {row}");
    }
    let summary = summarize_raw(graph, &raw, op_count);
    RepeatedInterval {
        sha3_256: sha3_hex(&raw),
        raw,
        op_count,
        instances: 255,
        first_op,
        end_op,
        summary,
    }
}

fn put_uvar(mut value: usize, out: &mut Vec<u8>) {
    while value >= 128 {
        out.push((value as u8 & 127) | 128);
        value >>= 7;
    }
    out.push(value as u8);
}

fn append_interval_node(
    data: &mut Vec<u8>,
    nodes: &mut Vec<Node>,
    summaries: &mut Vec<Summary>,
    interval: &RepeatedInterval,
) -> usize {
    let mut body = Vec::with_capacity(interval.raw.len() + 16);
    put_uvar(518, &mut body);
    put_uvar(256, &mut body);
    put_uvar(interval.op_count, &mut body);
    body.extend_from_slice(&interval.raw);
    let start = data.len();
    data.extend_from_slice(&body);
    let id = nodes.len();
    nodes.push(Node { start, end: data.len() });
    summaries.push(interval.summary);
    id
}

fn explicit_parent_map() -> Vec<QubitId> {
    (257..=512)
        .chain(513..=768)
        // Extracted D/H uses local S[1..4] = 513..516. Normalize those four
        // live locals onto parent S[0..3]; copied/S[5] locals are unused.
        .chain([773, 769, 770, 771, 772, 774])
        .map(|q| QubitId(q as u64))
        .collect()
}

fn replay_interval(graph: &Graph<'_>, node_id: usize, summary: Summary) -> Vec<Op> {
    let qinputs: Vec<_> = (257..=768).collect();
    let cinputs: Vec<_> = (0..512).collect();
    let mut state = State::new(835, 1280, &qinputs, &cinputs, true, summary.output_ops + 4096);
    state.retention.enabled = false;
    state.family24_enabled = false;
    state.family36_enabled = false;
    state.family63_enabled = false;
    let qmap = explicit_parent_map();
    assert_eq!(qmap.len(), 518);
    state.qmap[..518].copy_from_slice(&qmap);
    for (local, global) in (1024..=1279).enumerate() {
        state.cmap[local] = BitId(global as u64);
    }
    expand_node(graph, &mut state, node_id, 0, 518, 0, 256);
    state.flush_raw();
    assert!(matches!(state.pending_hmr, PendingHmr::None));
    assert!(state.proof.balanced());
    state.assert_accounting(summary.output_ops, 0);
    assert_eq!(state.input_hist[OperationType::CCX as usize]
        + state.input_hist[OperationType::CCZ as usize], summary.toffoli);
    assert!(state.out.iter().all(|op| {
        [op.q_control2, op.q_control1, op.q_target]
            .into_iter()
            .filter(|&q| q != NO_QUBIT)
            .all(|q| (257..=772).contains(&(q.0 as usize)))
    }));
    assert!(state.out.iter().all(|op| {
        [op.c_target, op.c_condition]
            .into_iter()
            .filter(|&bit| bit != NO_BIT)
            .all(|bit| (1024..=1281).contains(&(bit.0 as usize)))
    }));
    state.out
}

struct DeterministicXof([u8; 8]);

impl XofReader for DeterministicXof {
    fn read(&mut self, out: &mut [u8]) {
        for (index, byte) in out.iter_mut().enumerate() {
            *byte = self.0[index % self.0.len()];
        }
    }
}

fn set_word(sim: &mut Simulator<'_, DeterministicXof>, start: usize, value: U256) {
    for bit in 0..256 {
        sim.qubits[start + bit] = u64::from(value.bit(bit));
    }
}

fn get_word(sim: &Simulator<'_, DeterministicXof>, start: usize) -> U256 {
    let mut value = U256::ZERO;
    for bit in 0..256 {
        value.set_bit(bit, sim.qubits[start + bit] & 1 != 0);
    }
    value
}

fn halve_mod(value: U256, p: U256) -> U256 {
    if !value.bit(0) {
        value >> 1
    } else {
        (value >> 1) + (p >> 1) + U256::from(1)
    }
}

#[test]
fn exact_double_halve_interval_extraction_replay_and_count_only_root() {
    let original = zstd::stream::decode_all(COMPRESSED_HIR).unwrap();
    let mut shifted = shift_controls::replace(&original);
    let graph = parse_graph(&shifted);
    assert_atomic_parent_triple(&graph);
    let double = repeated_shift_interval(&graph, 2265, (0..256).rev());
    let halve = repeated_shift_interval(&graph, 2266, 0..256);

    assert_eq!(double.instances, 255);
    assert_eq!(halve.instances, 255);
    assert_eq!(double.summary.toffoli, 1_531);
    assert_eq!(halve.summary.toffoli, 1_531);
    assert_eq!(double.summary.h, double.summary.measure);
    assert_eq!(double.summary.h, double.summary.reset);
    assert_eq!(halve.summary.h, halve.summary.measure);
    assert_eq!(halve.summary.h, halve.summary.reset);

    let mut nodes = graph.nodes.clone();
    let mut summaries = graph.summaries.clone();
    let root = graph.root;
    let root_qubits = graph.root_qubits;
    let root_bits = graph.root_bits;
    drop(graph);
    let double_node = append_interval_node(&mut shifted, &mut nodes, &mut summaries, &double);
    let halve_node = append_interval_node(&mut shifted, &mut nodes, &mut summaries, &halve);
    let graph = Graph {
        data: &shifted,
        nodes,
        root,
        root_qubits,
        root_bits,
        summaries,
    };
    let double_ops = replay_interval(&graph, double_node, double.summary);
    let halve_ops = replay_interval(&graph, halve_node, halve.summary);
    let double_replay_t = double_ops.iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count();
    let halve_replay_t = halve_ops.iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count();

    let p = U256::from_str_radix(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
        16,
    ).unwrap();
    let values = [
        U256::ZERO,
        U256::from(1),
        U256::from(2),
        p >> 1,
        p.wrapping_sub(U256::from(2)),
        p.wrapping_sub(U256::from(1)),
    ];
    let dirty_values = [U256::ZERO, U256::MAX, U256::from(0xa5a5_a5a5_a5a5_a5a5u64)];
    let mut oracle_cases = 0usize;
    for random_pattern in [
        [0u8; 8],
        [0xffu8; 8],
        [0xa5, 0x5a, 0xc3, 0x3c, 0x96, 0x69, 0xf0, 0x0f],
    ] {
        for value in values {
            for dirty in dirty_values {
                let mut rng = DeterministicXof(random_pattern);
                let mut sim = Simulator::new(835, 1282, &mut rng);
                set_word(&mut sim, 257, dirty);
                set_word(&mut sim, 513, value);
                sim.apply_iter(double_ops.iter());
                assert_eq!(get_word(&sim, 513), value.add_mod(value, p));
                assert_eq!(get_word(&sim, 257), dirty);
                assert!(sim.qubits[769..=772].iter().all(|&bit| bit == 0));
                assert_eq!(sim.phase & 1, 0);
                sim.apply_iter(halve_ops.iter());
                assert_eq!(get_word(&sim, 513), value);
                assert_eq!(get_word(&sim, 257), dirty);
                assert!(sim.qubits[769..=772].iter().all(|&bit| bit == 0));
                assert_eq!(sim.phase & 1, 0);
                oracle_cases += 1;
            }
        }
        for value in values {
            let mut rng = DeterministicXof(random_pattern);
            let mut sim = Simulator::new(835, 1282, &mut rng);
            set_word(&mut sim, 513, value);
            sim.apply_iter(halve_ops.iter());
            assert_eq!(get_word(&sim, 513), halve_mod(value, p));
            assert_eq!(sim.phase & 1, 0);
            sim.apply_iter(double_ops.iter());
            assert_eq!(get_word(&sim, 513), value);
            assert_eq!(get_word(&sim, 257), U256::ZERO);
            assert!(sim.qubits[769..=772].iter().all(|&bit| bit == 0));
            assert_eq!(sim.phase & 1, 0);
            oracle_cases += 1;
        }
    }

    const OLD_INTERVAL: usize = 2_223_879;
    const NONMOD: usize = 295_680;
    const CSUB: usize = 2_813;
    let replacement = NONMOD
        + 129 * (double.summary.toffoli + halve.summary.toffoli)
        + 256 * (double.summary.toffoli + halve.summary.toffoli)
        + 3 * CSUB;
    assert_eq!(replacement, 1_482_989);
    let whole_root = graph.summaries[2269].toffoli - OLD_INTERVAL + replacement;
    assert_eq!(whole_root, 69_313_208);
    const NONMOD_OPS: usize = 295_680 + 394_240;
    let old_interval_ops = graph.summaries[2265].output_ops
        + graph.summaries[2258].output_ops
        + graph.summaries[2266].output_ops;
    let replacement_ops = NONMOD_OPS
        + 129 * (double.summary.output_ops + halve.summary.output_ops)
        + 256 * (double.summary.output_ops + halve.summary.output_ops)
        + 3 * graph.summaries[2258].output_ops;
    let whole_root_ops = graph.summaries[2269].output_ops - old_interval_ops + replacement_ops;

    println!("HALF_SQUARE_DH_EXTRACT double_instances={} double_ops={} double_bytes={} double_sha3_256={} double_t={} double_hmr={} double_expanded_ops={} halve_instances={} halve_ops={} halve_bytes={} halve_sha3_256={} halve_t={} halve_hmr={} halve_expanded_ops={} replay_double_ops={} replay_double_t={} replay_halve_ops={} replay_halve_t={} oracle_cases={} whole_root_old={} replacement={} whole_root_new={} delta=-{} old_root_ops={} old_interval_ops={} replacement_ops={} whole_root_ops={} status=pass",
        double.instances, double.op_count, double.raw.len(), double.sha3_256,
        double.summary.toffoli, double.summary.h, double.summary.output_ops,
        halve.instances, halve.op_count, halve.raw.len(), halve.sha3_256,
        halve.summary.toffoli, halve.summary.h, halve.summary.output_ops,
        double_ops.len(), double_replay_t, halve_ops.len(), halve_replay_t, oracle_cases,
        graph.summaries[2269].toffoli, replacement, whole_root,
        graph.summaries[2269].toffoli - whole_root,
        graph.summaries[2269].output_ops, old_interval_ops, replacement_ops, whole_root_ops);
    println!("HALF_SQUARE_DH_BOUNDARIES double_first=[{},{}), halve_first=[{},{}), normalized_qmap=Y257..512,A513..768,S0..3=769..772 normalized_cmap=1024..1279 copied_and_S5_unused=true",
        double.first_op, double.end_op, halve.first_op, halve.end_op);
}
