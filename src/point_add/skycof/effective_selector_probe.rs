//! Native bounded validation and transcript export for [`super::effective_selector`].
//! Research-only dispatch: `SKYCOF_RESEARCH=1 SKYCOF_PROBE=effective-selector`.
use super::effective_selector;
use crate::circuit::{Op, OperationType, QubitId as Q, NO_QUBIT};
use crate::point_add::builder::Builder;
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};
use std::fmt::Write as _;

fn toffoli(ops: &[Op]) -> (usize, f64) {
    let (mut depth, mut raw, mut expected) = (0usize, 0usize, 0.0);
    for op in ops {
        match op.kind {
            OperationType::PushCondition => depth += 1,
            OperationType::PopCondition => depth -= 1,
            OperationType::CCX | OperationType::CCZ => {
                raw += 1;
                expected += 2.0f64.powi(-(depth as i32));
            }
            _ => {}
        }
    }
    assert_eq!(depth, 0);
    (raw, expected)
}

fn touches(op: &Op, q: Q) -> bool {
    op.q_target == q || op.q_control1 == q || op.q_control2 == q
}

struct Built {
    ops: Vec<Op>,
    nq: usize,
    nb: usize,
    peak: u32,
    h: [Q; 6],
    g: Q,
    cin: Q,
    nodes: [Q; 5],
    flag: Q,
    observers: Vec<Q>,
    spectators: Vec<Q>,
}

fn build(lo: usize, hi: usize, descending: bool, g_positive: bool) -> Built {
    let c = &mut Builder::new();
    let h: [Q; 6] = c.alloc_qubits(6).try_into().unwrap();
    let g = c.alloc_qubit();
    let cin = c.alloc_qubit();
    let nodes: [Q; 5] = c.alloc_qubits(5).try_into().unwrap();
    let flag = c.alloc_qubit();
    let observers = c.alloc_qubits(hi - lo + 1);
    let spectators = c.alloc_qubits(256);
    effective_selector::stream(
        c, &h, &nodes, flag, g, lo, hi, descending, g_positive,
        |c, k, f, clean| {
            // Bind the advertised callback loan: `clean` temporarily holds
            // f&cin, drives a distinct observation, then returns to zero.
            c.ccx(f, cin, clean);
            c.cx(clean, observers[k - lo]);
            c.ccx(f, cin, clean);
        },
    );
    let (nq, nb) = c.i13_dims();
    let peak = c.peak_total();
    let ops = c.take_ops();
    for &q in &spectators {
        assert!(!ops.iter().any(|op| touches(op, q)), "spectator referenced");
    }
    Built { ops, nq, nb, peak, h, g, cin, nodes, flag, observers, spectators }
}

fn simulate(b: &Built, lo: usize, hi: usize, descending: bool, g_positive: bool) -> usize {
    let cases: Vec<(usize, bool, bool)> = (lo..=hi)
        .flat_map(|k| [false, true].into_iter().flat_map(move |g| [false, true].into_iter().map(move |cin| (k, g, cin))))
        .collect();
    let mut hsh = sha3::Shake256::default();
    hsh.update(b"effective-selector-native-probe-v1");
    let mut rd = hsh.finalize_xof();
    let mut sim = Simulator::new(b.nq, b.nb + 1, &mut rd);
    for (batch_idx, batch) in cases.chunks(64).enumerate() {
        sim.clear_for_shot();
        let mut observer_before = vec![0u64; b.observers.len()];
        let mut spectator_before = vec![0u64; b.spectators.len()];
        for (lane, &(k, g, cin)) in batch.iter().enumerate() {
            for (i, &q) in b.h.iter().enumerate() {
                if (k % 64 >> i) & 1 != 0 { *sim.qubit_mut(q) |= 1 << lane; }
            }
            if g { *sim.qubit_mut(b.g) |= 1 << lane; }
            if cin { *sim.qubit_mut(b.cin) |= 1 << lane; }
            for (i, &q) in b.observers.iter().enumerate() {
                let v = ((i * 17 + lane * 29 + batch_idx) & 1) != 0;
                if v { *sim.qubit_mut(q) |= 1 << lane; observer_before[i] |= 1 << lane; }
            }
            for (i, &q) in b.spectators.iter().enumerate() {
                let v = ((i * 13 + lane * 7 + batch_idx * 3) & 1) != 0;
                if v { *sim.qubit_mut(q) |= 1 << lane; spectator_before[i] |= 1 << lane; }
            }
        }
        sim.apply_iter(b.ops.iter());
        assert_eq!(sim.phase, 0, "residual phase batch {batch_idx}");
        for (lane, &(k, g, cin)) in batch.iter().enumerate() {
            for (i, &q) in b.h.iter().enumerate() {
                assert_eq!((sim.qubit(q) >> lane) & 1, (k % 64 >> i) as u64 & 1);
            }
            assert_eq!((sim.qubit(b.g) >> lane) & 1, g as u64);
            assert_eq!((sim.qubit(b.cin) >> lane) & 1, cin as u64);
            for &q in b.nodes.iter().chain(std::iter::once(&b.flag)) {
                assert_eq!((sim.qubit(q) >> lane) & 1, 0, "dirty work");
            }
            let eg = if g_positive { g } else { !g };
            for (i, &q) in b.observers.iter().enumerate() {
                let j = lo + i;
                let threshold = if descending { k >= j } else { k > j };
                let want = ((observer_before[i] >> lane) & 1) ^ (eg && cin && threshold) as u64;
                assert_eq!((sim.qubit(q) >> lane) & 1, want, "observer k={k} j={j}");
            }
            for (i, &q) in b.spectators.iter().enumerate() {
                assert_eq!((sim.qubit(q) >> lane) & 1, (spectator_before[i] >> lane) & 1);
            }
        }
    }
    cases.len()
}

fn op_json(op: &Op) -> String {
    let q = |x: Q| if x == NO_QUBIT { "null".to_string() } else { x.0.to_string() };
    format!(
        "{{\"kind\":\"{:?}\",\"q2\":{},\"q1\":{},\"qt\":{},\"ct\":{},\"cc\":{}}}",
        op.kind, q(op.q_control2), q(op.q_control1), q(op.q_target), op.c_target.0, op.c_condition.0
    )
}

pub fn run() {
    let supports = [(0, 63), (247, 310), (247, 256), (118, 166), (1, 5)];
    let mut total_cases = 0usize;
    let mut transcript = String::from("{\n  \"format\": \"effective-selector-native-v1\",\n  \"channels\": [\n");
    let mut first = true;
    for &(lo, hi) in &supports {
        for descending in [false, true] {
            for g_positive in [false, true] {
                let b = build(lo, hi, descending, g_positive);
                total_cases += simulate(&b, lo, hi, descending, g_positive);
                let (raw, expected) = toffoli(&b.ops);
                eprintln!("EFFECTIVE_SELECTOR lo={lo} hi={hi} dir={} gpol={} Q={} rawT={raw} expectedT={expected:.1} ops={} cases={}", if descending{"desc"}else{"asc"}, g_positive as u8, b.peak, b.ops.len(), 4*(hi-lo+1));
                if (lo, hi) == (0, 63) {
                    if !first { transcript.push_str(",\n"); }
                    first = false;
                    write!(transcript, "    {{\"lo\":{lo},\"hi\":{hi},\"descending\":{descending},\"g_positive\":{g_positive},\"roles\":{{\"h\":{:?},\"g\":{},\"cin\":{},\"nodes\":{:?},\"flag\":{},\"observers\":{:?}}},\"ops\":[", b.h.map(|q|q.0), b.g.0, b.cin.0, b.nodes.map(|q|q.0), b.flag.0, b.observers.iter().map(|q|q.0).collect::<Vec<_>>()).unwrap();
                    for (i, op) in b.ops.iter().enumerate() {
                        if i != 0 { transcript.push(','); }
                        transcript.push_str(&op_json(op));
                    }
                    transcript.push_str("]}");
                }
            }
        }
    }
    transcript.push_str("\n  ]\n}\n");
    std::fs::write("analysis/ALG007_EFFECTIVE_SELECTOR_NATIVE_TRANSCRIPT_2026-10-06.json", transcript).unwrap();
    eprintln!("EFFECTIVE_SELECTOR_PASS cases={total_cases} transcript=analysis/ALG007_EFFECTIVE_SELECTOR_NATIVE_TRANSCRIPT_2026-10-06.json");
}
