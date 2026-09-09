use super::{Graph, QubitId, Reader, State, NO_BIT, NO_QUBIT};
#[derive(Clone, Copy, Default)]
struct O {
    t: u8,
    cw: usize,
    e: usize,
    nq: usize,
    q: [usize; 3],
    nc: usize,
}
fn read(r: &mut Reader<'_>) -> O {
    let mut o = O::default();
    o.t = r.byte();
    o.cw = r.uvar();
    o.e = r.uvar();
    for _ in 0..o.cw {
        r.uvar();
    }
    if o.t == 11 {
        r.uvar();
    }
    o.nq = r.uvar();
    for i in 0..o.nq {
        let q = r.uvar();
        if i < 3 {
            o.q[i] = q;
        }
    }
    o.nc = r.uvar();
    for _ in 0..o.nc {
        r.uvar();
    }
    o
}
fn plain(o: O, t: u8, nq: usize) -> bool {
    o.t == t && o.cw == 0 && o.e == 1 && o.nq == nq && o.nc == 0
}
fn pair(o: O, a: usize, b: usize, t: usize) -> bool {
    plain(o, 5, 3) && o.q[2] == t && ((o.q[0] == a && o.q[1] == b) || (o.q[0] == b && o.q[1] == a))
}
fn cx(o: O, a: usize, b: usize) -> bool {
    plain(o, 3, 2) && o.q[..2] == [a, b]
}
fn x(o: O, a: usize) -> bool {
    plain(o, 1, 1) && o.q[0] == a
}
pub(super) fn exclusions(g: &Graph<'_>) -> Vec<Vec<(usize, usize)>> {
    let mut out = Vec::new();
    for (id, node) in g.nodes.iter().enumerate() {
        let mut r = Reader {
            data: &g.data[node.start..node.end],
            at: 0,
        };
        r.uvar();
        r.uvar();
        let count = r.uvar();
        let mut ranges: Vec<(usize, usize)> = Vec::new();
        for ix in 0..count {
            let at = r.at;
            let o = read(&mut r);
            let mut end = ix;
            if (id == 2261 && (155419..155438).contains(&ix))
                || (id == 2263 && (10661..10680).contains(&ix))
            {
                end = ix + 1;
            }
            if o.t == 5 {
                if [
                    include_bytes!("prefix_retention_bank531.hir").as_slice(),
                    include_bytes!("prefix_retention_bank540.hir").as_slice(),
                ]
                .iter()
                .any(|b| r.data[at..].starts_with(b))
                {
                    end = ix + 65;
                } else if count - ix >= 7 {
                    let mut p = Reader { data: r.data, at };
                    let mut tags = [0; 7];
                    for t in &mut tags {
                        *t = read(&mut p).t;
                    }
                    if tags == [5, 5, 8, 9, 10, 11, 5] || tags == [5, 5, 5, 8, 9, 10, 11] {
                        end = ix + 7;
                    }
                }
            }
            if end > ix {
                if let Some(last) = ranges.last_mut() {
                    if ix <= last.1 {
                        last.1 = last.1.max(end);
                        continue;
                    }
                }
                ranges.push((ix, end));
            }
        }
        assert_eq!(r.at, r.data.len());
        out.push(ranges);
    }
    out
}
pub(super) fn try_apply(
    s: &mut State,
    r: &mut Reader<'_>,
    node: usize,
    ix: usize,
    count: usize,
    qs: usize,
    qlen: usize,
    boundary: usize,
) -> Option<usize> {
    let tag = r.data[r.at];
    if tag != 1 && tag != 5 {
        return None;
    }
    let len = if tag == 1 { 6 } else { 3 };
    if count - ix < len {
        return None;
    }
    let ranges = &s.motif_exclusions[node];
    let p = ranges.partition_point(|x| x.1 <= ix);
    if ranges.get(p).is_some_and(|x| x.0 < ix + len) {
        return None;
    }
    let mut rr = Reader {
        data: r.data,
        at: r.at,
    };
    let mut v = [O::default(); 6];
    for i in 0..len {
        v[i] = read(&mut rr);
    }
    if rr.at > boundary {
        return None;
    }
    let (family, wires) = if tag == 5 {
        if !plain(v[0], 5, 3) {
            return None;
        }
        let [a, b, t] = v[0].q;
        let u = v[1].q[1];
        if !cx(v[1], t, u) || !pair(v[2], a, b, t) {
            return None;
        }
        (0, vec![a, b, t, u])
    } else {
        if !plain(v[0], 1, 1) || !plain(v[1], 5, 3) {
            return None;
        }
        let a = v[0].q[0];
        let b = if v[1].q[0] == a {
            v[1].q[1]
        } else if v[1].q[1] == a {
            v[1].q[0]
        } else {
            return None;
        };
        let t = v[1].q[2];
        if !x(v[2], a) || !x(v[4], a) || !pair(v[5], a, b, t) {
            return None;
        }
        if cx(v[3], b, a) {
            (2, vec![a, b, t])
        } else {
            let u = v[3].q[1];
            if !cx(v[3], t, u) {
                return None;
            }
            (1, vec![a, b, t, u])
        }
    };
    if s.motif_family != 3 && s.motif_family != family {
        return None;
    }
    if wires.iter().any(|q| *q >= qlen) {
        return None;
    }
    let mut mapped = Vec::new();
    for &q in &wires {
        let p = s.qmap[qs + q];
        if mapped.contains(&p) {
            return None;
        }
        mapped.push(p);
    }
    // Keep original mathematical IDs/cache and semantic counter sequence. Exclude outer control.
    if mapped.contains(&QubitId(0)) {
        return None;
    }
    let mut replacement = Vec::new();
    let mut emit = |tag: u8, args: &[usize]| {
        let mut op = super::Op::empty();
        match tag {
            1 => {
                op.kind = super::OperationType::X;
                op.q_target = mapped[args[0]];
            }
            3 => {
                op.kind = super::OperationType::CX;
                op.q_control1 = mapped[args[0]];
                op.q_target = mapped[args[1]];
            }
            5 => {
                op.kind = super::OperationType::CCX;
                op.q_control2 = mapped[args[0]];
                op.q_control1 = mapped[args[1]];
                op.q_target = mapped[args[2]];
            }
            _ => unreachable!(),
        }
        op.validate();
        replacement.push(op);
    };
    match family {
        0 => {
            emit(3, &[2, 3]);
            emit(5, &[0, 1, 3]);
        }
        1 => {
            emit(1, &[0]);
            emit(3, &[2, 3]);
            emit(5, &[0, 1, 3]);
        }
        2 => {
            emit(1, &[0]);
            emit(3, &[1, 0]);
            emit(3, &[1, 2]);
        }
        _ => unreachable!(),
    }
    s.flush_raw();
    assert!(s.capture.is_none());
    s.capture = Some(Vec::new());
    let before = [
        s.proof.rewrites,
        s.proof.support_dead,
        s.proof.support_x,
        s.proof.support_cx,
    ];
    for o in v.iter().take(len) {
        let mut q = [NO_QUBIT; 3];
        for j in 0..o.nq {
            q[j] = s.qmap[qs + o.q[j]];
        }
        s.emit_leaf(o.t, &q, o.nq, NO_BIT, 0);
    }
    s.flush_raw();
    let captured = s.capture.take().unwrap();
    let count_t = |v: &[super::Op]| {
        v.iter()
            .filter(|o| {
                matches!(
                    o.kind,
                    super::OperationType::CCX | super::OperationType::CCZ
                )
            })
            .count()
    };
    let old_t = count_t(&captured);
    let new_t = count_t(&replacement);
    if new_t < old_t {
        // Only generated private scratch may occur; every use is preceded by an unconditional write.
        let mut private_written = false;
        for op in &captured {
            assert!(op.c_target == NO_BIT || op.c_target == s.measurement_bit);
            assert!(op.c_condition == NO_BIT || op.c_condition == s.measurement_bit);
            if op.c_condition == s.measurement_bit {
                assert!(private_written);
            }
            if op.c_target == s.measurement_bit {
                assert_eq!(op.kind, super::OperationType::Hmr);
                assert_eq!(op.c_condition, NO_BIT);
                private_written = true;
            }
        }
        s.selected_counts[family] += 1;
        s.selected_t_saving += old_t - new_t;
        s.skipped_cleanups += s.proof.rewrites - before[0];
        s.skipped_support[0] += s.proof.support_dead - before[1];
        s.skipped_support[1] += s.proof.support_x - before[2];
        s.skipped_support[2] += s.proof.support_cx - before[3];
        s.selected_delta += replacement.len() as isize - captured.len() as isize;
        s.output_ops -= captured.len();
        for op in &captured {
            s.output_hist[op.kind as usize] -= 1;
        }
        for op in replacement {
            s.write(op);
        }
    } else if s.retain_output {
        s.out.extend(captured);
    }
    s.motif_counts[family] += 1;
    r.at = rr.at;
    Some(len)
}
#[cfg(test)]
#[test]
fn selfcheck() {
    extended_tests();
    use super::OperationType as K;
    let fixtures = [
        include_bytes!("motif_fixture_0.hir").as_slice(),
        include_bytes!("motif_fixture_2.hir").as_slice(),
        include_bytes!("motif_fixture_6.hir").as_slice(),
    ];
    for (family, data) in fixtures.iter().enumerate() {
        let mut rr = Reader { data, at: 0 };
        let mut old = Vec::new();
        let mut locals = Vec::new();
        while rr.at < data.len() {
            let o = read(&mut rr);
            for &q in &o.q[..o.nq] {
                if !locals.contains(&q) {
                    locals.push(q);
                }
            }
            old.push(o);
        }
        let n = locals.len();
        let mut s = State::new(n + 1, 1, &(1..=n).collect::<Vec<_>>(), &[], true, 0);
        s.qmap = vec![QubitId(0); 580];
        for (j, &q) in locals.iter().enumerate() {
            s.qmap[q] = QubitId((j + 1) as u64);
        }
        s.motif_exclusions = vec![vec![]];
        let mut r = Reader { data, at: 0 };
        assert_eq!(
            try_apply(&mut s, &mut r, 0, 0, old.len(), 0, 580, usize::MAX),
            Some(old.len())
        );
        s.flush_raw();
        assert_eq!(s.motif_counts[family], 1);
        assert_eq!(r.at, data.len());
        assert_eq!(s.input_ops, old.len());
        assert_eq!(s.selected_counts[family], 1);
        for mask in 0..1usize << n {
            let mut before = mask;
            for o in &old {
                let qs: Vec<_> = o.q[..o.nq]
                    .iter()
                    .map(|q| locals.iter().position(|p| p == q).unwrap())
                    .collect();
                match o.t {
                    1 => before ^= 1 << qs[0],
                    3 => before ^= ((before >> qs[0]) & 1) << qs[1],
                    5 => before ^= (((before >> qs[0]) & (before >> qs[1])) & 1) << qs[2],
                    _ => panic!(),
                }
            }
            let mut after = mask << 1;
            for o in &s.out {
                o.validate();
                match o.kind {
                    K::X => after ^= 1 << o.q_target.0,
                    K::CX => after ^= ((after >> o.q_control1.0) & 1) << o.q_target.0,
                    K::CCX => {
                        after ^= (((after >> o.q_control1.0) & (after >> o.q_control2.0)) & 1)
                            << o.q_target.0
                    }
                    _ => panic!("unexpected selfcheck op"),
                }
            }
            assert_eq!(before, after >> 1);
        }
        // Exclusion overlap, conditional/inactive record and physical alias must reject before mutation.
        let mut blocked = State::new(600, 1, &[], &[], false, 0);
        blocked.motif_exclusions = vec![vec![(old.len() - 1, old.len())]];
        let mut r = Reader { data, at: 0 };
        assert_eq!(
            try_apply(&mut blocked, &mut r, 0, 0, old.len(), 0, 580, usize::MAX),
            None
        );
        assert_eq!(r.at, 0);
        let mut inactive = data.to_vec();
        inactive[2] = 0;
        let mut blocked = State::new(600, 1, &[], &[], false, 0);
        blocked.motif_exclusions = vec![vec![]];
        let mut r = Reader {
            data: &inactive,
            at: 0,
        };
        assert_eq!(
            try_apply(&mut blocked, &mut r, 0, 0, old.len(), 0, 580, usize::MAX),
            None
        );
        assert_eq!(r.at, 0);
        let mut conditioned = data.to_vec();
        conditioned[1] = 1;
        conditioned.insert(3, 0);
        let mut blocked = State::new(600, 1, &[], &[], false, 0);
        blocked.motif_exclusions = vec![vec![]];
        let mut r = Reader {
            data: &conditioned,
            at: 0,
        };
        assert_eq!(
            try_apply(&mut blocked, &mut r, 0, 0, old.len(), 0, 580, usize::MAX),
            None
        );
        assert_eq!(r.at, 0);
        let mut blocked = State::new(600, 1, &[], &[], false, 0);
        blocked.motif_exclusions = vec![vec![]];
        blocked.qmap.fill(QubitId(1));
        let mut r = Reader { data, at: 0 };
        assert_eq!(
            try_apply(&mut blocked, &mut r, 0, 0, old.len(), 0, 580, usize::MAX),
            None
        );
        assert_eq!(r.at, 0);
    }
    eprintln!("SELF_CHECK PASS: three actual matcher/emitter cores, 40 basis cases, exclusion/inactive/conditional/alias negatives");
}
#[cfg(test)]
fn extended_tests() {
    use crate::{
        circuit::{BitId, Op, OperationType as K},
        sim::Simulator,
    };
    use sha3::digest::XofReader;
    struct Outcome(u8);
    impl XofReader for Outcome {
        fn read(&mut self, b: &mut [u8]) {
            b.fill(self.0);
        }
    }
    fn gate(k: K, a: usize, b: usize, t: usize) -> Op {
        let mut o = Op::empty();
        o.kind = k;
        o.q_target = QubitId(t as u64);
        if matches!(k, K::CX | K::CCX) {
            o.q_control1 = QubitId(b as u64);
        }
        if k == K::CCX {
            o.q_control2 = QubitId(a as u64);
        }
        o
    }
    let fixtures = [
        include_bytes!("motif_fixture_0.hir").as_slice(),
        include_bytes!("motif_fixture_2.hir").as_slice(),
        include_bytes!("motif_fixture_6.hir").as_slice(),
    ];
    let mut cases = 0;
    let (mut selected, mut fallback, mut selected_hmr) = (0, 0, 0);
    for data in fixtures {
        let mut r = Reader { data, at: 0 };
        let mut old = Vec::new();
        let mut locals = Vec::new();
        while r.at < data.len() {
            let o = read(&mut r);
            for &q in &o.q[..o.nq] {
                if !locals.contains(&q) {
                    locals.push(q);
                }
            }
            old.push(o);
        }
        let n = locals.len();
        let mut original = Vec::new();
        for o in &old {
            let qs: Vec<_> = o.q[..o.nq]
                .iter()
                .map(|q| locals.iter().position(|p| p == q).unwrap() + 1)
                .collect();
            original.push(match o.t {
                1 => gate(K::X, 0, 0, qs[0]),
                3 => gate(K::CX, 0, qs[0], qs[1]),
                5 => gate(K::CCX, qs[0], qs[1], qs[2]),
                _ => panic!(),
            });
        }
        for pattern in 0..3 {
            for condition in 0..4 {
                // pattern2 establishes t=(not a)*b before the motif, forcing first-CCX cleanup in C.
                let mut lead = Vec::new();
                if pattern == 2 {
                    lead.extend([
                        gate(K::X, 0, 0, 1),
                        gate(K::CCX, 1, 2, 3),
                        gate(K::X, 0, 0, 1),
                    ]);
                }
                if condition == 1 || condition == 2 {
                    let mut op = Op::empty();
                    op.kind = if condition == 1 {
                        K::BitStore1
                    } else {
                        K::BitStore0
                    };
                    op.c_target = BitId(0);
                    lead.push(op);
                }
                if condition > 0 {
                    let mut op = Op::empty();
                    op.kind = K::PushCondition;
                    op.c_condition = BitId(0);
                    lead.push(op);
                }
                let mut tail = Vec::new();
                if condition > 0 {
                    let mut op = Op::empty();
                    op.kind = K::PopCondition;
                    tail.push(op);
                }
                tail.extend([gate(K::CCX, 1, 2, n + 1), gate(K::CCX, 1, 2, n + 1)]);
                let inputs: Vec<_> = (1..=n).filter(|q| pattern == 0 || *q != 3).collect();
                let cinputs = if condition == 3 { vec![0] } else { vec![] };
                let build = |retain| {
                    let mut s = State::new(n + 2, 1, &inputs, &cinputs, retain, 0);
                    s.qmap = vec![QubitId(0); 580];
                    for (j, &q) in locals.iter().enumerate() {
                        s.qmap[q] = QubitId((j + 1) as u64);
                    }
                    s.motif_exclusions = vec![vec![]];
                    for &op in &lead {
                        *s.raw(op.kind) = op;
                    }
                    let mut r = Reader { data, at: 0 };
                    assert!(
                        try_apply(&mut s, &mut r, 0, 0, old.len(), 0, 580, usize::MAX).is_some()
                    );
                    for &op in &tail {
                        *s.raw(op.kind) = op;
                    }
                    s.flush_raw();
                    s.assert_accounting(lead.len() + old.len() + tail.len(), 0);
                    assert!(s.proof.balanced());
                    s
                };
                let state = build(true);
                let counted = build(false);
                assert!(state.out.iter().any(|o| o.kind == K::Hmr));
                assert!(counted.out.is_empty());
                assert_eq!(state.input_hist, counted.input_hist);
                assert_eq!(state.output_hist, counted.output_hist);
                assert_eq!(state.input_ops, counted.input_ops);
                assert_eq!(state.output_ops, counted.output_ops);
                assert_eq!(state.trace, counted.trace);
                assert_eq!(
                    state.proof.diagnostic_fingerprint(),
                    counted.proof.diagnostic_fingerprint()
                );
                assert_eq!(state.selected_counts, counted.selected_counts);
                assert_eq!(state.skipped_cleanups, counted.skipped_cleanups);
                assert_eq!(state.selected_delta, counted.selected_delta);
                if state.selected_counts.iter().sum::<usize>() == 1 {
                    selected += 1;
                    if state.skipped_cleanups > 0 {
                        selected_hmr += 1;
                    }
                } else {
                    fallback += 1;
                }
                let all_original: Vec<_> = lead
                    .iter()
                    .chain(original.iter())
                    .chain(tail.iter())
                    .copied()
                    .collect();
                for mask in 0..1usize << n {
                    if pattern > 0 && (mask >> 2) & 1 != 0 {
                        continue;
                    }
                    for outcome in [0, 255] {
                        for stale in [0, 1] {
                            for active in [0, 1] {
                                let mut rng = Outcome(outcome);
                                let mut got = Simulator::new(n + 2, 3, &mut rng);
                                for j in 0..n {
                                    got.qubits[j + 1] = ((mask >> j) & 1) as u64;
                                }
                                got.bits[0] = active;
                                got.bits[1] = stale;
                                got.apply_iter(state.out.iter());
                                let mut rr = Outcome(0);
                                let mut want = Simulator::new(n + 2, 3, &mut rr);
                                for j in 0..n {
                                    want.qubits[j + 1] = ((mask >> j) & 1) as u64;
                                }
                                want.bits[0] = active;
                                want.bits[1] = stale;
                                want.apply_iter(all_original.iter());
                                for j in 0..=n + 1 {
                                    assert_eq!(
                                        got.qubits[j] & 1,
                                        want.qubits[j] & 1,
                                        "pattern={pattern} condition={condition}"
                                    );
                                }
                                assert_eq!(got.phase & 1, want.phase & 1);
                                assert_eq!(got.bits[0], want.bits[0]);
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(selected > 0 && fallback > 0 && selected_hmr > 0);
    eprintln!("ACTUAL_SIMULATOR PASS cases={cases} selected_contexts={selected} fallback_contexts={fallback} selected_HMR_contexts={selected_hmr}; arbitrary/zero/correlated target, both measurement outcomes, stale private bit0/1, inherited active/inactive/unknown conditions, retained/count-only parity, subsequent cleanup overwrites private scratch before phase use, source classical bit preserved");
}
