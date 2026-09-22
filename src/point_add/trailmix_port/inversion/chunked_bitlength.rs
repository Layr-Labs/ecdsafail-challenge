//! Exact prefix queries with bounded clean chunks and measured cleanup.
use super::{env_usize, Circuit, QReg};

struct Boundary {
    wire: QReg,
    start: usize,
    end: usize,
}

fn chunk_size(c: &Circuit, n: usize) -> Option<usize> {
    if n <= 2 { return Some(1); }
    let cap = env_usize("MIDQ_PREFIX_QCAP", 1019);
    let available = cap.saturating_sub(c.b.active_qubits as usize);
    let count = n - 2;
    (1..=count.min(env_usize("MIDQ_PREFIX_CHUNK", 32).max(1)))
        .filter(|&k| k + count.div_ceil(k) - 1 <= available)
        .min_by_key(|&k| ((count.div_ceil(k) - 1) * (k - 1),
            k + count.div_ceil(k) - 1, k))
}

pub(super) fn fits(c: &mut Circuit, n: usize) -> bool {
    c.flush_pending_frees();
    if std::env::var("MIDQ_VARIABLE_CHUNKS").ok().as_deref() == Some("1") {
        return variable_plan(c, n).is_some();
    }
    chunk_size(c, n).is_some()
}

fn variable_plan(c: &Circuit, n: usize) -> Option<Vec<usize>> {
    let cap = env_usize("MIDQ_PREFIX_QCAP", 1019);
    crate::point_add::clean_chunk_plan::plan(n.saturating_sub(2),
        cap.saturating_sub(c.b.active_qubits as usize))
}

fn deposit(c: &mut Circuit, control: Option<&QReg>, pos: &[QReg], n: usize, i: usize) {
    let k = n - 1 - i;
    let gray = k ^ (k + 1);
    for (bit, out) in pos.iter().enumerate() {
        if gray >> bit & 1 != 0 {
            if let Some(control) = control { c.cx(control, out); }
            else { c.x(out); }
        }
    }
}

pub(super) fn xor(c: &mut Circuit, src: &[&QReg], pos: &[QReg]) {
    if std::env::var("MIDQ_VARIABLE_CHUNKS").ok().as_deref() == Some("1") {
        let plan = variable_plan(c, src.len()).expect("query scratch budget checked");
        return xor_with_plan(c, src, pos, &plan);
    }
    let block = chunk_size(c, src.len()).expect("query scratch budget checked");
    xor_with_block(c, src, pos, block);
}

fn xor_with_block(c: &mut Circuit, src: &[&QReg], pos: &[QReg], block: usize) {
    let mut remaining = src.len().saturating_sub(2);
    let mut plan = Vec::new();
    while remaining != 0 {
        plan.push(remaining.min(block));
        remaining -= remaining.min(block);
    }
    xor_with_plan(c, src, pos, &plan);
}

fn xor_with_plan(c: &mut Circuit, src: &[&QReg], pos: &[QReg], plan: &[usize]) {
    let n = src.len();
    if n == 0 { return; }
    assert!(src.iter().all(|a| pos.iter().all(|b| a.id() != b.id())));
    let section = c.push_section("chunked.bitlength");
    for &bit in src { c.x(bit); }
    deposit(c, None, pos, n, 0);
    if n >= 2 {
        let q: Vec<_> = src.iter().rev().take(n - 1).copied().collect();
        deposit(c, Some(q[0]), pos, n, 1);
        let mut boundaries: Vec<Boundary> = Vec::new();
        let mut start = 1;
        for &size in plan {
            let end = start + size;
            let initial = boundaries.last().map_or(q[0], |b| &b.wire);
            let mut chain: Vec<QReg> = Vec::new();
            for j in start..end {
                let next = c.alloc_qreg("prefix.and");
                c.ccx(chain.last().unwrap_or(initial), q[j], &next);
                deposit(c, Some(&next), pos, n, j + 1);
                chain.push(next);
            }
            let keep = end < q.len();
            let last_to_clear = chain.len() - usize::from(keep);
            for i in (0..last_to_clear).rev() {
                let previous = if i == 0 { initial } else { &chain[i - 1] };
                c.clear_and(&chain[i], previous, q[start + i]);
            }
            let retained = keep.then(|| chain.pop().unwrap());
            for bit in chain { c.zero_and_free(bit); }
            if let Some(wire) = retained {
                boundaries.push(Boundary { wire, start, end });
            }
            start = end;
        }
        assert_eq!(start, q.len());
        // Boundary parents are still live. Recompute only the local chunk's
        // phase, then discharge its temporary ANDs in reverse order.
        while let Some(boundary) = boundaries.pop() {
            let initial = boundaries.last().map_or(q[0], |b| &b.wire);
            let phase = c.alloc_bit();
            c.hmr(&boundary.wire, phase);
            c.with_condition(phase, |c| {
                let mut chain: Vec<QReg> = Vec::new();
                for j in boundary.start..boundary.end - 1 {
                    let next = c.alloc_qreg("prefix.phase.and");
                    c.ccx(chain.last().unwrap_or(initial), q[j], &next);
                    chain.push(next);
                }
                c.cz(chain.last().unwrap_or(initial), q[boundary.end - 1]);
                for i in (0..chain.len()).rev() {
                    let previous = if i == 0 { initial } else { &chain[i - 1] };
                    c.clear_and(&chain[i], previous, q[boundary.start + i]);
                }
                for bit in chain { c.zero_and_free(bit); }
            });
            c.free_bit(phase);
            c.zero_and_free(boundary.wire);
        }
    }
    for &bit in src { c.x(bit); }
    c.pop_section(&section);
}

pub(crate) fn selftest() {
    use crate::circuit::{analyze_ops, QubitId, OperationType};
    use crate::sim::Simulator;
    use sha3::{digest::{ExtendableOutput, Update, XofReader}, Shake256};
    struct Random { forced: Option<u8>, rng: sha3::Shake256Reader }
    impl XofReader for Random {
        fn read(&mut self, out: &mut [u8]) {
            if let Some(byte) = self.forced { out.fill(byte); }
            else { self.rng.read(out); }
        }
    }
    let mut checked = 0usize;
    for n in 1usize..=10 {
        for width in [1usize, 5] {
            for block in [0usize, 1, 2, 4, 32] {
                std::env::set_var("MIDQ_PREFIX_CHUNK", block.to_string());
                std::env::set_var("MIDQ_PREFIX_QCAP", "1019");
                let mut c = Circuit::new();
                let value = c.alloc_qreg_bits("test.value", n);
                let pos = c.alloc_qreg_bits("test.pos", width);
                let value_ids: Vec<_> = value.iter().map(|q| QubitId(q.id().into())).collect();
                let pos_ids: Vec<_> = pos.iter().map(|q| QubitId(q.id().into())).collect();
                let plan = crate::point_add::clean_chunk_plan::plan(n.saturating_sub(2),
                    n.saturating_sub(4).max(3));
                let emit = |c: &mut Circuit| {
                    if block == 0 {
                        xor_with_plan(c, &value.iter().collect::<Vec<_>>(), &pos, plan.as_ref().unwrap());
                    } else {
                        xor_with_block(c, &value.iter().collect::<Vec<_>>(), &pos, block);
                    }
                };
                emit(&mut c);
                let midpoint = c.b.ops.len();
                emit(&mut c);
                let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
                let nq = (nq as usize).max(value_ids.iter().chain(&pos_ids)
                    .map(|q| q.0 as usize + 1).max().unwrap());
                let t = c.b.ops[..midpoint].iter()
                    .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count();
                for mode in 0..4 {
                    let mut seed = Shake256::default();
                    seed.update(b"chunked-bitlength-v1");
                    let mut random = Random { forced: [Some(0), Some(255), Some(0x55), None][mode],
                        rng: seed.finalize_xof() };
                    for first in (0..1usize << (n + width)).step_by(64) {
                        let count = (1usize << (n + width)).saturating_sub(first).min(64);
                        let mask = u64::MAX >> (64 - count);
                        let mut sim = Simulator::new(nq, nb as usize + 1, &mut random);
                        for (bit, &id) in value_ids.iter().chain(&pos_ids).enumerate() {
                            for shot in 0..count {
                                *sim.qubit_mut(id) |= (((first + shot) >> bit & 1) as u64) << shot;
                            }
                        }
                        super::predicate_clear_selftest::checked_apply(&mut sim, &c.b.ops[..midpoint], mask);
                        assert_eq!(sim.phase & mask, 0, "query phase n={n} block={block}");
                        for shot in 0..count {
                            let input = first + shot;
                            let x = input & ((1 << n) - 1);
                            let p = input >> n;
                            let index = if x == 0 { 0 } else { usize::BITS as usize - 1 - x.leading_zeros() as usize };
                            let expected = p ^ ((n ^ index) & ((1 << width) - 1));
                            for (bit, &id) in pos_ids.iter().enumerate() {
                                assert_eq!(sim.qubit(id) >> shot & 1, (expected >> bit & 1) as u64);
                            }
                            for (bit, &id) in value_ids.iter().enumerate() {
                                assert_eq!(sim.qubit(id) >> shot & 1, (x >> bit & 1) as u64);
                            }
                        }
                        super::predicate_clear_selftest::checked_apply(&mut sim, &c.b.ops[midpoint..], mask);
                        assert_eq!(sim.phase & mask, 0, "inverse phase");
                        for (bit, &id) in value_ids.iter().chain(&pos_ids).enumerate() {
                            for shot in 0..count {
                                assert_eq!(sim.qubit(id) >> shot & 1, ((first + shot) >> bit & 1) as u64);
                            }
                            *sim.qubit_mut(id) = 0;
                        }
                        assert!(sim.qubits.iter().all(|v| v & mask == 0), "dirty scratch");
                        checked += count;
                    }
                }
                if n == 10 && width == 5 { eprintln!("PREFIX component n={n} block={block} Q={nq} emittedT={t}"); }
            }
        }
    }
    std::env::remove_var("MIDQ_PREFIX_CHUNK");
    eprintln!("CHUNKED_PREFIX_SELFTEST PASS: {checked} basis/measurement cases, value/phase/pre-reset");
}
