//! Bounded exact AND queries, with measured replay of retained prefixes.
use super::*;

pub(super) fn apply(c: &mut Circuit, src: &[&QReg], out: Option<&QReg>) -> bool {
    if std::env::var("MIDQ_CHUNKED_PREDICATE").ok().as_deref() != Some("1") {
        return false;
    }
    c.flush_pending_frees();
    let available = env_usize("MIDQ_PREFIX_QCAP", 1019)
        .saturating_sub(c.b.active_qubits as usize);
    let Some(plan) = crate::point_add::clean_chunk_plan::plan(src.len().saturating_sub(2), available)
        else { return false; };
    let section = c.push_section("chunked.predicate");
    match (src, out) {
        ([], Some(out)) => c.x(out),
        ([], None) => c.b.push_op(crate::circuit::Op::empty()),
        ([a], Some(out)) => c.cx(a, out),
        ([a], None) => c.z(a),
        ([a, b], Some(out)) => c.ccx(a, b, out),
        ([a, b], None) => c.cz(a, b),
        _ => {
            let mut boundaries: Vec<QReg> = Vec::new();
            let mut ranges = Vec::new();
            let mut start = 1;
            for size in plan {
                let end = start + size;
                let previous = boundaries.last().unwrap_or(src[0]);
                let mut chain: Vec<QReg> = Vec::new();
                for bit in &src[start..end] {
                    let next = c.alloc_qreg("predicate.and");
                    c.ccx(chain.last().unwrap_or(previous), bit, &next);
                    chain.push(next);
                }
                let last = end == src.len() - 1;
                if last {
                    if let Some(out) = out { c.ccx(chain.last().unwrap(), src[end], out); }
                    else { c.cz(chain.last().unwrap(), src[end]); }
                }
                let retained = if last { None } else { chain.pop() };
                for i in (0..chain.len()).rev() {
                    let parent = if i == 0 { previous } else { &chain[i - 1] };
                    c.clear_and(&chain[i], parent, src[start + i]);
                }
                for bit in chain { c.zero_and_free(bit); }
                if let Some(bit) = retained {
                    boundaries.push(bit);
                    ranges.push((start, end));
                }
                start = end;
            }
            assert_eq!(start, src.len() - 1);
            while let Some(bit) = boundaries.pop() {
                let (start, end) = ranges.pop().unwrap();
                let previous = boundaries.last().unwrap_or(src[0]);
                let phase = c.alloc_bit();
                c.hmr(&bit, phase);
                c.zero_and_free(bit);
                c.with_condition(phase, |c| {
                    let mut chain: Vec<QReg> = Vec::new();
                    for bit in &src[start..end - 1] {
                        let next = c.alloc_qreg("predicate.phase.and");
                        c.ccx(chain.last().unwrap_or(previous), bit, &next);
                        chain.push(next);
                    }
                    c.cz(chain.last().unwrap_or(previous), src[end - 1]);
                    for i in (0..chain.len()).rev() {
                        let parent = if i == 0 { previous } else { &chain[i - 1] };
                        c.clear_and(&chain[i], parent, src[start + i]);
                    }
                    for bit in chain { c.zero_and_free(bit); }
                });
                c.free_bit(phase);
            }
        }
    }
    c.pop_section(&section);
    true
}
