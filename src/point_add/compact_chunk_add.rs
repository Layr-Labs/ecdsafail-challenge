//! Exact wrapped addition with measured block-carry erasure. No truncated
//! comparison: each outgoing carry is reconstructed from every post-sum bit,
//! the entire source block, and the still-live incoming carry.
use super::{compare, modular, Builder};
use crate::circuit::QubitId;

pub(crate) fn workspace(source: usize, width: usize, chunk: usize, lent: bool) -> usize {
    assert!(source > 0 && source <= width && chunk > 0);
    assert!(!lent || source == width);
    if width <= chunk {
        return width.saturating_sub(2);
    }
    let zero = usize::from(source < width);
    let (mut at, mut boundaries, mut peak) = (0usize, 0usize, zero);
    while at < width {
        let end = (at + chunk).min(if at < source { source } else { width });
        let last = end == width;
        let flags = boundaries.saturating_sub(usize::from(lent));
        let extra = if last {
            (end - at).saturating_sub(2)
        } else {
            end - at - usize::from(lent && boundaries == 0)
        };
        peak = peak.max(zero + flags + extra);
        boundaries += usize::from(!last);
        at = end;
    }
    peak
}

fn and_phase(c: &mut Builder, bits: &[QubitId]) {
    assert!(bits.len() >= 2);
    if bits.len() == 2 {
        c.cz(bits[0], bits[1]);
        return;
    }
    let work = c.alloc_qubits(bits.len() - 2);
    c.ccx(bits[0], bits[1], work[0]);
    for i in 1..work.len() {
        c.ccx(work[i - 1], bits[i + 1], work[i]);
    }
    c.cz(work[work.len() - 1], bits[bits.len() - 1]);
    for i in (0..work.len()).rev() {
        let m = c.alloc_bit();
        c.hmr(work[i], m);
        let a = if i == 0 { bits[0] } else { work[i - 1] };
        c.cz_if(a, bits[i + 1], m);
        c.free_bit(m);
        c.release_clean(work[i]);
    }
}
fn erase(
    c: &mut Builder,
    flag: QubitId,
    source: &[QubitId],
    sum: &[QubitId],
    incoming: Option<QubitId>,
) {
    if !source.is_empty() && sum.len() > 1 {
        assert_eq!(source.len(), sum.len());
        compare::erase_with_compare(c, flag, sum, source, incoming);
        return;
    }
    let m = c.alloc_bit();
    c.hmr(flag, m);
    c.push_condition(m);
    c.x_all(sum);
    if source.is_empty() {
        let mut controls = sum.to_vec();
        controls.push(incoming.expect("zero source block has incoming carry"));
        and_phase(c, &controls);
    } else {
        assert_eq!(sum.len(), 1);
        c.cz(source[0], sum[0]);
        if let Some(q) = incoming {
            c.cz(source[0], q);
            c.cz(sum[0], q);
        }
    }
    c.x_all(sum);
    c.pop_condition();
    c.free_bit(m);
}
pub(crate) fn add(
    c: &mut Builder,
    a: &[QubitId],
    b: &[QubitId],
    incoming: Option<QubitId>,
    negative: bool,
    chunk: usize,
) {
    add_impl(c, a, b, incoming, negative, chunk, None);
}

pub(crate) fn add_lent(
    c: &mut Builder,
    a: &[QubitId],
    b: &[QubitId],
    incoming: Option<QubitId>,
    negative: bool,
    chunk: usize,
    lent: QubitId,
) {
    assert_eq!(a.len(), b.len());
    assert!(!a.contains(&lent) && !b.contains(&lent) && incoming != Some(lent));
    add_impl(c, a, b, incoming, negative, chunk, Some(lent));
}

fn add_impl(
    c: &mut Builder,
    a: &[QubitId],
    b: &[QubitId],
    incoming: Option<QubitId>,
    negative: bool,
    chunk: usize,
    lent: Option<QubitId>,
) {
    assert!(!a.is_empty() && a.len() <= b.len() && chunk >= 1);
    if negative {
        c.x_all(b);
    }
    if b.len() <= chunk {
        modular::ripple_add(c, a, b, incoming, None);
        if negative {
            c.x_all(b);
        }
        return;
    }
    // End a source block exactly at a.len(); no repeated zero aliases enter a
    // comparison. Above it, one clean zero is reused by the native ripple.
    let zero = if a.len() < b.len() {
        Some(c.alloc_qubit())
    } else {
        None
    };
    let mut stages = Vec::new();
    let mut at = 0;
    let mut previous = incoming;
    while at < b.len() {
        let end = (at + chunk).min(if at < a.len() { a.len() } else { b.len() });
        let flag = if end < b.len() {
            Some(if at == 0 {
                lent.unwrap_or_else(|| c.alloc_qubit())
            } else {
                c.alloc_qubit()
            })
        } else {
            None
        };
        let zeros: Vec<_> = zero.into_iter().collect();
        let source = if at < a.len() { &a[at..end] } else { &zeros };
        modular::ripple_add(c, source, &b[at..end], previous, flag);
        if let Some(q) = flag {
            stages.push((at, end, previous, q));
        }
        previous = flag;
        at = end;
    }
    // Descending order preserves each incoming boundary until its successor's
    // measurement phase is repaired. Then its own exact predicate is erased.
    for (at, end, prev, q) in stages.into_iter().rev() {
        let source = if at < a.len() { &a[at..end] } else { &[] };
        erase(c, q, source, &b[at..end], prev);
        if Some(q) != lent {
            c.release_clean(q);
        }
    }
    if let Some(q) = zero {
        c.release_clean(q);
    }
    if negative {
        c.x_all(b);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::{digest::ExtendableOutput, Shake256};

    #[test]
    fn workspace_matches_actual_full_and_zero_extended_ladders() {
        for width in 1..=14 {
            for source in 1..=width {
                for chunk in 1..=width {
                    for lent in [false, true] {
                        if lent && source != width {
                            continue;
                        }
                        let mut circ = Builder::new();
                        let a = circ.alloc_qubits(source);
                        let b = circ.alloc_qubits(width);
                        let incoming = circ.alloc_qubit();
                        let loan = lent.then(|| circ.alloc_qubit());
                        let base = circ.active_qubits();
                        add_impl(&mut circ, &a, &b, Some(incoming), false, chunk, loan);
                        assert_eq!(circ.active_qubits(), base);
                        let actual = analyze_ops(circ.take_ops().iter())
                            .0
                            .saturating_sub(base as u64);
                        assert_eq!(
                            actual as usize,
                            workspace(source, width, chunk, lent),
                            "source={source}, width={width}, chunk={chunk}, lent={lent}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn borrowed_boundary_is_restored_with_exact_add_and_subtract() {
        for width in 2..=5 {
            for chunk in 1..width {
                for negative in [false, true] {
                    let mut circ = Builder::new();
                    let a = circ.alloc_qubits(width);
                    let b = circ.alloc_qubits(width);
                    let incoming = circ.alloc_qubit();
                    let loan = circ.alloc_qubit();
                    add_lent(&mut circ, &a, &b, Some(incoming), negative, chunk, loan);
                    let ops = circ.take_ops();
                    let (nq, nb, _, _) = analyze_ops(ops.iter());
                    let mask = (1usize << width) - 1;
                    let assignments = 1usize << (2 * width + 1);
                    for start in (0..assignments).step_by(64) {
                        let mut rng = Shake256::default().finalize_xof();
                        let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
                        let mut expected_sum = vec![0; width];
                        for lane in 0..64.min(assignments - start) {
                            let assignment = start + lane;
                            let x = assignment & mask;
                            let y = (assignment >> width) & mask;
                            let carry = (assignment >> (2 * width)) & 1;
                            let sum = if negative {
                                y.wrapping_sub(x + carry)
                            } else {
                                y + x + carry
                            } & mask;
                            for bit in 0..width {
                                sim.qubits[a[bit].0 as usize] |= (((x >> bit) & 1) as u64) << lane;
                                sim.qubits[b[bit].0 as usize] |= (((y >> bit) & 1) as u64) << lane;
                                expected_sum[bit] |= (((sum >> bit) & 1) as u64) << lane;
                            }
                            sim.qubits[incoming.0 as usize] |= (carry as u64) << lane;
                        }
                        let mut expected = sim.qubits.clone();
                        for bit in 0..width {
                            expected[b[bit].0 as usize] = expected_sum[bit];
                        }
                        sim.apply_iter(ops.iter());
                        assert_eq!(
                            sim.qubits, expected,
                            "width={width}, chunk={chunk}, negative={negative}"
                        );
                        assert_eq!(sim.phase, 0);
                    }
                }
            }
        }
    }
}
