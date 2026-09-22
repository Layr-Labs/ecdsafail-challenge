//! Gather only the prefix read by a scan, then undo the entire permutation.
//!
//! For a right rotation by a quantum amount, after processing bit i the
//! remaining offset is at most 2^i-1. Thus only the first window+2^i-1
//! positions can still influence the answer. Higher bits run first; each
//! successive layer can rotate a smaller prefix. Before bit i its required
//! prefix is min(ring.len(), window+2^(i+1)-1). Padding that prefix can reduce
//! the number of swaps through a larger gcd, but never discards a needed bit.
//! Only the output window equals a full rotation. The rest is restored by
//! the explicit inverse, not assumed to be zero or a classical remapping.
//! Within each layer only its live output prefix is constrained. Complete
//! the resulting disjoint paths into cycles instead of rotating dead outputs.

use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 { (a, b) = (b, a % b); }
    a
}

fn layers(width: usize, window: usize, bits: usize) -> Vec<(usize, usize, usize)> {
    assert!(window > 0 && window <= width);
    (0..bits).rev().map(|bit| {
        let shift = 1usize << bit;
        let need = width.min(window + 2 * shift - 1);
        let length = (need..=width)
            .min_by_key(|&n| (n - gcd(n, shift), n)).unwrap();
        (bit, length, width.min(window + shift - 1))
    }).collect()
}

pub(crate) fn toffoli(width: usize, window: usize, bits: usize) -> usize {
    layers(width, window, bits).iter()
        .map(|&(bit, n, live)| live.min(n - gcd(n, 1usize << bit))).sum()
}

// Required edges j -> j+shift for j<live form disjoint paths and cycles.
// Closing each path arbitrarily preserves every required output and uses
// one swap per edge; a closed cycle saves one more swap.
fn layer_swaps(n: usize, shift: usize, live: usize) -> Vec<(usize, usize)> {
    assert!(live <= n);
    let shift = shift % n;
    let mut incoming = vec![false; n];
    for j in 0..live { incoming[(j + shift) % n] = true; }
    let mut seen = vec![false; n];
    let starts: Vec<usize> = (0..live).filter(|&j| !incoming[j])
        .chain(0..live).collect();
    let mut swaps = Vec::new();
    for start in starts {
        if seen[start] { continue; }
        seen[start] = true;
        let mut j = start;
        while j < live {
            j = (j + shift) % n;
            if j == start { break; }
            assert!(!seen[j], "partial rotation components must be disjoint");
            seen[j] = true;
            swaps.push((start, j));
        }
    }
    assert_eq!(swaps.len(), live.min(n - gcd(n, shift)));
    swaps
}

pub(crate) fn enabled() -> bool {
    std::env::var("MIDQ_PACKED_WINDOW_GATHER").ok().as_deref() != Some("0")
}

pub(crate) fn gather(
    c: &mut Circuit, ring: &[&QReg], amount: &[QReg], window: usize, inverse: bool,
) {
    let sec = c.push_section("p.window_gather");
    let mut plan = layers(ring.len(), window, amount.len());
    if inverse { plan.reverse(); }
    for (bit, n, live) in plan {
        let mut swaps = layer_swaps(n, 1usize << bit, live);
        if !inverse { swaps.reverse(); }
        for (a, b) in swaps { c.cswap(&amount[bit], ring[a], ring[b]); }
    }
    c.pop_section(&sec);
}

pub(crate) fn selftest() {
    use crate::circuit::{analyze_ops, OperationType, QubitId};
    use crate::sim::Simulator;
    use sha3::{Shake256, digest::{Update, ExtendableOutput}};
    let mut checked = 0usize;
    let mut shapes: Vec<(usize, usize, usize)> = (2..=20)
        .flat_map(|w| (1..=w).map(move |n| (w, n, 5))).collect();
    for width in [32, 33, 63, 64, 65, 78, 79, 95, 96, 109, 110, 111,
                  112, 127, 128, 129, 159, 160, 255, 256, 257] {
        for window in [1, 7, 16, 32] {
            shapes.push((width, window, 7));
        }
    }
    for &(w, n, k) in &shapes {
        let mut c = Circuit::new();
        let data = c.alloc_qreg_bits("gather.test.data", w + 2);
        let amount = c.alloc_qreg_bits("gather.test.amount", k);
        let ring: Vec<&QReg> = data[1..w+1].iter().collect();
        gather(&mut c, &ring, &amount, n, false);
        let forward = c.b.ops.clone();
        let split = forward.len();
        gather(&mut c, &ring, &amount, n, true);
        let inverse = &c.b.ops[split..];
        let t = forward.iter().filter(|op| op.kind == OperationType::CCX).count();
        assert_eq!(t, toffoli(w, n, k));
        assert!(forward.iter().all(|op| matches!(op.kind, OperationType::CX | OperationType::CCX)));
        let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
        assert_eq!(c.b.active_qubits as usize, w + 2 + k, "no scratch");
        let mut seed = Shake256::default();
        seed.update(b"packed-window-gather-structural12");
        let mut rng = seed.finalize_xof();
        let cases = (1usize << k) * w;
        for start in (0..cases).step_by(64) {
            let count = 64.min(cases - start);
            let mask = u64::MAX >> (64 - count);
            let mut sim = Simulator::new((nq as usize).max(w + 2 + k), (nb as usize).max(1), &mut rng);
            for lane in 0..count {
                let case = start + lane;
                let (shift, hot) = (case / w, case % w);
                *sim.qubit_mut(QubitId(data[hot + 1].id().into())) |= 1u64 << lane;
                // Both foreign neighbours are dirty and must survive.
                *sim.qubit_mut(QubitId(data[0].id().into())) |= 1u64 << lane;
                *sim.qubit_mut(QubitId(data[w+1].id().into())) |= 1u64 << lane;
                for (bit, q) in amount.iter().enumerate() {
                    if shift >> bit & 1 != 0 {
                        *sim.qubit_mut(QubitId(q.id().into())) |= 1u64 << lane;
                    }
                }
            }
            let original = sim.qubits.clone();
            sim.apply_iter(forward.iter());
            assert_eq!(sim.phase & mask, 0);
            for lane in 0..count {
                let case = start + lane;
                let (shift, hot) = (case / w, case % w);
                for j in 0..n {
                    let got = sim.qubit(QubitId(data[j+1].id().into())) >> lane & 1;
                    assert_eq!(got, u64::from((j + shift) % w == hot),
                               "w={w} n={n} shift={shift} hot={hot} j={j}");
                }
            }
            sim.apply_iter(inverse.iter());
            assert_eq!(sim.phase & mask, 0);
            assert_eq!(sim.qubits, original, "all wires restored w={w} n={n}");
            checked += count;
        }
    }
    eprintln!("PACKED_WINDOW_GATHER PASS {checked} one-hot/amount cases, {} shapes, all wires/inverse/phase, no scratch", shapes.len());
}
