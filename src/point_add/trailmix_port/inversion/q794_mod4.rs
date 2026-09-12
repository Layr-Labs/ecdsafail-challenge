//! Experimental two-residue-bit chart. This module is NOT a whole-Q794 integration.
//!
//! p mod4=3 and t*r+u*v+q*t*v=p. Store (t,b,v,q) mod4, with b=u
//! for odd t and b=r for even t. Odd t is invertible modulo4; even t
//! forces u and v odd, so v is invertible. No extra chart tag is needed.
//! The cycle primitive below only handles the exact q=0 exit boundary.
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use crate::point_add::trailmix_port::inversion::length_recompute::mixed_mcx;
pub(crate) fn enabled() -> bool {
    std::env::var("Q794_MOD4").ok().as_deref() == Some("1")
}

fn decode(code: usize) -> (usize, usize, usize, usize) {
    let t = code & 3;
    let b = code >> 2 & 3;
    let v = code >> 4 & 3;
    if t & 1 != 0 {
        let u = b;
        let r = ((3usize.wrapping_sub(u * v)).wrapping_mul(t)) & 3;
        (t, u, r, v)
    } else {
        assert_eq!(v & 1, 1);
        let r = b;
        let u = ((3usize.wrapping_sub(t * r)).wrapping_mul(v)) & 3;
        (t, u, r, v)
    }
}

fn permutation() -> [usize; 64] {
    let mut permutation = std::array::from_fn(|i| i);
    for code in 0..64 {
        let t = code & 3;
        let v = code >> 4 & 3;
        if (t | v) & 1 == 0 {
            continue; // Fixed extension on the16 unreachable codes.
        }
        let (t, u, r, v) = decode(code);
        assert_eq!((t * r + u * v) & 3, 3);
        // New semantic tuple is (u,t,v,r); select its chart from u parity.
        let b_new = if u & 1 != 0 { t } else { v };
        permutation[code] = u | (b_new << 2) | (r << 4);
    }
    let mut sorted = permutation;
    sorted.sort_unstable();
    assert_eq!(sorted, std::array::from_fn(|i| i));
    assert!((0..64).all(|i| permutation[permutation[i]] == i));
    permutation
}

/// Controlled q=0 cycle exit on [t0,t1,b0,b1,v0,v1].
/// All six chart wires, the guard and >=4 dirty lenders must be distinct.
/// It acts as identity off guard and fixes invalid chart codes. It creates
/// no clean qubit and never materializes either omitted remainder bit.
pub(crate) fn cycle_swap(
    circ: &mut Circuit,
    word: [&QReg; 6],
    guard: &QReg,
    dirty: &[QReg],
) {
    assert!(dirty.len() >= 4);
    let mut ids: Vec<_> = word.iter().map(|q| q.id()).collect();
    ids.push(guard.id());
    ids.extend(dirty.iter().map(QReg::id));
    ids.sort_unstable();
    assert!(ids.windows(2).all(|pair| pair[0] != pair[1]));
    let owned = circ.b.next_qubit;
    let permutation = permutation();
    for (left, &right) in permutation.iter().enumerate() {
        if left >= right {
            continue;
        }
        let mut value = left;
        let mut path = Vec::new();
        for bit in 0..6 {
            if (left ^ right) >> bit & 1 != 0 {
                path.push((bit, value));
                value ^= 1 << bit;
            }
        }
        assert_eq!(value, right);
        let mut edges = path.clone();
        edges.extend(path[..path.len() - 1].iter().rev().copied());
        for (bit, value) in edges {
            let mut controls = vec![(guard, true)];
            controls.extend((0..6).filter(|&i| i != bit).map(|i| {
                (word[i], value >> i & 1 != 0)
            }));
            mixed_mcx(circ, &controls, word[bit], dirty);
        }
    }
    assert_eq!(circ.b.next_qubit, owned);
}

pub fn run() {
    use crate::{circuit::OperationType, sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;
    impl XofReader for Fixed {
        fn read(&mut self, bytes: &mut [u8]) { bytes.fill(0x69); }
    }
    let mut circ = Circuit::new();
    circ.b.count_only = false;
    circ.b.fiat_hash = None;
    let chart = circ.alloc_qreg_bits("mod4.chart", 6);
    let guard = circ.alloc_qreg("mod4.guard");
    let dirty = circ.alloc_qreg_bits("mod4.dirty", 4);
    let owned = circ.b.next_qubit;
    cycle_swap(&mut circ, std::array::from_fn(|i| &chart[i]), &guard, &dirty);
    assert_eq!(circ.b.next_qubit, owned);
    let builder = circ.into_builder();
    for op in &builder.ops {
        op.validate();
        assert!(matches!(op.kind, OperationType::X | OperationType::CX | OperationType::CCX));
    }
    let t = builder.ops.iter().filter(|op| op.kind == OperationType::CCX).count();
    assert_eq!(t, 2048);
    let permutation = permutation();
    let mut lanes = 0;
    for on in 0..2 {
        for lender_pattern in 0..16 {
            let mut before = vec![0u64; owned as usize];
            let mut expected = before.clone();
            for lane in 0..64 {
                let result = if on != 0 { permutation[lane] } else { lane };
                for (word, value) in [(&mut before, lane), (&mut expected, result)] {
                    for bit in 0..6 {
                        word[chart[bit].id() as usize] |= (((value >> bit) & 1) as u64) << lane;
                    }
                    word[guard.id() as usize] |= (on as u64) << lane;
                    for bit in 0..4 {
                        word[dirty[bit].id() as usize] |= (((lender_pattern >> bit) & 1) as u64) << lane;
                    }
                }
            }
            let mut random = Fixed;
            let mut sim = Simulator::new(owned as usize, 0, &mut random);
            sim.qubits.copy_from_slice(&before);
            sim.apply_iter(builder.ops.iter());
            assert_eq!(sim.qubits, expected, "mod4 on={on} dirty={lender_pattern}");
            assert_eq!(sim.phase, 0);
            sim.apply_iter(builder.ops.iter().rev());
            assert_eq!(sim.qubits, before);
            assert_eq!(sim.phase, 0);
            lanes += 64;
        }
    }
    eprintln!("Q794_MOD4_CYCLE_PASS lanes={lanes} ops={} T={t} allocated_delta=0 chart_wires=6 dirty_wires=4; all64codes, bothguards, all16lenderpatterns, exactphase andliteralinverse; NOT wholeQ795", builder.ops.len());
}

