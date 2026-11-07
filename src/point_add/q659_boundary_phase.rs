//! Exact column-entry/return component. The adjacent binary is built and
//! gate-tested by phase_pilot.py. Install this module inside src/point_add.
//! C=the incoming crossing tag. E=ordinary top bit length minus one when C=0.
//! target ^= C || (Q > (reversed ring top mod 2^(E+1))). Seven clean
//! temporaries and all input data are restored. The target receives the XOR.
//! On a packed column entry the eight returned S and role wires supply
//! seven temporaries and the output, while all 258 payload ports are held.
use super::builder::B;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

const GATES: &[u8] = include_bytes!("boundary_phase_128v2.bin");

pub(crate) fn xor_boundary_phase(
    b: &mut B,
    ring: &[QubitId],
    q: &[QubitId],
    e: &[QubitId; 7],
    incoming_cross: QubitId,
    clean: &[QubitId; 7],
    target: QubitId,
) {
    assert_eq!((ring.len(), q.len()), (257, 128));
    let ports: Vec<_> = ring.iter().chain(q).chain(e).copied()
        .chain([incoming_cross]).chain(clean.iter().copied())
        .chain([target]).collect();
    assert_eq!(ports.len(), 401);
    assert_eq!(ports.iter().copied().collect::<BTreeSet<_>>().len(), ports.len());
    assert_eq!(GATES.len() % 7, 0);
    for gate in GATES.chunks_exact(7) {
        let wire = |byte| {
            let index = u16::from_le_bytes([gate[byte], gate[byte + 1]]);
            ports[usize::from(index)]
        };
        match gate[0] {
            1 => b.x(wire(1)),
            2 => b.cx(wire(1), wire(3)),
            3 => b.ccx(wire(1), wire(3), wire(5)),
            _ => panic!("invalid phase-pilot program"),
        }
    }
}
