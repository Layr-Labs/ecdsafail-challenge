//! Cancel equal reversible gates through a run of proved-commuting quantum gates.
use crate::circuit::{Op, OperationType as K, QubitId, NO_QUBIT};

const WIRES: usize = 2048;
const CACHE: usize = 1 << 14;
const ABSENT: u64 = u64::MAX;

pub(super) struct Pairs {
    cache: Vec<usize>,
    reads: Vec<usize>,
    writes: Vec<usize>,
    alive: Vec<bool>,
}

impl Pairs {
    pub(super) fn new() -> Self {
        Self {
            cache: vec![0; CACHE],
            reads: vec![0; WIRES],
            writes: vec![0; WIRES],
            alive: Vec::new(),
        }
    }

    // Both X-type permutations and their diagonal phases are involutions.
    // A Toffoli's control order and a phase gate's entire wire order are immaterial.
    fn canonical(mut g: Op) -> Option<Op> {
        match g.kind {
            K::Neg | K::X | K::Z | K::CX => {}
            K::CCX => {
                if g.q_control1.0 > g.q_control2.0 {
                    std::mem::swap(&mut g.q_control1, &mut g.q_control2);
                }
            }
            K::CZ => {
                if g.q_control1.0 > g.q_target.0 {
                    std::mem::swap(&mut g.q_control1, &mut g.q_target);
                }
            }
            K::CCZ => {
                let mut q = [g.q_control1.0, g.q_control2.0, g.q_target.0];
                q.sort_unstable();
                [g.q_control1, g.q_control2, g.q_target] = q.map(QubitId);
            }
            _ => return None,
        }
        Some(g)
    }

    fn slot(g: Op) -> usize {
        let [a, b, t, c] = [
            g.q_control2.0,
            g.q_control1.0,
            g.q_target.0,
            g.c_condition.0,
        ];
        let key = (g.kind as u64)
            ^ a.wrapping_mul(0x9e3779b97f4a7c15)
            ^ b.wrapping_mul(0x94d049bb133111eb)
            ^ t.wrapping_mul(0xbf58476d1ce4e5b9)
            ^ c.wrapping_mul(0x2545f4914f6cdd1d);
        ((key ^ (key >> 31)) as usize) & (CACHE - 1)
    }

    pub(super) fn reduce(&mut self, gates: &mut Vec<Op>) -> (usize, u64) {
        self.cache.fill(0);
        self.reads.fill(0);
        self.writes.fill(0);
        self.alive.clear();
        self.alive.resize(gates.len(), true);
        let mut barrier = 0;
        let mut pairs = 0;
        let mut charged = 0;
        for i in 0..gates.len() {
            let Some(g) = Self::canonical(gates[i]) else {
                barrier = i + 1;
                continue;
            };
            // Unknown wire ranges and non-unitary/classical boundaries cut the scan.
            let wires = [g.q_control2.0, g.q_control1.0, g.q_target.0];
            if wires.iter().any(|&q| q != ABSENT && q >= WIRES as u64) {
                barrier = i + 1;
                continue;
            }
            let toggles = matches!(g.kind, K::X | K::CX | K::CCX);
            let mut stop = barrier;
            for j in 0..3 {
                if wires[j] == ABSENT {
                    continue;
                }
                let q = wires[j] as usize;
                if toggles && j == 2 {
                    stop = stop.max(self.reads[q]);
                } else {
                    stop = stop.max(self.writes[q]);
                }
            }
            let slot = Self::slot(g);
            let old = self.cache[slot];
            if old != 0
                && old > barrier
                && old >= stop
                && self.alive[old - 1]
                && Self::canonical(gates[old - 1]) == Some(g)
            {
                self.alive[old - 1] = false;
                self.alive[i] = false;
                self.cache[slot] = 0;
                pairs += 1;
                charged += 2 * u64::from(matches!(g.kind, K::CCX | K::CCZ));
                // Leaving historical dependency stamps in place is conservative.
                continue;
            }
            self.cache[slot] = i + 1;
            for j in 0..3 {
                if wires[j] == ABSENT {
                    continue;
                }
                let q = wires[j] as usize;
                if toggles && j == 2 {
                    self.writes[q] = i + 1;
                } else {
                    self.reads[q] = i + 1;
                }
            }
        }
        if pairs > 0 {
            let mut out = 0;
            for i in 0..gates.len() {
                if self.alive[i] {
                    gates[out] = gates[i];
                    out += 1;
                }
            }
            gates.truncate(out);
        }
        (2 * pairs, charged)
    }
}
