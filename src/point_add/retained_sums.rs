//! Separate canonical lookup from storage of recent immutable XOR definitions.
//! A definition is evicted only when a full turn of new sum insertions reuses its slot.
//! A live wire may retain an older value ID indefinitely, even after its expansion
//! is forgotten. An exact identifier check is required before using an expansion.
use super::{mix, State, Sum, Value, Values};

pub(super) struct Retention {
    by_hash: Vec<Value>,
    next_slot: usize,
}

impl<const N: usize> State<N> {
    pub(crate) fn enable_retention(&mut self) {
        let slots = self.v.mask + 1;
        self.v.products.resize(4 * slots, (0, 0, 0));
        self.v.large_xors.resize(4 * slots, (0, 0, 0));
        self.v.retention = Some(Retention {
            by_hash: vec![0; 4 * slots],
            next_slot: 0,
        });
    }
}

impl<const N: usize> Values<N> {
    pub(super) fn retained_pair(&mut self, a: Value, b: Value, and: bool) -> Value {
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        let table = if and {
            &self.products
        } else {
            &self.large_xors
        };
        let mask = table.len() - 1;
        let first = mix(a ^ b.rotate_left(23)) as usize & mask;
        let mut destination = first;
        for offset in 0..4 {
            let slot = (first + offset) & mask;
            let (left, right, id) = table[slot];
            if id != 0 && left == a && right == b {
                return id;
            }
            if id == 0 {
                destination = slot;
                break;
            }
        }
        let id = self.fresh();
        let table = if and {
            &mut self.products
        } else {
            &mut self.large_xors
        };
        table[destination] = (a, b, id);
        id
    }

    pub(super) fn retained_sum(&mut self, sum: Sum<N>, hash: u64, sign: Value) -> Value {
        let retained = self.retention.as_ref().unwrap();
        let mask = retained.by_hash.len() - 1;
        let first = mix(hash) as usize & mask;
        let mut vacancy = None;
        for offset in 0..4 {
            let slot = (first + offset) & mask;
            let candidate = retained.by_hash[slot];
            let (id, definition) = &self.sums[(candidate as usize >> 1) & self.mask];
            if candidate == 0 || *id != candidate {
                vacancy.get_or_insert(slot);
            } else if definition.terms[..definition.len] == sum.terms[..sum.len] {
                return candidate ^ sign;
            }
        }
        let ring_slot = retained.next_slot;
        let name = self.fresh() | ((ring_slot as u64) << 1);
        self.sums[ring_slot] = (name, sum);
        let retained = self.retention.as_mut().unwrap();
        retained.by_hash[vacancy.unwrap_or(first)] = name;
        retained.next_slot = (ring_slot + 1) & self.mask;
        name ^ sign
    }
}
