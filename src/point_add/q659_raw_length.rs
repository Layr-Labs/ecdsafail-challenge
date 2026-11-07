//! XOR the high bit of E=bit_length(Y)-1 on a raw positive-Y port.
//! Precondition: Q[E] is the physical leading one, data above it is zero
//! apart from up to 30 quotient parks at Q[E+1..]. A DONE counter, a
//! normalized frame or a temporarily borrowed leading cell requires its own
//! guard. No persistent E[6] is a port. E.low6, every Q lane and an arbitrary
//! initial target are restored except for the specified target toggle.
use super::builder::B;
use crate::circuit::QubitId;

pub(crate) fn xor_raw_length_high(b: &mut B, low: &[QubitId; 6], q: &[QubitId], target: QubitId) {
    assert_eq!(q.len(), 128);
    let mut ports = std::collections::BTreeSet::new();
    assert!(q.iter().chain(low.iter()).copied().chain([target]).all(|v| ports.insert(v)));
    let leaves: Vec<_> = (0..64).map(|i| (i, q[64 + i])).collect();
    let mut swaps = Vec::new();
    let selected = super::midg::swap_tree(low, &leaves, 6, &mut swaps);
    for &(bit, left, right) in &swaps { b.cswap(bit, left, right); }
    b.cx(selected, target);
    for &(bit, left, right) in swaps.iter().rev() { b.cswap(bit, left, right); }
}
