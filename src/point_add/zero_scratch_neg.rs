//! A low-memory fallback using two zero-ancilla additions per increment.
use crate::point_add::trailmix_port::arith::gidney_const_adder::controlled_hybrid_add_refs;
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

fn update(c: &mut Circuit, g: &QReg, a: &[QReg], donor: &[QReg], increment: bool) {
    if a.is_empty() { return; }
    if a.len() == 1 { c.cx(g, &a[0]); return; }
    let source: Vec<_> = donor[..a.len()].iter().collect();
    let target: Vec<_> = a.iter().collect();
    if increment { for bit in a { c.x(bit); } }
    // D + NOT D = -1 modulo2^n, even for an arbitrary quantum donor.
    controlled_hybrid_add_refs(c, g, &target, &source, 0);
    for bit in &source { c.x(bit); }
    controlled_hybrid_add_refs(c, g, &target, &source, 0);
    for bit in &source { c.x(bit); }
    if increment { for bit in a { c.x(bit); } }
}

pub(crate) fn try_apply(c: &mut Circuit, g: &QReg, a: &[QReg], donor: &[QReg]) -> bool {
    if std::env::var("MIDQ_ZERO_SCRATCH_NEG").ok().as_deref() != Some("1")
        || !matches!(a.len(), 256 | 257) || donor.len() < a.len() - 4 { return false; }
    c.flush_pending_frees();
    let cap = std::env::var("MIDQ_ZERO_SCRATCH_QCAP").ok()
        .and_then(|v| v.parse::<usize>().ok()).unwrap_or(1009);
    if c.b.active_qubits as usize + 2 <= cap { return false; }
    let mut ids = std::collections::HashSet::new();
    if a.iter().chain(donor.iter().take(a.len() - 4))
        .any(|q| q.id() == g.id() || !ids.insert(q.id())) { return false; }
    let before = c.b.active_qubits;
    let section = c.push_section("zero_scratch.field_neg");
    for bit in a { c.cx(g, bit); }
    // p+1 =2^256-2^32-2^10+2^5+2^4. Preserve the full existing word width.
    if a.len() == 257 { c.cx(g, &a[256]); }
    for (start, increment) in [(32, false), (10, false), (5, true), (4, true)] {
        update(c, g, &a[start..], donor, increment);
    }
    c.flush_pending_frees();
    assert_eq!(before, c.b.active_qubits);
    c.pop_section(&section);
    true
}

pub(crate) fn selftest() {
    use crate::circuit::{analyze_ops, QubitId};
    use crate::sim::Simulator;
    use sha3::{digest::{ExtendableOutput, Update}, Shake256};
    let mut checked = 0;
    for n in 1usize..=7 {
        for increment in [false, true] {
            let mut c = Circuit::new();
            let a = c.alloc_qreg_bits("test.a", n);
            let donor = c.alloc_qreg_bits("test.donor", n);
            let g = c.alloc_qreg("test.g");
            update(&mut c, &g, &a, &donor, increment);
            assert_eq!(c.b.peak_qubits as usize, 2 * n + 1);
            let ids: Vec<_> = a.iter().chain(&donor).chain([&g]).map(|q| QubitId(q.id().into())).collect();
            let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
            let nq = nq.max(ids.iter().map(|q| q.0 + 1).max().unwrap());
            let mut hash = Shake256::default(); hash.update(b"zero-scratch-increment-v1");
            let mut rng = hash.finalize_xof();
            let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
            let mask = (1usize << n) - 1;
            for first in (0..1usize << (2 * n + 1)).step_by(64) {
                sim.clear_for_shot();
                let valid = 64.min((1usize << (2 * n + 1)) - first);
                let live = u64::MAX >> (64 - valid);
                for (bit, &id) in ids.iter().enumerate() {
                    for shot in 0..valid { *sim.qubit_mut(id) |= (((first + shot) >> bit & 1) as u64) << shot; }
                }
                sim.apply_iter(c.b.ops.iter());
                assert_eq!(sim.phase & live, 0);
                for shot in 0..valid {
                    let input = first + shot;
                    let old = input & mask;
                    let new = if input >> (2 * n) == 0 { old }
                        else if increment { old.wrapping_add(1) & mask }
                        else { old.wrapping_sub(1) & mask };
                    let want = (input & !mask) | new;
                    for (bit, &id) in ids.iter().enumerate() {
                        assert_eq!(sim.qubit(id) >> shot & 1, (want >> bit & 1) as u64);
                    }
                }
                checked += valid;
            }
        }
    }
    eprintln!("ZERO_SCRATCH_INCREMENT PASS: {checked} exhaustive target/donor/control/direction states, phase and no added qubits");
}
