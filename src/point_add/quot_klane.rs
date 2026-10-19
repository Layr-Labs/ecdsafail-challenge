//! agent_lowq_quot: K-lane reciprocal remainder with the divisor's virtual zero top (stacks on the 694's virtual zero).
//!
//! stage1_v keeps R in K + 1 lanes because each iteration rotates first: the rotated-in zero lane is the compare's
//! carry-in and then takes the new low bit. Here R keeps K lanes: compare-and-subtract S = Zh >> 1 (K - 1 lanes, the
//! top source bit virtual zero) first, with ancilla-free Takahashi-Tani-Kunihiro carries (no carry-in lane, one
//! borrowed dirty lane); afterwards R < 2^(K-1), so the zero top lane rotates in as the new low bit !f.
//! Remainder sequence R' = 2R + 1 - f (2S + 1), identical to stage1_v; the window additions are unchanged.
use super::builder::B;
use crate::circuit::QubitId;

/// f ^= [R >= S] (f clean on entry), then R -= f S. R has K lanes, S the K - 1 low lanes of a K-lane operand whose
/// top bit is zero (virtual). `d` is a borrowed dirty lane (restored). S restored.
pub fn cmp_csub_ttk_vz(b: &mut B, r: &[QubitId], s: &[QubitId], f: QubitId, d: QubitId) {
    let k = r.len();
    assert_eq!(s.len() + 1, k);
    assert!(k >= 3);
    let (low, top) = (&r[..k - 1], r[k - 1]);
    for &x in r { b.x(x); }
    // carry out of ~R + S over K bits = ~R_top & carry out of the low K - 1 bits (S's top is zero): [S > R]
    super::arith::ttk_carry(b, s, low, top, f, d);
    b.x(f);
    // ~R += f S: the low K - 1 bits, the carry into the top bit through the flag
    super::arith::ttk_add(b, s, low, Some(f), Some((top, d)));
    for &x in r { b.x(x); }
}

/// agent_lowq_quot (the virtual leading one of jackylee0424's 693, sub 261d4e06, on the K-lane TTK form): f ^= [R >= S]
/// (f clean on entry), then R -= f S, with S = 2^(K-2) + S_low: R has K lanes, `s_low` the K - 2 low lanes of the
/// aligned divisor head; its bit K - 2 (the head's leading one on every act shot) is a virtual one, bit K - 1 the
/// virtual zero. `d`: two borrowed dirty lanes (restored).
pub fn cmp_csub_ttk_vh1(b: &mut B, r: &[QubitId], s_low: &[QubitId], f: QubitId, d: &[QubitId]) {
    let k = r.len();
    assert_eq!(s_low.len() + 2, k);
    assert!(k >= 4 && d.len() >= 2);
    let (low, a, z) = (&r[..k - 2], r[k - 2], r[k - 1]);
    let (d0, d1) = (d[0], d[1]);
    for &x in r { b.x(x); }
    // [S > R] = carry out of ~R + S = z & (a | c) = z & a ^ (z & !a) & c, c = carry(~R_low + S_low)
    b.ccx(z, a, f);
    let za = |b: &mut B| { b.x(a); b.ccx(z, a, d0); b.x(a); };
    super::arith::ttk_carry(b, s_low, low, d0, f, d1);
    za(b);
    super::arith::ttk_carry(b, s_low, low, d0, f, d1);
    za(b);
    b.x(f);
    // ~R += f S: ~R_low += f S_low (its carry c' = f & c into a), then z ^= a & c' = !a' & f & c (c recomputed as
    // [~R_low' < S_low] = carry(~(~R_low') + S_low)), then (a, z) += f (the virtual one)
    super::arith::ttk_add(b, s_low, low, Some(f), Some((a, d1)));
    let fa = |b: &mut B| { b.x(a); b.ccx(f, a, d0); b.x(a); };
    for &x in low { b.x(x); }
    super::arith::ttk_carry(b, s_low, low, d0, z, d1);
    fa(b);
    super::arith::ttk_carry(b, s_low, low, d0, z, d1);
    fa(b);
    for &x in low { b.x(x); }
    b.ccx(f, a, z);
    b.cx(f, a);
    for &x in r { b.x(x); }
}

/// Encode the quotient flag in R's top lane on the reciprocal support
/// R < 2S, S = 2^(k-2) + s_low. The top lane and [R_low >= S] are disjoint.
#[cfg(test)]
fn cmp_csub_ttk_vh1_inplace_old(b: &mut B, r: &[QubitId], s_low: &[QubitId], d: &[QubitId]) {
    let k = r.len();
    assert_eq!(s_low.len() + 2, k);
    assert!(k >= 4 && d.len() >= 2);
    let (low, a, z) = (&r[..k - 2], r[k - 2], r[k - 1]);
    for &q in low { b.x(q); }
    super::arith::ttk_carry(b, s_low, low, a, z, d[0]);
    for &q in low { b.x(q); }
    b.cx(a, z);
    for &q in &r[..k - 1] { b.x(q); }
    super::arith::ttk_add(b, s_low, low, Some(z), Some((a, d[1])));
    b.cx(z, a);
    for &q in &r[..k - 1] { b.x(q); }
}

/// Fused virtual-leading-one compare and conditional subtract. The add's
/// carry chain also supplies the comparison bit, so it is formed only once.
pub fn cmp_csub_ttk_vh1_inplace(b: &mut B, r: &[QubitId], s_low: &[QubitId], d: &[QubitId]) {
    let k = r.len();
    assert_eq!(s_low.len() + 2, k);
    assert!(k >= 4 && !d.is_empty());
    let (low, a, z) = (&r[..k - 2], r[k - 2], r[k - 1]);
    let n = low.len();
    let (t, aa, dd) = (low, s_low, d[0]);
    for &q in low { b.x(q); }
    for i in 1..n { b.cx(aa[i], t[i]); }
    b.ccx(a, aa[n - 1], z);
    for i in (1..n - 1).rev() { b.cx(aa[i], aa[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], aa[i], aa[i + 1]); }
    b.ccx(aa[n - 1], dd, z); b.ccx(a, t[n - 1], dd);
    b.ccx(aa[n - 1], dd, z); b.ccx(a, t[n - 1], dd);
    b.cx(a, z); b.cx(z, a);
    b.ccx(aa[n - 1], dd, a); b.ccx(z, t[n - 1], dd);
    b.ccx(aa[n - 1], dd, a); b.ccx(z, t[n - 1], dd);
    for i in (1..n).rev() { b.ccx(z, aa[i], t[i]); b.ccx(t[i - 1], aa[i - 1], aa[i]); }
    for i in 1..n - 1 { b.cx(aa[i], aa[i + 1]); }
    b.ccx(z, aa[0], t[0]);
    for i in 1..n { b.cx(aa[i], t[i]); }
    b.ccx(z, aa[n - 1], a);
    for &q in low { b.x(q); }
}

/// Use returned clean lanes for the virtual-leading-one comparator, then pack its
/// flag into the now-zero top of R. The temporary flag lane is returned clean.
pub fn cmp_csub_clean_vh1_inplace(b: &mut B, r: &[QubitId], s_low: &[QubitId],
                                  bank: &[QubitId], dirty: &[QubitId]) {
    assert_eq!(r.len(), s_low.len() + 2);
    assert!(bank.len() >= 2 && !dirty.is_empty());
    let flag = bank[0];
    let one = bank[1];
    b.x(one);
    let s: Vec<QubitId> = s_low.iter().copied().chain([one]).collect();
    if bank.len() >= 3 {
        super::frogdrop::cmp_csub_carries_vz(b, r, &s, bank[2], flag, &bank[3..]);
    } else {
        cmp_csub_ttk_vz(b, r, &s, flag, dirty[0]);
    }
    b.x(one);
    let top = r[r.len() - 1];
    b.cx(flag, top);
    b.cx(top, flag);
}

#[cfg(test)]
mod b2_inplace_tests {
    use super::*;
    use crate::sim::Simulator;

    #[test]
    fn b8a_fused_ttk_all_wire_forward_inverse_dirty() {
        use sha3::digest::{ExtendableOutput, Update};
        let mut b = B::new();
        let r = b.alloc_n(24);
        let s_low = b.alloc_n(22);
        let dirty = b.alloc_n(14);
        b.begin();
        cmp_csub_ttk_vh1_inplace_old(&mut b, &r, &s_low, &dirty[..2]);
        let old = b.end();
        b.begin();
        cmp_csub_ttk_vh1_inplace(&mut b, &r, &s_low, &dirty[..2]);
        let new = b.end();
        let width = b.width() as usize;
        let mut seed = 0xb8a0049d17ac52e3u64;
        let mut init = vec![0u64; width];
        for word in &mut init {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            *word = seed;
        }
        let run = |record: &[super::super::builder::G], inverse: bool| {
            let mut bb = B::new();
            bb.alloc_n(width);
            bb.play(record, inverse);
            bb.flush_global();
            let mut h = sha3::Shake256::default();
            h.update(b"b8a-fused-ttk-all-wire");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(width, 1, &mut xof);
            sim.qubits.copy_from_slice(&init);
            sim.apply_iter(bb.ops.iter());
            assert_eq!(sim.phase, 0, "phase inverse={inverse}");
            sim.qubits
        };
        for inverse in [false, true] {
            assert_eq!(run(&old, inverse), run(&new, inverse), "all wires inverse={inverse}");
        }
    }

    #[test]
    fn b2_inplace_remainder_matches_separate_flag_on_supported_domain() {
        use sha3::digest::{ExtendableOutput, Update};
        let mut b = B::new();
        let r = b.alloc_n(24);
        let s_low = b.alloc_n(22);
        let f = b.alloc();
        let d = b.alloc_n(2);
        b.begin();
        cmp_csub_ttk_vh1(&mut b, &r, &s_low, f, &d);
        let old = b.end();
        b.begin();
        cmp_csub_ttk_vh1_inplace(&mut b, &r, &s_low, &d);
        let new = b.end();
        let width = b.width() as usize;
        let mut init = vec![0u64; width];
        let mut seed = 0x681682u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for shot in 0..64 {
            let mask = 1u64 << shot;
            let slow = next() & ((1 << 22) - 1);
            let s = (1 << 22) + slow;
            let rv = match shot % 8 { 0 => 0, 1 => s - 1, 2 => s, 3 => 2 * s - 1, _ => next() % (2 * s) };
            for (i, &q) in r.iter().enumerate() { if rv & (1 << i) != 0 { init[q.0 as usize] |= mask; } }
            for (i, &q) in s_low.iter().enumerate() { if slow & (1 << i) != 0 { init[q.0 as usize] |= mask; } }
            for &q in &d { if next() & 1 != 0 { init[q.0 as usize] |= mask; } }
        }
        let run = |rec: &[super::super::builder::G], inverse: bool, input: &[u64]| {
            let mut bb = B::new();
            bb.alloc_n(width);
            bb.play(rec, inverse);
            bb.flush_global();
            let mut h = sha3::Shake256::default();
            h.update(b"b2-inplace-k3");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(width, 1, &mut xof);
            sim.qubits.copy_from_slice(input);
            sim.apply_iter(bb.ops.iter());
            assert_eq!(sim.phase, 0, "phase");
            sim.qubits.clone()
        };
        let a = run(&old, false, &init);
        let c = run(&new, false, &init);
        for &q in &r[..23] { assert_eq!(a[q.0 as usize], c[q.0 as usize], "remainder low"); }
        assert_eq!(a[f.0 as usize], c[r[23].0 as usize], "flag in top lane");
        assert_eq!(a[r[23].0 as usize], 0, "old remainder top");
        for &q in s_low.iter().chain(&d) { assert_eq!(a[q.0 as usize], c[q.0 as usize], "passenger"); }
        assert_eq!(run(&old, true, &a), init, "old inverse");
        assert_eq!(run(&new, true, &c), init, "new inverse");
    }

    #[test]
    fn b2_cleanbank_inplace_matches_ttk_on_supported_domain() {
        use sha3::digest::{ExtendableOutput, Update};
        let mut b = B::new();
        let r = b.alloc_n(24);
        let s_low = b.alloc_n(22);
        let dirty = b.alloc_n(2);
        let bank = b.alloc_n(72);
        let passengers = b.alloc_n(5);
        b.begin();
        cmp_csub_ttk_vh1_inplace(&mut b, &r, &s_low, &dirty);
        let old = b.end();
        let mut variants = Vec::new();
        for len in [2, 3, 26, 72] {
            b.begin();
            cmp_csub_clean_vh1_inplace(&mut b, &r, &s_low, &bank[..len], &dirty);
            variants.push((len, b.end()));
        }
        let width = b.width() as usize;
        let mut init = vec![0u64; width];
        let mut seed = 0xb2c1ea4u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for shot in 0..64 {
            let mask = 1u64 << shot;
            let slow = next() & ((1 << 22) - 1);
            let s = (1 << 22) + slow;
            let rv = match shot % 8 { 0 => 0, 1 => s - 1, 2 => s, 3 => 2 * s - 1, _ => next() % (2 * s) };
            for (i, &q) in r.iter().enumerate() { if rv & (1 << i) != 0 { init[q.0 as usize] |= mask; } }
            for (i, &q) in s_low.iter().enumerate() { if slow & (1 << i) != 0 { init[q.0 as usize] |= mask; } }
            for &q in dirty.iter().chain(&passengers) { if next() & 1 != 0 { init[q.0 as usize] |= mask; } }
        }
        let run = |rec: &[super::super::builder::G], inverse: bool, input: &[u64]| {
            let mut bb = B::new();
            bb.alloc_n(width);
            bb.play(rec, inverse);
            bb.flush_global();
            let mut h = sha3::Shake256::default();
            h.update(b"b2-clean-inplace-k3");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(width, 1, &mut xof);
            sim.qubits.copy_from_slice(input);
            sim.apply_iter(bb.ops.iter());
            assert_eq!(sim.phase, 0, "phase");
            sim.qubits.clone()
        };
        let reference = run(&old, false, &init);
        assert_eq!(run(&old, true, &reference), init, "old inverse");
        for (len, rec) in variants {
            let got = run(&rec, false, &init);
            assert_eq!(got, reference, "forward bank len {len}");
            assert_eq!(run(&rec, true, &got), init, "inverse bank len {len}");
        }
    }
}

#[cfg(test)]
mod vh1_tests {
    use super::*;
    use crate::sim::Simulator;

    /// cmp_csub_ttk_vh1 against cmp_csub_ttk_vz with the leading one physical: forward, inverse, dirty passengers
    #[test]
    fn vh1_matches_physical_leading_one() {
        let mut b = B::new();
        let r = b.alloc_n(24);
        let s_low = b.alloc_n(22);
        let one = b.alloc();
        let f = b.alloc();
        let d = b.alloc_n(3);
        let s_full: Vec<QubitId> = s_low.iter().copied().chain([one]).collect();
        b.begin();
        cmp_csub_ttk_vz(&mut b, &r, &s_full, f, d[2]);
        let phys = b.end();
        b.begin();
        cmp_csub_ttk_vh1(&mut b, &r, &s_low, f, &d[..2]);
        let virt = b.end();
        let width = b.width() as usize;
        let mut seed = 0x0d1_0e5u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for round in 0..64 {
            let mut init = vec![0u64; width];
            for &q in s_low.iter().chain(&d) { init[q.0 as usize] = next(); }
            // (both are exact mod 2^24 for any R)
            for &q in &r { init[q.0 as usize] = next(); }
            if round % 2 == 0 { init[r[23].0 as usize] = 0; }
            init[one.0 as usize] = !0;
            let run = |g: &[super::super::builder::G], inv: bool, init: &[u64]| -> Vec<u64> {
                let mut bb = B::new();
                let _ = bb.alloc_n(width);
                bb.play(g, inv);
                bb.flush_global();
                let mut h = sha3::Shake256::default();
                use sha3::digest::{Update, ExtendableOutput};
                h.update(b"vh1");
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(width, 1, &mut xof);
                sim.qubits.copy_from_slice(init);
                sim.apply_iter(bb.ops.iter());
                assert_eq!(sim.phase, 0, "phase");
                sim.qubits.clone()
            };
            let want = run(&phys, false, &init);
            let got = run(&virt, false, &init);
            assert_eq!(&want[..width], &got[..width], "forward round {round}");
            let back = run(&virt, true, &got);
            assert_eq!(back, init, "inverse round {round}");
        }
    }
}
