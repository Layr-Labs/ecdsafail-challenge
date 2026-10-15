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
