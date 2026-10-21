//! Shared digit size view: raw low-five Z and the full eight-bit Y size.
//!
//! When 231 <= Z + Y <= 257, both sizes share three physical high owners:
//! toggling the high-size view leaves both low-five words unchanged. This
//! is a literal, measurement-free involution on every raw input word.
//! Integrated by payload::pool5_shared_digit; whole qualification is separate.

use super::builder::{B, G};
use crate::circuit::QubitId;

/// Clear the three raw Z-high owners on 231 <= Z+Y <= 257, leaving Z-low
/// and the complete Y unchanged. Its inverse restores Z-high. The high
/// owners themselves are the workspace: no additional clean bit is used.
/// Exact literal cost: 47 CCX; no measurements. This is a full permutation
/// off the bounded domain too, but its three output high bits need not be 0.
pub(crate) fn encode_record(b: &mut B, z: &[QubitId], y: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(z.len(), 8);
    assert_eq!(y.len(), 8);
    let ports: Vec<_> = z.iter().chain(y).copied().collect();
    assert_eq!(ports.iter().collect::<std::collections::BTreeSet<_>>().len(), 16);
    let mut bank = Vec::new();
    for &q in dirty {
        if !ports.contains(&q) && !bank.contains(&q) { bank.push(q); }
    }
    assert!(bank.len() >= 2);
    let h = &z[5..];
    let carry = super::frogdrop_col::rec(b, |b| {
        super::arith::ttk_carry_u(b, &z[..5], &y[..5], h[2], bank[0]);
    });
    let add_low = super::frogdrop_col::rec(b, |b| {
        super::arith::ttk_add(b, &z[..5], &y[..5], None, None);
    });
    super::frogdrop_col::rec(b, |b| {
        super::arith::ttk_add(b, &y[5..], h, None, None);
        // H = -c-d mod8: H0=c XOR d, H1=H2=c OR d,
        // with c=carry5(Zlo+Ylo), d=[(Zlo+Ylo) mod32 >=2].
        b.cx(h[1], h[2]);
        b.play(&carry, false);
        b.cx(h[2], h[0]);
        b.cx(h[0], h[1]);
        b.cx(h[2], h[1]);
        b.ccx(h[0], h[2], h[1]);
        b.play(&add_low, false);
        b.x(h[0]);
        let zero: Vec<_> = y[1..5].iter().map(|&q| (q, true)).collect();
        super::mask::mc_xor(b, &zero, h[0], &[], &bank);
        b.play(&add_low, true);
        b.play(&carry, true);
    })
}

/// Toggle Y-high <-> Z-high, with low Z and low Y unchanged.
///
/// The input `high` is the shared three-bit high word. `tmp` and the two
/// `clean` owners must be globally zero; all are returned before exit.
/// The digit lends its g/c0 only between complete arithmetic/decoder epochs.
/// All dirty donors are restored. On the
/// bounded size domain, the returned high word is the other raw size's high
/// word. Outside that domain this is still an exact self-inverse permutation.
/// The complete literal record contains 36 CCX and no measured uncompute.
pub(crate) fn view_record(b: &mut B, zlow: &[QubitId], ylow: &[QubitId],
    high: &[QubitId], tmp: QubitId, clean: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(zlow.len(), 5);
    assert_eq!(ylow.len(), 5);
    assert_eq!(high.len(), 3);
    assert_eq!(clean.len(), 2);
    let ports: Vec<_> = zlow.iter().chain(ylow).chain(high)
        .chain(clean).copied().chain([tmp]).collect();
    assert_eq!(ports.iter().collect::<std::collections::BTreeSet<_>>().len(), ports.len());
    let mut bank = Vec::new();
    for &q in dirty {
        if !ports.contains(&q) && !bank.contains(&q) { bank.push(q); }
    }
    assert!(bank.len() >= 2, "shared-size view requires two returned dirty donors");
    let inc_high = super::frogdrop_col::rec(b, |b| {
        // Save the conjunction, update the upper bit, and return its owner
        // before either of the saved controls is changed. Four literal CCX.
        b.ccx(tmp, high[0], clean[0]);
        b.ccx(clean[0], high[1], high[2]);
        b.ccx(tmp, high[0], clean[0]);
        b.ccx(tmp, high[0], high[1]);
        b.cx(tmp, high[0]);
    });
    let add_low = super::frogdrop_col::rec(b, |b| {
        super::arith::ttk_add(b, zlow, ylow, None, None);
    });
    // The ordinary TTK addition has a carry hook at its forward-ladder peak.
    // tmp = original_z4 XOR (peak_z4 AND peak_y4) is exactly carry_out.
    // Unhook before completing TTK, then erase original_z4 after z returns.
    let add_low_with_high_decrement = super::frogdrop_col::rec(b, |b| {
        b.cx(zlow[4], tmp);
        for i in 1..5 { b.cx(zlow[i], ylow[i]); }
        for i in (1..4).rev() { b.cx(zlow[i], zlow[i + 1]); }
        for i in 0..4 { b.ccx(ylow[i], zlow[i], zlow[i + 1]); }
        b.ccx(zlow[4], ylow[4], tmp);
        b.play(&inc_high, true);
        b.ccx(zlow[4], ylow[4], tmp);
        for i in (1..5).rev() {
            b.cx(zlow[i], ylow[i]);
            b.ccx(ylow[i - 1], zlow[i - 1], zlow[i]);
        }
        for i in 1..4 { b.cx(zlow[i], zlow[i + 1]); }
        b.cx(zlow[0], ylow[0]);
        for i in 1..5 { b.cx(zlow[i], ylow[i]); }
        b.cx(zlow[4], tmp);
    });
    let small = super::frogdrop_col::rec(b, |b| {
        // tmp ^= [sum_low <= 1]. The two pair summaries are returned
        // literally while every input control retains its original value.
        for &q in &ylow[1..] { b.x(q); }
        b.ccx(ylow[1], ylow[2], clean[0]);
        b.ccx(ylow[3], ylow[4], clean[1]);
        b.ccx(clean[0], clean[1], tmp);
        b.ccx(ylow[3], ylow[4], clean[1]);
        b.ccx(ylow[1], ylow[2], clean[0]);
        for &q in &ylow[1..] { b.x(q); }
    });
    super::frogdrop_col::rec(b, |b| {
        // Let c=floor((Zlo+Ylo)/32), e=[(Zlo+Ylo) mod32 <= 1].
        // H' = 7-H-c+e (mod8). Low words are unchanged, so F(F(H))=H.
        for &q in high { b.x(q); }
        b.play(&add_low_with_high_decrement, false);
        b.play(&small, false);
        b.play(&inc_high, false);
        b.play(&small, true);
        b.play(&add_low, true);
    })
}
