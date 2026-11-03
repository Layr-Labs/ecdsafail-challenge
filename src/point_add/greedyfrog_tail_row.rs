//! L4 exact terminal-row sign oracle. Parent integration is deliberately separate.
//!
//! On a fully pooled plain final division row, only the new top sign is read.
//! Keep the original remainder untouched, compute that sign into `out`, let the
//! sweep read `out`, then erase `out` by X measurement and a conditional sign phase.
//! No row count, source bit, rounding bit, or quotient decision is removed.
use super::*;

pub(super) fn tail_break(k: u32) -> bool {
    cfg!(test) && std::env::var("L4_TAIL_BREAK").map_or(false, |v| v.trim() == k.to_string())
}

/// Reconstruct one ordinary final row's exact original data/source wiring.
/// Called separately on compute and erase because X0 can be rebound by hosting.
pub(super) fn operands(u: &GreedyFrog, w: &Win, rt: &RowTmp, parked: bool, top: usize)
    -> (Vec<QubitId>, Vec<QubitId>, QubitId, Option<QubitId>) {
    assert!(w.k >= 2 && rt.m.is_none() && rt.last_sign.is_none());
    let j = w.k - 1;
    let hi = if parked { (j + top).min(NB) } else { NB };
    let t = (j as isize - 1..hi as isize).rev().map(|i| rt.rem(u, i)).collect();
    let s = (j..hi).rev().map(|i| u.x[i - j]).collect();
    let prev = rt.rem(u, j as isize - 2);
    let rb = (round_div() && w.mx >= NB - j + 1 && hi == NB).then(|| u.x[NB - j]);
    (t, s, prev, rb)
}

fn check(t: &[QubitId], s: &[QubitId], sign: QubitId, round: Option<QubitId>, out: QubitId, pool: &[QubitId]) {
    let n = s.len();
    assert!(n > 0 && t.len() == n + 1 && pool.len() >= n, "terminal sign needs C lower lanes, one top lane and C pool lanes");
    let mut q: Vec<QubitId> = t.iter().chain(s).copied().collect();
    q.push(sign);
    if let Some(r) = round { q.push(r); }
    q.push(out);
    q.extend_from_slice(&pool[..n]);
    q.sort_by_key(|x| x.0);
    assert!(q.windows(2).all(|a| a[0] != a[1]), "terminal sign operands must be disjoint");
}

/// Enter the same ROW-F source/carry frame as division_rows:
/// source_i ^= m, m = !sign; carry-in = m ^ rounding_bit. The sign-extension
/// term at the top is still m, so the rounding bit must be canceled there.
fn enter(b: &mut B, s: &[QubitId], sign: QubitId, round: Option<QubitId>) {
    for &q in s { b.cx(sign, q); b.x(q); }
    if let Some(r) = round { b.cx(r, sign); }
    b.x(sign);
}
fn leave(b: &mut B, s: &[QubitId], sign: QubitId, round: Option<QubitId>) {
    b.x(sign);
    if let Some(r) = round { b.cx(r, sign); }
    for &q in s { b.x(q); b.cx(sign, q); }
}

/// carry' = carry XOR ((target XOR carry) AND (source XOR carry)).
/// Unlike the in-place ladder, the data lanes are restored immediately.
fn form(b: &mut B, t: QubitId, s: QubitId, carry: QubitId, next: QubitId) {
    b.cx(carry, t); b.cx(carry, s);
    b.and_c(t, s, next);
    b.cx(carry, t); b.cx(carry, s);
    b.cx(carry, next);
}
fn unform(b: &mut B, t: QubitId, s: QubitId, carry: QubitId, next: QubitId) {
    b.cx(carry, next);
    b.cx(carry, t); b.cx(carry, s);
    b.and_u(t, s, next);
    b.cx(carry, t); b.cx(carry, s);
}

/// Compute the terminal sign into fresh |0> `out`, preserving every input lane.
/// `t` is low-to-high including the sign lane; `s` is low-to-high excluding its
/// zero sign-extension source. `sign` is the previous row's sign (zero for row 0
/// if a caller supplies a separate zero lane), `round` the dropped divisor bit.
/// The caller must guarantee a full clean carry pool. No ROLL receipt is created.
/// Analytic nonlinear cost: C = s.len() Toffoli (not a measured whole-build delta).
pub(super) fn compute(b: &mut B, t: &[QubitId], s: &[QubitId], sign: QubitId,
                      round: Option<QubitId>, out: QubitId, pool: &[QubitId]) {
    check(t, s, sign, round, out, pool);
    let n = s.len();
    enter(b, s, sign, round);
    for i in 0..n {
        form(b, t[i], s[i], if i == 0 { sign } else { pool[i - 1] }, pool[i]);
    }
    b.cx(t[n], out);
    if !tail_break(1) { b.cx(pool[n - 1], out); }
    b.cx(sign, out);
    if let Some(r) = round { if !tail_break(2) { b.cx(r, out); } }
    for i in (0..n).rev() {
        unform(b, t[i], s[i], if i == 0 { sign } else { pool[i - 1] }, pool[i]);
    }
    leave(b, s, sign, round);
}

/// Apply (-1)^terminal_sign while preserving every data/pool lane. Form only the
/// first C-1 carries: the last carry's phase is Z(c) CZ(t XOR c,s XOR c).
/// Analytic nonlinear cost C-1, entered only on the measurement-one branch.
fn phase(b: &mut B, t: &[QubitId], s: &[QubitId], sign: QubitId,
         round: Option<QubitId>, pool: &[QubitId]) {
    let n = s.len();
    enter(b, s, sign, round);
    for i in 0..n - 1 {
        form(b, t[i], s[i], if i == 0 { sign } else { pool[i - 1] }, pool[i]);
    }
    b.z(t[n]);
    b.z(sign);
    if let Some(r) = round { b.z(r); }
    let c = if n == 1 { sign } else { pool[n - 2] };
    b.z(c);
    b.cx(c, t[n - 1]); b.cx(c, s[n - 1]);
    if !tail_break(3) { b.cz(t[n - 1], s[n - 1]); }
    b.cx(c, t[n - 1]); b.cx(c, s[n - 1]);
    for i in (0..n - 1).rev() {
        unform(b, t[i], s[i], if i == 0 { sign } else { pool[i - 1] }, pool[i]);
    }
    leave(b, s, sign, round);
}

/// Erase the computed sign after all sweep consumers, with inputs still unchanged.
/// `out` returns |0> and remains allocated. Analytic expected cost (C-1)/2 T.
/// This must be emitted directly, not captured inside a builder recording.
pub(super) fn erase(b: &mut B, t: &[QubitId], s: &[QubitId], sign: QubitId,
                    round: Option<QubitId>, out: QubitId, pool: &[QubitId]) {
    check(t, s, sign, round, out, pool);
    let bit = b.fresh_bits(1)[0];
    b.hmr_to(out, bit);
    b.push_condition(bit);
    phase(b, t, s, sign, round, pool);
    b.pop_condition();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    /// Exhaust all operand assignments through C=3; deterministic random vectors
    /// for C=4..24. Check sign, unchanged inputs, clean scratch, phase and erase.
    /// Negative controls (run separately; each MUST fail): L4_TAIL_BREAK=1 carry
    /// omitted; =2 rounding-bit cancellation omitted; =3 phase repair CZ omitted.
    #[test]
    fn l4_terminal_sign_gate_level() {
        for n in 1..=24usize {
            for rounded in [false, true] {
                let mut b = B::new();
                let t = b.alloc_n(n + 1);
                let s = b.alloc_n(n);
                let sign = b.alloc();
                let round = rounded.then(|| b.alloc());
                let out = b.alloc();
                let pool = b.alloc_n(n);
                compute(&mut b, &t, &s, sign, round, out, &pool);
                let mid = b.ops.len();
                erase(&mut b, &t, &s, sign, round, out, &pool);
                let nb = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0])
                    .filter(|&q| q != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                let ib = 2*n + 2 + usize::from(rounded);
                let batches = if n <= 3 { ((1usize << ib) + 63) / 64 } else { 4 };
                let mask = (1u64 << n) - 1;
                let tmask = (1u64 << (n + 1)) - 1;
                let mut rng = 0xa71e_c0f0_41ab_70d1u64 ^ n as u64 ^ ((rounded as u64) << 32);
                for batch in 0..batches {
                    let mut h = sha3::Shake256::default();
                    h.update(b"l4-terminal-sign-measurements");
                    h.update(&(n as u64).to_le_bytes());
                    h.update(&(batch as u64).to_le_bytes());
                    h.update(&[rounded as u8]);
                    let mut xof = h.finalize_xof();
                    let mut sim = Simulator::new(b.width() as usize, nb, &mut xof);
                    let mut expected = 0u64;
                    for sh in 0..64usize {
                        let word = if n <= 3 { ((batch*64 + sh) % (1usize << ib)) as u64 } else {
                            rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; rng
                        };
                        let tv = word & tmask;
                        let sv = (word >> (n+1)) & mask;
                        let sg = (word >> (2*n+1)) & 1;
                        let rv = if rounded { (word >> (2*n+2)) & 1 } else { 0 };
                        let bit = 1u64 << sh;
                        for i in 0..n+1 { if tv >> i & 1 != 0 { sim.qubits[t[i].0 as usize] |= bit; } }
                        for i in 0..n { if sv >> i & 1 != 0 { sim.qubits[s[i].0 as usize] |= bit; } }
                        if sg != 0 { sim.qubits[sign.0 as usize] |= bit; }
                        if let Some(r) = round { if rv != 0 { sim.qubits[r.0 as usize] |= bit; } }
                        let v = (tv as i64 + if sg == 0 { -(sv as i64 + rv as i64) } else { sv as i64 + rv as i64 })
                            .rem_euclid(1i64 << (n+1)) as u64;
                        if v >> n & 1 != 0 { expected |= bit; }
                    }
                    let initial = sim.qubits.clone();
                    sim.apply_iter(b.ops[..mid].iter());
                    assert_eq!(sim.qubits[out.0 as usize], expected, "terminal sign n={n} rounded={rounded} batch={batch}");
                    assert_eq!(sim.phase, 0, "terminal sign compute phase n={n} rounded={rounded}");
                    for q in 0..b.width() as usize { if q != out.0 as usize { assert_eq!(sim.qubits[q], initial[q], "terminal sign compute restored q={q} n={n}"); } }
                    sim.apply_iter(b.ops[mid..].iter());
                    assert_eq!(sim.phase, 0, "terminal sign erase phase n={n} rounded={rounded} batch={batch}");
                    assert_eq!(sim.qubits, initial, "terminal sign erase restore n={n} rounded={rounded} batch={batch}");
                }
            }
        }
    }
}
