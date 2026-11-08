//! Re-anchoring of the stream-bound tables (y42_bound, square_guard, linear_restore).
//!
//! Those tables name ops by absolute index and used to assert the length and hash of the whole input stream, so any
//! change upstream (even far from the edits) stopped the build. Here each table is bound to content near its edits:
//! - y42_bound and square_guard: the region [lo, hi) that spans every edit (plus a margin) must occur in the input,
//!   op for op, exactly once at some shift d; the edits then apply at index + d. A change inside the region panics.
//! - linear_restore: each edit is bound by the window of 2k+1 ops centred on the op it rewrites (k chosen so that the
//!   window is unique in the stream it was made on); the window must occur exactly once and the windows stay in order.
//!
//! Matching: a polynomial rolling hash of the per-op mix finds candidates, a position-weighted fingerprint confirms.
//! Anchors live in `rebind_anchors.txt` ("region <name> lo hi poly fp" and "window <name> idx k poly fp"). A table
//! with no anchor line falls back to the exact whole-stream binding and prints its anchor lines ("RBA ...").
use crate::circuit::{Op, OperationType};
use std::collections::HashMap;

pub(super) type Want = Vec<u64>;
pub(super) fn want_of(v: impl IntoIterator<Item = u64>) -> Want {
    let mut w: Vec<u64> = v.into_iter().collect();
    w.sort_unstable();
    w.dedup();
    w
}

const ANCHORS: &str = include_str!("rebind_anchors.txt");
const B: u64 = 0x9E37_79B9_7F4A_7C15 | 1;
/// Region margin (ops) on each side of the edit span.
pub(super) const MARGIN: usize = 64;

pub(super) fn mix(o: &Op) -> u64 {
    let mut h = 0x9E3779B97F4A7C15u64;
    for x in [o.kind as u64, o.q_control2.0, o.q_control1.0, o.q_target.0, o.c_target.0, o.c_condition.0, o.r_target.0] {
        h = (h ^ x).wrapping_mul(0x100000001B3);
        h ^= h >> 29;
    }
    h
}
pub(super) fn mixes(ops: &[Op]) -> Vec<u64> {
    ops.iter().map(mix).collect()
}
pub(super) fn poly(h: &[u64]) -> u64 {
    h.iter().fold(0u64, |a, &x| a.wrapping_mul(B).wrapping_add(x))
}
pub(super) fn fp(h: &[u64]) -> u64 {
    h.iter().enumerate().fold(0u64, |a, (j, &x)| a.wrapping_add(x.wrapping_mul(2 * j as u64 + 1)))
}
fn powb(n: usize) -> u64 {
    let (mut r, mut b, mut e) = (1u64, B, n);
    while e > 0 {
        if e & 1 == 1 {
            r = r.wrapping_mul(b);
        }
        b = b.wrapping_mul(b);
        e >>= 1;
    }
    r
}
/// Start positions p where poly(h[p..p+len]) is in `want`; returns (p, want value).
pub(super) fn scan(h: &[u64], len: usize, want: &Want) -> Vec<(usize, u64)> {
    let mut out = Vec::new();
    if len == 0 || h.len() < len {
        return out;
    }
    let top = powb(len - 1);
    let mut cur = poly(&h[..len]);
    for p in 0..=h.len() - len {
        if (want.len() == 1 && want[0] == cur) || (want.len() > 1 && want.binary_search(&cur).is_ok()) {
            out.push((p, cur));
        }
        if p + len < h.len() {
            cur = cur.wrapping_sub(h[p].wrapping_mul(top)).wrapping_mul(B).wrapping_add(h[p + len]);
        }
    }
    out
}

fn lines(kind: &str, name: &str) -> Vec<Vec<u64>> {
    ANCHORS
        .lines()
        .filter_map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            (f.len() == 6 && f[0] == kind && f[1] == name).then(|| f[2..].iter().map(|x| x.parse::<u64>().unwrap()).collect())
        })
        .collect()
}

/// Shift d for a region table: `span` = (first, last) edit index in the table's own stream. `exact` = the input passed
/// the table's original whole-stream binding. Without an anchor the input must be exact (d = 0) and the anchor prints.
pub(super) fn region_shift(name: &str, ops: &[Op], span: (usize, usize), exact: bool) -> isize {
    let a = lines("region", name);
    let h = mixes(ops);
    if a.is_empty() {
        assert!(exact, "rebind {name}: no anchor and the input is not the bound stream");
        let lo = span.0.saturating_sub(MARGIN);
        let hi = (span.1 + 1 + MARGIN).min(ops.len());
        eprintln!("RBA region {name} {lo} {hi} {} {}", poly(&h[lo..hi]), fp(&h[lo..hi]));
        return 0;
    }
    assert_eq!(a.len(), 1, "rebind {name}: one region anchor");
    let (lo, hi, pv, fv) = (a[0][0] as usize, a[0][1] as usize, a[0][2], a[0][3]);
    assert!(lo <= span.0 && span.1 < hi, "rebind {name}: anchor region does not cover the edits");
    let len = hi - lo;
    let want = want_of([pv]);
    let hits: Vec<usize> = scan(&h, len, &want).into_iter().map(|x| x.0).filter(|&p| fp(&h[p..p + len]) == fv).collect();
    assert!(hits.len() == 1, "rebind {name}: region of {len} ops found {} times (a change inside the bound region?)", hits.len());
    let d = hits[0] as isize - lo as isize;
    assert!(!exact || d == 0, "rebind {name}: exact input but shift {d}");
    eprintln!("REBIND region {name} len={len} shift={d} exact={exact}");
    d
}

/// New positions of single-op edits at `idx` (ascending) in `ops`.
pub(super) fn window_positions(name: &str, ops: &[Op], idx: &[usize], exact: bool) -> Vec<usize> {
    let a = lines("window", name);
    let h = mixes(ops);
    if a.is_empty() {
        assert!(exact, "rebind {name}: no anchor and the input is not the bound stream");
        for &i in idx {
            let mut k = 8usize;
            loop {
                assert!(k <= 1 << 16, "rebind {name}: no unique window at {i}");
                if i >= k && i + k < ops.len() {
                    let (lo, hi) = (i - k, i + k + 1);
                    let (pv, fv) = (poly(&h[lo..hi]), fp(&h[lo..hi]));
                    let want = want_of([pv]);
                    let n = scan(&h, hi - lo, &want).into_iter().filter(|&(p, _)| fp(&h[p..p + hi - lo]) == fv).count();
                    // unique with a 4x margin: the window at k/4.. must also be unique (checked by growing to 4k)
                    if n == 1 {
                        let k4 = 4 * k;
                        let (lo, hi) = (i.saturating_sub(k4), (i + k4 + 1).min(ops.len()));
                        if i >= k4 && hi == i + k4 + 1 {
                            eprintln!("RBA window {name} {i} {k4} {} {}", poly(&h[lo..hi]), fp(&h[lo..hi]));
                        } else {
                            eprintln!("RBA window {name} {i} {k} {pv} {fv}");
                        }
                        break;
                    }
                }
                k *= 2;
            }
        }
        return idx.to_vec();
    }
    assert_eq!(a.len(), idx.len(), "rebind {name}: one window anchor per edit");
    let mut by_len: HashMap<usize, Vec<usize>> = HashMap::new();
    for (e, w) in a.iter().enumerate() {
        assert_eq!(w[0] as usize, idx[e], "rebind {name}: anchor {e} names another edit");
        by_len.entry(2 * w[1] as usize + 1).or_default().push(e);
    }
    let mut pos = vec![usize::MAX; idx.len()];
    for (len, es) in by_len {
        let want = want_of(es.iter().map(|&e| a[e][2]));
        let hits = scan(&h, len, &want);
        for &e in &es {
            let found: Vec<usize> =
                hits.iter().filter(|&&(p, v)| v == a[e][2] && fp(&h[p..p + len]) == a[e][3]).map(|&(p, _)| p + a[e][1] as usize).collect();
            assert!(found.len() == 1, "rebind {name}: window of edit {} found {} times", idx[e], found.len());
            pos[e] = found[0];
        }
    }
    assert!(pos.windows(2).all(|w| w[0] < w[1]), "rebind {name}: windows out of order");
    assert!(!exact || pos == idx, "rebind {name}: exact input but moved edits");
    let moved = pos.iter().zip(idx).filter(|(p, i)| p != i).count();
    eprintln!("REBIND window {name} edits={} moved={moved} exact={exact}", idx.len());
    pos
}

/// Test of the re-anchoring (false = this gate list byte for byte): X;X pairs (identity, no Toffoli) on a CCX's target
/// before the bound passes, one block before the square and one after it, so that every bound edit moves.
pub(super) const TEST_SHIFT: bool = false;
pub(super) fn test_shift(mut ops: Vec<Op>) -> Vec<Op> {
    for &(at, n) in &[(9_000_000usize, 4usize), (2_000_000, 2)] {
        let w = (at..ops.len()).find(|&i| ops[i].kind == OperationType::CCX).expect("rebind test: a CCX");
        let mut x = Op::empty();
        x.kind = OperationType::X;
        x.q_target = ops[w].q_target;
        ops.splice(w..w, std::iter::repeat_n(x, n));
    }
    eprintln!("REBIND test shift: 4 X at 9000000, 2 X at 2000000");
    ops
}
