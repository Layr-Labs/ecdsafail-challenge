//! Exact two-chunk fold add. The low chunk is written before its boundary
//! carry is measured; its phase is repaid on the written sum at half rate.
//! The caller must be outside a reversible builder recording.

use super::builder::{B, ONE};
use crate::circuit::QubitId;

pub const L1_FOLD_HALF: bool = true;
pub const L1_FOLD_SITES: u8 = 15;
/// Form a multi-term XOR source temporarily in its first source qubit,
/// restoring that qubit after each carry operation. This frees the clean
/// JIT lane for carries; the switch alone never changes the add's width.
pub const L1_FOLD_BORROW_XOR: bool = true;

#[cfg(test)]
thread_local! {
    static TEST_BORROW_XOR: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

#[cfg(test)]
pub(crate) fn test_borrow_xor(v: Option<bool>) -> Option<bool> { TEST_BORROW_XOR.with(|c| c.replace(v)) }

pub(crate) fn borrow_xor_enabled() -> bool {
    #[cfg(test)]
    if let Some(value) = TEST_BORROW_XOR.with(|v| v.get()) { return value; }
    static ON: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_L1_FOLD_BORROW_XOR")
            .map(|v| v.trim() == "1")
            .unwrap_or(L1_FOLD_BORROW_XOR)
    });
    *ON
}

pub(crate) fn enabled_at(site: u8) -> bool {
    enabled() && std::env::var("WL_L1_FOLD_SITES").ok().and_then(|s| s.parse::<u8>().ok()).unwrap_or(L1_FOLD_SITES) & site != 0
}

pub(crate) fn enabled() -> bool {
    static ON: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("WL_L1_FOLD_HALF")
            .map(|v| v.trim() == "1")
            .unwrap_or(L1_FOLD_HALF)
    });
    *ON
}

fn broken() -> u8 {
    if cfg!(test) {
        std::env::var("L1_FOLD_BREAK").ok().and_then(|s| s.parse().ok()).unwrap_or(0)
    } else {
        0
    }
}

fn open(b: &mut B, source: &[QubitId], jit: Option<QubitId>) -> Option<QubitId> {
    match source {
        [] => None,
        [q] => Some(*q),
        _ => {
            let (q, terms) = xor_workspace(source, jit);
            for &s in terms { b.cx(s, q); }
            Some(q)
        }
    }
}

fn close(b: &mut B, source: &[QubitId], jit: Option<QubitId>) {
    if source.len() > 1 {
        let (q, terms) = xor_workspace(source, jit);
        for &s in terms { b.cx(s, q); }
    }
}

fn xor_workspace(source: &[QubitId], jit: Option<QubitId>) -> (QubitId, &[QubitId]) {
    if let Some(q) = jit { return (q,source); }
    assert!(borrow_xor_enabled(), "a multi-term source needs a clean JIT lane when borrowed XOR is off");
    let q=source[0];
    assert!(q!=ONE && !source[1..].contains(&q), "borrowed XOR needs a distinct real first source");
    (q,&source[1..])
}

// Form c' = MAJ(t, h, c), preserving h. With two nonzero inputs the
// target data lane retains t XOR c until its sum or inverse is emitted.
fn carry(b: &mut B, t: QubitId, h: Option<QubitId>, ci: Option<QubitId>, co: QubitId) {
    match (h, ci) {
        (Some(h), None) => b.and_c(t, h, co),
        (Some(ONE), Some(c)) => {
            b.cx(c, t); b.x(c); b.and_c(c, t, co); b.x(c); b.cx(c, co);
        }
        (Some(h), Some(c)) => {
            b.cx(c, h); b.cx(c, t); b.and_c(h, t, co); b.cx(c, co); b.cx(c, h);
        }
        (None, Some(c)) => b.and_c(t, c, co),
        (None, None) => unreachable!("leading zero addend lanes are omitted"),
    }
}

fn erase(b: &mut B, t: QubitId, h: Option<QubitId>, ci: Option<QubitId>, co: QubitId, sum: bool) {
    match (h, ci) {
        (Some(h), None) => { b.and_u(t, h, co); if sum { b.cx(h, t); } }
        (Some(ONE), Some(c)) => {
            b.cx(c, co); b.x(c); b.and_u(c, t, co); b.x(c);
            if sum { b.x(t); } else { b.cx(c, t); }
        }
        (Some(h), Some(c)) => {
            b.cx(c, h); b.cx(c, co); b.and_u(h, t, co); b.cx(c, h);
            if sum { b.cx(h, t); } else { b.cx(c, t); }
        }
        (None, Some(c)) => { b.and_u(t, c, co); if sum { b.cx(c, t); } }
        (None, None) => unreachable!(),
    }
}

fn phase_carry(b: &mut B, t: QubitId, h: Option<QubitId>, ci: Option<QubitId>) {
    // MAJ(t,h,c) = th XOR tc XOR hc, so the final carry's phase
    // requires only CZs, without materializing a final AND.
    if let Some(h) = h { b.cz(t, h); }
    if let Some(c) = ci {
        b.cz(t, c);
        if let Some(h) = h { b.cz(h, c); }
    }
}

/// Add an arbitrary per-lane XOR of stable source qubits to t, modulo
/// 2^t.len(). Sources may repeat across lanes but must be outside t/pool.
/// Multi-term sources use and restore `jit`, also outside t/pool/sources.
/// With borrowed XOR enabled, `jit=None` instead borrows the first source
/// term (which must be real and not repeat in that source's terms). Every
/// source term remains outside t/pool and is restored before the next step.
/// With N active target lanes and P pool lanes, need=N-1 and
/// loan=need-P>0, this emits need+loan Toffoli, of which loan are
/// conditional on one X-measurement outcome: expected need+loan/2.
pub(crate) fn add(
    b: &mut B,
    t: &[QubitId],
    source: &[Vec<QubitId>],
    pool: &[QubitId],
    jit: Option<QubitId>,
) {
    assert!(!b.is_recording(), "half-rate fold must emit outside a reversible recording");
    let targets: std::collections::BTreeSet<_> = t.iter().copied().collect();
    let carries: std::collections::BTreeSet<_> = pool.iter().copied().collect();
    assert_eq!(targets.len(), t.len(), "duplicate fold target");
    assert_eq!(carries.len(), pool.len(), "duplicate fold carry");
    assert!(targets.is_disjoint(&carries), "fold target/carry overlap");
    if let Some(q) = jit {
        assert!(q != ONE && !targets.contains(&q) && !carries.contains(&q), "invalid JIT workspace");
    }
    for src in source {
        for &q in src {
            assert!(!targets.contains(&q) && !carries.contains(&q) && Some(q) != jit,
                    "fold source overlaps writable workspace");
        }
    }
    add_inner(b, t, source, pool, jit, broken());
}

fn add_inner(
    b: &mut B,
    t: &[QubitId],
    source: &[Vec<QubitId>],
    pool: &[QubitId],
    jit: Option<QubitId>,
    brk: u8,
) {
    assert_eq!(source.len(), t.len());
    let i0 = source.iter().position(|s| !s.is_empty()).expect("nonzero addend");
    let need = t.len() - 1 - i0;
    assert!(pool.len() < need);
    let loan = need - pool.len();
    assert!(pool.len() > loan, "two-chunk fold needs a distinct boundary lane");
    let split = i0 + loan + 1;
    let anchor = *pool.last().unwrap();
    let low_c = |i: usize| if i == split { anchor } else { pool[i - i0 - 1] };
    let high_c = |i: usize| if i == split { anchor } else { pool[i - split - 1] };
    let top = t.len() - 1;
    for i in i0..split {
        let h = open(b, &source[i], jit);
        carry(b, t[i], h, (i > i0).then(|| low_c(i)), low_c(i + 1));
        close(b, &source[i], jit);
    }
    for i in (i0..split).rev() {
        let h = open(b, &source[i], jit);
        let ci = (i > i0).then(|| low_c(i));
        if i + 1 == split {
            // Keep the boundary carry, but expose this lane's sum.
            if brk != 2 {
                if let Some(h) = h { b.cx(h, t[i]); }
                else if let Some(c) = ci { b.cx(c, t[i]); }
            }
        } else {
            erase(b, t[i], h, ci, low_c(i + 1), true);
        }
        close(b, &source[i], jit);
    }
    for i in split..top {
        let h = open(b, &source[i], jit);
        carry(b, t[i], h, Some(high_c(i)), high_c(i + 1));
        close(b, &source[i], jit);
    }
    b.cx(high_c(top), t[top]);
    let h = open(b, &source[top], jit);
    if let Some(h) = h { b.cx(h, t[top]); }
    close(b, &source[top], jit);
    for i in (split..top).rev() {
        let h = open(b, &source[i], jit);
        erase(b, t[i], h, Some(high_c(i)), high_c(i + 1), true);
        close(b, &source[i], jit);
    }
    b.measure_and_push(anchor);
    // If s=t+a mod 2^L, the old carry out is [s<a], equivalently
    // carry_out((~s)+a). This identity is exact at every finite width.
    if brk != 3 { for &q in &t[i0..split] { b.x(q); } }
    for i in i0..split - 1 {
        let h = open(b, &source[i], jit);
        carry(b, t[i], h, (i > i0).then(|| pool[i-i0-1]), pool[i-i0]);
        close(b, &source[i], jit);
    }
    let i = split - 1;
    let h = open(b, &source[i], jit);
    if brk != 1 { phase_carry(b, t[i], h, (i > i0).then(|| pool[i-i0-1])); }
    close(b, &source[i], jit);
    for i in (i0..split - 1).rev() {
        let h = open(b, &source[i], jit);
        erase(b, t[i], h, (i > i0).then(|| pool[i-i0-1]), pool[i-i0], false);
        close(b, &source[i], jit);
    }
    if brk != 3 { for &q in &t[i0..split] { b.x(q); } }
    b.pop_classical();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::XofReader;

    struct Forced(u64);
    impl XofReader for Forced {
        fn read(&mut self, out: &mut [u8]) {
            assert_eq!(out.len(),8); out.copy_from_slice(&self.0.to_le_bytes());
        }
    }

    fn run(brk: u8, kind: usize, ones: bool) -> (bool, u64, u64) {
        run_mask(brk,kind,if ones {u64::MAX} else {0},false)
    }

    fn run_mask(brk: u8, kind: usize, forced: u64, borrow: bool) -> (bool, u64, u64) {
        let n = 7;
        let p = 4;
        let mut b = B::new();
        let t = b.alloc_n(n);
        let a = b.alloc_n(n);
        let pool = b.alloc_n(p);
        let jit = b.alloc();
        let source: Vec<Vec<QubitId>> = (0..n).map(|i| match kind {
            0 => vec![a[i]],
            1 => if i == 2 || i == 4 { vec![] } else { vec![a[0]] },
            2 => if i % 2 == 0 { vec![a[0], a[1], a[2]] } else { vec![a[3]] },
            3 => if i % 2 == 0 { vec![ONE] } else { vec![] },
            _ => unreachable!(),
        }).collect();
        add_inner(&mut b, &t, &source, &pool, if borrow {None} else {Some(jit)}, brk);
        let mut good = true;
        let mut charge = 0;
        // Every pair of seven-bit operands, packed as 64 shots.
        for packet in 0..256 {
            let mut xof = Forced(forced);
            let mut sim = Simulator::new(b.peak as usize, 10_100, &mut xof);
            for shot in 0..64 {
                let x = (packet * 64 + shot) & 127;
                let y = (packet * 64 + shot) >> 7;
                for i in 0..n {
                    sim.qubits[t[i].0 as usize] |= (((x >> i) & 1) as u64) << shot;
                    sim.qubits[a[i].0 as usize] |= (((y >> i) & 1) as u64) << shot;
                }
            }
            sim.apply_iter(b.ops.iter());
            good &= sim.phase == 0 && pool.iter().chain(std::iter::once(&jit)).all(|q| sim.qubits[q.0 as usize] == 0);
            for shot in 0..64 {
                let x = (packet * 64 + shot) & 127;
                let y = (packet * 64 + shot) >> 7;
                let addend: usize = source.iter().enumerate().map(|(i, src)| {
                    let bit = src.iter().fold(0, |v, q| v ^ if *q == ONE { 1 } else { (y >> a.iter().position(|a| a == q).unwrap()) & 1 });
                    bit << i
                }).sum();
                let got = t.iter().enumerate().fold(0usize, |v,(i,q)| v | (((sim.qubits[q.0 as usize] >> shot)&1) as usize) << i);
                let preserved = a.iter().enumerate().fold(0usize, |v,(i,q)| v | (((sim.qubits[q.0 as usize] >> shot)&1) as usize) << i);
                good &= got == ((x + addend) & 127) && preserved == y;
            }
            charge += sim.stats.toffoli_gates;
        }
        (good, charge, b.tof)
    }

    #[test]
    fn l1_fold_forced_exact_and_counts() {
        for kind in 0..4 {
            for ones in [false, true] {
                let (ok, charge, emitted) = run(0, kind, ones);
                assert!(ok, "kind {kind} forced ones {ones}");
                // ONE lowers the first carry in both passes to Clifford.
                let expected = if kind == 3 { 5 + usize::from(ones) } else { 6 + 2 * usize::from(ones) };
                assert_eq!(charge, expected as u64 * 16_384, "kind {kind} forced ones {ones}");
                assert_eq!(emitted, if kind == 3 { 6 } else { 8 });
            }
        }
    }

    #[test]
    fn l1_fold_negative_controls_detected() {
        for brk in 1..=3 {
            assert!(!run(brk, 0, true).0, "broken rewrite {brk} escaped all-input test");
        }
    }

    #[test]
    fn l1_fold_borrowed_xor_exhaustive_forced_counts() {
        struct Reset(Option<bool>);
        impl Drop for Reset { fn drop(&mut self) { TEST_BORROW_XOR.with(|v|v.set(self.0)); } }
        let _reset=Reset(TEST_BORROW_XOR.with(|v|v.replace(Some(true))));
        for forced in [0u64,u64::MAX,0xaaaa_aaaa_aaaa_aaaa,0x5555_5555_5555_5555] {
            let (ok,charge,emitted)=run_mask(0,2,forced,true);
            assert!(ok,"borrowed XOR forced={forced:016x}");
            assert_eq!(charge,256*(64*6+forced.count_ones()as u64*2));
            assert_eq!(emitted,8);
        }
        for brk in 1..=3 {
            assert!(!run_mask(brk,2,u64::MAX,true).0,"borrowed XOR broken site {brk} escaped");
        }
    }
}
