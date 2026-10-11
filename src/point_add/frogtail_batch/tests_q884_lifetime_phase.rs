//! Research-only Q888 lifetime/phase proof harness.
//!
//! This module does not alter the production builder.  It binds the proposed
//! page4 splice to the source gate vocabulary and checks the three interfaces
//! that a clean-target arithmetic primitive does not cover: the j/g lifetime
//! conjugation, a dirty standing page, and phase repayment for the omitted
//! low quotient digits.  It deliberately leaves production untouched.

use super::arith::{and_lits, dec, inc, ttk_add};
use super::builder::{B, G};
use super::frogdrop::crot_up;
use super::frogdrop_sched::{p, N};
use super::frogtail::{Sched, Walk, MB, RLEN};
use super::mask::{mc_xor, onehot_scan};
use super::modp_ft::{const_add_pool_test, C};
use super::pointadd_frogtail::{div_forward, SCHED_FROGTAIL};
use super::tests_frogdrop::Rng;
use super::tests_frogtail::M;
use crate::circuit::{analyze_ops, BitId, QubitId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

const LOGICAL_Q: usize = 23;
const PAGE: usize = 4;
const JB: usize = 5;

struct Words {
    words: Vec<u64>,
    at: usize,
}

impl Words {
    fn new(words: Vec<u64>) -> Self {
        Self { words, at: 0 }
    }
}

impl XofReader for Words {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        let word = self.words.get(self.at).copied().unwrap_or(0);
        self.at += 1;
        out.copy_from_slice(&word.to_le_bytes());
    }
}

fn put(words: &mut [u64], q: QubitId, value: u64) {
    words[q.0 as usize] = value;
}

fn get(words: &[u64], qs: &[QubitId], shot: usize) -> u64 {
    qs.iter().enumerate().fold(0u64, |v, (i, q)| {
        v | (((words[q.0 as usize] >> shot) & 1) << i)
    })
}

fn inv_pow2(b: u64, n: usize) -> u64 {
    let mask = (1u64 << n) - 1;
    let mut x = 1u64;
    for _ in 0..6 {
        x = x.wrapping_mul(2u64.wrapping_sub(b.wrapping_mul(x))) & mask;
    }
    x
}

fn quotient(b: u64, l: u64, n: usize) -> u64 {
    let mask = (1u64 << n) - 1;
    ((!l).wrapping_add(1) * inv_pow2(b, n)) & mask
}

fn ttk_record(b: &mut B, a: &[QubitId], t: &[QubitId], ctl: QubitId) -> Vec<G> {
    b.begin();
    ttk_add(b, a, t, Some(ctl), None);
    b.end()
}

/// Source-preserving high-page constructor whose output targets may be dirty.
/// Page lanes are only XOR targets; no old page payload is ever a control.
/// `tmp` is the proposed alias of production `sc.tmp[4]`.
fn high_page_dirty_record(
    b: &mut B,
    active: QubitId,
    bb: &[QubitId],
    acc: &[QubitId],
    page: &[QubitId],
    tmp: QubitId,
    m: usize,
) -> Vec<G> {
    assert!((2..=LOGICAL_Q).contains(&m));
    assert!(bb.len() >= m && acc.len() >= m && page.len() == PAGE);
    let omitted = m.saturating_sub(PAGE);
    b.begin();

    // q0=1 on the selected odd domain.
    let add0 = ttk_record(b, &bb[..m], &acc[..m], active);
    b.play(&add0, false);

    // acc0 becomes selected*q1 and is restored before add0 is inverted.
    b.x(acc[0]);
    b.cx(active, acc[0]);
    b.ccx(active, acc[1], acc[0]);

    let add1 = if m >= 3 {
        let r = ttk_record(b, &bb[..m - 1], &acc[1..m], acc[0]);
        b.play(&r, false);
        Some(r)
    } else {
        None
    };

    // Freeze q2..q(m-2) in their newly cleared source columns.  tmp is live
    // for one row only and is measurement-uncomputed before the next row.
    let mut rows: Vec<(usize, Vec<G>)> = vec![];
    for k in 2..m.saturating_sub(1) {
        b.and_c(active, acc[k], tmp);
        let r = ttk_record(b, &bb[..m - k], &acc[k..m], tmp);
        b.play(&r, false);
        b.cx(tmp, acc[k]);
        b.and_u(active, acc[k], tmp);
        rows.push((k, r));
    }

    // XOR the selected, top-aligned word into a dirty page.  The page is not
    // subsequently consulted while restoring the source accumulator.
    for k in omitted..m {
        let slot = k + PAGE - m;
        if k == 0 {
            b.cx(active, page[slot]);
        } else if k == 1 {
            b.ccx(active, acc[0], page[slot]);
        } else {
            b.ccx(active, acc[k], page[slot]);
        }
    }

    for (k, r) in rows.iter().rev() {
        b.and_c(active, acc[*k], tmp);
        b.cx(tmp, acc[*k]);
        b.play(r, true);
        b.and_u(active, acc[*k], tmp);
    }
    if let Some(r) = &add1 {
        b.play(r, true);
    }
    b.ccx(active, acc[1], acc[0]);
    b.cx(active, acc[0]);
    b.x(acc[0]);
    b.play(&add0, true);
    b.end()
}

/// Recompute the first `r` quotient digits in the source accumulator, apply
/// their classical measurement receipts, and restore the accumulator.  No
/// quantum output/work register is allocated: q0 is `active`, q1 is `acc[0]`,
/// and qk is `acc[k]` after the source-local Hensel rows.  `tmp` is the same
/// fixed `sc.tmp[4]` alias used by the high-page constructor.
fn low_phase_record(
    b: &mut B,
    active: QubitId,
    bb: &[QubitId],
    acc: &[QubitId],
    tmp: QubitId,
    receipts: &[BitId],
    r: usize,
) -> Vec<G> {
    assert!(r <= LOGICAL_Q - PAGE);
    assert!(bb.len() >= r && acc.len() >= r && receipts.len() >= r);
    b.begin();
    if r == 0 {
        return b.end();
    }
    b.z_if(active, receipts[0]);
    if r == 1 {
        return b.end();
    }

    let add0 = ttk_record(b, &bb[..r], &acc[..r], active);
    b.play(&add0, false);
    b.x(acc[0]);
    b.cx(active, acc[0]);
    b.ccx(active, acc[1], acc[0]);
    let add1 = if r >= 3 {
        let row = ttk_record(b, &bb[..r - 1], &acc[1..r], acc[0]);
        b.play(&row, false);
        Some(row)
    } else {
        None
    };
    let mut rows: Vec<(usize, Vec<G>)> = vec![];
    for k in 2..r.saturating_sub(1) {
        b.and_c(active, acc[k], tmp);
        let row = ttk_record(b, &bb[..r - k], &acc[k..r], tmp);
        b.play(&row, false);
        b.cx(tmp, acc[k]);
        b.and_u(active, acc[k], tmp);
        rows.push((k, row));
    }

    // The source columns are meaningful quotient digits only on `active`.
    // Form that conjunction in the one fixed helper before each classical
    // receipt correction; otherwise the unconditional acc[0] toggle would
    // leak a phase on inactive shots.
    b.and_c(active, acc[0], tmp);
    b.z_if(tmp, receipts[1]);
    b.and_u(active, acc[0], tmp);
    for k in 2..r {
        b.and_c(active, acc[k], tmp);
        b.z_if(tmp, receipts[k]);
        b.and_u(active, acc[k], tmp);
    }

    for (k, row) in rows.iter().rev() {
        b.and_c(active, acc[*k], tmp);
        b.cx(tmp, acc[*k]);
        b.play(row, true);
        b.and_u(active, acc[*k], tmp);
    }
    if let Some(row) = &add1 {
        b.play(row, true);
    }
    b.ccx(active, acc[1], acc[0]);
    b.cx(active, acc[0]);
    b.x(acc[0]);
    b.play(&add0, true);
    b.end()
}

fn compute_minus_one_marker(b: &mut B, j: &[QubitId], e: QubitId, tmp: &[QubitId]) {
    b.ccx(j[0], j[1], tmp[0]);
    b.ccx(tmp[0], j[2], tmp[1]);
    b.ccx(tmp[1], j[3], tmp[2]);
    b.ccx(tmp[2], j[4], e);
    b.ccx(tmp[1], j[3], tmp[2]);
    b.ccx(tmp[0], j[2], tmp[1]);
    b.ccx(j[0], j[1], tmp[0]);
}

fn clear_minus_one_marker(b: &mut B, j: &[QubitId], e: QubitId, tmp: &[QubitId]) {
    b.ccx(j[0], j[1], tmp[0]);
    b.ccx(tmp[0], j[2], tmp[1]);
    b.ccx(tmp[1], j[3], tmp[2]);
    b.ccx(tmp[2], j[4], e);
    b.ccx(tmp[1], j[3], tmp[2]);
    b.ccx(tmp[0], j[2], tmp[1]);
    b.ccx(j[0], j[1], tmp[0]);
}

struct Capsule {
    b: B,
    j: Vec<QubitId>,
    gap_source: Vec<QubitId>,
    e: QubitId,
    tmp: Vec<QubitId>,
    bb: Vec<QubitId>,
    ll: Vec<QubitId>,
    page: Vec<QubitId>,
    after_gap: usize,
    after_hensel: usize,
    end: usize,
}

fn owner_capsule() -> Capsule {
    let mut b = B::new();
    let j = b.alloc_n(JB);
    let gap_source = b.alloc_n(JB); // test oracle for the normalizer output
    let e = b.alloc();
    let tmp = b.alloc_n(5);
    let bb = b.alloc_n(LOGICAL_Q);
    let ll = b.alloc_n(LOGICAL_Q);
    let page = b.alloc_n(PAGE);

    compute_minus_one_marker(&mut b, &j, e, &tmp);
    for &q in &j {
        b.cx(e, q);
    }
    for k in 0..JB {
        b.ccx(e, gap_source[k], j[k]);
    }
    let after_gap = b.ops.len();

    let hr = high_page_dirty_record(&mut b, e, &bb, &ll, &page, tmp[4], LOGICAL_Q);
    b.play(&hr, false);
    let after_hensel = b.ops.len();

    for k in (0..JB).rev() {
        b.ccx(e, gap_source[k], j[k]);
    }
    for &q in &j {
        b.cx(e, q);
    }
    clear_minus_one_marker(&mut b, &j, e, &tmp);
    let end = b.ops.len();
    Capsule {
        b,
        j,
        gap_source,
        e,
        tmp,
        bb,
        ll,
        page,
        after_gap,
        after_hensel,
        end,
    }
}

#[test]
fn q888_tmp4_alias_owner_intervals_and_counter_restoration() {
    let c = owner_capsule();
    let helper_hmrs = 2 * (LOGICAL_Q - 3);
    let mut xof = Words::new(
        (0..helper_hmrs)
            .map(|i| {
                if i & 1 == 0 {
                    u64::MAX
                } else {
                    0xaaaa_5555_aaaa_5555
                }
            })
            .collect(),
    );
    let mut sim = Simulator::new(c.b.width() as usize, 90_000, &mut xof);
    let mut expected_j = [0u64; JB];
    let mut expected_g = [0u64; JB];
    let mut selected = 0u64;
    for shot in 0..64 {
        let jv = if shot < 23 { 31 } else { (shot * 7 + 3) & 31 };
        let gv = shot % 23;
        if jv == 31 {
            selected |= 1u64 << shot;
        }
        for k in 0..JB {
            expected_j[k] |= (((jv >> k) & 1) as u64) << shot;
            expected_g[k] |= (((gv >> k) & 1) as u64) << shot;
        }
        let mask = (1u64 << LOGICAL_Q) - 1;
        let bv = ((shot as u64 * 0x9e37 + 3) & mask) | 1;
        let lv = ((shot as u64 * 0x7f4a + 5) & mask) | 1;
        for k in 0..LOGICAL_Q {
            sim.qubits[c.bb[k].0 as usize] |= ((bv >> k) & 1) << shot;
            sim.qubits[c.ll[k].0 as usize] |= ((lv >> k) & 1) << shot;
        }
        for k in 0..PAGE {
            let old = ((shot + 3 * k) % 5 == 0) as u64;
            sim.qubits[c.page[k].0 as usize] |= old << shot;
        }
    }
    for k in 0..JB {
        put(&mut sim.qubits, c.j[k], expected_j[k]);
        put(&mut sim.qubits, c.gap_source[k], expected_g[k]);
    }
    let source_b: Vec<u64> = c.bb.iter().map(|q| sim.qubits[q.0 as usize]).collect();
    let source_l: Vec<u64> = c.ll.iter().map(|q| sim.qubits[q.0 as usize]).collect();
    let old_page: Vec<u64> = c.page.iter().map(|q| sim.qubits[q.0 as usize]).collect();

    sim.apply_iter(c.b.ops[..c.after_gap].iter());
    assert_eq!(sim.qubits[c.e.0 as usize], selected);
    for k in 0..JB {
        let want = (expected_j[k] & !selected) ^ (expected_g[k] & selected);
        assert_eq!(sim.qubits[c.j[k].0 as usize], want, "gap lane {k}");
    }
    assert!(c.tmp.iter().all(|q| sim.qubits[q.0 as usize] == 0));

    sim.apply_iter(c.b.ops[c.after_gap..c.after_hensel].iter());
    assert_eq!(sim.qubits[c.tmp[4].0 as usize], 0, "tmp[4] endpoint");
    assert!(c.tmp[..4].iter().all(|q| sim.qubits[q.0 as usize] == 0));
    assert_eq!(
        c.bb.iter()
            .map(|q| sim.qubits[q.0 as usize])
            .collect::<Vec<_>>(),
        source_b
    );
    assert_eq!(
        c.ll.iter()
            .map(|q| sim.qubits[q.0 as usize])
            .collect::<Vec<_>>(),
        source_l
    );
    assert_ne!(
        c.page
            .iter()
            .map(|q| sim.qubits[q.0 as usize])
            .collect::<Vec<_>>(),
        old_page
    );

    sim.apply_iter(c.b.ops[c.after_hensel..c.end].iter());
    assert_eq!(sim.qubits[c.e.0 as usize], 0);
    for k in 0..JB {
        assert_eq!(
            sim.qubits[c.j[k].0 as usize], expected_j[k],
            "restored j{k}"
        );
    }
    assert!(c.tmp.iter().all(|q| sim.qubits[q.0 as usize] == 0));
    assert_eq!(sim.phase, 0);
    eprintln!(
        "Q888_OWNER after_gap={} after_hensel={} end={} helper_hmrs={helper_hmrs}",
        c.after_gap, c.after_hensel, c.end
    );
}

fn factored_receipt(shot: usize, m: usize, r: usize) -> usize {
    if r == 0 {
        0
    } else if shot == 0 {
        0
    } else if shot <= r {
        1usize << (shot - 1)
    } else if shot == r + 1 {
        (1usize << r) - 1
    } else {
        (shot.wrapping_mul(0x9e37) ^ m.wrapping_mul(0x211)) & ((1usize << r) - 1)
    }
}

#[test]
fn q888_low19_factored_receipts_mixed_lengths_dirty_page() {
    let mut simulations = 0usize;
    let mut max_high_t = 0u64;
    let mut max_low_phase_t = 0u64;
    let mut high_t_by_m = [0u64; LOGICAL_Q + 1];
    let mut low_t_by_r = [0u64; LOGICAL_Q - PAGE + 1];
    let mut receipt_basis_seen = [false; LOGICAL_Q - PAGE];
    for m in 2usize..=LOGICAL_Q {
        let r = m.saturating_sub(PAGE);
        // Classical receipts enter only through ZIf gates, so phase is linear
        // over GF(2) in the receipt word.  A zero word, every basis vector,
        // their all-ones sum and deterministic mixed words prove the complete
        // 2^r transducer without naively enumerating 2^19 outcomes.
        let batches = 1usize;
        for batch in 0..batches {
            let mut b = B::new();
            let active = b.alloc();
            let bb = b.alloc_n(m);
            let ll = b.alloc_n(m);
            let page = b.alloc_n(PAGE);
            let helper = b.alloc();
            let passenger = b.alloc_n(3);
            let receipts = b.fresh_bits(r.max(1));
            let high = high_page_dirty_record(&mut b, active, &bb, &ll, &page, helper, m);
            let th = b.tof;
            b.play(&high, false);
            let high_t = b.tof - th;
            max_high_t = max_high_t.max(high_t);
            high_t_by_m[m] = high_t_by_m[m].max(high_t);
            let high_end = b.ops.len();
            let low = low_phase_record(&mut b, active, &bb, &ll, helper, &receipts, r);
            let supplied_receipts: Vec<BitId> = low
                .iter()
                .filter_map(|g| match g {
                    G::ZIf(_, bit) => Some(*bit),
                    _ => None,
                })
                .collect();
            assert_eq!(
                supplied_receipts,
                receipts[..r],
                "receipt dependence must be exactly one linear ZIf per low digit, m={m}"
            );
            let tl = b.tof;
            b.play(&low, false);
            let low_phase_t = b.tof - tl;
            max_low_phase_t = max_low_phase_t.max(low_phase_t);
            low_t_by_r[r] = low_t_by_r[r].max(low_phase_t);
            let end = b.ops.len();

            let helper_hmrs =
                2 * m.saturating_sub(3) + 2 * r.saturating_sub(3) + r.saturating_sub(1);
            let mut xof = Words::new(
                (0..helper_hmrs)
                    .map(|i| 0x9e37_79b9_7f4a_7c15u64.rotate_left((i + batch + m) as u32))
                    .collect(),
            );
            let mut sim = Simulator::new(b.width() as usize, 120_000 + m * 100 + batch, &mut xof);
            let active_mask = 0xeeee_eeee_eeee_eeeeu64;
            put(&mut sim.qubits, active, active_mask);
            let mut receipt_masks = vec![0u64; r];
            for shot in 0..64 {
                let receipt = factored_receipt(shot, m, r);
                if r == LOGICAL_Q - PAGE && (1..=r).contains(&shot) {
                    receipt_basis_seen[shot - 1] = true;
                }
                for k in 0..r {
                    receipt_masks[k] |= (((receipt >> k) & 1) as u64) << shot;
                }
            }
            for k in 0..r {
                sim.bits[receipts[k].0 as usize] = receipt_masks[k];
            }

            let mut expected_page = [0u64; PAGE];
            let mut old_page = [0u64; PAGE];
            let mut bm = vec![0u64; m];
            let mut lm = vec![0u64; m];
            let mut debt = 0u64;
            for shot in 0..64 {
                let case = batch * 64 + shot;
                let mask = (1u64 << m) - 1;
                let low_mask = if r == 0 { 0 } else { (1u64 << r) - 1 };
                let low_odd_space = if r <= 1 { 1 } else { 1usize << (r - 1) };
                let bi = case % low_odd_space;
                let li = (13 * case + 7 * shot + m) % low_odd_space;
                let mut bv =
                    ((shot as u64 * 0x9e37 + batch as u64 * 0x101 + m as u64 * 13 + 3) & mask) | 1;
                let mut lv =
                    ((shot as u64 * 0x7f4a + batch as u64 * 0x211 + m as u64 * 17 + 5) & mask) | 1;
                if r > 0 {
                    bv = (bv & !low_mask) | (1 + 2 * bi as u64);
                    lv = (lv & !low_mask) | (1 + 2 * li as u64);
                }
                let q = quotient(bv, lv, m);
                if r > 0 {
                    let high_q = q & !low_mask;
                    let changed_l = lv.wrapping_add(bv.wrapping_mul(high_q)) & mask;
                    assert_eq!(
                        quotient(bv & low_mask, changed_l & low_mask, r),
                        q & low_mask,
                        "low-residue invariant m={m} shot={shot}"
                    );
                    let receipt = factored_receipt(shot, m, r);
                    if (((q as usize) & receipt).count_ones() & 1) != 0
                        && ((active_mask >> shot) & 1) != 0
                    {
                        debt |= 1u64 << shot;
                    }
                }
                for k in 0..m {
                    bm[k] |= ((bv >> k) & 1) << shot;
                    lm[k] |= ((lv >> k) & 1) << shot;
                }
                for k in 0..PAGE {
                    let old = match shot % (PAGE + 2) {
                        0 => 1,
                        1 => 0,
                        s => (k == s - 2) as u64,
                    };
                    old_page[k] |= old << shot;
                    let active_shot = ((active_mask >> shot) & 1) != 0;
                    let mapped = k + m >= PAGE;
                    let logical = if mapped { k + m - PAGE } else { 0 };
                    let inject = active_shot && mapped && logical < m && ((q >> logical) & 1) != 0;
                    expected_page[k] |= (old ^ inject as u64) << shot;
                }
            }
            for k in 0..m {
                put(&mut sim.qubits, bb[k], bm[k]);
                put(&mut sim.qubits, ll[k], lm[k]);
            }
            for k in 0..PAGE {
                put(&mut sim.qubits, page[k], old_page[k]);
            }
            let passenger_before: Vec<u64> = passenger
                .iter()
                .enumerate()
                .map(|(i, &q)| {
                    let v = 0x243f_6a88_85a3_08d3u64.rotate_left((m + batch + 9 * i) as u32);
                    put(&mut sim.qubits, q, v);
                    v
                })
                .collect();
            let source_b = bm.clone();
            let source_l = lm.clone();
            sim.phase = debt; // exact debt left by the earlier digit measurements

            sim.apply_iter(b.ops[..high_end].iter());
            assert_eq!(sim.qubits[helper.0 as usize], 0, "m={m} helper after high");
            assert_eq!(sim.phase, debt, "high helper phase m={m} batch={batch}");
            assert_eq!(
                page.iter()
                    .map(|q| sim.qubits[q.0 as usize])
                    .collect::<Vec<_>>(),
                expected_page,
                "m={m} batch={batch}"
            );
            assert_eq!(
                bb.iter()
                    .map(|q| sim.qubits[q.0 as usize])
                    .collect::<Vec<_>>(),
                source_b
            );
            assert_eq!(
                ll.iter()
                    .map(|q| sim.qubits[q.0 as usize])
                    .collect::<Vec<_>>(),
                source_l
            );

            sim.apply_iter(b.ops[high_end..end].iter());
            assert_eq!(sim.phase, 0, "low19 receipt repayment m={m} batch={batch}");
            assert_eq!(
                sim.qubits[helper.0 as usize], 0,
                "m={m} helper after low phase"
            );
            assert_eq!(
                bb.iter()
                    .map(|q| sim.qubits[q.0 as usize])
                    .collect::<Vec<_>>(),
                source_b
            );
            assert_eq!(
                ll.iter()
                    .map(|q| sim.qubits[q.0 as usize])
                    .collect::<Vec<_>>(),
                source_l
            );
            for (i, &q) in passenger.iter().enumerate() {
                assert_eq!(sim.qubits[q.0 as usize], passenger_before[i]);
            }
            simulations += 1;
        }
    }
    assert!(receipt_basis_seen.into_iter().all(|x| x));
    assert_eq!(high_t_by_m[LOGICAL_Q], 1608);
    assert_eq!(low_t_by_r[19], 1114);
    eprintln!("Q888_MIXED simulations={simulations} lengths=22 receipt_rank=19 implied_receipts=524288 max_high_t={max_high_t} max_low_phase_t={max_low_phase_t} high_t_by_m={:?} low_t_by_r={:?}", &high_t_by_m[2..], &low_t_by_r);
}

#[test]
fn q888_five_boundary_partition_and_selector() {
    let js = [3usize, 7, 11, 15, 19];
    for h in 0usize..32 {
        let term0 = h & 1 != 0 && h & 0b11000 == 0;
        let term1 = h == 9;
        assert_eq!(term0 ^ term1, matches!(h, 1 | 3 | 5 | 7 | 9), "h={h}");
    }
    for g in 1usize..=22 {
        let omitted = (g + 1).saturating_sub(PAGE);
        let mut seen = vec![false; omitted];
        let mut boundaries = 0usize;
        for &j in &js {
            if j >= g { continue; }
            let s = g - j;
            let ks = s.saturating_sub(PAGE)..s;
            let mut lanes = std::collections::BTreeSet::new();
            for k in ks {
                assert!(k < omitted, "g={g} j={j} k={k} omitted={omitted}");
                assert!(!seen[k], "duplicate low digit g={g} j={j} k={k}");
                seen[k] = true;
                let lane = (PAGE - ((s - k) % PAGE)) % PAGE;
                assert!(lanes.insert(lane), "lane collision g={g} j={j} s={s} k={k}");
            }
            boundaries += 1;
        }
        assert!(seen.into_iter().all(|x| x), "incomplete omitted suffix g={g}");
        assert_eq!(boundaries, (omitted + PAGE - 1) / PAGE, "boundary count g={g}");
    }
    eprintln!("Q888_BOUNDARIES selectors=5 gaps=22 partition=PASS");
}

/// Exact helper-free row used when all five fixed scratch lanes hold the
/// page4 normalizer shift.  `dirty` may be arbitrary and is restored.
fn dirty_hensel_row(
    b: &mut B,
    a: &[QubitId],
    t: &[QubitId],
    active: QubitId,
    digit: QubitId,
    dirty: QubitId,
) {
    assert_eq!(a.len(), t.len());
    assert!(a.len() >= 2 && t[0] == digit);
    let cccx = |b: &mut B, x: QubitId, y: QubitId, z: QubitId, out: QubitId| {
        b.ccx(x, y, dirty);
        b.ccx(z, dirty, out);
        b.ccx(x, y, dirty);
        b.ccx(z, dirty, out);
    };
    let n = t.len();
    for i in 1..n { b.cx(a[i], t[i]); }
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], a[i], a[i + 1]); }
    for i in (1..n).rev() {
        cccx(b, active, digit, a[i], t[i]);
        b.ccx(t[i - 1], a[i - 1], a[i]);
    }
    for i in 1..n - 1 { b.cx(a[i], a[i + 1]); }
    for i in 1..n { b.cx(a[i], t[i]); }
}

#[test]
fn q888_helper_free_refill_row_matches_clean_reference() {
    const W: usize = 19;
    for byte in [0u8, 255, 170, 85] {
        let mut clean = B::new();
        let ce = clean.alloc();
        let ca = clean.alloc_n(W);
        let ct = clean.alloc_n(W);
        let ch = clean.alloc();
        clean.and_c(ce, ct[0], ch);
        ttk_add(&mut clean, &ca, &ct, Some(ch), None);
        clean.cx(ch, ct[0]);
        clean.and_u(ce, ct[0], ch);

        let mut dirty = B::new();
        let de = dirty.alloc();
        let da = dirty.alloc_n(W);
        let dt = dirty.alloc_n(W);
        let dd = dirty.alloc();
        dirty_hensel_row(&mut dirty, &da, &dt, de, dt[0], dd);
        let clean_t = clean.tof;
        let dirty_t = dirty.tof;

        let mut xc = Words::new(vec![u64::from_le_bytes([byte; 8]); 256]);
        let mut xd = Words::new(vec![u64::from_le_bytes([byte; 8]); 256]);
        let mut sc = Simulator::new(clean.width() as usize, 180_000 + byte as usize, &mut xc);
        let mut sd = Simulator::new(dirty.width() as usize, 181_000 + byte as usize, &mut xd);
        let mut dirty_before = 0u64;
        for shot in 0..64 {
            let av = ((shot as u64 * 7919 + 3) & ((1 << W) - 1)) | 1;
            let tv = (shot as u64 * 3571 + 5) & ((1 << W) - 1);
            for k in 0..W {
                sc.qubits[ca[k].0 as usize] |= ((av >> k) & 1) << shot;
                sd.qubits[da[k].0 as usize] |= ((av >> k) & 1) << shot;
                sc.qubits[ct[k].0 as usize] |= ((tv >> k) & 1) << shot;
                sd.qubits[dt[k].0 as usize] |= ((tv >> k) & 1) << shot;
            }
            if shot % 3 != 0 {
                sc.qubits[ce.0 as usize] |= 1 << shot;
                sd.qubits[de.0 as usize] |= 1 << shot;
            }
            if shot % 5 < 2 {
                sd.qubits[dd.0 as usize] |= 1 << shot;
                dirty_before |= 1 << shot;
            }
        }
        sc.apply_iter(clean.ops.iter());
        sd.apply_iter(dirty.ops.iter());
        assert_eq!(sd.qubits[dd.0 as usize], dirty_before, "dirty byte={byte}");
        assert_eq!(sc.qubits[ch.0 as usize], 0, "helper byte={byte}");
        assert_eq!(sc.phase, sd.phase, "phase byte={byte}");
        for k in 0..W {
            assert_eq!(sc.qubits[ca[k].0 as usize], sd.qubits[da[k].0 as usize], "a{k} byte={byte}");
            assert_eq!(sc.qubits[ct[k].0 as usize], sd.qubits[dt[k].0 as usize], "t{k} byte={byte}");
        }
        assert_eq!(dirty_t, 108);
        assert!(dirty_t > clean_t);
        eprintln!("Q888_DIRTY_HENSEL_STREAM byte={byte:02x} cleanT={clean_t} dirtyT={dirty_t}");
    }
    eprintln!("Q888_DIRTY_HENSEL width=19 receipts=4 dirtyT=108 PASS");
}

#[test]
fn q888_m_from_ct_v2_is_rejected_on_packed_walks() {
    let mut b = B::new();
    let x = b.alloc_n(256);
    let dirty = b.alloc_n(256);
    let dv = div_forward(&mut b, &x, &dirty);
    let mut xof = Words::new((0..4096)
        .map(|i| 0xd1b5_4a32_d192_ed03u64.rotate_left((7 * i) as u32))
        .collect());
    let mut sim = Simulator::new(b.width() as usize, 240_000, &mut xof);
    let mut rng = Rng::new(0x888);
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let mut xs: Vec<N> = vec![];
    while xs.len() < 64 {
        let mut xv = rng.below(256) % p();
        if xv == N::ZERO { continue; }
        if !xv.bit(0) { xv = p() - xv; }
        let mut model = M::new(xv);
        for t in 1..=sch.t { model.tick(t, &sch); }
        model.close(&sch);
        if model.bad.is_none() && model.absorbed() { xs.push(xv); }
    }
    let mut dirty_before = vec![0u64; dirty.len()];
    for (shot, xv) in xs.iter().copied().enumerate() {
        for k in 0..256 {
            if xv.bit(k) { sim.qubits[x[k].0 as usize] |= 1u64 << shot; }
        }
        for (k, &q) in dirty.iter().enumerate() {
            let bit = ((0x9e37_79b9_7f4a_7c15u64.rotate_left((k + shot) as u32) >> shot) & 1) << shot;
            sim.qubits[q.0 as usize] |= bit;
            dirty_before[k] |= bit;
        }
    }
    sim.apply_iter(b.ops.iter());
    let mut min_m = 64u64;
    let mut max_m = 0u64;
    let mut mismatches = 0usize;
    let mut first = None;
    let mut delta_hist = [0usize; 127];
    for shot in 0..64 {
        let m = get(&sim.qubits, &dv.mr, shot);
        let low = get(&sim.qubits, &dv.inv[..64], shot);
        assert_ne!(low, 0, "C_T has no set bit below 64, shot={shot} m={m}");
        let tz = low.trailing_zeros() as u64;
        let delta = tz as i64 - m as i64;
        delta_hist[(delta + 63) as usize] += 1;
        if tz != m {
            mismatches += 1;
            first.get_or_insert((shot, m, tz, low));
        }
        min_m = min_m.min(m);
        max_m = max_m.max(m);
    }
    for (k, &q) in dirty.iter().enumerate() {
        assert_eq!(sim.qubits[q.0 as usize], dirty_before[k], "dirty lane {k}");
    }
    assert!(mismatches > 0, "unexpectedly recovered m as v2(C_T) on all shots");
    let nonzero_delta: Vec<(i64, usize)> = delta_hist.iter().copied().enumerate()
        .filter(|(_, n)| *n != 0).map(|(i, n)| (i as i64 - 63, n)).collect();
    eprintln!("Q888_M_FROM_CT_REJECTED packed=64 mismatches={mismatches} min_m={min_m} max_m={max_m} delta_hist={nonzero_delta:?} first={first:?}");
}

/// Source-identical unabsorb with a variable prefix cache.  The frozen path
/// passes five clean prefix lanes (`tm[1..6]`).  `Dec`/`onehot_scan` also
/// support a shorter prefix and finish the remaining conjunction with the
/// existing arbitrary-state passenger lanes, restored by `mcx_dirty`.
fn unabsorb_with_tm(
    b: &mut B,
    w: &Walk,
    sch: &Sched,
    mr: &[QubitId],
    tm: &[QubitId],
    dirty: &[QubitId],
) -> (Vec<QubitId>, QubitId, Vec<G>) {
    assert!(!tm.is_empty());
    let t = sch.t + 1;
    let nm = 1usize << MB;
    let oh: Vec<QubitId> = (0..nm).map(|k| w.asig(t, k)).collect();
    let cl = sch.wb - sch.c[t];
    let mut r: Vec<QubitId> = (0..cl).map(|s| w.bsig(s)).collect();
    let ext: Vec<QubitId> = (0..RLEN - cl).map(|f| w.af(t, f)).collect();
    assert!(sch.wa - sch.c[t] - (RLEN - cl) >= nm);
    r.extend(&ext);
    let sg = tm[0];
    b.begin();
    for k in 0..nm {
        for i in 0..MB {
            if (k >> i) & 1 == 1 { b.cx(oh[k], mr[i]); }
        }
    }
    for k in (0..nm - 1).rev() { b.cx(oh[k + 1], oh[k]); }
    b.cx(r[cl - 1], sg);
    for &q in &ext { b.cx(sg, q); }
    for k in 0..nm - 1 { b.ccx(sg, oh[k + 1], r[RLEN - 1 - k]); }
    for i in 0..MB { crot_up(b, mr[i], &r, 1 << i); }
    b.cx(r[RLEN - 1], sg);
    for k in 0..nm - 1 { b.cx(oh[k + 1], oh[k]); }
    onehot_scan(b, mr, &tm[1..], 0, nm, 0, |b, v, ctrls| {
        mc_xor(b, ctrls, oh[v], &[], dirty);
    });
    let rec = b.end();
    b.play(&rec, false);
    (r, w.bf(1), rec)
}

struct UnabsorbCapsule {
    b: B,
    w: Walk,
    dirty: Vec<QubitId>,
    n0: QubitId,
    mr: Vec<QubitId>,
    tm: Vec<QubitId>,
    inv: Vec<QubitId>,
    key: QubitId,
    mid: usize,
    forward_t: u64,
}

fn unabsorb_capsule(tm_len: usize) -> UnabsorbCapsule {
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let mut b = B::new();
    let bb = b.alloc_n(sch.wb);
    let dirty = b.alloc_n(256); // coordinate-y passenger in the production geometry
    let a = b.alloc_n(sch.wa);
    let j = b.alloc_n(5);
    let par = b.alloc();
    let n0 = b.alloc();
    let w = Walk { a, bb, q: vec![], j, par };
    let mr = b.alloc_n(MB);
    let tm = b.alloc_n(tm_len);
    assert_eq!(b.live, 885 + tm_len as u64);
    let t0 = b.tof;
    let (inv, key, rec) = unabsorb_with_tm(&mut b, &w, &sch, &mr, &tm, &dirty);
    let forward_t = b.tof - t0;
    let mid = b.ops.len();
    b.play(&rec, true);
    UnabsorbCapsule { b, w, dirty, n0, mr, tm, inv, key, mid, forward_t }
}

fn init_absorbed(cap: &UnabsorbCapsule, sim: &mut Simulator<'_, Words>) {
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let t = sch.t + 1;
    let cl = sch.wb - sch.c[t];
    for shot in 0..64 {
        let m = (7 * shot + 3) & 63;
        let neg = shot & 1 == 1;
        let mag = (shot as u64 + 5).wrapping_mul(0x9e37) | 1;
        // A=(0,2^m), B.v=-2s, B.c=C in cl-bit two's complement.
        sim.qubits[cap.w.asig(t, m).0 as usize] |= 1u64 << shot;
        if neg { sim.qubits[cap.w.bf(1).0 as usize] |= 1u64 << shot; }
        let neg_low = 0u64.wrapping_sub(mag);
        for k in 0..cl {
            let bit = if neg {
                if k < 64 { (neg_low >> k) & 1 } else { 1 }
            } else if k < 64 {
                (mag >> k) & 1
            } else { 0 };
            sim.qubits[cap.w.bsig(k).0 as usize] |= bit << shot;
        }
        if shot % 3 == 1 { sim.qubits[cap.w.par.0 as usize] |= 1u64 << shot; }
        if shot % 5 < 2 { sim.qubits[cap.n0.0 as usize] |= 1u64 << shot; }
        for (k, &q) in cap.dirty.iter().enumerate() {
            let bit = (0xd1b5_4a32_d192_ed03u64.rotate_left((k + shot) as u32) >> shot) & 1;
            sim.qubits[q.0 as usize] |= bit << shot;
        }
    }
}

fn assert_same_masks(a: &Simulator<'_, Words>, aq: &[QubitId], b: &Simulator<'_, Words>, bq: &[QubitId], label: &str) {
    assert_eq!(aq.len(), bq.len());
    for (i, (&x, &y)) in aq.iter().zip(bq).enumerate() {
        assert_eq!(a.qubits[x.0 as usize], b.qubits[y.0 as usize], "{label}[{i}]");
    }
}

#[test]
fn q888_unabsorb_tm3_matches_tm6_and_restores_all_state() {
    let reference = unabsorb_capsule(6);
    let compact = unabsorb_capsule(3);
    assert_eq!((reference.b.peak, compact.b.peak), (891, 888));
    let intervals: Vec<(usize, usize, usize)> = reference.tm.iter().map(|&q| {
        let uses: Vec<usize> = reference.b.ops[..reference.mid].iter().enumerate()
            .filter(|(_, op)| op.q_target == q || op.q_control1 == q || op.q_control2 == q)
            .map(|(i, _)| i).collect();
        (*uses.first().unwrap(), *uses.last().unwrap(), uses.len())
    }).collect();
    for byte in [0u8, 255, 170, 85] {
        let word = u64::from_le_bytes([byte; 8]);
        let mut xr = Words::new(vec![word; 8192]);
        let mut xc = Words::new(vec![word; 8192]);
        let mut sr = Simulator::new(reference.b.width() as usize, 300_000 + byte as usize, &mut xr);
        let mut sc = Simulator::new(compact.b.width() as usize, 301_000 + byte as usize, &mut xc);
        init_absorbed(&reference, &mut sr);
        init_absorbed(&compact, &mut sc);
        let init_r = sr.qubits.clone();
        let init_c = sc.qubits.clone();
        sr.apply_iter(reference.b.ops[..reference.mid].iter());
        sc.apply_iter(compact.b.ops[..compact.mid].iter());
        assert_same_masks(&sr, &reference.inv, &sc, &compact.inv, "inv");
        assert_same_masks(&sr, &reference.mr, &sc, &compact.mr, "m");
        assert_same_masks(&sr, &[reference.key], &sc, &[compact.key], "key");
        assert_same_masks(&sr, &reference.dirty, &sc, &compact.dirty, "dirty-mid");
        assert_eq!(sr.phase, sc.phase, "phase-mid byte={byte}");
        assert!(reference.tm.iter().all(|q| sr.qubits[q.0 as usize] == 0));
        assert!(compact.tm.iter().all(|q| sc.qubits[q.0 as usize] == 0));
        sr.apply_iter(reference.b.ops[reference.mid..].iter());
        sc.apply_iter(compact.b.ops[compact.mid..].iter());
        assert_eq!(sr.qubits, init_r, "reference roundtrip byte={byte}");
        assert_eq!(sc.qubits, init_c, "compact roundtrip byte={byte}");
        assert_eq!((sr.phase, sc.phase), (0, 0), "roundtrip phase byte={byte}");
    }
    eprintln!("Q888_UNABSORB_TM tm6T={} tm3T={} deltaT={} peaks=891->888 receipts=4 intervals={intervals:?} PASS",
        reference.forward_t, compact.forward_t, compact.forward_t as i64 - reference.forward_t as i64);
}

fn unabsorb_j_alias_capsule() -> UnabsorbCapsule {
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let mut b = B::new();
    let bb = b.alloc_n(sch.wb);
    let dirty = b.alloc_n(256);
    let a = b.alloc_n(sch.wa);
    let j = b.alloc_n(5);
    let par = b.alloc();
    let n0 = b.alloc();
    let w = Walk { a, bb, q: vec![], j, par };
    let mr = b.alloc_n(MB);
    // At the post-close interface all shots have j=+1.  The stored half-
    // counter is therefore zero on all five lanes.  Borrow three of those
    // already-live lanes as sign/prefix scratch and restore them before exit.
    let tm = w.j[..3].to_vec();
    assert_eq!(b.live, 885);
    let t0 = b.tof;
    let (inv, key, rec) = unabsorb_with_tm(&mut b, &w, &sch, &mr, &tm, &dirty);
    let forward_t = b.tof - t0;
    let mid = b.ops.len();
    b.play(&rec, true);
    UnabsorbCapsule { b, w, dirty, n0, mr, tm, inv, key, mid, forward_t }
}

#[test]
fn q884_unabsorb_borrows_three_zero_j_lanes() {
    let reference = unabsorb_capsule(3);
    let alias = unabsorb_j_alias_capsule();
    assert_eq!((reference.b.peak, alias.b.peak), (888, 885));
    assert_eq!(reference.forward_t, alias.forward_t);
    for byte in [0u8, 255, 170, 85] {
        let word = u64::from_le_bytes([byte; 8]);
        let mut xr = Words::new(vec![word; 8192]);
        let mut xa = Words::new(vec![word; 8192]);
        let mut sr = Simulator::new(reference.b.width() as usize, 320_000 + byte as usize, &mut xr);
        let mut sa = Simulator::new(alias.b.width() as usize, 321_000 + byte as usize, &mut xa);
        init_absorbed(&reference, &mut sr);
        init_absorbed(&alias, &mut sa);
        let init_r = sr.qubits.clone();
        let init_a = sa.qubits.clone();
        sr.apply_iter(reference.b.ops[..reference.mid].iter());
        sa.apply_iter(alias.b.ops[..alias.mid].iter());
        assert_same_masks(&sr, &reference.inv, &sa, &alias.inv, "inv");
        assert_same_masks(&sr, &reference.mr, &sa, &alias.mr, "m");
        assert_same_masks(&sr, &[reference.key], &sa, &[alias.key], "key");
        assert_same_masks(&sr, &reference.dirty, &sa, &alias.dirty, "dirty");
        assert_eq!(sr.phase, sa.phase, "mid phase byte={byte}");
        assert!(alias.w.j.iter().all(|q| sa.qubits[q.0 as usize] == 0), "j alias endpoint byte={byte}");
        sr.apply_iter(reference.b.ops[reference.mid..].iter());
        sa.apply_iter(alias.b.ops[alias.mid..].iter());
        assert_eq!(sr.qubits, init_r, "reference inverse byte={byte}");
        assert_eq!(sa.qubits, init_a, "alias inverse byte={byte}");
        assert_eq!((sr.phase, sa.phase), (0, 0));
    }
    eprintln!("Q884_UNABSORB_J_ALIAS borrowed=j[0..3] peak=888->885 T={} receipts=4 PASS", alias.forward_t);
}

#[test]
fn q884_n0_is_early_parity_frame_offset() {
    for byte in [0u8, 255, 170, 85] {
        let mut r = B::new();
        let (rx, re, rk, rp, rn) = (r.alloc(), r.alloc(), r.alloc(), r.alloc(), r.alloc());
        let receipt = r.fresh_bits(1)[0];
        r.cx(rx, rn); r.x(rn);            // n0 = !x0
        r.cx(re, rp);                      // forward parity P
        r.cx(rp, rk); r.cx(rn, rk); r.x(rk);
        r.cx(rn, rp);                      // retained frame P ^ n0
        r.hmr_to(rn, receipt);
        r.x(rk); r.cx(rp, rk);             // undo sign key
        r.cx(re, rp);                      // inverse walk: frame -> n0
        r.z_if(rp, receipt);
        r.cx(rx, rp); r.x(rp);             // clear n0 from frame

        let mut c = B::new();
        let (cx, ce, ck, cp) = (c.alloc(), c.alloc(), c.alloc(), c.alloc());
        c.cx(cx, cp); c.x(cp);              // frame starts at n0
        c.cx(ce, cp);                       // forward parity P ^ n0
        c.cx(cp, ck); c.x(ck);              // same sign key
        c.x(ck); c.cx(cp, ck);              // undo sign key
        c.cx(ce, cp);                       // inverse frame -> n0
        c.cx(cx, cp); c.x(cp);              // clear

        let mut xr = Words::new(vec![u64::from_le_bytes([byte; 8]); 8]);
        let mut xc = Words::new(vec![]);
        let mut sr = Simulator::new(r.width() as usize, 350_000 + byte as usize, &mut xr);
        let mut sc = Simulator::new(c.width() as usize, 351_000 + byte as usize, &mut xc);
        let xm = 0xaaaa_5555_1234_f0f0u64;
        let em = 0x0f0f_f0f0_3333_ccccu64;
        let km = 0x9696_6996_a55a_5aa5u64;
        put(&mut sr.qubits, rx, xm); put(&mut sc.qubits, cx, xm);
        put(&mut sr.qubits, re, em); put(&mut sc.qubits, ce, em);
        put(&mut sr.qubits, rk, km); put(&mut sc.qubits, ck, km);
        sr.apply_iter(r.ops.iter());
        sc.apply_iter(c.ops.iter());
        assert_eq!(sr.qubits[rk.0 as usize], km);
        assert_eq!(sc.qubits[ck.0 as usize], km);
        assert_eq!(sr.qubits[rx.0 as usize], xm); assert_eq!(sc.qubits[cx.0 as usize], xm);
        assert_eq!(sr.qubits[re.0 as usize], em); assert_eq!(sc.qubits[ce.0 as usize], em);
        assert_eq!(sr.qubits[rp.0 as usize], 0); assert_eq!(sc.qubits[cp.0 as usize], 0);
        assert_eq!(sr.qubits[rn.0 as usize], 0);
        assert_eq!((sr.phase, sc.phase), (0, 0));
    }
    eprintln!("Q884_N0_PARITY_FRAME states=64 receipts=4 owners=2->1 PASS");
}

fn inc_flex(b: &mut B, ctrl: QubitId, bits: &[QubitId], tmp: &[QubitId], dirty: &[QubitId]) {
    if bits.is_empty() { return; }
    for i in (1..bits.len()).rev() {
        let mut lits = vec![(ctrl, false)];
        lits.extend(bits[..i].iter().map(|&q| (q, false)));
        mc_xor(b, &lits, bits[i], tmp, dirty);
    }
    b.cx(ctrl, bits[0]);
}

fn dec_flex(b: &mut B, ctrl: QubitId, bits: &[QubitId], tmp: &[QubitId], dirty: &[QubitId]) {
    for &q in bits { b.x(q); }
    inc_flex(b, ctrl, bits, tmp, dirty);
    for &q in bits { b.x(q); }
}

struct ForwardScratchCapsule {
    b: B,
    j: Vec<QubitId>,
    ci: QubitId,
    cd: QubitId,
    payload: Vec<QubitId>,
    dirty: Vec<QubitId>,
    tmp: Vec<QubitId>,
    witness: QubitId,
    invoice: [u64; 4],
}

fn forward_scratch_capsule(compact: bool) -> ForwardScratchCapsule {
    let mut b = B::new();
    let j = b.alloc_n(5);
    let ci = b.alloc();
    let cd = b.alloc();
    let payload = b.alloc_n(23);
    let dirty = b.alloc_n(32);
    let tmp = b.alloc_n(if compact { 2 } else { 5 });
    let eq = b.alloc();
    let flag = b.alloc();
    let witness = b.alloc();

    let t0 = b.tof;
    if compact {
        inc_flex(&mut b, ci, &j, &tmp, &dirty);
    } else {
        inc(&mut b, ci, &j, &tmp[..4]);
    }
    let t_inc = b.tof - t0;
    let td = b.tof;
    if compact {
        dec_flex(&mut b, cd, &j, &tmp, &dirty);
    } else {
        dec(&mut b, cd, &j, &tmp[..4]);
    }
    let t_dec = b.tof - td;
    let te = b.tof;
    if compact {
        let zl: Vec<(QubitId, bool)> = j.iter().map(|&q| (q, true)).collect();
        mc_xor(&mut b, &zl, eq, &tmp, &dirty);
        b.cx(eq, witness);
        mc_xor(&mut b, &zl, eq, &tmp, &dirty);
    } else {
        let zl: Vec<(QubitId, bool)> = j.iter().map(|&q| (q, true)).collect();
        let rec = and_lits(&mut b, &zl, eq, &tmp[..3]);
        b.play(&rec, false);
        b.cx(eq, witness);
        b.play(&rec, true);
    }
    let t_eq = b.tof - te;
    let ta = b.tof;
    let mut absorb = vec![(j[4], false)];
    absorb.extend(payload.iter().map(|&q| (q, true)));
    mc_xor(&mut b, &absorb, flag, &tmp, &dirty);
    b.cx(flag, witness);
    mc_xor(&mut b, &absorb, flag, &tmp, &dirty);
    let t_absorb = b.tof - ta;
    ForwardScratchCapsule { b, j, ci, cd, payload, dirty, tmp, witness, invoice: [t_inc, t_dec, t_eq, t_absorb] }
}

#[test]
fn q884_forward_tmp2_matches_tmp5_with_dirty_passenger() {
    let reference = forward_scratch_capsule(false);
    let compact = forward_scratch_capsule(true);
    for byte in [0u8, 255, 170, 85] {
        let word = u64::from_le_bytes([byte; 8]);
        let mut xr = Words::new(vec![word; 4096]);
        let mut xc = Words::new(vec![word; 4096]);
        let mut sr = Simulator::new(reference.b.width() as usize, 360_000 + byte as usize, &mut xr);
        let mut sc = Simulator::new(compact.b.width() as usize, 361_000 + byte as usize, &mut xc);
        for shot in 0..64 {
            let jv = shot & 31;
            for k in 0..5 {
                sr.qubits[reference.j[k].0 as usize] |= (((jv >> k) & 1) as u64) << shot;
                sc.qubits[compact.j[k].0 as usize] |= (((jv >> k) & 1) as u64) << shot;
            }
            if shot & 1 == 1 { sr.qubits[reference.ci.0 as usize] |= 1 << shot; sc.qubits[compact.ci.0 as usize] |= 1 << shot; }
            if shot % 3 == 1 { sr.qubits[reference.cd.0 as usize] |= 1 << shot; sc.qubits[compact.cd.0 as usize] |= 1 << shot; }
            for k in 0..23 {
                let bit = ((shot * 13 + k * 7 + 3) & 1) as u64;
                sr.qubits[reference.payload[k].0 as usize] |= bit << shot;
                sc.qubits[compact.payload[k].0 as usize] |= bit << shot;
            }
            for k in 0..32 {
                let bit = (0x9e37_79b9_7f4a_7c15u64.rotate_left((shot + k) as u32) >> shot) & 1;
                sr.qubits[reference.dirty[k].0 as usize] |= bit << shot;
                sc.qubits[compact.dirty[k].0 as usize] |= bit << shot;
            }
        }
        let dirty_r: Vec<u64> = reference.dirty.iter().map(|q| sr.qubits[q.0 as usize]).collect();
        let dirty_c: Vec<u64> = compact.dirty.iter().map(|q| sc.qubits[q.0 as usize]).collect();
        sr.apply_iter(reference.b.ops.iter());
        sc.apply_iter(compact.b.ops.iter());
        assert_same_masks(&sr, &reference.j, &sc, &compact.j, "j");
        assert_same_masks(&sr, &reference.payload, &sc, &compact.payload, "payload");
        assert_same_masks(&sr, &[reference.witness], &sc, &[compact.witness], "witness");
        assert_eq!(reference.dirty.iter().map(|q| sr.qubits[q.0 as usize]).collect::<Vec<_>>(), dirty_r);
        assert_eq!(compact.dirty.iter().map(|q| sc.qubits[q.0 as usize]).collect::<Vec<_>>(), dirty_c);
        assert!(reference.tmp.iter().all(|q| sr.qubits[q.0 as usize] == 0));
        assert!(compact.tmp.iter().all(|q| sc.qubits[q.0 as usize] == 0));
        assert_eq!(sr.phase, sc.phase, "phase byte={byte}");
    }
    eprintln!("Q884_FORWARD_TMP tmp5T={} tmp2T={} deltaT={} invoice_ref={:?} invoice_tmp2={:?} owners=9->6 receipts=4 PASS",
        reference.b.tof, compact.b.tof, compact.b.tof as i64 - reference.b.tof as i64,
        reference.invoice, compact.invoice);
}

/// A direct clean-carry relabel of the four coherent absorption-counter lanes
/// is unsound.  This is the cheapest discriminating gate for the Q888 product
/// peak: keep 48 genuinely clean carries, append four arbitrary `m` bits to
/// the logical pool, and run the unchanged Q892 constant-add ladder.  A valid
/// alias would restore `m`, clear all carries and match exact addition for
/// every shot/outcome stream.  The test deliberately passes only when that
/// proposed relabel is falsified by a concrete witness.
#[test]
fn q888_direct_dirty_m_as_clean_carries_is_rejected() {
    let mut b = B::new();
    let t = b.alloc_n(64);
    let h = b.alloc();
    let clean = b.alloc_n(48);
    let m = b.alloc_n(4);
    let mut logical_pool = clean.clone();
    logical_pool.extend(&m);
    const_add_pool_test(&mut b, &t, h, C, &logical_pool);
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut total_bad = 0usize;
    let mut first = None;
    for (stream_id, word) in [0u64, u64::MAX, 0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555]
        .into_iter()
        .enumerate()
    {
        let mut xof = Words::new(vec![word; 1024]);
        let mut sim = Simulator::new(
            (nq as usize).max(b.width() as usize),
            (nb as usize).max(1),
            &mut xof,
        );
        let mut input_t = [0u64; 64];
        let mut input_m = [0u8; 64];
        for shot in 0..64 {
            let tv = (shot as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
                ^ (stream_id as u64).wrapping_mul(0xd1b5_4a32_d192_ed03);
            let mv = ((shot * 11 + stream_id * 5 + 3) & 15) as u8;
            input_t[shot] = tv;
            input_m[shot] = mv;
            for k in 0..64 {
                sim.qubits[t[k].0 as usize] |= ((tv >> k) & 1) << shot;
            }
            if shot & 1 == 1 {
                sim.qubits[h.0 as usize] |= 1u64 << shot;
            }
            for k in 0..4 {
                sim.qubits[m[k].0 as usize] |= (((mv >> k) & 1) as u64) << shot;
            }
        }
        sim.apply_iter(b.ops.iter());
        for shot in 0..64 {
            let got = get(&sim.qubits, &t, shot);
            let want = input_t[shot].wrapping_add(if shot & 1 == 1 { C } else { 0 });
            let got_m = get(&sim.qubits, &m, shot) as u8;
            let clean_dirty = clean
                .iter()
                .any(|q| ((sim.qubits[q.0 as usize] >> shot) & 1) != 0);
            let bad = got != want
                || got_m != input_m[shot]
                || clean_dirty
                || ((sim.phase >> shot) & 1) != 0;
            if bad {
                total_bad += 1;
                first.get_or_insert((
                    stream_id,
                    shot,
                    input_t[shot],
                    input_m[shot],
                    got,
                    got_m,
                    (sim.phase >> shot) & 1,
                ));
            }
        }
    }
    assert!(
        total_bad > 0,
        "unexpectedly accepted dirty carries as clean AND targets"
    );
    eprintln!("Q888_DIRTY_M_DIRECT_ALIAS rejected bad={total_bad}/256 first={first:?}");
}

fn parse_schedule() -> (usize, usize, usize, Vec<usize>) {
    let mut it = include_str!("sched_frogtail.txt")
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .flat_map(|l| l.split_whitespace())
        .map(|x| x.parse::<usize>().unwrap());
    let wa = it.next().unwrap();
    let wb = it.next().unwrap();
    let t = it.next().unwrap();
    let mut c = vec![0];
    c.extend(it);
    assert_eq!(c.len(), t + 2);
    (wa, wb, t, c)
}

fn parse_lsc(t: usize) -> (Vec<usize>, Vec<usize>) {
    let mut it = include_str!("lsc_frogtail.txt")
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .flat_map(|l| l.split_whitespace())
        .map(|x| x.parse::<usize>().unwrap());
    assert_eq!(it.next().unwrap(), t);
    let mut kv = vec![0];
    let mut kc = vec![0];
    for _ in 1..=t {
        kv.push(it.next().unwrap());
        kc.push(it.next().unwrap());
    }
    (kv, kc)
}

fn local_zero_hosts(
    tick: usize,
    wb: usize,
    total_t: usize,
    c: &[usize],
    kv: &[usize],
    kc: &[usize],
) -> usize {
    let tz = (tick + 1).min(total_t);
    let (boundary, value_width, coeff_width) = if tick < total_t {
        (c[tick + 1], kv[tick + 1], kc[tick + 1])
    } else {
        (c[tz + 1], c[tz + 1], wb - c[tz + 1])
    };
    2 * (boundary - value_width)
        + (wb - boundary).saturating_sub(coeff_width.max(46))
        + (wb - boundary).saturating_sub(coeff_width.max(23))
}

#[test]
fn q888_late_tick_540_542_has_no_local_clean_host() {
    let (wa, wb, total_t, c) = parse_schedule();
    let (kv, kc) = parse_lsc(total_t);
    assert_eq!((wa, wb, total_t), (308, 308, 556));
    let mut bins = [0usize; 4];
    for tick in (4..=total_t).step_by(2) {
        let z = local_zero_hosts(tick, wb, total_t, &c, &kv, &kc);
        if z >= 6 {
            bins[0] += 1;
        } else if z >= 2 {
            bins[1] += 1;
        } else if z == 1 {
            bins[2] += 1;
        } else {
            bins[3] += 1;
        }
    }
    assert_eq!(bins, [212, 20, 0, 45]);
    assert_eq!(local_zero_hosts(540, wb, total_t, &c, &kv, &kc), 0);
    assert_eq!(local_zero_hosts(542, wb, total_t, &c, &kv, &kc), 0);
    assert_eq!(308 + 308 + 256 + 5 + 1 + 6 + PAGE, 888);
    eprintln!("Q888_LATE hosts540=0 hosts542=0 census={bins:?} standing_scratch=6 peak=888");
}
