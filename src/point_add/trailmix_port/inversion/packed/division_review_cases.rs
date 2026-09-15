//! Adversarial review cases for the packed division (child module of
//! `division_selftest.rs`; runs inside its `run()` with the same harness):
//!
//! * **Part A - adversarial real inputs**: 24 inputs picked by a classical
//!   search over 160k inputs of the exact `pz_prefix` recurrence (the largest
//!   drop d = 25 and shift s = 25, d = 24 at steps 324/382, the 141-row tight
//!   input, `e_A = W_A` with off = 1 on a tight row, `e_A = W_A` with off = 0,
//!   B = 1 inexact rows with d = 10 and the widest terminal shift s = 9, rows
//!   with an empty field `d >= E` and `d > E` (the MSB in A's wrapped low bits),
//!   inputs terminating at 368, 369, 374, 380, 384, 388..400 (every step) and
//!   at 518, and the input with the deepest `lo_b` miss under the static
//!   tables). Every step 0..530 forward + backward, misses classified.
//! * **Part B - synthetic division rows** at steps 100, 250, 300, 365, 378,
//!   400, 480, 529: `e_A = W_A` with off in {0, 1} and tight R1 (cb's MSB at
//!   wire `e_A`), tight R2 (ca's MSB at wire `e_B`, or at `e_B + 1` with the
//!   spare bit on off = 1 rows), `e_B = W_A` (s_raw = 0), `s_raw = 2^rb - 1`
//!   (the maximal rotation), the maximal supported drop `d = n_w - 1 + off`
//!   (31 / 32) and one beyond it (`drop_bound` miss), the empty-field rows
//!   `d = E` and `d > E`, `e_B = lo_b + 1` (the D11 ring bottom `L > 0`) with
//!   off = 0 and the always-tying off = 1 variant (residue miss), terminal rows
//!   with s = 0, 27, 28 (the D0 window's last leaf) and s = 29..31
//!   (`term_window` miss), B = 1 inexact rows with d = 31 (s = 31), a B = 1 row
//!   with `s_raw >= 2^rb` (`shift` miss). (No `width_c` kind: the packing
//!   invariant puts ca's MSB at a wire >= e_B >= zone_start, asserted.) Every
//!   row forward + backward; the on-support rows value-checked, the miss rows
//!   inverse-checked only. q always carries bits above s (as on the walk).
//!
//! Assertions: every class non-empty, every on-support row exact, every row
//! restored by `division_backward`, phase 0, ancillae clean.

use super::*;

/// Adversarial inputs (hex, `x` before the `p - x` fold), see the module doc.
const ADVERSARIAL: &[(&str, &str)] = &[
    ("dmax25_smax25_gap24@230", "0x6b3a2b6f3a4ff7674fd048f7deef389b257a7694c60cc0f3733432b2fa21fbf8"),
    ("s24@384_d24@382", "0xa2010b2871aa05a7abfeaf52e4a5d2a97a6a2fe00c14c476ef07878e271e9415"),
    ("d24@324", "0x8922ed3c82499ac80f3b55b0027519486ab898b8c4abb17accc5338f3c2b0e7c"),
    ("d23@316", "0xe4321501171736c45c4945e32d9ae2f6c4e5991a416428226c78ace087cb2eeb"),
    ("tight141", "0x9bee33a38a5a22656c9cfe3de7b135db25f674c68a394c471c6f7327caefe028"),
    ("eawa_off1_tight8", "0x46c1b61950face2cc720753e6bd7964db655b626bfe14b9b004485a7f29ab0ad"),
    ("eawa_off0_4_ebwa2", "0xb6e4ddd2c8714f3ed0e486097d2f19bb351c3ce404ba140f5996fde0df08d95f"),
    ("b1inexact_d10_terms9", "0x0f119cdb07417ee6843d85d87eaf026c129a531a41f3cd02ceef336459d63291"),
    ("dgtE6", "0xeeb306e83275209ab7f652f5cbc8324b8e928fa281510a435e3bfe6f630e0f5f"),
    ("dgeE_d17", "0x68e0e4ea8cb2a2ba16623f226c7d9f845fcc356e2ab930acea4d9f3506b395da"),
    ("term368_lobmiss12", "0x35e1602a58377ba9a2a4e9cc0f1397a2385273afdc3a3c3613748c64b887b695"),
    ("term369", "0xc51f1c4ff785b67fcf8ab80c33e311375dfdd4ba96ddc82798b4a45b7a3b0294"),
    ("term374", "0x32e78b8742913030291842d2ba0c07aa4e136cacb6283de708f40b7618856d3e"),
    ("term380", "0x16531faa5ecaa4ab79ab476eea0d6ae366f94575cd0367ef0c0dbb3222425d7a"),
    ("term384", "0xcc8986872393e9c0cdd12361801168a46a6b306f8a1015a465d06bfddd5566db"),
    ("term388", "0x98bd2bf04841700b4ec35b74f867ed48079c7b1c6b6a564f10a1365f1f0f46e8"),
    ("term390", "0x1ffe8d4ae05d1bd394d9c8b056c97dc700900c4942887023a3dfcc1161b36f77"),
    ("term392", "0x4128a30a7c3b0dd547f914f069a2c505c61266552007dcd9cdf3fa9e2cce0b63"),
    ("term394", "0xd71d9e1f3c2a13642f1de4a5badfabda2858590576e82df2784a95265ede1210"),
    ("term396", "0xfd7756f14b04857189af70cd351bbecb68f10d82d057da34505ccfc195d05e49"),
    ("term398", "0x79b59cfbeed295ee2a0a6df4a4c2a903222afa73558a7ba2d48838ff3ce2188c"),
    ("term399", "0x95d43be782f27176e5152916080b33ddb391a78e05f488994b23dfca3ba42cb4"),
    ("term400", "0x569dd5378802bc80912071dad195a724f5ea730775ffe52504f26c595056900f"),
    ("term518", "0x8e99f8791e270fcd9d264055cdd01a7c1030439f8226e279b2fc7bbe6cfe3277"),
];

fn parse_hex(s: &str) -> U512 {
    let s = s.trim_start_matches("0x");
    let mut v = U512::ZERO;
    for ch in s.chars() {
        v = (v << 4) + U512::from(ch.to_digit(16).expect("hex") as u64);
    }
    v
}

struct Rng(sha3::Shake256Reader);

impl Rng {
    fn new(label: &str) -> Self {
        let mut seed = Shake256::default();
        seed.update(b"packed-division-review-v1");
        seed.update(label.as_bytes());
        Self(seed.finalize_xof())
    }
    /// A random value of exactly `bits` bits (0 for `bits == 0`).
    fn exact(&mut self, bits: usize) -> U512 {
        if bits == 0 {
            return U512::ZERO;
        }
        self.below(bits - 1) | (one() << (bits - 1))
    }
    /// A random value below `2^bits`.
    fn below(&mut self, bits: usize) -> U512 {
        let mut bytes = [0u8; 64];
        self.0.read(&mut bytes);
        let v = U512::from_le_bytes(bytes);
        if bits >= 512 { v } else { v & ((one() << bits) - one()) }
    }
}

/// A division row from the raw state: `s_raw`, `off`, `s`, `A_new` by the
/// `pz_prefix` rule; asserts the row is a division (`A >= B << s`).
fn synth(a: U512, b: U512, ca: U512, cb: U512, q: U512) -> Row {
    assert!(!a.is_zero() && !b.is_zero());
    let s_raw = bl(&a) as i64 - bl(&b) as i64;
    assert!(s_raw >= 0, "synth: A narrower than B");
    let off = a < (b << (s_raw as usize));
    let s = s_raw - i64::from(off);
    assert!(s >= 0, "synth: A < B");
    let s = s as usize;
    let bsh = b << s;
    assert!(a >= bsh, "synth: A < B << s");
    assert!(ca < cb, "synth: ca >= cb is not a division row");
    Row { a, b, ca, cb, q, kind: Kind::Div, s, off, a_new: a - bsh }
}

/// `q` with random bits above `s` (the quotient of the preceding division
/// rows of the same run) inside the `wq`-bit envelope, bit `s` clear.
fn q_above(rng: &mut Rng, s: usize, wq: usize) -> U512 {
    if s + 1 >= wq {
        return U512::ZERO;
    }
    rng.below(wq - s - 1) << (s + 1)
}

/// Coefficients for a synthetic row: `cb` of `bl_cb` bits, `ca` of `bl_ca`
/// bits (`ca < cb`).
fn coefs(rng: &mut Rng, bl_cb: usize, bl_ca: usize) -> (U512, U512) {
    assert!(bl_ca <= bl_cb && bl_cb >= 1);
    let bl_ca = if bl_ca == bl_cb && bl_cb == 1 { 0 } else { bl_ca };
    loop {
        let cb = rng.exact(bl_cb);
        let ca = rng.exact(bl_ca);
        if ca < cb {
            return (ca, cb);
        }
    }
}

/// off = 0 row: `A >> s_raw = B + R` with `bl(R) = e_B - d` (`R = 0` for
/// `d >= e_B`: the empty-field case, `A_new`'s MSB among A's low `s` bits;
/// `low` = A's low `s_raw` bits, bit-length `bl_low`).
fn row_off0(rng: &mut Rng, e_b: usize, s_raw: usize, d: usize, bl_low: usize) -> (U512, U512) {
    assert!(e_b >= 2 && bl_low <= s_raw);
    let (b, r) = if d >= e_b {
        (rng.exact(e_b), U512::ZERO)
    } else if d == 1 {
        // B = 2^(e_B-1) + r1, R = 2^(e_B-2) + r2, r1, r2 < 2^(e_B-3): B + R < 2^e_B.
        assert!(e_b >= 3);
        let b = (one() << (e_b - 1)) | rng.below(e_b - 3);
        let r = (one() << (e_b - 2)) | rng.below(e_b - 3);
        (b, r)
    } else {
        // B = 2^(e_B-1) + r1 (r1 < 2^(e_B-2)), R of e_B - d <= e_B - 2 bits.
        let b = (one() << (e_b - 1)) | rng.below(e_b - 2);
        (b, rng.exact(e_b - d))
    };
    assert!(bl(&(b + r)) == e_b);
    let low = rng.exact(bl_low);
    let a = ((b + r) << s_raw) | low;
    (a, b)
}

/// off = 1 row: `A >> s = B + R` with `bl(A >> s) = e_B + 1`, `R < B`,
/// `bl(R) = e_B + 1 - d` (so `A >> s_raw < B`); `s = s_raw - 1`.
fn row_off1(rng: &mut Rng, e_b: usize, s_raw: usize, d: usize, bl_low: usize) -> (U512, U512) {
    assert!(s_raw >= 1 && e_b >= 2 && d >= 1 && d <= e_b && bl_low <= s_raw - 1);
    let s = s_raw - 1;
    let bl_r = e_b + 1 - d;
    // B = 2^e_B - 1 - t with t < 2^(bl_r - 2): then 2^e_B - B = 1 + t <= 2^(bl_r-1) <= R and
    // the admissible R range [2^e_B - B, B) covers at least a quarter of the bl_r-bit values.
    let t = if bl_r >= 2 { rng.below(bl_r - 2) } else { U512::ZERO };
    let b = ((one() << e_b) - one()) - t;
    let r = loop {
        let r = rng.exact(bl_r);
        if r + b >= (one() << e_b) && r < b {
            break r;
        }
    };
    let low = rng.exact(bl_low);
    let a = ((b + r) << s) | low;
    assert_eq!(bl(&a), e_b + s_raw);
    assert!((a >> s_raw) < b);
    (a, b)
}

/// off = 1 row whose D4 window `[cascade_lo, e_B)` TIES: `B` odd with its bits
/// `e_B - 1` and `e_B - 2` set, `A >> s_raw = B - 1` (the operands differ only
/// at bit 0, below the cascade bottom `cascade_lo >= 1`), so `[A >> s_raw < B]`
/// is captured as 0 although it is 1 (the residue miss, d = 1). `s = s_raw - 1`.
fn row_off1_tie(rng: &mut Rng, e_b: usize, s_raw: usize, cascade_lo: usize) -> (U512, U512) {
    assert!(cascade_lo >= 1 && e_b >= cascade_lo + 3 && s_raw >= 1);
    let b = (one() << (e_b - 1)) | (one() << (e_b - 2)) | rng.below(e_b - 2) | one();
    let v = b - one();
    let low = rng.below(s_raw);
    let a = (v << s_raw) | low;
    assert_eq!(bl(&a), e_b + s_raw);
    assert!((a >> s_raw) < b);
    assert_eq!((a >> s_raw) >> cascade_lo, b >> cascade_lo, "the D4 window must tie");
    (a, b)
}

/// off = 1 row whose D4 window `[lo, e_B)` does not tie (`A >> s_raw` vs `B`) and
/// whose D9 window does not tie (`~B` vs `R`): the captured flags are then exact,
/// not the residue. Retried (a tie on `k` cells has probability ~2^-k).
fn row_off1_notie(rng: &mut Rng, e_b: usize, s_raw: usize, d: usize, bl_low: usize, lo: usize) -> (U512, U512) {
    for _ in 0..256 {
        let (a, b) = row_off1(rng, e_b, s_raw, d, bl_low);
        let s = s_raw - 1;
        let v4 = (a >> s_raw) >> lo;
        let u4 = b >> lo;
        let mask = (one() << e_b) - one();
        let r = (a - (b << s)) >> s;
        let nb = (mask ^ b) >> lo;
        let rr = r >> lo;
        if v4 != u4 && nb != rr {
            return (a, b);
        }
    }
    panic!("row_off1_notie: no tie-free row for e_B {e_b}, lo {lo}, d {d}");
}

#[derive(Default, Debug)]
struct ReviewCounts {
    adv_div_rows: usize,
    adv_checked: usize,
    adv_terminal_365_400: usize,
    adv_d_max: usize,
    adv_s_max: usize,
    adv_field_empty: usize,
    adv_field_empty_wrapped: usize,
    adv_lo_b_miss: usize,
    adv_eawa_off1: usize,
    adv_tight_eawa: usize,
    synth_rows: usize,
    synth_checked: usize,
    synth_miss: usize,
}

/// Miss-kind snapshot of the base harness's counters.
fn miss_snapshot(cnt: &Counts) -> [usize; 9] {
    [cnt.miss_width_a, cnt.miss_width_q, cnt.miss_lo_b, cnt.miss_rot, cnt.miss_drop, cnt.miss_term_row, cnt.miss_term_window, cnt.miss_residue4, cnt.miss_residue9]
}
const MISS_NAMES: [&str; 9] = ["width_a", "width_q", "lo_b", "rot", "drop", "term_row", "term_window", "residue4", "residue9"];

/// The refined `lo_b` support of the built division (review finding, updated
/// for the widened geometry of `sched.rs`): the harness's `lo_b` miss is
/// `e_B < win.lo` (below the D4/D9 capture window: `lo_b + 1` while `lo_b >
/// 32`, else 1) or `E = e_B + off < zone_start` (the D7 toggle leaf below the
/// masked zone, `zone_start = min(257 - W_c, lo_b + 1)`). Such a row is still
/// EXACT when
/// (a) off = 0 or `e_B >= win.lo` (D4/D9 capture the right flag),
/// (b) D7 stays exact: `E >= zone_start` (the masked cells then mask ca as
///     designed) or, when `E < zone_start` (the thermometer never toggles and
///     EVERY window cell is plain), no ca bit lies in the window at all:
///     `257 - e_ca >= W_A`;
/// (c) D11's ring holds the window: `lo_b <= 32` (`L = 0`) or `e_B >= lo_b`.
/// Rows failing (b) are HARD misses (ca bits added into R1 by plain cells),
/// not capture residues. With the zone from `257 - W_c` on the late rows and
/// the capture window from 1 once `lo_b <= 32`, the B = 1 rows of the
/// terminal-aware steps are on the support wherever `W_c = 256`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum LoB {
    OnSupport,
    Soft,
    HardCaInPlainCell,
    HardOff1,
    HardRing,
}

fn lo_b_class(row: &Row, sched: &StepWidths) -> LoB {
    let e_b = bl(&row.b);
    let win = sched.div_capture_window();
    let e_e = e_b + usize::from(row.off);
    if e_b >= win.lo && sched.div_zone_admits(e_e) {
        return LoB::OnSupport;
    }
    let e_ca = bl(&row.ca);
    if !sched.div_zone_admits(e_e) && e_ca > 0 && RING - e_ca < sched.w_a {
        return LoB::HardCaInPlainCell;
    }
    if row.off && e_b < win.lo {
        return LoB::HardOff1;
    }
    if sched.lo_b > 32 && e_b < sched.lo_b {
        return LoB::HardRing;
    }
    LoB::Soft
}

/// One shot with the refined `lo_b` support: a row whose only miss kind is
/// `lo_b` and whose class is `Soft` is value-checked after all.
fn shot_refined(row: &Row, sched: &StepWidths, wq: usize, with_term: bool, gate: bool, cnt: &mut Counts, lob: &mut BTreeMap<LoB, (usize, usize)>) -> (Shot, bool) {
    let before = miss_snapshot(cnt);
    let checked_before = cnt.div_checked;
    let mut sh = shot(row, sched, wq, with_term, gate, cnt);
    let mut checked = cnt.div_checked > checked_before;
    if gate {
        let after = miss_snapshot(cnt);
        let only_lo_b = after[2] == before[2] + 1 && (0..9).all(|i| i == 2 || after[i] == before[i]);
        let class = lo_b_class(row, sched);
        let e = lob.entry(class).or_insert((0, 0));
        if class == LoB::Soft && only_lo_b {
            sh.check = true;
            checked = true;
            e.0 += 1;
        } else if class != LoB::OnSupport {
            assert!(!checked, "a lo_b-miss row was value-checked by the base harness");
            e.1 += 1;
        }
    }
    (sh, checked)
}

pub(super) fn run(term_from: usize, cnt: &mut Counts, circuits: &mut usize) {
    let mut rc = ReviewCounts::default();

    // ---------------------------------------------------------------- Part A
    let inputs: Vec<(String, U512)> = ADVERSARIAL.iter().map(|(n, h)| (n.to_string(), parse_hex(h))).collect();
    let traces: Vec<Vec<Row>> = inputs.iter().map(|(_, x)| trace(*x)).collect();
    for ((name, _), t) in inputs.iter().zip(&traces) {
        let term_step = t.iter().position(|r| r.terminal()).expect("terminates");
        if let Some(want) = name.strip_prefix("term").and_then(|s| s.split('_').next()).and_then(|s| s.parse::<usize>().ok()) {
            assert_eq!(term_step, want, "{name}: terminal step");
        }
        if (365..=400).contains(&term_step) {
            rc.adv_terminal_365_400 += 1;
        }
    }
    let miss_before = miss_snapshot(cnt);
    let mut lob: BTreeMap<LoB, (usize, usize)> = BTreeMap::new();
    for step in 0..NSTEPS {
        let sched = StepWidths::from_schedule(step);
        let wq = sched.w_q.clamp(1, 1 << SROT);
        let with_term = step >= term_from;
        let mut shots = Vec::with_capacity(traces.len());
        for t in &traces {
            let row = &t[step];
            let before_lo_b = cnt.miss_lo_b;
            let (sh, checked) = shot_refined(row, &sched, wq, with_term, row.kind == Kind::Div, cnt, &mut lob);
            if row.kind == Kind::Div {
                rc.adv_div_rows += 1;
                if checked {
                    rc.adv_checked += 1;
                    let e_a = bl(&row.a);
                    let e_b = bl(&row.b);
                    let off = usize::from(row.off);
                    let d = e_a - bl(&row.a_new);
                    if !row.terminal() {
                        rc.adv_d_max = rc.adv_d_max.max(d);
                        if d >= e_b + off {
                            rc.adv_field_empty += 1;
                        }
                        if d > e_b + off {
                            rc.adv_field_empty_wrapped += 1;
                        }
                    }
                    rc.adv_s_max = rc.adv_s_max.max(row.s);
                    if e_a == sched.w_a && row.off {
                        rc.adv_eawa_off1 += 1;
                    }
                    if e_a == sched.w_a && RING - e_a - bl(&row.cb) == 0 {
                        rc.adv_tight_eawa += 1;
                    }
                }
                if cnt.miss_lo_b > before_lo_b {
                    rc.adv_lo_b_miss += 1;
                }
            }
            shots.push(sh);
        }
        round_trip(&sched, wq, with_term, &shots, &format!("adv-s{step}"), cnt);
        *circuits += 2;
    }
    let miss_after = miss_snapshot(cnt);
    let misses: Vec<String> = MISS_NAMES.iter().zip(miss_before.iter().zip(&miss_after)).map(|(n, (b, a))| format!("{n} {}", a - b)).collect();
    eprintln!(
        "PACKED_DIVISION review A: {} adversarial inputs, {} division rows, {} value-checked, d_max {}, s_max {}, empty-field rows {} (MSB in A's wrapped low bits {}), lo_b-miss rows {}, e_A = W_A with off = 1 {}, tight e_A = W_A {}, inputs terminating in [365, 400] {}; miss kinds on these inputs: {}",
        inputs.len(), rc.adv_div_rows, rc.adv_checked, rc.adv_d_max, rc.adv_s_max, rc.adv_field_empty,
        rc.adv_field_empty_wrapped, rc.adv_lo_b_miss, rc.adv_eawa_off1, rc.adv_tight_eawa, rc.adv_terminal_365_400, misses.join(", ")
    );
    eprintln!("PACKED_DIVISION review A lo_b rows (e_B <= lo_b) by refined class (value-checked / inverse-only): {lob:?}");
    // The soft class occurs on the static tables (lo_b > 0 up to step ~390 with
    // ca narrow enough); the thin schedule's lo_b reaches 0 earlier, so there it
    // may be empty - the value claim on soft rows is asserted where they exist.
    let thin = std::env::var("MIDQ_DIVISION_SELFTEST_THIN").ok().as_deref() == Some("1");
    // every Soft row is value-checked (by construction of shot_refined)
    assert!(lob.get(&LoB::Soft).map_or(true, |e| e.1 == 0), "a soft lo_b row was not value-checked");
    if !thin {
        // under the thin schedule the s = 24/25 rows are q-width misses (inverse-checked only)
        assert!(rc.adv_d_max >= 24, "adversarial inputs: expected a drop >= 24");
        assert!(rc.adv_s_max >= 24, "adversarial inputs: expected a shift >= 24");
    }
    assert!(rc.adv_field_empty_wrapped > 0, "adversarial inputs: no d > E row");
    assert!(rc.adv_eawa_off1 > 0 && rc.adv_tight_eawa > 0);
    assert!(rc.adv_terminal_365_400 >= 12);

    // ---------------------------------------------------------------- Part B
    let mut rng = Rng::new("synthetic");
    let steps = [100usize, 250, 300, 365, 378, 400, 480, 529];
    let mut classes: BTreeMap<String, (usize, usize)> = BTreeMap::new(); // class -> (checked, miss)
    let mut lob_b: BTreeMap<LoB, (usize, usize)> = BTreeMap::new();
    for &step in &steps {
        let sched = StepWidths::from_schedule(step);
        let wq = sched.w_q.clamp(1, 1 << SROT);
        let with_term = step >= term_from;
        let w_a = sched.w_a;
        let w_c = sched.w_c;
        let lo_b = sched.lo_b;
        let cascade_lo = sched.div_cascade_lo();
        let rb = sched.rb_div.min(SROT);
        let n_w = sched.div_scan_window();
        let n0 = sched.div_term_window();
        let max_sraw = (1usize << rb) - 1;
        let mut rows: Vec<(String, Row)> = Vec::new();
        let mut push = |name: &str, row: Row| rows.push((name.to_string(), row));

        // cb width for a tight R1 at e_A; ca width for a tight R2 at e_B (spare bit when off).
        let tight_cb = |e_a: usize| RING - e_a;
        let tight_ca = |e_b: usize, off: bool| RING - e_b - usize::from(off);

        // e_A = W_A, off = 0, tight both sides, d in {1, 2, 24}; and e_B = W_A (s_raw = 0)
        for &(s_raw, d) in &[(1usize, 1usize), (5, 2), (5, 24), (0, 1), (0, 3)] {
            let s_raw = s_raw.min(max_sraw);
            let e_b = w_a - s_raw;
            if e_b < lo_b + 1 || e_b < 3 || e_b <= d + 1 || d >= n_w {
                continue;
            }
            let (a, b) = row_off0(&mut rng, e_b, s_raw, d, s_raw);
            let (ca, cb) = coefs(&mut rng, tight_cb(w_a).min(w_c), tight_ca(e_b, false).min(tight_cb(w_a).min(w_c)));
            let q = q_above(&mut rng, s_raw, wq);
            push(if s_raw == 0 { "eB=WA_sraw0_tight" } else { "eA=WA_off0_tight" }, synth(a, b, ca, cb, q));
        }
        // e_A = W_A, off = 1, tight R1 (and tight R2 with the spare bit when s_raw = 1)
        for &(s_raw, d) in &[(1usize, 1usize), (2, 1), (6, 3), (max_sraw, 2)] {
            if s_raw < 1 || s_raw > max_sraw {
                continue;
            }
            let e_b = w_a - s_raw;
            if e_b < lo_b + 1 || e_b < 3 || d > e_b || d > n_w {
                continue;
            }
            let (a, b) = row_off1_notie(&mut rng, e_b, s_raw, d, s_raw - 1, cascade_lo);
            let bl_cb = tight_cb(w_a).min(w_c);
            let bl_ca = tight_ca(e_b, true).min(bl_cb);
            let (ca, cb) = coefs(&mut rng, bl_cb, bl_ca);
            let q = q_above(&mut rng, s_raw - 1, wq);
            push("eA=WA_off1_tight", synth(a, b, ca, cb, q));
        }
        // maximal supported drop and one beyond (off = 0: d = n_w - 1 / n_w; off = 1: n_w / n_w + 1)
        for &(off, extra) in &[(false, 0usize), (false, 1), (true, 0), (true, 1)] {
            let d = n_w - 1 + usize::from(off) + extra;
            let s_raw = 3.min(max_sraw).max(usize::from(off));
            let e_b = (w_a - s_raw).min(lo_b + 1 + 40).max(d + 2);
            if e_b + s_raw > w_a || e_b < lo_b + 1 || s_raw < usize::from(off) {
                continue;
            }
            let (a, b) = if off {
                row_off1_notie(&mut rng, e_b, s_raw, d, s_raw - 1, cascade_lo)
            } else {
                row_off0(&mut rng, e_b, s_raw, d, s_raw)
            };
            let bl_cb = tight_cb(bl(&a)).min(w_c).max(1);
            let (ca, cb) = coefs(&mut rng, bl_cb, tight_ca(e_b, off).min(bl_cb));
            let q = q_above(&mut rng, s_raw - usize::from(off), wq);
            push(if extra == 0 { "drop_max" } else { "drop_miss" }, synth(a, b, ca, cb, q));
        }
        // empty field: d = E (R = 0, bl(A_new) = s) and d > E (A_new's MSB below A's bit s - 1)
        for &(off, below) in &[(false, 0usize), (false, 3), (true, 0), (true, 2)] {
            let s_raw = 12.min(max_sraw);
            let s = s_raw - usize::from(off);
            if s < below + 1 || s_raw < 1 || (off && lo_b != 0) {
                // off = 1 with bl(R) = 1: R's only bit is bit 0, so D9's window [lo_b, e_B)
                // ties whenever lo_b > 0 (~B is tiny too) - the residue miss; build it only
                // where the window reaches bit 0.
                continue;
            }
            let e_b = (lo_b + 1).max(4);
            let e_e = e_b + usize::from(off);
            if e_b + s_raw > w_a || e_e + below >= n_w {
                continue; // d = E + below must stay on the support
            }
            let bl_low = s - below;
            let (a, b) = if off {
                // R = 0 is impossible for off = 1 (R >= 2^e_B - B >= 1): use d = E - 1 with
                // bl(R) = 1, then the field holds a single bit; still the wrapped-bits path
                // is the off = 0 one. Keep the off = 1 row as the d = E - 1 boundary.
                row_off1_notie(&mut rng, e_b, s_raw, e_e - 1, bl_low.min(s), cascade_lo)
            } else {
                row_off0(&mut rng, e_b, s_raw, e_b, bl_low)
            };
            let bl_cb = tight_cb(bl(&a)).min(w_c).max(1);
            let (ca, cb) = coefs(&mut rng, bl_cb, tight_ca(e_b, off).min(bl_cb));
            let q = q_above(&mut rng, s, wq);
            push(if off { "field_one_bit_off1" } else if below == 0 { "field_empty_dE" } else { "field_empty_dgtE" }, synth(a, b, ca, cb, q));
        }
        // e_B = lo_b + 1 (D11 ring bottom L > 0 when lo_b > 32): off = 0 exact; off = 1 with
        // the D4 window [cascade_lo, e_B) tying deliberately (A >> s_raw = B - 1 with B odd:
        // the operands differ only at bit 0 < cascade_lo) = the residue miss, buildable only
        // where the cascade bottom is above wire 0 (lo_b > 32)
        if lo_b + 1 >= 3 {
            let e_b = lo_b + 1;
            for &(off, s_raw, d) in &[(false, 1usize, 1usize), (false, 7, 5), (true, 4, 1)] {
                let s_raw = s_raw.min(max_sraw);
                if e_b + s_raw > w_a || s_raw < usize::from(off) || d > e_b || d >= n_w || (off && cascade_lo == 0) {
                    continue;
                }
                let (a, b) = if off { row_off1_tie(&mut rng, e_b, s_raw, cascade_lo) } else { row_off0(&mut rng, e_b, s_raw, d, s_raw) };
                let bl_cb = tight_cb(bl(&a)).min(w_c).max(1);
                let (ca, cb) = coefs(&mut rng, bl_cb, tight_ca(e_b, off).min(bl_cb));
                let q = q_above(&mut rng, s_raw - usize::from(off), wq);
                push(if off { "eB=lob+1_off1_tie" } else { "eB=lob+1_off0" }, synth(a, b, ca, cb, q));
            }
            // e_B = lo_b + 2 with off = 1 and the second bits distinct: exact
            let e_b = lo_b + 2;
            let s_raw = 4.min(max_sraw);
            if e_b + s_raw <= w_a && e_b >= 3 && s_raw >= 1 {
                let (a, b) = row_off1_notie(&mut rng, e_b, s_raw, 1, s_raw - 1, cascade_lo);
                let bl_cb = tight_cb(bl(&a)).min(w_c).max(1);
                let (ca, cb) = coefs(&mut rng, bl_cb, tight_ca(e_b, true).min(bl_cb));
                let q = q_above(&mut rng, s_raw - 1, wq);
                push("eB=lob+2_off1", synth(a, b, ca, cb, q));
            }
        }
        // maximal rotation s_raw = 2^rb - 1 with off in {0, 1}
        for &off in &[false, true] {
            let s_raw = max_sraw;
            let e_b = (w_a - s_raw).min(lo_b + 20).max(lo_b + 1);
            if e_b + s_raw > w_a || e_b < 3 {
                continue;
            }
            let (a, b) = if off { row_off1_notie(&mut rng, e_b, s_raw, 1, s_raw - 1, cascade_lo) } else { row_off0(&mut rng, e_b, s_raw, 2, s_raw) };
            let bl_cb = tight_cb(bl(&a)).min(w_c).max(1);
            let (ca, cb) = coefs(&mut rng, bl_cb, tight_ca(e_b, off).min(bl_cb));
            let q = q_above(&mut rng, s_raw - usize::from(off), wq);
            push("sraw_max", synth(a, b, ca, cb, q));
        }
        // B = 1 rows (terminal-aware steps): terminal with s = 0, n0 - 1, n0 (last D0 leaf), n0 + 1.. (term_window miss);
        // inexact with d = 31 at s = 31; s_raw >= 2^rb (shift miss)
        if with_term {
            let bl_cb_max = |e_a: usize| tight_cb(e_a).min(w_c).max(1);
            for &s in &[0usize, n0.saturating_sub(1), n0, n0 + 1, n0 + 3] {
                if s + 1 > w_a || s >= wq || s > max_sraw {
                    continue;
                }
                let a = one() << s;
                let bl_cb = bl_cb_max(s + 1);
                let (ca, cb) = coefs(&mut rng, bl_cb, tight_ca(1, false).min(bl_cb));
                let q = q_above(&mut rng, s, wq);
                push(if s <= n0 { "terminal" } else { "terminal_window_miss" }, synth(a, one(), ca, cb, q));
            }
            for &(s, dd) in &[(31usize, 31usize), (31, 30), (20, 20), (n0.min(max_sraw), 1)] {
                if s > max_sraw || s + 1 > w_a || s >= wq || dd > s {
                    continue;
                }
                // A = 2^s + 2^(s - dd) (+ lower noise below that): bl(A_new) = s - dd + 1, d = dd
                let a = (one() << s) | (one() << (s - dd)) | rng.below(s - dd);
                let bl_cb = bl_cb_max(s + 1);
                let (ca, cb) = coefs(&mut rng, bl_cb, tight_ca(1, false).min(bl_cb));
                let q = q_above(&mut rng, s, wq);
                push("b1_inexact", synth(a, one(), ca, cb, q));
            }
            if (1usize << rb) + 1 <= w_a && (1usize << rb) < wq {
                let s = 1usize << rb; // s_raw = 2^rb: shift miss
                let a = (one() << s) | one();
                let bl_cb = bl_cb_max(s + 1);
                let (ca, cb) = coefs(&mut rng, bl_cb, tight_ca(1, false).min(bl_cb));
                push("b1_shift_miss", synth(a, one(), ca, cb, U512::ZERO));
            }
        }
        // a shift outside the q envelope is the q-width miss, not a class under test
        rows.retain(|(_, r)| r.s < wq);
        // shots (chunks of 64), extra classification, round trips
        for chunk in rows.chunks(64) {
            let mut shots: Vec<Shot> = Vec::new();
            for (name, row) in chunk {
                let (sh, checked) = shot_refined(row, &sched, wq, with_term, true, cnt, &mut lob_b);
                let lob_class = lo_b_class(row, &sched);
                let e = classes.entry(name.clone()).or_insert((0, 0));
                if checked { e.0 += 1 } else { e.1 += 1 }
                rc.synth_rows += 1;
                if checked { rc.synth_checked += 1 } else { rc.synth_miss += 1 }
                // the expectations of the miss classes
                match name.as_str() {
                    "drop_max" | "eA=WA_off0_tight" | "eA=WA_off1_tight" | "eB=WA_sraw0_tight" | "field_empty_dE"
                    | "field_empty_dgtE" | "field_one_bit_off1" | "eB=lob+1_off0" | "eB=lob+2_off1" | "sraw_max"
                    | "terminal" | "b1_inexact" => {
                        // B = 1 rows at steps where lo_b > 0 are lo_b rows: exact (Soft) unless a
                        // ca bit sits in a plain D7 cell (tight R2 at e_B = 1: a HARD miss).
                        assert!(
                            checked || matches!(lob_class, LoB::HardCaInPlainCell),
                            "step {step}: synthetic row {name} classified off the support ({lob_class:?}): {cnt:?}"
                        )
                    }
                    "drop_miss" | "eB=lob+1_off1_tie" | "terminal_window_miss" | "b1_shift_miss" => {
                        assert!(!checked, "step {step}: synthetic row {name} should be a classified miss")
                    }
                    other => panic!("unknown class {other}"),
                }
                shots.push(sh);
            }
            round_trip(&sched, wq, with_term, &shots, &format!("synth-s{step}"), cnt);
            *circuits += 2;
        }
    }
    let mut summary = String::new();
    for (k, (c, m)) in &classes {
        summary.push_str(&format!(" {k} {c}/{m}"));
    }
    eprintln!(
        "PACKED_DIVISION review B: {} synthetic rows at {:?} ({} value-checked, {} classified misses inverse-only); class checked/miss:{}; lo_b rows by refined class: {lob_b:?}",
        rc.synth_rows, steps, rc.synth_checked, rc.synth_miss, summary
    );
    for need in ["terminal", "b1_inexact"] {
        assert!(classes.get(need).map_or(0, |e| e.0) > 0, "class {need} never value-checked");
    }
    if !thin {
        // class coverage is asserted on the static tables (the thin schedule's narrower
        // q / W_A envelopes leave some boundary rows unbuildable there)
        for need in [
            "eA=WA_off0_tight", "eA=WA_off1_tight", "eB=WA_sraw0_tight", "drop_max", "drop_miss", "field_empty_dE", "field_empty_dgtE",
            "field_one_bit_off1", "eB=lob+1_off0", "eB=lob+1_off1_tie", "eB=lob+2_off1", "sraw_max", "terminal", "terminal_window_miss",
            "b1_inexact", "b1_shift_miss",
        ] {
            assert!(classes.contains_key(need), "synthetic class {need} never built");
        }
    }
}
