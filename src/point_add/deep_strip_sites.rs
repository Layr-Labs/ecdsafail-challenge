//! Source-identity ("stable site") certificates for the deep-strip census (task-7 of
//! `.superpowers/sdd/2026-08-01-valid-sub-1482m-circuit`).
//!
//! `deep_strip_keys.rs`'s existing `DEAD_KEYS`/`DOWNGRADE_KEYS` name a gate by
//! `(kind, operands, k-th-occurrence ordinal, census-time tuple occupancy)` -- a purely
//! *positional* identity. Any upstream edit that adds or removes a gate sharing that
//! operand tuple slides every later ordinal, and `apply_deep_strip_identity`'s occupancy
//! tripwire correctly discards the key rather than risk deleting a live gate (see that
//! function's doc comment). That is safe, but it means a geometry change as large as
//! Tasks 5-6's (`ITERS` 261->258, plus a baked schedule-margin/apply-fold precision
//! profile) throws away most of the table.
//!
//! `StableSiteKey` is a different, source-identity-keyed addressing scheme: literally
//! which line of Rust source emitted the gate (`OpSite` = `(file, line, context)`, already
//! captured by `crate::point_add`'s `TRACE_OP_SITES` machinery), plus a within-that-exact
//! -site occurrence count. Unlike a positional ordinal, this survives a schedule/precision
//! edit as long as the SOURCE CALL SITE still emits that gate at all -- which is a much
//! weaker (and much more often true) condition than "the whole stream's operand-tuple
//! layout is unchanged".
//!
//! This module never decides that a gate is dead or downgradable on its own. It only
//! answers "which gate, by source identity, does this key/candidate refer to" in either
//! direction:
//!   - `export_baseline_sites`   (task-7 brief Step 2): existing positional key -> stable
//!                                 site, on the OLD geometry those keys were mined against.
//!   - `translate_stable_sites`  (Step 4): stable site -> new positional key, on the NEW
//!                                 (candidate) geometry.
//!   - `compute_stable_site_keys`/`load_baseline_key_set` are the shared primitives
//!     `census.rs`'s Step 5 inner-join (reject shallow discoveries) is built on.
//!
//! A wrong translation here would silently delete or downgrade a live gate, so every
//! function below refuses to guess: a stable identity that cannot be mapped to EXACTLY one
//! gate is either a hard `panic!` (Step 2, which must map perfectly because it runs on the
//! exact geometry the keys were mined on) or a counted, logged, and dropped miss (Step 4,
//! where "the source site no longer exists / fires fewer times under the new geometry" is
//! an expected, legitimate outcome -- never silently slid to a neighboring occurrence).

use crate::circuit::{Op, OperationType};
use crate::point_add::OpSite;
use std::collections::{HashMap, HashSet};

/// Step 1 of the task-7 brief, verbatim.
pub(crate) type StableSiteKey = (
    &'static str, // source file
    u32,          // source line
    u32,          // trace context
    u8,           // CCX or CCZ
    u32,          // occurrence within this exact source site/context/kind
);

/// Owned-string counterpart of `StableSiteKey`, used wherever the key has to survive a
/// round trip through a file (a `&'static str` cannot be produced from parsed text).
type StringSiteKey = (String, u32, u32, u8, u32);

fn to_string_key((file, line, context, kind, ord): StableSiteKey) -> StringSiteKey {
    (file.to_string(), line, context, kind, ord)
}

/// Operand tuple identifying a gate the same way `census.rs`/`apply_deep_strip_identity`
/// do: (kind, q_control2, q_control1, q_target, c_condition).
type Tup = (u8, u64, u64, u64, u64);

const KIND_CCX: u8 = OperationType::CCX as u8;
const KIND_CCZ: u8 = OperationType::CCZ as u8;

fn tup_of(op: &Op) -> Tup {
    (op.kind as u8, op.q_control2.0, op.q_control1.0, op.q_target.0, op.c_condition.0)
}

fn is_toffoli_family(kind: u8) -> bool {
    kind == KIND_CCX || kind == KIND_CCZ
}

/// For every op in `ops` (aligned 1:1 with `sites`, i.e. `sites.len() == ops.len()` -- see
/// task-7 brief Step 3), compute its `StableSiteKey` if it is a CCX/CCZ gate (`None`
/// otherwise). The occurrence counter increments per `(file, line, context, kind)` in
/// stream order -- the same idea as the positional ordinal `census.rs`/
/// `apply_deep_strip_identity` assign per OPERAND TUPLE, just keyed by SOURCE IDENTITY
/// instead of operand values.
pub(crate) fn compute_stable_site_keys(
    ops: &[Op],
    sites: &[OpSite],
) -> Vec<Option<StableSiteKey>> {
    assert_eq!(
        ops.len(),
        sites.len(),
        "stable-site computation requires 1:1 op/site alignment (see task-7 Step 3)"
    );
    let mut occ: HashMap<(&'static str, u32, u32, u8), u32> = HashMap::new();
    ops.iter()
        .zip(sites.iter())
        .map(|(op, &(file, line, context))| {
            let kb = op.kind as u8;
            if !is_toffoli_family(kb) {
                return None;
            }
            let counter = occ.entry((file, line, context, kb)).or_insert(0);
            let this = *counter;
            *counter += 1;
            Some((file, line, context, kb, this))
        })
        .collect()
}

/// Build the positional-identity index `apply_deep_strip_identity`/`census.rs::report` use:
/// tuple occupancy in this stream, and `(tuple, ordinal) -> op index`.
fn positional_index(ops: &[Op]) -> (HashMap<Tup, u32>, HashMap<(Tup, u32), usize>) {
    let mut occ: HashMap<Tup, u32> = HashMap::new();
    for op in ops {
        let kb = op.kind as u8;
        if is_toffoli_family(kb) {
            *occ.entry(tup_of(op)).or_insert(0) += 1;
        }
    }
    let mut ord: HashMap<Tup, u32> = HashMap::new();
    let mut pos_index: HashMap<(Tup, u32), usize> = HashMap::new();
    for (i, op) in ops.iter().enumerate() {
        let kb = op.kind as u8;
        if !is_toffoli_family(kb) {
            continue;
        }
        let tup = tup_of(op);
        let o = ord.entry(tup).or_insert(0);
        let this_ord = *o;
        *o += 1;
        pos_index.insert((tup, this_ord), i);
    }
    (occ, pos_index)
}

/// One row of the Step 2 CSV, parsed back in.
pub(crate) struct BaselineRow {
    pub action: String, // "dead" | "downgrade"
    pub act: u8,        // 0 for dead, 1|2 for downgrade (act's meaning: see census.rs)
    pub key: StringSiteKey,
}

const BASELINE_CSV_HEADER: &str =
    "action,act,file,line,context,kind,site_ordinal,old_tuple_ordinal,old_occupancy";

/// Step 2: locate every existing `deep_strip_keys::DEAD_KEYS`/`DOWNGRADE_KEYS` key in
/// `ops` (the final pre-strip stream, on the EXACT geometry those keys were mined
/// against -- ITERS=261, no baked precision profile) and emit its stable-site ancestry as
/// a CSV (`action,act,file,line,context,kind,site_ordinal,old_tuple_ordinal,old_occupancy`).
///
/// Aborts (panics) if any production key cannot be mapped to exactly one gate. Step 2 runs
/// on the exact geometry the keys were mined on, so every key must resolve cleanly: a miss
/// here means the geometry reproduction is wrong (see `task-7-report.md`'s hash
/// checkpoints), not that the key is legitimately stale -- staleness is
/// `apply_deep_strip_identity`'s own, later, separate concern (Step 4).
pub(crate) fn export_baseline_sites(ops: &[Op], sites: &[OpSite], path: &str) {
    let stable = compute_stable_site_keys(ops, sites);
    let (occ, pos_index) = positional_index(ops);

    let mut rows: Vec<String> = Vec::with_capacity(
        crate::point_add::deep_strip_keys::DEAD_KEYS.len()
            + crate::point_add::deep_strip_keys::DOWNGRADE_KEYS.len()
            + 1,
    );
    rows.push(BASELINE_CSV_HEADER.to_string());

    let mut unmapped = 0usize;
    let mut mapped = 0usize;
    let mut emit = |action: &str, act: u8, k: u8, c2: u64, c1: u64, t: u64, cc: u64, o: u32, tot: u32| {
        let tup = (k, c2, c1, t, cc);
        if occ.get(&tup).copied() != Some(tot) {
            unmapped += 1;
            eprintln!(
                "[export-strip-sites] UNMAPPED (occupancy mismatch) action={action} act={act} \
                 kind={k} tuple=(c2={c2},c1={c1},t={t},cond={cc}) ord={o} tot={tot} \
                 occ_now={:?}",
                occ.get(&tup)
            );
            return;
        }
        let Some(&idx) = pos_index.get(&(tup, o)) else {
            unmapped += 1;
            eprintln!(
                "[export-strip-sites] UNMAPPED (no op at that ordinal) action={action} act={act} \
                 kind={k} tuple=(c2={c2},c1={c1},t={t},cond={cc}) ord={o} tot={tot}"
            );
            return;
        };
        let Some((file, line, context, kb, site_ord)) = stable[idx] else {
            unmapped += 1;
            eprintln!(
                "[export-strip-sites] UNMAPPED (op at index {idx} is not CCX/CCZ per its own \
                 site trace -- should be unreachable)"
            );
            return;
        };
        rows.push(format!("{action},{act},{file},{line},{context},{kb},{site_ord},{o},{tot}"));
        mapped += 1;
    };

    for &(k, c2, c1, t, cc, o, tot) in crate::point_add::deep_strip_keys::DEAD_KEYS {
        emit("dead", 0, k, c2, c1, t, cc, o, tot);
    }
    for &(k, c2, c1, t, cc, o, tot, act) in crate::point_add::deep_strip_keys::DOWNGRADE_KEYS {
        emit("downgrade", act, k, c2, c1, t, cc, o, tot);
    }

    assert_eq!(
        unmapped, 0,
        "{unmapped} of {} production deep-strip keys could not be mapped to exactly one gate \
         against this stream -- Step 2 must run on the EXACT geometry the keys were mined \
         against; aborting rather than emit a wrong/partial ancestry export (see \
         task-7-report.md's geometry-sequencing section)",
        crate::point_add::deep_strip_keys::DEAD_KEYS.len()
            + crate::point_add::deep_strip_keys::DOWNGRADE_KEYS.len()
    );

    match std::fs::write(path, rows.join("\n") + "\n") {
        Ok(()) => eprintln!(
            "TLM_EXPORT_STRIP_SITES: wrote {path} ({mapped} keys mapped, 0 unmapped)"
        ),
        Err(e) => eprintln!("TLM_EXPORT_STRIP_SITES: failed to write {path}: {e}"),
    }
}

/// Parse Step 2's CSV back into rows. Panics on a malformed row (a hand-edited or
/// truncated file) rather than silently skip it -- a dropped baseline row can only ever
/// make Step 4/5 MORE conservative (fewer candidates survive), never less safe, but
/// silently ignoring a parse error would hide a real tooling bug.
pub(crate) fn load_baseline_rows(path: &str) -> Vec<BaselineRow> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read baseline stable-site CSV {path}: {e}"));
    let mut out = Vec::new();
    for (lineno, line) in text.lines().enumerate() {
        if lineno == 0 {
            assert_eq!(
                line, BASELINE_CSV_HEADER,
                "baseline stable-site CSV {path} has an unexpected header: {line:?}"
            );
            continue;
        }
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let f: Vec<&str> = line.split(',').collect();
        assert_eq!(f.len(), 9, "malformed baseline stable-site CSV row in {path}: {line:?}");
        let act: u8 = f[1]
            .parse()
            .unwrap_or_else(|e| panic!("bad act in {path} row {line:?}: {e}"));
        let src_line: u32 = f[3]
            .parse()
            .unwrap_or_else(|e| panic!("bad line in {path} row {line:?}: {e}"));
        let context: u32 = f[4]
            .parse()
            .unwrap_or_else(|e| panic!("bad context in {path} row {line:?}: {e}"));
        let kind: u8 = f[5]
            .parse()
            .unwrap_or_else(|e| panic!("bad kind in {path} row {line:?}: {e}"));
        let site_ordinal: u32 = f[6]
            .parse()
            .unwrap_or_else(|e| panic!("bad site_ordinal in {path} row {line:?}: {e}"));
        out.push(BaselineRow {
            action: f[0].to_string(),
            act,
            key: (f[2].to_string(), src_line, context, kind, site_ordinal),
        });
    }
    out
}

/// The baseline stable-site identity set alone (action-agnostic), for `census.rs`'s Step 5
/// inner join: "a gate absent from the baseline certificate list cannot enter
/// `deep_strip_keys.rs`, even if it never fires in the current sample" -- membership is
/// all that matters there, not which specific action the baseline certified.
pub(crate) fn load_baseline_key_set(path: &str) -> HashSet<StringSiteKey> {
    load_baseline_rows(path).into_iter().map(|r| r.key).collect()
}

pub(crate) struct TranslateStats {
    pub baseline_rows: usize,
    pub matched: usize,
    pub missing: usize,
    pub dead: usize,
    pub down: usize,
}

/// Step 4: translate baseline stable-site certificates (Step 2's CSV) onto the CURRENT
/// build's final pre-strip stream -- the "final candidate geometry" (ITERS=258, baked
/// precision profile, strip disabled). For every baseline row whose stable identity
/// exists EXACTLY ONCE in this stream, emit an ordinary positional candidate key in
/// `apply_deep_strip_identity`'s own `(kind, operands, ordinal, occupancy[, act])` format,
/// written to `out_path` in `deep_strip_keys.rs`'s own literal table syntax so downstream
/// tooling (including a human diff) can read it the same way.
///
/// A baseline identity that does not occur in this stream AT ALL (the source call site
/// fires fewer times under the new geometry -- a real, expected, and common consequence of
/// `ITERS` 261->258 and the widened fold/margin schedule) is counted as "missing" and
/// dropped, NOT slid to a neighboring occurrence -- sliding would silently address a
/// different gate. A stable identity that maps to MORE than one op is impossible by
/// `compute_stable_site_keys`'s construction (each occurrence gets a distinct counter
/// value) unless the occurrence-counting logic itself is broken, so that case is a hard
/// `panic!` ("abort on duplicate", per the brief), not a soft skip.
pub(crate) fn translate_stable_sites(
    ops: &[Op],
    sites: &[OpSite],
    baseline_csv_path: &str,
    out_path: &str,
) -> TranslateStats {
    let rows = load_baseline_rows(baseline_csv_path);
    let stable = compute_stable_site_keys(ops, sites);
    let (occ, _pos_index) = positional_index(ops);

    let mut ord: HashMap<Tup, u32> = HashMap::new();
    let mut site_to_pos: HashMap<StringSiteKey, (Tup, u32, u32)> = HashMap::new();
    for (i, op) in ops.iter().enumerate() {
        let kb = op.kind as u8;
        if !is_toffoli_family(kb) {
            continue;
        }
        let tup = tup_of(op);
        let o = ord.entry(tup).or_insert(0);
        let this_ord = *o;
        *o += 1;
        let tot = occ[&tup];
        if let Some(key) = stable[i] {
            let skey = to_string_key(key);
            let prior = site_to_pos.insert(skey.clone(), (tup, this_ord, tot));
            assert!(
                prior.is_none(),
                "duplicate StableSiteKey {skey:?} within this stream (two ops resolved to the \
                 identical (file,line,context,kind,occurrence) identity) -- this is an \
                 occurrence-counting bug in compute_stable_site_keys, not a legitimate geometry \
                 fact; aborting rather than translate ambiguously"
            );
        }
    }

    let mut dead: Vec<(u8, u64, u64, u64, u64, u32, u32)> = Vec::new();
    let mut down: Vec<(u8, u64, u64, u64, u64, u32, u32, u8)> = Vec::new();
    let mut missing = 0usize;
    for row in &rows {
        match site_to_pos.get(&row.key) {
            None => missing += 1,
            Some(&((k, c2, c1, t, cc), o, tot)) => {
                if row.action == "dead" {
                    dead.push((k, c2, c1, t, cc, o, tot));
                } else {
                    down.push((k, c2, c1, t, cc, o, tot, row.act));
                }
            }
        }
    }
    let matched = dead.len() + down.len();

    eprintln!(
        "TLM_TRANSLATE_STRIP_SITES: baseline_rows={} matched={} missing={} (dead={} down={})",
        rows.len(),
        matched,
        missing,
        dead.len(),
        down.len()
    );

    let mut s = String::new();
    s.push_str("// Auto-generated by TLM_TRANSLATE_STRIP_SITES (task-7 Step 4): baseline\n");
    s.push_str("// StableSiteKey certificates translated onto the current op stream's\n");
    s.push_str("// positional (kind, operands, ordinal, occupancy) identity. NOT yet\n");
    s.push_str("// census-confirmed on this geometry -- see Step 5/6 before trusting these.\n");
    s.push_str("pub static DEAD_KEYS: &[(u8, u64, u64, u64, u64, u32, u32)] = &[\n");
    for &(k, c2, c1, t, cc, o, tot) in &dead {
        s.push_str(&format!("    ({k}, {c2}, {c1}, {t}, {cc}, {o}, {tot}),\n"));
    }
    s.push_str("];\n\n");
    s.push_str("pub static DOWNGRADE_KEYS: &[(u8, u64, u64, u64, u64, u32, u32, u8)] = &[\n");
    for &(k, c2, c1, t, cc, o, tot, act) in &down {
        s.push_str(&format!("    ({k}, {c2}, {c1}, {t}, {cc}, {o}, {tot}, {act}),\n"));
    }
    s.push_str("];\n");
    match std::fs::write(out_path, s) {
        Ok(()) => eprintln!("TLM_TRANSLATE_STRIP_SITES: wrote {out_path}"),
        Err(e) => eprintln!("TLM_TRANSLATE_STRIP_SITES: failed to write {out_path}: {e}"),
    }

    TranslateStats { baseline_rows: rows.len(), matched, missing, dead: dead.len(), down: down.len() }
}

/// A distinguishing bit no genuine trace context ever sets (the real per-iteration
/// contexts this crate emits top out at a top-byte tag like `0xa0`-`0xa5` plus a $\le
/// 16$-bit iteration index -- see `task-6-report.md`'s context byte table), OR'd into a
/// synthesized gate's inherited context so a synthesized gate's `StableSiteKey` can never
/// collide with a genuine occurrence of the gate it was derived from.
pub(crate) const SYNTH_SITE_TAG: u32 = 0x8000_0000;

/// Filter a `sites` vector by a "kept" mask aligned 1:1 with the `ops` it was computed
/// from (`true` = keep). Valid for any pass that only removes ops -- never reorders or
/// inserts (`single_ccx_fanout` needs the dedicated transform below instead).
pub(crate) fn filter_sites_by_kept(sites: &[OpSite], kept: &[bool]) -> Vec<OpSite> {
    assert_eq!(sites.len(), kept.len(), "kept-mask length must match the sites it filters");
    sites.iter().zip(kept.iter()).filter_map(|(&s, &k)| k.then_some(s)).collect()
}

/// `single_ccx_fanout::rewrite_first_target_fanout`'s rewrite, in `OpSite` terms: drop the
/// two consumed CCX gates' sites (`first_index`, `second_index`), and give the newly
/// synthesized replacement CCX -- inserted immediately after the kept `blocker_index`,
/// exactly where the real rewrite inserts the synthesized op -- the EARLIER consumed
/// gate's site (`first_index`) with `SYNTH_SITE_TAG` set in its context, so it is
/// distinguishable from a real occurrence of that site while still carrying real
/// (file, line) provenance. Mirrors `rewrite_first_target_fanout`'s own
/// `for (op_index, stream_op) in ops.into_iter().enumerate() { skip first/second; push;
/// if op_index == blocker_index { push replacement } }` loop structure line for line, so
/// the two vectors cannot drift apart.
pub(crate) fn fanout_site_transform(
    sites: &[OpSite],
    first_index: usize,
    second_index: usize,
    blocker_index: usize,
) -> Vec<OpSite> {
    let (file, line, context) = sites[first_index];
    let synthesized: OpSite = (file, line, context | SYNTH_SITE_TAG);
    let mut out = Vec::with_capacity(sites.len().saturating_sub(1));
    for (i, &s) in sites.iter().enumerate() {
        if i == first_index || i == second_index {
            continue;
        }
        out.push(s);
        if i == blocker_index {
            out.push(synthesized);
        }
    }
    out
}
