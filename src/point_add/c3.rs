//! (internal) (internal) (internal) ((internal)): modes and rewrite steps for ITEM 12 (counter-top-bit loop enable, roles c / d of wire 251).
use super::*;
use super::w2::*;
use std::io::Write as _;




// ================================================================================================ step `fold`
thread_local! {
    /// pivot choice per folded pair (in stream order); None = take it from C3_FOLDSEL / the snapshots / the first wire
    pub static FOLD_PIVOTS: std::cell::RefCell<Option<Vec<u16>>> = std::cell::RefCell::new(None);
}
/// A dirty-accumulator update of several wires by the same value: CX(h -> w1) .. CX(h -> wk), [records that name no w_i],
/// CX(h -> w1) .. CX(h -> wk).  Between the two groups every w_i carries the garbage h_old.  Rewritten (an identity of circuits
/// for every state and every choice of the pivot p among the w_i): CX(p -> wj) (j != p), CX(h -> p), [same records], CX(h -> p),
/// CX(p -> wj): only p carries the garbage, w_j holds w_j xor p in between.  +0 records.
/// The pivot is a DATA-SELECTED choice (a wire that is zero on every sampled shot at the group, so that the other wires keep
/// their own values): taken from FOLD_PIVOTS / the file C3_FOLDSEL, or computed from the snapshots in W2_SNAPS (and written to
/// C3_FOLDSEL).  The selection only decides which lane is live; correctness does not depend on it.
pub fn fold(rows: Vec<Row>, info: &mut w2rw::Info, m: &[u16]) -> Vec<Row> {
    let n = rows.len(); let maxgap: usize = 40000;
    let iscx = |r: &Row| r[0] == 8 && r[3] == NONE;
    // pass 1: the pairs (start, group size, start of the second group)
    let mut pairs: Vec<(usize, usize, usize)> = Vec::new(); let mut i = 0usize;
    while i < n { let r = rows[i];
        if !(iscx(&r) && i + 1 < n && iscx(&rows[i + 1]) && rows[i + 1][1] == r[1] && rows[i + 1][2] != r[2]) { i += 1; continue; }
        let h = r[1]; let mut k = 1usize; let mut ws: Vec<u16> = vec![r[2]];
        while i + k < n && iscx(&rows[i + k]) && rows[i + k][1] == h && !ws.contains(&rows[i + k][2]) && rows[i + k][2] != h { ws.push(rows[i + k][2]); k += 1; }
        let mut j = i + k; let mut ok = false;
        while j < n && j - (i + k) <= maxgap { let q = rows[j]; let nq = qubits(q[0]);
            if !matches!(q[0], 6 | 8 | 13) || (q[0] == 6 && q[2] != NONE) || (q[0] == 8 && q[3] != NONE) { break; }
            if (1..=nq).any(|t| ws.contains(&q[t]) || q[t] == h && t == nq && false) { ok = j + k <= n && rows[j..j + k] == rows[i..i + k]; break; }
            j += 1; }
        if ok { pairs.push((i, k, j)); i = j + k; } else { i += 1; } }
    // pass 2: pivots
    let piv: Option<Vec<u16>> = FOLD_PIVOTS.with(|p| p.borrow().clone());   // packaged: the embedded selection only
    if let Some(p) = &piv { assert!(p.len() == pairs.len(), "fold: {} pivots for {} pairs (the selection belongs to other rows)", p.len(), pairs.len()); }
    // pass 3: emit
    let mut out: Vec<Row> = Vec::with_capacity(n); let mut pos = 0usize; let mut span = 0u64;
    for (gi, &(a, k, j)) in pairs.iter().enumerate() { out.extend_from_slice(&rows[pos..a]);
        let h = rows[a][1]; let ws: Vec<u16> = rows[a..a + k].iter().map(|r| r[2]).collect();
        let p = piv.as_ref().map_or(ws[0], |v| v[gi]); assert!(ws.contains(&p), "fold: pivot {} is not in group {}", p, gi);
        for &w in &ws { if w != p { out.push([8, p, w, NONE]); } } out.push([8, h, p, NONE]);
        out.extend_from_slice(&rows[a + k..j]);
        out.push([8, h, p, NONE]); for &w in &ws { if w != p { out.push([8, p, w, NONE]); } }
        span += (j + k - a) as u64; pos = j + k; }
    out.extend_from_slice(&rows[pos..]); assert!(out.len() == n);
    info.notes.push(format!("fold: {} dirty-accumulator pairs folded ({} rows inside, +0 records); pivots {}", pairs.len(), span, if piv.is_some() { "selected" } else { "first wire" }));
    out
}



// ================================================================================================ step `cap`
/// `cap:<wire>,<lo>,<hi>` (record numbers; values below 1,000,000 are thousands): delete every CX / CCX record that TARGETS <wire> in [lo, hi) of the rows this step receives.
/// A CAP, not an identity: the wire is the top bit of a leading-zero counter there; with its writes removed it keeps its entry
/// value, which is right exactly when the count stays below the bit's weight.  Refuses when an X, a measurement or a classical
/// record names the wire inside the range.
pub fn cap(rows: Vec<Row>, arg: &str, info: &mut w2rw::Info) -> Vec<Row> {
    let a: Vec<usize> = arg.split(',').map(|x| x.parse().unwrap()).collect(); let ex = |v: usize| if v >= 1_000_000 { v } else { v * 1000 }; let (w, lo, hi) = (a[0] as u16, ex(a[1]), ex(a[2]));
    let mut out: Vec<Row> = Vec::with_capacity(rows.len()); let (mut del, mut uses) = (0u64, 0u64);
    for (i, &r) in rows.iter().enumerate() { if i >= lo && i < hi { let nq = qubits(r[0]);
            if (1..=nq).any(|j| r[j] == w) { assert!(matches!(r[0], 8 | 13), "cap: record {} {:?} names the wire", i, r);
                if r[nq] == w { assert!(r[0] == 13 || r[3] == NONE); del += 1; continue; } uses += 1; } }
        out.push(r); }
    info.notes.push(format!("cap wire {} in [{}, {}): {} target records deleted, {} control uses left", w, lo, hi, del, uses));
    out
}

// ================================================================================================ step `apply`
pub fn parse_cover(txt: &str) -> Vec<(usize, usize, u16)> {
    txt.lines().filter(|l| !l.starts_with('#') && !l.trim().is_empty()).map(|l| { let v: Vec<i64> = l.split_whitespace().map(|x| x.parse().unwrap()).collect(); (v[0] as usize, v[1] as usize, v[2] as u16) }).collect()
}
thread_local! { pub static APPLY_COVER: std::cell::RefCell<Option<Vec<(usize, usize, u16)>>> = std::cell::RefCell::new(None); }
/// `apply:<R>`: the witness cover APPLIED (cover = APPLY_COVER or the file C3_APPLY, stretches of the rows this step receives).
/// The value of the foreign wire R (a passenger the item never names) is hosted on the stretch's witness wire: at the start
/// `CX R w ; CX w R`, at every changeover `CX a b ; CX b a`, at the end the reverse.  Inside a stretch a record that uses the
/// witness as a CONTROL is dropped (a no-op on a zero lane); a Z / CZ on it is dropped; anything else naming it is an error.
/// After this step wire R is named by 4 records only (2 at each end): one physical lane is free through the item.
/// EXACT ONLY IF every witness is zero at its stretch's start on the input at hand.
pub fn apply(rows: Vec<Row>, arg: &str, info: &mut w2rw::Info) -> Vec<Row> {
    let r: u16 = arg.parse().unwrap(); let cov = APPLY_COVER.with(|c| c.borrow().clone()).expect("apply: no embedded cover");
    assert!(cov[0].0 == 0 && cov[cov.len() - 1].1 == rows.len() && cov.windows(2).all(|w| w[0].1 == w[1].0), "apply: the cover does not tile these rows");
    let only: Option<Vec<u16>> = None;
    let mut out: Vec<Row> = Vec::with_capacity(rows.len() + 4 * cov.len()); let (mut dropped, mut moves) = (0u64, 0u64); let mut cur = r;
    for &(a, b, w0) in &cov { let w = if only.as_ref().map_or(true, |o| o.contains(&w0)) { w0 } else { r };   // a stretch whose witness is not allowed keeps the value on R
        if w != cur { out.push([8, cur, w, NONE]); out.push([8, w, cur, NONE]); moves += 1; cur = w; }
        for &q in &rows[a..b] { let nq = qubits(q[0]);
            if w != r && (1..=nq).any(|j| q[j] == w) { let is_t = matches!(q[0], 6 | 8 | 13) && q[nq] == w; assert!(!is_t && matches!(q[0], 7 | 8 | 9 | 13), "apply: record {:?} writes or measures witness {}", q, w); dropped += 1; continue; }
            assert!(!(1..=nq).any(|j| q[j] == r), "apply: the foreign wire is named by the item");
            out.push(q); } }
    if cur != r { out.push([8, cur, r, NONE]); out.push([8, r, cur, NONE]); moves += 1; }
    info.notes.push(format!("apply R = wire {}: {} stretches, {} changeovers (+{} records), {} control / Z uses of a witness dropped; wire {} is named by the first 2 and last 2 records only", r, cov.len(), moves, 2 * moves, dropped, r));
    out
}
