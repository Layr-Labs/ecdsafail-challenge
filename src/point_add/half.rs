//! Half-sweep selector: ONE reusable qubit selects the half of the candidate indices of each big scan (D, F, D', F').
//! Just before the parent measures out the high bit of an erased candidate word, one CX copies that bit to the selector;
//! the scan trace (data/scans.trc, tools: halve.py) runs a half-length sweep between two conditional outer jumps and
//! swaps the selector into the (clean) high output slot at its end; the parent's conditional Z then restores the phase.
//! The selector has logical id SEL_ID in the 646-id space of the traces and glue items.  Segment maps send it to lane
//! SEL_LANE (633); after the relabelling it is renamed to lane 632 (the lane the relabelling hides in the parent), so
//! the circuit has 633 qubits.
use super::*;

/// logical id of the selector (unused by every segment map of the pack)
pub const SEL_ID: u16 = 646;
/// lane of the selector in the stream before the final compaction
pub const SEL_LANE: u16 = 633;
/// lane of the selector in the final stream
pub const SEL_FINAL: u16 = 632;
/// per scan (order D, F, D', F'): glue item holding the HMR of the erased candidate word's high bit, logical id of that
/// bit (the top output lane of the scan), measurement bit of that HMR (asserted)
pub const SITES: [(usize, u16, u16); 4] = [(1, 128, 10883), (3, 639, 11153), (9, 639, 11369), (11, 128, 11701)];
/// which scans carry the selector (must match the traces in data/scans.trc)
pub const ACTIVE: [bool; 4] = [true, true, true, true];

/// extend a segment map and its inverse with the selector
pub fn seg(mut s: Seg) -> Seg {
    assert!(s.map.len() == 646 && s.inv[SEL_LANE as usize] == NONE, "selector id/lane taken");
    s.map.push(SEL_LANE); s.inv[SEL_LANE as usize] = SEL_ID; s
}

/// insert CX(top, selector) before the HMR row of each active site (the item becomes / stays a hooked item)
pub fn add_hooks(pk: &Pack, g: &gir::Girs, v: &mut Vec<Option<i1::Hooked>>) {
    for (k, &(ii, top, mbit)) in SITES.iter().enumerate() {
        if !ACTIVE[k] { continue; }
        assert!(pk.items[ii].wm == 0, "half site item {} has a wire map", ii);
        let mut h = match v[ii].take() { Some(h) => h, None => i1::Hooked { rows: w2rw::item_rows(pk, g, ii), ins: Vec::new(), lane_space: false } };
        let idx: Vec<usize> = (0..h.rows.len()).filter(|&j| h.rows[j][0] == 12 && h.rows[j][1] == top).collect();
        assert!(idx.len() == 1 && h.rows[idx[0]][2] == mbit, "half site {}: HMR row of lane {} not unique / wrong bit", ii, top);
        let j = idx[0];
        for x in h.ins.iter_mut() { if *x >= j { *x += 1; } }
        h.rows.insert(j, [8, top, SEL_ID, NONE]); h.ins.push(j); h.ins.sort();
        v[ii] = Some(h);
    }
}
/// hook lengths: +1 row per active site
pub fn add_lens(pk: &Pack, v: &mut Vec<Option<u64>>) {
    for (k, &(ii, _, _)) in SITES.iter().enumerate() { if ACTIVE[k] { v[ii] = Some(v[ii].unwrap_or(pk.items[ii].n) + 1); } }
}
/// after the relabelling: rename lane SEL_LANE to SEL_FINAL in every record (the relabelled stream names neither 632 nor 633 otherwise)
pub fn compact<S: Slot + Send>(out: &mut [S], n: usize, relabelled: bool) {
    if !relabelled || !ACTIVE.iter().any(|&a| a) { return; }
    let seen = std::sync::atomic::AtomicUsize::new(0);
    i1::par_chunks(&mut out[..n], &|c: &mut [S], _b: usize| {
        let mut k = 0usize;
        for x in c.iter_mut() { let r = x.to_row(); let mut r2 = r;
            for j in 1..=qubits(r2[0]) { assert!(r2[j] != SEL_FINAL, "record names lane 632 before the selector rename"); if r2[j] == SEL_LANE { r2[j] = SEL_FINAL; } }
            if r2[0] == 2 { assert!(r2[2] != SEL_FINAL); if r2[2] == SEL_LANE { r2[2] = SEL_FINAL; } }
            if r2 != r { *x = S::from_row(r2); k += 1; } }
        seen.fetch_add(k, std::sync::atomic::Ordering::Relaxed); });
    eprintln!("half: {} records renamed from lane {} to lane {}", seen.into_inner(), SEL_LANE, SEL_FINAL);
}
/// lane count handed to the passes: 633 with a selector, the parent's 632 without
pub const WIDTH: usize = if ACTIVE[0] || ACTIVE[1] || ACTIVE[2] || ACTIVE[3] { 633 } else { 632 };
