//! Two-level clean-prefix schedule minimizing measured boundary replay.

/// Each nonfinal chunk retains its last wire. Its other `k - 1` wires
/// are replayed during measured cleanup. Fill the final live set exactly
/// when possible, attaining the lower bound `count - available` replays.
pub(crate) fn plan(count: usize, available: usize) -> Option<Vec<usize>> {
    if count == 0 { return Some(Vec::new()); }
    if available == 0 { return None; }
    let mut remaining = count;
    let mut boundaries = 0;
    let mut chunks = Vec::new();
    while remaining > available.saturating_sub(boundaries) {
        let room = available.saturating_sub(boundaries);
        if room < 2 { return None; }
        let excess = remaining - room;
        let k = room.min(excess + 1);
        chunks.push(k);
        remaining -= k;
        boundaries += 1;
    }
    if remaining != 0 { chunks.push(remaining); }
    Some(chunks)
}

pub(crate) fn selftest() {
    for count in 0usize..=512 {
        for available in 0usize..=512 {
            if let Some(chunks) = plan(count, available) {
                assert_eq!(chunks.iter().sum::<usize>(), count);
                let peak = chunks.iter().enumerate().map(|(i, &k)| i + k).max().unwrap_or(0);
                assert!(peak <= available);
                let replay: usize = chunks.iter().take(chunks.len().saturating_sub(1))
                    .map(|&k| k - 1).sum();
                assert_eq!(replay, count.saturating_sub(available));
            } else {
                assert!(count > available * (available + 1) / 2);
            }
        }
    }
    eprintln!("CLEAN_CHUNK_PLAN PASS: 263169 schedules, peak and replay bound");
}
