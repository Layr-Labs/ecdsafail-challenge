//! (internal) (internal) (internal) ((internal)): rewrite step `pad` = digit gadgets whose TOP PAD is wire E (251).
//! Input rows: after `negxall:251` (the pad's X pair is gone: E = 0 before the gadget and E carries G = ladder xor carry inside
//! it).  A pad episode is the stretch from the first write of E to the write that closes it (mirrored compute / uncompute).
//! Inside it E is replaced by a never-touched lane d (value d0, restored): writes go to d, control uses read d = G xor d0.  The
//! d0 terms are echoed outside the episode, where d = d0:
//!   type 1  C(L, E -> b)  twice with L toggled by e*h between: b ^= e*h*G   echo A: b ^= e*h*d0  at a time when h has the same value
//!   type 2  C(e, E -> L)  twice around C(L, b -> h):           h ^= e*b*G   echo B: h ^= e*b*d0  at a time when b has the same value
//! forward gadget (type 2 first): B before the episode, A after;  reversed gadget (type 1 first): A before, B after.
//! Exact for every d0 and every state with E = 0 at the episode's entry (checked per episode on random states by `wtest`).
use super::*;
use super::w2::*;
use super::c3ctr::{E, DPAD, QLOAN, Win, tgt, is_gate, has_ctl, names, cccx};

thread_local! { pub static PWINS: std::cell::RefCell<Vec<Win>> = std::cell::RefCell::new(Vec::new()); }

fn episode(rows: &[Row], first: usize, maxlen: usize) -> Result<(usize, Vec<Row>), String> {
    let n = rows.len(); let mut open: Vec<Row> = Vec::new(); let mut last = usize::MAX;
    for k in first..n.min(first + maxlen) { let r = rows[k]; if !is_gate(&r) { return Err(format!("kind {} inside the episode", r[0])); }
        if names(&r, DPAD) || names(&r, QLOAN) { return Err("loan named".into()); }
        if tgt(&r) != E { continue; } if has_ctl(&r, E) { return Err("E controls its own write".into()); }
        if let Some(p) = open.iter().rposition(|q| *q == r) { open.remove(p); } else { open.push(r); }
        if open.is_empty() { last = k; break; } }
    if last == usize::MAX { return Err("episode does not close".into()); }
    // control uses of E inside
    let mut uses: Vec<(usize, u16, u16)> = Vec::new();
    for k in first..=last { let r = rows[k]; if tgt(&r) == E || !has_ctl(&r, E) { continue; } if r[0] != 13 { return Err("CX from E inside the episode".into()); }
        let x = if r[1] == E { r[2] } else { r[1] }; uses.push((k, x, r[3])); }
    let mut out: Vec<Row> = Vec::with_capacity(last - first + 12);
    let subst = |r: Row| -> Row { let mut q = r; for j in 1..=qubits(r[0]) { if q[j] == E { q[j] = DPAD; } } q };
    if uses.is_empty() { return Err("no control use of E inside (not a pad gadget)".into()); }
    // the loan L: a wire that is the partner of some uses (type 1) and the target of the others (type 2)
    let mut loan = NONE; for &(_, x, _) in &uses { if uses.iter().any(|&(_, _, y2)| y2 == x) { loan = x; } }
    if loan == NONE { return Err("no loan pattern".into()); }
    let t1: Vec<&(usize, u16, u16)> = uses.iter().filter(|u| u.1 == loan).collect(); let t2: Vec<&(usize, u16, u16)> = uses.iter().filter(|u| u.2 == loan).collect();
    if t1.len() + t2.len() != uses.len() || t1.is_empty() || t2.is_empty() { return Err("uses are not type 1 / type 2".into()); }
    let bl = t1[0].2; let e = t2[0].1; if t1.iter().any(|u| u.2 != bl) || t2.iter().any(|u| u.1 != e) || t1.len() % 2 != 0 || t2.len() % 2 != 0 { return Err("type 1 / type 2 not uniform".into()); }
    let mut h = NONE; for k in first..=last { let r = rows[k]; if r[0] == 13 && r[3] != E && ((r[1] == loan && r[2] == bl) || (r[2] == loan && r[1] == bl)) { if h != NONE && h != r[3] { return Err("slot not unique".into()); } h = r[3]; } }
    if h == NONE { return Err("no slot".into()); }
    if [e, h, bl, loan].contains(&E) { return Err("role is E".into()); }
    let forward = t2[0].0 < t1[0].0;
    if forward { cccx(e, bl, DPAD, h, QLOAN, &mut out); } else { cccx(e, h, DPAD, bl, QLOAN, &mut out); }
    for k in first..=last { out.push(subst(rows[k])); }
    if forward { cccx(e, h, DPAD, bl, QLOAN, &mut out); } else { cccx(e, bl, DPAD, h, QLOAN, &mut out); }
    Ok((last + 1, out))
}
/// build-time instance check: 2 x 256 random states with E = 0, every wire equal after the episode
fn inline_ok(old: &[Row], new: &[Row], seed: usize) -> bool {
    for rep in 0..2u64 { let mut o = super::c2e::Mini::random((seed as u64 + 12345).wrapping_mul(0x9E3779B97F4A7C15) ^ (rep + 7).wrapping_mul(0xD1B54A32D192ED03));
        o.q[E as usize] = Z; let mut nw = super::c2e::Mini { q: o.q.clone() };
        for r in old { o.exec(r); } for r in new { nw.exec(r); }
        if o.q != nw.q { return false; } }
    true
}
pub fn pad(rows: Vec<Row>, info: &mut w2rw::Info) -> Vec<Row> {
    let n = rows.len(); let mut out: Vec<Row> = Vec::with_capacity(n + n / 256); let mut wins: Vec<Win> = Vec::new(); let mut p = 0usize; let mut i = 0usize;
    let mut rej: std::collections::BTreeMap<String, (u64, usize)> = std::collections::BTreeMap::new(); let mut plain = 0u64;
    let maxlen: usize = env("C3_PADMAX").map(|x| x.parse().unwrap()).unwrap_or(4000);
    let lo: usize = env("C3_PLO").map(|x| x.parse().unwrap()).unwrap_or(0); let hi: usize = env("C3_PHI").map(|x| x.parse().unwrap()).unwrap_or(usize::MAX);
    // episodes opened by a ladder write CX(a -> E) or a carry write CCX(a, b -> E)
    while i < n { let r = rows[i];
        if !(((r[0] == 8 && r[2] == E && r[3] == NONE) || (r[0] == 13 && r[3] == E)) && i >= lo && i < hi) { i += 1; continue; }
        match episode(&rows, i, maxlen) {
            Ok((end, new)) if !inline_ok(&rows[i..end], &new, i) => { let en = rej.entry("fails the random-state check".to_string()).or_insert((0, i)); en.0 += 1; let _ = end; i += 1; }
            Ok((end, new)) => { if new.len() == end - i { plain += 1; }
                out.extend_from_slice(&rows[p..i]); let na = out.len(); out.extend_from_slice(&new);
                wins.push(Win { a: i, b: end, na, nb: out.len(), kind: 2, tags: Vec::new(), start_toggle: false, cmax: 0, ntog: 0, npad: 1, n2: 0 }); p = end; i = end; }
            Err(e) => { let key: String = e.chars().map(|c| if c.is_ascii_digit() { '#' } else { c }).collect(); let en = rej.entry(key).or_insert((0, i)); en.0 += 1;
                if env("C3_VERBOSE").is_some() { println!("  pad reject at {}: {}", i, e); } i += 1; } } }
    out.extend_from_slice(&rows[p..]);
    let (old, new): (usize, usize) = (wins.iter().map(|w| w.b - w.a).sum(), wins.iter().map(|w| w.nb - w.na).sum());
    info.notes.push(format!("pad: episodes {} ({} without a control use), rows {} -> {} ({:+}); rejected {:?}", wins.len(), plain, old, new, new as i64 - old as i64, rej));
    PWINS.with(|w| *w.borrow_mut() = wins);
    out
}
