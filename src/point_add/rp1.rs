//! q631 / rp1 (local research, NOT part of any package; agent rp1, 2026-11-19): the SECOND hidden lane, soft mode.
//!
//! The 632-lane list (after i1::apply and the ITEM 4 rewrites, before the peephole) is renamed per stretch by the frame
//! tau_g = the transposition (631 g) of physical lanes, where g is the lane hidden on lane 631 in that stretch:
//!   * g != 631: g is zero at the stretch start (on the planner's sample) and no record of the stretch names it, so after
//!     the renaming no record of the stretch names lane 631 (lane 631 holds g's zero content);
//!   * g == 631 (identity): either lane 631 itself is zero and unnamed there ("nothing hidden"), or the planner found no
//!     lane ("uncovered"): then lane 631 keeps its content and the records that name it name lane 631 (SOFT mode).
//! At a change g -> c (table entry (pos, c, flags)) lane 631's content moves from physical g (= tau_g(631)) to physical c
//! (= tau_c(631)) with two CX when flag bit 0 is set (CX g->c, CX c->g): physical c holds a zero lane before (c's own zero
//! content, or for c = 631 the zero content of the old hidden lane g) and physical g holds a zero lane after.  The planner
//! clears the flag only where lane 631's content is zero (on its sample) at the switch.  A switch point inside condition
//! scopes gets its moves wrapped (scopes popped, moves, scopes re-pushed): see entry_rows.
//! The table has i1's form (magic I1RELAB1, n, hash of the list, h0, entries (pos, c, flags)), stored uncompressed; it is
//! bound to the list's length and hash (asserted).  Planner: src/bin/rpplan.rs; checks: src/bin/rpcheck.rs, rpops.rs.
//! Switch `ON` = false and runtime `FORCE` (local tools) = false: nothing here runs, the build is byte-identical.
//! The table is read from the file named by the environment variable RP1_TABLE when the hook runs.
use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub const ON: bool = super::FINAL631;
/// runtime override for local tools (default false = switch off)
pub static FORCE: AtomicBool = AtomicBool::new(false);
#[inline] pub fn active() -> bool { ON || FORCE.load(Ordering::Relaxed) }
/// the lane that is to disappear
pub const HIDE2: u16 = 631;
pub const TABLE_ENV: &str = "RP1_TABLE";
/// worker threads of the renaming pass (machine rule: at most 4)
pub const THREADS: usize = 3;

/// frame of a stretch: the transposition (631 g) of physical lanes (identity when g = 631)
#[inline] pub fn sigma2(mut r: Row, g: u16) -> Row { if g == HIDE2 { return r; }
    let f = |l: u16| if l == HIDE2 { g } else if l == g { HIDE2 } else { l };
    for j in 1..=qubits(r[0]) { r[j] = f(r[j]); } if r[0] == 2 { r[2] = f(r[2]); } r }
/// the move rows of an entry g -> c (physical lanes, stream order)
pub fn moves2(g: u16, c: u16, f: u8) -> Vec<Row> { assert!(f & !1 == 0, "rp1: flags {}", f); let mut v = Vec::new();
    if f & 1 == 1 { assert!(g != c, "rp1: move to the same lane"); v.push([8, g, c, NONE]); v.push([8, c, g, NONE]); } v }
#[inline] pub fn names(r: &Row, l: u16) -> bool { i1::names(r, l) }
/// the table in i1's binary form (uncompressed)
pub fn table_bytes(t: &i1::Relabel) -> Vec<u8> {
    let mut d: Vec<u8> = Vec::new(); d.extend_from_slice(b"I1RELAB1"); d.extend_from_slice(&t.n.to_le_bytes()); d.extend_from_slice(&t.hash.to_le_bytes());
    d.extend_from_slice(&t.h0.to_le_bytes()); d.extend_from_slice(&(t.ent.len() as u32).to_le_bytes());
    let mut prev = 0u64;
    for (k, e) in t.ent.iter().enumerate() { assert!(k == 0 || e.0 > prev, "rp1: entries not increasing"); let mut v = e.0 - prev; prev = e.0;
        loop { let b = (v & 127) as u8; v >>= 7; if v == 0 { d.push(b); break; } d.push(b | 128); }
        d.extend_from_slice(&e.1.to_le_bytes()); d.push(e.2); }
    d }
/// fin631 package: the planned layer-2 table (q631/fin3/plans5/final5.table: DEV round 2 + holdout verified), used when RP1_TABLE is unset
const TABLE_631: &[u8] = include_bytes!("data/l2_631.lzma");
pub fn load_table() -> i1::Relabel { match Err::<String, ()>(()) {
    Ok(p) => { let d = std::fs::read(&p).unwrap_or_else(|e| panic!("rp1: table {}: {}", p, e)); i1::parse_table(&d) }
    Err(_) => {
        assert!(super::FINAL631, "rp1: set {} to the planned table", TABLE_ENV);
        i1::parse_table(&lzma::decode(TABLE_631).expect("second relabel table"))
    } } }
pub fn list_hash<S: Slot>(out: &[S]) -> u64 { let mut h = i1::HASH0; for s in out { h = i1::hash_step(h, s.to_row()); } h }
/// the rows inserted before every entry: its moves, and when the switch point lies inside condition scopes (PUSH / POP) the
/// moves WRAPPED: the open scopes are popped first and re-pushed after with the same bits in the same order, so the two CX run
/// on every shot (inside a scope they would run only where its condition holds).  Asserts that no bit of an open scope was
/// written (bit ops, HMR outcome) since its PUSH, so the re-push restores the same condition.  Returns (rows per entry,
/// entries wrapped, deepest wrap).
pub fn entry_rows<S: Slot>(out: &[S], n: usize, t: &i1::Relabel) -> (Vec<Vec<Row>>, usize, usize) {
    let m = t.ent.len(); let hid = |k: usize| if k == 0 { t.h0 } else { t.ent[k - 1].1 };
    let mut res: Vec<Vec<Row>> = vec![Vec::new(); m]; let (mut wrapped, mut deepest) = (0usize, 0usize);
    let mut stack: Vec<(u16, bool)> = Vec::new(); let mut k = 0usize;
    let mark = |stack: &mut Vec<(u16, bool)>, b: u16| { for x in stack.iter_mut() { if x.0 == b { x.1 = true; } } };
    for i in 0..n {
        while k < m && t.ent[k].0 == i as u64 {
            let mv = moves2(hid(k), t.ent[k].1, t.ent[k].2);
            if !mv.is_empty() && !stack.is_empty() {
                assert!(stack.iter().all(|x| !x.1), "rp1: entry {} at {} lies in a condition scope whose bit was written since its PUSH ({:?})", k, i, stack);
                let mut v: Vec<Row> = Vec::new(); for _ in 0..stack.len() { v.push([16, NONE, NONE, NONE]); } v.extend(mv); for x in stack.iter() { v.push([15, x.0, NONE, NONE]); }
                wrapped += 1; deepest = deepest.max(stack.len()); res[k] = v;
            } else { res[k] = mv; }
            k += 1; }
        let r = out[i].to_row();
        match r[0] { 15 => stack.push((r[1], false)), 16 => { stack.pop(); }, 3 | 4 | 5 => mark(&mut stack, r[1]), 12 => if r[2] != NONE { mark(&mut stack, r[2]); }, _ => {} }
    }
    (res, wrapped, deepest)
}
/// frame (hidden lane) of record position p of the PLANNED list
#[inline] pub fn frame_at(t: &i1::Relabel, p: u64) -> u16 { let k = t.ent.partition_point(|e| e.0 <= p); if k == 0 { t.h0 } else { t.ent[k - 1].1 } }

/// run f(chunk, first index) over xs on THREADS threads
fn par4<T: Send>(xs: &mut [T], f: &(dyn Fn(&mut [T], usize) + Sync)) {
    let cs = (xs.len() / (4 * THREADS)).max(1 << 20);
    let work: std::sync::Mutex<Vec<(usize, &mut [T])>> = std::sync::Mutex::new(xs.chunks_mut(cs).enumerate().map(|(i, c)| (i * cs, c)).rev().collect());
    let job = || loop { let c = work.lock().unwrap().pop(); match c { Some((b, c)) => f(c, b), None => break } };
    std::thread::scope(|sc| { for _ in 1..THREADS { if std::thread::Builder::new().spawn_scoped(sc, &job).is_err() { break; } } job(); });
}

#[derive(Default, Debug, Clone)]
pub struct SoftStats { pub entries: usize, pub move_entries: usize, pub move_rows: usize, pub wrapped: usize, pub deepest_wrap: usize, pub named631_identity: u64, pub identity_frames: usize, pub hidden_frames: usize, pub n_in: usize, pub n_out: usize }

/// the builder hook: table from RP1_TABLE
pub fn apply_soft<S: Slot + Send>(out: &mut Vec<S>, n: usize) -> usize { let t = load_table(); let (m, st, _) = apply_soft_t(out, n, &t); eprintln!("rp1 soft: {:?}", st); m }

/// in place: out[..n] -> the soft-mode stream (moves inserted); out grows if needed (room for the nonce tail kept);
/// returns the new length, counts and the rows inserted before each entry.  Asserts: table bound to this list; no record of
/// a stretch with g != 631 names g.
pub fn apply_soft_t<S: Slot + Send>(out: &mut Vec<S>, n: usize, t: &i1::Relabel) -> (usize, SoftStats, Vec<usize>) {
    let h = list_hash(&out[..n]);
    assert!(t.n == n as u64 && t.hash == h, "rp1: table planned on another list (table n {} hash {:016x}, list n {} hash {:016x}): re-plan", t.n, t.hash, n, h);
    let m = t.ent.len(); let hid = |k: usize| if k == 0 { t.h0 } else { t.ent[k - 1].1 };
    for k in 0..m { assert!(t.ent[k].0 < n as u64 && (k == 0 || t.ent[k].0 > t.ent[k - 1].0), "rp1: entry {} position", k); assert!(t.ent[k].1 != hid(k), "rp1: entry {} keeps the lane", k); assert!(t.ent[k].1 <= HIDE2); }
    let (mvs, wrapped, deepest) = entry_rows(&out[..n], n, t);
    let extra: usize = mvs.iter().map(|v| v.len()).sum(); let total = n + extra;
    let need = total + TAIL; if out.len() < need { out.reserve_exact(need - out.len()); out.resize(need, S::empty()); }
    // 1. rename every record with the frame of its stretch; count records that name the hidden lane (must be 0) and records naming 631 in identity frames
    let bad = AtomicUsize::new(0); let n631 = AtomicUsize::new(0);
    par4(&mut out[..n], &|c: &mut [S], b: usize| { let mut k = t.ent.partition_point(|e| e.0 <= b as u64); let mut g = hid(k); let (mut x, mut y) = (0usize, 0usize);
        for (o, s) in c.iter_mut().enumerate() { let i = (b + o) as u64; while k < m && t.ent[k].0 <= i { g = t.ent[k].1; k += 1; }
            let r = s.to_row(); if g != HIDE2 && names(&r, g) { x += 1; } let r2 = sigma2(r, g); if names(&r2, HIDE2) { y += 1; } *s = S::from_row(r2); }
        bad.fetch_add(x, Ordering::Relaxed); n631.fetch_add(y, Ordering::Relaxed); });
    let bad = bad.into_inner(); assert!(bad == 0, "rp1: {} records name their stretch's hidden lane (planner bug)", bad);
    // 2. top down: move each stretch up by the moves before it, then write the moves of its entry just in front of it
    let mut off: Vec<usize> = Vec::with_capacity(m); let mut acc = 0usize; for v in &mvs { acc += v.len(); off.push(acc); }
    for k in (0..m).rev() { let start = t.ent[k].0 as usize; let end = if k + 1 < m { t.ent[k + 1].0 as usize } else { n };
        if end > start && off[k] > 0 { out.copy_within(start..end, start + off[k]); }
        let base = start + off[k] - mvs[k].len(); for (q, r) in mvs[k].iter().enumerate() { out[base + q] = S::from_row(*r); } }
    let st = SoftStats { entries: m, move_entries: mvs.iter().filter(|v| !v.is_empty()).count(), move_rows: extra, wrapped, deepest_wrap: deepest, named631_identity: n631.into_inner() as u64,
        identity_frames: (0..=m).filter(|&k| hid(k) == HIDE2).count(), hidden_frames: (0..=m).filter(|&k| hid(k) != HIDE2).count(), n_in: n, n_out: total };
    (total, st, mvs.iter().map(|v| v.len()).collect())
}
