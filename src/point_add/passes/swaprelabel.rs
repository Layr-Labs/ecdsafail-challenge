//! swaprelabel: exact record pass.  Deletes every swap written as CX(x,y) CX(y,x) CX(x,y) (no per-record condition) by lane relabelling.
//! Condition-scope aware: a swap executed inside a PushCondition scope only happens on the shots where the scope's conditions hold, so the
//! relabelling is undone by explicit fix-up swaps (3 CX per displaced lane) just before the scope's PopCondition, inside the scope.
//! Called on one padded chunk (every pop matches a push), so the relabelling is the identity at the chunk end; deterministic (ordered maps only);
//! touches only the lane operands of kinds 6 7 8 9 10 11 12 13 14, never classical bit ids, kinds or the number of CCX.
use std::collections::{BTreeMap, BTreeSet};
type R = [u16; 4];
const N: u16 = u16::MAX;
fn nq(k: u16) -> usize { match k { 13 | 14 => 3, 8 | 9 | 10 => 2, 6 | 7 | 11 | 12 => 1, _ => 0 } }
fn put(o: &mut Vec<R>, mut r: R, sg: &[u16]) { for j in 1..=nq(r[0]) { r[j] = sg[r[j] as usize]; } o.push(r); }
/// close a scope: undo its logged swaps on `sg`, emit the fix-up swaps on physical lanes
fn close(o: &mut Vec<R>, sg: &mut [u16], log: &mut Vec<(u16, u16)>) {
    if log.is_empty() { return; }
    let touched: BTreeSet<u16> = log.iter().flat_map(|&(x, y)| [x, y]).collect();
    let s1: BTreeMap<u16, u16> = touched.iter().map(|&l| (l, sg[l as usize])).collect();
    for &(x, y) in log.iter().rev() { sg.swap(x as usize, y as usize); }
    // content now at physical s1[l] must go to physical sg[l]
    let mut f: BTreeMap<u16, u16> = BTreeMap::new();
    for &l in &touched { let (src, dst) = (s1[&l], sg[l as usize]); if src != dst { f.insert(src, dst); } }
    let mut done: BTreeSet<u16> = BTreeSet::new();
    for (&s, _) in f.iter() {
        if done.contains(&s) { continue; }
        let mut cyc = vec![s]; done.insert(s);
        let mut t = f[&s];
        while t != s { cyc.push(t); done.insert(t); t = *f.get(&t).expect("not a permutation"); }
        for i in 1..cyc.len() { let (x, y) = (cyc[0], cyc[i]); for r in [[8u16, x, y, N], [8, y, x, N], [8, x, y, N]] { o.push(r); } }
    }
    log.clear();
}
/// one padded chunk in, relabelled chunk out
pub fn swp(rows: Vec<R>) -> Vec<R> {
    let mut o: Vec<R> = Vec::with_capacity(rows.len());
    let mut sg: Vec<u16> = (0..1024u16).collect();
    let mut logs: Vec<Vec<(u16, u16)>> = vec![Vec::new()];
    let mut pend: Vec<R> = Vec::new();
    for rec in rows {
        let cxu = rec[0] == 8 && rec[3] == N && rec[1] != rec[2] && (rec[1] as usize) < 1024 && (rec[2] as usize) < 1024;
        if cxu {
            if pend.len() == 1 && pend[0][1] == rec[2] && pend[0][2] == rec[1] { pend.push(rec); continue; }
            if pend.len() == 2 && pend[0][1] == rec[1] && pend[0][2] == rec[2] {
                sg.swap(rec[1] as usize, rec[2] as usize); logs.last_mut().unwrap().push((rec[1], rec[2])); pend.clear(); continue;
            }
            for p in pend.drain(..) { put(&mut o, p, &sg); }
            pend.push(rec); continue;
        }
        for p in pend.drain(..) { put(&mut o, p, &sg); }
        if rec[0] == 15 { put(&mut o, rec, &sg); logs.push(Vec::new()); continue; }
        if rec[0] == 16 {
            let mut lg = logs.pop().unwrap_or_default(); if logs.is_empty() { logs.push(Vec::new()); }
            close(&mut o, &mut sg, &mut lg); o.push(rec); continue;
        }
        put(&mut o, rec, &sg);
    }
    for p in pend.drain(..) { put(&mut o, p, &sg); }
    while let Some(mut lg) = logs.pop() { close(&mut o, &mut sg, &mut lg); }
    o
}
