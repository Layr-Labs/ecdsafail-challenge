// Exact macro-level rewrites on the F gate list (before the dirty-ladder expansion):
// (E1) adjacent same-target MCX whose controls differ by one literal are merged:
//      S.x ^ S.y = S.(x^y) via CX(x->y); S.x ^ S = S.!x; S.x ^ S.!x = S.
// (E2) adjacent MCX with distinct targets whose control sets are S+x_i (size k) or S (size k-1) share one Barenco
//      ladder; only the target gates are repeated per extra member (2 CCX each).
use super::{gc, gt, gx, mac_expand, Lit, Mac, G, MAC};
use std::collections::HashSet;
use std::sync::atomic::{AtomicU64, Ordering};

static E1F: [AtomicU64; 7] = [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)];
fn e1f(i: usize) -> Option<Item> {
    E1F[i].fetch_add(1, Ordering::Relaxed);
    None
}

#[derive(Clone)]
struct Item {
    cc: bool, // clean-lane (cc_core) form: k >= 3 with no dirty ancillas
    orig: Option<G>,
    cx: Vec<(u32, u32)>,
    lits: Vec<Lit>,
    tgt: u32,
    an: Vec<u32>,
}
enum Piece {
    Gate(G),
    It(Item),
}

fn cost(k: usize, cc: bool) -> i64 {
    match k {
        0 | 1 => 0,
        2 => 1,
        _ => if cc { 2 * k as i64 - 3 } else { 4 * k as i64 - 8 },
    }
}

fn wires_ok(lits: &[Lit], tgt: u32, an: &[u32]) -> bool {
    let mut seen = HashSet::new();
    for l in lits {
        if !seen.insert(l.0) {
            return false;
        }
    }
    if seen.contains(&tgt) {
        return false;
    }
    for a in an {
        if seen.contains(a) || *a == tgt {
            return false;
        }
    }
    true
}

fn emit_plain(it: &Item, out: &mut Vec<G>) {
    for &(x, y) in &it.cx {
        out.push(gc(x, y));
    }
    let k = it.lits.len();
    if k >= 3 {
        let m = Mac { lits: it.lits.clone(), tgt: it.tgt, an: it.an.clone() };
        mac_expand(&m, out);
    } else {
        let pre: Vec<G> = it.lits.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
        out.extend_from_slice(&pre);
        match k {
            0 => out.push(gx(it.tgt)),
            1 => out.push(gc(it.lits[0].0, it.tgt)),
            _ => out.push(gt(it.lits[0].0, it.lits[1].0, it.tgt)),
        }
        out.extend_from_slice(&pre);
    }
    for &(x, y) in it.cx.iter().rev() {
        out.push(gc(x, y));
    }
}

/// merge b into a (both MCX onto the same target, a first, nothing in between)
fn merge_same_t(a: &Item, b: &Item) -> Option<Item> {
    if a.tgt != b.tgt {
        return None;
    }
    if a.cc != b.cc {
        return e1f(5);
    }
    let da: Vec<Lit> = a.lits.iter().filter(|x| !b.lits.contains(x)).cloned().collect();
    let db: Vec<Lit> = b.lits.iter().filter(|x| !a.lits.contains(x)).cloned().collect();
    if da.len() > 1 || db.len() > 1 || da.len() + db.len() == 0 {
        return None;
    }
    let common: Vec<Lit> = a.lits.iter().filter(|x| b.lits.contains(x)).cloned().collect();
    let mut lits = common.clone();
    let cx: Vec<(u32, u32)>;
    if da.len() == 1 && db.len() == 1 {
        let (x, px) = da[0];
        let (y, py) = db[0];
        if x == y {
            if !a.cx.is_empty() || !b.cx.is_empty() {
                return e1f(0);
            }
            cx = vec![];
        } else {
            if !b.cx.is_empty() {
                return e1f(1);
            }
            if !a.cx.is_empty() && a.cx.last().unwrap().1 != x {
                return e1f(2);
            }
            if a.cx.iter().any(|&(_, d)| d == y) {
                return e1f(6); // guard: incoming wire already written by the CX prefix
            }
            let mut c = a.cx.clone();
            c.push((x, y));
            cx = c;
            lits.push((y, px == py));
        }
    } else if da.len() == 1 {
        if !b.cx.is_empty() || !a.cx.is_empty() {
            return e1f(1);
        }
        lits.push((da[0].0, !da[0].1));
        cx = vec![];
    } else {
        if !b.cx.is_empty() || !a.cx.is_empty() {
            return e1f(1);
        }
        lits.push((db[0].0, !db[0].1));
        cx = vec![];
    }
    let tgt = a.tgt;
    for &(x, y) in &cx {
        if x == tgt || y == tgt || common.iter().any(|l| l.0 == x || l.0 == y) {
            return e1f(3);
        }
    }
    let k = lits.len();
    if a.cc {
        let mut seen = HashSet::new();
        if lits.iter().any(|l| !seen.insert(l.0)) || seen.contains(&tgt) {
            return e1f(4);
        }
        return Some(Item { cc: true, orig: None, cx, lits, tgt, an: vec![] });
    }
    let need = if k >= 3 { k - 2 } else { 0 };
    for cand in [&a.an, &b.an] {
        if cand.len() >= need {
            let c: Vec<u32> = cand[..need].to_vec();
            if wires_ok(&lits, tgt, &c) {
                return Some(Item { cc: false, orig: None, cx, lits, tgt, an: c });
            }
        }
    }
    e1f(4)
}

/// shared-ladder group of plain items around the control set s (|s| = k-1): members are s+x_i (ext) or s (core).
/// Returns a common valid ancilla list of length k-2 (taken from an ext member).
fn group_ok(s: &[Lit], mem: &[&Item], k: usize) -> Result<Vec<u32>, u8> {
    let mut tg = HashSet::new();
    let mut allw: HashSet<u32> = HashSet::new();
    let mut xs = HashSet::new();
    let mut n_ext = 0;
    let mut n_core = 0;
    for m in mem {
        if !tg.insert(m.tgt) {
            return Err(1);
        }
        for l in &m.lits {
            allw.insert(l.0);
            if !s.contains(l) {
                if !xs.insert(l.0) {
                    return Err(2);
                }
                if s.iter().any(|q| q.0 == l.0) {
                    return Err(2);
                }
            }
        }
        if m.lits.len() == k {
            n_ext += 1;
        } else {
            n_core += 1;
        }
    }
    if n_ext == 0 || (n_core > 0 && k < 4) {
        return Err(5);
    }
    for m in mem {
        if allw.contains(&m.tgt) {
            return Err(3);
        }
    }
    for m in mem {
        if m.lits.len() == k && m.an.len() == k - 2 && m.an.iter().all(|w| !allw.contains(w) && !tg.contains(w)) {
            return Ok(m.an.clone());
        }
    }
    Err(4)
}

/// is it ext/core wrt s ?
fn role(it: &Item, s: &[Lit]) -> Option<bool> {
    // Some(true) = ext (s + one literal), Some(false) = core (== s)
    if !(it.orig.is_some() && it.cx.is_empty()) {
        return None;
    }
    let d = it.lits.iter().filter(|x| !s.contains(x)).count();
    let missing = s.iter().filter(|x| !it.lits.contains(x)).count();
    if missing != 0 {
        return None;
    }
    match d {
        0 if it.lits.len() == s.len() => Some(false),
        1 if it.lits.len() == s.len() + 1 => Some(true),
        _ => None,
    }
}

fn emit_group(s: &[Lit], mem: &[&Item], anl: &[u32], k: usize, out: &mut Vec<G>) {
    let mut sorted_s = s.to_vec();
    sorted_s.sort();
    let mut cs: Vec<u32> = sorted_s.iter().map(|x| x.0).collect();
    cs.push(u32::MAX);
    let mut pre: Vec<G> = sorted_s.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    let mut ts_a: Vec<G> = vec![];
    let mut ts_b: Vec<G> = vec![];
    for it in mem {
        if it.lits.len() == k {
            let x = *it.lits.iter().find(|l| !s.contains(l)).unwrap();
            if !x.1 {
                pre.push(gx(x.0));
            }
            ts_a.push(gt(x.0, anl[k - 3], it.tgt));
        } else {
            ts_b.push(gt(cs[k - 2], anl[k - 4], it.tgt));
        }
    }
    let mut chain: Vec<G> = vec![];
    let mut ii = k - 2;
    while ii > 1 {
        chain.push(gt(cs[ii], anl[ii - 2], anl[ii - 1]));
        ii -= 1;
    }
    let mid = gt(cs[0], cs[1], anl[0]);
    out.extend_from_slice(&pre);
    // first half: TsA TsB [U_{k-2}] inner mid rev(inner) TsB [U_{k-2}] TsA
    out.extend_from_slice(&ts_a);
    out.extend_from_slice(&ts_b);
    let (head, inner): (Vec<G>, Vec<G>) = if chain.is_empty() { (vec![], vec![]) } else { (vec![chain[0]], chain[1..].to_vec()) };
    out.extend_from_slice(&head);
    out.extend_from_slice(&inner);
    out.push(mid);
    out.extend(inner.iter().rev().cloned());
    out.extend_from_slice(&ts_b);
    out.extend_from_slice(&head);
    out.extend_from_slice(&ts_a);
    // second half
    out.extend_from_slice(&chain);
    out.push(mid);
    out.extend(chain.iter().rev().cloned());
    out.extend_from_slice(&pre);
}

pub fn run(opt: Vec<G>, t: &[Mac], e1: bool, e2: bool) -> Vec<G> {
    let mut pieces: Vec<Piece> = Vec::with_capacity(opt.len());
    let mut cur: Option<Item> = None;
    let (mut n_e1, mut s_e1) = (0u64, 0i64);
    for g in opt {
        if g.0 != MAC {
            if let Some(c) = cur.take() {
                pieces.push(Piece::It(c));
            }
            pieces.push(Piece::Gate(g));
            continue;
        }
        let m = &t[g.1 as usize];
        let it = Item { cc: m.an.is_empty(), orig: Some(g), cx: vec![], lits: m.lits.clone(), tgt: m.tgt, an: m.an.clone() };
        if let Some(c) = cur.take() {
            if e1 {
                if let Some(mg) = merge_same_t(&c, &it) {
                    n_e1 += 1;
                    s_e1 += cost(c.lits.len(), c.cc) + cost(it.lits.len(), it.cc) - cost(mg.lits.len(), mg.cc);
                    cur = Some(mg);
                    continue;
                }
            }
            pieces.push(Piece::It(c));
        }
        cur = Some(it);
    }
    if let Some(c) = cur.take() {
        pieces.push(Piece::It(c));
    }
    eprintln!("MERGE E1 failures: {:?}", E1F.iter().map(|x| x.load(Ordering::Relaxed)).collect::<Vec<_>>());
    eprintln!("MERGE E1: merges {n_e1}, expected T saved per F pass {s_e1}");

    let mut out: Vec<G> = Vec::with_capacity(pieces.len() * 3);
    let (mut n_g, mut n_m, mut s_e2, mut n_core) = (0u64, 0u64, 0i64, 0u64);
    let mut i = 0;
    let n = pieces.len();
    while i < n {
        match &pieces[i] {
            Piece::Gate(g) => {
                out.push(*g);
                i += 1;
            }
            Piece::It(a) => {
                let plain_a = a.orig.is_some() && a.cx.is_empty();
                if e2 && plain_a && !a.cc && a.lits.len() >= 3 {
                    // candidate control sets s: a as ext (drop one literal) or a as core (s = a.lits)
                    let mut cands: Vec<Vec<Lit>> = vec![];
                    for xi in 0..a.lits.len() {
                        let mut s = a.lits.clone();
                        s.remove(xi);
                        cands.push(s);
                    }
                    if a.lits.len() >= 3 {
                        cands.push(a.lits.clone());
                    }
                    let mut best: Option<(Vec<Lit>, Vec<&Item>, Vec<u32>, usize, i64)> = None;
                    for s in cands {
                        // roles are only defined if group has an ext member; first member may be core
                        let mut mem: Vec<&Item> = vec![];
                        let mut jj = i;
                        let mut ok_prefix: Option<(Vec<&Item>, Vec<u32>, usize)> = None;
                        while let Some(Piece::It(c)) = pieces.get(jj) {
                            let r = match role(c, &s) {
                                Some(r) => r,
                                None => break,
                            };
                            let k = s.len() + 1;
                            let _ = r;
                            let mut trial = mem.clone();
                            trial.push(c);
                            // evaluate validity of the trial group (needs an ext member eventually)
                            match group_ok(&s, &trial, k) {
                                Ok(anl) => {
                                    mem.push(c);
                                    jj += 1;
                                    if mem.len() >= 2 {
                                        ok_prefix = Some((mem.clone(), anl, k));
                                    }
                                }
                                Err(5) => {
                                    // no ext member yet (only cores): keep collecting
                                    mem.push(c);
                                    jj += 1;
                                }
                                Err(_) => break,
                            }
                        }
                        if let Some((mm, anl, k)) = ok_prefix {
                            if mm.len() >= 2 {
                                let orig: i64 = mm.iter().map(|x| cost(x.lits.len(), x.cc)).sum();
                                let neu = cost(k, false) + 2 * (mm.len() as i64 - 1);
                                let sav = orig - neu;
                                if sav > 0 && best.as_ref().map_or(true, |b| sav > b.4) {
                                    best = Some((s, mm, anl, k, sav));
                                }
                            }
                        }
                    }
                    if let Some((s, mem, anl, k, sav)) = best {
                        emit_group(&s, &mem, &anl, k, &mut out);
                        n_g += 1;
                        n_m += mem.len() as u64;
                        n_core += mem.iter().filter(|x| x.lits.len() != k).count() as u64;
                        s_e2 += sav;
                        i += mem.len();
                        continue;
                    }
                }
                match &a.orig {
                    Some(g) if a.cx.is_empty() => out.push(*g),
                    _ => emit_plain(a, &mut out),
                }
                i += 1;
            }
        }
    }
    eprintln!("MERGE E2: groups {n_g} covering {n_m} macros ({n_core} core members), expected T saved per F pass {s_e2}");
    out
}
