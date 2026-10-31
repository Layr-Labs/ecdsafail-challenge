//! Census cuts: Toffolis whose replaced control pattern occurred on no correct shot of a random-input census, applied by op index on
//! the stream after the row cuts. Row line: `site kind c2 c1 t cc action`, kind ccx|ccz, cc the op's c_condition id or
//! `-`, action `del` (the AND never fires), `cx:w` (the AND equals control w) or `cz:a,b` (the CCZ's three-way AND
//! equals the AND of a and b). The op at `site` is asserted (kind, wires, condition); replacements keep its condition.
//! Block line: `B push pop bit z neg`: the PUSH(bit) .. POP block at [push, pop] restores every wire it touches and
//! flips the phase by the parity of the wires `z` (`w1,w2,..` or `-`) plus `neg` (0|1); it becomes Z gates (and a Neg)
//! under `bit`. Edits apply in descending order and may not overlap, so every index refers to the unedited stream.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};
use super::rebind;

/// Expected executed Toffoli of a gate list: each CCX / CCZ weighted 2^-k for the k classical conditions it runs under.
pub fn static_t(ops: &[Op]) -> f64 {
    let (mut d, mut w) = (0i32, 0.0);
    for o in ops {
        match o.kind {
            K::PushCondition => d += 1,
            K::PopCondition => d -= 1,
            K::CCX | K::CCZ => w += 0.5f64.powi(d + (o.c_condition != NO_BIT) as i32),
            _ => {}
        }
    }
    w
}

pub fn rows() -> Vec<(usize, Vec<&'static str>)> {
    include_str!("census_cut_data.txt").lines()
        .map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            let (n, at) = if f[0] == "B" { (6, 1) } else { (7, 0) };
            assert!(f.len() == n, "census_cut: bad line {l:?}");
            (f[at].parse().unwrap(), f)
        })
        .collect()
}

pub fn run(ops: Vec<Op>) -> Vec<Op> {
    let rows = rows();
    let ops = if TEST_SHIFT { test_shift(ops, &rows) } else { ops };
    let rows = anchor_rows(&ops, rows);
    run_rows(ops, rows)
}

// ---- Portable rows: each row is bound by local content, not by its index. ----
//
// `census_cut_anchors.txt` holds one line per row, `A site kl pl fl kr pr fr`: the left window (the kl ops before the
// target plus the target) and the right window (the target plus the kr ops after it) of the stream the row was made
// on, as rebind's rolling hash `pl`/`pr` and fingerprint `fl`/`fr`. Each k is twice the smallest power of two (>= 8)
// that made that side unique in that stream. A row with no anchor line applies at its index (asserted) and prints its
// anchor line ("CCA ..."), so new rows from a census on the current stream bind themselves on their first build.
//
// A row applies at p only on an exact match: both sides' unique hits agree; or one side is unique and the other has no
// hit or also hits p; or the two sides' hit sets meet in exactly one p; or (ambiguous) exactly one hit of either side
// lies within LOCAL ops of the row's site plus the median shift of the rows already placed. Then the target op itself
// must still be the row's op (kind, wires, condition), and no two rows may land on one op. Any other row is missed:
// skipped and listed, never applied.
const ANCHORS: &str = include_str!("census_cut_anchors.txt");
const LOCAL: usize = 1 << 16;

/// Test hook (false = this gate list byte for byte): X;X pairs (identities, no Toffoli) inserted before the census rows at
/// several positions: before every row, between rows, inside the left window of one row and inside the right window of
/// another, so that every row moves and two rows lose one side each.
pub(super) const TEST_SHIFT: bool = false;
fn test_shift(mut ops: Vec<Op>, rows: &[(usize, Vec<&str>)]) -> Vec<Op> {
    let mut s: Vec<usize> = rows.iter().map(|r| r.0).collect();
    s.sort_unstable();
    let n = s.len();
    // positions in the unedited stream, applied in descending order so each names the same op
    let mut at = vec![1000usize, (s[n / 2] + s[n / 2 + 1]) / 2, s[n / 3] - 3, s[2 * n / 3] + 2, (s[n - 1] + ops.len()) / 2];
    at.sort_unstable();
    for &p in at.iter().rev() {
        let mut x = Op::empty();
        x.kind = K::X;
        x.q_target = QubitId(0);
        ops.splice(p..p, [x, x]);
    }
    eprintln!("CENSUS_ANCHOR test shift: X;X pairs at {at:?}");
    ops
}

fn side_hits(h: &[u64], wants: &[(usize, u64, u64)]) -> Vec<Vec<usize>> {
    // wants[i] = (len, poly, fp); returns the start positions of each want's exact hits
    let mut out = vec![Vec::new(); wants.len()];
    let mut lens: Vec<usize> = wants.iter().map(|w| w.0).collect();
    lens.sort_unstable();
    lens.dedup();
    for len in lens {
        let idx: Vec<usize> = (0..wants.len()).filter(|&i| wants[i].0 == len).collect();
        let want = rebind::want_of(idx.iter().map(|&i| wants[i].1));
        for (p, v) in rebind::scan(h, len, &want) {
            let f = rebind::fp(&h[p..p + len]);
            for &i in &idx {
                if wants[i].1 == v && wants[i].2 == f {
                    out[i].push(p);
                }
            }
        }
    }
    out
}

fn gen_side(h: &[u64], sites: &[usize], left: bool) -> Vec<(usize, u64, u64)> {
    let win = |s: usize, k: usize| -> Option<(usize, usize)> {
        if left { (s >= k).then(|| (s - k, s + 1)) } else { (s + k < h.len()).then(|| (s, s + k + 1)) }
    };
    let mut k_of = vec![0usize; sites.len()];
    let mut k = 8usize;
    while k_of.iter().any(|&x| x == 0) {
        assert!(k <= 1 << 20, "census_cut: no unique window");
        let open: Vec<usize> = (0..sites.len()).filter(|&i| k_of[i] == 0).collect();
        let wants: Vec<(usize, u64, u64)> = open.iter().map(|&i| match win(sites[i], k) {
            Some((lo, hi)) => (hi - lo, rebind::poly(&h[lo..hi]), rebind::fp(&h[lo..hi])),
            None => (0, 0, 0),
        }).collect();
        let hits = side_hits(h, &wants);
        for (j, &i) in open.iter().enumerate() {
            if wants[j].0 > 0 && hits[j].len() == 1 { k_of[i] = k; }
        }
        k *= 2;
    }
    (0..sites.len()).map(|i| {
        let k = if win(sites[i], 2 * k_of[i]).is_some() { 2 * k_of[i] } else { k_of[i] };
        let (lo, hi) = win(sites[i], k).unwrap();
        (k, rebind::poly(&h[lo..hi]), rebind::fp(&h[lo..hi]))
    }).collect()
}

fn row_matches(o: &Op, f: &[&str]) -> bool {
    let w = |s: &str| -> u64 { s.parse().unwrap() };
    let kind = if f[1] == "ccx" { K::CCX } else { K::CCZ };
    let cc = if o.c_condition == NO_BIT { "-".to_string() } else { o.c_condition.0.to_string() };
    o.kind == kind && o.q_control2.0 == w(f[2]) && o.q_control1.0 == w(f[3]) && o.q_target.0 == w(f[4]) && cc == f[5]
}

/// Map each row to its op in `ops` by its anchor; rows without an anchor keep their index and print their anchor.
pub fn anchor_rows<'a>(ops: &[Op], rows: Vec<(usize, Vec<&'a str>)>) -> Vec<(usize, Vec<&'a str>)> {
    let mut anc: std::collections::HashMap<usize, [u64; 6]> = std::collections::HashMap::new();
    for l in ANCHORS.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let f: Vec<u64> = l.split_whitespace().skip(1).map(|x| x.parse().unwrap()).collect();
        assert!(l.starts_with("A ") && f.len() == 7, "census_cut: bad anchor line {l:?}");
        anc.insert(f[0] as usize, [f[1], f[2], f[3], f[4], f[5], f[6]]);
    }
    assert!(rows.iter().all(|r| r.1[0] != "B"), "census_cut: block rows have no anchors");
    let h = rebind::mixes(ops);
    let (bound, fresh): (Vec<_>, Vec<_>) = rows.into_iter().partition(|r| anc.contains_key(&r.0));
    let mut out: Vec<(usize, Vec<&str>)> = Vec::new();
    // rows without an anchor: made on this stream; apply at the index (asserted in run_rows) and print the anchor
    if !fresh.is_empty() {
        let sites: Vec<usize> = fresh.iter().map(|r| r.0).collect();
        let (l, r) = (gen_side(&h, &sites, true), gen_side(&h, &sites, false));
        for i in 0..sites.len() {
            eprintln!("CCA A {} {} {} {} {} {} {}", sites[i], l[i].0, l[i].1, l[i].2, r[i].0, r[i].1, r[i].2);
        }
    }
    // rows with an anchor
    let mut wants = Vec::new();
    for r in &bound {
        let a = anc[&r.0];
        wants.push((a[0] as usize + 1, a[1], a[2]));
        wants.push((a[3] as usize + 1, a[4], a[5]));
    }
    let hits = side_hits(&h, &wants);
    let (mut n_exact, mut n_moved, mut n_local) = (0usize, 0usize, 0usize);
    let mut placed: Vec<Option<usize>> = vec![None; bound.len()];
    let mut why: Vec<&str> = vec![""; bound.len()];
    let mut ambiguous = Vec::new();
    for (i, r) in bound.iter().enumerate() {
        let kl = anc[&r.0][0] as usize;
        let lp: Vec<usize> = hits[2 * i].iter().map(|&p| p + kl).collect();
        let rp: Vec<usize> = hits[2 * i + 1].clone();
        let both: Vec<usize> = lp.iter().copied().filter(|p| rp.contains(p)).collect();
        placed[i] = if lp.len() == 1 && (rp.is_empty() || rp.contains(&lp[0])) {
            Some(lp[0])
        } else if rp.len() == 1 && (lp.is_empty() || lp.contains(&rp[0])) {
            Some(rp[0])
        } else if both.len() == 1 {
            Some(both[0])
        } else if lp.is_empty() && rp.is_empty() {
            why[i] = "no-context";
            None
        } else if lp.len() == 1 && rp.len() == 1 {
            why[i] = "sides-disagree";
            None
        } else {
            ambiguous.push((i, lp.into_iter().chain(rp).collect::<Vec<usize>>()));
            None
        };
    }
    let mut shifts: Vec<isize> = (0..bound.len()).filter_map(|i| placed[i].map(|p| p as isize - bound[i].0 as isize)).collect();
    shifts.sort_unstable();
    let med = if shifts.is_empty() { 0 } else { shifts[shifts.len() / 2] };
    for (i, mut c) in ambiguous {
        let e = bound[i].0 as isize + med;
        c.sort_unstable();
        c.dedup();
        let near: Vec<usize> = c.into_iter().filter(|&p| (p as isize - e).unsigned_abs() <= LOCAL).collect();
        if near.len() == 1 { placed[i] = Some(near[0]); n_local += 1; } else { why[i] = "ambiguous"; }
    }
    for i in 0..bound.len() {
        if let Some(p) = placed[i] {
            if p >= ops.len() || !row_matches(&ops[p], &bound[i].1) { placed[i] = None; why[i] = "op-differs"; }
        }
    }
    let mut seen: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    for p in placed.iter().flatten() { *seen.entry(*p).or_default() += 1; }
    for i in 0..bound.len() {
        if let Some(p) = placed[i] { if seen[&p] > 1 { placed[i] = None; why[i] = "collision"; } }
    }
    let mut n_miss = 0usize;
    for (i, r) in bound.into_iter().enumerate() {
        match placed[i] {
            Some(p) => { if p == r.0 { n_exact += 1 } else { n_moved += 1 } out.push((p, r.1)); }
            None => { n_miss += 1; eprintln!("CENSUS_ANCHOR miss site={} reason={}", r.0, why[i]); }
        }
    }
    eprintln!("CENSUS_ANCHOR rows={} anchored={} matched={} (in place {n_exact}, moved {n_moved}, local {n_local}) missed={n_miss} median_shift={med} fresh={}",
        out.len() + n_miss + fresh.len(), out.len() + n_miss, out.len(), fresh.len());
    out.extend(fresh);
    out
}

pub fn run_rows(mut ops: Vec<Op>, mut rows: Vec<(usize, Vec<&str>)>) -> Vec<Op> {
    let w0 = static_t(&ops);
    rows.sort_by(|a, b| b.0.cmp(&a.0));
    let w = |s: &str| -> u64 { s.parse().unwrap() };
    let (mut n_del, mut n_red, mut n_blk) = (0usize, 0usize, 0usize);
    let mut floor = usize::MAX;
    for (site, f) in &rows {
        let mut x = Op::empty();
        if f[0] == "B" {
            let (push, pop, bit) = (*site, w(f[2]) as usize, w(f[3]));
            assert!(pop < floor, "census_cut: edits overlap at {push}");
            floor = push;
            assert!(ops[push].kind == K::PushCondition && ops[push].c_condition.0 == bit && ops[pop].kind == K::PopCondition,
                "census_cut: block at {push} does not match the stream");
            let mut d = 0i64;
            for o in &ops[push..=pop] { if o.kind == K::PushCondition { d += 1; } if o.kind == K::PopCondition { d -= 1; assert!(d > 0 || std::ptr::eq(o, &ops[pop]), "census_cut: block {push} closes early"); } }
            assert!(d == 0, "census_cut: block {push} unbalanced");
            x.c_condition = ops[push].c_condition;
            let mut rep = Vec::new();
            if f[4] != "-" { for z in f[4].split(',') { let mut y = x; y.kind = K::Z; y.q_target = QubitId(w(z)); y.validate(); rep.push(y); } }
            if f[5] == "1" { let mut y = x; y.kind = K::Neg; y.validate(); rep.push(y); }
            n_blk += 1;
            ops.splice(push..=pop, rep);
            continue;
        }
        assert!(*site < floor, "census_cut: edits overlap at {site}");
        floor = *site;
        let o = ops[*site];
        let kind = if f[1] == "ccx" { K::CCX } else { K::CCZ };
        let cc = if o.c_condition == NO_BIT { "-".to_string() } else { o.c_condition.0.to_string() };
        assert!(o.kind == kind && o.q_control2.0 == w(f[2]) && o.q_control1.0 == w(f[3]) && o.q_target.0 == w(f[4]) && cc == f[5],
            "census_cut: row at {site} does not match the stream");
        x.c_condition = o.c_condition;
        let rep = match f[6].split_once(':') {
            None if f[6] == "del" => { n_del += 1; vec![] }
            Some(("cx", a)) if kind == K::CCX => { x.kind = K::CX; x.q_control1 = QubitId(w(a)); x.q_target = o.q_target; vec![x] }
            Some(("cz", ab)) if kind == K::CCZ => {
                let (a, b) = ab.split_once(',').unwrap();
                x.kind = K::CZ; x.q_control1 = QubitId(w(a)); x.q_target = QubitId(w(b)); vec![x]
            }
            _ => panic!("census_cut: bad action {:?}", f[6]),
        };
        if !rep.is_empty() { n_red += 1; for r in &rep { r.validate(); } }
        ops.splice(*site..*site + 1, rep);
    }
    let w1 = static_t(&ops);
    eprintln!("CENSUS_CUT rows={} deleted={} reduced={} blocks={} static expected Toffoli {w0:.1} -> {w1:.1} ({:.1})", rows.len(), n_del, n_red, n_blk, w1 - w0);
    ops
}
