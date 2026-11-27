//! Build-time partial evaluation of the shift counter ("unrolling") of the four big blocks, applied to the item's own records.
//! Port of the unroll worker's gen3b.py (one more bit on a block that already has two unrolled bits: item 10, the inner
//! walks of items 4 / 12), plain.py (two bits on a plain inverter run: item 2, the reverse walks of items 4 / 12) and the
//! run_rev.py / run_plain.py glue.  Input: the raw records of an item (generator wire numbering, as decoded from blocks.girs);
//! output: the replacement records.  No data is shipped.  All numbers below are record positions of the raw items.
pub type Row = [u16; 4];
const NO: u16 = u16::MAX;
#[inline] fn x(l: u16) -> Row { [6, l, NO, NO] }
#[inline] fn ccx(a: u16, b: u16, t: u16) -> Row { [13, a, b, t] }
#[inline] fn cx(a: u16, b: u16) -> Row { [8, a, b, NO] }
fn mcx(c: &[u16], t: u16, anc: &[u16], out: &mut Vec<Row>) {
    let k = c.len();
    if k == 1 { out.push(cx(c[0], t)); return; }
    if k == 2 { out.push(ccx(c[0], c[1], t)); return; }
    let a = &anc[..k - 2];
    let mut chain: Vec<Row> = vec![[0; 4]; k]; // chain[i] = A[i], i in 1..=k-2
    chain[1] = ccx(c[0], c[1], a[0]);
    for i in 2..k - 1 { chain[i] = ccx(c[i], a[i - 2], a[i - 1]); }
    let fg = ccx(c[k - 1], a[k - 3], t);
    for i in 1..=k - 2 { out.push(chain[i]); } out.push(fg);
    for i in (1..=k - 2).rev() { out.push(chain[i]); }
    for i in 2..=k - 2 { out.push(chain[i]); } out.push(fg);
    for i in (2..=k - 2).rev() { out.push(chain[i]); }
}
fn swap(f: u16, a: u16, b: u16, out: &mut Vec<Row>) { out.push(cx(a, b)); out.push(ccx(f, b, a)); out.push(cx(a, b)); }
fn rot(f: u16, a: &[u16], s: i64, out: &mut Vec<Row>) {
    let n = a.len() as i64; let s = s.rem_euclid(n) as usize; let n = n as usize; if s == 0 { return; }
    let mut seen = vec![false; n];
    for k in 0..n { if seen[k] { continue; } seen[k] = true; let mut j = (k + s) % n;
        while j != k { swap(f, a[k], a[j], out); seen[j] = true; j = (j + s) % n; } }
}
fn sl(m: &[Row], a: usize, b: usize) -> &[Row] { if a < b { &m[a..b] } else { &[] } }
/// rows of `m` with every X on a lane of `tags` removed
fn strip_tags(seg: &[Row], tags: &[u16], out: &mut Vec<Row>) { for r in seg { if !(r[0] == 6 && tags.contains(&r[1])) { out.push(*r); } } }
fn apply_edits(m: &[Row], mut edits: Vec<(usize, usize, Option<Vec<Row>>)>) -> Vec<Row> {
    edits.sort_by_key(|e| e.0);
    for w in edits.windows(2) { assert!(w[0].1 <= w[1].0, "edit overlap"); }
    let mut out: Vec<Row> = Vec::with_capacity(m.len() + m.len() / 3); let mut pos = 0;
    let dbg = Err::<String, ()>(()).is_ok(); let mut ik = 0usize;
    for (a, e, new) in edits { out.extend_from_slice(&m[pos..a]); if let Some(n) = new { if dbg && n.len() > 3000 { eprintln!("ITER {} raw {}..{} new {}..{}", ik, a, e, out.len(), out.len() + n.len()); ik += 1; } out.extend_from_slice(&n); } pos = e; }
    out.extend_from_slice(&m[pos..]); out
}
/// the 6-record fire-controlled swap gadgets CX(a,b) CCX(fire,c,anc0) CX(a,b) CX(a,b) CCX CX(a,b), found by their CCX records
fn gadget_units(m: &[Row], lo: usize, hi: usize, pred: impl Fn(&Row) -> bool, prot: Option<&[bool]>) -> Vec<(usize, usize)> {
    let mut cs: Vec<usize> = Vec::new();
    for i in lo..hi { if pred(&m[i]) && !prot.map_or(false, |p| p[i - lo]) { cs.push(i); } }
    let set: std::collections::HashSet<usize> = cs.iter().copied().collect();
    let mut units = Vec::new(); let mut nstart = 0;
    for &v in &cs { if set.contains(&(v + 2)) && !(v >= 2 && set.contains(&(v - 2))) {
        let st = if m[v - 1][0] == 8 { v - 1 } else { v - 2 };
        assert!(m[st][0] == 8 && m[st + 5][0] == 8 && m[st][1] == m[st + 5][1] && m[st][2] == m[st + 5][2], "gadget unit at {}", v); units.push((st, st + 6)); nstart += 1; } }
    if 2 * nstart != cs.len() { let ps: Vec<usize> = cs.iter().copied().filter(|&v| !(set.contains(&(v + 2)) || (v >= 2 && set.contains(&(v - 2))))).take(8).collect(); eprintln!("PAIRING cs {} nstart {} lo {} hi {} unpaired {:?}", cs.len(), nstart, lo, hi, ps); for &p in ps.iter().take(2) { for q in p.saturating_sub(4)..p + 6 { eprintln!("  {} {:?}", q, m[q]); } } }
    assert!(2 * nstart == cs.len(), "gadget pairing"); units
}

// ---------------------------------------------------------------------------------------------------------------- gen3b
pub struct G3 { pub f: u16, pub fire: u16, pub tst: u16, pub tags: Vec<u16>, pub anc: Vec<u16>, pub lo: usize, pub hi: usize, pub b0: usize, pub tagbit0: usize }
struct Fl { kind: u8, sp: usize, st: usize, en: usize } // 'c' = 0, 'u' = 1
fn fladders(evs: &[usize]) -> Vec<Fl> {
    let mut out = vec![Fl { kind: 0, sp: 0, st: evs[0], en: evs[0] + 1 }];
    if evs.len() > 1 { out.push(Fl { kind: 1, sp: 0, st: evs[1], en: evs[1] + 1 }); }
    let (mut q, mut sp) = (2usize, 1usize);
    while q + 1 < evs.len() {
        for kind in 0..2u8 { if q + 1 >= evs.len() { break; } let e1 = evs[q]; let st = e1 - sp - sp; let en = st + sp + 4 * sp + sp; out.push(Fl { kind, sp, st, en }); q += 2; }
        sp += 1; }
    out
}
struct Lad { st: usize, en: usize, g: u32 }
fn ladders3(m: &[Row], c: &G3) -> Vec<Lad> {
    let t = &c.tags; let k = t.len() + 1; let chain = 4 * (k - 2); let alast = c.anc[k - 3];
    let mut ev: Vec<usize> = Vec::new();
    for i in c.lo..c.hi { let r = &m[i]; if r[0] == 13 && r[1] == *t.last().unwrap() && r[2] == alast && r[3] == c.tst { ev.push(i); } }
    let mut out = Vec::new();
    for &f1 in ev.iter().step_by(2) {
        let mut a = f1 - (k - 2);
        if !(m[a][0] == 13 && m[a][3] == c.anc[0] && m[a][1] == c.f) { a = f1 - (k - 3); }
        let e = a + chain; let mut st = a; while m[st - 1][0] == 6 && t.contains(&m[st - 1][1]) { st -= 1; }
        let mut en = e; while m[en][0] == 6 && t.contains(&m[en][1]) { en += 1; }
        let xs: Vec<u16> = (st..a).map(|q| m[q][1]).collect();
        let g = t.iter().enumerate().map(|(j, tt)| if xs.contains(tt) { 0 } else { 1u32 << j }).sum();
        out.push(Lad { st, en, g }); }
    out
}
/// one more unrolled bit (b = 3) on a block that has b0 = 2 unrolled bits
pub fn gen3b(m: &[Row], c: &G3, b: usize) -> Vec<Row> {
    let (f, fire, tst) = (c.f, c.fire, c.tst); let anc = &c.anc; let t = &c.tags;
    // landmarks: records touching F: CCX target, CX target, X
    let idx: Vec<usize> = (c.lo..c.hi).filter(|&i| { let r = &m[i]; (r[0] == 13 && r[3] == f) || (r[0] == 8 && r[2] == f) || (r[0] == 6 && r[1] == f) }).collect();
    let st: Vec<usize> = (0..idx.len()).filter(|&q| { let r = &m[idx[q]]; r[0] == 13 && r[1] == fire }).collect();
    let mut bounds: Vec<usize> = (0..st.len()).step_by(2).map(|i| st[i]).collect(); bounds.push(idx.len());
    let its: Vec<&[usize]> = (0..bounds.len() - 1).map(|i| &idx[bounds[i]..bounds[i + 1]]).collect();
    let l = ladders3(m, c); let lst: Vec<usize> = l.iter().map(|q| q.st).collect();
    let ni = its.len();
    let mut ord = vec![0u16; ni]; for k in 0..ni { ord[ni - 1 - k] = m[its[k][0]][2]; }
    let b0 = c.b0;
    let strip = |st: usize, en: usize| -> (Vec<Row>, Vec<(usize, u32)>) {
        let mut body: Vec<Row> = Vec::new(); let mut slots = Vec::new(); let mut pos = st;
        let mut i = lst.partition_point(|&v| v < st);
        while i < l.len() && l[i].st < en { strip_tags(sl(m, pos, l[i].st), t, &mut body); slots.push((body.len(), l[i].g)); pos = l[i].en; i += 1; }
        strip_tags(sl(m, pos, en), t, &mut body); (body, slots) };
    // per iteration copy intervals
    struct D { m: usize, nc: usize, fl: Vec<Fl>, cs: Vec<(usize, usize)> }
    let mut data: Vec<D> = Vec::with_capacity(ni);
    for k in 0..ni { let mm = ni - k; let fl = fladders(its[k]); let nc = (1usize << b0).min(mm); let mut cs = Vec::new();
        for sp in 0..nc { let cc = fl.iter().find(|q| q.kind == 0 && q.sp == sp).unwrap(); let u = fl.iter().find(|q| q.kind == 1 && q.sp == sp); cs.push((cc.en, u.expect("copy end").st)); }
        data.push(D { m: mm, nc, fl, cs }); }
    // tail register A* from copy 1 of the first iteration
    let ast: Vec<u16> = { let d = &data[0]; let (b0r, _) = strip(d.cs[0].0, d.cs[0].1); let (b1r, _) = strip(d.cs[1].0, d.cs[1].1); let t1 = &b1r[b0r.len()..];
        let piv = t1[0][1]; let mut ys: Vec<u16> = t1.iter().filter(|r| r[0] == 8).map(|r| r[2]).collect(); ys = ys.iter().step_by(2).copied().collect();
        let mut a = vec![piv]; a.extend(ys.iter().rev()); a };
    let mut edits: Vec<(usize, usize, Option<Vec<Row>>)> = Vec::new();
    let dt: Vec<u16> = t[..b - b0].to_vec(); let tags: Vec<u16> = t[b - b0..].to_vec();
    for k in 0..ni {
        let d = &data[k]; let mm = d.m; let (body0, slots0) = strip(d.cs[0].0, d.cs[0].1);
        let mut slots: Vec<Vec<(usize, u32)>> = vec![slots0]; for sp in 1..d.nc { slots.push(strip(d.cs[sp].0, d.cs[sp].1).1); }
        let ncs = (1usize << b).min(mm); let mut out: Vec<Row> = Vec::new();
        let fl = |sp: usize, out: &mut Vec<Row>| { if sp == 0 { out.push(ccx(fire, ord[mm - 1], f)); return; }
            let bb: Vec<u16> = (0..=sp).map(|j| ord[mm - 1 - j]).collect();
            for j in (0..sp).rev() { out.push(x(bb[j])); }
            let mut ctr = vec![fire]; for j in (0..=sp).rev() { ctr.push(bb[j]); } mcx(&ctr, f, anc, out);
            for j in (0..sp).rev() { out.push(x(bb[j])); } };
        for sp in 0..ncs {
            fl(sp, &mut out);
            let s4 = sp % (1 << b0); let mut keep: Vec<(usize, u32)> = Vec::new();
            for &(off, g) in &slots[s4] { let v = (g << b0) | s4 as u32; if v % (1 << b) == sp as u32 { keep.push((off, v >> b)); } }
            let mut mp: Vec<u16> = (0..1024u16).collect(); for p in 0..mm { mp[ord[p] as usize] = ord[(p + mm - sp % mm) % mm]; }
            let bd: Vec<Row> = body0.iter().map(|r| { let mut q = *r; for col in 1..4 { if q[col] != NO { q[col] = mp[q[col] as usize]; } } q }).collect();
            let mut last = 0;
            for (off, gg) in keep { out.extend_from_slice(&bd[last..off]);
                for (jj, tt) in tags.iter().enumerate() { if (gg >> jj) & 1 == 0 { out.push(x(*tt)); } }
                let mut ctr = vec![f]; ctr.extend(tags.iter()); mcx(&ctr, tst, anc, &mut out);
                for (jj, tt) in tags.iter().enumerate() { if (gg >> jj) & 1 == 0 { out.push(x(*tt)); } } last = off; }
            out.extend_from_slice(&bd[last..]);
            for jj in 0..b { if (sp >> jj) & 1 == 1 { rot(f, &ast, -(1i64 << jj), &mut out); } }
            fl(sp, &mut out); }
        edits.push((d.fl[0].st, d.fl.last().unwrap().en, Some(out))); }
    // deletions of the tag gadgets of the newly specialised tag(s) outside the copy areas
    let (lo, hi) = (c.lo, c.hi);
    let units = gadget_units(m, lo, hi, |r| r[0] == 13 && r[1] == fire && dt.contains(&r[2]) && r[3] == anc[0], None);
    for u in units { edits.push((u.0, u.1, None)); }
    let isanc = |r: &Row| r[0] == 13 && anc.iter().take(12).any(|a| *a == r[3]);
    let zf: Vec<usize> = (lo..hi).filter(|&i| m[i][0] == 13 && dt.contains(&m[i][3])).collect();
    let mut i = 0;
    while i < zf.len() {
        let f1 = zf[i]; let tgt = m[f1][3]; let nx = 1usize << (c.tagbit0 + t.iter().position(|q| *q == tgt).unwrap());
        let mut a = f1; while isanc(&m[a - 1]) { a -= 1; } let xa = a - nx;
        assert!((xa..a).all(|q| m[q][0] == 6), "zer prefix at {} tgt {} a {} nx {}: {:?}", f1, tgt, a, nx, &m[a - 6..a + 2]);
        let f2; if i + 1 < zf.len() && zf[i + 1] - f1 <= 16 && m[zf[i + 1]][3] == tgt { f2 = zf[i + 1]; i += 2; } else { f2 = f1; i += 1; }
        let mut e = f2 + 1; while isanc(&m[e]) { e += 1; } let xe = e + nx;
        assert!((e..xe).all(|q| m[q][0] == 6), "zer suffix");
        edits.push((xa, xe, None)); }
    apply_edits(m, edits)
}

// ---------------------------------------------------------------------------------------------------------------- plain
pub struct Pl { pub n: usize, pub fire: u16, pub tst: u16, pub tags: Vec<u16>, pub anc: Vec<u16>, pub ord: Vec<u16>, pub ast: Vec<u16> }
struct PLad { st: usize, en: usize, v: u32 }
fn find_ladders(m: &[Row], c: &Pl, lo: usize, hi: usize) -> Vec<PLad> {
    let t = &c.tags; let k = t.len() + 1; let chain = 4 * (k - 2); let alast = c.anc[k - 3];
    let ev: Vec<usize> = (lo..hi).filter(|&i| { let r = &m[i]; r[0] == 13 && r[1] == *t.last().unwrap() && r[2] == alast && r[3] == c.tst }).collect();
    let mut out = Vec::new();
    for &f1 in ev.iter().step_by(2) {
        let mut a = f1 - (k - 2);
        if !(m[a][0] == 13 && m[a][3] == c.anc[0] && m[a][1] == c.fire) { a = f1 - (k - 3); }
        let e = a + chain; assert!(m[e - 1][0] == 13);
        let mut st = a; while m[st - 1][0] == 6 && t.contains(&m[st - 1][1]) { st -= 1; }
        let mut en = e; while m[en][0] == 6 && t.contains(&m[en][1]) { en += 1; }
        let xs: Vec<u16> = (st..a).map(|q| m[q][1]).collect();
        let v = t.iter().enumerate().map(|(j, tt)| if xs.contains(tt) { 0 } else { 1u32 << j }).sum();
        out.push(PLad { st, en, v }); }
    out
}
/// b unrolled bits on a plain inverter run m[lo..hi]; returns the edit list applied to m
pub fn plain(m: &[Row], c: &Pl, lo: usize, hi: usize, b: usize) -> Vec<Row> {
    let (fire, tst, anc, ord, ast) = (c.fire, c.tst, &c.anc, &c.ord, &c.ast); let t = &c.tags; let f = t[0]; let d: Vec<u16> = t[..b].to_vec();
    let l = find_ladders(m, c, lo, hi); let nl = l.len();
    let mut groups: Vec<&[PLad]> = Vec::new(); let mut q = 0;
    for k in 0..c.n { let mm = c.n - k; let n = 2 * 32.min(mm); if q + n > nl { break; } groups.push(&l[q..q + n]); q += n; }
    assert!(q == nl, "ladder groups {} {}", q, nl);
    let mut prot = vec![false; hi - lo]; for p in &l { for i in p.st..p.en { prot[i - lo] = true; } }
    let mut dels: Vec<(usize, usize)> = gadget_units(m, lo, hi, |r| r[0] == 13 && r[1] == fire && d.contains(&r[2]) && r[3] == anc[0], Some(&prot));
    let isanc = |r: &Row| r[0] == 13 && anc.iter().take(12).any(|a| *a == r[3]);
    let zf: Vec<usize> = (lo..hi).filter(|&i| m[i][0] == 13 && d.contains(&m[i][3]) && !prot[i - lo]).collect();
    let mut i = 0;
    while i < zf.len() {
        let f1 = zf[i]; let tgt = m[f1][3]; let mut a = f1; while isanc(&m[a - 1]) { a -= 1; }
        let nx = 1usize << t.iter().position(|q| *q == tgt).unwrap(); let xa = a - nx;
        assert!((xa..a).all(|q| m[q][0] == 6), "zer prefix");
        let f2; if i + 1 < zf.len() && zf[i + 1] - f1 <= 16 && m[zf[i + 1]][3] == tgt { f2 = zf[i + 1]; i += 2; } else { f2 = f1; i += 1; }
        let mut e = f2 + 1; while isanc(&m[e]) { e += 1; } let xe = e + nx;
        assert!((e..xe).all(|q| m[q][0] == 6), "zer suffix");
        dels.push((xa, xe)); }
    dels.sort(); let ds: Vec<usize> = dels.iter().map(|u| u.0).collect();
    let tagsb: Vec<u16> = t[b..].to_vec();
    let mut edits: Vec<(usize, usize, Option<Vec<Row>>)> = Vec::new(); let mut extra: Vec<(usize, usize)> = Vec::new();
    for (k, lk) in groups.iter().enumerate() {
        let mm = c.n - k;
        let i = ds.partition_point(|&v| v < lk[0].st); let mut wstart = if i > 0 { dels[i - 1].1 } else { panic!("no wstart") };
        if mm == 1 { let mut p = wstart; while !(m[p][0] == 8 && m[p][1] == fire && m[p][2] == ord[mm - 1]) { p += 1; } wstart = p; }
        let j = ds.partition_point(|&v| v <= lk.last().unwrap().en); let wend = if j < dels.len() { dels[j].0 } else { panic!("no wend") };
        // stripped body of W with the ladders cut out
        let mut body: Vec<Row> = Vec::new(); let mut slots: Vec<(usize, u32)> = Vec::new(); let mut pos = wstart;
        for p in lk.iter() { strip_tags(sl(m, pos, p.st), t, &mut body); slots.push((body.len(), p.v)); pos = p.en; }
        strip_tags(sl(m, pos, wend), t, &mut body);
        for r in body.iter_mut() { for col in 1..4 { if r[col] == fire { r[col] = f; } } }
        let mut sw: Vec<Row> = Vec::new();
        if k >= 1 {
            let nxt = if k + 1 < groups.len() { groups[k + 1][0].st } else { usize::MAX };
            let cand = dels.iter().find(|u| u.0 >= wend && u.0 < nxt && m[u.0][0] == 8 && m[u.0][1] == ast[0] && m[u.0][2] == *ast.last().unwrap());
            let st = cand.expect("no R rot run").0;
            if st > wend {
                for qi in 0..k { let (a_, b_, c_) = (m[st - 3 * k + 3 * qi], m[st - 3 * k + 3 * qi + 1], m[st - 3 * k + 3 * qi + 2]);
                    assert!(a_[0] == 8 && b_[0] == 13 && b_[1] == fire && c_[0] == 8, "fire swaps"); }
                sw = m[st - 3 * k..st].to_vec(); for r in sw.iter_mut() { for col in 1..4 { if r[col] == fire { r[col] = f; } } }
                extra.push((st - 3 * k, st)); } }
        body.extend_from_slice(&sw);
        let ncs = (1usize << b).min(mm); let mut out: Vec<Row> = Vec::new();
        let fl = |sp: usize, out: &mut Vec<Row>| { if sp == 0 { out.push(ccx(fire, ord[mm - 1], f)); return; }
            let bb: Vec<u16> = (0..=sp).map(|jj| ord[mm - 1 - jj]).collect();
            for jj in (0..sp).rev() { out.push(x(bb[jj])); }
            let mut ctr = vec![fire]; for jj in (0..=sp).rev() { ctr.push(bb[jj]); } mcx(&ctr, f, anc, out);
            for jj in (0..sp).rev() { out.push(x(bb[jj])); } };
        for sp in 0..ncs {
            fl(sp, &mut out);
            let keep: Vec<(usize, u32)> = slots.iter().filter(|s| s.1 % (1 << b) == sp as u32).map(|s| (s.0, s.1 >> b)).collect();
            let mut mp: Vec<u16> = (0..1024u16).collect(); for p in 0..mm { mp[ord[p] as usize] = ord[(p + mm - sp % mm) % mm]; }
            let bd: Vec<Row> = body.iter().map(|r| { let mut q = *r; for col in 1..4 { if q[col] != NO { q[col] = mp[q[col] as usize]; } } q }).collect();
            let mut last = 0;
            for (off, gg) in keep { out.extend_from_slice(&bd[last..off]);
                for (jj, tt) in tagsb.iter().enumerate() { if (gg >> jj) & 1 == 0 { out.push(x(*tt)); } }
                let mut ctr = vec![f]; ctr.extend(tagsb.iter()); mcx(&ctr, tst, anc, &mut out);
                for (jj, tt) in tagsb.iter().enumerate() { if (gg >> jj) & 1 == 0 { out.push(x(*tt)); } } last = off; }
            out.extend_from_slice(&bd[last..]);
            for jj in 0..b { if (sp >> jj) & 1 == 1 { rot(f, ast, -(1i64 << jj), &mut out); } }
            fl(sp, &mut out); }
        edits.push((wstart, wend, Some(out))); }
    for dd in dels { edits.push((dd.0, dd.1, None)); }
    for dd in extra { edits.push((dd.0, dd.1, None)); }
    apply_edits(m, edits)
}
/// ORD / A* of a run, from the pivots of its rotation runs (run_plain.derive)
pub fn derive(m: &[Row], fire: u16, c0: u16, anc0: u16) -> (Vec<u16>, Vec<u16>) {
    let units = gadget_units_loose(m, fire, c0, anc0);
    let mut runs: Vec<Vec<(usize, u16, u16)>> = Vec::new(); let mut cur = vec![units[0]];
    for u in &units[1..] { if u.0 == cur.last().unwrap().0 + 6 && u.1 == cur.last().unwrap().1 { cur.push(*u); } else { runs.push(std::mem::take(&mut cur)); cur = vec![*u]; } }
    runs.push(cur);
    let asc = runs.iter().find(|r| r.len() > 1 && r[0].2 < r[1].2).expect("ascending run");
    let mut ord = vec![asc[0].1]; ord.extend(asc.iter().map(|u| u.2));
    let rr = runs.iter().find(|r| r[0].1 != ord[0]).expect("R run");
    let mut ast = vec![rr[0].1]; ast.extend(rr.iter().map(|u| u.2).rev()); (ord, ast)
}
fn gadget_units_loose(m: &[Row], fire: u16, c0: u16, anc0: u16) -> Vec<(usize, u16, u16)> {
    let cs: Vec<usize> = (0..m.len()).filter(|&i| m[i][0] == 13 && m[i][1] == fire && m[i][2] == c0 && m[i][3] == anc0).collect();
    let set: std::collections::HashSet<usize> = cs.iter().copied().collect(); let mut u = Vec::new();
    for &v in &cs { if set.contains(&(v + 2)) && !(v >= 2 && set.contains(&(v - 2))) { let st = if m[v - 1][0] == 8 { v - 1 } else { v - 2 }; u.push((st, m[st][1], m[st][2])); } }
    u
}

// ---------------------------------------------------------------------------------------------------------------- the four blocks
fn rng(a: u16, b: u16) -> Vec<u16> { (a..b).collect() }
/// the reverse walk of a divide: reverse the region, two plain bits, reverse back
fn reverse_walk(m: &[Row], lo: usize, hi: usize, n: usize, anc0: u16) -> Vec<Row> {
    let reg: Vec<Row> = m[lo..hi].iter().rev().copied().collect();
    let (ord, ast) = derive(&reg, 637, 626, anc0);
    let c = Pl { n, fire: 637, tst: 633, tags: rng(626, 631), anc: (0..12).map(|i| anc0 + i).collect(), ord, ast };
    let out = plain(&reg, &c, 0, reg.len(), 2);
    let mut full: Vec<Row> = Vec::with_capacity(m.len() + out.len());
    full.extend_from_slice(&m[..lo]); full.extend(out.iter().rev()); full.extend_from_slice(&m[hi..]); full
}
/// ITEM 2 / 4 / 10 / 12 of the tree: the raw records in, the unrolled records out (generator wire numbering)
pub fn unroll_item(item: usize, m: &[Row]) -> Vec<Row> {
    match item {
        10 => gen3b(m, &G3 { f: 631, fire: 634, tst: 635, tags: vec![628, 629, 630], anc: rng(513, 521), lo: 37_913_900, hi: 60_160_000, b0: 2, tagbit0: 2 }, 3),
        104 => gen3b(m, &G3 { f: 631, fire: 634, tst: 635, tags: vec![628, 629, 630], anc: rng(513, 529), lo: 37_913_151, hi: 60_160_000, b0: 2, tagbit0: 2 }, 4),
        2 => { let c = Pl { n: 127, fire: 251, tst: 243, tags: rng(246, 251), anc: rng(0, 8), ord: rng(115, 242), ast: { let mut a = rng(513, 640); a.push(253); a } };
            plain(m, &c, 37_099_000, 44_195_000, 2) }
        // experimental variants (unroll633). ITEM 2: 201 = runs 1,3 b2 + run 2 b2 ; 202 = run 3 b2, run 2 b3, run 1 b2 ; 203 = run 2 b3 only.
        201 | 202 | 203 => { let c = Pl { n: 127, fire: 251, tst: 243, tags: rng(246, 251), anc: rng(0, 8), ord: rng(115, 242), ast: { let mut a = rng(513, 640); a.push(253); a } };
            let b2 = if item == 201 { 2 } else { 3 };
            if item == 203 { return plain(m, &c, 37_099_000, 44_195_000, 3); }
            let r3 = plain_rev(m, &c, 44_200_000, 51_860_000, 2);
            let r2 = plain(&r3, &c, 37_099_000, 44_195_000, b2);
            plain(&r2, &c, 18_900_000, 26_325_000, 2) }
        // ITEM 10: 105 = run 3 b2 (reversed run), run 2 b4, run 1 b2 ; 106 = run 3 b2 + run 1 b2 only (run 2 untouched) ; 107 = run 1 b2 only
        105 | 106 | 107 => {
            let (lo1, hi1, lo3, hi3) = (19_000_000usize, 26_900_000usize, 60_600_000usize, 68_100_000usize);
            let cfg = |reg: &[Row]| { let (ord, ast) = derive(reg, 635, 628, 513);
                Pl { n: 129, fire: 635, tst: 636, tags: vec![628, 629, 630, 631, 634], anc: rng(513, 525), ord, ast } };
            let mut cur: Vec<Row> = m.to_vec();
            if item != 107 { let reg: Vec<Row> = cur[lo3..hi3].iter().rev().copied().collect(); let c = cfg(&reg); cur = plain_rev(&cur, &c, lo3, hi3, 2); }
            if item == 105 { cur = gen3b(&cur, &G3 { f: 631, fire: 634, tst: 635, tags: vec![628, 629, 630], anc: rng(513, 529), lo: 37_913_151, hi: 60_160_000, b0: 2, tagbit0: 2 }, 4); }
            { let c = cfg(&cur[lo1..hi1]); cur = plain(&cur, &c, lo1, hi1, 2); }
            cur }
        4 | 12 => { let d2 = item == 12;
            let g = G3 { f: 626, fire: 637, tst: 627, tags: vec![628, 629, 630], anc: if d2 { rng(254, 264) } else { rng(258, 268) }, lo: if d2 { 39_985_000 } else { 41_340_000 }, hi: if d2 { 61_440_000 } else { 63_600_000 }, b0: 2, tagbit0: 2 };
            let mid = gen3b(m, &g, 3); let delta = mid.len() - m.len();
            let (lo, hi) = if d2 { (72_760_000, 79_965_000) } else { (75_430_000, 82_890_000) };
            reverse_walk(&mid, lo + delta, hi + delta, if d2 { 127 } else { 129 }, if d2 { 254 } else { 258 }) }
        _ => panic!("no unrolling for item {}", item),
    }
}
/// items that are unrolled, and the record counts expected (raw n, new n); checked by the caller
pub const ITEMS: [(usize, u64, u64); 4] = [(2, 57_425_369, 71_735_247), (4, 83_575_700, 118_645_126), (10, 73_723_849, 94_018_965), (12, 80_641_154, 114_490_250)];

/// plain() on a run that is the time reversal of a forward run: reverse the window, unroll, reverse back (c carries ord / ast already)
pub fn plain_rev(m: &[Row], c: &Pl, lo: usize, hi: usize, b: usize) -> Vec<Row> {
    let reg: Vec<Row> = m[lo..hi].iter().rev().copied().collect();
    let c2 = Pl { n: c.n, fire: c.fire, tst: c.tst, tags: c.tags.clone(), anc: c.anc.clone(), ord: c.ord.clone(), ast: c.ast.clone() };
    let out = plain(&reg, &c2, 0, reg.len(), b);
    let mut full: Vec<Row> = Vec::with_capacity(m.len() + out.len());
    full.extend_from_slice(&m[..lo]); full.extend(out.iter().rev()); full.extend_from_slice(&m[hi..]); full
}
