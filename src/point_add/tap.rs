//! build631 harness: tap and splice of members of the stream (experiment tool; HARNESS = false removes every effect).
//!  B631_TAP=dir      write the rows of every hooked item (wire space, exactly as `i1::emit_hooked` receives them: item<ii>.r8) and of the six
//!                    native stages (physical lane space after the item copy, before relabelling: native<stage>.r8) as u16le [kind,a,b,c]
//!  B631_SPLICE=dir   use item<ii>.r8 instead of the generated hook rows (length may differ: i1::hook_lens -> deltas -> Shift moves everything
//!                    after it), and overlay native<stage>.r8 (same length) on the stage before relabelling
//!  B631_DUMP_PRE=f   write the pre-relabel stream (u16le rows) to f
//!  B631_STOP=tap|pre|relabel   exit(0) after that point (relabel: after i1::apply, i.e. after the table's n/hash assertion and FULL_632)
use super::*;
use std::io::{Read, Write};
pub const HARNESS: bool = true;
pub const NATIVE: [usize; 6] = [2, 12, 13, 18, 28, 29];
/// fin631: the 631 row's own settings (used when the variable is not set in the environment)
fn baked(n: &str) -> Option<&'static str> { match n { "B631_ERASE497" => Some("0:11891,1:11892,2:11893,3:11894"), "B631_REHOST" => Some("4:621:531"), "B631_GLUE" => Some("111:11895:1:3,621:11896:3:6,621:11897:9:11,111:11898:11:14"), _ => None } }
fn var(n: &str) -> Option<std::path::PathBuf> { if !HARNESS { return None; } std::env::var(n).ok().filter(|s| !s.is_empty()).map(Into::into).or_else(|| baked(n).map(Into::into)) }
fn manifest(line: &str) { if let Some(d) = var("B631_TAP") { let mut f = std::fs::OpenOptions::new().create(true).append(true).open(d.join("manifest.txt")).unwrap(); writeln!(f, "{}", line).unwrap(); } }
pub fn write_rows<I: Iterator<Item = Row>>(path: &std::path::Path, it: I) -> (u64, u64) {
    let mut w = std::io::BufWriter::with_capacity(1 << 22, std::fs::File::create(path).unwrap()); let (mut n, mut h) = (0u64, i1::HASH0);
    for r in it { for x in r { w.write_all(&x.to_le_bytes()).unwrap(); } h = i1::hash_step(h, r); n += 1; } w.flush().unwrap(); (n, h) }
pub fn read_rows(path: &std::path::Path) -> Vec<Row> {
    let mut f = std::io::BufReader::with_capacity(1 << 22, std::fs::File::open(path).unwrap_or_else(|e| panic!("splice file {:?}: {}", path, e)));
    let len = f.get_ref().metadata().unwrap().len() as usize; assert!(len % 8 == 0, "splice file length"); let mut v: Vec<Row> = Vec::with_capacity(len / 8);
    let mut buf = vec![0u8; 8 << 16]; let mut left = len;
    while left > 0 { let k = left.min(buf.len()); f.read_exact(&mut buf[..k]).unwrap(); for c in buf[..k].chunks_exact(8) { v.push([u16::from_le_bytes([c[0], c[1]]), u16::from_le_bytes([c[2], c[3]]), u16::from_le_bytes([c[4], c[5]]), u16::from_le_bytes([c[6], c[7]])]); } left -= k; }
    v }
fn splice_path(name: &str) -> Option<std::path::PathBuf> { let p = var("B631_SPLICE")?.join(name); if p.exists() { Some(p) } else { None } }

/// RPATCH01 edit script (rowpatch.py): ops (pos, ndel, new rows) against the original member rows
pub fn apply_patch(orig: &[Row], d: &[u8]) -> Vec<Row> {
    assert!(&d[..8] == b"RPATCH01", "patch magic"); let n = u64::from_le_bytes(d[8..16].try_into().unwrap()) as usize; let mut q = 16usize;
    let mut out: Vec<Row> = Vec::with_capacity(orig.len() + 1024); let mut i = 0usize;
    for _ in 0..n { let pos = u64::from_le_bytes(d[q..q + 8].try_into().unwrap()) as usize; let nd = u32::from_le_bytes(d[q + 8..q + 12].try_into().unwrap()) as usize; let ni = u32::from_le_bytes(d[q + 12..q + 16].try_into().unwrap()) as usize; q += 16;
        assert!(pos >= i && pos + nd <= orig.len(), "patch op out of order"); out.extend_from_slice(&orig[i..pos]);
        for k in 0..ni { let c = &d[q + 8 * k..q + 8 * k + 8]; out.push([u16::from_le_bytes([c[0], c[1]]), u16::from_le_bytes([c[2], c[3]]), u16::from_le_bytes([c[4], c[5]]), u16::from_le_bytes([c[6], c[7]])]); }
        q += 8 * ni; i = pos + nd; }
    assert!(q == d.len(), "patch length"); out.extend_from_slice(&orig[i..]); out }
fn patch_path(name: &str) -> Option<std::path::PathBuf> { let p = var("B631_SPLICE")?.join(name); if p.exists() { Some(p) } else { None } }
/// length of the replacement of hooked item `ii`, if one is given (the allocation in build_slots needs it before the hooks exist)
pub fn len_override(ii: usize, base: u64) -> Option<u64> {
    if let Some(p) = splice_path(&format!("item{}.r8", ii)) { return Some(std::fs::metadata(p).unwrap().len() / 8); }
    if patch_path(&format!("item{}.patch", ii)).is_none() { if let Some(l) = fixed_len(ii) { return Some(l); } }
    let p = patch_path(&format!("item{}.patch", ii))?; let d = std::fs::read(p).unwrap(); let n = u64::from_le_bytes(d[8..16].try_into().unwrap()) as usize; let mut q = 16usize; let mut delta = 0i64;
    for _ in 0..n { let nd = u32::from_le_bytes(d[q + 8..q + 12].try_into().unwrap()) as i64; let ni = u32::from_le_bytes(d[q + 12..q + 16].try_into().unwrap()) as i64; q += 16 + 8 * ni as usize; delta += ni - nd; }
    Some((base as i64 + delta) as u64) }
/// the rows of hooked item `ii`: the replacement file when given, else `gen()`; tapped when B631_TAP is set
pub fn item(ii: usize, gen: impl FnOnce() -> Vec<Row>) -> Vec<Row> {
    let rows = match splice_path(&format!("item{}.r8", ii)) { Some(p) => { let r = read_rows(&p); eprintln!("[b631] item {} SPLICED from {:?}: {} rows", ii, p, r.len()); r } None => { let g = gen(); match patch_path(&format!("item{}.patch", ii)) { Some(p) => { let r = apply_patch(&g, &std::fs::read(&p).unwrap()); eprintln!("[b631] item {} PATCHED from {:?}: {} -> {} rows", ii, p, g.len(), r.len()); r } None => match fixed_events(ii) { Some(ev) => { let r = fix_item(ii, &g, ev); eprintln!("[b631] item {} fixed interface (baked events): {} -> {} rows", ii, g.len(), r.len()); r } None => g } } } };
    if let Some(d) = var("B631_TAP") { let (n, h) = write_rows(&d.join(format!("item{}.r8", ii)), rows.iter().copied()); manifest(&format!("item {} rows {} hash {:016x}", ii, n, h)); }
    rows }
/// native stages: tap, overlay (generic over the slot type; call after items(), before relabelling)
pub fn natives<S: Slot>(pk: &Pack, sh: &Shift, out: &mut [S]) {
    if !HARNESS { return; }
    for &k in NATIVE.iter() { let s0 = if k == 0 { 0 } else { pk.segs[k - 1].end }; let e0 = pk.segs[k].end;
        let (a, b) = ((s0 as i64 + sh.at(s0)) as usize, (e0 as i64 + sh.at(e0)) as usize);
        if let Some(d) = var("B631_TAP") { let (n, h) = write_rows(&d.join(format!("native{}.r8", k)), out[a..b].iter().map(|s| s.to_row())); manifest(&format!("native {} start {} end {} rows {} hash {:016x}", k, a, b, n, h)); }
        if let Some(pd) = patch_path(&format!("native{}.patch", k)).map(|p| std::fs::read(&p).unwrap()).or_else(|| if splice_path(&format!("native{}.r8", k)).is_none() { baked_native(k).map(|d| d.to_vec()) } else { None }) { let p = k; let orig: Vec<Row> = out[a..b].iter().map(|s| s.to_row()).collect(); let r = apply_patch(&orig, &pd); assert!(r.len() == b - a, "native {} patch changes the length", k);
            for (i, row) in r.into_iter().enumerate() { if row != orig[i] { out[a + i] = S::from_row(row); } } eprintln!("[b631] native {} PATCHED from {:?}", k, p); }
        if let Some(p) = splice_path(&format!("native{}.r8", k)) { let r = read_rows(&p); assert!(r.len() == b - a, "native {} splice length {} != stage {}", k, r.len(), b - a);
            for (i, row) in r.into_iter().enumerate() { out[a + i] = S::from_row(row); } eprintln!("[b631] native {} overlaid from {:?} at {}..{}", k, p, a, b); } }
}
pub fn stop_if(what: &str) { if var("B631_STOP").map_or(false, |s| s.to_string_lossy() == what) { eprintln!("[b631] stop after {}", what); std::process::exit(0); } }
pub fn dump_pre<S: Slot>(out: &[S], n: usize) {
    if let Some(p) = var("B631_DUMP_PRE") { let (m, h) = write_rows(&p, out[..n].iter().map(|s| s.to_row())); eprintln!("[b631] pre stream written: n {} hash {:016x}", m, h); }
    if var("B631_TAP").is_some() { manifest(&format!("pre n {}", n)); }
}

/// B631_SCANS=file: replacement of data/scans.trc (container SCANS1)
pub fn scans_override() -> Option<Vec<u8>> { let p = var("B631_SCANS")?; let d = std::fs::read(&p).unwrap(); eprintln!("[b631] scans.trc OVERRIDDEN from {:?}: {} bytes", p, d.len()); Some(d) }
/// B631_ERASE497="k:bit,k:bit" (k = bracket 0..3): logical 497 erased (HMR into classical bit) at the end of the bracket's erase item, Z fix after its scan
pub fn erase497(k: usize) -> Option<u16> { let v = var("B631_ERASE497")?; for e in v.to_string_lossy().split(',') { let mut it = e.split(':'); let (a, b) = (it.next()?.parse::<usize>().ok()?, it.next()?.parse::<u16>().ok()?); if a == k { return Some(b); } } None }
/// B631_NOFIX=1: drop the Z phase fix of the 497 erase (wrong variant)
pub fn nofix() -> bool { var("B631_NOFIX").is_some() }
/// B631_GLUE="id:bit:e:r,..." : glue id erased (HMR into classical bit) at the end of item e, conditional Z at the start of item r (r = x: none)
pub fn glue() -> Vec<(u16, u16, usize, usize)> { let v = match var("B631_GLUE") { Some(v) => v, None => return Vec::new() }; let mut o = Vec::new();
    for e in v.to_string_lossy().split(',') { let f: Vec<&str> = e.split(':').collect(); assert!(f.len() == 4, "B631_GLUE entry {}", e);
        o.push((f[0].parse().unwrap(), f[1].parse().unwrap(), f[2].parse().unwrap(), if f[3] == "x" { usize::MAX } else { f[3].parse().unwrap() })); } o }
/// B631_REHOST="ii:from:donor": rename, in hooked item ii (wire space), every operand wire mapping to glue id `from` to the wire of id `donor` (law631 rehost_item4)
pub fn rehost(pk: &Pack, ii: usize, rows: &mut Vec<Row>) { let v = match var("B631_REHOST") { Some(v) => v, None => return };
    for e in v.to_string_lossy().split(',') { let f: Vec<u16> = e.split(':').map(|x| x.parse().unwrap()).collect(); if f[0] as usize != ii { continue; }
        let it = &pk.items[ii]; let wm = &pk.wire_maps[it.wm - 1];
        let wf: Vec<u16> = (0..wm.len() as u16).filter(|&w| wm[w as usize] == f[1]).collect(); let wd: Vec<u16> = (0..wm.len() as u16).filter(|&w| wm[w as usize] == f[2]).collect();
        assert!(!wf.is_empty() && !wd.is_empty(), "rehost: no wire for id {} or {}", f[1], f[2]); let d = wd[0];
        for r in rows.iter() { for q in 1..=qubits(r[0]) { assert!(!wd.contains(&r[q]), "rehost: donor wire {} is named by a row", r[q]); } }
        let mut n = 0u64; for r in rows.iter_mut() { let mut hit = false; for q in 1..=qubits(r[0]) { if wf.contains(&r[q]) { r[q] = d; hit = true; } } if hit { n += 1; } }
        eprintln!("[b631] item {} rows re-hosted from id {} to id {} (wire {}): {}", ii, f[1], f[2], d, n); } }
/// B631_TABLE1 / B631_TABLE2 = raw I1RELAB1 table files (relplan plan --out)
pub fn table_override(k: usize) -> Option<Vec<u8>> { let p = var(if k == 1 { "B631_TABLE1" } else { "B631_TABLE2" })?; let d = std::fs::read(&p).unwrap(); eprintln!("[b631] relabel table {} from {:?}: {} bytes", k, p, d.len()); Some(d) }
pub fn dump_rel<S: Slot>(out: &[S], n: usize) { if let Some(p) = var("B631_DUMP_REL") { let (m, h) = write_rows(&p, out[..n].iter().map(|s| s.to_row())); eprintln!("[b631] relabelled stream written: n {} hash {:016x}", m, h); } }

// ---- fin631: baked members of the 631 row
/// native walks and U rebuilds without logical 497: RPATCH01 edit scripts (same length) against the stage rows
fn baked_native(k: usize) -> Option<&'static [u8]> { Some(match k { 2 => &include_bytes!("data/b631/native2.patch")[..], 12 => &include_bytes!("data/b631/native12.patch")[..], 13 => &include_bytes!("data/b631/native13.patch")[..],
    18 => &include_bytes!("data/b631/native18.patch")[..], 28 => &include_bytes!("data/b631/native28.patch")[..], 29 => &include_bytes!("data/b631/native29.patch")[..], _ => return None }) }
/// fixed-interface items 2 and 10: event tables (l, r, host, donor, pol) and the asserted output lengths
fn fixed_events(ii: usize) -> Option<&'static [u8]> { match ii { 2 => Some(&include_bytes!("data/b631/item2.ev")[..]), 10 => Some(&include_bytes!("data/b631/item10.ev")[..]), _ => None } }
fn fixed_len(ii: usize) -> Option<u64> { match ii { 2 => Some(61903305), 10 => Some(76908446), _ => None } }
/// Port of the L11 quotient (apply_items.run): the carrier wire (135 in item 2, 637 in item 10) is followed through its moves, every later reference goes through the slot map,
/// guest intervals are re-hosted on their donor, and the original exit interface is restored by swaps of physical slots.
fn fix_item(ii: usize, src: &[Row], ev: &[u8]) -> Vec<Row> {
    assert!(&ev[..8] == b"B631EV01", "event table"); let m = u32::from_le_bytes(ev[8..12].try_into().unwrap()) as usize; assert!(ev.len() == 12 + 13 * m, "event table length");
    let h0: u16 = if ii == 2 { 135 } else { 637 }; let mut h = h0; let mut slot: Vec<u16> = (0..646u16).collect(); slot[h as usize] = NONE;
    let mut out: Vec<Row> = Vec::with_capacity(src.len() + 64);
    fn block(out: &mut Vec<Row>, rows: &[Row], slot: &[u16], h: u16, rename: Option<u16>) {
        for r in rows { let n = match r[0] { 6 | 7 | 12 => 1, 8 | 9 => 2, 13 => 3, k => panic!("fix_item: row kind {}", k) }; let mut q = *r;
            for j in 1..=n { let mut w = q[j]; if let Some(d) = rename { if w == h { w = d; } } let s = slot[w as usize]; assert!(s != NONE, "unaccounted carrier reference"); q[j] = s; }
            out.push(q); } }
    let mut at = 0usize;
    for e in 0..m { let p = 12 + 13 * e; let l = u32::from_le_bytes(ev[p..p + 4].try_into().unwrap()) as usize; let r = u32::from_le_bytes(ev[p + 4..p + 8].try_into().unwrap()) as usize;
        let host = u16::from_le_bytes([ev[p + 8], ev[p + 9]]); let d = u16::from_le_bytes([ev[p + 10], ev[p + 11]]); let pol = ev[p + 12] as i8;
        assert!(at <= l && l < r && r <= src.len() && host == h, "fix_item: event order");
        block(&mut out, &src[at..l], &slot, h, None); let row = &src[l..r];
        if pol == -1 { assert!(row.len() == 2 && row[0] == [8, h, d, NONE] && row[1] == [8, d, h, NONE], "fix_item: move rows"); slot[h as usize] = slot[d as usize]; slot[d as usize] = NONE; h = d; }
        else if row.len() == 1 && row[0] == [6, h, NONE, NONE] { assert!(pol == 1); }
        else if pol == 2 { assert!(row.len() == 1 && row[0][0] == 8 && row[0][2] == h && row[0][3] == NONE); }
        else { block(&mut out, row, &slot, h, Some(d)); if pol != 0 { out.push([6, slot[d as usize], NONE, NONE]); } }
        at = r; }
    block(&mut out, &src[at..], &slot, h, None); assert!(h == h0, "fix_item: carrier not home");
    for j in 0..slot.len() { if j as u16 == h || slot[j] == j as u16 { continue; } let k = slot[j]; let other = slot.iter().position(|&x| x == j as u16).unwrap();
        out.push([8, k, j as u16, NONE]); out.push([8, j as u16, k, NONE]); out.push([8, k, j as u16, NONE]); slot[other] = k; slot[j] = j as u16; }
    assert!(out.len() as u64 == fixed_len(ii).unwrap(), "fix_item: length {}", out.len()); out }
