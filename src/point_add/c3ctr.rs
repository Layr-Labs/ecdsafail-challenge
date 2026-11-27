//! (internal) (internal) (internal) ((internal)): rewrite step `ctr` = loop enable on the top bit of a counter (r2\(internal)'s encoding,
//! generalised to k tag bits, forward and reverse loops, pad of the reverse bodies moved to a dirty lane).
//! Works on rows where the X pairs of wire E are already removed (`negxall:251`), so E = 0 at a loop's entry.
use super::*;
use super::w2::*;

pub const E: u16 = 251;
pub const F: u16 = 243;
/// dirty loans: wires the item never names (lanes 14..111, 508)
pub const LOANS: [u16; 6] = [14, 15, 16, 17, 18, 19];
pub const DPAD: u16 = 30;
pub const QLOAN: u16 = 31;
#[derive(Clone, Debug)]
pub struct Win { pub a: usize, pub b: usize, pub na: usize, pub nb: usize, pub kind: u8, pub tags: Vec<u16>, pub start_toggle: bool, pub cmax: usize, pub ntog: usize, pub npad: usize, pub n2: usize }
thread_local! { pub static WINS: std::cell::RefCell<Vec<Win>> = std::cell::RefCell::new(Vec::new()); }
#[inline] pub fn tgt(r: &Row) -> u16 { match r[0] { 6 => r[1], 8 => r[2], 13 => r[3], _ => NONE } }
#[inline] pub fn is_gate(r: &Row) -> bool { match r[0] { 6 => r[2] == NONE, 8 => r[3] == NONE, 13 => true, _ => false } }
#[inline] pub fn ctl2(r: &Row) -> [u16; 2] { match r[0] { 8 => [r[1], NONE], 13 => [r[1], r[2]], _ => [NONE, NONE] } }
#[inline] pub fn has_ctl(r: &Row, w: u16) -> bool { let c = ctl2(r); c[0] == w || c[1] == w }
#[inline] pub fn names(r: &Row, w: u16) -> bool { (1..=qubits(r[0])).any(|j| r[j] == w) }
pub fn mcx(ctl: &[u16], z: u16, loans: &[u16], out: &mut Vec<Row>) {
    let n = ctl.len();
    match n { 0 => { out.push([6, z, NONE, NONE]); return; } 1 => { out.push([8, ctl[0], z, NONE]); return; } 2 => { out.push([13, ctl[0], ctl[1], z]); return; } _ => {} }
    let b = &loans[..n - 2];
    for _ in 0..2 { out.push([13, ctl[n - 1], b[n - 3], z]); for i in (1..=n - 3).rev() { out.push([13, ctl[i + 1], b[i - 1], b[i]]); } out.push([13, ctl[0], ctl[1], b[0]]); for i in 1..=n - 3 { out.push([13, ctl[i + 1], b[i - 1], b[i]]); } }
}
/// R += 1 on bits (lsb first)
pub fn inc(bits: &[u16], loans: &[u16], out: &mut Vec<Row>) { for j in (1..bits.len()).rev() { mcx(&bits[..j], bits[j], loans, out); } out.push([6, bits[0], NONE, NONE]); }
pub fn dec(bits: &[u16], loans: &[u16], out: &mut Vec<Row>) { let mut v = Vec::new(); inc(bits, loans, &mut v); v.reverse(); out.extend_from_slice(&v); }
/// three-control toggle with one dirty loan q
pub fn cccx(a: u16, b: u16, c: u16, t: u16, q: u16, out: &mut Vec<Row>) { out.push([13, a, b, q]); out.push([13, q, c, t]); out.push([13, a, b, q]); out.push([13, q, c, t]); }

/// toggle span at i: [up(j) top down(j) A] x 2 with top = C(x, r_j -> E), A = C(F, t0 -> r_0); returns (length, tags lsb..msb = t0, t1..tj, top)
pub fn toggle_at(rows: &[Row], i: usize) -> Option<(usize, Vec<u16>)> {
    let n = rows.len();
    for j in 0..=9usize { let p = i + j; if p >= n { break; } let top = rows[p]; if top[0] != 13 { break; } if top[3] != E { continue; }
        let len = 4 * j + 4; let half = 2 * j + 2; if i + len > n { return None; }
        if rows[i..i + half] != rows[i + half..i + len] { return None; }
        let a = rows[i + 2 * j + 1]; if a[0] != 13 { return None; } let (t0, r0) = if a[1] == F { (a[2], a[3]) } else if a[2] == F { (a[1], a[3]) } else { return None; };
        let mut tags = vec![t0]; let mut r = r0;
        for u in 0..j { let q = rows[i + u]; if q[0] != 13 || q != rows[i + 2 * j - u] { return None; } let t = if q[1] == r { q[2] } else if q[2] == r { q[1] } else { return None; }; tags.push(t); r = q[3]; }
        let x = if top[1] == r { top[2] } else if top[2] == r { top[1] } else { return None; }; tags.push(x);
        if tags.contains(&E) || tags.contains(&F) { return None; }
        return Some((len, tags)); }
    None
}
/// the clean tag wires (zero when the fire bit is 0); every other tag of a sector is a register lane, dirty when F = 0
pub const CLEAN: [u16; 4] = [248, 244, 245, 246];
struct Ctr { out: Vec<Row>, seg: Vec<Row>, seeded: bool, c: usize, ce: usize, cmax: usize, encoded: bool, tags: Vec<u16>, xpar: Vec<bool>, npad: usize, ntog: usize, nuse: usize, n2: usize }
impl Ctr {
    fn bits(&self) -> Vec<u16> { let mut b = self.tags.clone(); b.push(F); b }
    fn ndirty(&self) -> usize { self.tags.iter().filter(|t| !CLEAN.contains(t)).count() }
    fn sync(&mut self, target: usize) { let b = self.bits(); while self.ce < target { inc(&b, &LOANS, &mut self.out); self.ce += 1; } while self.ce > target { dec(&b, &LOANS, &mut self.out); self.ce -= 1; } }
    /// PRE (forward = true) / POST: where F = 0 the dirty tags move to the lowest positions; then tags ^= F
    fn prepost(&mut self, forward: bool) -> Result<(), String> {
        let tg = self.tags.clone(); let nc = tg.iter().filter(|t| CLEAN.contains(t)).count(); let nd = tg.len() - nc;
        if tg[..nc].iter().any(|t| !CLEAN.contains(t)) || nd > nc { return Err("tag layout".into()); }
        let mut v: Vec<Row> = Vec::new();
        if nd > 0 { v.push([6, F, NONE, NONE]); for j in 0..nd { let (lo, hi) = (tg[j], tg[nc + j]); v.push([8, hi, lo, NONE]); v.push([13, F, lo, hi]); v.push([8, hi, lo, NONE]); } v.push([6, F, NONE, NONE]); }
        for &t in &tg { v.push([8, F, t, NONE]); }
        if !forward { v.reverse(); } self.out.extend_from_slice(&v); Ok(())
    }
    /// the enable as a control list at the current count: [F], or [F, t0] at the last count of a full sector
    fn en(&mut self) -> Result<Vec<u16>, String> {
        if !self.encoded { return Ok(vec![F]); }
        let w = 1usize << self.tags.len(); let nd = self.ndirty();
        if self.c + (1usize << nd) - 1 < w { return Ok(vec![F]); }
        if nd == 1 && self.c == w - 1 { self.n2 += 1; return Ok(vec![F, self.tags[0]]); }
        Err(format!("count {} does not fit {} tags with {} dirty", self.c, self.tags.len(), nd))
    }
    /// target ^= enable AND (extra controls)
    fn en_x(&mut self, en: &[u16], extra: &[u16], t: u16) { let mut c: Vec<u16> = en.to_vec(); c.extend_from_slice(extra);
        if c.len() == 3 { cccx(c[0], c[1], c[2], t, QLOAN, &mut self.out); } else { mcx(&c, t, &LOANS, &mut self.out); } }
    /// a record outside a pad episode: control uses of E become uses of the enable
    fn sub(&mut self, r: Row, en: &[u16]) -> Result<(), String> {
        if !names(&r, E) { self.out.push(r); return Ok(()); }
        if tgt(&r) == E { return Err("write of the enable inside a body".into()); }
        self.nuse += 1;
        match r[0] { 8 => { self.en_x(en, &[], r[2]); }
            13 => { let x = if r[1] == E { r[2] } else { r[1] }; if x == E { return Err("E twice".into()); } if x == F { self.en_x(en, &[], r[3]); } else { self.en_x(en, &[x], r[3]); } }
            _ => return Err("E in a non-gate".into()) }
        Ok(())
    }
    fn flush(&mut self) -> Result<(), String> {
        let seg = std::mem::take(&mut self.seg); if seg.is_empty() { return Ok(()); }
        let any_e = seg.iter().any(|r| names(r, E)); let any_f = seg.iter().any(|r| names(r, F));
        if !any_e && !any_f { self.out.extend_from_slice(&seg); return Ok(()); }
        if !self.seeded { if any_e { return Err("use of the enable before the seed".into()); } self.sync(0); self.out.extend_from_slice(&seg); return Ok(()); }
        let c = self.c; self.sync(c); self.cmax = self.cmax.max(c); let en = self.en()?;
        // pad episodes: maximal stretches in which the pad (wire F in the original) carries open writes
        let mut eps: Vec<(usize, usize)> = Vec::new(); { let mut open: Vec<Row> = Vec::new(); let mut st = 0usize;
            for (k, r) in seg.iter().enumerate() { if tgt(r) != F { continue; } if names(r, E) || has_ctl(r, F) { return Err("pad write controlled by E or F".into()); }
                if open.is_empty() { st = k; } if let Some(p) = open.iter().rposition(|q| q == r) { open.remove(p); } else { open.push(*r); } if open.is_empty() { eps.push((st, k)); } }
            if !open.is_empty() { return Err("pad writes do not close in the segment".into()); } }
        let mut k = 0usize; let mut e = 0usize;
        while k < seg.len() {
            if e < eps.len() && eps[e].0 == k { let (first, last) = eps[e]; e += 1; self.npad += 1;
                let (mut loan, mut bl, mut h) = (NONE, NONE, NONE); let (mut n1, mut n2) = (0, 0);
                for j in first..=last { let r = seg[j]; if tgt(&r) == F || !has_ctl(&r, F) { continue; } if r[0] != 13 { return Err("CX from the pad while it carries".into()); }
                    let x = if r[1] == F { r[2] } else { r[1] };
                    if x == E { n2 += 1; if loan != NONE && loan != r[3] { return Err("pad type 2 target is not the loan".into()); } loan = r[3]; }
                    else { n1 += 1; if (loan != NONE && loan != x) || (bl != NONE && bl != r[3]) { return Err("pad type 1 not unique".into()); } loan = x; bl = r[3]; } }
                if n1 > 0 || n2 > 0 { if bl == NONE { return Err("pad: no top sum lane".into()); }
                    for j in first..=last { let r = seg[j]; if r[0] == 13 && r[3] != F && ((r[1] == loan && r[2] == bl) || (r[2] == loan && r[1] == bl)) { if h != NONE && h != r[3] { return Err("pad: slot not unique".into()); } h = r[3]; } }
                    if h == NONE { return Err("pad: no slot".into()); } }
                if n1 > 0 { self.en_x(&en, &[h, DPAD], bl); }
                for j in first..=last { let r = seg[j];
                    if tgt(&r) == F { let mut q = r; let nq = qubits(r[0]); q[nq] = DPAD; self.out.push(q); }
                    else if has_ctl(&r, F) { let x = if r[1] == F { r[2] } else { r[1] }; let y = r[3];
                        if x == E { self.en_x(&en, &[DPAD], y); self.en_x(&en, &[], y); self.nuse += 1; } else { self.out.push([13, x, DPAD, y]); self.out.push([8, x, y, NONE]); } }
                    else { self.sub(r, &en)?; } }
                if n2 > 0 { self.en_x(&en, &[bl, DPAD], h); }
                k = last + 1; continue; }
            self.sub(seg[k], &en)?; k += 1; }
        Ok(())
    }
}
/// parse one loop window starting at `start` (a seed CX F->E or a toggle); Ok((end, new rows, win info, counts))
fn ctr_window(rows: &[Row], start: usize, maxlen: usize) -> Result<(usize, Vec<Row>, Win, [usize; 3]), String> {
    let n = rows.len(); let mut s = Ctr { out: Vec::new(), seg: Vec::new(), seeded: false, c: 0, ce: 0, cmax: 0, encoded: false, tags: Vec::new(), xpar: Vec::new(), npad: 0, ntog: 0, nuse: 0, n2: 0 };
    let mut i = start; let start_toggle = rows[start] != [8, F, E, NONE]; let mut all_tags: Vec<u16> = Vec::new();
    while i < n { if i - start > maxlen { return Err("window too long".into()); }
        let r = rows[i];
        if r[0] == 13 { if let Some((len, tg)) = toggle_at(rows, i) { s.flush()?; s.ntog += 1;
            if !s.encoded { if s.c != 0 { return Err("toggle while decoded with a non-zero count".into()); }
                if !s.tags.is_empty() && s.tags != tg { return Err("tag set changes".into()); }
                s.tags = tg.clone(); all_tags = tg.clone(); s.xpar = vec![true; tg.len()];
                for &t in &tg { s.out.push([6, t, NONE, NONE]); } s.prepost(true)?;
                s.encoded = true; s.c = 1; }
            else { if tg != s.tags { return Err("tag set changes".into()); }
                let v: usize = (0..tg.len()).map(|k| if s.xpar[k] { 0 } else { 1usize << k }).sum();
                if v == s.c { s.c += 1; } else if s.c >= 1 && v == s.c - 1 { s.c -= 1; } else { return Err(format!("toggle value {} at count {}", v, s.c)); }
                if s.c == 0 { s.sync(0); let tg = s.tags.clone(); s.prepost(false)?; for k in 0..tg.len() { if s.xpar[k] { s.out.push([6, tg[k], NONE, NONE]); } } s.encoded = false; } }
            i += len; continue; } }
        if r == [8, F, E, NONE] { s.flush()?;
            if !s.seeded { s.seeded = true; i += 1; continue; }
            if s.c != 0 || s.encoded { return Err("un-seed at a non-zero count".into()); }
            if s.ntog == 0 { return Err("no toggle".into()); }
            let w = Win { a: start, b: i + 1, na: 0, nb: 0, kind: 1, tags: all_tags, start_toggle, cmax: s.cmax, ntog: s.ntog, npad: s.npad, n2: s.n2 };
            return Ok((i + 1, s.out, w, [s.ntog, s.npad, s.nuse])); }
        if !is_gate(&r) { return Err(format!("kind {} inside the window", r[0])); }
        if s.encoded { if let Some(k) = s.tags.iter().position(|&t| names(&r, t)) { if r[0] == 6 { s.xpar[k] = !s.xpar[k]; i += 1; continue; } return Err("a body names a tag".into()); } }
        if tgt(&r) == E { return Err(format!("write of E: {:?}", r)); }
        if LOANS.iter().any(|&l| names(&r, l)) || names(&r, DPAD) || names(&r, QLOAN) { return Err("loan named".into()); }
        s.seg.push(r); i += 1; }
    Err("no end".into())
}
/// `ctr[:<lo>]`: loops that start at record lo * 1,000,000 or later (of the rows this step receives)
pub fn ctr(rows: Vec<Row>, info: &mut w2rw::Info, lo_arg: usize) -> Vec<Row> {
    let n = rows.len(); let mut out: Vec<Row> = Vec::with_capacity(n + n / 64); let mut wins: Vec<Win> = Vec::new(); let mut i = 0usize; let mut p = 0usize;
    let mut rej: std::collections::BTreeMap<String, (u64, usize)> = std::collections::BTreeMap::new(); let (mut tog, mut pad, mut uses) = (0usize, 0usize, 0usize);
    let maxlen: usize = env("C3_MAXLEN").map(|x| x.parse().unwrap()).unwrap_or(1_500_000);
    let lo: usize = env("C3_LO").map(|x| x.parse().unwrap()).unwrap_or(lo_arg); let hi: usize = env("C3_HI").map(|x| x.parse().unwrap()).unwrap_or(usize::MAX);
    while i < n { let r = rows[i];
        let cand = i >= lo && i < hi && (r == [8, F, E, NONE] || (r[0] == 13 && toggle_at(&rows, i).is_some()));
        if !cand { i += 1; continue; }
        match ctr_window(&rows, i, maxlen) {
            Ok((end, new, mut w, st)) => { out.extend_from_slice(&rows[p..i]); w.na = out.len(); out.extend_from_slice(&new); w.nb = out.len(); wins.push(w); tog += st[0]; pad += st[1]; uses += st[2]; p = end; i = end; }
            Err(e) => { let key: String = e.chars().map(|c| if c.is_ascii_digit() { '#' } else { c }).collect(); let en = rej.entry(key).or_insert((0, i)); en.0 += 1;
                if env("C3_VERBOSE").is_some() { println!("  ctr reject at {}: {}", i, e); }
                i += if r[0] == 13 { toggle_at(&rows, i).unwrap().0 } else { 1 }; } } }
    out.extend_from_slice(&rows[p..]);
    let (old, new): (usize, usize) = (wins.iter().map(|w| w.b - w.a).sum(), wins.iter().map(|w| w.nb - w.na).sum());
    info.notes.push(format!("ctr: windows {} (rows {} -> {}, {:+}); toggles {} pad bodies {} enable uses {}; rejected candidates {:?}", wins.len(), old, new, new as i64 - old as i64, tog, pad, uses, rej));
    if env("C3_WINLOG").is_some() { for w in &wins { println!("  win [{}, {}) -> {} rows; tags {:?} start_toggle {} cmax {} toggles {} pads {} two-control segments {}", w.a, w.b, w.nb - w.na, w.tags, w.start_toggle, w.cmax, w.ntog, w.npad, w.n2); } }
    WINS.with(|w| *w.borrow_mut() = wins);
    out
}


