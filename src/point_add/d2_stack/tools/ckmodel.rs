// D2 stack/park classical model (private).  rustc -O ckmodel.rs
// Production FD-seed walk with alternating relabel (same walk and storage rules as jl-probe/d2sim.rs needB),
// with two stack disciplines side by side:
//   ideal : pops at every post-park tick t > p (d2sim).
//   ck    : the circuit's discipline.  Detection only at checkpoint ticks d in D: a walk with p < d that is still
//           undetected is detected at d with p_eff = max(p, lo - 1) (lo = previous checkpoint + 1, or F for the first
//           checkpoint); at d it pops t - p_eff bits (catch-up scan over wires (p_eff, d]).  At every tick t after a
//           detection, one per-tick pop (p_eff < t).  Pushes as d2sim (B/C letters, t <= p).
// Per walk: need (= needB) for both disciplines; per tick and per stage: N ranges (all walks, and only the walks
// where the stage's control fires), the X-rail bit length after the tick, the add width.
// Usage: ckmodel N THREADS SEED OUTPREFIX F d1,d2,... [noscan]   (D may be "all" = every tick >= F)
//   noscan: a walk detected at d records p_eff = d - 1 (no catch-up scan; typ wires (p, d-1] stay unreclaimed).
use std::io::Write;
const T: usize = 395;
const NL: usize = 5;
type U = [u64; NL];
const P: U = [0xFFFFFFFEFFFFFC2F, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0];
const ONE: U = [1, 0, 0, 0, 0];
#[inline] fn zero() -> U { [0; NL] }
#[inline] fn is_zero(a: &U) -> bool { a.iter().all(|&x| x == 0) }
#[inline] fn add(a: &U, b: &U) -> U { let mut o = zero(); let mut c = 0u128;
    for i in 0..NL { let t = a[i] as u128 + b[i] as u128 + c; o[i] = t as u64; c = t >> 64; } o }
#[inline] fn sub(a: &U, b: &U) -> U { let mut o = zero(); let mut br = 0i128;
    for i in 0..NL { let t = a[i] as i128 - b[i] as i128 - br; o[i] = t as u64; br = if t < 0 { 1 } else { 0 }; } o }
#[inline] fn shr1(a: &U) -> U { let mut o = zero(); for i in 0..NL { o[i] = (a[i] >> 1) | if i + 1 < NL { a[i + 1] << 63 } else { 0 }; } o }
#[inline] fn sar1(a: &U) -> U { let mut o = shr1(a); if (a[NL - 1] as i64) < 0 { o[NL - 1] |= 1 << 63; } o }
#[inline] fn bits(a: &U) -> i32 { for i in (0..NL).rev() { if a[i] != 0 { return 64 * i as i32 + 64 - a[i].leading_zeros() as i32; } } 0 }
#[inline] fn neg(a: &U) -> bool { (a[NL - 1] as i64) < 0 }
#[inline] fn not(a: &U) -> U { let mut o = *a; for x in o.iter_mut() { *x = !*x; } o }
#[inline] fn nrm(a: &U) -> U { if neg(a) { not(a) } else { *a } }
#[inline] fn bl(a: &U) -> i32 { bits(&nrm(a)) }
#[inline] fn sw(a: &U) -> i32 { bl(a) + 1 }
#[inline] fn absv(a: &U) -> U { if neg(a) { add(&not(a), &ONE) } else { *a } }
#[inline] fn ltu(a: &U, b: &U) -> bool { for i in (0..NL).rev() { if a[i] != b[i] { return a[i] < b[i]; } } false }
#[inline] fn is01(a: &U, b: &U) -> bool { let (x, y) = (absv(a), absv(b));
    (is_zero(&x) && y == ONE) || (is_zero(&y) && x == ONE) }
struct Rng(u64, u64, u64, u64);
impl Rng {
    fn new(seed: u64) -> Rng { let mut z = seed; let mut nx = || { z = z.wrapping_add(0x9E3779B97F4A7C15); let mut x = z;
        x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9); x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB); x ^ (x >> 31) };
        Rng(nx(), nx(), nx(), nx()) }
    fn next(&mut self) -> u64 { let r = self.1.wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = self.1 << 17; self.2 ^= self.0; self.3 ^= self.1; self.1 ^= self.2; self.0 ^= self.3; self.2 ^= t; self.3 = self.3.rotate_left(45); r }
    fn scalar(&mut self) -> U { loop { let mut d = zero(); for i in 0..4 { d[i] = self.next(); }
        if !is_zero(&d) && ltu(&d, &P) { return d; } } }
}
const AB: usize = 420;
// stage ranges: 0 Npre(all) 1 push(fires) 2 tickpop(fires) 3 scan(fires: N at scan start) 4 xbl(all, after tick)
// 5 ead(all) 6 Npre(ck all) 7 detect-M window (ck, all walks at checkpoint ticks)
const NS: usize = 8;
#[derive(Clone)]
struct Agg { walks: u64, unparked: u64, need_i: Vec<u64>, need_c: Vec<u64>, need_n: Vec<u64>,
    lo: Vec<i32>, hi: Vec<i32>, scanlen: Vec<u64>, det_at: Vec<u64>, peff_lag: Vec<u64> }
impl Agg { fn new() -> Agg { Agg { walks: 0, unparked: 0, need_i: vec![0; AB], need_c: vec![0; AB], need_n: vec![0; AB],
    lo: vec![i32::MAX; T * NS], hi: vec![i32::MIN; T * NS], scanlen: vec![0; 512], det_at: vec![0; T], peff_lag: vec![0; 512] } }
    fn merge(&mut self, o: &Agg) { self.walks += o.walks; self.unparked += o.unparked;
        for (a, b) in [(&mut self.need_i, &o.need_i), (&mut self.need_c, &o.need_c), (&mut self.need_n, &o.need_n),
            (&mut self.scanlen, &o.scanlen), (&mut self.det_at, &o.det_at), (&mut self.peff_lag, &o.peff_lag)] {
            for (x, y) in a.iter_mut().zip(b.iter()) { *x += *y; } }
        for i in 0..T * NS { self.lo[i] = self.lo[i].min(o.lo[i]); self.hi[i] = self.hi[i].max(o.hi[i]); } }
    fn rec(&mut self, t: usize, s: usize, v: i32) { let k = t * NS + s; self.lo[k] = self.lo[k].min(v); self.hi[k] = self.hi[k].max(v); }
}
struct Disc { nst: i32, need: i32, det: bool, peff: i32 }
fn walk(d: &U, ag: &mut Agg, f0: usize, ck: &[bool], lo_of: &[usize], noscan: bool) {
    let b = d[0] & 1;
    let x0 = if b == 1 { sar1(&sub(d, &P)) } else { sar1(d) };
    let y0 = if b == 1 { add(d, &x0) } else { add(&sub(d, &P), &x0) };
    let mut v = [x0, y0];
    let mut typ: u32 = if ltu(&absv(&x0), &absv(&y0)) { 1 } else { 0 };
    let mut park: i32 = -1;
    // three disciplines: 0 ideal, 1 ck, 2 no park skip
    let mut ds = [Disc { nst: 0, need: 0, det: false, peff: -1 }, Disc { nst: 0, need: 0, det: false, peff: -1 },
                  Disc { nst: 0, need: 0, det: false, peff: -1 }];
    for t in 0..T {
        let x = t % 2; let y = 1 - x;
        let (o0p, o1p) = (((t + 1) / 2) as i32, (t / 2) as i32);
        let c = (v[x][0] & 1) as u32;
        let wsw = bl(&v[0]).max(bl(&v[1]));
        ag.rec(t, 0, ds[0].nst); ag.rec(t, 6, ds[1].nst);
        if ck[t] { ag.rec(t, 7, (ds[1].nst + 1) / 2); }
        for dd in ds.iter_mut() { let (s0, _s1) = ((dd.nst + 1) / 2, dd.nst / 2); if c == 1 { dd.need = dd.need.max(o0p + wsw + s0); } }
        if c == 1 { v.swap(0, 1); }
        let h = sar1(&v[x]); let o = v[y];
        let agr = neg(&h) == neg(&o);
        let op = if agr { sub(&o, &h) } else { add(&o, &h) };
        let s = (agr ^ (neg(&h) == neg(&op))) as u32;
        typ = if t > 0 { c ^ typ ^ 1 } else { c ^ typ };
        let (nx_, ny_) = (nrm(&h), nrm(&o));
        let mut r = sub(&ny_, &nx_); if neg(&h) { r = sub(&r, &ONE); }
        let wad = bits(&nx_).max(bits(&ny_)).max(sw(&r));
        ag.rec(t, 5, wad);
        let (oxp, oyp) = if x == 0 { (o0p + 1, o1p) } else { (o1p + 1, o0p) };
        for dd in ds.iter_mut() {
            let (s0, s1) = ((dd.nst + 1) / 2, dd.nst / 2);
            let (sx_, sy_) = if x == 0 { (s0, s1) } else { (s1, s0) };
            dd.need = dd.need.max((oxp + sx_ + wad).max(oyp + sy_ + wad));
        }
        v[x] = h; v[y] = op;
        ag.rec(t, 4, bl(&v[x]));
        if park < 0 && is01(&v[0], &v[1]) { park = t as i32; }
        let lett = if typ == 1 { 0 } else if s == 1 { 2 } else { 1 };
        let ti = t as i32;
        // ideal
        { let dd = &mut ds[0];
          if park < 0 || ti <= park { if lett != 0 { ag.rec(t, 1, dd.nst); dd.nst += 1; } } else if dd.nst > 0 { dd.nst -= 1; } }
        // ck: detection (checkpoint), per-tick pop, scan, push
        { let dd = &mut ds[1];
          if dd.det && dd.peff < ti { ag.rec(t, 2, dd.nst); dd.nst -= 1; }
          if ck[t] && !dd.det && park >= 0 && park < ti {
              let lo = lo_of[t] as i32;
              let peff = if noscan { ti - 1 } else { park.max(lo - 1) };
              dd.det = true; dd.peff = peff;
              ag.rec(t, 3, dd.nst);
              let n = ti - peff; dd.nst -= n;
              ag.scanlen[(n as usize).min(511)] += 1; ag.det_at[t] += 1; ag.peff_lag[((ti - park) as usize).min(511)] += 1;
          }
          if lett != 0 { if park >= 0 && ti > park { panic!("post-park B/C"); } dd.nst += 1; }
          let _ = f0; }
        // none
        { let dd = &mut ds[2]; if lett != 0 { dd.nst += 1; } }
        let (o0q, o1q) = (((t + 2) / 2) as i32, ((t + 1) / 2) as i32);
        for dd in ds.iter_mut() {
            assert!(dd.nst >= 0);
            let (s0q, s1q) = ((dd.nst + 1) / 2, dd.nst / 2);
            let st = (o0q + bl(&v[0]) + s0q).max(o1q + bl(&v[1]) + s1q);
            dd.need = dd.need.max(st);
        }
    }
    ag.walks += 1;
    if park < 0 { ag.unparked += 1; return; }
    ag.need_i[(ds[0].need as usize).min(AB - 1)] += 1;
    ag.need_c[(ds[1].need as usize).min(AB - 1)] += 1;
    ag.need_n[(ds[2].need as usize).min(AB - 1)] += 1;
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: u64 = a[1].parse().unwrap(); let nth: u64 = a[2].parse().unwrap(); let seed: u64 = a[3].parse().unwrap();
    let pre = a[4].clone(); let f0: usize = a[5].parse().unwrap();
    let noscan = a.len() > 7 && a[7] == "noscan";
    let mut ck = vec![false; T];
    if a[6] == "all" { for t in f0..T { ck[t] = true; } } else { for s in a[6].split(',') { ck[s.parse::<usize>().unwrap()] = true; } }
    let mut lo_of = vec![0usize; T]; let mut prev: Option<usize> = None;
    for t in 0..T { if ck[t] { lo_of[t] = match prev { Some(p) => p + 1, None => f0 }; prev = Some(t); } }
    let t0 = std::time::Instant::now();
    let aggs: Vec<Agg> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..nth).map(|th| { let (ck, lo_of) = (&ck, &lo_of); let noscan = noscan; sc.spawn(move || {
            let mut rng = Rng::new(seed.wrapping_mul(1_000_003).wrapping_add(th)); let mut ag = Agg::new();
            let per = n / nth + if th < n % nth { 1 } else { 0 };
            for _ in 0..per { let d = rng.scalar(); walk(&d, &mut ag, f0, ck, lo_of, noscan); }
            ag }) }).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect() });
    let mut ag = Agg::new(); for x in &aggs { ag.merge(x); }
    let mut f = std::fs::File::create(format!("{pre}.txt")).unwrap();
    writeln!(f, "# ckmodel {} time={:.1}s", a[1..].join(" "), t0.elapsed().as_secs_f64()).unwrap();
    writeln!(f, "walks {} unparked {}", ag.walks, ag.unparked).unwrap();
    for (name, h) in [("ideal", &ag.need_i), ("ck", &ag.need_c), ("noskip", &ag.need_n)] {
        let tot: u64 = h.iter().sum();
        let line: Vec<String> = h.iter().enumerate().filter(|(_, &c)| c > 0).map(|(i, c)| format!("{i}:{c}")).collect();
        writeln!(f, "hist {name} {}", line.join(" ")).unwrap();
        let mut row = String::new();
        for aa in 284..296 { let over: u64 = h.iter().enumerate().filter(|(i, _)| *i > aa).map(|(_, c)| *c).sum();
            row += &format!(" A{aa}:{:.3}", 18048.0 * over as f64 / tot as f64); }
        writeln!(f, "events/corpus {name}{row}").unwrap();
    }
    let line: Vec<String> = ag.scanlen.iter().enumerate().filter(|(_, &c)| c > 0).map(|(i, c)| format!("{i}:{c}")).collect();
    writeln!(f, "hist scanlen {}", line.join(" ")).unwrap();
    let line: Vec<String> = ag.peff_lag.iter().enumerate().filter(|(_, &c)| c > 0).map(|(i, c)| format!("{i}:{c}")).collect();
    writeln!(f, "hist detect_lag(d-p) {}", line.join(" ")).unwrap();
    let mut g = std::fs::File::create(format!("{pre}_win.tsv")).unwrap();
    writeln!(g, "# t  Npre_lo Npre_hi | push_lo push_hi | tickpop_lo tickpop_hi | scan_lo scan_hi | xbl_hi | ead_hi | ckNpre_lo ckNpre_hi | detM_lo detM_hi   (empty = never fires)").unwrap();
    for t in 0..T {
        let mut row = format!("{t}");
        for s in 0..NS { let (l, h) = (ag.lo[t * NS + s], ag.hi[t * NS + s]);
            if l == i32::MAX { row += "\t-\t-"; } else { row += &format!("\t{l}\t{h}"); } }
        writeln!(g, "{row}").unwrap();
    }
    println!("done {:.1}s walks {} unparked {}", t0.elapsed().as_secs_f64(), ag.walks, ag.unparked);
}
