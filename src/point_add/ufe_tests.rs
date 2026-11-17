//! Ufezuegle (upward page converter) unit tests, run in a tree whose PAGE_D is the working page D > 16:
//!   cargo test --release --bin build_circuit -- ufe_ --nocapture --test-threads=4
//! Population: explicit frame states at the two cut boundaries (tools/ufe_states.py: Euclid walks + the spec2 cut rule and
//! ring layout; up to 1,024 states per (cut, E, parity class of B / the explicit cofactor)), env UFE_STATES (default the
//! lane file). Each state runs on the tree's own gate lists (page_in at 16 and at D, ufe_fwd, ufe_back) simulated
//! bit-parallel on 64 shots with random passenger (the dirty pool) and random parity; every lane is checked:
//!   ufe_up_start   page_in(431, 16) + narrow + ufe_fwd (CONV_K_S) == page_in(431, D) + narrow, by role (ring X / ring Y by
//!                  position, VA / VB / SC, passenger, parity, code), every other lane 0
//!   ufe_down_tail  page_in(79, D) + narrow + ufe_back_gates (CONV_K_T) == page_in(79, 16) + narrow, by role
//!   ufe_roundtrip  page_in(tt, 16) + narrow + ufe_fwd + ufe_back (+ relabel) == page_in(tt, 16) + narrow on EVERY label,
//!                  tt = 431 and 79 (K_S up, K_T down: the production pair), i.e. 16 -> D -> 16 is the identity
//! A shot counts only if the reference page exists (VA0 or VB0 = 1) and every word has more than D bits (the census
//! short-word class, which fails at D whatever the converter does); the others are reported, not judged.
use super::*;

struct St { tt: i32, e: i32, cls: String, minlen: usize, x: Vec<u8>, y: Vec<u8>, h: (u8, u8) }

fn hexbits(h: &str, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    for (i, c) in h.chars().rev().enumerate() {
        let d = c.to_digit(16).unwrap() as u8;
        for b in 0..4 { if 4 * i + b < n { v[4 * i + b] = (d >> b) & 1; } }
    }
    v
}
fn load(tt: i32) -> Vec<St> {
    let path = std::env::var("UFE_STATES").unwrap_or("/Users/odin/ecdsa-cliff758-20261115/lanes/ufezuegle/census/ufe_states.txt".into());
    let txt = std::fs::read_to_string(&path).expect("UFE_STATES file");
    let cap: usize = std::env::var("UFE_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(usize::MAX);
    let mut out = vec![];
    for l in txt.lines() {
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() != 8 || f[0].parse::<i32>().unwrap() != tt { continue; }
        out.push(St { tt, e: f[1].parse().unwrap(), cls: f[2].into(), minlen: f[3].parse().unwrap(), x: hexbits(f[4], W), y: hexbits(f[5], W), h: (f[6].parse().unwrap(), f[7].parse().unwrap()) });
        if out.len() >= cap { break; }
    }
    out
}
fn mk(dp: usize) -> Machine {
    let mut b = B { free: vec![], next: 512, gates: vec![] };
    for _ in 0..ZB { b.alloc(); }
    let xl: Vec<u32> = (0..256).collect();
    let pas: Vec<u32> = (256..512).collect();
    let y0 = b.alloc();
    let par = xl[N - 1];
    let y1 = b.alloc();
    let mut y = vec![y0, y1];
    y.extend_from_slice(&xl[..N - 1]);
    let x: Vec<u32> = (0..W).map(|_| b.alloc()).collect();
    let e: Vec<u32> = (0..EB).map(|_| b.alloc()).collect();
    let mut dirty = pas.clone();
    dirty.extend_from_slice(&x);
    dirty.extend_from_slice(&y);
    let mut mc = Machine { b, dirty, pas, x, y, e, par, pg: vec![], wr: W, freed: vec![], w4: NONE, w1: NONE, cv_t2: vec![], cv_freed: vec![], cv_x16: vec![], cv_y16: vec![], cv_pg16: vec![], e3t: false };
    mc.pg = (0..4 * dp + 1).map(|_| mc.b.alloc()).collect();
    mc.pg.push(ZB_LANE);
    mc
}
fn narrow(mc: &mut Machine, d: usize) {
    let wh = W - 2 * d;
    mc.freed = mc.x[wh..].to_vec();
    mc.freed.extend_from_slice(&mc.y[wh..]);
    mc.x.truncate(wh);
    mc.y.truncate(wh);
    mc.wr = wh;
    if CAD4 { mc.w1 = mc.freed[0]; }
}
fn sim(g: &[G], st: &mut [u64]) {
    for x in g {
        assert!(x.0 != MAC, "MAC macro in a unit-test list");
        if x.2 != NONE {
            let t = gl_loader::lane_of(x.2) as usize;
            st[t] ^= st[x.0 as usize] & st[x.1 as usize];
        } else if x.1 != NONE {
            st[x.1 as usize] ^= st[x.0 as usize];
        } else {
            st[x.0 as usize] = !st[x.0 as usize];
        }
    }
}
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15); let mut z = self.0; z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9); z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB); z ^ (z >> 31) } }
/// initial explicit state of a batch on machine mc (labels), shots 0..chunk.len()
fn init(mc: &Machine, chunk: &[St], rng: &mut Rng, nlab: usize) -> Vec<u64> {
    let mut st = vec![0u64; nlab];
    for (s, c) in chunk.iter().enumerate() {
        let bit = 1u64 << s;
        for i in 0..W { if c.x[i] == 1 { st[mc.x[i] as usize] |= bit; } if c.y[i] == 1 { st[mc.y[i] as usize] |= bit; } }
        if c.h.0 == 1 { st[mc.e[0] as usize] |= bit; }
        if c.h.1 == 1 { st[mc.e[1] as usize] |= bit; }
    }
    let m = if chunk.len() == 64 { u64::MAX } else { (1u64 << chunk.len()) - 1 };
    for &p in &mc.pas { st[p as usize] = rng.next() & m; }
    st[mc.par as usize] = rng.next() & m;
    st
}
/// role-by-role comparison of machine a (lists xa, ya, page pa of width d) against reference b; every label of `a` outside the
/// roles must be 0. Returns the mask of shots that differ.
#[allow(clippy::too_many_arguments)]
fn cmp_roles(sa: &[u64], xa: &[u32], ya: &[u32], pa: &[u32], sb: &[u64], xb: &[u32], yb: &[u32], pb: &[u32], d: usize, mc: &Machine, nlab_a: usize, why: &mut String) -> u64 {
    let mut dm = 0u64;
    let mut note = |dm: &mut u64, v: u64, what: &str| { if v != 0 && why.is_empty() { *why = what.to_string(); } *dm |= v; };
    assert!(xa.len() == xb.len() && ya.len() == yb.len());
    for i in 0..xa.len() { note(&mut dm, sa[xa[i] as usize] ^ sb[xb[i] as usize], &format!("ring X {i}")); }
    for i in 0..ya.len() { note(&mut dm, sa[ya[i] as usize] ^ sb[yb[i] as usize], &format!("ring Y {i}")); }
    for j in 0..3 * d { note(&mut dm, sa[pa[j] as usize] ^ sb[pb[j] as usize], &format!("page {} bit {}", ["VA", "VB", "SC"][j / d], j % d)); }
    for &q0 in mc.pas.iter().chain(mc.e.iter()).chain([mc.par].iter()) { note(&mut dm, sa[q0 as usize] ^ sb[q0 as usize], "passenger / code / parity"); }
    let roles: std::collections::HashSet<u32> = xa.iter().chain(ya.iter()).chain(pa[..3 * d].iter()).chain(mc.pas.iter()).chain(mc.e.iter()).chain([mc.par].iter()).copied().collect();
    for q0 in 0..nlab_a as u32 { if !roles.contains(&q0) { note(&mut dm, sa[q0 as usize], &format!("non-role lane {q0} not 0")); } }
    dm
}
fn valid(chunk: &[St], sref: &[u64], pref: &[u32], d: usize) -> u64 {
    let mut v = sref[pref[0] as usize] | sref[pref[d] as usize]; // the reference page exists: VA0 or VB0
    for (s, c) in chunk.iter().enumerate() { if c.minlen <= d { v &= !(1u64 << s); } }
    if chunk.len() < 64 { v &= (1u64 << chunk.len()) - 1; }
    v
}
fn report(tag: &str, tot: usize, judged: u64, bad: u64, cls: &BTreeMap<String, (u64, u64)>, es: &BTreeSet<i32>, firstwhy: &str) {
    eprintln!("UFETEST {tag} D={} mode={} states {tot} judged {judged} FAIL {bad} | per class (judged, fail) {:?} | E values {:?}{}", PAGE_D, ufe_mode(), cls, es, if firstwhy.is_empty() { String::new() } else { format!(" | first: {firstwhy}") });
}

fn up_at(tt: i32) -> u64 {
    let d = PAGE_D;
    let sts = load(tt);
    let mut rng = Rng(0x5eed ^ tt as u64);
    let (mut judged, mut bad) = (0u64, 0u64);
    let mut cls: BTreeMap<String, (u64, u64)> = BTreeMap::new();
    let mut es = BTreeSet::new();
    let mut why = String::new();
    for chunk in sts.chunks(64) {
        // A: page_in at 16, narrow, the upward converter
        let mut a = mk(PAGE_DI);
        let g1 = a.page_in_d(tt, PAGE_DI);
        narrow(&mut a, PAGE_DI);
        a.b.gates.clear();
        a.ufe_fwd(tt);
        let g2 = std::mem::take(&mut a.b.gates);
        let nla = a.b.next as usize;
        // B: the reference at D (same labels for rings, passenger, code: the machines allocate in the same order up to the page)
        let mut b = mk(d);
        let gb = b.page_in_d(tt, d);
        narrow(&mut b, d);
        let nlb = b.b.next as usize;
        let mut sa = init(&mk(PAGE_DI), chunk, &mut rng, nla.max(nlb));
        let mut sb = sa.clone();
        sim(&g1, &mut sa);
        sim(&g2, &mut sa);
        sim(&gb, &mut sb);
        let v = valid(chunk, &sb, &b.pg, d);
        let mut w = String::new();
        let dm = cmp_roles(&sa, &a.x, &a.y, &a.pg, &sb, &b.x, &b.y, &b.pg, d, &a, nla, &mut w) & v;
        if dm != 0 && why.is_empty() { why = format!("{w} (E {})", chunk[dm.trailing_zeros() as usize].e); }
        for (s, c) in chunk.iter().enumerate() {
            if (v >> s) & 1 == 0 { continue; }
            let f = (dm >> s) & 1;
            let ent = cls.entry(c.cls.clone()).or_insert((0, 0)); ent.0 += 1; ent.1 += f;
            es.insert(c.e);
        }
        judged += v.count_ones() as u64;
        bad += dm.count_ones() as u64;
    }
    report(&format!("up tt={tt} (page_in16 + ufe_fwd == page_in{d})"), sts.len(), judged, bad, &cls, &es, &why);
    bad
}

fn down_at(tt: i32) -> u64 {
    let d = PAGE_D;
    let nl = d - PAGE_DI;
    let mode = ufe_mode();
    let sts = load(tt);
    let mut rng = Rng(0xd0e ^ tt as u64);
    let (mut judged, mut bad) = (0u64, 0u64);
    let mut cls: BTreeMap<String, (u64, u64)> = BTreeMap::new();
    let mut es = BTreeSet::new();
    let mut why = String::new();
    for chunk in sts.chunks(64) {
        // B: page_in at D, narrow, the downward converter with a start-like bookkeeping (spares 0, F / ZB 0, T2 fresh)
        let mut b = mk(d);
        let gb = b.page_in_d(tt, d);
        narrow(&mut b, d);
        let fresh = |b: &mut Machine, k: usize| -> Vec<u32> { (0..k).map(|_| b.b.alloc()).collect() };
        let mut spares = fresh(&mut b, nl);
        if mode >= 1 { spares[0] = b.pg[4 * d]; }
        let tops = fresh(&mut b, 4 * d);
        b.cv_t2 = fresh(&mut b, PAGE_DI);
        b.cv_pg16 = fresh(&mut b, 4 * PAGE_DI + 2);
        UFE.with(|u| { let mut u = u.borrow_mut(); u.spares = spares.clone(); u.tops = tops.clone(); u.mode = mode; });
        b.b.gates.clear();
        let (xe, ye, pg16) = b.ufe_back_gates(tt);
        let g2 = std::mem::take(&mut b.b.gates);
        let nlb = b.b.next as usize;
        // A: the reference at 16
        let mut a = mk(PAGE_DI);
        let ga = a.page_in_d(tt, PAGE_DI);
        narrow(&mut a, PAGE_DI);
        let nla = a.b.next as usize;
        let mut sb = init(&mk(PAGE_DI), chunk, &mut rng, nla.max(nlb));
        let mut sa = sb.clone();
        sim(&gb, &mut sb);
        sim(&g2, &mut sb);
        sim(&ga, &mut sa);
        let mut v = sa[a.pg[0] as usize] | sa[a.pg[PAGE_DI] as usize];
        for (s, c) in chunk.iter().enumerate() { if c.minlen <= d { v &= !(1u64 << s); } }
        if chunk.len() < 64 { v &= (1u64 << chunk.len()) - 1; }
        let mut w = String::new();
        let dm = cmp_roles(&sb, &xe, &ye, &pg16, &sa, &a.x, &a.y, &a.pg, PAGE_DI, &b, nlb, &mut w) & v;
        if dm != 0 && why.is_empty() { why = format!("{w} (E {})", chunk[dm.trailing_zeros() as usize].e); }
        for (s, c) in chunk.iter().enumerate() {
            if (v >> s) & 1 == 0 { continue; }
            let f = (dm >> s) & 1;
            let ent = cls.entry(c.cls.clone()).or_insert((0, 0)); ent.0 += 1; ent.1 += f;
            es.insert(c.e);
        }
        judged += v.count_ones() as u64;
        bad += dm.count_ones() as u64;
    }
    report(&format!("down tt={tt} (page_in{d} + ufe_back == page_in16)"), sts.len(), judged, bad, &cls, &es, &why);
    bad
}

fn round_at(tt: i32) -> u64 {
    let d = PAGE_D;
    let sts = load(tt);
    let mut rng = Rng(0x7007 ^ tt as u64);
    let (mut judged, mut bad) = (0u64, 0u64);
    let mut cls: BTreeMap<String, (u64, u64)> = BTreeMap::new();
    let mut es = BTreeSet::new();
    let mut why = String::new();
    for chunk in sts.chunks(64) {
        let mut a = mk(PAGE_DI);
        let g1 = a.page_in_d(tt, PAGE_DI);
        narrow(&mut a, PAGE_DI);
        let (x16, y16, pg16, fr16) = (a.x.clone(), a.y.clone(), a.pg.clone(), a.freed.clone());
        a.b.gates.clear();
        a.ufe_fwd(tt);
        a.ufe_back(tt);
        let g2 = std::mem::take(&mut a.b.gates);
        // the relabel restores the label SETS of ring X and ring Y (positions follow the tail converter's lists, as in the
        // parent's conv_back) and the page / freed lists by position
        assert!(a.pg == pg16 && a.freed == fr16, "ufe round trip: page / freed label lists differ");
        let sx: BTreeSet<u32> = a.x.iter().copied().collect(); let sy: BTreeSet<u32> = a.y.iter().copied().collect();
        assert!(sx == x16.iter().copied().collect::<BTreeSet<u32>>() && sy == y16.iter().copied().collect::<BTreeSet<u32>>(), "ufe round trip: ring label sets differ");
        let nla = a.b.next as usize;
        let mut s0 = init(&mk(PAGE_DI), chunk, &mut rng, nla);
        sim(&g1, &mut s0);
        let mut s1 = s0.clone();
        sim(&g2, &mut s1);
        let mut v = s0[pg16[0] as usize] | s0[pg16[PAGE_DI] as usize];
        for (s, c) in chunk.iter().enumerate() { if c.minlen <= d { v &= !(1u64 << s); } }
        if chunk.len() < 64 { v &= (1u64 << chunk.len()) - 1; }
        let mut w = String::new();
        let dm = cmp_roles(&s1, &a.x, &a.y, &a.pg, &s0, &x16, &y16, &pg16, PAGE_DI, &a, nla, &mut w) & v;
        if dm != 0 && why.is_empty() { why = format!("{w} (E {})", chunk[dm.trailing_zeros() as usize].e); }
        for (s, c) in chunk.iter().enumerate() {
            if (v >> s) & 1 == 0 { continue; }
            let f = (dm >> s) & 1;
            let ent = cls.entry(c.cls.clone()).or_insert((0, 0)); ent.0 += 1; ent.1 += f;
            es.insert(c.e);
        }
        judged += v.count_ones() as u64;
        bad += dm.count_ones() as u64;
    }
    report(&format!("roundtrip tt={tt} (16 -> {d} -> 16, every label)"), sts.len(), judged, bad, &cls, &es, &why);
    bad
}

#[test]
fn ufe_up_start() { if PAGE_D <= PAGE_DI { return; } assert_eq!(up_at(CUT_S - 1), 0); }
#[test]
fn ufe_down_tail() { if PAGE_D <= PAGE_DI { return; } assert_eq!(down_at(CUT_T - 1), 0); }
#[test]
fn ufe_roundtrip_start() { if PAGE_D <= PAGE_DI { return; } assert_eq!(round_at(CUT_S - 1), 0); }
#[test]
fn ufe_roundtrip_tail() { if PAGE_D <= PAGE_DI { return; } assert_eq!(round_at(CUT_T - 1), 0); }
/// informational (not production geometry): the upward converter at the tail and the downward one at the start
#[test]
fn ufe_cross_geometry() { if PAGE_D <= PAGE_DI { return; } let a = up_at(CUT_T - 1); let b = down_at(CUT_S - 1); eprintln!("UFETEST cross-geometry (K_S at tt 79, K_T at tt 431): up fails {a}, down fails {b} (information only)"); }

/// r2 export (SPEC17): the 16 <-> 17 converter lists in phys765 labels (mode 0 and mode 2), written as text gate lists to
/// env UFE_EXPORT_DIR (default ../r2/export). Labels of the D16 interface -> phys765 by role (mod.rs phys765()); the dirty
/// pool is the passenger only, so no lane outside the 765 map is named. Down = conv_gates_dd(17, 16) at tt 79 with CONV_K_T
/// on the canonical D17 labels, then CX swaps back onto the D16 positions.
#[test]
fn ufe_export17() {
    if PAGE_D != 17 { return; }
    let dir = std::env::var("UFE_EXPORT_DIR").unwrap_or("/Users/odin/ecdsa-cliff758-20261115/lanes/ufezuegle/r2/export".into());
    std::fs::create_dir_all(&dir).unwrap();
    let (d, dl, nl) = (17usize, 16usize, 1usize);
    for mode in [0u8, 2] {
        for (tt, up) in [(CUT_S - 1, true), (CUT_T - 1, false)] {
            let mut a = mk(dl);
            narrow(&mut a, dl);
            a.dirty = a.pas.clone();
            let mut ph: HashMap<u32, u32> = HashMap::new();
            for (i, &q0) in a.x.iter().enumerate() { ph.insert(q0, 514 + i as u32); }
            for (i, &q0) in a.y.iter().enumerate() { ph.insert(q0, i as u32); }
            for j in 0..16 { ph.insert(a.pg[j], 225 + j as u32); ph.insert(a.pg[32 + j], 739 + j as u32); }
            for j in 0..14 { ph.insert(a.pg[16 + j], 241 + j as u32); }
            ph.insert(a.pg[30], 512); ph.insert(a.pg[31], 513);
            ph.insert(a.pg[64], 764); ph.insert(a.pg[65], 763);
            ph.insert(a.e[0], 755); ph.insert(a.e[1], 756); ph.insert(a.par, 255);
            for (i, &q0) in a.pas.iter().enumerate() { ph.insert(q0, 256 + i as u32); }
            for i in 0..6 { ph.insert(a.freed[i], 757 + i as u32); }
            let (kx, ky) = if up { CONV_K_S } else { CONV_K_T };
            let (ks, kys) = CONV_K_S; // the canonical D17 map is the start converter's split
            let (x16, y16, pg16) = (a.x.clone(), a.y.clone(), a.pg.clone());
            let (nx, ny) = (x16[ks..ks + 2 * nl].to_vec(), y16[kys..kys + 2 * nl].to_vec());
            let xd: Vec<u32> = x16[..ks].iter().chain(x16[ks + 2 * nl..].iter()).copied().collect();
            let yd: Vec<u32> = y16[..kys].iter().chain(y16[kys + 2 * nl..].iter()).copied().collect();
            let spares: Vec<u32> = vec![ny[0]];
            let t2x: Vec<u32> = (0..nl).map(|_| a.b.alloc()).collect();
            let mut pgd: Vec<u32> = pg16[0..dl].to_vec(); pgd.push(nx[1]);
            pgd.extend_from_slice(&pg16[dl..2 * dl]); pgd.push(ny[1]);
            pgd.extend_from_slice(&pg16[2 * dl..3 * dl]); pgd.push(nx[0]);
            pgd.extend_from_slice(&pg16[3 * dl..4 * dl]); pgd.extend_from_slice(&t2x);
            pgd.push(pg16[4 * dl]); pgd.push(pg16[4 * dl + 1]);
            let tops: Vec<u32> = (0..4 * d).map(|_| a.b.alloc()).collect();
            let xf: Vec<u32> = xd.iter().chain(tops[..2 * d].iter()).copied().collect();
            let yf: Vec<u32> = yd.iter().chain(tops[2 * d..].iter()).copied().collect();
            let (g, xe, ye) = a.conv_gates_dd(d, dl, mode, tt, &xf, &yf, &pgd, &spares, (kx, ky));
            let mut gl: GL = if up { assert!(xe == x16 && ye == y16); rev(&g) } else { g };
            if !up {
                // CX swaps: content of label xe[i] -> x16[i], ye[i] -> y16[i]
                let mut dest: HashMap<u32, u32> = HashMap::new();
                for (c, t) in [(&xe, &x16), (&ye, &y16)] { for (&p, &q) in c.iter().zip(t.iter()) { if p != q { dest.insert(p, q); } } }
                let mut keys: Vec<u32> = dest.keys().copied().collect(); keys.sort();
                let mut done = std::collections::HashSet::new();
                for &s0 in &keys {
                    if done.contains(&s0) { continue; }
                    let mut c = vec![s0]; let mut q0 = dest[&s0];
                    while q0 != s0 { c.push(q0); q0 = dest[&q0]; }
                    for &l in &c { done.insert(l); }
                    for &sj in &c[1..] { gl.extend([G(s0, sj, NONE), G(sj, s0, NONE), G(s0, sj, NONE)]); }
                }
            }
            let mut txt = String::new();
            let mut used: BTreeSet<u32> = BTreeSet::new();
            for x in &gl {
                assert!(x.0 != MAC);
                let m = |q0: u32| -> u32 { *ph.get(&gl_loader::lane_of(q0)).unwrap_or_else(|| panic!("export: label {q0} outside the 765 map")) };
                if x.2 != NONE { txt += &format!("2 {} {} {}\n", m(x.0), m(x.1), m(x.2)); for q0 in [x.0, x.1, x.2] { used.insert(m(q0)); } }
                else if x.1 != NONE { txt += &format!("1 {} {}\n", m(x.0), m(x.1)); used.insert(m(x.0)); used.insert(m(x.1)); }
                else { txt += &format!("0 {}\n", m(x.0)); used.insert(m(x.0)); }
            }
            let name = format!("{}/{}17_m{}.txt", dir, if up { "up" } else { "dn" }, mode);
            std::fs::write(&name, txt).unwrap();
            let outside: Vec<u32> = used.iter().copied().filter(|&p| p >= 757).collect();
            eprintln!("UFEEXPORT {name}: {} gates, {} CCX, lanes named outside the 757 D16 data lanes: {:?}", gl.len(), gl.iter().filter(|x| x.2 != NONE).count(), outside);
        }
    }
}
