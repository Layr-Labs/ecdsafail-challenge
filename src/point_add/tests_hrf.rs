//! q765-HRF tests: q-box on real walk states (classical simulation, 64 shots).
use super::builder::B;
use super::frogdrop_sched::{N, p, sample};
use super::hrf::*;
use crate::circuit::QubitId;

fn put(w: &mut [u64], qs: &[QubitId], s: usize, v: &N) { for (i, &q) in qs.iter().enumerate() { if v.bit(i) { w[q.0 as usize] |= 1 << s; } } }
fn get(w: &[u64], qs: &[QubitId], s: usize) -> N { let mut v = N::ZERO; for (i, &q) in qs.iter().enumerate() { if (w[q.0 as usize] >> s) & 1 == 1 { v |= N::from(1u64) << i; } } v }
fn bl(x: &N) -> usize { x.bit_len() }

/// circuit model of the q-box quotient (matches hrf/census TRUNC model)
fn model(rj: &N, tj: &N, tj1: &N) -> N {
    let one = N::from(1u64);
    let s = bl(rj) - W; let sx = bl(tj1);
    let uu = *rj >> s;
    let (tt, tt1) = if sx >= WT { (*tj >> (sx - WT), *tj1 >> (sx - WT)) } else { (*tj << (WT - sx), *tj1 << (WT - sx)) };
    let d = bl(rj) + sx - 256;
    let row = |t: &N| { let mut acc = N::ZERO; for i in 0..WT { if t.bit(i) { acc += (uu << i) >> LT; } } acc };
    let x1 = row(&tt1); let x0 = row(&tt);
    let width = W + WT - LT - d;
    let dr = (!x1) & ((one << width) - one);
    let q = x0 / dr;
    if q >= (one << QC) { N::MAX } else { q }
}

fn qbox_case(col: usize, seed: u64) {
    let sc = super::pointadd_frogdrop::sched();
    let e = &sc.cols[col];
    let env = QEnv { sz: (e.sz.0.min(256), e.sz.1.min(256)), sy: (e.sy.0.min(255), e.sy.1.min(255)), sx: (e.smax.0.min(138), e.smax.1.min(138)) };
    let (n, nq, qw) = (288usize, 138usize, 116usize);
    let mut b = B::new();
    let ring = b.alloc_n(n); let q = b.alloc_n(nq); let sy = b.alloc_n(8); let sx = b.alloc_n(8);
    let cache = b.alloc_n(QC); let base = b.alloc_n(62); let probe_extra = b.alloc_n(0); let dirty = b.alloc_n(64);
    let _ = probe_extra;
    let mut late = ring_gap(&ring); late.extend(q_free(&q, qw, &env));
    let l = carve(&base, &late);
    let probe_bank: Vec<QubitId> = base[14..].to_vec();
    let t0 = b.tof;
    qbox(&mut b, &ring, &q, qw, &sy, &sx, &env, &l, &cache, &probe_bank, &dirty);
    b.finish_fold();
    let tq = b.census().1 - 0 * t0;
    eprintln!("HRF qbox col {col}: env {:?} toffoli {tq} (incl. erase box, mode 0), lanes dr/nr {} + bank {}, width {}", env, 2 * RW, l.bank.len(), b.width());
    // shots
    let pp = p();
    let xs = sample(4000, seed);
    let mut shots = vec![];
    for x in xs {
        let (mut r, mut t) = (vec![pp, x], vec![N::ZERO, N::from(1u64)]);
        while r.len() < col + 6 { let m = r.len(); let qq = r[m - 2] / r[m - 1]; r.push(r[m - 2] - qq * r[m - 1]); t.push(t[m - 2] + qq * t[m - 1]); }
        let j = col + 1;
        let (rj, tj, tj1) = (r[j], t[j], t[j + 1]);
        if bl(&rj) < env.sz.0 || bl(&rj) > env.sz.1 || bl(&tj) < env.sy.0 || bl(&tj) > env.sy.1 || bl(&tj1) < env.sx.0 || bl(&tj1) > env.sx.1 { continue; }
        shots.push((rj, tj, tj1, r[j] / r[j + 1]));
        if shots.len() == 64 { break; }
    }
    assert_eq!(shots.len(), 64);
    let dv: Vec<N> = (0..64).map(|s| N::from(0x9e3779b97f4a7c15u64.wrapping_mul(s as u64 + 7))).collect();
    let res = super::tests_frogdrop::run(&b.ops, b.width() as usize, &|w| {
        for (s, (rj, tj, tj1, _)) in shots.iter().enumerate() {
            put(w, &ring[..257], s, rj);
            for i in 0..bl(tj) { if tj.bit(i) { w[ring[n - 1 - i].0 as usize] |= 1 << s; } }
            put(w, &q, s, tj1);
            put(w, &sy, s, &N::from(bl(tj) as u64));
            put(w, &dirty, s, &dv[s]);
        }
    });
    assert_eq!(res.phase, 0, "phase garbage");
    let mut wrong = 0;
    for (s, (rj, tj, tj1, qt)) in shots.iter().enumerate() {
        let got = get(&res.q, &cache, s);
        assert_eq!(got, model(rj, tj, tj1), "shot {s}: cache != model");
        if got != *qt { wrong += 1; }
        for l2 in 0..n {
            let i = n - 1 - l2;
            let want = (l2 < 257 && rj.bit(l2)) || (i < bl(tj) && tj.bit(i));
            assert_eq!((res.q[ring[l2].0 as usize] >> s) & 1 == 1, want, "shot {s}: ring lane {l2}");
        }
        assert_eq!(get(&res.q, &q, s), *tj1, "shot {s}: Q");
        assert_eq!(get(&res.q, &sy, s), N::from(bl(tj) as u64), "shot {s}: sy");
        assert_eq!(get(&res.q, &sx, s), N::ZERO, "shot {s}: sx");
        assert_eq!(get(&res.q, &base, s), N::ZERO, "shot {s}: base");
        assert_eq!(get(&res.q, &dirty, s), dv[s], "shot {s}: dirty");
    }
    eprintln!("HRF qbox col {col}: 64 shots exact vs model, {wrong} differ from the true quotient");
}

#[test]
fn hrf_qbox_cols() {
    for &c in &[1usize, 9, 17] { qbox_case(c, 7 + c as u64); }
}

#[test]
fn hrf_qbox_debug() {
    let col = 1usize;
    let sc = super::pointadd_frogdrop::sched();
    let e = &sc.cols[col];
    let env = QEnv { sz: (e.sz.0.min(256), e.sz.1.min(256)), sy: (e.sy.0.min(255), e.sy.1.min(255)), sx: (e.smax.0.min(138), e.smax.1.min(138)) };
    let (n, nq, qw) = (288usize, 138usize, 116usize);
    for upto in 0..3u8 {
    let mut b = B::new();
    let ring = b.alloc_n(n); let q = b.alloc_n(nq); let sy = b.alloc_n(8); let sx = b.alloc_n(8);
    let cache = b.alloc_n(QC); let base = b.alloc_n(62); let dirty = b.alloc_n(64);
    let mut late = ring_gap(&ring); late.extend(q_free(&q, qw, &env));
    let l = carve(&base, &late);
    let probe_bank: Vec<QubitId> = base[14..].to_vec();
    phase_a(&mut b, &ring, &q, qw, &sy, &sx, &env, &l, &probe_bank, &dirty);
    if upto > 0 { phase_b(&mut b, &ring, &q, qw, &sx, &env, &l, &cache, &dirty, upto); }
    b.finish_fold();
    let pp = p();
    let xs = sample(200, 99);
    let mut shots = vec![];
    for x in xs {
        let (mut r, mut t) = (vec![pp, x], vec![N::ZERO, N::from(1u64)]);
        while r.len() < col + 6 { let m = r.len(); let qq = r[m - 2] / r[m - 1]; r.push(r[m - 2] - qq * r[m - 1]); t.push(t[m - 2] + qq * t[m - 1]); }
        let j = col + 1; shots.push((r[j], t[j], t[j + 1]));
        if shots.len() == 64 { break; }
    }
    let res = super::tests_frogdrop::run(&b.ops, b.width() as usize, &|w| {
        for (s, (rj, tj, tj1)) in shots.iter().enumerate() {
            put(w, &ring[..257], s, rj);
            for i in 0..bl(tj) { if tj.bit(i) { w[ring[n - 1 - i].0 as usize] |= 1 << s; } }
            put(w, &q, s, tj1); put(w, &sy, s, &N::from(bl(tj) as u64));
        }
    });
    for s in 0..3 {
        let (rj, tj, tj1) = &shots[s];
        let sxv = bl(tj1); let sh = bl(rj) - W;
        let uu = *rj >> sh;
        let (tt, tt1) = if sxv >= WT { (*tj >> (sxv - WT), *tj1 >> (sxv - WT)) } else { (*tj << (WT - sxv), *tj1 << (WT - sxv)) };
        let got_u = get(&res.q, &ring[n - W..], s);
        let t0l: Vec<QubitId> = (0..WT).map(|i| ring[31 + WT - i]).collect();
        let got_t0 = get(&res.q, &t0l, s);
        let got_t1 = get(&res.q, &q[qw - WT..qw], s);
        eprintln!("upto {upto} shot {s}: bl r {} bl tj {} bl tj1 {} | U ok {} T0 ok {} (got {:x} want {:x}) T1 ok {} | sx {} dl {} szr {} gap0 {}",
            bl(rj), bl(tj), sxv, got_u == uu, got_t0 == tt, got_t0, tt, got_t1 == tt1, get(&res.q,&sx,s), get(&res.q,&[l.dl],s), get(&res.q,&l.szr,s), get(&res.q,&ring[..29],s));
        if upto >= 1 { let row = |t: &N| { let mut acc = N::ZERO; for i in 0..WT { if t.bit(i) { acc += (uu << i) >> LT; } } acc };
            eprintln!("   Nr ok {} (got {:x} want {:x})", get(&res.q,&l.nr,s)==row(&tt), get(&res.q,&l.nr,s), row(&tt));
            if upto >= 2 { let one=N::from(1u64); let d = bl(rj)+sxv-256; let dr=(!row(&tt1))&((one<<(RW-d))-one); eprintln!("   Dr ok {}", get(&res.q,&l.dr,s)==dr); } }
    }
    }
}

#[test]
fn hrf_qbox_cost() {
    let sc = super::pointadd_frogdrop::sched();
    for &col in &[1usize, 5, 9, 13, 17] {
        let e = &sc.cols[col];
        let env = QEnv { sz: (e.sz.0.min(256), e.sz.1.min(256)), sy: (e.sy.0.min(255), e.sy.1.min(255)), sx: (e.smax.0.min(138), e.smax.1.min(138)) };
        let (n, nq, qw) = (288usize, 138usize, 116usize);
        let mut b = B::new();
        let ring = b.alloc_n(n); let q = b.alloc_n(nq); let sy = b.alloc_n(8); let sx = b.alloc_n(8);
        let cache = b.alloc_n(QC); let base = b.alloc_n(62); let dirty = b.alloc_n(64);
        let mut late = ring_gap(&ring); late.extend(q_free(&q, qw, &env));
        let l = carve(&base, &late);
        let pb: Vec<QubitId> = base[14..].to_vec();
        let c = |b: &mut B| { b.finish_fold(); b.census().1 };
        let a = { b.begin(); phase_a(&mut b, &ring, &q, qw, &sy, &sx, &env, &l, &pb, &dirty); b.end() };
        b.play(&a, false); let ta = c(&mut b);
        let (dp, np) = phase_b(&mut b, &ring, &q, qw, &sx, &env, &l, &cache, &dirty, 9); let tb = c(&mut b);
        let t_np = np.iter().filter(|g| matches!(g, super::builder::G::Ccx(..) | super::builder::G::AndC(..))).count();
        let t_dp = dp.iter().filter(|g| matches!(g, super::builder::G::Ccx(..) | super::builder::G::AndC(..))).count();
        b.begin();
        for k in 0..QC { super::frogdrop::cadd_tail_and_mixed(&mut b, cache[k], &l.nr[k..], &l.dr[..RW - k], &[], l.c0, l.h, &[], &dirty, &[]); }
        b.play(&dp, true); b.play(&np, true);
        let er = b.end();
        let t_e = er.iter().filter(|g| matches!(g, super::builder::G::Ccx(..) | super::builder::G::AndC(..))).count();
        eprintln!("HRF qbox cost col {col}: phaseA {ta} (x2 with inverse), phaseB {} (Nprod {t_np}, Dprod {t_dp}, division {}), erase box {t_e} | forward ~ {} inverse ~ {}",
            tb - ta, tb - ta - t_np as u64 - t_dp as u64, 2 * ta + (tb - ta), 2 * ta + (tb - ta) + t_e as u64);
    }
}

fn pair_case(col: usize, seed: u64, fused: bool) {
    use super::frogdrop_col::{Fd, ColScr};
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(&super::pointadd_frogdrop::sched());
    let (cp1, cp2) = (&cols[col], &cols[col + 1]);
    assert!(pair_ok(cp1, cp2), "pair_ok false at col {col}");
    let n = 288usize;
    let mut b = B::new();
    let mut fd = Fd { ring: b.alloc_n(n), q: b.alloc_n(138), sy: b.alloc_n(8), sx: b.alloc_n(8), ph: b.alloc(), cnt: b.alloc_n(7) };
    let pool = b.alloc_n(59);
    let dirty = b.alloc_n(128);
    let (sy0, sx0) = (fd.sy.clone(), fd.sx.clone());
    if fused {
        pair(&mut b, &mut fd, cp1, cp2, &pool, &dirty);
    } else {
        for cp in [cp1, cp2] {
            let sc = ColScr::carve(&pool, &fd.sx, &dirty, super::pointadd_frogdrop::kp(), super::pointadd_frogdrop::QB, super::pointadd_frogdrop::TAIL);
            super::frogdrop_col::column(&mut b, &mut fd, cp, &sc);
        }
    }
    b.finish_fold();
    let tof = b.census().1;
    let pp = p();
    let xs = sample(20000, seed);
    let mut shots = vec![];
    let inenv = |c: &super::frogdrop_col::ColPar, z: &N, y: &N, x2: &N| bl(z) >= c.sz.0 && bl(z) <= c.sz.1 && bl(y) >= c.sy.0 && bl(y) <= c.sy.1 && bl(x2).max(bl(y)) <= c.smax.1 && bl(x2).max(bl(y)) >= c.smax.0;
    for x in xs {
        let (mut r, mut t) = (vec![pp, x], vec![N::ZERO, N::from(1u64)]);
        while r.len() < col + 8 { let m = r.len(); let qq = r[m - 2] / r[m - 1]; r.push(r[m - 2] - qq * r[m - 1]); t.push(t[m - 2] + qq * t[m - 1]); }
        let j = col + 1;
        if !inenv(cp1, &r[j], &t[j], &t[j + 1]) || !inenv(cp2, &r[j + 1], &t[j + 1], &t[j + 2]) { continue; }
        if model(&r[j], &t[j], &t[j + 1]) != r[j] / r[j + 1] { continue; }
        shots.push((r.clone(), t.clone()));
        if shots.len() == 64 { break; }
    }
    assert_eq!(shots.len(), 64);
    let dv: Vec<N> = (0..64).map(|s| N::from(0x9e3779b97f4a7c15u64.wrapping_mul(s as u64 + 3))).collect();
    let res = super::tests_frogdrop::run(&b.ops, b.width() as usize, &|w| {
        for (s, (r, t)) in shots.iter().enumerate() {
            let j = col + 1;
            put(w, &fd.ring[..257], s, &r[j]);
            for i in 0..bl(&t[j]) { if t[j].bit(i) { w[fd.ring[n - 1 - i].0 as usize] |= 1 << s; } }
            put(w, &fd.q, s, &t[j - 1]);
            put(w, &sy0, s, &N::from(bl(&t[j]) as u64));
            put(w, &dirty, s, &dv[s]);
        }
    });
    let mut bad = 0;
    for (s, (r, t)) in shots.iter().enumerate() {
        let j = col + 1;
        let (z, qv, top) = (r[j + 2], t[j + 1], t[j + 2]);
        let mut ok = true;
        for l in 0..n { let i = n - 1 - l; let want = (l < 257 && z.bit(l)) || (i < bl(&top) && top.bit(i));
            if ((res.q[fd.ring[l].0 as usize] >> s) & 1 == 1) != want { ok = false; } }
        if get(&res.q, &fd.q, s) != qv { ok = false; }
        if get(&res.q, &fd.sy, s) != N::from(bl(&top) as u64) { ok = false; }
        if get(&res.q, &fd.sx, s) != N::ZERO { ok = false; }
        if get(&res.q, &pool, s) != N::ZERO || get(&res.q, &fd.cnt, s) != N::ZERO || get(&res.q, &[fd.ph], s) != N::ZERO { ok = false; }
        if get(&res.q, &dirty, s) != dv[s] { ok = false; }
        if !ok { bad += 1; if bad <= 3 { eprintln!("  shot {s} bad: Q {} sy {} sx {} pool0 {} ring_ok? z bl {} top bl {}", get(&res.q,&fd.q,s)==qv, get(&res.q,&fd.sy,s), get(&res.q,&fd.sx,s), get(&res.q,&pool,s)==N::ZERO, bl(&z), bl(&top)); } }
    }
    eprintln!("HRF pair col {col} fused={fused}: {tof} CCX (mode 0, erasure boxes played), phase {:#x}, {bad}/64 shots bad, sy names {}",
        res.phase, if fd.sy == sy0 { "same" } else if fd.sy == sx0 { "swapped" } else { "?" });
    assert_eq!(bad, 0);
    assert_eq!(res.phase, 0);
}

#[test]
fn hrf_pair_cols() {
    for &c in &[1usize, 9, 17] { pair_case(c, 100 + c as u64, false); pair_case(c, 100 + c as u64, true); }
}

#[test]
fn hrf_pair_debug() {
    use super::frogdrop_col::Fd;
    let col: usize = std::env::var("HRF_COL").ok().and_then(|v| v.parse().ok()).unwrap_or(9);
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(&super::pointadd_frogdrop::sched());
    let (cp1, cp2) = (&cols[col], &cols[col + 1]);
    let n = 288usize;
    let pp = p();
    let xs = sample(20000, 100 + col as u64);
    let mut shots = vec![];
    for x in xs {
        let (mut r, mut t) = (vec![pp, x], vec![N::ZERO, N::from(1u64)]);
        while r.len() < col + 8 { let m = r.len(); let qq = r[m - 2] / r[m - 1]; r.push(r[m - 2] - qq * r[m - 1]); t.push(t[m - 2] + qq * t[m - 1]); }
        let j = col + 1;
        let ok = |c: &super::frogdrop_col::ColPar, z: &N, y: &N, x2: &N| bl(z) >= c.sz.0 && bl(z) <= c.sz.1 && bl(y) >= c.sy.0 && bl(y) <= c.sy.1 && bl(x2).max(bl(y)) <= c.smax.1 && bl(x2).max(bl(y)) >= c.smax.0;
        if !ok(cp1, &r[j], &t[j], &t[j + 1]) || !ok(cp2, &r[j + 1], &t[j + 1], &t[j + 2]) { continue; }
        shots.push((r.clone(), t.clone()));
        if shots.len() == 64 { break; }
    }
    for upto in 2..=9u8 {
        let mut b = B::new();
        let mut fd = Fd { ring: b.alloc_n(n), q: b.alloc_n(138), sy: b.alloc_n(8), sx: b.alloc_n(8), ph: b.alloc(), cnt: b.alloc_n(7) };
        let pool = b.alloc_n(59); let dirty = b.alloc_n(128);
        let sy0 = fd.sy.clone();
        pair_upto(&mut b, &mut fd, cp1, cp2, &pool, &dirty, upto);
        b.finish_fold();
        let res = super::tests_frogdrop::run(&b.ops, b.width() as usize, &|w| {
            for (s, (r, t)) in shots.iter().enumerate() {
                let j = col + 1;
                put(w, &fd.ring[..257], s, &r[j]);
                for i in 0..bl(&t[j]) { if t[j].bit(i) { w[fd.ring[n - 1 - i].0 as usize] |= 1 << s; } }
                put(w, &fd.q, s, &t[j - 1]); put(w, &sy0, s, &N::from(bl(&t[j]) as u64));
            }
        });
        let s = 0; let (r, t) = &shots[s]; let j = col + 1;
        let topv = { let mut v = N::ZERO; for i in 0..120 { if (res.q[fd.ring[n-1-i].0 as usize] >> s) & 1 == 1 { v |= N::from(1u64) << i; } } v };
        let qv = get(&res.q, &fd.q[..116], s);
        let names = |v: &N| -> String { for (nm, x) in [("t_j-1",t[j-1]),("t_j",t[j]),("t_j+1",t[j+1]),("t_j+2",t[j+2])] { if *v == x { return nm.into(); } } format!("? bl {}", bl(v)) };
        eprintln!("upto {upto}: Q = {} top(120 lanes) = {} sy {} sx {} cache {} | bl tj {} tj1 {} tj2 {} q {}",
            names(&qv), names(&topv), get(&res.q,&fd.sy,s), get(&res.q,&fd.sx,s), get(&res.q,&fd.q[121..138],s), bl(&t[j]), bl(&t[j+1]), bl(&t[j+2]), r[j]/r[j+1]);
    }
}
