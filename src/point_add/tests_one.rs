//! froghop-one tests: integer model, window schedule (FH1_SCHED), gate-level slot against the model, point addition.

use super::refmodel_one::{self as rm, bl, Ph, St, N};

struct Rng(u64);
impl Rng {
    fn new(s: u64) -> Rng {
        Rng(s ^ 0x9E3779B97F4A7C15)
    }
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below_p(&mut self) -> N {
        let pp = rm::p();
        loop {
            let mut v = N::ZERO;
            for i in 0..4 {
                v |= N::from(self.next()) << (64 * i);
            }
            if v < pp && v != N::ZERO {
                return v;
            }
        }
    }
}

#[test]
fn one_model_result() {
    let pp = rm::p();
    let mut rng = Rng::new(7);
    let mut maxs = 0;
    for _ in 0..300 {
        let x = rng.below_p();
        let mut st = St::new(x);
        let mut s = 0;
        while st.ph != Ph::Dn {
            st.fwd_at(s);
            s += 1;
            assert!(s < 2000);
        }
        maxs = maxs.max(s);
        let inv = st.result();
        assert_eq!(inv.mul_mod(x, pp), N::from(1u64), "inverse");
    }
    eprintln!("one model OK, max slots {maxs}");
}

/// Per-slot envelopes for the window schedule. FH1_GEN=<shots> FH1_SEED=<seed> FH1_OUT=<file>.
/// Columns per slot: running, B1 min, B1 max, pi max, align b0 min/max, align (b + pi - 1 after) min/max,
/// step-end b min/max, first-step-end b min/max.
#[test]
fn one_envelope() {
    let Ok(n) = std::env::var("FH1_GEN") else { return };
    let n: usize = n.parse().unwrap();
    let seed: u64 = std::env::var("FH1_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    let out = std::env::var("FH1_OUT").unwrap_or("fh1_env.txt".into());
    const S: usize = 1000;
    let big = u32::MAX;
    let mut run = vec![0u64; S];
    let mut b1 = vec![(big, 0u32); S];
    let mut pim = vec![0u32; S];
    let mut al0 = vec![(big, 0u32); S];
    let mut al1 = vec![(big, 0u32); S];
    let mut se = vec![(big, 0u32); S];
    let mut fse = vec![(big, 0u32); S];
    let mut lens = vec![0u32; S + 2];
    let mut maxk = 0;
    let mut maxdep = 0;
    let mut rng = Rng::new(seed);
    let mm = |a: &mut (u32, u32), v: u32| {
        a.0 = a.0.min(v);
        a.1 = a.1.max(v);
    };
    for _ in 0..n {
        let x = rng.below_p();
        let mut st = St::new(x);
        let mut fin = S + 1;
        for s in 0..S {
            if st.ph == Ph::Dn {
                fin = s;
                break;
            }
            run[s] += 1;
            mm(&mut b1[s], st.b1());
            pim[s] = pim[s].max(st.pi);
            maxdep = maxdep.max(st.stk.len());
            let ev = st.fwd_at(s);
            maxk = maxk.max(st.k);
            if let Some((b0, bv, pi)) = ev.align {
                mm(&mut al0[s], b0);
                mm(&mut al1[s], bv + pi - 1);
            }
            if let Some(b) = ev.step_end {
                mm(&mut se[s], b);
                if ev.first_step_end {
                    mm(&mut fse[s], b);
                }
            }
        }
        lens[fin.min(S + 1)] += 1;
    }
    let mut txt = String::new();
    for s in 0..S {
        let z = |a: (u32, u32)| if a.0 == big { (0, 0) } else { a };
        let (b1s, al0s, al1s, ses, fses) = (z(b1[s]), z(al0[s]), z(al1[s]), z(se[s]), z(fse[s]));
        txt += &format!("{} {} {} {} {} {} {} {} {} {} {} {} {}
", s, run[s], b1s.0, b1s.1, pim[s], al0s.0, al0s.1,
                        al1s.0, al1s.1, ses.0, ses.1, fses.0, fses.1);
    }
    std::fs::write(&out, txt).unwrap();
    let mut acc = 0u64;
    let mut last = 0;
    for (s, &c) in lens.iter().enumerate() {
        if c > 0 {
            last = s;
        }
        acc += c as u64;
    }
    let _ = acc;
    eprintln!("envelope: {n} shots, last finishing slot {last}, max k {maxk}, max stack {maxdep}; written {out}");
    let _ = bl;
}

/// What one shot decodes and touches in one slot (pre-slot state s0, post-slot state s1), in the layout with the
/// quotient bits in the register gaps: b is the dividend's length until the turn, bit i >= 1 of the stack sits at
/// lane b + i (D's gap during OUT, V's gap during DIV), the cofactor ladder's boundary is B1 + max(d - 1, 0).
#[derive(Clone, Copy, Default, Debug)]
struct GapEv {
    run: bool,
    pi0: i64,
    /// OUT in the last step (b == 1, k == 0)
    fin: bool,
    /// terminates this slot
    term: bool,
    /// P1 boundary B1 (shots whose P1 result is used: DIV, unaligned OUT)
    p1: Option<i64>,
    /// S5 boundary B1 + max(d - 1, 0) (OUT shots and step ends)
    s5: Option<i64>,
    /// S7 boundary B1 (turning shots, d = 0)
    s7: Option<i64>,
    /// turn: V probe lane (physical) and D probe lane; dl1: the D probe lane holds a one
    vpr: Option<i64>,
    dpr: Option<i64>,
    dl1: bool,
    /// pop lane of D (d >= 1); popw: it holds a written bit (d >= 2)
    pop: Option<i64>,
    popw: bool,
    /// push lane (physical) of a written bit
    push: Option<i64>,
    /// step end: b; first_se: the first step's end
    se_b: Option<i64>,
    first_se: bool,
    /// smallest free-lane slack of the gap stack and of the S5 region (>= 0 required)
    room: i64,
    /// b as held by the register (the fin-slot [b == 1] test reads it)
    brep: Option<i64>,
}

fn gap_slot(s0: &St, s1: &St, ev: &rm::Ev) -> GapEv {
    let w = W1 as i64;
    let mut e = GapEv::default();
    e.room = i64::MAX;
    if s0.ph == Ph::Dn {
        return e;
    }
    e.run = true;
    let pi0 = s0.pi as i64;
    e.pi0 = pi0;
    let d0 = s0.stk.len() as i64;
    let mut room = i64::MAX;
    match s0.ph {
        Ph::Out => {
            let br = bl(&s0.r) as i64;
            e.brep = Some(br);
            e.fin = s0.k == 0 && s0.b == 1;
            if d0 >= 1 {
                e.pop = Some(br + d0 - 1);
                e.popw = d0 >= 2;
            }
            if d0 >= 2 {
                room = room.min(w - bl(&s0.cd) as i64 - 1 - (br + d0 - 1));
            }
            if s0.k == 0 && s0.b != 1 {
                e.p1 = Some(br);
            }
            let dp = (d0 - 1).max(0);
            let mid = if s1.ph == Ph::Ret {
                let k = s1.k as i64;
                let bn = s1.b as i64;
                e.vpr = Some(br - k + pi0);
                e.dpr = Some(bn + k - 1);
                e.dl1 = br - k + 1 - bn == 1;
                e.s7 = Some(bn + pi0);
                bn + pi0
            } else if s1.k != 0 || s0.b == 1 {
                br + pi0
            } else {
                br
            };
            let b5 = mid + (dp - 1).max(0);
            e.s5 = Some(b5);
            room = room.min(w - bl(&s0.cd) as i64 - 1 - b5);
            room = room.min(w - bl(&s1.cv) as i64 + pi0 - 1 - b5);
            e.term = s1.ph == Ph::Dn;
        }
        Ph::Ret | Ph::Div => {
            e.brep = Some(s0.b as i64);
            if s0.ph == Ph::Div {
                e.p1 = Some(s0.b as i64 + pi0);
            }
            if let Some(b) = ev.step_end {
                let b = b as i64;
                let d = s1.stk.len() as i64;
                e.se_b = Some(b);
                e.first_se = ev.first_step_end;
                let b5 = b + (d - 1).max(0);
                e.s5 = Some(b5);
                room = room.min(w - bl(&s1.cd) as i64 - 1 - b5);
                room = room.min(w - bl(&s1.cv) as i64 - 1 - b5);
            } else if s0.ph == Ph::Div {
                e.push = Some(s0.b as i64 + d0 + pi0);
                let d1 = s1.stk.len() as i64;
                room = room.min(w - bl(&s1.cv) as i64 - 1 - (s1.b as i64 + d1 - 1));
            }
        }
        Ph::Dn => {}
    }
    e.room = room;
    e
}

fn mmx(a: &mut (i64, i64), v: i64) {
    a.0 = a.0.min(v);
    a.1 = a.1.max(v);
}

/// envelope of per-slot (min, max) over slots s - tsh ..= s + tsh; (i64::MAX, -1) when empty
fn envw(v: &[(i64, i64)], s: usize, tsh: usize) -> (i64, i64) {
    let lo = s.saturating_sub(tsh);
    let hi = (s + tsh).min(v.len() - 1);
    let mut r = (i64::MAX, -1i64);
    for t in lo..=hi {
        if v[t].0 <= v[t].1 {
            r.0 = r.0.min(v[t].0);
            r.1 = r.1.max(v[t].1);
        }
    }
    r
}

fn sched_text(path_var: &str) -> String {
    match std::env::var(path_var) {
        Ok(p) => std::fs::read_to_string(p).unwrap(),
        Err(_) => include_str!("sched_one.txt").to_string(),
    }
}

fn parse_sched(txt: &str) -> (Vec<usize>, Vec<Vec<usize>>) {
    let mut lines = txt.lines();
    let hdr: Vec<usize> = lines.next().unwrap().split_whitespace().map(|t| t.parse().unwrap()).collect();
    let rows: Vec<Vec<usize>> = lines
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.split_whitespace().map(|t| t.parse().unwrap()).collect())
        .collect();
    (hdr, rows)
}

/// Window schedule from the integer model. FH1_SCHED=<out file> FH1_N=<shots> FH1_SEED=<seed> FH1_T=<slot shift>;
/// margins FH1_MPB (V probe), FH1_MPE (D probe), FH1_MQ (pop), FH1_MU (push), FH1_MP2 (cofactor ladder top),
/// FH1_MLC (cofactor ladder bottom), FH1_BM (offset register). The P1 columns (lv jw p1lo), lc's floor, p2hi's floor and the fin / termon flags come
/// from FH1_KEEP (default: the current sched_one.txt). Columns: lv jw p1lo lc p2hi pb0 pb1 pe0 pe1 fin 0 termon base
/// q0 q1 u0 u1; header "W S f1w".
#[test]
fn one_schedule() {
    let Ok(out) = std::env::var("FH1_SCHED") else { return };
    let n: usize = std::env::var("FH1_N").ok().and_then(|v| v.parse().ok()).unwrap_or(1_000_000);
    let seed: u64 = std::env::var("FH1_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(2026);
    let tsh: usize = std::env::var("FH1_T").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    let evn = |k: &str, d: i64| -> i64 { std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d) };
    let (mpb, mpe, mq, mu, mp2, mg) =
        (evn("FH1_MPB", 5), evn("FH1_MPE", 3), evn("FH1_MQ", 3), evn("FH1_MU", 3), evn("FH1_MP2", 3), evn("FH1_BM", 4));
    let mlc = evn("FH1_MLC", 2);
    let keep_txt = sched_text("FH1_KEEP");
    let (hdr, keep) = parse_sched(&keep_txt);
    let (w, s_n, f1w) = (hdr[0] as i64, hdr[1], hdr[2]);
    assert_eq!(w as usize, W1);
    assert_eq!(keep.len(), s_n);
    const S: usize = 1000;
    let empty = (i64::MAX, -1i64);
    let mut p1 = vec![empty; S];
    let mut s5 = vec![empty; S];
    let mut s7 = vec![empty; S];
    let mut vpr = vec![empty; S];
    let mut dpr = vec![empty; S];
    let mut popw = vec![empty; S];
    let mut popa = vec![empty; S];
    let mut push = vec![empty; S];
    let mut seb = vec![empty; S];
    let mut fin = vec![false; S];
    let mut term = vec![false; S];
    let mut finb = vec![0usize; S]; // running shots whose b is 1 mod 2^BB without being 1
    let (mut room, mut maxk, mut maxdep, mut f1last, mut last) = (i64::MAX, 0u32, 0usize, 0usize, 0usize);
    let mut rng = Rng::new(seed);
    for _ in 0..n {
        let x = rng.below_p();
        let mut st = St::new(x);
        for s in 0..S {
            if st.ph == Ph::Dn {
                break;
            }
            let s0 = st.clone();
            let ev = st.fwd_at(s);
            let e = gap_slot(&s0, &st, &ev);
            if let Some(v) = e.p1 { mmx(&mut p1[s], v); }
            if let Some(v) = e.s5 { mmx(&mut s5[s], v); }
            if let Some(v) = e.s7 { mmx(&mut s7[s], v); }
            if let Some(v) = e.vpr { mmx(&mut vpr[s], v); }
            if let Some(v) = e.dpr { mmx(&mut dpr[s], v); }
            if let Some(v) = e.pop {
                mmx(&mut popa[s], v);
                if e.popw { mmx(&mut popw[s], v); }
            }
            if let Some(v) = e.push { mmx(&mut push[s], v); }
            if let Some(v) = e.se_b { mmx(&mut seb[s], v); }
            if let Some(br) = e.brep {
                if br != 1 && (br - 1) % 64 == 0 { finb[s] += 1; }
            }
            fin[s] |= e.fin;
            term[s] |= e.term;
            room = room.min(e.room);
            maxk = maxk.max(st.k);
            maxdep = maxdep.max(s0.stk.len()).max(st.stk.len());
            if e.first_se { f1last = f1last.max(s); }
            last = last.max(s);
        }
    }
    let bb = super::froghop_one::BB as i64;
    let top = (1i64 << bb) - 1;
    let first = super::froghop_one::FIRST_BASE as i64;
    let mut txt = format!("{}\n", keep_txt.lines().next().unwrap().trim());
    let mut base_prev = first;
    let (mut changes, mut worst, mut grown, mut lowered) = (0usize, i64::MAX, 0usize, 0usize);
    for s in 0..s_n {
        let kr = &keep[s];
        let (lv, jw, p1lo, lc_k, p2hi_k, fi_k, tm_k) = (kr[0], kr[1], kr[2], kr[3], kr[4], kr[9], kr[11]);
        let trailing = s + 8 >= s_n;
        let fi_m = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| fin[t]);
        let tm_m = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| term[t]);
        if (fi_m && fi_k == 0) || (tm_m && tm_k == 0) {
            eprintln!("slot {s}: fin/termon flags of the kept schedule miss model shots (fin {fi_m}/{fi_k}, term {tm_m}/{tm_k})");
        }
        let win = |v: &Vec<(i64, i64)>, m: i64| -> (i64, i64) {
            let (a, z) = envw(v, s, tsh);
            if a > z || trailing { (0, 0) } else { ((a - m).max(0), (z + 1 + m).min(w)) }
        };
        let (pb0, pb1) = win(&vpr, mpb);
        let (pe0, pe1) = win(&dpr, mpe);
        let (q0, q1) = win(&popw, mq);
        let (u0, u1) = win(&push, mu);
        // cofactor ladder: S5 toggles at phys B5 (B5 in [lc - 1, p2hi - 1]), S7 at B1 - 1 (B1 in [lc, p2hi])
        let (l5, h5) = envw(&s5, s, tsh);
        let (l7, h7) = envw(&s7, s, tsh);
        let (mut need_lo, mut need_hi) = (i64::MAX, -1i64);
        if l5 <= h5 {
            need_lo = need_lo.min(l5 + 1);
            need_hi = need_hi.max(h5 + 1);
        }
        if l7 <= h7 {
            need_lo = need_lo.min(l7 + 1);
            need_hi = need_hi.max(h7);
        }
        let (mut lc, mut p2hi) = (lc_k, p2hi_k);
        if !trailing && need_hi >= 0 {
            let hi = (need_hi + mp2).min(w) as usize;
            if hi > p2hi {
                p2hi = hi;
                grown += 1;
            }
            let lo = (need_lo - mlc).max(0) as usize;
            if lo < lc {
                lc = lo;
                lowered += 1;
            }
        }
        // offset register: every decoded value (bq units) in [base, base + 2^BB - 1]
        let (mut lo, mut hi) = (i64::MAX, -1i64);
        let mut srcs: Vec<(&Vec<(i64, i64)>, i64)> =
            vec![(&p1, 1), (&popa, 1), (&vpr, 1), (&dpr, 0), (&push, 2), (&s5, 1), (&s7, 1)];
        if s < f1w {
            srcs.push((&seb, 1));
        }
        for (v, sh) in srcs {
            let (a, z) = envw(v, s, tsh);
            if a <= z {
                lo = lo.min(a - sh);
                hi = hi.max(z - sh);
            }
        }
        let base = if trailing || hi < 0 {
            if s < f1w { first } else { 0 }
        } else if s < f1w {
            if lo < first || hi > first + top {
                eprintln!("slot {s}: values [{lo}, {hi}] outside the first-step base {first}");
            }
            first
        } else if fi_k != 0 || tm_k != 0 {
            if hi > top {
                eprintln!("slot {s}: values [{lo}, {hi}] outside base 0 ([b == 1] test)");
            }
            0
        } else if base_prev <= lo - mg && base_prev + top >= hi + mg {
            base_prev
        } else {
            let mut m2 = mg;
            while m2 > 0 && (hi + m2 - top).max(0) > lo - m2 {
                m2 -= 1;
            }
            let lb = (hi + m2 - top).max(0);
            let ub = lo - m2;
            assert!(lb <= ub, "slot {s}: values [{lo}, {hi}] do not fit {bb} bits");
            (lb + ub) / 2
        };
        if hi >= 0 {
            let up = if base + top >= 256 { 99 } else { base + top - hi };
            let dn = if base == 0 { 99 } else { lo - base };
            if dn < 0 || up < 0 {
                eprintln!("slot {s}: base {base} does not cover [{lo}, {hi}]");
            }
            worst = worst.min(dn.min(up));
        }
        if (fi_k != 0 || tm_k != 0) && finb[s] > 0 {
            eprintln!("slot {s}: {} running shots with b = 1 mod 64 in a [b == 1] slot", finb[s]);
        }
        if s > 0 && base != base_prev {
            changes += 1;
        }
        base_prev = base;
        txt += &format!("{lv} {jw} {p1lo} {lc} {p2hi} {pb0} {pb1} {pe0} {pe1} {fi_k} 0 {tm_k} {base} {q0} {q1} {u0} {u1}\n");
    }
    assert_eq!(base_prev, 0, "the last slot must leave b - 1 unshifted");
    std::fs::write(&out, &txt).unwrap();
    eprintln!("schedule: {n} shots seed {seed}, slots {s_n} (last active {last}), f1w {f1w} (last first step end {f1last}), \
               shift {tsh}, margins pb {mpb} pe {mpe} q {mq} u {mu} p2 {mp2} lc {mlc} base {mg}; base changes {changes}, worst base \
               slack {worst}; p2hi raised in {grown} slots, lc lowered in {lowered}; max k {maxk}, max depth {maxdep}, \
               min room {room}; {out}");
}

/// Per-division slack of every window of the given schedule (clipped as LayOne clips it) along one trajectory;
/// returns the failing items (empty: the division stays inside every window).
fn gap_fails(x: N, lay: &LayOne) -> Vec<&'static str> {
    let w = W1 as i64;
    let mut st = St::new(x);
    let mut bad: Vec<&'static str> = vec![];
    let mut hit = |c: bool, nm: &'static str| {
        if c && !bad.contains(&nm) {
            bad.push(nm);
        }
    };
    let first_fin = lay.rows.iter().position(|r| r[9] != 0).unwrap_or(lay.s);
    let _ = first_fin;
    let mut finished = false;
    for s in 0..lay.s {
        if st.ph == Ph::Dn {
            finished = true;
            break;
        }
        let r = lay.rows[s];
        let base = lay.base[s] as i64;
        let [q0, q1, u0, u1] = lay.scan[s];
        let (lv, jw, p1lo, lc, p2hi) = (r[0] as i64, r[1] as i64, r[2] as i64, r[3] as i64, r[4] as i64);
        let (pb0, pb1, pe0, pe1) = (r[5] as i64, r[6] as i64, r[7] as i64, r[8] as i64);
        hit(w < bl(&st.r) as i64 + bl(&st.cd) as i64, "dlane");
        hit(w < bl(&st.rv) as i64 + bl(&st.cv) as i64, "vlane");
        let s0 = st.clone();
        let ev = st.fwd_at(s);
        let e = gap_slot(&s0, &st, &ev);
        let dec = |v: i64| v < base || v > base + 63;
        if let Some(b1) = e.p1 {
            hit(lv < b1 + 2 || p1lo > b1 + 1, "p1");
            hit(jw < e.pi0 + 1, "jw");
            hit(dec(b1 - 1), "base");
        }
        if let Some(b5) = e.s5 {
            hit(lc > b5 + 1 || b5 > p2hi - 1, "p2");
            hit(dec(b5 - 1), "base");
        }
        if let Some(b1) = e.s7 {
            hit(lc > b1 || b1 > p2hi, "p3");
            hit(dec(b1 - 1), "base");
        }
        if let Some(l) = e.vpr {
            hit(l < pb0 || l >= pb1, "vprobe");
            hit(dec(l - 1), "base");
        }
        if let Some(l) = e.dpr {
            hit(e.dl1 && (l < pe0 || l >= pe1), "dprobe");
            hit(dec(l), "base");
        }
        if let Some(l) = e.pop {
            hit(e.popw && (l < q0 as i64 || l >= q1 as i64), "pop");
            hit(dec(l - 1), "base");
        }
        if let Some(l) = e.push {
            hit(l < u0 as i64 || l >= u1 as i64, "push");
            hit(dec(l - 2), "base");
        }
        if let Some(b) = e.se_b {
            if s < lay.f1w {
                hit(dec(b - 1), "base");
            }
            hit(e.first_se && s >= lay.f1w, "f1w");
        }
        if r[9] != 0 || r[11] != 0 {
            if let Some(br) = e.brep {
                hit(br != 1 && (br - 1) % 64 == 0, "b1test");
            }
        }
        hit(e.fin && r[9] == 0, "fin");
        hit(e.term && r[11] == 0, "term");
        hit(e.room < 0, "room");
        hit(st.k > 31 || st.stk.len() > 32, "kdep");
        if st.ph == Ph::Dn && st.cnt == 0 {
            hit(s >= lay.trail_start || s.saturating_sub(lay.first_termon) >= 256, "late");
        }
    }
    hit(!finished && st.ph != Ph::Dn, "late");
    bad
}

/// Window tail of this build on fresh inputs: FH1_GAPTAIL=<divisions> FH1_SEED=<seed>. Prints the indices of the
/// divisions that leave a window (same input stream as `one_tail`).
#[test]
fn one_gap_tail() {
    let Ok(n) = std::env::var("FH1_GAPTAIL") else { return };
    let n: usize = n.parse().unwrap();
    let seed: u64 = std::env::var("FH1_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(77);
    let lay = LayOne::from_text(&sched_text("FH1_SCHED_IN"), 0);
    let mut rng = Rng::new(seed);
    let mut fails = vec![];
    let mut by = std::collections::BTreeMap::<&'static str, usize>::new();
    for i in 0..n {
        let x = rng.below_p();
        let f = gap_fails(x, &lay);
        if !f.is_empty() {
            for nm in &f {
                *by.entry(nm).or_default() += 1;
            }
            fails.push(i);
            eprintln!("GAPFAIL {i} {f:?}");
        }
    }
    eprintln!("gap-layout tail: {n} divisions seed {seed}: {} leave a window; by window {by:?}", fails.len());
    println!("GAPFAILS {}", fails.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(","));
}

/// The gate-level layout's free lanes on the model: every quotient bit's gap lane is free at every slot boundary
/// (checked by expect_lanes_one) for FH1_GAPN fresh divisions.
#[test]
fn one_gap_lanes_free() {
    let n: usize = std::env::var("FH1_GAPN").ok().and_then(|v| v.parse().ok()).unwrap_or(2000);
    let mut rng = Rng::new(31337);
    for _ in 0..n {
        let mut st = St::new(rng.below_p());
        let mut s = 0;
        while st.ph != Ph::Dn {
            let _ = expect_lanes_one(&st);
            st.fwd_at(s);
            s += 1;
        }
    }
    eprintln!("gap lanes free on {n} divisions");
}


// ---------------------------------------------------------------- gate-level slot against the model
use super::builder::B;
use super::froghop_one::{FhOne, LayOne, W1};
use super::tests_double::run;
use crate::circuit::QubitId;

pub fn lay_one() -> LayOne {
    LayOne::from_text(include_str!("sched_one.txt"), 0)
}

fn putv(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) {
            words[q.0 as usize] |= 1 << shot;
        } else {
            words[q.0 as usize] &= !(1 << shot);
        }
    }
}
fn getv(words: &[u64], qs: &[QubitId], shot: usize) -> u64 {
    let mut v = 0u64;
    for (i, &q) in qs.iter().enumerate() {
        v |= ((words[q.0 as usize] >> shot) & 1) << i;
    }
    v
}
fn gb(words: &[u64], q: QubitId, shot: usize) -> u64 {
    (words[q.0 as usize] >> shot) & 1
}

fn expect_lanes_one(m: &St) -> (Vec<u8>, Vec<u8>) {
    let w = W1;
    let mut d = vec![0u8; w];
    let mut v = vec![0u8; w];
    for j in 0..w {
        if j < 300 && m.r.bit(j) {
            d[j] |= 1;
        }
        if m.cd.bit(w - 1 - j) {
            d[j] |= 1;
        }
    }
    for u in 0..w {
        let mut bit = 0u8;
        if m.rv.bit(u) {
            bit = 1;
        }
        if m.cv.bit(w - 1 - u) {
            bit = 1;
        }
        let p = ((u as i64 + m.pi as i64).rem_euclid(w as i64)) as usize;
        v[p] = bit;
    }
    // quotient bits in the register gaps: stack bit i >= 1 at lane b + i (bit 0 is the quotient's first bit, always 1,
    // counted in the depth only); D's gap during OUT (b = bl(r), the dividend), V's gap during DIV (b the divisor's
    // length, V frame)
    if !m.stk.is_empty() {
        assert_eq!(m.stk[0], 1, "quotient's first bit");
    }
    for (i, &bit) in m.stk.iter().enumerate().skip(1) {
        match m.ph {
            Ph::Out => {
                let j = bl(&m.r) as usize + i;
                assert_eq!(d[j], 0, "stack lane {j} of D not free (stack {:?})", m.stk);
                d[j] = bit;
            }
            Ph::Div | Ph::Ret => {
                let u = m.b as usize + i;
                let p = ((u as i64 + m.pi as i64).rem_euclid(w as i64)) as usize;
                assert_eq!(v[p], 0, "stack lane {u} of V not free (stack {:?})", m.stk);
                v[p] = bit;
            }
            Ph::Dn => panic!("DONE with a stack"),
        }
    }
    (d, v)
}

fn check_state(words: &[u64], f: &FhOne, lay: &LayOne, sigma: usize, k: usize, m: &St) {
    let parity = ((sigma + 1) & 1) as u64;
    assert_eq!(m.pi as u64 & 1, parity, "slot {sigma} shot {k} pi parity");
    assert_eq!(2 * getv(words, &f.pi, k) + parity, m.pi as u64, "slot {sigma} shot {k} pi");
    let w = W1;
    let (ed, ev) = expect_lanes_one(m);
    for j in 0..w {
        assert_eq!(gb(words, f.d[j], k) as u8, ed[j], "slot {sigma} shot {k} D lane {j} ph {:?} pi {} k {} b {} stack {:?}",
                   m.ph, m.pi, m.k, m.b, m.stk);
        assert_eq!(gb(words, f.v[j], k) as u8, ev[j], "slot {sigma} shot {k} V lane {j} ph {:?} pi {} k {} b {} stack {:?}",
                   m.ph, m.pi, m.k, m.b, m.stk);
    }
    assert_eq!(gb(words, f.al_s, k), (m.k != 0) as u64, "slot {sigma} shot {k} al_s");
    if m.ph != Ph::Dn {
        assert_eq!(getv(words, &f.k, k), m.k as u64, "slot {sigma} shot {k} k");
        assert_eq!(getv(words, &f.dep, k), m.stk.len() as u64 + 31, "slot {sigma} shot {k} d6");
    } else {
        // DONE: the termination stamp in k and dep[..3] (complemented there: d6 was 31 at the termination)
        let kb = super::froghop_one::KB;
        let stamp = sigma - lay.first_termon - 1 - m.cnt as usize;
        assert_eq!(getv(words, &f.cnt(), k), (stamp ^ (0b111 << kb)) as u64, "slot {sigma} shot {k} timestamp");
        assert_eq!(getv(words, &f.dep[3..], k), 0b011, "slot {sigma} shot {k} d6 high bits");
    }
    let bb = super::froghop_one::BB;
    let bs = lay.base[sigma.saturating_sub(1)]; // the slot shifts the offset at its start
    let first_fin = lay.rows.iter().position(|r| r[9] != 0).unwrap_or(lay.s);
    // b is the dividend's length until the turn; the cached slots hold B1 = b + [k != 0] pi
    let brep = if m.ph == Ph::Out && m.k > 0 { bl(&m.r) } else { m.b };
    let b1 = if sigma <= first_fin && m.k != 0 { brep + m.pi } else { brep };
    let u = (b1 as i64 - 1 - bs as i64).rem_euclid(1 << bb) as u64;
    assert_eq!(getv(words, &f.bq, k), u, "slot {sigma} shot {k} b (ph {:?} k {} b {} brep {brep} pi {})", m.ph, m.k, m.b, m.pi);
    let f1on = sigma < lay.f1w;
    let (fo, fd, fnn) = (gb(words, f.fo, k), gb(words, f.fd, k), gb(words, f.fnn, k));
    let done = if f1on { 0 } else { fnn };
    let want = match m.ph {
        Ph::Out => (1, 0, 0),
        Ph::Ret => (0, 0, 0),
        Ph::Div => (0, 1, 0),
        Ph::Dn => (0, 0, 1),
    };
    assert_eq!((fo, fd, done), want, "slot {sigma} shot {k} phase {:?}", m.ph);
    if f1on {
        assert_eq!(fnn as u8, m.f1, "slot {sigma} shot {k} f1");
    }
    assert_eq!(gb(words, f.par, k) as u8, m.par, "slot {sigma} shot {k} par");
}

#[test]
fn one_traversal_matches_model() {
    let lay = lay_one();
    let w = W1;
    let gpool: usize = std::env::var("FH1_GP").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let mut b = B::new();
    let d = b.alloc_n(w);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, vec![], gpool);
    let seed: u64 = std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(4242);
    let mut rng = Rng::new(seed);
    let mut models: Vec<St> = (0..64).map(|_| St::new(rng.below_p())).collect();
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mods = models.clone();
    let mut words = run(&b.ops, nq, &|wd| {
        for k in 0..64 {
            putv(wd, &vl, k, &mods[k].rv);
        }
    })
    .q;
    let mut tof = 0u64;
    let pool = f.pool.clone();
    for sigma in 0..lay.s {
        for k in 0..64 {
            check_state(&words, &f, &lay, sigma, k, &models[k]);
        }
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let ops = b.ops[start..].to_vec();
        let wd = words.clone();
        let r = run(&ops, nq, &move |x| x.copy_from_slice(&wd));
        assert_eq!(r.phase, 0, "phase after slot {sigma}");
        tof += r.tof;
        words = r.q;
        for &q in pool.iter().chain(f.gp.iter()) {
            assert_eq!(words[q.0 as usize], 0, "scratch q{} dirty after slot {sigma} row {:?}", q.0, lay.rows[sigma]);
        }
        for m in models.iter_mut() {
            m.fwd_at(sigma);
        }
    }
    for m in &models {
        assert!(m.ph == Ph::Dn);
        let _ = m.result();
    }
    eprintln!("one traversal: {} slots, avg Toffoli/shot {} ({:.1} per slot), qubits {}, scratch high water {}",
              lay.s, tof / 64, tof as f64 / 64.0 / lay.s as f64, b.width(), f.hw);
}

#[test]
fn one_profile() {
    use crate::circuit::OperationType as OT;
    use std::collections::BTreeMap;
    let lay = lay_one();
    let gpool: usize = std::env::var("FH1_GP").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let mut b = B::new();
    let d = b.alloc_n(W1);
    let v = b.alloc_n(W1);
    let par = b.alloc();
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, vec![], gpool);
    f.init(&mut b, &lay);
    let mut tot: BTreeMap<&'static str, u64> = BTreeMap::new();
    let (mut odd_t, mut even_t) = (0u64, 0u64);
    for sigma in 0..lay.s {
        f.marks.clear();
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let mut mk = vec![("pre", start)];
        mk.extend(f.marks.iter().cloned());
        mk.push(("end", b.ops.len()));
        let mut st = 0u64;
        for i in 0..mk.len() - 1 {
            let c = b.ops[mk[i].1..mk[i + 1].1].iter().filter(|o| matches!(o.kind, OT::CCX | OT::CCZ)).count() as u64;
            *tot.entry(mk[i].0).or_default() += c;
            st += c;
        }
        if sigma % 2 == 1 { odd_t += st } else { even_t += st }
    }
    let all: u64 = tot.values().sum();
    for (k, v) in &tot {
        eprintln!("{:6} {:>9} ({:5.1}%) {:7.1}/slot", k, v, 100.0 * *v as f64 / all as f64, *v as f64 / lay.s as f64);
    }
    eprintln!("total {} ({:.1}/slot; odd slots {:.1}, even {:.1}); scratch high water {} at {}", all, all as f64 / lay.s as f64,
              odd_t as f64 / (lay.s / 2) as f64, even_t as f64 / ((lay.s + 1) / 2) as f64, f.hw, f.hw_at);
    eprintln!("scratch peaks by step: {:?}", f.peaks);
}

#[test]
fn one_r12_c13_pool_slot_census() {
    let lay = lay_one();
    let mut b = B::new();
    let d = b.alloc_n(W1); let v = b.alloc_n(W1); let par = b.alloc();
    let foreign = b.alloc_n(256);
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, foreign, 0);
    f.init(&mut b, &lay);
    let mut high = std::collections::BTreeMap::<&str, Vec<(usize, usize)>>::new();
    for sigma in 0..lay.s {
        f.peaks.clear();
        b.ops.clear();
        f.slot(&mut b, &lay, sigma);
        for stage in ["S2", "S5", "S7"] {
            if let Some(&n) = f.peaks.get(stage) {
                if n >= 15 { high.entry(stage).or_default().push((sigma, n)); }
            }
        }
    }
    for (stage, vals) in high {
        let max = vals.iter().map(|&(_, n)| n).max().unwrap();
        eprintln!("{stage}: >=15 count {}, max {}, first {:?}, last {:?}",
            vals.len(), max, &vals[..vals.len().min(12)], &vals[vals.len().saturating_sub(12)..]);
    }
}

#[test]
fn one_r12_c13_bq_topcarry_all_wires() {
    use super::modp_double::{gadd, gadd_top_zero};
    let make = |ng: usize| {
        let mut b = B::new();
        let t = b.alloc_n(7);
        let a = b.alloc_n(5);
        let g = b.alloc_n(ng);
        let foreign = b.alloc_n(256);
        (b, t, a, g, foreign)
    };
    let (mut ob, ot, oa, og, of) = make(6);
    let (mut nb, nt, na, ng, nf) = make(5);
    let oadd: Vec<Option<QubitId>> = oa.iter().copied().map(Some).chain([None, None]).collect();
    let nadd: Vec<Option<QubitId>> = na.iter().copied().map(Some).chain([None, None]).collect();
    gadd(&mut ob, &ot, &oadd, &og);
    gadd_top_zero(&mut nb, &nt, &nadd, &ng);
    let mut rng = Rng::new(12017);
    let dirty: Vec<u64> = (0..256).map(|_| rng.next()).collect();
    for batch in 0..64usize {
        let init = |wd: &mut Vec<u64>, t: &[QubitId], a: &[QubitId], foreign: &[QubitId]| {
            for lane in 0..64 {
                let x = batch * 64 + lane;
                let tv = x & 127;
                let av = x >> 7;
                for (j, &q) in t.iter().enumerate() {
                    if tv >> j & 1 != 0 { wd[q.0 as usize] |= 1u64 << lane; }
                }
                for (j, &q) in a.iter().enumerate() {
                    if av >> j & 1 != 0 { wd[q.0 as usize] |= 1u64 << lane; }
                }
            }
            for (i, &q) in foreign.iter().enumerate() { wd[q.0 as usize] = dirty[i]; }
        };
        let or = run(&ob.ops, ob.width() as usize, &|wd| init(wd, &ot, &oa, &of));
        let nr = run(&nb.ops, nb.width() as usize, &|wd| init(wd, &nt, &na, &nf));
        assert_eq!((or.phase, nr.phase), (0, 0), "batch {batch} phase");
        for lane in 0..64 {
            let x = batch * 64 + lane;
            let want = ((x & 127) + (x >> 7)) & 127;
            assert_eq!(getv(&or.q, &ot, lane), want as u64, "old sum batch {batch} lane {lane}");
            assert_eq!(getv(&nr.q, &nt, lane), want as u64, "new sum batch {batch} lane {lane}");
            assert_eq!(getv(&or.q, &oa, lane), (x >> 7) as u64, "old addend");
            assert_eq!(getv(&nr.q, &na, lane), (x >> 7) as u64, "new addend");
        }
        for &q in &og { assert_eq!(or.q[q.0 as usize], 0, "old clean carry"); }
        for &q in &ng { assert_eq!(nr.q[q.0 as usize], 0, "new clean carry"); }
        for (i, &q) in of.iter().enumerate() { assert_eq!(or.q[q.0 as usize], dirty[i], "old dirty {i}"); }
        for (i, &q) in nf.iter().enumerate() { assert_eq!(nr.q[q.0 as usize], dirty[i], "new dirty {i}"); }
    }
    eprintln!("BB7 top-zero adder: all 4096 inputs, old/new outputs, addends, carries, 256 dirty passengers and zero phase");
}

/// R9-C5 diagnostic: exact emitted T by slot stage for the paired ghost legs.
/// The builder's mark positions follow the enclosing recording during inverse construction.
#[test]
fn one_r9_c5_stage_attribution() {
    use super::builder::G;
    use super::froghop_one::SlotMode;
    use crate::circuit::OperationType as OT;
    use std::collections::BTreeMap;
    let lay = lay_one();
    let mut b = B::new();
    let d = b.alloc_n(W1);
    let v = b.alloc_n(W1);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, dirty, 0);
    eprintln!("stage-attr peak {}", b.peak);
    f.init(&mut b, &lay);
    let receipts = b.fresh_bits(lay.s);
    let dl_receipts = b.fresh_bits(lay.s);
    let extra_flat = b.fresh_bits(16 * lay.s);
    let extra_receipts: Vec<[crate::circuit::BitId; 16]> = extra_flat.chunks_exact(16)
        .map(|chunk| chunk.try_into().unwrap()).collect();
    let mut maps = Vec::with_capacity(lay.s);
    let mut fw = BTreeMap::<&'static str, u64>::new();
    let mut s5saved: Vec<Vec<crate::circuit::BitId>> = Vec::new();
    for (sigma, (&receipt, &dl_receipt)) in receipts.iter().zip(dl_receipts.iter()).enumerate() {
        maps.push(f.v.clone());
        f.marks.clear();
        let start = b.ops.len();
        let t0 = b.tof;
        f.s5_carry_bits.clear();
        f.slot_mode(&mut b, &lay, sigma, SlotMode::ForwardGhost {
            receipt, dl_receipt: Some(dl_receipt), extras: Some(extra_receipts[sigma]) });
        s5saved.push(f.s5_carry_bits.clone());
        let mut marks = vec![("pre", start)];
        marks.extend(f.marks.iter().copied());
        marks.push(("end", b.ops.len()));
        let mut st = 0;
        for pair in marks.windows(2) {
            let c = b.ops[pair[0].1..pair[1].1].iter()
                .filter(|op| matches!(op.kind, OT::CCX | OT::CCZ)).count() as u64;
            *fw.entry(pair[0].0).or_default() += c;
            st += c;
        }
        assert_eq!(st, b.tof - t0, "forward stage accounting slot {sigma}");
    }
    let fw_pool = f.peaks.clone();
    f.peaks.clear();
    let mut rv = BTreeMap::<&'static str, u64>::new();
    for sigma in (0..lay.s).rev() {
        f.v = maps[sigma].clone();
        f.marks.clear();
        f.s5_carry_bits = s5saved[sigma].clone();
        b.begin();
        f.slot_mode(&mut b, &lay, sigma,
                SlotMode::RecordInverseWithRepair { receipt: receipts[sigma], dl_receipt: Some(dl_receipts[sigma]),
                    extras: Some(extra_receipts[sigma]) });
        let rec = b.end();
        let mut marks = vec![("pre", 0)];
        marks.extend(f.marks.iter().copied());
        marks.push(("end", rec.len()));
        let mut st = 0;
        for pair in marks.windows(2) {
            let c = rec[pair[0].1..pair[1].1].iter()
                .filter(|g| matches!(g, G::Ccx(..) | G::AndU(..))).count() as u64;
            *rv.entry(pair[0].0).or_default() += c;
            st += c;
        }
        let t0 = b.tof;
        b.play(&rec, true);
        assert_eq!(st, b.tof - t0, "inverse stage accounting slot {sigma}");
        f.v = maps[sigma].clone();
    }
    let fw_sum: u64 = fw.values().sum();
    let rv_sum: u64 = rv.values().sum();
    eprintln!("R9-C5 forward T {fw_sum} by stage {fw:?}");
    eprintln!("R9-C5 inverse T {rv_sum} by stage {rv:?}");
    eprintln!("R9-C5 forward pool max-used {fw_pool:?}");
    eprintln!("R9-C5 inverse pool max-used {:?}", f.peaks);
}

/// R9-C5 sampled all-wire zero census, observing D/V after every emitted op.
/// The scratch ownership census comes from Pl.peaks in the stage attribution test.
#[test]
fn one_r9_c5_sampled_free_lanes() {
    use super::froghop_one::SlotMode;
    use crate::circuit::{Op, OperationType as OT};
    use sha3::digest::{ExtendableOutput, Update};
    use std::collections::BTreeMap;
    #[derive(Clone, Copy, Debug)]
    struct Span { d: usize, v: usize, both: usize, ops: u64 }
    impl Span {
        fn new() -> Self { Span { d: usize::MAX, v: usize::MAX, both: usize::MAX, ops: 0 } }
        fn see(&mut self, d: usize, v: usize) {
            self.d = self.d.min(d);
            self.v = self.v.min(v);
            self.both = self.both.min(d + v);
        }
    }
    fn apply<R: sha3::digest::XofReader>(ops: &[Op], sim: &mut crate::sim::Simulator<'_, R>, kind: &[u8], zeros: &mut [usize; 3], span: &mut Span) {
        span.see(zeros[1], zeros[2]);
        for op in ops {
            let a = op.q_target.0 as usize;
            let b = op.q_control1.0 as usize;
            let sw = op.kind == OT::Swap && b != a;
            let old_a = a < kind.len() && kind[a] != 0 && sim.qubits[a] == 0;
            let old_b = sw && b < kind.len() && kind[b] != 0 && sim.qubits[b] == 0;
            sim.apply_iter(std::iter::once(op));
            if a < kind.len() && kind[a] != 0 {
                zeros[kind[a] as usize] = (zeros[kind[a] as usize] as isize
                    + usize::from(sim.qubits[a] == 0) as isize - usize::from(old_a) as isize) as usize;
            }
            if sw && b < kind.len() && kind[b] != 0 {
                zeros[kind[b] as usize] = (zeros[kind[b] as usize] as isize
                    + usize::from(sim.qubits[b] == 0) as isize - usize::from(old_b) as isize) as usize;
            }
            span.see(zeros[1], zeros[2]);
            span.ops += 1;
        }
    }
    let lay = lay_one();
    let mut b = B::new();
    let d = b.alloc_n(W1);
    let v = b.alloc_n(W1);
    let par = b.alloc();
    let foreign = b.alloc_n(256);
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, foreign.clone(), 0);
    let vl = f.v[1..257].to_vec();
    let mut rng = Rng::new(4242);
    let xs: Vec<N> = (0..64).map(|_| St::new(rng.below_p()).rv).collect();
    f.init(&mut b, &lay);
    let receipts = b.fresh_bits(lay.s);
    let mut h = sha3::Shake256::default();
    h.update(b"R9-C5-free-lanes");
    let mut xof = h.finalize_xof();
    let mut sim = crate::sim::Simulator::new(b.width() as usize, receipts.last().unwrap().0 as usize + 1 + lay.s * W1, &mut xof);
    for k in 0..64 { putv(&mut sim.qubits, &vl, k, &xs[k]); }
    for &q in &foreign { sim.qubits[q.0 as usize] = rng.next(); }
    sim.apply_iter(b.ops.iter());
    b.ops.clear();
    let mut kind = vec![0u8; b.width() as usize];
    for &q in &f.d { kind[q.0 as usize] = 1; }
    for &q in &f.v { kind[q.0 as usize] = 2; }
    let mut zeros = [0, 0, 0];
    for (i, &k) in kind.iter().enumerate() {
        if k != 0 && sim.qubits[i] == 0 { zeros[k as usize] += 1; }
    }
    let mut maps = Vec::with_capacity(lay.s);
    let mut s5saved: Vec<Vec<crate::circuit::BitId>> = Vec::new();
    let mut fw = BTreeMap::<&'static str, Span>::new();
    for (sigma, &receipt) in receipts.iter().enumerate() {
        maps.push(f.v.clone());
        f.marks.clear();
        f.s5_carry_bits.clear();
        f.slot_mode(&mut b, &lay, sigma, SlotMode::ForwardGhost { receipt, dl_receipt: None, extras: None });
        s5saved.push(f.s5_carry_bits.clone());
        let mut marks = vec![("pre", 0)];
        marks.extend(f.marks.iter().copied());
        marks.push(("end", b.ops.len()));
        for pair in marks.windows(2) {
            apply(&b.ops[pair[0].1..pair[1].1], &mut sim, &kind, &mut zeros,
                fw.entry(pair[0].0).or_insert_with(Span::new));
        }
        b.ops.clear();
    }
    let mut rv = BTreeMap::<&'static str, Span>::new();
    for sigma in (0..lay.s).rev() {
        f.v = maps[sigma].clone();
        f.marks.clear();
        f.s5_carry_bits = s5saved[sigma].clone();
        b.begin();
        f.slot_mode(&mut b, &lay, sigma,
            SlotMode::RecordInverseWithRepair { receipt: receipts[sigma], dl_receipt: None, extras: None });
        let rec = b.end();
        let mut marks = vec![("pre", 0)];
        marks.extend(f.marks.iter().copied());
        marks.push(("end", rec.len()));
        for pair in marks.windows(2).rev() {
            b.play(&rec[pair[0].1..pair[1].1], true);
            apply(&b.ops, &mut sim, &kind, &mut zeros,
                rv.entry(pair[0].0).or_insert_with(Span::new));
            b.ops.clear();
        }
        f.v = maps[sigma].clone();
    }
    eprintln!("R9-C5 sampled D/V zero minima over every op of 903 forward slots, 64 deterministic words: {fw:?}");
    eprintln!("R9-C5 sampled D/V zero minima over every op of 903 inverse slots, 64 deterministic words: {rv:?}");
    assert_eq!(sim.phase, 0, "sampled paired phase");
}

fn getn(words: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (words[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}

impl Rng {
    fn below_bits(&mut self, bits: usize) -> N {
        let mut v = N::ZERO;
        for i in 0..6 {
            v |= N::from(self.next()) << (64 * i);
        }
        v & ((N::from(1u64) << bits) - N::from(1u64))
    }
}

#[test]
fn one_forward_inverse_identity() {
    let lay = lay_one();
    let w = W1;
    for seed in 0..4u64 {
        let mut b = B::new();
        let d = b.alloc_n(w);
        let v = b.alloc_n(w);
        let par = b.alloc();
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, vec![], 0);
        let vl: Vec<QubitId> = f.v[1..257].to_vec();
        let v0 = f.v.clone();
        let mut rng = Rng::new(900 + seed);
        let pp = rm::p();
        let xs: Vec<N> = (0..64).map(|_| { let x = rng.below_p() % pp; if x == N::ZERO { N::from(1u64) } else { x } }).collect();
        let ms: Vec<St> = xs.iter().map(|&x| St::new(x)).collect();
        f.init(&mut b, &lay);
        let maps = f.forward(&mut b, &lay);
        f.inverse(&mut b, &lay, &maps);
        f.init(&mut b, &lay);
        assert_eq!(f.v, v0);
        let nq = b.width() as usize;
        let r = run(&b.ops, nq, &|wd| { for k in 0..64 { putv(wd, &vl, k, &ms[k].rv); } });
        assert_eq!(r.phase, 0, "phase");
        for q in 0..nq {
            if vl.iter().any(|x| x.0 as usize == q) { continue; }
            assert_eq!(r.q[q], 0, "qubit {q} not restored (seed {seed})");
        }
        for k in 0..64 { assert_eq!(getn(&r.q, &vl, k), ms[k].rv); }
        eprintln!("one seed {seed}: forward+inverse identity ok, tof/shot {}", r.tof / 64);
    }
}

/// Independent Plain oracle at every boundary, with the actual pre-HMR TT
/// word and its actual measurement outcome accounting for forward phase debt.
#[test]
fn one_ghost_forward_data_and_debt() {
    use super::froghop_one::SlotMode;
    use crate::circuit::OperationType as OT;
    use sha3::digest::{ExtendableOutput, Update};
    let lay = lay_one();
    let setup = |b: &mut B| {
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let foreign = b.alloc_n(256);
        let mut f = FhOne::alloc(b, d, v, &lay, par, foreign.clone(), 0);
        f.init(b, &lay);
        (f, foreign)
    };
    let (mut plain_b, mut ghost_b) = (B::new(), B::new());
    let (mut plain, foreign) = setup(&mut plain_b);
    let (mut ghost, ghost_foreign) = setup(&mut ghost_b);
    assert_eq!(foreign, ghost_foreign);
    let vl = plain.v[1..257].to_vec();
    let receipts = ghost_b.fresh_bits(lay.s);
    let nb = receipts.last().unwrap().0 as usize + 1 + lay.s * W1; // + the rolling S5 carry receipts
    let nq = plain_b.width() as usize;
    assert_eq!(nq as u64, *crate::point_add::PEAK);
    let mut hash = sha3::Shake256::default();
    hash.update(b"froghop-ghost-debt-r2");
    let mut plain_xof = hash.clone().finalize_xof();
    let mut ghost_xof = hash.finalize_xof();
    let mut ps = crate::sim::Simulator::new(nq, nb, &mut plain_xof);
    let mut gs = crate::sim::Simulator::new(nq, nb, &mut ghost_xof);
    let mut rng = Rng::new(4242);
    let mut models: Vec<St> = (0..64).map(|_| St::new(rng.below_p())).collect();
    for k in 0..64 { putv(&mut ps.qubits, &vl, k, &models[k].rv); }
    for &q in &foreign { ps.qubits[q.0 as usize] = rng.next(); }
    gs.qubits.copy_from_slice(&ps.qubits);
    let foreign_words: Vec<u64> = foreign.iter().map(|q| ps.qubits[q.0 as usize]).collect();
    ps.apply_iter(plain_b.ops.iter());
    gs.apply_iter(ghost_b.ops.iter());
    let mut debt = 0;
    let mut tt_one = 0u64;
    let mut tt_zero = 0u64;
    let mut turn_post_fo_zero = 0u64;
    let mut no_lanes = 0;
    for sigma in 0..lay.s {
        for k in 0..64 { check_state(&gs.qubits, &ghost, &lay, sigma, k, &models[k]); }
        plain_b.ops.clear();
        ghost_b.ops.clear();
        plain.slot(&mut plain_b, &lay, sigma);
        ghost.slot_mode(&mut ghost_b, &lay, sigma, SlotMode::ForwardGhost { receipt: receipts[sigma], dl_receipt: None, extras: None });
        ps.apply_iter(plain_b.ops.iter());
        let mut discharges = 0;
        for op in &ghost_b.ops {
            if op.kind == OT::Hmr && op.c_target == receipts[sigma] {
                let tt = gs.qubits[op.q_target.0 as usize];
                tt_one += tt.count_ones() as u64;
                tt_zero += (!tt).count_ones() as u64;
                turn_post_fo_zero += (tt & !gs.qubits[ghost.fo.0 as usize]).count_ones() as u64;
                gs.apply_iter(std::iter::once(op));
                debt ^= tt & gs.bits[receipts[sigma].0 as usize];
                discharges += 1;
            } else if op.kind == OT::Hmr && ghost.s5_carry_bits.contains(&op.c_target) {
                let v = gs.qubits[op.q_target.0 as usize];
                gs.apply_iter(std::iter::once(op));
                debt ^= v & gs.bits[op.c_target.0 as usize];
            } else {
                gs.apply_iter(std::iter::once(op));
            }
        }
        assert_eq!(discharges, 1, "ghost slot {sigma}");
        assert_eq!(ps.phase, 0, "Plain phase slot {sigma}");
        assert_eq!(gs.phase, debt, "forward debt slot {sigma}");
        assert_eq!(gs.qubits, ps.qubits, "forward data/foreign payload slot {sigma}");
        assert_eq!(ghost.v, plain.v, "lane descriptors slot {sigma}");
        for &q in ghost.pool.iter().chain(ghost.gp.iter()) {
            assert_eq!(gs.qubits[q.0 as usize], 0, "ghost scratch slot {sigma}");
        }
        for (i, &q) in foreign.iter().enumerate() { assert_eq!(gs.qubits[q.0 as usize], foreign_words[i]); }
        no_lanes += usize::from(lay.rows[sigma][3] >= W1);
        for m in &mut models { m.fwd_at(sigma); }
    }
    assert!(tt_one > 0 && tt_zero > 0 && turn_post_fo_zero > 0 && no_lanes > 0);
    assert!(plain_b.tof > ghost_b.tof);
    assert_eq!(ghost_b.peak, *crate::point_add::PEAK);
    eprintln!("ghost forward: 903 boundaries/data/debt/foreign words pass; tt1 {tt_one} tt0 {tt_zero}, tt1/postfo0 {turn_post_fo_zero}, no-lane slots {no_lanes}; saving {} T, debt {debt:016x}, Q{}", plain_b.tof - ghost_b.tof, ghost_b.peak);
}

/// Old/plain versus six-HMR forward kernel on every slot boundary.
#[test]
fn one_r9_c5_extra_forward_boundary() {
    use super::froghop_one::SlotMode;
    use crate::circuit::OperationType as OT;
    use sha3::digest::{ExtendableOutput, Update};
    let lay = lay_one();
    let setup = |b: &mut B| {
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let foreign = b.alloc_n(256);
        let mut f = FhOne::alloc(b, d, v, &lay, par, foreign.clone(), 0);
        f.init(b, &lay);
        (f, foreign)
    };
    let (mut old_b, mut new_b) = (B::new(), B::new());
    let (mut old, foreign) = setup(&mut old_b);
    let (mut new, new_foreign) = setup(&mut new_b);
    assert_eq!(foreign, new_foreign);
    let vl = old.v[1..257].to_vec();
    let tt_receipts = new_b.fresh_bits(lay.s);
    let dl_receipts = new_b.fresh_bits(lay.s);
    let extra_flat = new_b.fresh_bits(16 * lay.s);
    let extra_receipts: Vec<[crate::circuit::BitId; 16]> = extra_flat.chunks_exact(16)
        .map(|chunk| chunk.try_into().unwrap()).collect();
    let nb = extra_flat.last().unwrap().0 as usize + 1 + lay.s * W1; // + the rolling S5 carry receipts
    let nq = old_b.width() as usize;
    assert_eq!(nq as u64, *crate::point_add::PEAK);
    let mut h = sha3::Shake256::default();
    h.update(b"R9-C5-dl-boundary");
    let mut old_xof = h.clone().finalize_xof();
    let mut new_xof = h.finalize_xof();
    let mut os = crate::sim::Simulator::new(nq, nb, &mut old_xof);
    let mut ns = crate::sim::Simulator::new(nq, nb, &mut new_xof);
    let mut rng = Rng::new(4242);
    let mut models: Vec<St> = (0..64).map(|_| St::new(rng.below_p())).collect();
    for k in 0..64 { putv(&mut os.qubits, &vl, k, &models[k].rv); }
    for &q in &foreign { os.qubits[q.0 as usize] = rng.next(); }
    ns.qubits.copy_from_slice(&os.qubits);
    let foreign_words: Vec<u64> = foreign.iter().map(|q| os.qubits[q.0 as usize]).collect();
    os.apply_iter(old_b.ops.iter());
    ns.apply_iter(new_b.ops.iter());
    let mut debt = 0u64;
    let mut dl_one = 0u64;
    let mut dl_zero = 0u64;
    for sigma in 0..lay.s {
        for k in 0..64 { check_state(&ns.qubits, &new, &lay, sigma, k, &models[k]); }
        old_b.ops.clear();
        new_b.ops.clear();
        old.slot(&mut old_b, &lay, sigma);
        new.slot_mode(&mut new_b, &lay, sigma, SlotMode::ForwardGhost {
            receipt: tt_receipts[sigma], dl_receipt: Some(dl_receipts[sigma]),
            extras: Some(extra_receipts[sigma]) });
        os.apply_iter(old_b.ops.iter());
        let mut tt_hits = 0;
        let mut dl_hits = 0;
        let mut extra_hits = [0usize; 16];
        for op in &new_b.ops {
            let is_tt = op.kind == OT::Hmr && op.c_target == tt_receipts[sigma];
            let is_dl = op.kind == OT::Hmr && op.c_target == dl_receipts[sigma];
            let extra = extra_receipts[sigma].iter().position(|&id| op.kind == OT::Hmr && op.c_target == id);
            let carry = op.kind == OT::Hmr && new.s5_carry_bits.contains(&op.c_target);
            let val = if is_tt || is_dl || extra.is_some() || carry { ns.qubits[op.q_target.0 as usize] } else { 0 };
            ns.apply_iter(std::iter::once(op));
            if is_tt || is_dl || extra.is_some() || carry { debt ^= val & ns.bits[op.c_target.0 as usize]; }
            if is_tt { tt_hits += 1; }
            if is_dl { dl_hits += 1; dl_one += val.count_ones() as u64; dl_zero += (!val).count_ones() as u64; }
            if let Some(j) = extra { extra_hits[j] += 1; }
        }
        assert_eq!((tt_hits, dl_hits, extra_hits), (1, 1, [1; 16]), "receipts slot {sigma}");
        assert_eq!(os.phase, 0, "old phase slot {sigma}");
        assert_eq!(ns.phase, debt, "new phase debt slot {sigma}");
        assert_eq!(os.qubits, ns.qubits, "old/new all-wire data slot {sigma}");
        assert_eq!(old.v, new.v, "lane descriptor slot {sigma}");
        for &q in new.pool.iter().chain(new.gp.iter()) {
            assert_eq!(ns.qubits[q.0 as usize], 0, "scratch slot {sigma}");
        }
        for (i, &q) in foreign.iter().enumerate() {
            assert_eq!(ns.qubits[q.0 as usize], foreign_words[i], "foreign slot {sigma}");
        }
        for m in &mut models { m.fwd_at(sigma); }
    }
    assert!(dl_one > 0 && dl_zero > 0, "dl measurement sampled both values");
    eprintln!("R10-C6 17-debt old/new all 903 slots OK; forward saving {} T; dl one/zero {dl_one}/{dl_zero}", old_b.tof - new_b.tof);
}

#[test]
fn one_r9_c5_adjacent_pair_kernel() {
    let mut b = B::new();
    let qs = b.alloc_n(259);
    b.ccx(qs[0], qs[1], qs[2]);
    b.ccx(qs[0], qs[1], qs[2]);
    let old = b.ops.clone();
    let mut new = old.clone();
    assert_eq!(super::cancel_adjacent_ccx(&mut new), 2);
    assert!(new.is_empty());
    let mut rng = Rng::new(8435);
    let input: Vec<u64> = (0..259).map(|_| rng.next()).collect();
    let init = |words: &mut Vec<u64>| words.copy_from_slice(&input);
    let before = run(&old, 259, &init);
    let after = run(&new, 259, &init);
    assert_eq!(before.q, input);
    assert_eq!(after.q, input);
    assert_eq!((before.phase, after.phase), (0, 0));
    assert_eq!((before.tof, after.tof), (128, 0));
    eprintln!("R9-C5 adjacent CCX pair: all 259 wires/64 words, dirty passengers, zero phase");
}

#[test]
fn one_r10_c6_s6a_shared_and_kernel() {
    let build = |shared: bool| {
        let mut b = B::new();
        let q = b.alloc_n(5); // se, ww, z0, fd, fo
        let a = b.alloc();
        let dirty = b.alloc_n(256);
        let (se, ww, z0, fd, fo) = (q[0], q[1], q[2], q[3], q[4]);
        if shared {
            b.x(ww);
            b.and_c(se, ww, a);
            b.cx(a, fd);
            b.cx(a, fo);
            b.and_u(se, ww, a);
            b.x(ww);
            b.and_c(ww, z0, a);
            b.cx(a, fo);
            b.cx(ww, fd);
            b.cx(a, fd);
            b.and_u(ww, z0, a);
        } else {
            b.x(ww);
            b.ccx(se, ww, fd);
            b.ccx(se, ww, fo);
            b.x(ww);
            b.ccx(ww, z0, fo);
            b.x(z0);
            b.ccx(ww, z0, fd);
            b.x(z0);
        }
        (b, q, a, dirty)
    };
    let (old, q, a, dirty) = build(false);
    let (new, nq, na, ndirty) = build(true);
    assert_eq!((&q, a, &dirty), (&nq, na, &ndirty));
    let mut rng = Rng::new(6438);
    let foreign: Vec<u64> = dirty.iter().map(|_| rng.next()).collect();
    let init = |words: &mut Vec<u64>| {
        for i in 0..5 {
            words[q[i].0 as usize] = (0..64).filter(|shot| ((shot % 32) >> i) & 1 == 1)
                .fold(0u64, |mask, shot| mask | (1u64 << shot));
        }
        for (i, &id) in dirty.iter().enumerate() { words[id.0 as usize] = foreign[i]; }
    };
    let before = run(&old.ops, old.width() as usize, &init);
    let after = run(&new.ops, new.width() as usize, &init);
    assert_eq!(before.q, after.q);
    assert_eq!(before.q[a.0 as usize], 0);
    assert_eq!((before.phase, after.phase), (0, 0));
    eprintln!("S6a shared ANDs: all 32 flag states x2, 256 dirty passengers, zero phase; old/new T {} / {}", before.tof, after.tof);
}

#[test]
fn one_r10_c6_xd_parity_kernel() {
    for f1on in [false, true] {
        let build = |fused: bool| {
            let mut b = B::new();
            let q = b.alloc_n(5); // fo, fnn, fd, ct, xd
            let parity = b.alloc();
            let dirty = b.alloc_n(256);
            let (fo, fnn, fd, ct, xd) = (q[0], q[1], q[2], q[3], q[4]);
            if fused {
                b.x(parity);
                b.cx(fo, parity);
                if !f1on { b.cx(fnn, parity); }
                b.x(ct);
                b.and_c(parity, ct, xd);
                b.x(ct);
                if !f1on { b.cx(fnn, parity); }
                b.cx(fo, parity);
                b.x(parity);
            } else {
                b.x(ct);
                b.ccx(fd, ct, xd);
                b.cx(fo, fd);
                if !f1on { b.cx(fnn, fd); }
                b.x(fd);
                b.ccx(fd, ct, xd);
                b.cx(fo, fd);
                if !f1on { b.cx(fnn, fd); }
                b.x(fd);
                b.x(ct);
            }
            (b, q, parity, dirty)
        };
        let (old, q, parity, dirty) = build(false);
        let (new, nq, np, ndirty) = build(true);
        assert_eq!((&q, parity, &dirty), (&nq, np, &ndirty));
        let mut rng = Rng::new(8373 + f1on as u64);
        let foreign: Vec<u64> = dirty.iter().map(|_| rng.next()).collect();
        let init = |words: &mut Vec<u64>| {
            for i in 0..5 {
                words[q[i].0 as usize] = (0..64).filter(|shot| ((shot % 32) >> i) & 1 == 1)
                    .fold(0u64, |mask, shot| mask | (1u64 << shot));
            }
            for (i, &id) in dirty.iter().enumerate() { words[id.0 as usize] = foreign[i]; }
        };
        let before = run(&old.ops, old.width() as usize, &init);
        let after = run(&new.ops, new.width() as usize, &init);
        assert_eq!(before.q, after.q);
        assert_eq!(before.q[parity.0 as usize], 0);
        assert_eq!((before.phase, after.phase), (0, 0));
        eprintln!("xd parity f1on={f1on}: 32 states x2, dirty 256, zero phase, old/new T {} / {}", before.tof, after.tof);
    }
}

#[test]
fn one_r9_c5_decoder_pivot_kernel() {
    use super::mask::{onehot_scan, onehot_scan_old};
    let build = |fast: bool, undo: bool| {
        let mut b = B::new();
        let v = b.alloc_n(9);
        let pre = b.alloc_n(8);
        let out = b.alloc_n(512);
        let dirty = b.alloc_n(256);
        b.begin();
        if fast {
            onehot_scan(&mut b, &v, &pre, 0, 512, 0, |b, j, o| b.cx(o, out[j]));
        } else {
            onehot_scan_old(&mut b, &v, &pre, 0, 512, 0, |b, j, o| b.cx(o, out[j]));
        }
        let rec = b.end();
        b.play(&rec, false);
        if undo { b.play(&rec, true); }
        (b, v, pre, out, dirty)
    };
    let mut rng = Rng::new(8436);
    let data: Vec<u64> = (0..9 + 512 + 256).map(|_| rng.next()).collect();
    let eval = |fast: bool, undo: bool| {
        let (b, v, pre, out, dirty) = build(fast, undo);
        let r = run(&b.ops, b.width() as usize, &|wd| {
            for (i, &q) in v.iter().chain(out.iter()).chain(dirty.iter()).enumerate() {
                wd[q.0 as usize] = data[i];
            }
        });
        for q in pre { assert_eq!(r.q[q.0 as usize], 0, "decoder scratch"); }
        (r, b.tof)
    };
    let (old, old_t) = eval(false, false);
    let (new, new_t) = eval(true, false);
    assert_eq!(new.q, old.q, "forward all-wire mismatch");
    assert_eq!((old.phase, new.phase), (0, 0));
    let (old_inv, _) = eval(false, true);
    let (new_inv, _) = eval(true, true);
    assert_eq!(old_inv.q, new_inv.q, "inverse all-wire mismatch");
    assert_eq!((old_inv.phase, new_inv.phase), (0, 0));
    assert_eq!(new_inv.q[0..9], data[0..9]);
    eprintln!("R9-C5 decoder pivot all-wire forward/inverse, 256 dirty passengers, zero phase; old {old_t} T, new {new_t} T");
    assert!(new_t < old_t);
}

#[test]
fn one_r9_c5_masked_down_shared_and_kernel() {
    let build = |shared: bool, undo: bool| {
        let mut b = B::new();
        let q = b.alloc_n(7 + 256);
        let (f, t, s, x, g, tmp, gf) = (q[0], q[1], q[2], q[3], q[4], q[5], q[6]);
        b.begin();
        if shared {
            b.and_c(f, s, tmp);
            b.ccx(tmp, t, x);
            b.ccx(tmp, g, t);
            b.and_u(f, s, tmp);
        } else {
            b.and_c(t, s, tmp);
            b.ccx(f, tmp, x);
            b.and_u(t, s, tmp);
            b.and_c(g, f, gf);
            b.ccx(gf, s, t);
            b.and_u(g, f, gf);
        }
        b.cx(x, t);
        b.cx(x, s);
        let rec = b.end();
        b.play(&rec, false);
        if undo { b.play(&rec, true); }
        (b, q)
    };
    let mut rng = Rng::new(8437);
    let mut input = vec![0u64; 7 + 256];
    for bit in 0..5 {
        for shot in 0..64 { if ((shot >> bit) & 1) != 0 { input[bit] |= 1u64 << shot; } }
    }
    for q in &mut input[7..] { *q = rng.next(); }
    let eval = |shared: bool, undo: bool| {
        let (b, q) = build(shared, undo);
        let r = run(&b.ops, b.width() as usize, &|wd| wd.copy_from_slice(&input));
        assert_eq!(r.q[q[5].0 as usize], 0, "temporary AND target");
        assert_eq!(r.q[q[6].0 as usize], 0, "old second AND target");
        (r, b.tof)
    };
    let (old, old_t) = eval(false, false);
    let (new, new_t) = eval(true, false);
    assert_eq!(old.q, new.q, "forward all-wire mismatch");
    assert_eq!((old.phase, new.phase), (0, 0));
    let (old_inv, _) = eval(false, true);
    let (new_inv, _) = eval(true, true);
    assert_eq!(old_inv.q, input, "old inverse identity");
    assert_eq!(new_inv.q, input, "new inverse identity");
    assert_eq!((old_inv.phase, new_inv.phase), (0, 0));
    assert_eq!((old_t, new_t), (4, 3));
    eprintln!("R9-C5 shared-AND masked cell: all 263 wires, 32 control states, dirty passengers, inverse, zero phase");
}

#[test]
fn one_r9_c5_ladder_midpoint_kernel() {
    use super::mask::{mdown, mdown_mid, mup, mup_mid, Lad, Mscr, Src};
    let build = |mid: bool, undo: bool| {
        let mut b = B::new();
        let t = b.alloc_n(8);
        let s = b.alloc_n(8);
        let v = b.alloc_n(3);
        let pre = b.alloc_n(2);
        let c0 = b.alloc();
        let f = b.alloc();
        let temp = b.alloc();
        let gf = b.alloc();
        let chain = b.alloc_n(3);
        let g = b.alloc();
        let dirty = b.alloc_n(256);
        let srcs = vec![Src { lo: 0, hi: 8, v: v.clone(), a: 0, d: 1, pre: pre.clone(), late: false }];
        let sc = Mscr { f, t: temp, gf, chain: chain.clone() };
        let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
        b.begin();
        let up = if mid { mup_mid(&mut b, &ld) } else { mup(&mut b, &ld) };
        let down = if mid { mdown_mid(&mut b, &ld, Some(g)) } else { mdown(&mut b, &ld, Some(g)) };
        b.play(&up, false);
        b.play(&down, false);
        let rec = b.end();
        b.play(&rec, false);
        if undo { b.play(&rec, true); }
        (b, t, s, v, pre, c0, f, temp, gf, chain, g, dirty)
    };
    let mut rng = Rng::new(8438);
    let mut input = vec![0u64; 8 + 8 + 3 + 2 + 1 + 1 + 1 + 1 + 3 + 1 + 256];
    for x in &mut input[0..19] { *x = rng.next(); }
    input[28] = rng.next(); // g; all scratch lanes remain zero
    for x in &mut input[29..] { *x = rng.next(); }
    let eval = |mid: bool, undo: bool| {
        let (b, _, _, _, _, _, _, _, _, _, _, _) = build(mid, undo);
        let r = run(&b.ops, b.width() as usize, &|wd| wd.copy_from_slice(&input));
        (r, b.tof)
    };
    let (old, old_t) = eval(false, false);
    let (new, new_t) = eval(true, false);
    assert_eq!(old.q, new.q, "forward all-wire midpoint mismatch");
    assert_eq!((old.phase, new.phase), (0, 0));
    let (old_inv, _) = eval(false, true);
    let (new_inv, _) = eval(true, true);
    assert_eq!(old_inv.q, input, "old inverse identity");
    assert_eq!(new_inv.q, input, "new inverse identity");
    assert_eq!((old_inv.phase, new_inv.phase), (0, 0));
    assert!(new_t < old_t);
    eprintln!("R9-C5 ladder midpoint all-wire old/new and inverse with dirty passengers: {old_t} -> {new_t} emitted T");
}

#[test]
fn one_r10_c6_s5_forward_carry_kernel() {
    use super::mask::{mdown_mid, mup_mid, Lad, Mscr, Src};
    let build = |banked: bool, undo: bool| {
        let mut b = B::new();
        let t = b.alloc_n(9);
        let s = b.alloc_n(9);
        let v = b.alloc_n(3);
        let pre = b.alloc_n(2);
        let c0 = b.alloc();
        let mf = b.alloc_n(3);
        let bank = b.alloc_n(4);
        let be = b.alloc();
        let dirty = b.alloc_n(256);
        let srcs = vec![Src { lo: 0, hi: 4, v: v.clone(), a: 0, d: 1, pre: pre.clone(), late: false }];
        let sc = Mscr { f: mf[0], t: mf[1], gf: mf[2], chain: pre.clone() };
        let mut gp = Vec::new();
        if banked { gp.push(mf[2]); gp.extend_from_slice(&bank); }
        let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &sc, g: &gp };
        b.begin();
        let ru = mup_mid(&mut b, &ld);
        let rd = mdown_mid(&mut b, &ld, Some(be));
        b.play(&rd, true);
        b.play(&ru, true);
        let rec = b.end();
        b.play(&rec, false);
        if undo { b.play(&rec, true); }
        (b, t, s, v, be, dirty)
    };
    for seed in 0..8 {
        let (old_b, t, s, v, be, dirty) = build(false, false);
        let (new_b, _, _, _, _, _) = build(true, false);
        let mut input = vec![0u64; old_b.width() as usize];
        let mut rng = Rng::new(5000 + seed);
        for &q in t.iter().chain(s.iter()).chain(v.iter()).chain(std::iter::once(&be)).chain(dirty.iter()) {
            input[q.0 as usize] = rng.next();
        }
        let old = run(&old_b.ops, input.len(), &|wd| wd.copy_from_slice(&input));
        let new = run(&new_b.ops, input.len(), &|wd| wd.copy_from_slice(&input));
        assert_eq!(old.q, new.q, "old/new all-wire S5 seed {seed}");
        assert_eq!((old.phase, new.phase), (0, 0));
        let (old_inv, _, _, _, _, _) = build(false, true);
        let (new_inv, _, _, _, _, _) = build(true, true);
        let oi = run(&old_inv.ops, input.len(), &|wd| wd.copy_from_slice(&input));
        let ni = run(&new_inv.ops, input.len(), &|wd| wd.copy_from_slice(&input));
        assert_eq!(oi.q, input, "old paired identity seed {seed}");
        assert_eq!(ni.q, input, "new paired identity seed {seed}");
        assert_eq!((oi.phase, ni.phase), (0, 0));
        eprintln!("S5 forward carries seed {seed}: old {} new {} T, 64 words, 256 dirty passengers", old_b.tof, new_b.tof);
    }
}

#[test]
fn one_r16_c27_a4a_forward_s5_old_new_all_wires() {
    use super::mask::{mdown_mid, mup_mid, s5_rolling_finish, s5_rolling_prefix, Lad, Mscr, Src};
    for ordinary in [1usize, 4, 9] {
        let build = |rolling: bool| {
            let mut b = B::new();
            let t = b.alloc_n(9);
            let s = b.alloc_n(9);
            let v = b.alloc_n(3);
            let pre = b.alloc_n(2);
            let c0 = b.alloc();
            let mf = b.alloc_n(2);
            let gate = b.alloc();
            let dirty = b.alloc_n(256);
            let srcs = if ordinary < 9 { vec![Src { lo: ordinary, hi: 9, v: v.clone(),
                a: 7, d: -1, pre: pre.clone(), late: false }] } else { vec![] };
            let ms = Mscr { f: mf[0], t: mf[1], gf: mf[1], chain: pre.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, g: &[] };
            if rolling {
                let bits = b.fresh_bits(ordinary);
                s5_rolling_prefix(&mut b, &ld, gate, mf[1], &bits);
                if ordinary < 9 {
                    let shifted: Vec<Src> = srcs.iter().map(|q| Src { lo: 0, hi: 9 - ordinary,
                        v: q.v.clone(), a: q.a - ordinary as isize, d: q.d,
                        pre: q.pre.clone(), late: false }).collect();
                    let win = Lad { t: &t[ordinary..], s: &s[ordinary..], c0: s[ordinary - 1],
                        srcs: &shifted, f0: true, cmpl: true, sc: &ms, g: &[] };
                    let ru = mup_mid(&mut b, &win);
                    let rd = mdown_mid(&mut b, &win, Some(gate));
                    b.play(&rd, true);
                    b.play(&ru, true);
                    s5_rolling_finish(&mut b, &ld, &bits);
                }
            } else {
                let ru = mup_mid(&mut b, &ld);
                let rd = mdown_mid(&mut b, &ld, Some(gate));
                b.play(&rd, true);
                b.play(&ru, true);
            }
            (b, t, s, v, gate, dirty)
        };
        let (old, t, s, v, gate, dirty) = build(false);
        let (new, _, _, _, _, _) = build(true);
        let mut rng = Rng::new(16827 + ordinary as u64);
        let mut input = vec![0u64; old.width() as usize];
        for &q in t.iter().chain(s.iter()).chain(v.iter()).chain(std::iter::once(&gate)).chain(dirty.iter()) {
            input[q.0 as usize] = rng.next();
        }
        let a = run(&old.ops, input.len(), &|wd| wd.copy_from_slice(&input));
        let z = run(&new.ops, input.len(), &|wd| wd.copy_from_slice(&input));
        for q in 0..input.len() { assert_eq!(a.q[q], z.q[q], "ordinary {ordinary} wire {q}"); }
    }
}

#[test]
fn one_ghost_paired_identity() {
    let lay = lay_one();
    for seed in 0..4u64 {
        let mut b = B::new();
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let foreign = b.alloc_n(256);
        let mut f = FhOne::alloc(&mut b, d, v, &lay, par, foreign.clone(), 0);
        let vl = f.v[1..257].to_vec();
        let v0 = f.v.clone();
        let mut rng = Rng::new(900 + seed);
        // Match the existing traversal/Div entry promise, not the raw field
        // draw: the caller reflects x before entering the packed machine.
        let xs: Vec<N> = (0..64).map(|_| St::new(rng.below_p()).rv).collect();
        assert!(xs.iter().all(|&x| x > N::ZERO && x < rm::p() / N::from(2u64)));
        let foreign_words: Vec<u64> = foreign.iter().map(|_| rng.next()).collect();
        f.init(&mut b, &lay);
        let trace = f.forward_ghost(&mut b, &lay);
        f.inverse_ghost(&mut b, &lay, trace);
        f.init(&mut b, &lay);
        assert_eq!(f.v, v0);
        assert_eq!(b.peak, *crate::point_add::PEAK);
        let r = run(&b.ops, b.width() as usize, &|wd| {
            for k in 0..64 { putv(wd, &vl, k, &xs[k]); }
            for (i, &q) in foreign.iter().enumerate() { wd[q.0 as usize] = foreign_words[i]; }
        });
        for q in 0..b.width() as usize {
            if vl.iter().chain(foreign.iter()).any(|x| x.0 as usize == q) { continue; }
            assert_eq!(r.q[q], 0, "paired ghost ancilla q{q} seed {seed}");
        }
        for k in 0..64 { assert_eq!(getn(&r.q, &vl, k), xs[k]); }
        for (i, &q) in foreign.iter().enumerate() { assert_eq!(r.q[q.0 as usize], foreign_words[i]); }
        assert_eq!(r.phase, 0, "paired ghost phase seed {seed}");
        eprintln!("paired ghost seed {seed}: value/phase/foreign/scratch/channel OK, T{}, Q{}", r.tof / 64, b.peak);
    }
}

#[test]
fn one_r10_c6_d1_inverse_old_new_boundary() {
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    let lay = lay_one();
    let make = |enabled: bool| {
        let mut b = B::new();
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let dirty = b.alloc_n(256);
        let mut f = FhOne::alloc(&mut b, d, v, &lay, par, dirty.clone(), 0);
        f.d1_enabled = enabled;
        let vl = f.v[1..257].to_vec();
        f.init(&mut b, &lay);
        let tr = f.forward_ghost(&mut b, &lay);
        let forward_end = b.ops.len();
        f.inverse_ghost(&mut b, &lay, tr);
        f.init(&mut b, &lay);
        assert_eq!(f.inverse_boundaries.len(), lay.s);
        (b, f, dirty, vl, forward_end)
    };
    let (ob, of, od, ov, oe) = make(false);
    let (nb, nf, nd, nv, ne) = make(true);
    assert_eq!((ob.peak, nb.peak), (*crate::point_add::PEAK, *crate::point_add::PEAK));
    assert_eq!((&od, &ov), (&nd, &nv));
    assert_eq!(ob.ops[..oe], nb.ops[..ne], "forward stream changed");
    let mut rng = Rng::new(7444);
    let xs: Vec<N> = (0..64).map(|_| St::new(rng.below_p()).rv).collect();
    let foreign: Vec<u64> = od.iter().map(|_| rng.next()).collect();
    let mut h = sha3::Shake256::default();
    h.update(b"R10-C6-D1-boundaries");
    let mut ox = h.clone().finalize_xof();
    let mut nx = h.finalize_xof();
    let (_, bits, _, _) = crate::circuit::analyze_ops(nb.ops.iter());
    let mut os = Simulator::new(ob.width() as usize, bits as usize, &mut ox);
    let mut ns = Simulator::new(nb.width() as usize, bits as usize, &mut nx);
    for k in 0..64 { putv(&mut os.qubits, &ov, k, &xs[k]); }
    for (i, &q) in od.iter().enumerate() { os.qubits[q.0 as usize] = foreign[i]; }
    ns.qubits.copy_from_slice(&os.qubits);
    os.apply_iter(ob.ops[..oe].iter());
    ns.apply_iter(nb.ops[..ne].iter());
    assert_eq!(os.qubits, ns.qubits, "forward physical owners");
    assert_eq!(os.phase, ns.phase, "forward phase");
    let (mut op, mut np) = (oe, ne);
    for i in 0..lay.s {
        let (on, nn) = (of.inverse_boundaries[i], nf.inverse_boundaries[i]);
        os.apply_iter(ob.ops[op..on].iter());
        ns.apply_iter(nb.ops[np..nn].iter());
        assert_eq!(os.qubits, ns.qubits, "inverse physical owners after slot {}", lay.s - 1 - i);
        assert_eq!(os.phase, ns.phase, "inverse phase after slot {}", lay.s - 1 - i);
        for &q in &nf.pool { assert_eq!(ns.qubits[q.0 as usize], 0, "pool after inverse slot {}", lay.s - 1 - i); }
        op = on;
        np = nn;
    }
    os.apply_iter(ob.ops[op..].iter());
    ns.apply_iter(nb.ops[np..].iter());
    assert_eq!((os.qubits, os.phase), (ns.qubits, ns.phase));
    assert_eq!(ns.phase, 0);
    eprintln!("D1 probe-1 conditioned inverse: 903 all-wire and phase boundaries, 64 words, 256 dirty passengers, both builder receipt values isolated");
}

#[test]
fn one_r10_c8_d1phi_z0_forced_receipts() {
    use crate::sim::Simulator;
    struct Fixed(u8);
    impl sha3::digest::XofReader for Fixed {
        fn read(&mut self, out: &mut [u8]) { out.fill(self.0); }
    }
    let lay = lay_one();
    let make = |z0_phi: bool| {
        let mut b = B::new();
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let dirty = b.alloc_n(256);
        let mut f = FhOne::alloc(&mut b, d, v, &lay, par, dirty.clone(), 0);
        f.d1phi_z0 = z0_phi;
        let vl = f.v[1..257].to_vec();
        f.init(&mut b, &lay);
        let tr = f.forward_ghost(&mut b, &lay);
        let forward_end = b.ops.len();
        f.inverse_ghost(&mut b, &lay, tr);
        f.init(&mut b, &lay);
        (b, f, dirty, vl, forward_end)
    };
    let (ob, of, od, ov, oe) = make(false);
    let (nb, nf, nd, nv, ne) = make(true);
    assert_eq!((ob.peak, nb.peak), (*crate::point_add::PEAK, *crate::point_add::PEAK));
    assert_eq!((&od, &ov), (&nd, &nv));
    assert_eq!(ob.ops[..oe], nb.ops[..ne], "forward source is unchanged");
    let mut rng = Rng::new(843810);
    let xs: Vec<N> = (0..64).map(|_| St::new(rng.below_p()).rv).collect();
    let foreign: Vec<u64> = od.iter().map(|_| rng.next()).collect();
    let (_, bits, _, _) = crate::circuit::analyze_ops(nb.ops.iter());
    for fill in [0u8, 255u8] {
        let mut ox = Fixed(fill);
        let mut nx = Fixed(fill);
        let mut os = Simulator::new(ob.width() as usize, bits as usize, &mut ox);
        let mut ns = Simulator::new(nb.width() as usize, bits as usize, &mut nx);
        for k in 0..64 { putv(&mut os.qubits, &ov, k, &xs[k]); }
        for (i, &q) in od.iter().enumerate() { os.qubits[q.0 as usize] = foreign[i]; }
        ns.qubits.copy_from_slice(&os.qubits);
        os.apply_iter(ob.ops[..oe].iter());
        ns.apply_iter(nb.ops[..ne].iter());
        assert_eq!((os.qubits.as_slice(), os.phase), (ns.qubits.as_slice(), ns.phase), "forward fill {fill}");
        let (mut op, mut np) = (oe, ne);
        for i in 0..lay.s {
            let (on, nn) = (of.inverse_boundaries[i], nf.inverse_boundaries[i]);
            os.apply_iter(ob.ops[op..on].iter());
            ns.apply_iter(nb.ops[np..nn].iter());
            assert_eq!(os.qubits, ns.qubits, "inverse wires slot {} fill {fill}", lay.s - 1 - i);
            assert_eq!(os.phase, ns.phase, "inverse phase slot {} fill {fill}", lay.s - 1 - i);
            for &q in &nf.pool { assert_eq!(ns.qubits[q.0 as usize], 0, "inverse pool slot {} fill {fill}", lay.s - 1 - i); }
            op = on;
            np = nn;
        }
        os.apply_iter(ob.ops[op..].iter());
        ns.apply_iter(nb.ops[np..].iter());
        assert_eq!((os.qubits, os.phase), (ns.qubits, ns.phase), "clean end fill {fill}");
        eprintln!("D1Phi z0: forced receipt fill {fill}, 903 inverse boundaries, 64 words, 256 dirty passengers, all wires/phase equal");
    }
}

#[test]
fn one_point_add_end_to_end() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    let lay = lay_one();
    let mut b = B::new();
    let (xq, yq) = super::pointadd_one::point_add(&mut b, &lay);
    let ops = b.ops.clone();
    let (nq, _, _, regs) = crate::circuit::analyze_ops(ops.iter());
    eprintln!("ops {} qubits {} peak {} emitted tof {}", ops.len(), nq, b.peak, b.tof);
    // curve
    let pp = rm::p();
    let to_u = |v: &N| -> ruint::aliases::U256 { ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    type U = ruint::aliases::U256;
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO,
        b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
    let _ = &pp;
    let mut rng = Rng::new(2024);
    let mut cases = vec![];
    for _ in 0..64 {
        let k1 = to_u(&(rng.below_bits(250) + N::from(1u64)));
        let k2 = to_u(&(rng.below_bits(250) + N::from(1u64)));
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        let e = curve.add(t.0, t.1, o.0, o.1);
        cases.push((t, o, e));
    }
    use sha3::digest::{ExtendableOutput, Update};
    let mut h = sha3::Shake256::default();
    h.update(b"froghop-e2e");
    let mut xof = h.finalize_xof();
    let (_, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
    let mut sim = crate::sim::Simulator::new(nq as usize, nb as usize, &mut xof);
    for (k, (t, o, _)) in cases.iter().enumerate() {
        sim.set_register(&regs[0], t.0, k);
        sim.set_register(&regs[1], t.1, k);
        sim.set_register(&regs[2], o.0, k);
        sim.set_register(&regs[3], o.1, k);
    }
    sim.apply_iter(ops.iter());
    let mut bad = 0;
    for (k, (_, _, e)) in cases.iter().enumerate() {
        let gx = sim.get_register(&regs[0], k);
        let gy = sim.get_register(&regs[1], k);
        if gx != e.0 || gy != e.1 { bad += 1; }
    }
    assert_eq!(sim.phase, 0, "phase garbage");
    let regq: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    for q in 0..nq {
        if !regq.contains(&q) { assert_eq!(sim.qubits[q as usize], 0, "ancilla garbage q{q}"); }
    }
    assert_eq!(bad, 0, "classical mismatches");
    eprintln!("one end-to-end OK: avg Toffoli {}", sim.stats.toffoli_gates / 64);
}



/// Minimum slack of every sched_one.txt window over the trajectory of input x (slack >= margin 2 for every shot inside
/// the 1M-division envelope). Returns (slacks with slot, finishing slot, first step end slot, b + k there, max stack).
fn one_slacks(x: N, w: i64, s_n: usize, rows: &[Vec<i64>]) -> (Vec<(i64, usize)>, usize, usize, u32, usize) {
    let mut st = St::new(x);
    let mut sl = vec![(i64::MAX, 0usize); 13];
    let mut upd = |i: usize, v: i64, s: usize| {
        if v < sl[i].0 {
            sl[i] = (v, s);
        }
    };
    let mut fin_slot = usize::MAX;
    let mut fse = (0usize, 0u32);
    let mut maxdep = 0;
    for s in 0..s_n {
        if st.ph == Ph::Dn {
            fin_slot = fin_slot.min(s);
        }
        let r = &rows[s];
        let running = st.ph != Ph::Dn;
        if running {
            let b1 = st.b1() as i64;
            upd(0, r[0] - (b1 + 2), s);
            upd(1, r[1] - (st.pi as i64 + 1), s);
            upd(2, (b1 + 1) - r[2], s);
            if st.ph == Ph::Out && st.k == 0 && st.b == 1 {
                upd(9, if r[9] != 0 { 99 } else { -99 }, s);
            }
            upd(11, w - (bl(&st.r) as i64 + bl(&st.cd) as i64), s);
            upd(12, w - (bl(&st.rv) as i64 + bl(&st.cv) as i64), s);
        }
        let pre_b1 = st.b1() as i64;
        let bk = st.b + st.k;
        let ev = st.fwd_at(s);
        maxdep = maxdep.max(st.stk.len());
        if running {
            let mid = if let Some((_, bv, pi)) = ev.align {
                (bv + pi) as i64
            } else if let Some(b) = ev.step_end {
                b as i64
            } else {
                pre_b1
            };
            upd(3, (mid + 1) - r[3], s);
            upd(4, r[4] - (mid + 1), s);
        }
        if let Some((b0, bv, pi)) = ev.align {
            upd(5, b0 as i64 - r[5], s);
            upd(6, r[6] - 1 - b0 as i64, s);
            let e = (bv + pi - 1) as i64;
            upd(7, e - r[7], s);
            upd(8, r[8] - 1 - e, s);
        }
        if ev.first_step_end {
            fse = (s, bk);
        }
        if st.ph == Ph::Dn && st.cnt == 0 {
            upd(10, if r[11] != 0 { 99 } else { -99 }, s);
        }
    }
    if st.ph == Ph::Dn {
        fin_slot = fin_slot.min(s_n);
    }
    (sl, fin_slot, fse.0, fse.1, maxdep)
}

/// The base layout's rows (jackylee0424's 839-qubit schedule, semantics of `one_slacks`) from FH1_JL_SCHED.
fn one_sched_rows() -> (i64, usize, usize, Vec<Vec<i64>>) {
    let txt = sched_text("FH1_JL_SCHED");
    let mut lines = txt.lines();
    let hdr: Vec<i64> = lines.next().unwrap().split_whitespace().map(|v| v.parse().unwrap()).collect();
    let rows: Vec<Vec<i64>> = lines.map(|l| l.split_whitespace().map(|v| v.parse().unwrap()).collect()).collect();
    (hdr[0], hdr[1] as usize, hdr[2] as usize, rows)
}

const SLACK_NAMES: [&str; 13] = ["lv", "jw", "p1lo", "lc", "p2hi", "pb0", "pb1", "pe0", "pe1", "fin", "term", "dlane",
                                 "vlane"];

/// Check given inputs (FH1_X = comma-separated hex) against sched_one.txt.
#[test]
fn one_check_inputs() {
    let Ok(xs) = std::env::var("FH1_X") else { return };
    let (w, s_n, f1w, rows) = one_sched_rows();
    for xh in xs.split(',') {
        let x = N::from_str_radix(xh.trim(), 16).unwrap();
        let (sl, fin_slot, fs, bk, maxdep) = one_slacks(x, w, s_n, &rows);
        let mut msg = format!("x {xh}: finish {fin_slot} (S {s_n}), first step end slot {fs} (f1w {f1w}) b+k {bk}, max stack {maxdep};");
        for (i, n) in SLACK_NAMES.iter().enumerate() {
            if sl[i].0 != i64::MAX {
                msg += &format!(" {n} {}@{}", sl[i].0, sl[i].1);
            }
        }
        eprintln!("{msg}");
    }
}

/// Window tail of the base layout (FH1_JL_SCHED, 839-qubit semantics) on fresh inputs: FH1_TAIL=<divisions>
/// FH1_SEED=<seed>. Counts divisions whose minimum window slack is < 0, < 1, < 2, or that finish late / overflow the
/// stack, and prints the failing indices (same input stream as `one_gap_tail`).
#[test]
fn one_tail() {
    let Ok(n) = std::env::var("FH1_TAIL") else { return };
    let n: usize = n.parse().unwrap();
    let seed: u64 = std::env::var("FH1_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(77);
    let (w, s_n, f1w, rows) = one_sched_rows();
    let mut rng = Rng::new(seed);
    let (mut c0, mut c1, mut c2, mut late, mut any) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let mut by = vec![0usize; 13];
    let mut fails = vec![];
    for i in 0..n {
        let x = rng.below_p();
        let (sl, fin_slot, fs, _bk, maxdep) = one_slacks(x, w, s_n, &rows);
        let m = sl.iter().map(|v| v.0).min().unwrap();
        let lt = fin_slot >= s_n || fs >= f1w || maxdep > 24;
        if lt || m < 0 {
            fails.push(i);
        }
        if lt {
            late += 1;
        }
        if lt || m < 0 {
            any += 1;
        }
        if m < 0 {
            c0 += 1;
            for (i, v) in sl.iter().enumerate() {
                if v.0 < 0 {
                    by[i] += 1;
                }
            }
        }
        if m < 1 {
            c1 += 1;
        }
        if m < 2 {
            c2 += 1;
        }
    }
    let mut msg = format!("tail: {n} divisions seed {seed}: slack<0 {c0}, <1 {c1}, <2 {c2}, late/stack {late}, either {any}; slack<0 by window:");
    for (i, nm) in SLACK_NAMES.iter().enumerate() {
        if by[i] > 0 {
            msg += &format!(" {nm} {}", by[i]);
        }
    }
    eprintln!("{msg}");
    println!("JLFAILS {}", fails.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(","));
}
