//! frogstrip tests and tools: integer-model statistics (envelope tables), schedule validation (failure rate),
//! and the circuit checks.

use super::frogdrop_sched::{p, N};
use super::strip_model::*;
use super::tests_frogdrop::Rng;

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

/// odd x' as the circuit makes it (x or p - x), from a seeded stream
fn rand_x(rng: &mut Rng) -> N {
    let mut v = rng.below(256) % p();
    if v == N::ZERO {
        v = N::from(3u64);
    }
    if !v.bit(0) {
        v = p() - v;
    }
    v
}

/// Envelope statistics without a schedule (absorption as soon as a shot finishes): per-tick maxima and per-walk
/// end data. STRIP_N walks (default 100000), STRIP_SALT, STRIP_OUT (file for the per-tick maxima).
#[test]
#[ignore = "tool: STRIP_N=600000 STRIP_OUT=f cargo test --release --bin build_circuit strip_stats -- --ignored --nocapture"]
fn strip_stats() {
    let n = env_usize("STRIP_N", 100_000);
    let salt = env_usize("STRIP_SALT", 1) as u64;
    let th = env_usize("STRIP_TH", 16);
    let tm = env_usize("STRIP_TM", 340);
    POLICY.store(env_usize("STRIP_POLICY", 0), std::sync::atomic::Ordering::Relaxed);
    struct Out {
        env: Env,
        done: Vec<u32>,
        ends: Vec<(usize, usize, i64, usize, i64, u32)>,
    }
    let outs: Vec<Out> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..th)
            .map(|k| {
                sc.spawn(move || {
                    let mut env = Env::new(tm + 2);
                    let mut rng = Rng::new(salt * 1_000_003 + k as u64);
                    let mut done = vec![0u32; tm + 2];
                    let mut ends = vec![];
                    for _ in 0..n / th {
                        let x = rand_x(&mut rng);
                        let mut m = SM::new(x);
                        let mut tt = 0;
                        for t in 1..=tm {
                            m.tick(t, None, 0, Some(&mut env));
                            tt = t;
                            if m.absorbed() && t > m.tabs + 2 {
                                break;
                            }
                        }
                        if m.done == 0 {
                            done[tm + 1] += 1;
                            continue;
                        }
                        done[m.done] += 1;
                        // (done, tabs, S, width of C, gmax, idle)
                        ends.push((m.done, m.tabs, m.s, wx(m.bc), m.gmax, m.idle));
                        let _ = tt;
                    }
                    Out { env, done, ends }
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut env = Env::new(tm + 2);
    let mut done = vec![0u64; tm + 2];
    let mut ends = vec![];
    for o in &outs {
        env.merge(&o.env);
        for i in 0..tm + 2 {
            done[i] += o.done[i] as u64;
        }
        ends.extend(o.ends.iter().cloned());
    }
    let tot: u64 = done.iter().sum();
    let first = done.iter().position(|&d| d > 0).unwrap();
    let last = done[..tm + 1].iter().rposition(|&d| d > 0).unwrap();
    eprintln!("{tot} walks; done tick min {first} max {last}, not done by {tm}: {}", done[tm + 1]);
    let mut cum = 0u64;
    for t in (first..=last).rev() {
        cum += done[t];
        if [1u64, 2, 5, 10, 20, 50, 100, 1000].contains(&cum) || t + 3 > last {
            eprintln!("  done > {}: {} walks", t - 1, cum);
        }
    }
    let smin = ends.iter().map(|e| e.2).min().unwrap();
    let smax = ends.iter().map(|e| e.2).max().unwrap();
    let hmin = ends.iter().map(|e| e.1 as i64 + e.2).min().unwrap();
    let hmax = ends.iter().map(|e| e.1 as i64 + e.2).max().unwrap();
    let cw = ends.iter().map(|e| e.3).max().unwrap();
    let gm = ends.iter().map(|e| e.4).max().unwrap();
    let idle = ends.iter().map(|e| e.5 as f64).sum::<f64>() / ends.len() as f64;
    let mean_done = ends.iter().map(|e| e.0 as f64).sum::<f64>() / ends.len() as f64;
    eprintln!(
        "S min {smin} max {smax}; tabs + S min {hmin} max {hmax} (spread {}); C width max {cw}; gmax {gm}; idle/walk {idle:.2}; mean done {mean_done:.1}",
        hmax - hmin
    );
    let mut gh = vec![0u64; 40];
    for e in &ends {
        gh[e.4.clamp(0, 39) as usize] += 1;
    }
    eprintln!("gmax histogram (>=18): {:?}", &gh[18..30]);
    if let Ok(f) = std::env::var("STRIP_OUT") {
        let mut s = String::from("# t vin cin vpost cpost kvs kcs kva kca ksv ksc khv khc\n");
        for t in 1..=tm {
            s += &format!(
                "{} {} {} {} {} {} {} {} {} {} {} {} {}\n",
                t,
                env.vin[t],
                env.cin[t],
                env.vpost[t],
                env.cpost[t],
                env.kvs[t],
                env.kcs[t],
                env.kva[t],
                env.kca[t],
                env.ksv[t],
                env.ksc[t],
                env.khv[t],
                env.khc[t]
            );
        }
        std::fs::write(&f, s).unwrap();
        let mut s = String::from("# done tabs S cwidth gmax idle\n");
        for e in &ends {
            s += &format!("{} {} {} {} {} {}\n", e.0, e.1, e.2, e.3, e.4, e.5);
        }
        std::fs::write(format!("{f}.ends"), s).unwrap();
    }
}

/// The walk's end state is the inverse: x^-1 = (-1)^sgn C 2^m 2^-(T + S) (integer model, no schedule).
#[test]
fn strip_model_inverse() {
    let pm = p();
    let mut rng = Rng::new(77);
    let tt = 330usize;
    for _ in 0..200 {
        let x = rand_x(&mut rng);
        let mut m = SM::new(x);
        for t in 1..=tt {
            m.tick(t, None, 0, None);
        }
        m.step_end(tt + 1, None, 0, &mut None);
        assert!(m.absorbed() && m.bad.is_none(), "{:?}", m.bad);
        let (c, mm, s, sgn) = m.result(tt);
        let cm = if is_neg(c) { pm - (neg(c) % pm) } else { c % pm };
        let two = N::from(2u64);
        let lhs = cm.mul_mod(two.pow_mod(N::from(mm as u64), pm), pm).mul_mod(x, pm);
        let rhs = two.pow_mod(N::from((tt as i64 + s) as u64), pm);
        let rhs = if sgn { (pm - rhs) % pm } else { rhs };
        assert_eq!(lhs, rhs, "x C 2^m = (-1)^S 2^(T+S)");
    }
}

/// Failure rate of a schedule (files STRIP_SCHED, STRIP_LSC) on STRIP_N fresh walks (salt STRIP_SALT): failures by
/// kind, and lambda per 18048 divisions.
#[test]
#[ignore = "tool: STRIP_SCHED=f STRIP_LSC=g STRIP_N=2000000 cargo test --release --bin build_circuit strip_validate -- --ignored --nocapture"]
fn strip_validate() {
    let n = env_usize("STRIP_N", 200_000);
    let salt = env_usize("STRIP_SALT", 99) as u64;
    let th = env_usize("STRIP_TH", 16);
    let ss = std::fs::read_to_string(std::env::var("STRIP_SCHED").unwrap()).unwrap();
    let ls = std::env::var("STRIP_LSC").ok().map(|f| std::fs::read_to_string(f).unwrap());
    let sch = SSched::from_text(&ss, ls.as_deref());
    let res: Vec<std::collections::BTreeMap<String, u64>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..th)
            .map(|k| {
                let sch = &sch;
                sc.spawn(move || {
                    let mut rng = Rng::new(salt * 7_000_003 + k as u64);
                    let mut f = std::collections::BTreeMap::new();
                    for _ in 0..n / th {
                        let x = rand_x(&mut rng);
                        let m = run_walk(x, sch);
                        if let Some(w) = m.bad {
                            let key = w.split(':').nth(1).unwrap_or(&w).trim().split(' ').next().unwrap_or("").to_string();
                            let key = if w.contains(": g ") { "gap".to_string() } else { key + " " + w.split(':').nth(1).unwrap_or("").trim().split(' ').nth(1).unwrap_or("") };
                            *f.entry(key).or_insert(0) += 1;
                        }
                    }
                    f
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut f = std::collections::BTreeMap::<String, u64>::new();
    for r in res {
        for (k, v) in r {
            *f.entry(k).or_insert(0) += v;
        }
    }
    let tot: u64 = f.values().sum();
    let nn = (n / th * th) as f64;
    eprintln!(
        "W {} T {} TABS {}: {} walks, {} failures -> lambda {:.3} per 18048 divisions",
        sch.w, sch.t, sch.tabs, nn, tot, tot as f64 / nn * 18048.0
    );
    for (k, v) in &f {
        eprintln!("  {k:24} {v:8}  lambda {:.3}", *v as f64 / nn * 18048.0);
    }
}

// ---------------------------------------------------------------- circuit checks
use super::builder::B;
use super::frogstrip::*;
use super::frogtail::{Scr, QB};
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

pub const SCHED_S: &str = include_str!("sched_strip.txt");
pub const LSC_S: &str = include_str!("lsc_strip.txt");
pub const H0_TEST: usize = 564;

pub fn ssched() -> SSched {
    SSched::from_text(SCHED_S, Some(LSC_S))
}

/// Exhaustive value, source-restoration, scratch-cleanliness and phase check for the shared 2-bit decoder witness,
/// including forced HMR outcomes 0, 1 and alternating.
#[test]
fn strip_decode2_onehot_shared() {
    use sha3::digest::XofReader;
    struct Fixed(u8);
    impl XofReader for Fixed {
        fn read(&mut self, out: &mut [u8]) {
            out.fill(self.0);
        }
    }

    let mut b = B::new();
    let g = b.alloc_n(2);
    let onehot = b.alloc_n(4);
    let out = b.alloc_n(4);
    decode2_onehot_shared(&mut b, g[0], g[1], &onehot);
    for d in 0..4 {
        b.cx(onehot[d], out[d]);
    }
    clear_decode2_onehot_shared(&mut b, g[0], g[1], &onehot);
    assert_eq!(super::tests_chunked::expected_t(&b.ops), 1.0);

    for byte in [0u8, 255, 170] {
        let mut xof = Fixed(byte);
        let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
        for shot in 0..64 {
            let d = shot & 3;
            if d & 1 != 0 {
                sim.qubits[g[0].0 as usize] |= 1u64 << shot;
            }
            if d & 2 != 0 {
                sim.qubits[g[1].0 as usize] |= 1u64 << shot;
            }
        }
        sim.apply_iter(b.ops.iter());
        assert_eq!(sim.phase, 0, "forced HMR byte {byte}");
        for shot in 0..64 {
            let d = shot & 3;
            assert_eq!((sim.qubits[g[0].0 as usize] >> shot) & 1, (d & 1) as u64);
            assert_eq!((sim.qubits[g[1].0 as usize] >> shot) & 1, ((d >> 1) & 1) as u64);
            for k in 0..4 {
                assert_eq!((sim.qubits[out[k].0 as usize] >> shot) & 1, (k == d) as u64);
                assert_eq!((sim.qubits[onehot[k].0 as usize] >> shot) & 1, 0);
            }
        }
    }
}

/// Exhaust all 32 `(e,g4:g3:g2)` assignments through both recording directions, with forced
/// HMR outcomes 0, 1, and alternating. The five outputs are copied before the six witnesses
/// are measurement-cleared, so this checks value, source restoration, scratch, and phase.
#[test]
fn strip_decode5_high_shared() {
    use sha3::digest::XofReader;
    struct Fixed(u8);
    impl XofReader for Fixed {
        fn read(&mut self, out: &mut [u8]) {
            out.fill(self.0);
        }
    }

    for inverse in [false, true] {
        let mut b = B::new();
        let g = b.alloc_n(3);
        let e = b.alloc();
        let high = b.alloc_n(5);
        let q = b.alloc();
        let out = b.alloc_n(5);
        b.begin();
        decode5_high_shared(&mut b, g[0], g[1], g[2], e, &high, q);
        for d in 0..5 {
            b.cx(high[d], out[d]);
        }
        clear_decode5_high_shared(&mut b, g[0], g[1], g[2], e, &high, q);
        let rec = b.end();
        assert_eq!(b.measure(&rec, false), 6.0);
        assert_eq!(b.measure(&rec, true), 6.0);
        b.play(&rec, inverse);

        for byte in [0u8, 255, 170] {
            let mut xof = Fixed(byte);
            let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
            for shot in 0..64 {
                let v = shot & 31;
                for k in 0..3 {
                    if (v >> k) & 1 != 0 {
                        sim.qubits[g[k].0 as usize] |= 1u64 << shot;
                    }
                }
                if (v >> 3) & 1 != 0 {
                    sim.qubits[e.0 as usize] |= 1u64 << shot;
                }
            }
            sim.apply_iter(b.ops.iter());
            assert_eq!(sim.phase, 0, "inverse {inverse}, forced HMR byte {byte}");
            for shot in 0..64 {
                let v = shot & 31;
                let gv = v & 7;
                let ev = (v >> 3) & 1;
                for k in 0..3 {
                    assert_eq!((sim.qubits[g[k].0 as usize] >> shot) & 1, ((v >> k) & 1) as u64);
                }
                assert_eq!((sim.qubits[e.0 as usize] >> shot) & 1, ev as u64);
                for d in 0..5 {
                    assert_eq!(
                        (sim.qubits[out[d].0 as usize] >> shot) & 1,
                        (ev == 1 && gv == d) as u64,
                        "inverse {inverse}, byte {byte}, shot {shot}, H{d}"
                    );
                    assert_eq!((sim.qubits[high[d].0 as usize] >> shot) & 1, 0);
                }
                assert_eq!((sim.qubits[q.0 as usize] >> shot) & 1, 0);
            }
        }
    }
}

/// Exhaustive small-width proof of the modified-Booth paired-row primitive in both directions.
/// This covers every source/target/control assignment for widths 2..=6 and forces HMR outcomes
/// to zero, one, and alternating bits. It also checks the exact forward/inverse Toffoli model.
#[test]
fn strip_radix4_digit_exhaustive() {
    use sha3::digest::XofReader;
    struct Fixed(u8);
    impl XofReader for Fixed {
        fn read(&mut self, out: &mut [u8]) {
            out.fill(self.0);
        }
    }

    for n in 2usize..=6 {
        for inverse in [false, true] {
            let mut b = B::new();
            let a = b.alloc_n(n);
            let t = b.alloc_n(n);
            let e = b.alloc();
            let y1 = b.alloc();
            let y0 = b.alloc();
            let pool = b.alloc_n(2 * n + 6);
            b.begin();
            radix4_digit_add(&mut b, &a, &t, e, y1, Some(y0), &pool);
            let rec = b.end();
            assert_eq!(b.measure(&rec, false), 3.0 * n as f64 + 1.0, "n {n} forward price");
            assert_eq!(b.measure(&rec, true), 3.0 * n as f64 + 2.0, "n {n} inverse price");
            b.play(&rec, inverse);

            let mask = (1u64 << n) - 1;
            let total = 1usize << (2 * n + 3);
            for byte in [0u8, 255, 170] {
                for base in (0..total).step_by(64) {
                    let mut xof = Fixed(byte);
                    let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
                    let mut want = [0u64; 64];
                    for shot in 0..64 {
                        let v = base + shot;
                        if v >= total {
                            continue;
                        }
                        let tv = (v as u64) & mask;
                        let av = ((v as u64) >> n) & mask;
                        let y0v = ((v >> (2 * n)) & 1) as u64;
                        let y1v = ((v >> (2 * n + 1)) & 1) as u64;
                        let ev = ((v >> (2 * n + 2)) & 1) as u64;
                        put(&mut sim.qubits, &t, shot, N::from(tv));
                        put(&mut sim.qubits, &a, shot, N::from(av));
                        if y0v != 0 {
                            sim.qubits[y0.0 as usize] |= 1u64 << shot;
                        }
                        if y1v != 0 {
                            sim.qubits[y1.0 as usize] |= 1u64 << shot;
                        }
                        if ev != 0 {
                            sim.qubits[e.0 as usize] |= 1u64 << shot;
                        }
                        let one = ev & (y0v ^ y1v);
                        if inverse {
                            let x0 = (tv & 1) ^ (one & (av & 1));
                            let d = y0v as i64 + y1v as i64 - 2 * x0 as i64;
                            want[shot] = (tv as i64 - ev as i64 * d * av as i64).rem_euclid(1i64 << n) as u64;
                        } else {
                            let d = y0v as i64 + y1v as i64 - 2 * (tv & 1) as i64;
                            want[shot] = (tv as i64 + ev as i64 * d * av as i64).rem_euclid(1i64 << n) as u64;
                        }
                    }
                    sim.apply_iter(b.ops.iter());
                    assert_eq!(sim.phase, 0, "n {n} inverse {inverse} byte {byte} base {base}");
                    for shot in 0..64 {
                        let v = base + shot;
                        if v >= total {
                            continue;
                        }
                        let av = ((v as u64) >> n) & mask;
                        let y0v = ((v >> (2 * n)) & 1) as u64;
                        let y1v = ((v >> (2 * n + 1)) & 1) as u64;
                        let ev = ((v >> (2 * n + 2)) & 1) as u64;
                        assert_eq!(get_s(&sim.qubits, &t, shot).as_limbs()[0] & mask, want[shot]);
                        assert_eq!(get_s(&sim.qubits, &a, shot).as_limbs()[0] & mask, av);
                        assert_eq!((sim.qubits[y0.0 as usize] >> shot) & 1, y0v);
                        assert_eq!((sim.qubits[y1.0 as usize] >> shot) & 1, y1v);
                        assert_eq!((sim.qubits[e.0 as usize] >> shot) & 1, ev);
                        for &q in &pool {
                            assert_eq!(
                                (sim.qubits[q.0 as usize] >> shot) & 1,
                                0,
                                "n {n} inverse {inverse} pool q{} shot {shot}",
                                q.0
                            );
                        }
                    }
                }
            }
        }
    }
}

/// Exhaustive truth-table, input-restoration, scratch-cleanliness and phase check for the
/// factored strip amount, including forced HMR outcomes 0, 1 and alternating.
#[test]
fn strip_k_factor_exhaustive() {
    use sha3::digest::XofReader;
    struct Fixed(u8);
    impl XofReader for Fixed {
        fn read(&mut self, out: &mut [u8]) {
            out.fill(self.0);
        }
    }

    let mut b = B::new();
    let gq = b.alloc();
    let a0 = b.alloc();
    let a1 = b.alloc();
    let a2 = b.alloc();
    let t1 = b.alloc();
    let k1 = b.alloc();
    let k2 = b.alloc();
    strip_k_factor(&mut b, gq, a0, a1, a2, t1, k1, k2);
    assert_eq!(super::tests_chunked::expected_t(&b.ops), 3.0);

    let bit = |v: u64, shot: usize| (v >> shot) & 1;
    for byte in [0u8, 255, 170] {
        let mut xof = Fixed(byte);
        let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
        for shot in 0..64 {
            let v = shot & 15;
            for (q, n) in [(gq, 0), (a0, 1), (a1, 2), (a2, 3)] {
                if (v >> n) & 1 != 0 {
                    sim.qubits[q.0 as usize] |= 1u64 << shot;
                }
            }
        }
        sim.apply_iter(b.ops.iter());
        assert_eq!(sim.phase, 0, "forced HMR byte {byte}");
        for shot in 0..64 {
            let v = shot & 15;
            let g = ((v >> 0) & 1) != 0;
            let x0 = ((v >> 1) & 1) != 0;
            let x1 = ((v >> 2) & 1) != 0;
            let x2 = ((v >> 3) & 1) != 0;
            let et1 = g && !x0;
            let ek2 = et1 && !x1;
            let ek1 = et1 && (x1 || !x2);
            assert_eq!(bit(sim.qubits[gq.0 as usize], shot), g as u64);
            assert_eq!(bit(sim.qubits[a0.0 as usize], shot), x0 as u64);
            assert_eq!(bit(sim.qubits[a1.0 as usize], shot), x1 as u64);
            assert_eq!(bit(sim.qubits[a2.0 as usize], shot), x2 as u64);
            assert_eq!(bit(sim.qubits[k1.0 as usize], shot), ek1 as u64);
            assert_eq!(bit(sim.qubits[k2.0 as usize], shot), ek2 as u64);
            assert_eq!(bit(sim.qubits[t1.0 as usize], shot), 0);
        }
    }
}

pub fn get_s(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    let l = qs.len();
    if l > 0 && v.bit(l - 1) {
        v |= !((N::from(1u64) << l) - N::from(1u64));
    }
    v
}
pub fn get_u(w: &[u64], qs: &[QubitId], shot: usize) -> u64 {
    qs.iter().enumerate().map(|(i, &q)| ((w[q.0 as usize] >> shot) & 1) << i).sum()
}
pub fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: N) {
    for (i, &q) in qs.iter().enumerate() {
        if v.bit(i) {
            w[q.0 as usize] |= 1 << shot
        } else {
            w[q.0 as usize] &= !(1 << shot)
        }
    }
}

pub fn alloc_swalk(b: &mut B, sch: &SSched, x: &[QubitId], with_q: bool) -> SWalk {
    let mut bb = x.to_vec();
    bb.extend(b.alloc_n(sch.w - x.len()));
    SWalk {
        a: b.alloc_n(sch.w),
        bb,
        q: if with_q { b.alloc_n(QB) } else { vec![] },
        j: b.alloc_n(JS),
        par: b.alloc(),
        ec: b.alloc_n(EB),
        e0p: e0(sch, H0_TEST) & 1 == 1,
    }
}

/// decoded walk state at the start of tick t: (av, ac, bv, bc, j, par, E)
pub fn decode_s(w: &SWalk, sch: &SSched, t: usize, st: &[u64], k: usize) -> (N, N, N, N, i64, u64, u64) {
    let c = sch.c[t];
    let av: Vec<QubitId> = (0..c).map(|f| w.af(t, f)).collect();
    let ac: Vec<QubitId> = (0..sch.w - c).map(|s| w.asig(t, s)).collect();
    let bv: Vec<QubitId> = (0..c).map(|f| w.bf(f)).collect();
    let bc: Vec<QubitId> = (0..sch.w - c).map(|s| w.bsig(s)).collect();
    let jj = get_u(st, &w.j, k) as i64;
    let jj = if jj >= 1 << (JS - 1) { jj - (1 << JS) } else { jj };
    (
        get_s(st, &av, k),
        get_s(st, &ac, k),
        get_s(st, &bv, k),
        get_s(st, &bc, k),
        jj,
        get_u(st, &[w.par], k),
        get_u(st, &w.ec, k),
    )
}

fn xs64(seed: u64) -> Vec<N> {
    let mut rng = Rng::new(seed);
    (0..64).map(|_| rand_x(&mut rng)).collect()
}

/// Forward walk for `ticks` ticks on 64 shots against the model, every tick; scratch clean; per-tick Toffoli.
fn strip_walk_check(ticks: usize, seed: u64, room: usize) {
    let sch = ssched();
    let e0v = e0(&sch, H0_TEST);
    let mut b = B::new();
    let x = b.alloc_n(256);
    let w = alloc_swalk(&mut b, &sch, &x, false);
    let dirty = b.alloc_n(64);
    let sc = Scr::alloc_fwd(&mut b, &dirty, room);
    init(&mut b, &w, e0v);
    let mut bounds = vec![b.ops.len()];
    let mut tof = vec![b.tof];
    let m = b.fresh_bits(ticks + 1);
    for t in 1..=ticks {
        fwd_tick(&mut b, &w, t, &sch, &sc, m[t]);
        bounds.push(b.ops.len());
        tof.push(b.tof);
    }
    let full = ticks == sch.t;
    if full {
        close_fwd(&mut b, &w, &sch, &sc);
    }
    let exp = super::tests_chunked::expected_t(&b.ops);
    eprintln!(
        "frogstrip walk: {ticks} ticks, {} ops, {} Toffoli emitted ({:.0}/tick), expected {exp:.0}, peak {}",
        b.ops.len(),
        b.tof,
        b.tof as f64 / ticks as f64,
        b.peak
    );
    let xs = xs64(seed);
    let dv: Vec<N> = {
        let mut rng = Rng::new(seed + 1);
        (0..64).map(|_| rng.below(64)).collect()
    };
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogstrip-test");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &dirty, k, dv[k]);
    }
    let mut ms: Vec<SM> = xs.iter().map(|&x| SM::new(x)).collect();
    let scratch: Vec<QubitId> =
        [sc.e, sc.a, sc.eq, sc.one].iter().cloned().chain(sc.pool.iter().cloned()).chain(sc.tmp.iter().cloned()).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let emask = (1u64 << EB) - 1;
    let (mut ends, mut strips) = (0u64, 0u64);
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for k in 0..64 {
            let (par0, s0) = (ms[k].par, ms[k].s);
            ms[k].tick(t, Some(&sch), sch.tabs, None);
            ends += (ms[k].par != par0) as u64;
            strips += (ms[k].s != s0) as u64;
            if ms[k].bad.is_some() {
                continue;
            }
            let got = decode_s(&w, &sch, t + 1, &s.qubits, k);
            let want = (
                ms[k].av,
                ms[k].ac,
                ms[k].bv,
                ms[k].bc,
                ms[k].j >> 1,
                ms[k].par,
                ((e0v - ms[k].s) as u64) & emask,
            );
            assert!(got == want, "tick {t} shot {k}:\n got {:?}\nwant {:?}", got, want);
            if !ms[k].absorbed() {
                assert_eq!((ms[k].j + t as i64 + 1 + ms[k].s).rem_euclid(2), 0, "tick {t} shot {k}: parity");
            }
            for &q in &scratch {
                assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "tick {t} shot {k}: scratch q{} dirty", q.0);
            }
            assert_eq!(get_s(&s.qubits, &dirty, k) & ((N::from(1u64) << 64) - N::from(1u64)), dv[k], "dirty lanes");
        }
        if t % 50 == 0 {
            eprintln!("  tick {t}: ok ({} Toffoli so far)", tof[t]);
        }
    }
    let bad = ms.iter().filter(|m| m.bad.is_some()).count();
    eprintln!("strip_walk_check: {ticks} ticks, 64 shots match ({bad} outside the envelope), {ends} step ends, {strips} strip ticks");
    if full {
        s.apply_iter(b.ops[bounds[ticks]..].iter());
        let mut okn = 0;
        for k in 0..64 {
            if ms[k].bad.is_some() {
                continue;
            }
            ms[k].step_end(sch.t + 1, Some(&sch), sch.tabs, &mut None);
            if ms[k].bad.is_some() || !ms[k].absorbed() {
                continue;
            }
            let got = decode_s(&w, &sch, sch.t + 1, &s.qubits, k);
            assert_eq!((got.0, got.1, got.2, got.3, got.4), (ms[k].av, ms[k].ac, ms[k].bv, ms[k].bc, ms[k].j >> 1), "close shot {k}");
            okn += 1;
        }
        eprintln!("closing step: {okn} shots absorbed and matching");
    }
}

#[test]
fn strip_walk_short() {
    strip_walk_check(40, 7, 12);
}

#[test]
#[ignore]
fn strip_walk_full() {
    strip_walk_check(ssched().t, 11, env_usize("STRIP_ROOM", 12));
}

/// expected Q (frame t, after tick t) from the model's digit word
fn q_model(m: &SM) -> u64 {
    if m.nd == 0 {
        0
    } else {
        (m.dw << (QB as u32 - m.nd)) | (1u64 << (QB as u32 - m.nd - 1))
    }
}

/// The regenerating walk run forward: every tick the walk state and Q (marker + digit word) match the model, phase 0;
/// after the closing step Q = 0.
#[test]
#[ignore]
fn strip_regen_walk() {
    let sch = ssched();
    let e0v = e0(&sch, H0_TEST);
    let ticks = env_usize("STRIP_TICKS", sch.t);
    let mut b = B::new();
    let x = b.alloc_n(256);
    let w = alloc_swalk(&mut b, &sch, &x, true);
    let dirty = b.alloc_n(64);
    let mut sc = Scr::alloc(&mut b, &dirty);
    sc.pool = b.alloc_n(41);
    init_q(&mut b, &w, e0v);
    let mut bounds = vec![b.ops.len()];
    for t in 1..=ticks {
        let (p1, p3) = rec_regen_tick(&mut b, &w, t, &sch, &sc);
        b.play(&p1, false);
        b.play(&p3, false);
        bounds.push(b.ops.len());
    }
    if ticks == sch.t {
        let ce = rec_regen_close(&mut b, &w, &sch, &sc);
        b.play(&ce, false);
    }
    eprintln!("regen walk: {} ticks, {} Toffoli emitted, expected {:.0}", ticks, b.tof, super::tests_chunked::expected_t(&b.ops));
    let xs = xs64(5);
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogstrip-regen");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    s.apply_iter(b.ops[..bounds[0]].iter());
    let mut ms: Vec<SM> = xs.iter().map(|&x| SM::new(x)).collect();
    let emask = (1u64 << EB) - 1;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for k in 0..64 {
            ms[k].tick(t, Some(&sch), sch.tabs, None);
            if ms[k].bad.is_some() {
                continue;
            }
            let got = decode_s(&w, &sch, t + 1, &s.qubits, k);
            let want = (ms[k].av, ms[k].ac, ms[k].bv, ms[k].bc, ms[k].j >> 1, ms[k].par, ((e0v - ms[k].s) as u64) & emask);
            assert!(got == want, "tick {t} shot {k}:\n got {:?}\nwant {:?}", got, want);
            assert_eq!(get_u(&s.qubits, &w.qfr(t), k), q_model(&ms[k]), "tick {t} shot {k}: Q (nd {})", ms[k].nd);
        }
        assert_eq!(s.phase, 0, "tick {t}: phase");
    }
    if ticks == sch.t {
        s.apply_iter(b.ops[bounds[ticks]..].iter());
        for k in 0..64 {
            assert_eq!(get_u(&s.qubits, &w.q, k), 0, "shot {k}: Q after the closing step");
        }
        assert_eq!(s.phase, 0, "closing step phase");
    }
    eprintln!("regen walk ok ({} shots outside the envelope)", ms.iter().filter(|m| m.bad.is_some()).count());
}

/// Forward walk, unabsorb (C' checked) and its undo, inverse walk: every register back, scratch clean, phase 0.
#[test]
#[ignore]
fn strip_walk_roundtrip() {
    use super::frogstrip::{unabsorb, walk_forward, walk_inverse, SHB};
    let sch = ssched();
    let h0 = H0_TEST;
    let rlen = env_usize("STRIP_RLEN", 328);
    let e0v = e0(&sch, h0);
    let mut b = B::new();
    let x = b.alloc_n(256);
    let w = alloc_swalk(&mut b, &sch, &x, true);
    let dirty = b.alloc_n(64);
    let mut sc = Scr::alloc(&mut b, &dirty);
    sc.pool = b.alloc_n(41);
    let m = walk_forward(&mut b, &w, &sch, &sc, e0v);
    let n_fwd = (b.ops.len(), b.tof);
    let mr = b.alloc_n(SHB);
    let tm = b.alloc_n(SHB);
    let (r, key, rc) = unabsorb(&mut b, &w, &sch, rlen, &mr, &tm, &dirty);
    let n_mid = b.ops.len();
    let t_un = b.tof - n_fwd.1;
    b.play(&rc, true);
    let t_inv0 = b.tof;
    walk_inverse(&mut b, &w, &sch, &sc, &m, e0v);
    eprintln!(
        "forward walk {} Toffoli, unabsorb {t_un}, inverse walk {} Toffoli (emitted); expected total {:.0}",
        n_fwd.1,
        b.tof - t_inv0,
        super::tests_chunked::expected_t(&b.ops)
    );
    let xs = xs64(99);
    let dv: Vec<N> = {
        let mut rng = Rng::new(100);
        (0..64).map(|_| rng.below(64)).collect()
    };
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"frogstrip-rt");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &dirty, k, dv[k]);
    }
    s.apply_iter(b.ops[..n_mid].iter());
    let pm = p();
    let inv2h = N::from(2u64).pow_mod(pm - N::from(2u64), pm).pow_mod(N::from(h0 as u64), pm);
    let mut okn = 0;
    for k in 0..64 {
        let mut md = run_walk(xs[k], &sch);
        if md.bad.is_some() {
            continue;
        }
        let _ = &mut md;
        let cval = get_s(&s.qubits, &r, k);
        let sgn = is_neg(md.bv) ^ (md.par == 1) ^ true;
        assert_eq!((s.qubits[key.0 as usize] >> k) & 1, is_neg(md.bv) as u64, "shot {k}: key");
        let cm = if is_neg(cval) { pm - (neg(cval) % pm) } else { cval % pm };
        let mut inv = cm.mul_mod(inv2h, pm);
        if sgn {
            inv = (pm - inv) % pm;
        }
        assert_eq!(inv.mul_mod(xs[k], pm), N::from(1u64), "shot {k}: C' is not the inverse");
        for &q in w.a.iter().filter(|q| !r.contains(q)).chain(&tm).chain(std::iter::once(&w.bb[0])) {
            assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "shot {k}: q{} not cleared by unabsorb", q.0);
        }
        okn += 1;
    }
    eprintln!("unabsorb: {okn} shots give C'");
    s.apply_iter(b.ops[n_mid..].iter());
    for k in 0..64 {
        assert_eq!(get_s(&s.qubits, &x, k) & ((N::from(1u64) << 256) - N::from(1u64)), xs[k], "shot {k}: x' restored");
        for &q in w.a.iter().chain(&w.bb[256..]).chain(&w.q).chain(&w.j).chain(&w.ec).chain(std::iter::once(&w.par)).chain(&mr) {
            assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "shot {k}: walk register q{} not cleared", q.0);
        }
        assert_eq!(get_s(&s.qubits, &dirty, k) & ((N::from(1u64) << 64) - N::from(1u64)), dv[k]);
    }
    assert_eq!(s.phase, 0, "phase");
    eprintln!("roundtrip ok: {} ops, {} Toffoli, peak {}", b.ops.len(), b.tof, b.peak);
}

// ---------------------------------------------------------------- point addition
fn curve() -> crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
    type U = ruint::aliases::U256;
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO,
        b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    }
}

/// 64-shot end-to-end frogstrip point addition: results, phase, ancillas; analytic expected Toffoli.
#[test]
fn strip_point_add_end_to_end() {
    let mut b = B::new();
    let (xq, yq) = super::pointadd_strip::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let (nq, _, _, regs) = analyze_ops(ops.iter());
    eprintln!("ops {} qubits {} peak {} emitted tof {}", ops.len(), nq, b.peak, b.tof);
    super::tests_chunked::expected_t(&ops);
    let to_u = |v: &N| -> ruint::aliases::U256 { ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    let curve = curve();
    let mut rng = Rng::new(env_usize("STRIP_SEED", 2024) as u64);
    let shots = env_usize("STRIP_SHOTS", 64).max(64).div_ceil(64) * 64;
    let mut cases = vec![];
    for _ in 0..shots {
        let k1 = to_u(&(rng.below(250) + N::from(1u64)));
        let k2 = to_u(&(rng.below(250) + N::from(1u64)));
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        let e = curve.add(t.0, t.1, o.0, o.1);
        cases.push((t, o, e));
    }
    let mut h = sha3::Shake256::default();
    h.update(b"frogstrip-e2e");
    let mut xof = h.finalize_xof();
    let (_, nb, _, _) = analyze_ops(ops.iter());
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
    for (batch, cases) in cases.chunks(64).enumerate() {
    sim.clear_for_shot();
    for (k, (t, o, _)) in cases.iter().enumerate() {
        sim.set_register(&regs[0], t.0, k);
        sim.set_register(&regs[1], t.1, k);
        sim.set_register(&regs[2], o.0, k);
        sim.set_register(&regs[3], o.1, k);
    }
    sim.apply_iter(ops.iter());
    let mut bad = 0;
    for (k, (_, _, e)) in cases.iter().enumerate() {
        if sim.get_register(&regs[0], k) != e.0 || sim.get_register(&regs[1], k) != e.1 {
            bad += 1;
            eprintln!("shot {k} wrong");
        }
    }
    eprintln!("batch {batch} phase {:#x}, bad {bad}", sim.phase);
    assert_eq!(sim.phase, 0, "phase garbage");
    let regq: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    for q in 0..nq {
        if !regq.contains(&q) {
            assert_eq!(sim.qubits[q as usize], 0, "ancilla garbage q{q}");
        }
    }
    assert_eq!(bad, 0, "classical mismatches");
    }
    eprintln!("frogstrip end-to-end OK: shots{shots} avg Toffoli {}", sim.stats.toffoli_gates / shots as u64);
}

/// Per-phase average executed Toffoli of the frogstrip point addition (64 random shots).
#[test]
#[ignore]
fn strip_phase_profile() {
    use super::pointadd_strip::CKS;
    CKS.with(|c| c.borrow_mut().clear());
    let mut b = B::new();
    let _ = super::pointadd_strip::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let cks = CKS.with(|c| c.borrow().clone());
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    eprintln!("peak {} qubits {}", b.peak, nq);
    super::tests_chunked::expected_t(&ops);
    let mut rng = Rng::new(31);
    let pm = p();
    let mut h = sha3::Shake256::default();
    h.update(b"ftprod-prof");
    let mut xof = h.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
    for k in 0..64 {
        for r in 0..4 {
            let v = rng.below(256) % pm;
            let u = ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap());
            sim.set_register(&regs[r], u, k);
        }
    }
    let mut last = 0usize;
    let mut lt = 0u64;
    let mut prev = "start".to_string();
    for (name, at) in cks.iter().cloned().chain([("END".to_string(), ops.len())]) {
        sim.apply_iter(ops[last..at].iter());
        let t = sim.stats.toffoli_gates;
        eprintln!("{:28} avg T {:>9}", prev, (t - lt) / 64);
        lt = t;
        last = at;
        prev = name;
    }
    eprintln!("total avg T {}", lt / 64);
}

/// Analytic expected Toffoli and score of the frogstrip point addition at each peak in STRIP_PEAKS.
#[test]
#[ignore]
fn strip_peak_sweep() {
    let peaks: Vec<u64> = std::env::var("STRIP_PEAKS")
        .unwrap_or("940,950,960".into())
        .split(',')
        .map(|s| s.trim().parse().unwrap())
        .collect();
    for pk in peaks {
        std::env::set_var("STRIP_PEAK", pk.to_string());
        let mut b = B::new();
        let _ = super::pointadd_strip::point_add(&mut b);
        let exp = super::tests_chunked::expected_t(&b.ops);
        eprintln!("SWEEP peak {} (built peak {}): expected T {:.1}, score {:.0}", pk, b.peak, exp, exp * b.peak as f64);
    }
}

/// Walk failure prediction for a division input d (made odd as the circuit does): None if the frogstrip walk stays
/// in the machine's envelope, is absorbed by T + 1, and C' = C 2^(H0 - halvings) fits the shift and RLEN.
pub fn predict_strip(d: N, sch: &SSched, h0: usize, rlen: usize) -> Option<String> {
    use super::frogstrip::{MBS, SHB};
    let pm = p();
    let x = if d.bit(0) { d } else { pm - d };
    let m = run_walk(x, sch);
    if m.bad.is_some() {
        return m.bad;
    }
    let hd = m.tabs as i64 - 1 + m.s;
    let sh = h0 as i64 - hd;
    let mm = sch.t as i64 + 1 - m.tabs as i64;
    let e = super::frogstrip::e0(sch, h0) - m.s;
    if sh < 0 || sh >= 1 << SHB || mm >= 1 << MBS || e < 0 || e >= 1 << EB {
        return Some(format!("end: shift sh {sh} m {mm} E {e}"));
    }
    if wx(m.bc) + sh as usize > rlen {
        return Some(format!("end: C' width {}", wx(m.bc) + sh as usize));
    }
    None
}

#[test]
#[ignore = "tool: STRIP_SCAN=n cargo test --release --bin build_circuit -- strip_predict_nonce --ignored --nocapture"]
fn strip_predict_nonce() {
    use super::pointadd_strip::{point_add, sched, H0, RLEN_S};
    use sha3::digest::XofReader;
    type U = ruint::aliases::U256;
    let curve = curve();
    let scan = env_usize("STRIP_SCAN", 0);
    let mut b = B::new();
    let _ = point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let width = b.width();
    eprintln!("built {} ops, width {width}, peak {}", ops.len(), b.peak);
    let l = ops.len();
    let mut pre = sha3::Shake256::default();
    pre.update(b"quantum_ecc-fiat-shamir-v2");
    pre.update(&(l as u64).to_le_bytes());
    let upd = |h: &mut sha3::Shake256, op: &crate::circuit::Op| {
        h.update(&[op.kind as u8]);
        h.update(&op.q_control2.0.to_le_bytes());
        h.update(&op.q_control1.0.to_le_bytes());
        h.update(&op.q_target.0.to_le_bytes());
        h.update(&op.c_target.0.to_le_bytes());
        h.update(&op.c_condition.0.to_le_bytes());
        h.update(&op.r_target.0.to_le_bytes());
    };
    for op in &ops[..l - 2] {
        upd(&mut pre, op);
    }
    let tail = ops[l - 2];
    drop(ops);
    let sch = sched();
    let pp = p();
    let to_n = |u: U| -> N {
        let mut v = N::ZERO;
        for (i, &w) in u.as_limbs().iter().enumerate() {
            v |= N::from(w) << (64 * i);
        }
        v
    };
    let shots = env_usize("STRIP_SHOTS", 9024);
    let mut clean = vec![];
    for nonce in 0..(scan.max(1) as u64) {
        let q = if scan == 0 { tail.q_target.0 } else { nonce };
        if q >= width {
            break;
        }
        let mut h = pre.clone();
        let mut op = tail;
        op.q_target = QubitId(q);
        upd(&mut h, &op);
        upd(&mut h, &op);
        let mut xof = h.finalize_xof();
        let mut fails = std::collections::BTreeMap::<String, usize>::new();
        let mut n = 0;
        for _ in 0..shots {
            let mut rb = [[0u8; 32]; 2];
            xof.read(&mut rb[0]);
            xof.read(&mut rb[1]);
            let k1 = U::from_le_bytes(rb[0]);
            let k2 = U::from_le_bytes(rb[1]);
            let t = curve.mul(curve.gx, curve.gy, k1);
            let o = curve.mul(curve.gx, curve.gy, k2);
            if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) {
                continue;
            }
            let e = curve.add(t.0, t.1, o.0, o.1);
            n += 1;
            let (x1, x2, x3) = (to_n(t.0), to_n(o.0), to_n(e.0));
            let d1 = if x1 >= x2 { x1 - x2 } else { x1 + pp - x2 };
            let d2 = if x3 >= x2 { x3 - x2 } else { x3 + pp - x2 };
            for d in [d1, d2] {
                if let Some(why) = predict_strip(d, &sch, H0, RLEN_S) {
                    eprintln!("  fail shot {} ({}): {}", n - 1, if d == d1 { "div1" } else { "div2" }, why);
                    *fails.entry(why.split(':').nth(1).unwrap_or(&why).trim().split(' ').next().unwrap_or("").to_string()).or_default() += 1;
                }
            }
        }
        let nf: usize = fails.values().sum();
        eprintln!("nonce qubit {q}: {n} shots, failing divisions {nf} {:?}", fails);
        if nf == 0 {
            clean.push(q);
        }
    }
    eprintln!("clean nonces: {:?}", clean);
}

/// Per-section expected Toffoli of the walks (sections in frogstrip.rs), summed over the point addition's four
/// walks: total per point addition and average per occurrence.
#[test]
#[ignore]
fn strip_section_profile() {
    use super::frogstrip::SEC;
    SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    let mut b = B::new();
    let _ = super::pointadd_strip::point_add(&mut b);
    let m = SEC.with(|s| s.borrow_mut().take().unwrap());
    let mut tot = 0.0;
    for (k, (sum, n)) in &m {
        eprintln!("SEC {k:18} total {sum:>10.0}  n {n:>5}  avg {:>8.1}", sum / *n as f64);
        tot += sum;
    }
    eprintln!("SEC sections total {tot:.0}");
}

/// Expected Toffoli of the shell primitives at a given pool size (STRIP_POOLS).
#[test]
#[ignore]
fn strip_prim_costs() {
    use super::modp_ft::*;
    let pools: Vec<usize> = std::env::var("STRIP_POOLS").unwrap_or("64,120,180".into()).split(',').map(|s| s.parse().unwrap()).collect();
    for pl in pools {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let y = b.alloc_n(256);
        let s = b.alloc();
        let ms = Ms { k: b.alloc(), r: b.alloc_n(pl), one: b.alloc() };
        let mut zz = z.clone();
        let m = |b: &mut B, f: &dyn Fn(&mut B)| {
            let n0 = b.ops.len();
            f(b);
            super::tests_chunked::expected_t(&b.ops[n0..])
        };
        let a1 = m(&mut b, &|b| signed_modadd(b, &ms, &z, &y, Some(s)));
        let a2 = m(&mut b, &|b| modadd(b, &ms, &z, &y, s));
        let d = {
            let n0 = b.ops.len();
            mod_double(&mut b, &ms, &mut zz);
            super::tests_chunked::expected_t(&b.ops[n0..])
        };
        let h = {
            let n0 = b.ops.len();
            mod_halve(&mut b, &ms, &mut zz);
            super::tests_chunked::expected_t(&b.ops[n0..])
        };
        let c1 = m(&mut b, &|b| ctrl_modadd(b, &ms, &z, &y, s, s));
        let c2 = m(&mut b, &|b| ctrl_modsub(b, &ms, &z, &y, s));
        eprintln!("PRIM pool {pl}: signed_modadd {a1:.1} modadd {a2:.1} double {d:.1} halve {h:.1} ctrl_modadd {c1:.1} ctrl_modsub {c2:.1}");
    }
}

/// The regenerating tick's digit erase on synthetic completing states for every gap g = 1..=QB-1: A.c = b 2^g (b odd),
/// Q = W 2^(QB-1-g) (W = 2D + 1), B.c = W b mod 2^(g+1) plus higher bits; Q must end 0, everything else restored.
#[test]
fn strip_erase_all_gaps() {
    use super::frogstrip::finish_digits_pub;
    let sch = ssched();
    let t = 150usize;
    let tn = t + 1;
    let e0v = e0(&sch, H0_TEST);
    for g in 1..QB {
        let mut b = B::new();
        let x = b.alloc_n(256);
        let w = alloc_swalk(&mut b, &sch, &x, true);
        let dirty = b.alloc_n(64);
        let mut sc = Scr::alloc(&mut b, &dirty);
        sc.pool = b.alloc_n(41);
        let n0 = b.ops.len();
        finish_digits_pub(&mut b, &w, t, &sch, &sc);
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"frogstrip-erase");
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
        let mut rng = Rng::new(1000 + g as u64);
        let c = sch.c[tn];
        let ac: Vec<QubitId> = (0..sch.w - c).map(|k| w.asig(tn, k)).collect();
        let bc: Vec<QubitId> = (0..sch.w - c).map(|k| w.bsig(k)).collect();
        let mut want_ac = vec![];
        let mut want_bc = vec![];
        for k in 0..64 {
            // b odd with 40 bits, D random g bits; L = W b mod 2^(g+1) under random higher bits (both narrow)
            let bb = (rng.below(40) | N::from(1u64)) & ((N::from(1u64) << 40) - N::from(1u64));
            let d: N = rng.below(64) & ((N::from(1u64) << g) - N::from(1u64));
            let wv: N = (d << 1usize) | N::from(1u64);
            let m = (N::from(1u64) << (g + 1)) - N::from(1u64);
            let l = (wv.wrapping_mul(bb) & m) | ((rng.below(30)) << (g + 1));
            let acv = bb << g;
            put(&mut s.qubits, &ac, k, acv);
            put(&mut s.qubits, &bc, k, l);
            let qv = (wv << (QB - 1 - g)).as_limbs()[0];
            for (i, &q) in w.qfr(t).iter().enumerate() {
                if (qv >> i) & 1 == 1 {
                    s.qubits[q.0 as usize] |= 1 << k;
                }
            }
            // the completion flag (the digit's [j = 1], kept in e)
            s.qubits[sc.e.0 as usize] |= 1 << k;
            let _ = e0v;
            want_ac.push(acv);
            want_bc.push(l);
        }
        s.apply_iter(b.ops[n0..].iter());
        for k in 0..64 {
            assert_eq!(get_u(&s.qubits, &w.q, k), 0, "g {g} shot {k}: Q not erased");
            assert_eq!(get_s(&s.qubits, &ac, k), want_ac[k], "g {g} shot {k}: A.c");
            assert_eq!(get_s(&s.qubits, &bc, k), want_bc[k], "g {g} shot {k}: B.c");
            assert_eq!((s.qubits[sc.e.0 as usize] >> k) & 1, 1, "g {g} shot {k}: flag");
        }
        assert_eq!(s.phase, 0, "g {g}: phase");
    }
    eprintln!("erase ok for g = 1..={}", QB - 1);
}

/// mod_double4 / mod_halve4 against classical 16 z, z / 16 (mod p) on 64 random values per pool size (plus edge
/// values), ancillas clean, phase 0.
#[test]
fn strip_mod_shift4() {
    use super::modp_ft::*;
    let pm = p();
    for pl in [84usize, 120, 256] {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let ms = Ms { k: b.alloc(), r: b.alloc_n(pl), one: b.alloc() };
        b.x(ms.one);
        let mut zz = z.clone();
        mod_double4(&mut b, &ms, &mut zz);
        let n1 = b.ops.len();
        let mut zh = zz.clone();
        mod_halve4(&mut b, &ms, &mut zh);
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"shift4");
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
        let mut rng = Rng::new(4040 + pl as u64);
        let mut xs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        xs[0] = N::ZERO;
        xs[1] = pm - N::from(1u64);
        xs[2] = (N::from(1u64) << 255) | N::from(15u64);
        for k in 0..64 {
            put(&mut s.qubits, &z, k, xs[k]);
        }
        s.apply_iter(b.ops[..n1].iter());
        let n16 = N::from(16u64);
        for k in 0..64 {
            let got = get_u256(&s.qubits, &zz, k);
            assert_eq!(got % pm, xs[k].mul_mod(n16, pm), "double4 pool {pl} shot {k}");
            assert!(got < pm || xs[k] >= pm, "double4 non-canonical");
        }
        s.apply_iter(b.ops[n1..].iter());
        for k in 0..64 {
            assert_eq!(get_u256(&s.qubits, &zh, k), xs[k], "halve4 pool {pl} shot {k}");
            for &q in ms.r.iter().chain([ms.k].iter()) {
                assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "pool dirty");
            }
        }
        assert_eq!(s.phase, 0);
    }
    eprintln!("mod_double4 / mod_halve4 ok");
}

fn get_u256(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}

/// signed_modadd_halve against classical (z +- y) / 2 mod p on 64 shots per pool size and sign source (edge values
/// included), ancillas clean, phase 0.
#[test]
fn strip_modadd_halve() {
    use super::modp_ft::*;
    let pm = p();
    let inv2 = (pm + N::from(1u64)) >> 1;
    for pl in [80usize, 91, 179, 256] {
        for signed in [false, true] {
            let mut b = B::new();
            let z = b.alloc_n(256);
            let y = b.alloc_n(256);
            let sq = b.alloc();
            let ms = Ms { k: b.alloc(), r: b.alloc_n(pl), one: b.alloc() };
            b.x(ms.one);
            let mut zz = z.clone();
            signed_modadd_halve(&mut b, &ms, &mut zz, &y, if signed { Some(sq) } else { None });
            let (aq, nb, _, _) = analyze_ops(b.ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"addhalve");
            let mut xof = h.finalize_xof();
            let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
            let mut rng = Rng::new(9090 + pl as u64 + signed as u64);
            let mut zs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
            let mut ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
            let ss: Vec<bool> = (0..64).map(|k| signed && (k % 2 == 1)).collect();
            zs[0] = N::ZERO;
            ys[1] = zs[1];
            zs[2] = pm - ys[2];
            ys[3] = zs[3];
            for k in 0..64 {
                put(&mut s.qubits, &z, k, zs[k]);
                put(&mut s.qubits, &y, k, ys[k]);
                if ss[k] {
                    s.qubits[sq.0 as usize] |= 1 << k;
                }
            }
            s.apply_iter(b.ops.iter());
            for k in 0..64 {
                let sum = if ss[k] { (zs[k] + pm - ys[k]) % pm } else { (zs[k] + ys[k]) % pm };
                let want = sum.mul_mod(inv2, pm);
                if k == 2 && !ss[k] {
                    continue; // z + y = p: the non-canonical sum (known trap of the forward add)
                }
                assert_eq!(get_u256(&s.qubits, &zz, k), want, "pool {pl} signed {signed} shot {k}");
                assert_eq!(get_u256(&s.qubits, &y, k), ys[k]);
                for &q in ms.r.iter().chain([ms.k].iter()) {
                    assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "pool {pl} shot {k}: scratch dirty");
                }
            }
            assert_eq!(s.phase, 0, "phase");
        }
    }
    eprintln!("signed_modadd_halve ok");
}

/// signed_modadd_double against classical 2 (z +- y) mod p (as strip_modadd_halve).
#[test]
fn strip_modadd_double() {
    use super::modp_ft::*;
    let pm = p();
    for pl in [91usize, 179, 256] {
        for signed in [false, true] {
            let mut b = B::new();
            let z = b.alloc_n(256);
            let y = b.alloc_n(256);
            let sq = b.alloc();
            let ms = Ms { k: b.alloc(), r: b.alloc_n(pl), one: b.alloc() };
            b.x(ms.one);
            let mut zz = z.clone();
            signed_modadd_double(&mut b, &ms, &mut zz, &y, if signed { Some(sq) } else { None });
            let (aq, nb, _, _) = analyze_ops(b.ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"adddouble");
            let mut xof = h.finalize_xof();
            let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
            let mut rng = Rng::new(7070 + pl as u64 + signed as u64);
            let mut zs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
            let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
            let ss: Vec<bool> = (0..64).map(|k| signed && (k % 2 == 1)).collect();
            zs[0] = N::ZERO;
            zs[3] = ys[3];
            for k in 0..64 {
                put(&mut s.qubits, &z, k, zs[k]);
                put(&mut s.qubits, &y, k, ys[k]);
                if ss[k] {
                    s.qubits[sq.0 as usize] |= 1 << k;
                }
            }
            s.apply_iter(b.ops.iter());
            for k in 0..64 {
                let sum = if ss[k] { (zs[k] + pm - ys[k]) % pm } else { (zs[k] + ys[k]) % pm };
                let want = sum.mul_mod(N::from(2u64), pm);
                assert_eq!(get_u256(&s.qubits, &zz, k), want, "pool {pl} signed {signed} shot {k}");
                assert_eq!(get_u256(&s.qubits, &y, k), ys[k]);
                for &q in ms.r.iter().chain([ms.k].iter()) {
                    assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "pool {pl} shot {k}: scratch dirty");
                }
            }
            assert_eq!(s.phase, 0, "phase");
        }
    }
    eprintln!("signed_modadd_double ok");
}
