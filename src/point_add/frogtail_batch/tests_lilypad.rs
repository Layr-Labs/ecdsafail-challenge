//! Lilypad-GCD audit build tests: forward walk and regenerating walk against an integer model on 64 shots every tick
//! (rings, h, Q word, scratch, phase), and the paired forward + inverse round trip at a qubit cap with Toffoli
//! counts (expected executed, the metric) and the peak.
//! LILYPAD_SCHED = schedule file, LILYPAD_QB = Q lanes (default 20), LILYPAD_CAP = cap (pool fills to it), LILYPAD_TICKS,
//! LILYPAD_SEED.
use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::lilypad::*;
use super::pointadd_lilypad;
use super::tests_frogdrop::Rng;
use super::tests_strip::{get_s, get_u, put};
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

fn sched() -> PSched {
    let f = std::env::var("LILYPAD_SCHED").expect("LILYPAD_SCHED");
    PSched::from_text(&std::fs::read_to_string(f).unwrap())
}

/// Exhaust all `(e,g4:g3:g2)` assignments through the Q885 three-high
/// decoder, including both recording directions and forced HMR outcomes.
#[test]
fn lilypad_decode3_high_exact() {
    use sha3::digest::XofReader;
    struct Fixed(u8);
    impl XofReader for Fixed {
        fn read(&mut self, out: &mut [u8]) { out.fill(self.0); }
    }

    for inverse in [false, true] {
        let mut b = B::new();
        let g = b.alloc_n(3);
        let e = b.alloc();
        let high = b.alloc_n(3);
        let w = b.alloc();
        let out = b.alloc_n(3);
        b.begin();
        decode3_high_lilypad(&mut b, g[0], g[1], g[2], e, &high, w);
        for d in 0..3 { b.cx(high[d], out[d]); }
        clear_decode3_high_lilypad(&mut b, g[0], g[1], g[2], e, &high, w);
        let rec = b.end();
        assert_eq!(b.measure(&rec, false), 4.0);
        assert_eq!(b.measure(&rec, true), 4.0);
        b.play(&rec, inverse);

        for byte in [0u8, 255, 170] {
            let mut xof = Fixed(byte);
            let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
            for shot in 0..32 {
                let v = shot & 15;
                for k in 0..3 {
                    if (v >> k) & 1 != 0 { sim.qubits[g[k].0 as usize] |= 1u64 << shot; }
                }
                if (v >> 3) & 1 != 0 { sim.qubits[e.0 as usize] |= 1u64 << shot; }
            }
            sim.apply_iter(b.ops.iter());
            assert_eq!(sim.phase, 0, "inverse {inverse}, forced HMR byte {byte}");
            for shot in 0..32 {
                let v = shot & 15;
                let gv = v & 7;
                let ev = (v >> 3) & 1;
                for k in 0..3 {
                    assert_eq!((sim.qubits[g[k].0 as usize] >> shot) & 1, ((gv >> k) & 1) as u64);
                    assert_eq!((sim.qubits[high[k].0 as usize] >> shot) & 1, 0);
                    assert_eq!((sim.qubits[out[k].0 as usize] >> shot) & 1, (ev == 1 && gv == k) as u64);
                }
                assert_eq!((sim.qubits[e.0 as usize] >> shot) & 1, ev as u64);
                assert_eq!((sim.qubits[w.0 as usize] >> shot) & 1, 0);
            }
        }
    }
}

#[test]
fn lilypad_dec_topless_exact() {
    let mut b = B::new();
    let ctrl = b.alloc();
    let bits = b.alloc_n(5);
    let anc = b.alloc_n(3);
    super::arith::dec_topless(&mut b, ctrl, &bits, &anc);
    let mut xr = xof(b"lilypad-dec-topless");
    let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
    for shot in 0..64 {
        let value = shot & 31;
        let cv = (shot >> 5) & 1;
        if cv != 0 {
            s.qubits[ctrl.0 as usize] |= 1u64 << shot;
        }
        for (i, q) in bits.iter().enumerate() {
            if value >> i & 1 != 0 {
                s.qubits[q.0 as usize] |= 1u64 << shot;
            }
        }
    }
    s.apply_iter(b.ops.iter());
    assert_eq!(s.phase, 0);
    for shot in 0..64 {
        let value = shot & 31;
        let cv = (shot >> 5) & 1;
        assert_eq!(get_u(&s.qubits, &bits, shot) as usize, (value + 32 - cv) & 31, "shot {shot}");
        assert!(anc.iter().all(|q| (s.qubits[q.0 as usize] >> shot) & 1 == 0));
    }
}

#[test]
fn lilypad_const_add_topless_exact() {
    for n in 2usize..=5 {
        for k in 1u64..1u64 << n {
            for shortage in 1usize..=2 {
            let mut b = B::new();
            let ctrl = b.alloc();
            let target = b.alloc_n(n);
            let need = n - 1 - (k.trailing_zeros() as usize).min(n - 1);
            if need < shortage + 1 {
                continue;
            }
            let i0 = k.trailing_zeros() as usize;
            let tail_len = shortage + 1;
            let start = n - tail_len;
            if start - i0 < tail_len - 2 {
                continue;
            }
            let pool = b.alloc_n(need - shortage);
            super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
            let mut xr = xof(format!("lilypad-const-topless-{n}-{k}-{shortage}").as_bytes());
            let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
            for shot in 0..64 {
                let value = shot & ((1usize << n) - 1);
                let cv = (shot >> n) & 1;
                if cv != 0 {
                    s.qubits[ctrl.0 as usize] |= 1u64 << shot;
                }
                for (i, q) in target.iter().enumerate() {
                    if value >> i & 1 != 0 {
                        s.qubits[q.0 as usize] |= 1u64 << shot;
                    }
                }
            }
            s.apply_iter(b.ops.iter());
            assert_eq!(s.phase, 0, "n={n} k={k} shortage={shortage}");
            for shot in 0..64 {
                let value = shot & ((1usize << n) - 1);
                let cv = (shot >> n) & 1;
                let want = (value + cv * k as usize) & ((1usize << n) - 1);
                assert_eq!(get_u(&s.qubits, &target, shot) as usize, want, "n={n} k={k} shortage={shortage} shot={shot}");
                assert!(pool.iter().all(|q| (s.qubits[q.0 as usize] >> shot) & 1 == 0));
            }
            }
        }
    }
}

#[test]
fn lilypad_const_add_multi_topless_exact() {
    let n = 8usize;
    for shortage in 3usize..=4 {
        for k in 1u64..1u64 << n {
            let need = n - 1 - (k.trailing_zeros() as usize).min(n - 1);
            if need < shortage + 1 {
                continue;
            }
            let i0 = k.trailing_zeros() as usize;
            let tail_len = shortage + 1;
            let start = n - tail_len;
            if start - i0 < tail_len - 2 {
                continue;
            }
            let mut b = B::new();
            let ctrl = b.alloc();
            let target = b.alloc_n(n);
            let pool = b.alloc_n(need - shortage);
            super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
            for cv in 0usize..=1 {
                for batch in 0usize..4 {
                let mut xr = xof(format!("lilypad-const-multi-topless-{k}-{shortage}-{cv}").as_bytes());
                let mut s = Simulator::new(b.width() as usize, 1, &mut xr);
                if cv != 0 {
                    s.qubits[ctrl.0 as usize] = u64::MAX;
                }
                for shot in 0..64usize {
                    let value = batch * 64 + shot;
                    for (i, q) in target.iter().enumerate() {
                        if value >> i & 1 != 0 {
                            s.qubits[q.0 as usize] |= 1u64 << shot;
                        }
                    }
                }
                s.apply_iter(b.ops.iter());
                assert_eq!(s.phase, 0, "k={k} shortage={shortage} cv={cv}");
                for shot in 0..64usize {
                    let value = batch * 64 + shot;
                    let want = (value + cv * k as usize) & 255;
                    assert_eq!(get_u(&s.qubits, &target, shot) as usize, want, "k={k} shortage={shortage} cv={cv} value={value}");
                    assert!(pool.iter().all(|q| (s.qubits[q.0 as usize] >> shot) & 1 == 0));
                }
                }
            }
        }
    }
}


/// Independent integer oracle over all valid eight-bit shortage2..4 shapes,
/// input/control values, and every lower-carry measurement assignment.
#[test]
fn lilypad_const_add_signed_tail_exhaustive() {
    use sha3::digest::XofReader;
    struct Outcomes { assignment: usize, position: usize }
    impl XofReader for Outcomes {
        fn read(&mut self, out: &mut [u8]) {
            assert_eq!(out.len(), 8);
            out.fill(if (self.assignment >> self.position) & 1 != 0 { 255 } else { 0 });
            self.position += 1;
        }
    }
    let mut checked = 0u64;
    let mut shapes = 0;
    let mut negative_shapes = 0;
    for shortage in 2usize..=4 {
        for k in 1u64..256 {
            let i0 = k.trailing_zeros() as usize;
            let start = 8 - shortage - 1;
            if i0 >= start || start - i0 < shortage - 1 { continue; }
            let pool_len = 7 - i0 - shortage;
            let mut b = B::new();
            let ctrl = b.alloc();
            let target = b.alloc_n(8);
            let pool = b.alloc_n(pool_len);
            super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
            let (nq, nb, _, _) = analyze_ops(b.ops.iter());
            shapes += 1;
            negative_shapes += usize::from((k >> start) > (1u64 << shortage));
            for outcomes in 0..1usize << pool_len {
                for cv in 0..=1u64 {
                    for base in (0usize..256).step_by(64) {
                        let mut rng = Outcomes { assignment: outcomes, position: 0 };
                        let mut s = Simulator::new(nq as usize, nb as usize, &mut rng);
                        s.qubits[ctrl.0 as usize] = if cv == 1 { u64::MAX } else { 0 };
                        for lane in 0..64 {
                            for (i, q) in target.iter().enumerate() {
                                s.qubits[q.0 as usize] |= (((base + lane) >> i & 1) as u64) << lane;
                            }
                        }
                        s.apply_iter(b.ops.iter());
                        assert_eq!(s.phase, 0, "phase k={k} shortage={shortage} outcomes={outcomes} cv={cv}");
                        assert_eq!(s.qubits[ctrl.0 as usize], if cv == 1 { u64::MAX } else { 0 });
                        assert!(pool.iter().all(|q| s.qubits[q.0 as usize] == 0));
                        for lane in 0..64 {
                            assert_eq!(get_u(&s.qubits, &target, lane) as u64, (base as u64 + lane as u64 + cv * k) & 255);
                        }
                        assert_eq!(rng.position, pool_len);
                        checked += 64;
                    }
                }
            }
        }
    }
    assert!(negative_shapes > 0);
    eprintln!("SIGNED_TAIL_EXHAUSTIVE shapes={shapes} negative_shapes={negative_shapes} scalar_assignments={checked} PASS");
}

#[test]
fn lilypad_const_add_signed_tail_production_width() {
    use sha3::digest::XofReader;
    let constants = [1u64, 977, 0x1_0000_03d1, 0x8000_0000_0000_0001, 0xaaaa_aaaa_aaaa_aaab, u64::MAX, 0x9e37_79b9, 0xffff_ffff_61c8_8647, 0x8000_01e8];
    let mut checked = 0;
    for k in constants {
        let mut b = B::new();
        let ctrl = b.alloc();
        let target = b.alloc_n(64);
        let pool = b.alloc_n(59);
        super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
        if k == 0xffff_ffff_61c8_8647 { assert_eq!(b.tof, 109); }
        let (nq, nb, _, _) = analyze_ops(b.ops.iter());
        for cv in 0..=1u64 {
            let mut data_rng = xof(format!("shortage5-data-{k}-{cv}").as_bytes());
            for batch in 0..24usize {
                let mut values = [0u64; 64];
                for (lane, value) in values.iter_mut().enumerate() {
                    *value = if batch < 8 {
                        let low = [0, 1, (1u64 << 58) - 1, (1u64 << 58) - 2, 1u64 << 57, (1u64 << 57) - 1,
                            0x02aa_aaaa_aaaa_aaaa, 0x0155_5555_5555_5555][batch];
                        ((lane as u64) << 58) | low
                    } else {
                        let mut bytes = [0; 8]; data_rng.read(&mut bytes); u64::from_le_bytes(bytes)
                    };
                }
                let mut rng = xof(format!("shortage5-measure-{k}-{cv}-{batch}").as_bytes());
                let mut s = Simulator::new(nq as usize, nb as usize, &mut rng);
                s.qubits[ctrl.0 as usize] = if cv == 1 { u64::MAX } else { 0 };
                for (lane, value) in values.iter().enumerate() {
                    for (i, q) in target.iter().enumerate() {
                        s.qubits[q.0 as usize] |= ((value >> i) & 1) << lane;
                    }
                }
                s.apply_iter(b.ops.iter());
                assert_eq!(s.phase, 0, "phase k={k} cv={cv} batch={batch}");
                assert_eq!(s.qubits[ctrl.0 as usize], if cv == 1 { u64::MAX } else { 0 });
                assert!(pool.iter().all(|q| s.qubits[q.0 as usize] == 0));
                for (lane, value) in values.iter().enumerate() {
                    assert_eq!(get_u(&s.qubits, &target, lane) as u64, value.wrapping_add(cv * k));
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 27_648);
    eprintln!("SIGNED_TAIL_PRODUCTION_WIDTH scalar_assignments={checked} PASS");
}


const TOP: usize = 383;
fn sar1(v: N) -> N {
    let top = N::from(1u64) << TOP;
    (v >> 1usize) | (v & top)
}
fn tcb(v: N) -> usize {
    if v.bit(TOP) {
        (!v).bit_len() + 1
    } else {
        v.bit_len() + 1
    }
}

#[derive(Clone, Debug)]
struct Pm {
    f: N,
    g: N,
    cf: N,
    cg: N,
    d2: i64,
    cur: Vec<(usize, u8)>,
    pend: Vec<(usize, u8)>,
    bad: Option<String>,
    nev: usize,
}

impl Pm {
    fn new(x: N) -> Pm {
        Pm { f: p(), g: x, cf: N::ZERO, cg: N::from(1u64), d2: 1, cur: vec![], pend: vec![], bad: None, nev: 0 }
    }
    fn tick(&mut self, t: usize, sch: &PSched, qb: usize) {
        if self.bad.is_some() {
            return;
        }
        let (kv, kc) = (sch.kv[t], sch.kc[t]);
        let e = self.g.bit(0);
        let sw = e && self.d2 > 0;
        let r = !sw && self.d2 < 0;
        let pre = [self.f, self.g, self.cf, self.cg];
        if sw {
            let (f, g, cf, cg) = (self.f, self.g, self.cf, self.cg);
            self.f = g;
            self.g = sar1(g.wrapping_sub(f));
            self.cf = cg << 1usize;
            self.cg = cg.wrapping_sub(cf);
            self.d2 = 2 - self.d2;
            let q = env_usize("LILYPAD_CAPQ", 0) as i64;
            if q > 0 && self.d2 <= -(2 * q - 1) {
                let o = (-(2 * q - 1) - self.d2) / 2;
                self.d2 = -(2 * q - 1);
                self.nev += 1;
                if o > 15 || self.nev > env_usize("LILYPAD_K", 2) {
                    self.bad = Some(format!("cap log overflow t {t}"));
                }
            }
        } else {
            let gn = if e { self.g.wrapping_add(self.f) } else { self.g };
            self.g = sar1(gn);
            if e {
                self.cg = self.cg.wrapping_add(self.cf);
            }
            self.cf <<= 1usize;
            self.d2 += 2;
        }
        let vw = [tcb(pre[0]), tcb(pre[1]), tcb(self.f), tcb(self.g) + 1].into_iter().max().unwrap();
        let cw = [tcb(pre[2]), tcb(pre[3]), tcb(sar1(self.cf)), tcb(self.cg)].into_iter().max().unwrap();
        if vw > kv || cw > kc {
            self.bad = Some(format!("width t {t}: v {vw}/{kv} c {cw}/{kc}"));
        }
        if t == sch.s && (tcb(self.f).max(tcb(self.g)) > sch.kv[t + 1] || tcb(self.cf).max(tcb(self.cg)) > sch.kc[t + 1]) {
            self.bad = Some("end width".into());
        }
        let h = (self.d2 - 1) / 2;
        if !(-64..=63).contains(&h) {
            self.bad = Some("h range".into());
        }
        // digit word (marker + digits), ring frame positions
        if sw {
            assert!(self.cur.is_empty(), "t {t}: swap inside a run");
            self.cur = vec![(t, 1)];
        } else if r {
            self.cur.push((t, e as u8));
        }
        if self.cur.iter().chain(self.pend.iter()).any(|&(tau, _)| t - tau >= qb) {
            self.bad = Some(format!("QB overflow t {t}"));
        }
        if sw && self.d2 == 1 {
            self.cur.clear();
        }
        if r && self.d2 == 1 {
            let ic = self.cur.len().saturating_sub(1);
            let deferred = t % 2 == 1;
            let tau = if deferred { (t + 1).min(sch.s) } else { t };
            let region = sch.w - sch.c[tau];
            if 2 * ic + 2 + usize::from(deferred) > region {
                self.bad = Some(format!("window overflow t {t}"));
            }
            if t % 2 == 0 {
                self.cur.clear();
            } else {
                self.pend = std::mem::take(&mut self.cur);
            }
        }
        if t % 2 == 0 {
            self.pend.clear();
        }
    }
    fn qval(&self, t: usize, qb: usize) -> u64 {
        self.cur.iter().chain(self.pend.iter()).map(|&(tau, bit)| (bit as u64) << (qb - 1 - (t - tau))).sum()
    }
}

fn rand_x(rng: &mut Rng) -> N {
    let mut v = rng.below(256) % p();
    if v == N::ZERO {
        v = N::from(3u64);
    }
    v
}

struct Setup {
    b: B,
    y: Vec<QubitId>,
    x: Vec<QubitId>,
    w: PWalk,
}

fn setup(sch: &PSched, qb: usize, with_y: bool, with_q: bool) -> Setup {
    let capq = env_usize("LILYPAD_CAPQ", 0);
    setup_with_capq(sch, qb, with_y, with_q, capq)
}

fn setup_with_capq(sch: &PSched, qb: usize, with_y: bool, with_q: bool, capq: usize) -> Setup {
    let mut b = B::new();
    let y = if with_y { b.alloc_n(256) } else { vec![] };
    let x = b.alloc_n(256);
    let mut a = x.clone();
    a.extend(b.alloc_n(sch.w - 256));
    let w = PWalk { a, bb: b.alloc_n(sch.w), q: if with_q { b.alloc_n(qb) } else { vec![] }, h: b.alloc_n(HB), capq,
        log: if capq > 0 { b.alloc_n(4 * env_usize("LILYPAD_K", 2)) } else { vec![] } };
    Setup { b, y, x, w }
}

fn decode(w: &PWalk, sch: &PSched, t: usize, st: &[u64], k: usize) -> (N, N, N, N, u64) {
    let c = sch.c[t];
    let xv: Vec<QubitId> = (0..c).map(|f| w.af(t, f)).collect();
    let xc: Vec<QubitId> = (0..sch.w - c).map(|s| w.asig(t, s)).collect();
    let yv: Vec<QubitId> = (0..c).map(|f| w.bf(f)).collect();
    let yc: Vec<QubitId> = (0..sch.w - c).map(|s| w.bsig(s)).collect();
    (get_s(st, &yv, k), get_s(st, &xv, k), get_s(st, &xc, k), get_s(st, &yc, k), get_u(st, &w.h, k))
}

fn sim<'a>(b: &B, xof: &'a mut sha3::Shake256Reader) -> Simulator<'a, sha3::Shake256Reader> {
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), xof)
}

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = sha3::Shake256::default();
    h.update(tag);
    h.finalize_xof()
}

fn terminal_witness() -> N {
    let s = std::env::var("LILYPAD_X").unwrap_or_else(|_| "576d9924e2cf53d5f1c40cade115d639a7c3dbd1f3c764f069848459a53b1499".into());
    N::from_str_radix(s.trim_start_matches("0x"), 16).unwrap()
}

fn check_tick(w: &PWalk, sch: &PSched, t: usize, st: &[u64], ms: &[Pm], qb: usize, with_q: bool) -> usize {
    let mut nbad = 0;
    for (k, m) in ms.iter().enumerate() {
        if m.bad.is_some() {
            nbad += 1;
            continue;
        }
        let got = decode(w, sch, t + 1, st, k);
        let want = (m.f, m.g, m.cf, m.cg, (((m.d2 - 1) / 2) as u64) & 127);
        assert!(got == want, "tick {t} shot {k}:\n got {:?}\nwant {:?}", got, want);
        if with_q {
            assert_eq!(get_u(st, &w.qfr(t), k), m.qval(t, qb), "tick {t} shot {k}: Q (cur {:?} pend {:?})", m.cur, m.pend);
        }
    }
    nbad
}

/// Forward walk against the model every tick; scratch clean; per-tick expected Toffoli.
#[test]
#[ignore]
fn lilypad_fwd_check() {
    let sch = sched();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 24);
    let mut s0 = setup(&sch, 0, false, false);
    let sc = PScr::alloc_fwd(&mut s0.b, room);
    let Setup { mut b, x, w, .. } = s0;
    init(&mut b, &w);
    let mut bounds = vec![b.ops.len()];
    let m = b.fresh_bits(ticks + 1);
    for t in 1..=ticks {
        step_core(&mut b, &w, t, &sch, &sc, sc.e, &[], None);
        halve_h(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        bounds.push(b.ops.len());
    }
    let exp = super::tests_chunked::expected_t(&b.ops);
    eprintln!("lilypad fwd: {ticks} ticks, emitted {} expected {exp:.0} ({:.1}/tick), peak {}", b.tof, exp / ticks as f64, b.peak);
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 1) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-fwd");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Pm> = xs.iter().map(|&v| Pm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let scratch: Vec<QubitId> = [sc.e, sc.sg].iter().cloned().chain(sc.tmp.iter().cloned()).chain(sc.pool.iter().cloned()).collect();
    let mut nbad = 0;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for m in ms.iter_mut() {
            m.tick(t, &sch, 64);
        }
        nbad = check_tick(&w, &sch, t, &s.qubits, &ms, 64, false);
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & ms.iter().enumerate().filter(|(_, m)| m.bad.is_none()).map(|(k, _)| 1u64 << k).sum::<u64>(), 0, "tick {t}: scratch dirty");
        }
    }
    let gzero = ms.iter().filter(|m| m.bad.is_none() && m.g == N::ZERO).count();
    eprintln!("lilypad fwd ok: {ticks} ticks, 64 shots match ({nbad} outside the envelope), g = 0 at the end on {gzero}");
}

/// The regenerating walk run forward: rings, h and Q (marker + digits, deferred erasures) match the model every
/// tick, phase 0, Q = 0 at the end.
#[test]
#[ignore]
fn lilypad_regen_check() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 20);
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 24);
    let mut s0 = setup(&sch, qb, false, true);
    let sc = PScr::alloc_inv(&mut s0.b, room);
    let Setup { mut b, x, w, .. } = s0;
    init(&mut b, &w);
    let mut bounds = vec![b.ops.len()];
    let mut inv_cost = 0.0;
    for t in 1..=ticks {
        let (p1, p3) = rec_regen(&mut b, &w, t, &sch, &sc, None);
        inv_cost += b.measure(&p1, true) + b.measure(&p3, true);
        b.play(&p1, false);
        b.play(&p3, false);
        bounds.push(b.ops.len());
    }
    let exp = super::tests_chunked::expected_t(&b.ops);
    eprintln!("lilypad regen (qb {qb}): {ticks} ticks, played forward: emitted {} expected {exp:.0}; as the inverse walk plays it: {inv_cost:.0} ({:.1}/tick); peak {}",
        b.tof, inv_cost / ticks as f64, b.peak);
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 2) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-regen");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Pm> = xs.iter().map(|&v| Pm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let mut scratch: Vec<QubitId> = [sc.e, sc.sg].iter().cloned().chain(sc.tmp.iter().cloned()).chain(sc.pool.iter().cloned()).collect();
    scratch.extend(&sc.d);
    scratch.extend(&sc.sp);
    let mut nbad = 0;
    let mut erased = 0u64;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for m in ms.iter_mut() {
            let had = !m.cur.is_empty() || !m.pend.is_empty();
            m.tick(t, &sch, qb);
            if had && m.cur.is_empty() && m.pend.is_empty() {
                erased += 1;
            }
        }
        nbad = check_tick(&w, &sch, t, &s.qubits, &ms, qb, true);
        let good: u64 = ms.iter().enumerate().filter(|(_, m)| m.bad.is_none()).map(|(k, _)| 1u64 << k).sum();
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & good, 0, "tick {t}: scratch q{} dirty", q.0);
        }
        assert_eq!(s.phase & good, 0, "tick {t}: phase");
    }
    let open = ms.iter().filter(|m| m.bad.is_none() && (!m.cur.is_empty() || !m.pend.is_empty())).count();
    eprintln!("lilypad regen ok: {ticks} ticks, 64 shots, Q/rings/h match every tick, phase 0, {erased} word erasures, {nbad} outside, {open} with an open word at the end");
}

/// Paired forward + inverse at a cap (y register live, as in the point add): round trip exact (x back, all else 0,
/// phase 0) and the expected Toffoli of each walk; SEC profile when LILYPAD_SEC is set.
#[test]
#[ignore]
fn lilypad_count() {
    use super::frogstrip::SEC;
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 20);
    let cap = env_usize("LILYPAD_CAP", 906) as u64;
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let s0 = setup(&sch, qb, true, false);
    let Setup { mut b, y, x, mut w } = s0;
    let live_f = b.live + 2 + NT as u64;
    let nev: usize = 0;
    let _ = nev;
    let room_f = cap.saturating_sub(live_f) as usize;
    let sc = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let n0 = b.ops.len();
    let m = walk_forward(&mut b, &w, &sch, &sc, Some(div));
    let n1 = b.ops.len();
    sc.release(&mut b);
    let pk_f = b.peak;
    w.q = b.alloc_n(qb);
    let live_i = b.live + 3 + NT as u64 + SB as u64;
    let room_i = cap.saturating_sub(live_i) as usize;
    let sc = PScr::alloc_inv(&mut b, room_i);
    walk_inverse(&mut b, &w, &sch, &sc, &m, Some(div));
    let n2 = b.ops.len();
    b.close_division(div);
    let ef = super::tests_chunked::expected_t(&b.ops[n0..n1]);
    let ei = super::tests_chunked::expected_t(&b.ops[n1..n2]);
    eprintln!(
        "LILYPAD_COUNT W {} S {} qb {qb} cap {cap}: fwd live {live_f} pool {room_f} | inv live {live_i} pool {room_i} | fwd {ef:.0} ({:.1}/tick) inv {ei:.0} ({:.1}/tick) ratio {:.3} | peak fwd {pk_f} overall {}",
        sch.w, sch.s, ef / sch.s as f64, ei / sch.s as f64, ei / ef, b.peak
    );
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (k, (sum, n)) in &mm {
            eprintln!("SEC {k:14} total {sum:>10.0}  n {n:>5}  avg {:>8.1}", sum / *n as f64);
        }
    }
    if std::env::var("LILYPAD_NOSIM").is_ok() {
        return;
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 3) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-count");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let mut ms: Vec<Pm> = xs.iter().map(|&v| Pm::new(v)).collect();
    for t in 1..=sch.s {
        for mm in ms.iter_mut() {
            mm.tick(t, &sch, qb);
        }
    }
    let good: Vec<usize> = (0..64).filter(|&k| ms[k].bad.is_none() && ms[k].cur.is_empty() && ms[k].pend.is_empty()).collect();
    let gm: u64 = good.iter().map(|&k| 1u64 << k).sum();
    let mut other: Vec<QubitId> = w.a[256..].to_vec();
    other.extend(&w.bb);
    other.extend(&w.q);
    other.extend(&w.h);
    other.extend(&w.log);
    for &k in &good {
        assert_eq!(get_s(&s.qubits, &x, k) & ((N::from(1u64) << 256) - N::from(1u64)), xs[k], "shot {k}: x");
        assert_eq!(get_s(&s.qubits, &y, k) & ((N::from(1u64) << 256) - N::from(1u64)), ys[k], "shot {k}: y");
    }
    for &q in &other {
        assert_eq!(s.qubits[q.0 as usize] & gm, 0, "q{} dirty after the round trip", q.0);
    }
    assert_eq!(s.phase & gm, 0, "round-trip phase");
    eprintln!("lilypad round trip ok on {} / 64 shots (rest outside the envelope / QB)", good.len());
}

fn build_roundtrip(sch: &PSched, qb: usize, cap: u64) -> (B, Vec<QubitId>, Vec<QubitId>) {
    let Setup { mut b, y, x, mut w } = setup(sch, qb, true, false);
    let room_f = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sc = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let m = walk_forward(&mut b, &w, sch, &sc, Some(div));
    sc.release(&mut b);
    w.q = b.alloc_n(qb);
    let room_i = cap.saturating_sub(b.live + 3 + NT as u64 + SB as u64) as usize;
    let sc = PScr::alloc_inv(&mut b, room_i);
    walk_inverse(&mut b, &w, sch, &sc, &m, Some(div));
    b.close_division(div);
    (b, x, y)
}

fn verify_roundtrip_batch(
    b: &B,
    x: &[QubitId],
    y: &[QubitId],
    sch: &PSched,
    qb: usize,
    xs: &[N],
    ys: &[N],
    tag: &[u8],
) -> (usize, usize) {
    let mut xr = xof(tag);
    let mut s = sim(b, &mut xr);
    for k in 0..xs.len() {
        put(&mut s.qubits, x, k, xs[k]);
        put(&mut s.qubits, y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let mut models: Vec<Pm> = xs.iter().map(|&v| Pm::new(v)).collect();
    for t in 1..=sch.s {
        for m in &mut models {
            m.tick(t, sch, qb);
        }
    }
    for m in &mut models {
        if m.bad.is_none() && m.g != N::ZERO {
            m.bad = Some("overrun".into());
        }
    }
    let good: Vec<usize> = (0..xs.len()).filter(|&k| models[k].bad.is_none()).collect();
    let gm: u64 = good.iter().map(|&k| 1u64 << k).sum();
    let mask = (N::from(1u64) << 256) - N::from(1u64);
    for &k in &good {
        assert_eq!(get_s(&s.qubits, x, k) & mask, xs[k], "shot {k}: x");
        assert_eq!(get_s(&s.qubits, y, k) & mask, ys[k], "shot {k}: y");
    }
    let mut data = vec![false; s.qubits.len()];
    for q in x.iter().chain(y.iter()) {
        data[q.0 as usize] = true;
    }
    for (i, row) in s.qubits.iter().enumerate() {
        if !data[i] {
            assert_eq!(*row & gm, 0, "ancilla q{i} dirty");
        }
    }
    assert_eq!(s.phase & gm, 0, "round-trip phase");
    (good.len(), xs.len() - good.len())
}

/// First gate-level q=11 campaign: at least 10k random secp256k1 inputs.
/// Predicted envelope/QB/log failures are counted; every other shot must be
/// value-, ancilla-, and phase-exact.
#[test]
#[ignore]
fn lilypad_design_d_roundtrip_10k() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let (b, x, y) = build_roundtrip(&sch, qb, cap);
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 0x11d) as u64);
    let mut checked = 0;
    let mut predicted = 0;
    for batch in 0..157usize {
        let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
        let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
        let tag = format!("lilypad-q11-10k-{batch}");
        let (g, p) = verify_roundtrip_batch(&b, &x, &y, &sch, qb, &xs, &ys, tag.as_bytes());
        checked += g;
        predicted += p;
    }
    eprintln!("lilypad q11 10k: {checked} exact, {predicted} predicted approximation failures, total {}", checked + predicted);
    assert_eq!(checked + predicted, 10_048);
}

/// Cofactor-favoring split edge cases and a classical search for runs still
/// open at S.  Every selected input is then checked through the real gate walk.
#[test]
#[ignore]
fn lilypad_edge_inputs() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let (b, x, y) = build_roundtrip(&sch, qb, cap);
    let mut xs = vec![];
    let mut edge_rng = Rng::new(0xc0fa_c701u64);
    for k in 15..=19 {
        for _ in 0..4 {
            let odd = (rand_x(&mut edge_rng) >> k) | N::from(1u64);
            xs.push(odd << k);
        }
    }
    let mut rng = Rng::new(0x6e64_7275_6eu64);
    let mut scanned = 0usize;
    let mut open = 0usize;
    while scanned < 1_500_000 && open < 8 {
        let v = rand_x(&mut rng);
        let mut m = Pm::new(v);
        for t in 1..=sch.s {
            m.tick(t, &sch, qb);
        }
        if m.bad.is_none() && (!m.cur.is_empty() || !m.pend.is_empty()) {
            xs.push(v);
            open += 1;
        }
        scanned += 1;
    }
    assert!(open > 0, "no terminal-open-run witness in {scanned} inputs");
    let ys: Vec<N> = (0..xs.len()).map(|i| N::from((i + 17) as u64)).collect();
    let (g, pred) = verify_roundtrip_batch(&b, &x, &y, &sch, qb, &xs, &ys, b"lilypad-edge-inputs");
    eprintln!("lilypad edge inputs: {g} exact, {pred} predicted failures, {open} terminal-open witnesses from {scanned} scanned");
    assert_eq!(g, xs.len());
}

#[test]
#[ignore]
fn lilypad_terminal_word_trace() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let Setup { mut b, x, y, mut w } = setup(&sch, qb, true, false);
    let room_f = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sf = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    walk_forward(&mut b, &w, &sch, &sf, Some(div));
    sf.release(&mut b);
    let nf = b.ops.len();
    w.q = b.alloc_n(qb);
    let room_i = cap.saturating_sub(b.live + 3 + NT as u64 + SB as u64) as usize;
    let si = PScr::alloc_inv(&mut b, room_i);
    let tb = terminal_eraser(&mut b, &w, &sch, &si);
    let xval = terminal_witness();
    let mut pm = Pm::new(xval);
    for t in 1..=sch.s {
        pm.tick(t, &sch, qb);
    }
    let qwant = pm.qval(sch.s, qb);
    let mut xr = xof(b"lilypad-terminal-word-trace");
    let mut s = sim(&b, &mut xr);
    put(&mut s.qubits, &x, 0, xval);
    put(&mut s.qubits, &y, 0, N::from(17u64));
    s.apply_iter(b.ops[..nf].iter());
    let hend = get_u(&s.qubits, &w.h, 0);
    let mut qs = vec![];
    for end in [tb[1], tb[2], tb[3], b.ops.len()] {
        let start = if qs.is_empty() { nf } else { [tb[1], tb[2], tb[3]][qs.len() - 1] };
        s.apply_iter(b.ops[start..end].iter());
        qs.push(get_u(&s.qubits, &w.qfr(sch.s), 0));
    }
    let qgot = *qs.last().unwrap();
    eprintln!("terminal trace: h={hend} Q(word/rot/mul/final)={qs:?} want={qwant} phase={}", s.phase & 1);
    assert_eq!(qgot, qwant);
}

#[test]
#[ignore]
fn lilypad_terminal_integrated_trace() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let Setup { mut b, x, y, mut w } = setup(&sch, qb, true, false);
    let room_f = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sf = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let meas = walk_forward(&mut b, &w, &sch, &sf, Some(div));
    sf.release(&mut b);
    let nf = b.ops.len();
    w.q = b.alloc_n(qb);
    let room_i = cap.saturating_sub(b.live + 3 + NT as u64 + SB as u64) as usize;
    let si = PScr::alloc_inv(&mut b, room_i);
    let (p1, p3) = rec_regen(&mut b, &w, sch.s, &sch, &si, Some(div));
    b.play(&p3, true);
    let np3 = b.ops.len();
    b.z_if(w.qfr(sch.s)[qb - 1], meas[sch.s]);
    let nz = b.ops.len();
    b.play(&p1, true);
    let nstep = b.ops.len();
    let (p1b, p3b) = rec_regen(&mut b, &w, sch.s - 1, &sch, &si, Some(div));
    b.play(&p3b, true);
    let np3b = b.ops.len();
    b.z_if(w.qfr(sch.s - 1)[qb - 1], meas[sch.s - 1]);
    let nzb = b.ops.len();
    b.play(&p1b, true);
    let nstepb = b.ops.len();
    let xval = terminal_witness();
    let mut xr = xof(b"lilypad-terminal-integrated-trace");
    let mut s = sim(&b, &mut xr);
    put(&mut s.qubits, &x, 0, xval);
    put(&mut s.qubits, &y, 0, N::from(17u64));
    s.apply_iter(b.ops[..nf].iter());
    let mut vals = vec![];
    for (lo, hi) in [(nf, np3), (np3, nz), (nz, nstep)] {
        s.apply_iter(b.ops[lo..hi].iter());
        vals.push((get_u(&s.qubits, &w.qfr(sch.s), 0), get_u(&s.qubits, &w.h, 0), s.phase & 1));
    }
    let mut vals_b = vec![];
    for (lo, hi) in [(nstep, np3b), (np3b, nzb), (nzb, nstepb)] {
        s.apply_iter(b.ops[lo..hi].iter());
        vals_b.push((get_u(&s.qubits, &w.qfr(sch.s - 1), 0), get_u(&s.qubits, &w.h, 0), s.phase & 1));
    }
    let scratch: Vec<QubitId> = [si.e, si.sg]
        .into_iter()
        .chain(si.d.iter().copied())
        .chain(si.tmp.iter().copied())
        .chain(si.sp.iter().copied())
        .chain(si.pool.iter().copied())
        .collect();
    let dirty: Vec<u64> = scratch.iter().filter(|q| s.qubits[q.0 as usize] & 1 != 0).map(|q| q.0).collect();
    eprintln!("terminal integrated t532={vals:?} t531={vals_b:?}; dirty scratch={dirty:?}");
    assert_eq!(vals[0].0, 3 << (qb - 2));
    assert_eq!(vals[2].0, 1 << (qb - 2));
    assert_eq!(vals_b[0].0, 1 << (qb - 1));
    assert_eq!(vals_b[2].0, 0);
    assert!(dirty.is_empty());
}

#[test]
#[ignore]
fn lilypad_terminal_full_inverse_trace() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let Setup { mut b, x, y, mut w } = setup(&sch, qb, true, false);
    let room_f = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sf = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let meas = walk_forward(&mut b, &w, &sch, &sf, Some(div));
    sf.release(&mut b);
    let nf = b.ops.len();
    w.q = b.alloc_n(qb);
    let room_i = cap.saturating_sub(b.live + 3 + NT as u64 + SB as u64) as usize;
    let si = PScr::alloc_inv(&mut b, room_i);
    let mut bounds = vec![];
    for t in (1..=sch.s).rev() {
        let lo = b.ops.len();
        let (p1, p3) = rec_regen(&mut b, &w, t, &sch, &si, Some(div));
        b.play(&p3, true);
        b.z_if(w.qfr(t)[qb - 1], meas[t]);
        b.play(&p1, true);
        bounds.push((t, lo, b.ops.len()));
    }
    let xval = terminal_witness();
    let mut hist = vec![Pm::new(xval)];
    for t in 1..=sch.s {
        let mut m = hist.last().unwrap().clone();
        m.tick(t, &sch, qb);
        hist.push(m);
    }
    let mut xr = xof(b"lilypad-terminal-full-inverse-trace");
    let mut s = sim(&b, &mut xr);
    put(&mut s.qubits, &x, 0, xval);
    put(&mut s.qubits, &y, 0, N::from(17u64));
    s.apply_iter(b.ops[..nf].iter());
    for (t, lo, hi) in bounds {
        s.apply_iter(b.ops[lo..hi].iter());
        let got = decode(&w, &sch, t, &s.qubits, 0);
        let m = &hist[t - 1];
        let want = (m.f, m.g, m.cf, m.cg, (m.d2.div_euclid(2) as u64) & 127);
        if got != want {
            eprintln!("first inverse mismatch after tick {t}: Q={} phase={}\n got={got:?}\nwant={want:?}", get_u(&s.qubits, &w.qfr(t), 0), s.phase & 1);
            panic!("inverse mismatch at tick {t}");
        }
    }
    eprintln!("terminal full inverse trace exact; phase={}", s.phase & 1);
}

#[test]
#[ignore]
fn lilypad_c6_reference_corpus() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let path = std::env::var("LILYPAD_C6_CORPUS").expect("LILYPAD_C6_CORPUS");
    let xs: Vec<N> = std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .filter_map(|l| l.split_whitespace().next())
        .filter(|s| s.starts_with("0x"))
        .map(|s| N::from_str_radix(&s[2..], 16).unwrap())
        .collect();
    assert!(!xs.is_empty() && xs.len() <= 64);
    let ys: Vec<N> = (0..xs.len()).map(|i| N::from((i + 101) as u64)).collect();
    let (b, x, y) = build_roundtrip(&sch, qb, cap);
    let (good, predicted) = verify_roundtrip_batch(&b, &x, &y, &sch, qb, &xs, &ys, b"lilypad-c6-reference-corpus");
    eprintln!("Lilypad C6 auditor corpus: {good} exact, {predicted} predicted failures");
    assert_eq!(good + predicted, xs.len());
}

#[test]
#[ignore]
fn lilypad_recorded_input_replay() {
    let sch = sched();
    let qb = env_usize("LILYPAD_QB", 20);
    let cap = env_usize("LILYPAD_CAP", 920) as u64;
    let dir = std::env::var("LILYPAD_REPLAY_DIR").expect("LILYPAD_REPLAY_DIR");
    let mut xs: Vec<N> = vec![];
    for ent in std::fs::read_dir(dir).unwrap() {
        let path = ent.unwrap().path();
        if path.extension().and_then(|s| s.to_str()) != Some("json") {
            continue;
        }
        let txt = std::fs::read_to_string(path).unwrap();
        for (i, _) in txt.match_indices("0x") {
            let h: String = txt[i + 2..].chars().take_while(|c| c.is_ascii_hexdigit()).collect();
            if h.len() == 64 {
                let x = N::from_str_radix(&h, 16).unwrap();
                if !xs.contains(&x) {
                    xs.push(x);
                }
            }
        }
    }
    assert!(!xs.is_empty());
    let (b, x, y) = build_roundtrip(&sch, qb, cap);
    let mut exact = 0;
    let mut predicted = 0;
    for (batch, ch) in xs.chunks(64).enumerate() {
        let ys: Vec<N> = (0..ch.len()).map(|i| N::from((1000 + batch * 64 + i) as u64)).collect();
        let tag = format!("lilypad-recorded-replay-{batch}");
        let (g, p) = verify_roundtrip_batch(&b, &x, &y, &sch, qb, ch, &ys, tag.as_bytes());
        exact += g;
        predicted += p;
    }
    eprintln!("Lilypad recorded replay: {} inputs, {exact} exact, {predicted} predicted", xs.len());
    assert_eq!(exact + predicted, xs.len());
}

#[test]
#[ignore]
fn lilypad_endpoint_adapter() {
    let mut b = B::new();
    let y = b.alloc_n(256);
    let x = b.alloc_n(256);
    let dv = pointadd_lilypad::div_forward(&mut b, &x, &y);
    let inv = dv.inv.clone();
    let key = dv.key;
    let cleared_y = dv.w.bb.clone();
    let sch = dv.sch.clone();
    let mut rng = Rng::new(0x1eaf_ada7u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-endpoint-adapter");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let p = p();
    let two_s = N::from(2u64).pow_mod(N::from(sch.s as u64), p);
    let mut exact = 0usize;
    for k in 0..64 {
        let mut m = Pm::new(xs[k]);
        for t in 1..=sch.s {
            m.tick(t, &sch, 13);
        }
        if m.bad.is_some() || m.g != N::ZERO {
            continue;
        }
        exact += 1;
        let c = get_s(&s.qubits, &inv, k);
        let cmod = if c.bit(TOP) {
            let a = (!c).wrapping_add(N::from(1u64)) % p;
            if a == N::ZERO { N::ZERO } else { p - a }
        } else {
            c % p
        };
        let got = cmod.mul_mod(xs[k], p);
        let neg = (s.qubits[key.0 as usize] >> k) & 1 != 0;
        let want = if neg { p - two_s } else { two_s };
        assert_eq!(got, want, "shot {k}: endpoint relation");
        for &q in &cleared_y {
            assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "shot {k}: endpoint Y q{}", q.0);
        }
    }
    eprintln!("Lilypad endpoint adapter: {exact}/64 exact within the registered envelope");
    assert!(exact >= 60);
}

#[test]
#[ignore]
fn lilypad_one_division() {
    let mut b = B::new();
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    pointadd_lilypad::one_division_probe(&mut b, &x, &y);
    let expected_t = super::tests_chunked::expected_t(&b.ops);
    eprintln!("Lilypad one division: peak {} expected T {expected_t:.0} ops {}", b.peak, b.ops.len());
    let sch = pointadd_lilypad::sched();
    let mut rng = Rng::new(0x1d1f_1510u64);
    let mut xs = vec![];
    while xs.len() < 64 {
        let v = rand_x(&mut rng);
        let mut m = Pm::new(v);
        for t in 1..=sch.s { m.tick(t, &sch, 13); }
        if m.bad.is_none() && m.g == N::ZERO { xs.push(v); }
    }
    let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-one-division");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let pm = p();
    for k in 0..64 {
        let got_x = get_s(&s.qubits, &x, k) & ((N::from(1u64) << 256) - N::from(1u64));
        let got_y = get_s(&s.qubits, &y, k) & ((N::from(1u64) << 256) - N::from(1u64));
        let want_y = ys[k].mul_mod(xs[k].pow_mod(pm - N::from(2u64), pm), pm);
        assert_eq!(got_x, xs[k], "shot {k}: dx");
        assert_eq!(got_y, want_y, "shot {k}: lambda");
    }
    let mut data = vec![false; s.qubits.len()];
    for q in x.iter().chain(y.iter()) { data[q.0 as usize] = true; }
    for (i, row) in s.qubits.iter().enumerate() {
        if !data[i] { assert_eq!(*row, 0, "ancilla q{i}"); }
    }
    assert_eq!(s.phase, 0, "one-division phase");
}

fn lilypad_curve() -> crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
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

#[test]
#[ignore]
fn lilypad_point_add_end_to_end() {
    let mut b = B::new();
    let (xq, yq) = pointadd_lilypad::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let analytic = super::tests_chunked::expected_t(&ops);
    eprintln!("Lilypad point add: ops {} qubits {nq} allocator peak {} analytic T {analytic:.0}", ops.len(), b.peak);
    assert!(nq <= 893 && b.peak <= 893);
    let curve = lilypad_curve();
    let to_u = |v: &N| -> ruint::aliases::U256 { ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    let mut rng = Rng::new(0x1a1d_2026u64);
    let mut cases = vec![];
    while cases.len() < 64 {
        let k1 = to_u(&(rng.below(250) + N::from(1u64)));
        let k2 = to_u(&(rng.below(250) + N::from(1u64)));
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        if t.0 == o.0 { continue; }
        let e = curve.add(t.0, t.1, o.0, o.1);
        cases.push((t, o, e));
    }
    let mut h = sha3::Shake256::default();
    h.update(b"lilypad-point-add-e2e");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq as usize, nb as usize, &mut xof);
    for (k, (t, o, _)) in cases.iter().enumerate() {
        s.set_register(&regs[0], t.0, k);
        s.set_register(&regs[1], t.1, k);
        s.set_register(&regs[2], o.0, k);
        s.set_register(&regs[3], o.1, k);
    }
    s.apply_iter(ops.iter());
    for (k, (_, _, e)) in cases.iter().enumerate() {
        assert_eq!(s.get_register(&regs[0], k), e.0, "shot {k}: x3");
        assert_eq!(s.get_register(&regs[1], k), e.1, "shot {k}: y3");
    }
    assert_eq!(s.phase, 0, "point-add phase");
    let data: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    for q in 0..nq {
        if !data.contains(&q) { assert_eq!(s.qubits[q as usize], 0, "ancilla q{q}"); }
    }
    eprintln!("Lilypad point add exact 64/64; avg executed T {}", s.stats.toffoli_gates / 64);
}

/// Replay one explicit affine point-addition witness at one or more peak caps.
/// This is a diagnostic bridge between a salted full-circuit failure and the
/// per-division Lilypad replay, and deliberately has no production selector.
#[test]
#[ignore]
fn lilypad_point_add_witness() {
    type U = ruint::aliases::U256;
    let vals: Vec<U> = std::env::var("LILYPAD_PA_CASE")
        .expect("LILYPAD_PA_CASE=tx,ty,ox,oy")
        .split(',')
        .map(|v| U::from_str_radix(v.trim().trim_start_matches("0x"), 16).unwrap())
        .collect();
    assert_eq!(vals.len(), 4);
    let caps: Vec<u64> = std::env::var("LILYPAD_PA_CAPS")
        .unwrap_or_else(|_| pointadd_lilypad::PEAK0.to_string())
        .split(',')
        .map(|v| v.parse().unwrap())
        .collect();
    let curve = lilypad_curve();
    let expected = curve.add(vals[0], vals[1], vals[2], vals[3]);
    if let Ok(value) = std::env::var("LILYPAD_PA_L1") {
        let enabled = value != "0";
        pointadd_lilypad::test_layer_overrides(Some(enabled), Some(enabled));
    }
    if let Ok(value) = std::env::var("LILYPAD_PA_L2") {
        super::lilypad_g::test_l2_override(Some(value != "0"));
    }
    if let Ok(value) = std::env::var("LILYPAD_PA_L5") {
        super::lilypad_g::test_l5_override(Some(value != "0"));
    }

    for cap in caps {
        pointadd_lilypad::test_peak(Some(cap));
        let mut b = B::new();
        let (xq, yq) = pointadd_lilypad::point_add(&mut b);
        let ops = std::mem::take(&mut b.ops);
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let mut xr = xof(format!("lilypad-pa-witness-{cap}").as_bytes());
        let mut s = Simulator::new(nq as usize, nb as usize, &mut xr);
        s.set_register(&regs[0], vals[0], 0);
        s.set_register(&regs[1], vals[1], 0);
        s.set_register(&regs[2], vals[2], 0);
        s.set_register(&regs[3], vals[3], 0);
        s.apply_iter(ops.iter());
        let got = (s.get_register(&regs[0], 0), s.get_register(&regs[1], 0));
        let data: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
        let dirty: Vec<_> = (0..nq)
            .filter(|q| !data.contains(q) && (s.qubits[*q as usize] & 1) != 0)
            .collect();
        eprintln!(
            "LILYPAD_PA_WITNESS cap={cap} peak={} value_ok={} phase={} dirty={} got=({:#x},{:#x}) expected=({:#x},{:#x})",
            b.peak,
            got == expected,
            s.phase & 1,
            dirty.len(),
            got.0,
            got.1,
            expected.0,
            expected.1
        );
    }
    pointadd_lilypad::test_peak(None);
    pointadd_lilypad::test_layer_overrides(None, None);
    super::lilypad_g::test_l2_override(None);
    super::lilypad_g::test_l5_override(None);
}

/// Stable raw-stream fingerprint used by the layered optimization gates. The
/// top-level nonce tail is outside this builder, so equal digests prove that a
/// disabled layer leaves the complete point-add body byte-for-byte unchanged.
#[test]
#[ignore]
fn lilypad_raw_stream_digest() {
    let mut b = B::new();
    let _ = pointadd_lilypad::point_add(&mut b);
    let mut h = <sha3::Sha3_256 as sha3::Digest>::new();
    for op in &b.ops {
        sha3::Digest::update(&mut h, [op.kind as u8]);
        for v in [
            op.q_control2.0,
            op.q_control1.0,
            op.q_target.0,
            op.c_target.0,
            op.c_condition.0,
            op.r_target.0,
        ] {
            sha3::Digest::update(&mut h, v.to_le_bytes());
        }
    }
    let digest = sha3::Digest::finalize(h);
    eprintln!("LILYPAD_RAW_SHA3_256={digest:x} ops={} peak={} expected_t={:.1}",
        b.ops.len(), b.peak, b.tof as f64 - b.tof_cond as f64 / 2.0);
}

#[test]
#[ignore]
fn lilypad_layered_peak_sweep() {
    let caps: Vec<u64> = std::env::var("LILYPAD_LAYER_CAPS")
        .unwrap_or_else(|_| "893,889,885,881,877,873".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    for cap in caps {
        pointadd_lilypad::test_peak(Some(cap));
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut b = B::new();
            let _ = pointadd_lilypad::point_add(&mut b);
            let expected = super::tests_chunked::expected_t(&b.ops);
            eprintln!(
                "LOWQ_SWEEP requested={cap} actual_peak={} qubits={} expected_t={expected:.1} ops={}",
                b.peak,
                analyze_ops(b.ops.iter()).0,
                b.ops.len()
            );
        }));
        if result.is_err() {
            eprintln!("LOWQ_SWEEP requested={cap} BUILD_FAILED");
        }
        pointadd_lilypad::test_peak(None);
    }
}

#[test]
#[ignore]
fn lilypad_q890_window_sweep() {
    pointadd_lilypad::test_peak(Some(890));
    for wm in [66usize, 65, 64, 63, 62, 61, 60] {
        super::modp_ft::test_signed_wm_max(Some(wm));
        let mut b = B::new();
        let _ = pointadd_lilypad::point_add(&mut b);
        let expected = super::tests_chunked::expected_t(&b.ops);
        eprintln!("LOWQ_WM cap=890 wm_max={wm} peak={} expected_t={expected:.1} ops={}", b.peak, b.ops.len());
    }
    super::modp_ft::test_signed_wm_max(None);
    pointadd_lilypad::test_peak(None);
}

#[test]
#[ignore]
fn lilypad_layers_phase_witness() {
    type U = ruint::aliases::U256;
    let hx = |s: &str| U::from_str_radix(s, 16).unwrap();
    let t = (
        hx("2e29985a142ec0b528ce20c32d01e6740add40cd7b7f024cb3be5c1ffe2f45f5"),
        hx("a9e58767c1db0814c92a8f8a18c5110d072cffdb7175b06fab62eae39ca84800"),
    );
    let o = (
        hx("81338ceb22e3d0b6637e9ef36feada8b8623f51411f35c29f1ba744470c93678"),
        hx("7a93e397f1658fd916f15460d3cc8e729a79e62ee3574108d881bf4482c6019b"),
    );
    let expected = lilypad_curve().add(t.0, t.1, o.0, o.1);
    for &(name, l1, l2, l3) in &[
        ("base", false, false, false),
        ("l1", true, false, false),
        ("l1+l2", true, true, false),
        ("l1+l2+l3", true, true, true),
    ] {
        pointadd_lilypad::test_layer_overrides(Some(l1), Some(l3));
        super::lilypad_g::test_l2_override(Some(l2));
        let mut b = B::new();
        let (xq, yq) = pointadd_lilypad::point_add(&mut b);
        let (nq, nb, _, regs) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(format!("layers-phase-witness-{name}").as_bytes());
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new(nq as usize, nb as usize, &mut xof);
        for shot in 0..64 {
            s.set_register(&regs[0], t.0, shot);
            s.set_register(&regs[1], t.1, shot);
            s.set_register(&regs[2], o.0, shot);
            s.set_register(&regs[3], o.1, shot);
        }
        s.apply_iter(b.ops.iter());
        let mut bad = 0u32;
        for shot in 0..64 {
            bad += u32::from(s.get_register(&regs[0], shot) != expected.0 || s.get_register(&regs[1], shot) != expected.1);
        }
        let data: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
        let dirty = (0..nq).filter(|q| !data.contains(q) && s.qubits[*q as usize] != 0).count();
        eprintln!("LAYER_WITNESS {name}: bad={bad} phase={} dirty={dirty}", s.phase.count_ones());
    }
    pointadd_lilypad::test_layer_overrides(None, None);
    super::lilypad_g::test_l2_override(None);
}

#[test]
#[ignore]
fn lilypad_failure_localization() {
    let path = std::env::var("LILYPAD_CASES").expect("LILYPAD_CASES");
    let vals: Vec<[ruint::aliases::U256; 4]> = std::fs::read_to_string(path).unwrap().lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Vec<_> = l.split_whitespace().map(|h| ruint::aliases::U256::from_str_radix(h, 16).unwrap()).collect();
            [v[0], v[1], v[2], v[3]]
        }).collect();
    pointadd_lilypad::CKS.with(|c| c.borrow_mut().clear());
    let mut b = B::new();
    let _ = pointadd_lilypad::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let cks = pointadd_lilypad::CKS.with(|c| c.borrow().clone());
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let curve = lilypad_curve();
    let p = curve.modulus;
    let sub = |a, z| if a >= z { a - z } else { p - (z - a) };
    let mut expected = vec![];
    for v in &vals {
        let dx = sub(v[0], v[2]);
        let dy = sub(v[1], v[3]);
        let lam = dy.mul_mod(dx.pow_mod(p - ruint::aliases::U256::from(2u64), p), p);
        let mut dx2 = lam.mul_mod(lam, p);
        dx2 = sub(dx2, dx);
        for _ in 0..3 { dx2 = sub(dx2, v[2]); }
        let ndy0 = lam.mul_mod(dx2, p);
        let ndy = if ndy0.is_zero() { ndy0 } else { p - ndy0 };
        let x3 = (dx2 + v[2]) % p;
        let y3 = sub(ndy, v[3]);
        expected.push((dx, dy, lam, dx2, ndy, x3, y3));
    }
    let mut h = sha3::Shake256::default(); h.update(b"lilypad-localize"); let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq as usize, nb as usize, &mut xof);
    for (k, v) in vals.iter().enumerate() {
        s.set_register(&regs[0], v[0], k); s.set_register(&regs[1], v[1], k);
        s.set_register(&regs[2], v[2], k); s.set_register(&regs[3], v[3], k);
    }
    let mut lo = 0usize;
    for (name, hi) in cks {
        s.apply_iter(ops[lo..hi].iter()); lo = hi;
        let want = match name.as_str() {
            "-- division 1" => Some((0usize, 1usize)),
            "walk inverse 1 end" | "-- x: dx' = lambda^2 - " => Some((0, 2)),
            "-- ndy = -lambda * dx'," => Some((3, 2)),
            "-- division 2: recomput" | "-- x3 = dx' + ox, y3 = " => Some((3, 4)),
            "end" => Some((5, 6)),
            _ => None,
        };
        if let Some((ix, iy)) = want {
            let mut bad = 0;
            for (k, e) in expected.iter().enumerate() {
                let a = [e.0, e.1, e.2, e.3, e.4, e.5, e.6];
                if s.get_register(&regs[0], k) != a[ix] || s.get_register(&regs[1], k) != a[iy] { bad += 1; }
            }
            eprintln!("LOC {name}: bad {bad}/{} phase {:#x}", vals.len(), s.phase);
        }
    }
    s.apply_iter(ops[lo..].iter());
}

#[test]
#[ignore]
fn lilypad_residual_walks_exact() {
    let path = std::env::var("LILYPAD_CASES").expect("LILYPAD_CASES");
    let curve = lilypad_curve();
    let p = curve.modulus;
    let sub = |a, z| if a >= z { a - z } else { p - (z - a) };
    let to_n = |u: ruint::aliases::U256| N::from_limbs([u.as_limbs()[0], u.as_limbs()[1], u.as_limbs()[2], u.as_limbs()[3], 0, 0]);
    let mut xs = vec![];
    for line in std::fs::read_to_string(path).unwrap().lines().filter(|l| !l.trim().is_empty()) {
        let v: Vec<_> = line.split_whitespace().map(|h| ruint::aliases::U256::from_str_radix(h, 16).unwrap()).collect();
        let dx = sub(v[0], v[2]);
        let dy = sub(v[1], v[3]);
        let lam = dy.mul_mod(dx.pow_mod(p - ruint::aliases::U256::from(2u64), p), p);
        let mut dx2 = sub(lam.mul_mod(lam, p), dx);
        for _ in 0..3 { dx2 = sub(dx2, v[2]); }
        xs.push(to_n(dx)); xs.push(to_n(dx2));
    }
    let sch = sched();
    let mut predicted_flags = vec![];
    for &v in &xs {
        let mut m = Pm::new(v);
        for t in 1..=sch.s { m.tick(t, &sch, 13); }
        if m.bad.is_none() && m.g != N::ZERO { m.bad = Some("overrun".into()); }
        predicted_flags.push(m.bad.clone());
    }
    for (i, pair) in predicted_flags.chunks(2).enumerate() {
        eprintln!("residual {i}: div1={:?} div2={:?}", pair[0], pair[1]);
        assert_eq!(usize::from(pair[0].is_some()) + usize::from(pair[1].is_some()), 1, "case {i}: expected one failing division");
    }
    let (b, x, y) = build_roundtrip(&sch, 13, 893);
    let ys: Vec<N> = (0..xs.len()).map(|i| N::from((i + 7) as u64)).collect();
    let (good, predicted) = verify_roundtrip_batch(&b, &x, &y, &sch, 13, &xs, &ys, b"lilypad-residual-walks");
    eprintln!("Lilypad residual operands: {good} exact walks, {predicted} predicted");
    assert_eq!(good + predicted, xs.len());
    assert_eq!(predicted, 12);
}

/// Closed native square at caps (LILYPAD_SQCAPS): expected executed Toffoli (conditional CCX weighted 1/2 per depth).
#[test]
#[ignore]
fn lilypad_square_caps() {
    use crate::circuit::OperationType as K;
    let caps: Vec<usize> = std::env::var("LILYPAD_SQCAPS").unwrap_or("935".into()).split(',').map(|s| s.parse().unwrap()).collect();
    for cap in caps {
        let r = std::panic::catch_unwind(|| super::super::public_square_port::native_square_ops_at_cap(cap));
        match r {
            Err(_) => eprintln!("SQUARE cap {cap}: unbuildable"),
            Ok(ops) => {
                let (nq, _, _, _) = analyze_ops(ops.iter());
                let (mut w, mut st, mut tot, mut nat) = (1.0f64, vec![], 0.0, 0u64);
                for op in &ops {
                    match op.kind {
                        K::PushCondition => { st.push(w); w *= 0.5; }
                        K::PopCondition => w = st.pop().unwrap(),
                        K::CCX | K::CCZ => { tot += w; nat += 1; }
                        _ => {}
                    }
                }
                eprintln!("SQUARE cap {cap}: qubits {nq} native {nat} expected {tot:.0}");
            }
        }
    }
}

/// square_acc (z += y^2 mod p) as the replacement square below cap 935: expected T at pools (LILYPAD_SQPOOLS),
/// value-checked on 64 shots.
#[test]
#[ignore]
fn lilypad_square_acc_pools() {
    use super::modp_ft::{square_acc, Ms};
    let pools: Vec<usize> = std::env::var("LILYPAD_SQPOOLS").unwrap_or("256".into()).split(',').map(|s| s.parse().unwrap()).collect();
    let pm = p();
    for pool in pools {
        let mut b = B::new();
        let (z, y) = (b.alloc_n(256), b.alloc_n(256));
        let ms = Ms { k: b.alloc(), r: b.alloc_n(pool), one: b.alloc() };
        b.x(ms.one);
        let tmp = b.alloc();
        let n0 = b.ops.len();
        let mut zz = z.clone();
        square_acc(&mut b, &ms, &mut zz, &y, tmp);
        let e = super::tests_chunked::expected_t(&b.ops[n0..]);
        let mut rng = Rng::new(pool as u64);
        let zs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let mut xr = xof(b"lilypad-sq");
        let mut s = sim(&b, &mut xr);
        for k in 0..64 {
            put(&mut s.qubits, &z, k, zs[k]);
            put(&mut s.qubits, &y, k, ys[k]);
        }
        s.apply_iter(b.ops.iter());
        let mut bad = 0;
        for k in 0..64 {
            let want = (zs[k] + ys[k].mul_mod(ys[k], pm)) % pm;
            if get_u256(&s.qubits, &zz, k) != want {
                bad += 1;
            }
        }
        eprintln!("SQACC pool {pool}: live+pool {} expected {e:.0} bad {bad} phase {:#x}", 512 + pool + 3, s.phase);
    }
}
fn get_u256(w: &[u64], qs: &[QubitId], k: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> k) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}

/// The narrow MBU shell (pointadd_strip's sequence) at cap STRIP_PEAK with Lilypad-GCD's interface and walk stubs: after a
/// forward walk the live set is y + C (LILYPAD_CLEN lanes) + key + h (6) + log (LILYPAD_LOG); tails use S = LILYPAD_S halvings;
/// the square is ctrl_neg + square_acc (the closed square does not fit below 935). Expected T per phase.
#[test]
#[ignore]
fn lilypad_shell_stub() {
    use super::modp_frogdrop::load_bits;
    use super::modp_ft::{ctrl_neg, mod_double_n, modadd, modsub, product_inv, product_tail_neg_stream, square_acc, Ms};
    use super::pointadd_strip::{peak, rec_product, rec_product_tail_s, reduce_ct, uncompute_product_tail_s};
    let clen = env_usize("LILYPAD_CLEN", 288);
    let nlog = env_usize("LILYPAD_LOG", 8);
    let s_h = env_usize("LILYPAD_S", 532);
    let lhat = s_h - 256;
    let mut b = B::new();
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    let ox: Vec<crate::circuit::BitId> = b.declare_bits(2, 256);
    let oy: Vec<crate::circuit::BitId> = b.declare_bits(3, 256);
    let mut marks: Vec<(String, usize, u64)> = vec![("start".into(), 0, 0)];
    let mark = |b: &B, m: &mut Vec<(String, usize, u64)>, s: &str| m.push((s.to_string(), b.ops.len(), b.peak));
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        load_bits(&mut b, &t, &ox);
        modsub(&mut b, &ms, &x, &t, y[0]);
        load_bits(&mut b, &t, &ox);
        load_bits(&mut b, &t, &oy);
        modsub(&mut b, &ms, &y, &t, x[0]);
        load_bits(&mut b, &t, &oy);
        b.free_n(&t);
        ms.release(&mut b);
    }
    mark(&b, &mut marks, "setup");
    // walk stub: x -> (C, key, h, log)
    let fwd_stub = |b: &mut B| -> (Vec<QubitId>, QubitId, Vec<QubitId>) {
        b.free_n(&x);
        let c = b.alloc_n(clen);
        let key = b.alloc();
        let ex = b.alloc_n(6 + nlog);
        (c, key, ex)
    };
    let inv_stub = |b: &mut B, c: Vec<QubitId>, key: QubitId, ex: Vec<QubitId>| {
        b.free_n(&c);
        b.free(key);
        b.free_n(&ex);
        for &q in &x {
            b.acquire(q);
        }
    };
    let (c, key, ex) = fwd_stub(&mut b);
    let live_end = b.live;
    let m1 = b.fresh_bits(256);
    reduce_ct(&mut b, &c, false);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        let mut zz = z.clone();
        product_tail_neg_stream(&mut b, &ms, &mut zz, &y, &c[..256], s_h, &m1);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        ctrl_neg(&mut b, &ms, &z, Some(key));
        ms.release(&mut b);
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    reduce_ct(&mut b, &c, true);
    mark(&b, &mut marks, "lambda tail (+reduce, undo)");
    inv_stub(&mut b, c, key, ex);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        let r = rec_product(&mut b, &ms, &z, &y, &x, false);
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        let mut zz = z.clone();
        product_inv(&mut b, &ms, &mut zz, &y, &x);
        b.free_n(&z);
        ms.release(&mut b);
    }
    mark(&b, &mut marks, "dy fix");
    {
        let ms = Ms::alloc_room(&mut b, peak());
        ctrl_neg(&mut b, &ms, &x, None);
        let tmp = b.alloc();
        let mut xx = x.clone();
        square_acc(&mut b, &ms, &mut xx, &y, tmp);
        assert_eq!(xx, x);
        b.free(tmp);
        ms.release(&mut b);
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        load_bits(&mut b, &t, &ox);
        for _ in 0..3 {
            modsub(&mut b, &ms, &x, &t, y[0]);
        }
        load_bits(&mut b, &t, &ox);
        b.free_n(&t);
        ms.release(&mut b);
    }
    mark(&b, &mut marks, "x' (neg + square_acc + 3 modsub)");
    let m2 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        let mut yy = y.clone();
        mod_double_n(&mut b, &ms, &mut yy, lhat);
        let mut zz = z.clone();
        product_tail_neg_stream(&mut b, &ms, &mut zz, &yy, &x, lhat, &m2);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        ms.release(&mut b);
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    mark(&b, &mut marks, "ndy tail");
    let (c, key, ex) = fwd_stub(&mut b);
    reduce_ct(&mut b, &c, false);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        let tt = s_h - lhat;
        let r = rec_product_tail_s(&mut b, &ms, &z, &c[..256], &y, tt, Some((key, true)));
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        uncompute_product_tail_s(&mut b, &ms, &z, &c[..256], &y, tt, Some((key, true)), 48);
        b.free_n(&z);
        ms.release(&mut b);
    }
    reduce_ct(&mut b, &c, true);
    mark(&b, &mut marks, "lambda fix (+reduce, undo)");
    inv_stub(&mut b, c, key, ex);
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(&mut b, peak());
        load_bits(&mut b, &t, &ox);
        modadd(&mut b, &ms, &x, &t, y[0]);
        load_bits(&mut b, &t, &ox);
        load_bits(&mut b, &t, &oy);
        modsub(&mut b, &ms, &y, &t, x[0]);
        load_bits(&mut b, &t, &oy);
        b.free_n(&t);
        ms.release(&mut b);
    }
    mark(&b, &mut marks, "final");
    let mut tot = 0.0;
    for w in marks.windows(2) {
        let e = super::tests_chunked::expected_t(&b.ops[w[0].1..w[1].1]);
        tot += e;
        eprintln!("SHELL cap {} clen {clen} log {nlog}: {:36} {e:>9.0}  (peak so far {})", peak(), w[1].0, w[1].2);
    }
    eprintln!("SHELL cap {} clen {clen} log {nlog} S {s_h}: live at the C end {live_end}; total {tot:.0}; peak {}", peak(), b.peak);
}

// ------------------------------------------------------------------------------------------------ Lilypad-G
use super::lilypad_g::*;

#[derive(Clone, Debug)]
struct Gm {
    f: N,
    g: N,
    cf: N,
    cg: N,
    rho: bool,
    pm: Pm,
    bad: bool,
}

impl Gm {
    fn new(x: N) -> Self {
        let pp = p();
        Self {
            f: pp,
            g: (x << 1usize).wrapping_sub(pp),
            cf: N::ZERO,
            cg: N::from(2u64),
            rho: false,
            pm: Pm::new(x),
            bad: false,
        }
    }

    fn tick(&mut self, t: usize, sch: &PSched, qb: usize) {
        if self.bad || self.pm.bad.is_some() {
            self.bad = true;
            self.pm.tick(t, sch, qb);
            return;
        }
        let (kv, kc) = (sch.kv[t], sch.kc[t]);
        let d = self.g.bit(1) == self.f.bit(1);
        let e = d ^ self.rho;
        assert_eq!(e, self.pm.g.bit(0), "tick {t}: forced digit differs from Lilypad e");
        let sw = e && self.pm.d2 > 0;
        let pre = [self.f, self.g, self.cf, self.cg];
        let mid = if d { self.g.wrapping_add(self.f) } else { self.g.wrapping_sub(self.f) };
        let midc = if d { self.cg.wrapping_add(self.cf) } else { self.cg.wrapping_sub(self.cf) };
        self.g = sar1(mid);
        self.cg = midc;
        self.cf <<= 1usize;
        if sw {
            std::mem::swap(&mut self.f, &mut self.g);
            std::mem::swap(&mut self.cf, &mut self.cg);
            self.rho = !self.rho;
        }
        let vw = [tcb(pre[0]), tcb(pre[1]), tcb(mid)].into_iter().max().unwrap();
        let stored_c = |v: N| if HALF_COFACTOR_G { sar1(v) } else { v };
        let cw = [tcb(stored_c(pre[2])), tcb(stored_c(pre[3])), tcb(stored_c(midc))]
            .into_iter()
            .max()
            .unwrap();
        if vw > kv || cw > kc {
            self.bad = true;
        }
        if t == sch.s
            && (tcb(self.f).max(tcb(self.g)) > sch.kv[t + 1]
                || tcb(stored_c(self.cf)).max(tcb(stored_c(self.cg))) > sch.kc[t + 1])
        {
            self.bad = true;
        }
        self.pm.tick(t, sch, qb);
        if self.pm.bad.as_ref().is_some_and(|s| s.starts_with("width") || s.starts_with("end width")) {
            self.pm.bad = None;
        }
        if self.pm.bad.is_some() {
            self.bad = true;
        }
    }
}

fn check_tick_g(
    w: &PWalk,
    sch: &PSched,
    t: usize,
    st: &[u64],
    ms: &[Gm],
    qb: usize,
    with_q: bool,
) -> usize {
    let mut nbad = 0;
    for (k, m) in ms.iter().enumerate() {
        if m.bad {
            nbad += 1;
            continue;
        }
        let got = decode(w, sch, t + 1, st, k);
        let stored_c = |v: N| if HALF_COFACTOR_G { sar1(v) } else { v };
        let want = (m.f, m.g, stored_c(m.cf), stored_c(m.cg), (((m.pm.d2 - 1) / 2) as u64) & 127);
        assert_eq!(got, want, "Lilypad-G tick {t} shot {k}");
        let mut got_rho = (t & 1 == 1) ^ ((st[w.h[0].0 as usize] >> k) & 1 == 1);
        if w.log.len() >= 8 {
            got_rho ^= ((st[w.log[0].0 as usize] ^ st[w.log[4].0 as usize]) >> k) & 1 == 1;
        }
        assert_eq!(got_rho, m.rho, "Lilypad-G tick {t} shot {k}: derived rho");
        if with_q {
            assert_eq!(get_u(st, &w.qfr(t), k), m.pm.qval(t, qb), "Lilypad-G tick {t} shot {k}: Q");
        }
    }
    nbad
}

#[test]
#[ignore]
fn lilypad_g_fwd_check() {
    use super::frogstrip::SEC;
    let sch = sched_g();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 27);
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let mut s0 = setup(&sch, 0, false, false);
    let sc = PScr::alloc_fwd(&mut s0.b, room);
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    let division = b.new_division();
    let mut bounds = vec![b.ops.len()];
    let m = b.fresh_bits(ticks + 1);
    for t in 1..=ticks {
        let rho = rho_stable(&w, t - 1);
        step_core_g(&mut b, &w, t, &sch, &sc, &rho, sc.e, &[], Some((division, false)));
        halve_g(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        bounds.push(b.ops.len());
    }
    let exp = super::tests_chunked::expected_t(&b.ops[bounds[0]..]);
    eprintln!("Lilypad-G forward: {ticks} ticks, expected {exp:.0} ({:.1}/tick), peak {}", exp / ticks as f64, b.peak);
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (name, (sum, n)) in &mm {
            eprintln!("SEC {name:14} total {sum:>10.0} n {n:>5} avg {:>8.1}", sum / *n as f64);
        }
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 1) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-forward");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let scratch: Vec<QubitId> = [sc.e, sc.sg]
        .iter()
        .copied()
        .chain(sc.tmp.iter().copied())
        .chain(sc.pool.iter().copied())
        .collect();
    let mut nbad = 0;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for mm in &mut ms {
            mm.tick(t, &sch, 64);
        }
        nbad = check_tick_g(&w, &sch, t, &s.qubits, &ms, 64, false);
        let good: u64 = ms.iter().enumerate().filter(|(_, m)| !m.bad).map(|(k, _)| 1u64 << k).sum();
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & good, 0, "tick {t}: scratch q{} dirty", q.0);
        }
    }
    eprintln!("Lilypad-G forward exact on {} / 64 shots", 64 - nbad);
}

#[test]
#[ignore]
fn lilypad_g_regen_check() {
    use super::frogstrip::SEC;
    let sch = sched_g();
    let qb = env_usize("LILYPAD_QB", 13);
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 8);
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let mut s0 = setup_with_capq(&sch, qb, false, true, 11);
    let sc = PScr::alloc_inv_g(&mut s0.b, room);
    let g = GScr;
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    let mut bounds = vec![b.ops.len()];
    let mut inv_cost = 0.0;
    for t in 1..=ticks {
        let (p1, p3) = rec_regen_g(&mut b, &w, t, &sch, &sc, &g, None);
        inv_cost += b.measure(&p1, true) + b.measure(&p3, true);
        b.play(&p1, false);
        b.play(&p3, false);
        bounds.push(b.ops.len());
    }
    eprintln!("Lilypad-G regen: inverse cost {inv_cost:.0} ({:.1}/tick), peak {}", inv_cost / ticks as f64, b.peak);
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (name, (sum, n)) in &mm {
            eprintln!("SEC {name:14} total {sum:>10.0} n {n:>5} avg {:>8.1}", sum / *n as f64);
        }
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 2) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-regen");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let mut scratch: Vec<QubitId> = [sc.e, sc.sg]
        .iter()
        .copied()
        .chain(sc.tmp.iter().copied())
        .chain(sc.pool.iter().copied())
        .collect();
    scratch.extend(&sc.d);
    scratch.extend(&sc.sp);
    let mut nbad = 0;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for mm in &mut ms {
            mm.tick(t, &sch, qb);
        }
        nbad = check_tick_g(&w, &sch, t, &s.qubits, &ms, qb, true);
        let good: u64 = ms.iter().enumerate().filter(|(_, m)| !m.bad).map(|(k, _)| 1u64 << k).sum();
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & good, 0, "tick {t}: scratch q{} dirty", q.0);
        }
        assert_eq!(s.phase & good, 0, "tick {t}: phase");
    }
    eprintln!("Lilypad-G regeneration exact on {} / 64 shots", 64 - nbad);
}

#[test]
#[ignore]
fn lilypad_g_count() {
    use super::frogstrip::SEC;
    let sch = sched_g();
    let qb = env_usize("LILYPAD_QB", 13);
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let Setup { mut b, y, x, mut w } = setup(&sch, qb, true, false);
    let g = GScr;
    let live_f = b.live + 2 + NT as u64;
    let room_f = cap.saturating_sub(live_f) as usize;
    let sc = PScr::alloc_fwd(&mut b, room_f);
    let div = b.new_division();
    let n0 = b.ops.len();
    let m = walk_forward_g(&mut b, &w, &sch, &sc, &g, Some(div));
    let n1 = b.ops.len();
    let adapter = endpoint_adapter_g(&mut b, &w, &sch, &sc);
    b.play(&adapter, false);
    let na = b.ops.len();
    b.play(&adapter, true);
    b.cx(w.h[HB - 2], w.h[HB - 1]);
    b.free(w.h[HB - 1]);
    sc.release(&mut b);
    b.acquire(w.h[HB - 1]);
    b.cx(w.h[HB - 2], w.h[HB - 1]);
    w.q = b.alloc_n(qb);
    let live_i = b.live + 2 + inverse_d_len_g() as u64 + inverse_tmp_len_g() as u64 + SB as u64;
    let room_i = cap.saturating_sub(live_i) as usize;
    let sc = PScr::alloc_inv_g(&mut b, room_i);
    let ni0 = b.ops.len();
    walk_inverse_g(&mut b, &w, &sch, &sc, &g, &m, Some(div));
    let n2 = b.ops.len();
    b.close_division(div);
    let ef = super::tests_chunked::expected_t(&b.ops[n0..n1]);
    let ei = super::tests_chunked::expected_t(&b.ops[ni0..n2]);
    eprintln!(
        "LILYPAD_G_COUNT W {} qb {qb} cap {cap}: fwd pool {room_f} inv pool {room_i} fwd {ef:.0} inv {ei:.0} peak {}",
        sch.w, b.peak
    );
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (name, (sum, n)) in &mm {
            eprintln!("SEC {name:18} total {sum:>10.0} n {n:>5} avg {:>8.1}", sum / *n as f64);
        }
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 3) as u64);
    let xs: Vec<N> = if let Ok(path) = std::env::var("LILYPAD_G_XFILE") {
        let batch = env_usize("LILYPAD_G_BATCH", 0);
        std::fs::read_to_string(path)
            .unwrap()
            .lines()
            .filter(|line| !line.trim().is_empty())
            .skip(batch * 64)
            .take(64)
            .map(|line| N::from_str_radix(line.trim().trim_start_matches("0x"), 16).unwrap())
            .collect()
    } else {
        (0..64).map(|_| rand_x(&mut rng)).collect()
    };
    assert!(!xs.is_empty() && xs.len() <= 64);
    let ys: Vec<N> = (0..xs.len()).map(|_| rand_x(&mut rng)).collect();
    let xtag = std::env::var("LILYPAD_XOF_TAG").unwrap_or_else(|_| "lilypad-g-count".into());
    let mut xr = xof(xtag.as_bytes());
    let mut s = sim(&b, &mut xr);
    let mut xrf = xof(format!("{xtag}-forward").as_bytes());
    let mut sf = sim(&b, &mut xrf);
    let mut xra = xof(format!("{xtag}-adapter").as_bytes());
    let mut sa = sim(&b, &mut xra);
    for k in 0..xs.len() {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
        put(&mut sf.qubits, &x, k, xs[k]);
        put(&mut sf.qubits, &y, k, ys[k]);
        put(&mut sa.qubits, &x, k, xs[k]);
        put(&mut sa.qubits, &y, k, ys[k]);
    }
    sf.apply_iter(b.ops[..n1].iter());
    sa.apply_iter(b.ops[..na].iter());
    s.apply_iter(b.ops.iter());
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    for t in 1..=sch.s {
        for mm in &mut ms {
            mm.tick(t, &sch, qb);
        }
    }
    let mut other: Vec<QubitId> = w.a[256..].to_vec();
    other.extend(&w.bb);
    other.extend(&w.q);
    other.extend(&w.h);
    other.extend(&w.log);
    let value_len = sch.c[sch.s + 1];
    let cofactor_len = sch.w - value_len;
    let fq: Vec<QubitId> = (0..value_len).map(|j| w.bf(j)).collect();
    let cfq: Vec<QubitId> = (0..cofactor_len).map(|j| w.asig(sch.s + 1, j)).collect();
    let key = w.bf(1);
    let pm = p();
    let endpoint_exp = sch.s - usize::from(HALF_COFACTOR_G);
    let two_s = N::from(2u64).pow_mod(N::from(endpoint_exp as u64), pm);
    let smod = |v: N| {
        if v.bit(TOP) {
            let a = (!v).wrapping_add(N::from(1u64)) % pm;
            if a == N::ZERO { N::ZERO } else { pm - a }
        } else {
            v % pm
        }
    };
    let mut clean = 0;
    let mut predicted = 0;
    let mut repaired = 0;
    for k in 0..xs.len() {
        let f = get_s(&sf.qubits, &fq, k);
        let cf = get_s(&sf.qubits, &cfq, k);
        let output_ok = smod(f).mul_mod(smod(cf), pm).mul_mod(xs[k], pm) == two_s;
        let key_neg = (sa.qubits[key.0 as usize] >> k) & 1 != 0;
        let acf = smod(get_s(&sa.qubits, &cfq, k));
        let adapter_output = acf.mul_mod(xs[k], pm);
        let adapter_relation_ok = adapter_output == if key_neg { pm - two_s } else { two_s };
        let mut adapter_keep = vec![false; sa.qubits.len()];
        for &q in y.iter().chain(cfq.iter()).chain(w.h.iter()).chain(w.log.iter()) {
            adapter_keep[q.0 as usize] = true;
        }
        adapter_keep[key.0 as usize] = true;
        let adapter_residue_ok = sa
            .qubits
            .iter()
            .enumerate()
            .all(|(i, row)| adapter_keep[i] || ((row >> k) & 1 == 0));
        let adapter_ok = adapter_relation_ok && adapter_residue_ok;
        let xok = get_s(&s.qubits, &x, k) & ((N::from(1u64) << 256) - N::from(1u64)) == xs[k];
        let yok = get_s(&s.qubits, &y, k) & ((N::from(1u64) << 256) - N::from(1u64)) == ys[k];
        let anc_ok = other.iter().all(|q| (s.qubits[q.0 as usize] >> k) & 1 == 0);
        let phase_ok = (s.phase >> k) & 1 == 0;
        let roundtrip_ok = xok && yok && anc_ok && phase_ok;
        let hsign_park_ok = ((sf.qubits[w.h[HB - 2].0 as usize] ^ sf.qubits[w.h[HB - 1].0 as usize]) >> k) & 1 == 0;
        let model_fail = ms[k].bad || ms[k].pm.g != N::ZERO;
        if model_fail {
            if output_ok && adapter_ok && roundtrip_ok
                && ms[k].pm.bad.as_ref().is_some_and(|reason| reason.starts_with("cap log overflow"))
            {
                // L4's repaired encoding intentionally rescues the benign
                // third-push subset that the pre-L4 predictor marks log3.
                repaired += 1;
            } else {
                predicted += 1;
                assert!(!output_ok || !adapter_ok || !roundtrip_ok, "shot {k}: predicted failure passed every gate check");
            }
        } else {
            clean += 1;
            assert!(hsign_park_ok, "shot {k}: endpoint h sign lane is not parkable");
            assert!(output_ok, "shot {k}: unexplained forward-output failure");
            assert!(adapter_ok, "shot {k}: unexplained adapter failure");
            assert!(roundtrip_ok, "shot {k}: unexplained round-trip/phase/ancilla failure");
        }
    }
    eprintln!("Lilypad-G replay: {clean} clean exact, {predicted} predicted failures, {repaired} repaired cap cases, 0 unexplained");
}

#[test]
#[ignore]
fn lilypad_pool_control_count() {
    super::lilypad_g::test_delay_sigma(false);
    lilypad_g_count();
    super::lilypad_g::test_delay_sigma(true);
}

/// Matched arbitrary supported tick states, without the walk/model envelope.
/// Compare every quantum coordinate and phase for forward and inverse emission;
/// the inverse is fed the forward image, including sigma's promised value.
#[test]
fn lilypad_sigma_pool_exact() {
    let sch = sched_g();
    let mut rng = Rng::new(0x517a10a);
    let mut checked = 0usize;
    for t in 1..=sch.s {
        for regen in [false, true] {
            let make = |loan: bool, inverse: bool| {
                super::lilypad_g::test_delay_sigma(loan);
                let mut b = B::new();
                let w = PWalk { a: b.alloc_n(sch.w), bb: b.alloc_n(sch.w),
                    q: if regen { b.alloc_n(13) } else { vec![] },
                    h: b.alloc_n(HB), capq: 11, log: b.alloc_n(8) };
                let sc = if regen { PScr::alloc_inv_g(&mut b, 0) } else { PScr::alloc_fwd(&mut b, 10) };
                let e = if regen { w.qfr(t)[12] } else { sc.e };
                let mut extra = vec![];
                if regen { extra.push(sc.e); extra.extend(&sc.d); extra.extend(&sc.sp); }
                let rho = super::lilypad_g::rho_stable(&w, t-1);
                b.begin();
                super::lilypad_g::step_core_g(&mut b, &w, t, &sch, &sc, &rho, e, &extra, None);
                let r = b.end(); b.play(&r, inverse);
                (b, w)
            };
            let (old, w) = make(false, false);
            let (new, _) = make(true, false);
            let (old_inv, _) = make(false, true);
            let (new_inv, _) = make(true, true);
            for batch in 0..2 {
                let mut xr0 = xof(format!("sigma-old-{t}-{regen}-{batch}").as_bytes());
                let mut xr1 = xof(format!("sigma-new-{t}-{regen}-{batch}").as_bytes());
                let mut a = sim(&old, &mut xr0);
                let mut z = sim(&new, &mut xr1);
                // Low/active coordinates arbitrary; inactive high coordinates
                // are sign copies, precisely the LSC clean-loan precondition.
                for k in 0..64 {
                    for (is_a, len, cofactor) in [(true,sch.kv[t],false),(false,sch.kv[t],false),
                        (true,sch.kc[t],true),(false,sch.kc[t],true)] {
                        let value = rng.below(len);
                        let total = if cofactor { sch.w-sch.c[t] } else { sch.c[t] };
                        for j in 0..total {
                            let q = if cofactor { if is_a { w.asig(t,j) } else { w.bsig(j) } }
                                else if is_a { w.af(t,j) } else { w.bf(j) };
                            if value.bit(j.min(len-1)) { a.qubits[q.0 as usize] |= 1u64<<k; }
                        }
                    }
                    for qs in [&w.h, &w.log, &w.q] {
                        let value=rng.below(qs.len());
                        for (j,q) in qs.iter().enumerate() {
                            if value.bit(j) { a.qubits[q.0 as usize] |= 1u64<<k; }
                        }
                    }
                }
                let input=a.qubits.clone(); z.qubits.clone_from(&input);
                a.apply_iter(old.ops.iter()); z.apply_iter(new.ops.iter());
                assert_eq!(a.qubits,z.qubits,"forward t={t} regen={regen} batch={batch}");
                assert_eq!(a.phase,0); assert_eq!(z.phase,0);
                let mut xr2=xof(b"sigma-inverse-old"); let mut xr3=xof(b"sigma-inverse-new");
                let mut ai=sim(&old_inv,&mut xr2); let mut zi=sim(&new_inv,&mut xr3);
                ai.qubits.clone_from(&a.qubits); zi.qubits.clone_from(&z.qubits);
                ai.apply_iter(old_inv.ops.iter()); zi.apply_iter(new_inv.ops.iter());
                assert_eq!(ai.qubits,input,"old inverse t={t} regen={regen}");
                assert_eq!(zi.qubits,input,"new inverse t={t} regen={regen}");
                assert_eq!(ai.phase,0); assert_eq!(zi.phase,0);
                checked+=64;
            }
        }
    }
    super::lilypad_g::test_delay_sigma(true);
    eprintln!("SIGMA_POOL_EXACT {checked} arbitrary supported forward/inverse lane states passed");
}

#[test]
#[ignore]
fn lilypad_l2_negative_controls() {
    std::env::set_var("LILYPAD_CAPQ", "11");
    std::env::set_var("LILYPAD_K", "2");
    let rho_corpus = format!(
        "{}/../research/pdhd-892-handoff/probes/r8_combined/corpora/rho.txt",
        env!("CARGO_MANIFEST_DIR")
    );
    for mode in [1u8, 2, 3, 4, 5, 7] {
        if mode == 7 {
            std::env::set_var("LILYPAD_G_XFILE", &rho_corpus);
            std::env::set_var("LILYPAD_G_BATCH", "0");
        } else {
            std::env::remove_var("LILYPAD_G_XFILE");
            std::env::set_var("LILYPAD_SEED", format!("{}", 0x7200 + mode as usize));
        }
        super::lilypad::l2_test_neg(mode);
        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
        super::lilypad::l2_test_neg(0);
        assert!(failed.is_err(), "L2 negative control mode {mode} did not fire");
    }
    std::env::remove_var("LILYPAD_G_XFILE");
    std::env::remove_var("LILYPAD_G_BATCH");
}

#[test]
#[ignore]
fn lilypad_l4_negative_controls() {
    std::env::set_var("LILYPAD_CAPQ", "11");
    std::env::set_var("LILYPAD_K", "2");
    std::env::set_var(
        "LILYPAD_G_XFILE",
        format!(
            "{}/../research/pdhd-892-handoff/probes/r8_combined/corpora/cap1.txt",
            env!("CARGO_MANIFEST_DIR")
        ),
    );
    std::env::set_var("LILYPAD_G_BATCH", "0");
    for mode in [1u8, 2, 3] {
        super::lilypad::l4_test_neg(mode);
        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
        super::lilypad::l4_test_neg(0);
        assert!(failed.is_err(), "L4 negative control mode {mode} did not fire");
    }
    std::env::remove_var("LILYPAD_G_XFILE");
    std::env::remove_var("LILYPAD_G_BATCH");
}

#[test]
#[ignore]
fn lilypad_l5_rare_negative_controls() {
    std::env::set_var("LILYPAD_CAPQ", "11");
    std::env::set_var("LILYPAD_K", "2");
    let corpus = |name: &str| {
        format!(
            "{}/../research/pdhd-892-handoff/probes/r8_combined/corpora/{name}",
            env!("CARGO_MANIFEST_DIR")
        )
    };
    std::env::set_var("LILYPAD_G_BATCH", "0");

    std::env::set_var("LILYPAD_G_XFILE", corpus("mined.txt"));
    super::lilypad::l5_test_neg(1);
    let q11 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
    super::lilypad::l5_test_neg(0);
    assert!(q11.is_err(), "L5 q11 core-offset control did not fire");

    std::env::set_var("LILYPAD_G_XFILE", corpus("open.txt"));
    super::lilypad::l5_test_neg(2);
    let c6cf1 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
    super::lilypad::l5_test_neg(0);
    assert!(c6cf1.is_err(), "L5 C6 post-swap-flag control did not fire");

    std::env::set_var("LILYPAD_G_XFILE", corpus("rho.txt"));
    super::lilypad::l2_test_neg(7);
    let rhopub = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
    super::lilypad::l2_test_neg(0);
    assert!(rhopub.is_err(), "L5 public-rho proxy control did not fire");

    std::env::set_var("LILYPAD_G_XFILE", corpus("cap1.txt"));
    super::lilypad_g::g_test_neg(6);
    let noadrho = std::panic::catch_unwind(std::panic::AssertUnwindSafe(lilypad_g_count));
    super::lilypad_g::g_test_neg(0);
    assert!(noadrho.is_err(), "L5 no-adapter-rho control did not fire");

    std::env::remove_var("LILYPAD_G_XFILE");
    std::env::remove_var("LILYPAD_G_BATCH");
}

#[test]
#[ignore]
fn lilypad_g_endpoint_adapter() {
    let sch = sched_g();
    let qb = 13;
    let cap = env_usize("LILYPAD_CAP", 893) as u64;
    let Setup { mut b, y, x, w } = setup(&sch, qb, true, false);
    let g = GScr;
    let room = cap.saturating_sub(b.live + 2 + NT as u64) as usize;
    let sc = PScr::alloc_fwd(&mut b, room);
    let _m = walk_forward_g(&mut b, &w, &sch, &sc, &g, None);
    let adapter = endpoint_adapter_g(&mut b, &w, &sch, &sc);
    let n0 = b.ops.len();
    b.play(&adapter, false);
    let n1 = b.ops.len();
    let cost = super::tests_chunked::expected_t(&b.ops[n0..n1]);
    eprintln!("Lilypad-G endpoint adapter: expected T {cost:.0}, peak {}", b.peak);
    assert!(cost <= 1000.0, "adapter kill threshold exceeded: {cost}");
    let mut rng = Rng::new(0x61_ada7u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let ys: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-adapter");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops.iter());
    let pmod = p();
    let endpoint_exp = sch.s - usize::from(HALF_COFACTOR_G);
    let two_s = N::from(2u64).pow_mod(N::from(endpoint_exp as u64), pmod);
    let inv: Vec<QubitId> = (0..sch.w - sch.c[sch.s + 1]).map(|j| w.asig(sch.s + 1, j)).collect();
    let key = w.bf(1);
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    for t in 1..=sch.s {
        for mm in &mut ms {
            mm.tick(t, &sch, qb);
        }
    }
    let mut exact = 0;
    for k in 0..64 {
        if ms[k].bad || ms[k].pm.g != N::ZERO {
            continue;
        }
        exact += 1;
        let c = get_s(&s.qubits, &inv, k);
        let cmod = if c.bit(TOP) {
            let a = (!c).wrapping_add(N::from(1u64)) % pmod;
            if a == N::ZERO { N::ZERO } else { pmod - a }
        } else {
            c % pmod
        };
        let got = cmod.mul_mod(xs[k], pmod);
        let neg = (s.qubits[key.0 as usize] >> k) & 1 != 0;
        let want = if neg { pmod - two_s } else { two_s };
        assert_eq!(got, want, "shot {k}: Lilypad-G endpoint relation");
        let mut keep = vec![false; s.qubits.len()];
        for &q in y.iter().chain(inv.iter()).chain(w.h.iter()).chain(w.log.iter()) {
            keep[q.0 as usize] = true;
        }
        keep[key.0 as usize] = true;
        for (i, row) in s.qubits.iter().enumerate() {
            if !keep[i] {
                assert_eq!((row >> k) & 1, 0, "shot {k}: adapter residue q{i}");
            }
        }
    }
    eprintln!("Lilypad-G endpoint adapter exact on {exact}/64 shots");
    assert!(exact >= 60);
}

/// Minimum valid shortage-five instance. Exhaust every odd constant, input,
/// control value and all four measurement outcomes; the integer oracle also
/// checks restoration of lower data borrowed by the six-control increment.
#[test]
fn lilypad_const_add_shortage5_exhaustive() {
    use sha3::digest::XofReader;
    struct Outcomes { assignment: u8, position: usize }
    impl XofReader for Outcomes {
        fn read(&mut self, out: &mut [u8]) {
            assert_eq!(out.len(), 8);
            assert!(self.position < 4);
            out.fill(if (self.assignment >> self.position) & 1 != 0 { 255 } else { 0 });
            self.position += 1;
        }
    }
    let mut checked = 0u64;
    for k in (1u64..1024).step_by(2) {
        let mut b = B::new();
        let ctrl = b.alloc();
        let target = b.alloc_n(10);
        let pool = b.alloc_n(4);
        super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
        let (nq, nb, _, _) = analyze_ops(b.ops.iter());
        for outcomes in 0..16 {
            for cv in 0..=1u64 {
                for base in (0usize..1024).step_by(64) {
                    let mut rng = Outcomes { assignment: outcomes, position: 0 };
                    let mut s = Simulator::new(nq as usize, nb as usize, &mut rng);
                    s.qubits[ctrl.0 as usize] = if cv == 1 { u64::MAX } else { 0 };
                    for lane in 0..64 {
                        for (i, q) in target.iter().enumerate() {
                            s.qubits[q.0 as usize] |= (((base + lane) >> i & 1) as u64) << lane;
                        }
                    }
                    s.apply_iter(b.ops.iter());
                    assert_eq!(s.phase, 0, "phase k={k} outcomes={outcomes} cv={cv}");
                    assert_eq!(s.qubits[ctrl.0 as usize], if cv == 1 { u64::MAX } else { 0 });
                    assert!(pool.iter().all(|q| s.qubits[q.0 as usize] == 0));
                    for lane in 0..64 {
                        assert_eq!(get_u(&s.qubits, &target, lane) as u64, (base as u64 + lane as u64 + cv * k) & 1023,
                            "value k={k} outcomes={outcomes} cv={cv} input={}", base + lane);
                    }
                    assert_eq!(rng.position, 4);
                    checked += 64;
                }
            }
        }
    }
    assert_eq!(checked, 16_777_216);
    eprintln!("SHORTAGE5_EXHAUSTIVE scalar_assignments={checked} PASS");
}

#[test]
fn lilypad_const_add_shortage5_production_width() {
    use sha3::digest::XofReader;
    let constants = [1u64, 977, 0x1_0000_03d1, 0x8000_0000_0000_0001, 0xaaaa_aaaa_aaaa_aaab, u64::MAX];
    let mut checked = 0;
    for k in constants {
        let mut b = B::new();
        let ctrl = b.alloc();
        let target = b.alloc_n(64);
        let pool = b.alloc_n(58);
        super::modp_ft::const_add_pool(&mut b, &target, ctrl, k, &pool);
        let (nq, nb, _, _) = analyze_ops(b.ops.iter());
        for cv in 0..=1u64 {
            let mut data_rng = xof(format!("shortage5-data-{k}-{cv}").as_bytes());
            for batch in 0..24usize {
                let mut values = [0u64; 64];
                for (lane, value) in values.iter_mut().enumerate() {
                    *value = if batch < 8 {
                        let low = [0, 1, (1u64 << 58) - 1, (1u64 << 58) - 2, 1u64 << 57, (1u64 << 57) - 1,
                            0x02aa_aaaa_aaaa_aaaa, 0x0155_5555_5555_5555][batch];
                        ((lane as u64) << 58) | low
                    } else {
                        let mut bytes = [0; 8]; data_rng.read(&mut bytes); u64::from_le_bytes(bytes)
                    };
                }
                let mut rng = xof(format!("shortage5-measure-{k}-{cv}-{batch}").as_bytes());
                let mut s = Simulator::new(nq as usize, nb as usize, &mut rng);
                s.qubits[ctrl.0 as usize] = if cv == 1 { u64::MAX } else { 0 };
                for (lane, value) in values.iter().enumerate() {
                    for (i, q) in target.iter().enumerate() {
                        s.qubits[q.0 as usize] |= ((value >> i) & 1) << lane;
                    }
                }
                s.apply_iter(b.ops.iter());
                assert_eq!(s.phase, 0, "phase k={k} cv={cv} batch={batch}");
                assert_eq!(s.qubits[ctrl.0 as usize], if cv == 1 { u64::MAX } else { 0 });
                assert!(pool.iter().all(|q| s.qubits[q.0 as usize] == 0));
                for (lane, value) in values.iter().enumerate() {
                    assert_eq!(get_u(&s.qubits, &target, lane) as u64, value.wrapping_add(cv * k));
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 18_432);
    eprintln!("SHORTAGE5_PRODUCTION_WIDTH scalar_assignments={checked} PASS");
}

#[test]
#[should_panic(expected = "enough disjoint dirty data lanes")]
fn lilypad_const_add_shortage5_rejects_insufficient_dirty() {
    let mut b = B::new();
    let ctrl = b.alloc();
    let target = b.alloc_n(8);
    let pool = b.alloc_n(2);
    super::modp_ft::const_add_pool(&mut b, &target, ctrl, 1, &pool);
}

#[test]
fn lilypad_recycled_carry_all_outcomes() {
    use crate::circuit::OperationType;
    use sha3::digest::XofReader;
    struct Outcomes { assignment: usize, position: usize }
    impl XofReader for Outcomes {
        fn read(&mut self,out:&mut[u8]) {
            assert_eq!(out.len(),8);
            out.fill(if self.assignment>>self.position&1!=0 {255}else{0});
            self.position+=1;
        }
    }
    let mut checked=0u64;
    for (n,pool_len) in [(7usize,4usize),(8,4)] {
        for k in 1u64..1u64<<n {
            let need=n-1-k.trailing_zeros() as usize;
            let loan=need.saturating_sub(pool_len);
            if !(2..=5).contains(&loan) || pool_len<=loan {continue;}
            for inverse in [false,true] {
                let mut b=B::new();let h=b.alloc();let t=b.alloc_n(n);let pool=b.alloc_n(pool_len);
                b.begin();super::modp_ft::const_add_recycled(&mut b,&t,h,k,&pool);
                let r=b.end();b.play(&r,inverse);
                let draws=b.ops.iter().filter(|op| op.kind==OperationType::Hmr).count();
                assert_eq!(draws,need+loan);
                assert!(b.ops.iter().all(|op| !matches!(op.kind,OperationType::PushCondition|OperationType::PopCondition)));
                let (nq,nb,_,_)=analyze_ops(b.ops.iter());
                for assignment in 0..1usize<<draws {
                    for control in 0..=1u64 {
                        for base in (0..1usize<<n).step_by(64) {
                            let mut rng=Outcomes{assignment,position:0};
                            let mut s=Simulator::new(nq as usize,nb as usize,&mut rng);
                            s.qubits[h.0 as usize]=if control!=0 {u64::MAX}else{0};
                            for lane in 0..64 { for (j,q) in t.iter().enumerate() {
                                s.qubits[q.0 as usize]|=(((base+lane)>>j&1) as u64)<<lane;
                            }}
                            s.apply_iter(b.ops.iter());
                            assert_eq!(s.phase,0,"n{n} k{k} inverse{inverse} assignment{assignment}");
                            assert_eq!(s.qubits[h.0 as usize],if control!=0 {u64::MAX}else{0});
                            assert!(pool.iter().all(|q| s.qubits[q.0 as usize]==0));
                            for lane in 0..64 {
                                let x=(base+lane) as u64;
                                let want=if inverse {x.wrapping_sub(control*k)}else{x.wrapping_add(control*k)}&((1<<n)-1);
                                assert_eq!(get_u(&s.qubits,&t,lane),want,"n{n} k{k} inverse{inverse}");
                            }
                            assert_eq!(rng.position,draws);checked+=64;
                        }
                    }
                }
            }
        }
    }
    eprintln!("RECYCLED_CARRY_ALL_OUTCOMES scalar_assignments={checked} PASS");
}

#[test]
#[should_panic(expected="distinct bridge")]
fn lilypad_recycled_carry_rejects_bridge_alias() {
    let mut b=B::new();let h=b.alloc();let t=b.alloc_n(9);let pool=b.alloc_n(4);
    super::modp_ft::const_add_recycled(&mut b,&t,h,1,&pool);
}

#[test]
fn lilypad_recycled_carry_64bit_directions() {
    use sha3::digest::XofReader;
    let constants=[1u64,977,0x1_0000_03d1,0x8000_0000_0000_0001,0xaaaa_aaaa_aaaa_aaab,u64::MAX,0x9e37_79b9,0xffff_ffff_61c8_8647];
    let mut checked=0;
    for k in constants {
        for inverse in [false,true] {
            let mut b=B::new();let h=b.alloc();let t=b.alloc_n(64);let pool=b.alloc_n(58);
            b.begin();super::modp_ft::const_add_pool(&mut b,&t,h,k,&pool);
            let r=b.end();b.play(&r,inverse);
            assert_eq!(b.tof,68,"constant {k:#x} inverse={inverse}");
            let (nq,nb,_,_)=analyze_ops(b.ops.iter());
            assert_eq!(nq,123);
            for control in 0..=1u64 {
                for batch in 0..32 {
                    let mut data=xof(format!("recycle-data-{k}-{batch}").as_bytes());
                    let mut tape=xof(format!("recycle-tape-{k}-{inverse}-{control}-{batch}").as_bytes());
                    let mut values=[0u64;64];
                    for (lane,v) in values.iter_mut().enumerate() {
                        if batch<8 {
                            let low=[0,1,(1u64<<58)-1,(1u64<<58)-2,(1u64<<5)-1,1u64<<57,0x02aa_aaaa_aaaa_aaaa,0x0155_5555_5555_5555][batch];
                            *v=((lane as u64)<<58)|low;
                        } else { let mut bytes=[0;8];data.read(&mut bytes);*v=u64::from_le_bytes(bytes); }
                    }
                    let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);
                    s.qubits[h.0 as usize]=if control!=0{u64::MAX}else{0};
                    for (lane,v) in values.iter().enumerate(){for (j,q) in t.iter().enumerate(){s.qubits[q.0 as usize]|=(v>>j&1)<<lane;}}
                    s.apply_iter(b.ops.iter());
                    assert_eq!(s.phase,0);assert_eq!(s.qubits[h.0 as usize],if control!=0{u64::MAX}else{0});
                    assert!(pool.iter().all(|q|s.qubits[q.0 as usize]==0));
                    for (lane,v) in values.iter().enumerate(){
                        let want=if inverse{v.wrapping_sub(control*k)}else{v.wrapping_add(control*k)};
                        assert_eq!(get_u(&s.qubits,&t,lane),want);checked+=1;
                    }
                }
            }
        }
    }
    eprintln!("RECYCLED_CARRY_64BIT_DIRECTIONS scalar_assignments={checked} native_T=68 PASS");
}
#[test]
fn lilypad_recycled_carry_shortage6_directions() {
    use sha3::digest::XofReader;
    let constants=[1u64,977,0x1_0000_03d1,0x8000_0000_0000_0001,0xaaaa_aaaa_aaaa_aaab,u64::MAX,0x9e37_79b9,0xffff_ffff_61c8_8647];
    let mut checked=0;
    for k in constants {
        for inverse in [false,true] {
            let mut b=B::new();let h=b.alloc();let t=b.alloc_n(64);let pool=b.alloc_n(57);
            b.begin();super::modp_ft::const_add_pool(&mut b,&t,h,k,&pool);
            let r=b.end();b.play(&r,inverse);
            assert_eq!(b.tof,69,"constant {k:#x} inverse={inverse}");
            let (nq,nb,_,_)=analyze_ops(b.ops.iter());
            assert_eq!(nq,122);
            for control in 0..=1u64 {
                for batch in 0..32 {
                    let mut data=xof(format!("recycle-data-{k}-{batch}").as_bytes());
                    let mut tape=xof(format!("recycle-tape-{k}-{inverse}-{control}-{batch}").as_bytes());
                    let mut values=[0u64;64];
                    for (lane,v) in values.iter_mut().enumerate() {
                        if batch<8 {
                            let low=[0,1,(1u64<<57)-1,(1u64<<57)-2,(1u64<<6)-1,1u64<<56,0x00aa_aaaa_aaaa_aaaa,0x0155_5555_5555_5555][batch];
                            *v=(((lane as u64)|(((batch&1) as u64)<<6))<<57)|low;
                        } else { let mut bytes=[0;8];data.read(&mut bytes);*v=u64::from_le_bytes(bytes); }
                    }
                    let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);
                    s.qubits[h.0 as usize]=if control!=0{u64::MAX}else{0};
                    for (lane,v) in values.iter().enumerate(){for (j,q) in t.iter().enumerate(){s.qubits[q.0 as usize]|=(v>>j&1)<<lane;}}
                    s.apply_iter(b.ops.iter());
                    assert_eq!(s.phase,0);assert_eq!(s.qubits[h.0 as usize],if control!=0{u64::MAX}else{0});
                    assert!(pool.iter().all(|q|s.qubits[q.0 as usize]==0));
                    for (lane,v) in values.iter().enumerate(){
                        let want=if inverse{v.wrapping_sub(control*k)}else{v.wrapping_add(control*k)};
                        assert_eq!(get_u(&s.qubits,&t,lane),want);checked+=1;
                    }
                }
            }
        }
    }
    eprintln!("RECYCLED_CARRY_SHORTAGE6_DIRECTIONS scalar_assignments={checked} native_T=69 PASS");
}

#[test]
fn lilypad_recycled_carry_shortage6_all_outcomes() {
    use crate::circuit::OperationType;
    use sha3::digest::XofReader;
    struct Outcomes { assignment: usize, position: usize }
    impl XofReader for Outcomes {
        fn read(&mut self,out:&mut[u8]) {
            assert_eq!(out.len(),8);
            out.fill(if self.assignment>>self.position&1!=0 {255}else{0});self.position+=1;
        }
    }
    let mut checked=0u64;
    for inverse in [false,true] {
        let mut b=B::new();let h=b.alloc();let t=b.alloc_n(14);let pool=b.alloc_n(7);
        b.begin();super::modp_ft::const_add_recycled(&mut b,&t,h,0x3fff,&pool);
        let r=b.end();b.play(&r,inverse);
        let draws=b.ops.iter().filter(|op| op.kind==OperationType::Hmr).count();
        assert_eq!(draws,19);assert_eq!(b.tof,19);
        let (nq,nb,_,_)=analyze_ops(b.ops.iter());
        let values:Vec<u64>=(0..64).map(|lane| match lane/2 {
            0=>0,1=>1,2=>0x3fff,3=>0x3ffe,4=>127,5=>128,6=>63,7=>64,
            j=>(j as u64*541)&0x3fff }).collect();
        for assignment in 0..1usize<<draws {
            let mut rng=Outcomes{assignment,position:0};
            let mut s=Simulator::new(nq as usize,nb as usize,&mut rng);
            s.qubits[h.0 as usize]=0xaaaa_aaaa_aaaa_aaaa;
            for (lane,x) in values.iter().enumerate(){for(j,q)in t.iter().enumerate(){s.qubits[q.0 as usize]|=(x>>j&1)<<lane;}}
            s.apply_iter(b.ops.iter());
            assert_eq!(s.phase,0);assert_eq!(s.qubits[h.0 as usize],0xaaaa_aaaa_aaaa_aaaa);
            assert!(pool.iter().all(|q|s.qubits[q.0 as usize]==0));
            for(lane,x)in values.iter().enumerate(){
                let delta=(lane as u64&1)*0x3fff;
                let want=if inverse{x.wrapping_sub(delta)}else{x.wrapping_add(delta)}&0x3fff;
                assert_eq!(get_u(&s.qubits,&t,lane),want);
            }
            assert_eq!(rng.position,draws);checked+=64;
        }
    }
    eprintln!("RECYCLED_CARRY_SHORTAGE6_ALL_OUTCOMES scalar_assignments={checked} PASS");
}

#[test]
fn lilypad_normalizer_p3_alpha() {
    let sch=sched_g();let mut total=0usize;
    let mut oldhash=<sha3::Sha3_256 as sha3::Digest>::new();
    let mut newhash=<sha3::Sha3_256 as sha3::Digest>::new();
    for t in 1..=sch.s {
      for inverse in [false,true] {
        let make=|owned_four:bool| {
            let mut s0=setup_with_capq(&sch,13,false,true,11);
            let mut sc=PScr::alloc_inv_g(&mut s0.b,0);
            assert_eq!(sc.sp.len(),3);
            if owned_four {sc.sp.push(s0.b.alloc());}
            let (_,p3)=rec_regen_g(&mut s0.b,&s0.w,t,&sch,&sc,&GScr,None);
            s0.b.play(&p3,inverse);(s0.b,s0.w,sc)
        };
        let (old,w,sc)=make(true);let (new,_,_)=make(false);
        let donor=w.bf(0);let original=sc.sp[3];
        assert_eq!(new.ops.len(),old.ops.len()+2,"tick {t}");
        for op in [&new.ops[0],new.ops.last().unwrap()] {
            assert_eq!(op.kind,crate::circuit::OperationType::X);assert_eq!(op.q_target,donor);
        }
        for (a,z) in old.ops.iter().zip(&new.ops[1..new.ops.len()-1]) {
            assert!(![a.q_control2,a.q_control1,a.q_target].contains(&donor),"original p3 tick{t}");
            let rename=|q:QubitId| if q==original{donor.0}else{q.0};
            let ka=[a.kind as u64,rename(a.q_control2),rename(a.q_control1),rename(a.q_target),a.c_target.0,a.c_condition.0,a.r_target.0];
            let kz=[z.kind as u64,z.q_control2.0,z.q_control1.0,z.q_target.0,z.c_target.0,z.c_condition.0,z.r_target.0];
            assert_eq!(ka,kz,"p3 alpha tick{t}");
            for v in ka {sha3::Digest::update(&mut oldhash,v.to_le_bytes());}
            for v in kz {sha3::Digest::update(&mut newhash,v.to_le_bytes());}
        }
        total+=old.ops.len();
        eprintln!("P3_ALPHA tick={t} inverse={inverse} donor={} original_sp3={} original_ops={} xlow={} ylow={}",donor.0,original.0,old.ops.len(),w.asig(t+1,0).0,w.bsig(0).0);
      }
    }
    let a=sha3::Digest::finalize(oldhash);let z=sha3::Digest::finalize(newhash);assert_eq!(a,z);
    eprintln!("NORMALIZER_P3_ALPHA frames={} directions=2 operations={total} mapped_sha3={a:x} PASS",sch.s);
}

#[test]
fn lilypad_normalizer_p3_paired() {
    // p3-only comparison has no forward cap receipts; U24 is separately
    // checked by c50_cap_receipt_contract and the full point-add closure.
    super::lilypad::c50_test_mask(Some(127));
    use sha3::digest::XofReader;
    struct Tape { state:u64, mode:u8, words:usize }
    impl XofReader for Tape {
        fn read(&mut self,out:&mut[u8]) {assert_eq!(out.len(),8);self.words+=1;
            self.state^=self.state<<13;self.state^=self.state>>7;self.state^=self.state<<17;
            let x=match self.mode{0=>0,1=>u64::MAX,_=>self.state};out.copy_from_slice(&x.to_le_bytes());}
    }
    let sch=sched_g();let mut s0=setup_with_capq(&sch,13,false,true,11);
    let sc=PScr::alloc_inv_g(&mut s0.b,0);let donor=s0.w.bf(0);
    // Diagnostic storage includes the old fourth scratch ID for the paired oracle.
    let old_extra=s0.b.alloc();
    init_g(&mut s0.b,&s0.w,&sch,&sc);
    let init=s0.b.ops.clone();s0.b.ops.clear();
    let mut xr=xof(b"normalizer-reachable-walk");
    let mut current=Simulator::new(s0.b.width() as usize,100_000,&mut xr);
    let mut rng=Rng::new(2);
    for lane in 0..64 {put(&mut current.qubits,&s0.x,lane,rand_x(&mut rng));}
    current.apply_iter(init.iter()); // K8 loads the donor during tick1, not init.
    let mut checked=0usize;let mut negative=0u64;
    for t in 1..=sch.s {
        let (p1,p3)=rec_regen_g(&mut s0.b,&s0.w,t,&sch,&sc,&GScr,None);
        s0.b.play(&p1,false);let first=std::mem::take(&mut s0.b.ops);
        let before=current.qubits[donor.0 as usize];current.apply_iter(first.iter());
        if t==1 {assert_eq!(current.qubits[donor.0 as usize],u64::MAX,"K8 tick1 loads donor");}
        else {assert_eq!(current.qubits[donor.0 as usize],before,"p1 donor tick{t}");}
        s0.b.play(&p3,false);let new=std::mem::take(&mut s0.b.ops);
        let old:Vec<_>=new[1..new.len()-1].iter().map(|op|{let mut a=*op;
            if a.q_control2==donor{a.q_control2=old_extra;}if a.q_control1==donor{a.q_control1=old_extra;}if a.q_target==donor{a.q_target=old_extra;}a}).collect();
        s0.b.play(&p3,true);let new_inv=std::mem::take(&mut s0.b.ops);
        let old_inv:Vec<_>=new_inv[1..new_inv.len()-1].iter().map(|op|{let mut a=*op;
            if a.q_control2==donor{a.q_control2=old_extra;}if a.q_control1==donor{a.q_control1=old_extra;}if a.q_target==donor{a.q_target=old_extra;}a}).collect();
        for mode in 0..3 {
            for bad in [false,true] {
                let mut r0=Tape{state:0x49b6702af10e55d1^(t as u64),mode,words:0};
                let mut r1=Tape{state:r0.state,mode,words:0};
                let mut a=Simulator::new(current.num_qubits,current.num_bits,&mut r0);
                let mut z=Simulator::new(current.num_qubits,current.num_bits,&mut r1);
                a.qubits.clone_from(&current.qubits);z.qubits.clone_from(&current.qubits);
                a.bits.clone_from(&current.bits);z.bits.clone_from(&current.bits);
                a.phase=current.phase;z.phase=current.phase;
                if bad {a.qubits[donor.0 as usize]=0;z.qubits[donor.0 as usize]=0;}
                a.apply_iter(old.iter());z.apply_iter(new.iter());
                if !bad {
                    assert_eq!(a.qubits,z.qubits,"p3 quantum t{t} mode{mode}");assert_eq!(a.bits,z.bits,"p3 classical t{t}");
                    assert_eq!(a.phase,z.phase,"p3 phase t{t}");assert_eq!(z.qubits[donor.0 as usize],u64::MAX);
                    assert_eq!(z.qubits[old_extra.0 as usize],0);checked+=64;
                    a.apply_iter(old_inv.iter());z.apply_iter(new_inv.iter());
                    assert_eq!(a.qubits,z.qubits,"inverse quantum t{t}");assert_eq!(a.bits,z.bits,"inverse classical t{t}");
                    assert_eq!(a.phase,z.phase,"inverse phase t{t}");assert_eq!(z.qubits,current.qubits,"inverse restore t{t}");
                    assert_eq!(z.phase,current.phase,"inverse phase restore t{t}");checked+=64;
                } else {
                    let mut mask=a.phase^z.phase;for (x,y) in a.qubits.iter().zip(&z.qubits){mask|=x^y;}
                    negative+=mask.count_ones() as u64;
                }
                assert_eq!(r0.words,r1.words);assert_eq!(r0.state,r1.state);
            }
        }
        current.apply_iter(new.iter());assert_eq!(current.qubits[donor.0 as usize],u64::MAX);
    }
    assert!(negative>0,"bad donor premise was not detected");
    eprintln!("NORMALIZER_P3_PAIRED scalar_cases={checked} bad_entry_detected_lanes={negative} quantum/classical/phase/RNG PASS");
    super::lilypad::c50_test_mask(None);
}



#[test]
fn c43_value_low_pool_exact() {
    super::lilypad_g::c49_reference(true);
    let sch = sched_g();
    let mut rng = Rng::new(0x517a10a);
    let mut checked = 0usize;
    for t in 2..=sch.s {
        for regen in [false, true] {
            let make = |loan: bool, inverse: bool| {
                super::lilypad_g::test_low_loan(loan);
                let mut b = B::new();
                let w = PWalk { a: b.alloc_n(sch.w), bb: b.alloc_n(sch.w),
                    q: if regen { b.alloc_n(13) } else { vec![] },
                    h: b.alloc_n(HB), capq: 11, log: b.alloc_n(8) };
                let sc = if regen { PScr::alloc_inv_g(&mut b, 0) } else { PScr::alloc_fwd(&mut b, 10) };
                let e = if regen { w.qfr(t)[12] } else { sc.e };
                let mut extra = vec![];
                if regen { extra.push(sc.e); extra.extend(&sc.d); extra.extend(&sc.sp); }
                let rho = super::lilypad_g::rho_stable(&w, t-1);
                b.begin();
                super::lilypad_g::step_core_g(&mut b, &w, t, &sch, &sc, &rho, e, &extra, None);
                let r = b.end(); b.play(&r, inverse);
                (b, w)
            };
            let (old, w) = make(false, false);
            let (new, _) = make(true, false);
            let (old_inv, _) = make(false, true);
            let (new_inv, _) = make(true, true);
            for batch in 0..2 {
                let mut xr0 = xof(format!("sigma-old-{t}-{regen}-{batch}").as_bytes());
                let mut xr1 = xof(format!("sigma-new-{t}-{regen}-{batch}").as_bytes());
                let mut a = sim(&old, &mut xr0);
                let mut z = sim(&new, &mut xr1);
                // Low/active coordinates arbitrary; inactive high coordinates
                // are sign copies, precisely the LSC clean-loan precondition.
                for k in 0..64 {
                    for (is_a, len, cofactor) in [(true,sch.kv[t],false),(false,sch.kv[t],false),
                        (true,sch.kc[t],true),(false,sch.kc[t],true)] {
                        let value = rng.below(len);
                        let total = if cofactor { sch.w-sch.c[t] } else { sch.c[t] };
                        for j in 0..total {
                            let q = if cofactor { if is_a { w.asig(t,j) } else { w.bsig(j) } }
                                else if is_a { w.af(t,j) } else { w.bf(j) };
                            if value.bit(j.min(len-1)) { a.qubits[q.0 as usize] |= 1u64<<k; }
                        }
                    }
                    for qs in [&w.h, &w.log, &w.q] {
                        let value=rng.below(qs.len());
                        for (j,q) in qs.iter().enumerate() {
                            if value.bit(j) { a.qubits[q.0 as usize] |= 1u64<<k; }
                        }
                    }
                }
                // The force-add contract is two odd value operands. Test
                // every other active field arbitrarily under the LSC promise.
                a.qubits[w.af(t,0).0 as usize]=u64::MAX;
                a.qubits[w.bf(0).0 as usize]=u64::MAX;
                let input=a.qubits.clone(); z.qubits.clone_from(&input);
                a.apply_iter(old.ops.iter()); z.apply_iter(new.ops.iter());
                assert_eq!(a.qubits,z.qubits,"forward t={t} regen={regen} batch={batch}");
                assert_eq!(a.phase,0); assert_eq!(z.phase,0);
                let mut xr2=xof(b"sigma-inverse-old"); let mut xr3=xof(b"sigma-inverse-new");
                let mut ai=sim(&old_inv,&mut xr2); let mut zi=sim(&new_inv,&mut xr3);
                ai.qubits.clone_from(&a.qubits); zi.qubits.clone_from(&z.qubits);
                ai.apply_iter(old_inv.ops.iter()); zi.apply_iter(new_inv.ops.iter());
                assert_eq!(ai.qubits,input,"old inverse t={t} regen={regen}");
                assert_eq!(zi.qubits,input,"new inverse t={t} regen={regen}");
                assert_eq!(ai.phase,0); assert_eq!(zi.phase,0);
                checked+=64;
            }
        }
    }
    super::lilypad_g::test_low_loan(true); super::lilypad_g::c49_reference(false);
    eprintln!("C43_VALUE_LOW_POOL_EXACT {checked} arbitrary supported forward/inverse lane states passed");
}

#[test]
fn c49_p1_all_ticks_exact() {
    let sch = sched_g();
    let mut rng = Rng::new(0x517a10a);
    let mut checked = 0usize;
    for t in 2..=sch.s {
        for regen in [false, true] {
            let make = |loan: bool, inverse: bool| {
                super::lilypad_g::test_low_loan(true); super::lilypad_g::c49_reference(!loan);
                let mut b = B::new();
                let w = PWalk { a: b.alloc_n(sch.w), bb: b.alloc_n(sch.w),
                    q: if regen { b.alloc_n(13) } else { vec![] },
                    h: b.alloc_n(HB), capq: 11, log: b.alloc_n(8) };
                let sc = if regen { PScr::alloc_inv_g(&mut b, 0) } else { PScr::alloc_fwd(&mut b, 10) };
                let e = if regen { w.qfr(t)[12] } else { sc.e };
                let mut extra = vec![];
                if regen { extra.push(sc.e); extra.extend(&sc.d); extra.extend(&sc.sp); }
                let rho = super::lilypad_g::rho_stable(&w, t-1);
                b.begin();
                super::lilypad_g::step_core_g(&mut b, &w, t, &sch, &sc, &rho, e, &extra, None);
                let r = b.end(); b.play(&r, inverse);
                (b, w)
            };
            let (old, w) = make(false, false);
            let (new, _) = make(true, false);
            let (old_inv, _) = make(false, true);
            let (new_inv, _) = make(true, true);
            for batch in 0..2 {
                let mut xr0 = xof(format!("sigma-old-{t}-{regen}-{batch}").as_bytes());
                let mut xr1 = xof(format!("sigma-new-{t}-{regen}-{batch}").as_bytes());
                let mut a = sim(&old, &mut xr0);
                let mut z = sim(&new, &mut xr1);
                // Low/active coordinates arbitrary; inactive high coordinates
                // are sign copies, precisely the LSC clean-loan precondition.
                for k in 0..64 {
                    for (is_a, len, cofactor) in [(true,sch.kv[t],false),(false,sch.kv[t],false),
                        (true,sch.kc[t],true),(false,sch.kc[t],true)] {
                        let value = rng.below(len);
                        let total = if cofactor { sch.w-sch.c[t] } else { sch.c[t] };
                        for j in 0..total {
                            let q = if cofactor { if is_a { w.asig(t,j) } else { w.bsig(j) } }
                                else if is_a { w.af(t,j) } else { w.bf(j) };
                            if value.bit(j.min(len-1)) { a.qubits[q.0 as usize] |= 1u64<<k; }
                        }
                    }
                    for qs in [&w.h, &w.log, &w.q] {
                        let value=rng.below(qs.len());
                        for (j,q) in qs.iter().enumerate() {
                            if value.bit(j) { a.qubits[q.0 as usize] |= 1u64<<k; }
                        }
                    }
                }
                // U29 early loans require the exact tick support. Generate
                // all retained counter/log fields arbitrarily on that support.
                for k in 0..64 {
                    let hv=((k as i64 % (2*t-1) as i64)-(t as i64-1)) as u64;
                    for(j,q)in w.h.iter().enumerate(){
                        a.qubits[q.0 as usize]&=!(1u64<<k);
                        a.qubits[q.0 as usize]|=((hv>>j)&1)<<k;
                    }
                }
                if t<=11 {for q in &w.log {a.qubits[q.0 as usize]=0;}}
                // The force-add contract is two odd value operands. Test
                // every other active field arbitrarily under the LSC promise.
                a.qubits[w.af(t,0).0 as usize]=u64::MAX;
                a.qubits[w.bf(0).0 as usize]=u64::MAX;
                // The p1 input has its digit target clean; inverse p1
                // starts from the corresponding forced-add output. Other
                // Q lanes are arbitrary. A dirty qe is outside this contract.
                if regen { a.qubits[w.qfr(t)[12].0 as usize]=0; }
                let input=a.qubits.clone(); z.qubits.clone_from(&input);
                a.apply_iter(old.ops.iter()); z.apply_iter(new.ops.iter());
                assert_eq!(a.qubits,z.qubits,"forward t={t} regen={regen} batch={batch}");
                assert_eq!(a.phase,0); assert_eq!(z.phase,0);
                let mut xr2=xof(b"sigma-inverse-old"); let mut xr3=xof(b"sigma-inverse-new");
                let mut ai=sim(&old_inv,&mut xr2); let mut zi=sim(&new_inv,&mut xr3);
                ai.qubits.clone_from(&a.qubits); zi.qubits.clone_from(&z.qubits);
                ai.apply_iter(old_inv.ops.iter()); zi.apply_iter(new_inv.ops.iter());
                assert_eq!(ai.qubits,input,"old inverse t={t} regen={regen}");
                assert_eq!(zi.qubits,input,"new inverse t={t} regen={regen}");
                assert_eq!(ai.phase,0); assert_eq!(zi.phase,0);
                checked+=64;
            }
        }
    }
    super::lilypad_g::test_low_loan(true); super::lilypad_g::c49_reference(false);
    eprintln!("C49_P1_ALL_TICKS_EXACT {checked} arbitrary supported forward/inverse lane states passed");
}

#[test]
fn c49_p1_small_exhaustive() {
    use sha3::digest::XofReader;
    struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
    fn fsim<'a,R:XofReader>(b:&B,x:&'a mut R)->Simulator<'a,R> {
        let(_,nb,_,_)=crate::circuit::analyze_ops(b.ops.iter());
        Simulator::new(b.width() as usize,nb as usize,x)
    }
    let t=32;
    let sch=PSched {w:9,s:32,c:vec![4;34],kv:vec![4;34],kc:vec![5;34]};
    let make=|reference:bool,inverse:bool| {
        super::lilypad_g::c49_reference(reference);
        let mut b=B::new();let w=PWalk {a:b.alloc_n(9),bb:b.alloc_n(9),q:vec![],h:b.alloc_n(HB),capq:11,log:b.alloc_n(8)};
        // Actual low-room p1 bank: sigma only, before the constant donors.
        let sc=PScr {e:b.alloc(),sg:b.alloc(),d:vec![],tmp:vec![],sp:vec![],pool:vec![]};
        let rho=rho_stable(&w,t-1);
        b.begin();step_core_g(&mut b,&w,t,&sch,&sc,&rho,sc.e,&[],None);let r=b.end();b.play(&r,inverse);
        (b,w)
    };
    let(old,w)=make(true,false);let(new,_)=make(false,false);
    let(oi,_)=make(true,true);let(ni,_)=make(false,true);
    assert!(old.tof+old.tof_cond>new.tof+new.tof_cond,"low-room cut must activate");
    let mut checked=0;
    // All odd four-bit values, both five-bit cofactors, h sign and parity.
    let cases:Vec<_>=(0..4u64).flat_map(|h|(1..16u64).step_by(2).flat_map(move|av|
        (1..16u64).step_by(2).flat_map(move|bv|(0..32u64).flat_map(move|ac|(0..32u64).map(move|bc|(h,av,bv,ac,bc)))))).collect();
    for fb in [0u8,255,170,85]{for ib in [0u8,255,170,85]{for batch in cases.chunks(64){
        let mut x0=Fixed(fb);let mut x1=Fixed(fb);let mut a=fsim(&old,&mut x0);let mut z=fsim(&new,&mut x1);
        for(k,&(h,av,bv,ac,bc))in batch.iter().enumerate(){
            for(j,&val)in [av,bv,ac,bc].iter().enumerate(){let len=if j<2{4}else{5};
                for i in 0..len{let q=match j{0=>w.af(t,i),1=>w.bf(i),2=>w.asig(t,i),_=>w.bsig(i)};
                    if val>>i&1!=0{a.qubits[q.0 as usize]|=1<<k;}}}
            if h&1!=0{a.qubits[w.h[0].0 as usize]|=1<<k;}
            if h&2!=0{a.qubits[w.h[HB-1].0 as usize]|=1<<k;}
        }
        let init=a.qubits.clone();z.qubits.clone_from(&init);
        a.apply_iter(old.ops.iter());z.apply_iter(new.ops.iter());
        assert_eq!(a.qubits,z.qubits,"small p1 allwire fwd HMR{fb}");assert_eq!(a.phase,0);assert_eq!(z.phase,0);
        let mut x2=Fixed(ib);let mut x3=Fixed(ib);let mut ai=fsim(&oi,&mut x2);let mut zi=fsim(&ni,&mut x3);
        ai.qubits.clone_from(&a.qubits);zi.qubits.clone_from(&z.qubits);
        ai.apply_iter(oi.ops.iter());zi.apply_iter(ni.ops.iter());
        assert_eq!(ai.qubits,init);assert_eq!(zi.qubits,init);assert_eq!(ai.phase,0);assert_eq!(zi.phase,0);
        checked+=batch.len();
    }}}
    super::lilypad_g::c49_reference(false);
    eprintln!("C49_P1_SMALL_EXHAUSTIVE {checked} scalar cases, all wires/phase, forced16 tape pairs");
}

#[test]
fn c49_four_all_ticks_exact() {
    let sch = sched_g();
    let mut rng = Rng::new(0x517a10a);
    let mut checked = 0usize;
    for t in 2..=sch.s {
        for regen in [false, true] {
            let make = |loan: bool, inverse: bool| {
                super::lilypad_g::test_low_loan(true); super::lilypad_g::c49_reference(!loan);
                let mut b = B::new();
                let w = PWalk { a: b.alloc_n(sch.w), bb: b.alloc_n(sch.w),
                    q: if regen { b.alloc_n(13) } else { vec![] },
                    h: b.alloc_n(HB), capq: 11, log: b.alloc_n(8) };
                let sc = if regen { PScr::alloc_inv_g(&mut b, 0) } else { PScr::alloc_fwd(&mut b, 10) };
                let e = if regen { w.qfr(t)[12] } else { sc.e };
                let mut extra = vec![];
                if regen { extra.push(sc.e); extra.extend(&sc.d); extra.extend(&sc.sp); }
                let rho = super::lilypad_g::rho_stable(&w, t-1);
                b.begin();
                super::lilypad_g::step_core_g(&mut b, &w, t, &sch, &sc, &rho, e, &extra, None);
                let r = b.end(); b.play(&r, inverse);
                (b, w)
            };
            let (old, w) = make(false, false);
            let (new, _) = make(true, false);
            let (old_inv, _) = make(false, true);
            let (new_inv, _) = make(true, true);
            for batch in 0..2 {
                let mut xr0 = xof(format!("sigma-old-{t}-{regen}-{batch}").as_bytes());
                let mut xr1 = xof(format!("sigma-new-{t}-{regen}-{batch}").as_bytes());
                let mut a = sim(&old, &mut xr0);
                let mut z = sim(&new, &mut xr1);
                // Low/active coordinates arbitrary; inactive high coordinates
                // are sign copies, precisely the LSC clean-loan precondition.
                for k in 0..64 {
                    for (is_a, len, cofactor) in [(true,sch.kv[t],false),(false,sch.kv[t],false),
                        (true,sch.kc[t],true),(false,sch.kc[t],true)] {
                        let value = rng.below(len);
                        let total = if cofactor { sch.w-sch.c[t] } else { sch.c[t] };
                        for j in 0..total {
                            let q = if cofactor { if is_a { w.asig(t,j) } else { w.bsig(j) } }
                                else if is_a { w.af(t,j) } else { w.bf(j) };
                            if value.bit(j.min(len-1)) { a.qubits[q.0 as usize] |= 1u64<<k; }
                        }
                    }
                    for qs in [&w.h, &w.log, &w.q] {
                        let value=rng.below(qs.len());
                        for (j,q) in qs.iter().enumerate() {
                            if value.bit(j) { a.qubits[q.0 as usize] |= 1u64<<k; }
                        }
                    }
                }
                // U29 early loans require the exact tick support. Generate
                // all retained counter/log fields arbitrarily on that support.
                for k in 0..64 {
                    let hv=((k as i64 % (2*t-1) as i64)-(t as i64-1)) as u64;
                    for(j,q)in w.h.iter().enumerate(){
                        a.qubits[q.0 as usize]&=!(1u64<<k);
                        a.qubits[q.0 as usize]|=((hv>>j)&1)<<k;
                    }
                }
                if t<=11 {for q in &w.log {a.qubits[q.0 as usize]=0;}}
                // The force-add contract is two odd value operands. Test
                // every other active field arbitrarily under the LSC promise.
                a.qubits[w.af(t,0).0 as usize]=u64::MAX;
                a.qubits[w.bf(0).0 as usize]=u64::MAX;
                // The p1 input has its digit target clean; inverse p1
                // starts from the corresponding forced-add output. Other
                // Q lanes are arbitrary. A dirty qe is outside this contract.
                if regen { a.qubits[w.qfr(t)[12].0 as usize]=0; }
                // Fourth lender requires the stable U0 xor V0=1 invariant.
                a.qubits[w.bsig(0).0 as usize]=!a.qubits[w.asig(t,0).0 as usize];
                let input=a.qubits.clone(); z.qubits.clone_from(&input);
                a.apply_iter(old.ops.iter()); z.apply_iter(new.ops.iter());
                assert_eq!(a.qubits,z.qubits,"forward t={t} regen={regen} batch={batch}");
                assert_eq!(a.phase,0); assert_eq!(z.phase,0);
                let mut xr2=xof(b"sigma-inverse-old"); let mut xr3=xof(b"sigma-inverse-new");
                let mut ai=sim(&old_inv,&mut xr2); let mut zi=sim(&new_inv,&mut xr3);
                ai.qubits.clone_from(&a.qubits); zi.qubits.clone_from(&z.qubits);
                ai.apply_iter(old_inv.ops.iter()); zi.apply_iter(new_inv.ops.iter());
                assert_eq!(ai.qubits,input,"old inverse t={t} regen={regen}");
                assert_eq!(zi.qubits,input,"new inverse t={t} regen={regen}");
                assert_eq!(ai.phase,0); assert_eq!(zi.phase,0);
                checked+=64;
            }
        }
    }
    super::lilypad_g::test_low_loan(true); super::lilypad_g::c49_reference(false);
    eprintln!("C49_FOUR_ALL_TICKS_EXACT {checked} arbitrary supported forward/inverse lane states passed");
}
#[test]
fn c49_four_small_exhaustive() {
    use sha3::digest::XofReader;
    struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
    fn fsim<'a,R:XofReader>(b:&B,x:&'a mut R)->Simulator<'a,R> {
        let(_,nb,_,_)=crate::circuit::analyze_ops(b.ops.iter());
        Simulator::new(b.width() as usize,nb as usize,x)
    }
    let t=32;
    let sch=PSched {w:9,s:32,c:vec![4;34],kv:vec![4;34],kc:vec![5;34]};
    let make=|reference:bool,inverse:bool| {
        super::lilypad_g::c49_reference(reference);
        let mut b=B::new();let w=PWalk {a:b.alloc_n(9),bb:b.alloc_n(9),q:vec![],h:b.alloc_n(HB),capq:11,log:b.alloc_n(8)};
        // Actual low-room p1 bank: sigma only, before the constant donors.
        let sc=PScr {e:b.alloc(),sg:b.alloc(),d:vec![],tmp:vec![],sp:vec![],pool:vec![]};
        let rho=rho_stable(&w,t-1);
        b.begin();step_core_g(&mut b,&w,t,&sch,&sc,&rho,sc.e,&[],None);let r=b.end();b.play(&r,inverse);
        (b,w)
    };
    let(old,w)=make(true,false);let(new,_)=make(false,false);
    let(oi,_)=make(true,true);let(ni,_)=make(false,true);
    assert!(old.tof+old.tof_cond>new.tof+new.tof_cond,"low-room cut must activate");
    let mut checked=0;
    // All odd four-bit values, both five-bit cofactors, h sign and parity.
    let cases:Vec<_>=(0..4u64).flat_map(|h|(1..16u64).step_by(2).flat_map(move|av|
        (1..16u64).step_by(2).flat_map(move|bv|(0..32u64).flat_map(move|ac|(0..32u64).map(move|bc|(h,av,bv,ac,bc)))))).filter(|&(_,_,_,ac,bc)|(ac^bc)&1==1).collect();
    for fb in [0u8,255,170,85]{for ib in [0u8,255,170,85]{for batch in cases.chunks(64){
        let mut x0=Fixed(fb);let mut x1=Fixed(fb);let mut a=fsim(&old,&mut x0);let mut z=fsim(&new,&mut x1);
        for(k,&(h,av,bv,ac,bc))in batch.iter().enumerate(){
            for(j,&val)in [av,bv,ac,bc].iter().enumerate(){let len=if j<2{4}else{5};
                for i in 0..len{let q=match j{0=>w.af(t,i),1=>w.bf(i),2=>w.asig(t,i),_=>w.bsig(i)};
                    if val>>i&1!=0{a.qubits[q.0 as usize]|=1<<k;}}}
            if h&1!=0{a.qubits[w.h[0].0 as usize]|=1<<k;}
            if h&2!=0{a.qubits[w.h[HB-1].0 as usize]|=1<<k;}
        }
        let init=a.qubits.clone();z.qubits.clone_from(&init);
        a.apply_iter(old.ops.iter());z.apply_iter(new.ops.iter());
        assert_eq!(a.qubits,z.qubits,"small p1 allwire fwd HMR{fb}");assert_eq!(a.phase,0);assert_eq!(z.phase,0);
        let mut x2=Fixed(ib);let mut x3=Fixed(ib);let mut ai=fsim(&oi,&mut x2);let mut zi=fsim(&ni,&mut x3);
        ai.qubits.clone_from(&a.qubits);zi.qubits.clone_from(&z.qubits);
        ai.apply_iter(oi.ops.iter());zi.apply_iter(ni.ops.iter());
        assert_eq!(ai.qubits,init);assert_eq!(zi.qubits,init);assert_eq!(ai.phase,0);assert_eq!(zi.phase,0);
        checked+=batch.len();
    }}}
    super::lilypad_g::c49_reference(false);
    eprintln!("C49_FOUR_SMALL_EXHAUSTIVE {checked} scalar cases, all wires/phase, forced16 tape pairs");
}
#[test]
#[ignore]
fn c49_four_walk_check() {
    use super::frogstrip::SEC;
    let sch = sched_g();
    let ticks = env_usize("LILYPAD_TICKS", sch.s);
    let room = env_usize("LILYPAD_ROOM", 27);
    let prof = std::env::var("LILYPAD_SEC").is_ok();
    if prof {
        SEC.with(|s| *s.borrow_mut() = Some(Default::default()));
    }
    let mut s0 = setup(&sch, 0, false, false);
    let sc = PScr::alloc_fwd(&mut s0.b, room);
    let Setup { mut b, x, w, .. } = s0;
    init_g(&mut b, &w, &sch, &sc);
    let division = b.new_division();
    let mut bounds = vec![b.ops.len()];
    let m = b.fresh_bits(ticks + 1);
    for t in 1..=ticks {
        let rho = rho_stable(&w, t - 1);
        step_core_g(&mut b, &w, t, &sch, &sc, &rho, sc.e, &[], Some((division, false)));
        halve_g(&mut b, &w, t, &sch, &sc);
        b.hmr_to(sc.e, m[t]);
        bounds.push(b.ops.len());
    }
    let exp = super::tests_chunked::expected_t(&b.ops[bounds[0]..]);
    eprintln!("Lilypad-G forward: {ticks} ticks, expected {exp:.0} ({:.1}/tick), peak {}", exp / ticks as f64, b.peak);
    if prof {
        let mm = SEC.with(|s| s.borrow_mut().take().unwrap());
        for (name, (sum, n)) in &mm {
            eprintln!("SEC {name:14} total {sum:>10.0} n {n:>5} avg {:>8.1}", sum / *n as f64);
        }
    }
    let mut rng = Rng::new(env_usize("LILYPAD_SEED", 1) as u64);
    let xs: Vec<N> = (0..64).map(|_| rand_x(&mut rng)).collect();
    let mut xr = xof(b"lilypad-g-forward");
    let mut s = sim(&b, &mut xr);
    for k in 0..64 {
        put(&mut s.qubits, &x, k, xs[k]);
    }
    let mut ms: Vec<Gm> = xs.iter().map(|&v| Gm::new(v)).collect();
    s.apply_iter(b.ops[..bounds[0]].iter());
    let scratch: Vec<QubitId> = [sc.e, sc.sg]
        .iter()
        .copied()
        .chain(sc.tmp.iter().copied())
        .chain(sc.pool.iter().copied())
        .collect();
    let mut nbad = 0;
    for t in 1..=ticks {
        s.apply_iter(b.ops[bounds[t - 1]..bounds[t]].iter());
        for mm in &mut ms {
            mm.tick(t, &sch, 64);
        }
        nbad = check_tick_g(&w, &sch, t, &s.qubits, &ms, 64, false);
        assert_eq!(s.qubits[w.asig(t+1,0).0 as usize]^s.qubits[w.bsig(0).0 as usize],u64::MAX,"stable cofactor parity t{t}");
        let good: u64 = ms.iter().enumerate().filter(|(_, m)| !m.bad).map(|(k, _)| 1u64 << k).sum();
        for &q in &scratch {
            assert_eq!(s.qubits[q.0 as usize] & good, 0, "tick {t}: scratch q{} dirty", q.0);
        }
    }
    eprintln!("Lilypad-G forward exact on {} / 64 shots", 64 - nbad);
}

#[test]
fn c49_four_value_lender_exhaustive() {
    use sha3::digest::XofReader;
    struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
    fn fsim<'a,R:XofReader>(b:&B,x:&'a mut R)->Simulator<'a,R> {
        let(_,nb,_,_)=crate::circuit::analyze_ops(b.ops.iter());
        Simulator::new(b.width() as usize,nb as usize,x)
    }
    let t=32;
    let sch=PSched {w:10,s:32,c:vec![7;34],kv:vec![7;34],kc:vec![3;34]};
    let make=|reference:bool,inverse:bool| {
        super::lilypad_g::c49_reference(reference);
        let mut b=B::new();let w=PWalk {a:b.alloc_n(10),bb:b.alloc_n(10),q:vec![],h:b.alloc_n(HB),capq:11,log:b.alloc_n(8)};
        // Actual low-room p1 bank: sigma only, before the constant donors.
        let sc=PScr {e:b.alloc(),sg:b.alloc(),d:vec![],tmp:vec![],sp:vec![],pool:vec![]};
        let rho=rho_stable(&w,t-1);
        b.begin();step_core_g(&mut b,&w,t,&sch,&sc,&rho,sc.e,&[],None);let r=b.end();b.play(&r,inverse);
        (b,w)
    };
    let(old,w)=make(true,false);let(new,_)=make(false,false);
    let(oi,_)=make(true,true);let(ni,_)=make(false,true);
    assert!(new.ops.iter().any(|o|o.kind==crate::circuit::OperationType::CCX && o.q_target==w.bsig(0)),"fourth lender must be a physical carry target");
    assert!(old.tof+old.tof_cond>new.tof+new.tof_cond,"low-room cut must activate");
    let mut checked=0;
    // All odd four-bit values, both five-bit cofactors, h sign and parity.
    let cases:Vec<_>=(0..4u64).flat_map(|h|(1..128u64).step_by(2).flat_map(move|av|
        (1..128u64).step_by(2).flat_map(move|bv|(0..8u64).flat_map(move|ac|(0..8u64).map(move|bc|(h,av,bv,ac,bc)))))).filter(|&(_,_,_,ac,bc)|(ac^bc)&1==1).collect();
    for fb in [0u8,255,170,85]{for ib in [0u8,255,170,85]{for batch in cases.chunks(64){
        let mut x0=Fixed(fb);let mut x1=Fixed(fb);let mut a=fsim(&old,&mut x0);let mut z=fsim(&new,&mut x1);
        for(k,&(h,av,bv,ac,bc))in batch.iter().enumerate(){
            for(j,&val)in [av,bv,ac,bc].iter().enumerate(){let len=if j<2{7}else{3};
                for i in 0..len{let q=match j{0=>w.af(t,i),1=>w.bf(i),2=>w.asig(t,i),_=>w.bsig(i)};
                    if val>>i&1!=0{a.qubits[q.0 as usize]|=1<<k;}}}
            if h&1!=0{a.qubits[w.h[0].0 as usize]|=1<<k;}
            if h&2!=0{a.qubits[w.h[HB-1].0 as usize]|=1<<k;}
        }
        let init=a.qubits.clone();z.qubits.clone_from(&init);
        a.apply_iter(old.ops.iter());z.apply_iter(new.ops.iter());
        assert_eq!(a.qubits,z.qubits,"small p1 allwire fwd HMR{fb}");assert_eq!(a.phase,0);assert_eq!(z.phase,0);
        let mut x2=Fixed(ib);let mut x3=Fixed(ib);let mut ai=fsim(&oi,&mut x2);let mut zi=fsim(&ni,&mut x3);
        ai.qubits.clone_from(&a.qubits);zi.qubits.clone_from(&z.qubits);
        ai.apply_iter(oi.ops.iter());zi.apply_iter(ni.ops.iter());
        assert_eq!(ai.qubits,init);assert_eq!(zi.qubits,init);assert_eq!(ai.phase,0);assert_eq!(zi.phase,0);
        checked+=batch.len();
    }}}
    super::lilypad_g::c49_reference(false);
    eprintln!("C49_FOUR_VALUE_LENDER_EXHAUSTIVE {checked} scalar cases, all wires/phase, forced16 tape pairs");
}

#[test]
fn c42_fold_recycled_directions() {
    use sha3::digest::XofReader;
    let constants=[1u64,977,0x1_0000_03d1,0x8000_0000_0000_0001,0xaaaa_aaaa_aaaa_aaab,u64::MAX,0x9e37_79b9,0xffff_ffff_61c8_8647];
    let mut checked=0;
    for room in [57usize,58,59,60,61] { for k in constants {
        for inverse in [false,true] {
            let mut b=B::new();let h=b.alloc();let t=b.alloc_n(64);let pool=b.alloc_n(room);
            b.begin();super::modp_ft::const_add_pool(&mut b,&t,h,k,&pool);
            let r=b.end();b.play(&r,inverse);
            assert_eq!(b.tof,(126-room) as u64,"constant {k:#x} inverse={inverse}");
            let (nq,nb,_,_)=analyze_ops(b.ops.iter());
            assert_eq!(nq,65+room as u64);
            for control in 0..=1u64 {
                for batch in 0..32 {
                    let mut data=xof(format!("recycle-data-{k}-{batch}").as_bytes());
                    let mut tape=xof(format!("recycle-tape-{k}-{inverse}-{control}-{batch}").as_bytes());
                    let mut values=[0u64;64];
                    for (lane,v) in values.iter_mut().enumerate() {
                        if batch<8 {
                            let low=[0,1,(1u64<<58)-1,(1u64<<58)-2,(1u64<<5)-1,1u64<<57,0x02aa_aaaa_aaaa_aaaa,0x0155_5555_5555_5555][batch];
                            *v=((lane as u64)<<58)|low;
                        } else { let mut bytes=[0;8];data.read(&mut bytes);*v=u64::from_le_bytes(bytes); }
                    }
                    let mut s=Simulator::new(nq as usize,nb as usize,&mut tape);
                    s.qubits[h.0 as usize]=if control!=0{u64::MAX}else{0};
                    for (lane,v) in values.iter().enumerate(){for (j,q) in t.iter().enumerate(){s.qubits[q.0 as usize]|=(v>>j&1)<<lane;}}
                    s.apply_iter(b.ops.iter());
                    assert_eq!(s.phase,0);assert_eq!(s.qubits[h.0 as usize],if control!=0{u64::MAX}else{0});
                    assert!(pool.iter().all(|q|s.qubits[q.0 as usize]==0));
                    for (lane,v) in values.iter().enumerate(){
                        let want=if inverse{v.wrapping_sub(control*k)}else{v.wrapping_add(control*k)};
                        assert_eq!(get_u(&s.qubits,&t,lane),want);checked+=1;
                    }
                }
            }
        }
    }
    }
    eprintln!("RECYCLED_CARRY_64BIT_DIRECTIONS scalar_assignments={checked} native_T=68 PASS");
}
#[test]
fn c50_cap_contract() {
 use sha3::digest::XofReader;
 struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
 use super::lilypad::{c50_test_mask,cap_logic};
 let mut supported=0;let mut excluded=0;
 for compact in [false,true] {
  let make=|mask:u32,inv:bool| {
   c50_test_mask(Some(mask));let mut b=B::new();let h=b.alloc_n(HB);let log=b.alloc_n(8);
   let e=b.alloc();let sg=b.alloc();let d=if compact{b.alloc_n(1)}else{vec![]};
   let tmp=if compact{vec![]}else{b.alloc_n(8)};let sp=if compact{b.alloc_n(4)}else{vec![]};
   let mut clean=vec![e];clean.extend(&d);clean.extend(&tmp);clean.extend(&sp);
   let sc=PScr{e,sg,d,tmp,sp,pool:vec![]};let w=PWalk{a:vec![],bb:vec![],q:vec![],h,capq:11,log};
   b.begin();cap_logic(&mut b,&w,&sc);let r=b.end();let cost=b.measure(&r,inv);b.play(&r,inv);
   eprintln!("C50_CAP_PRICE compact={compact} mask={mask} inv={inv} cost={cost}");(b,w,clean,sg)
  };
  let(old,w,clean,sg)=make(0,false);let(new,_,_,_)=make(1,false);
  let(oi,_,_,_)=make(0,true);let(ni,_,_,_)=make(1,true);
  for byte in [0,255,170,85] {for batch in 0..(1usize<<(HB+9))/64 {
   let mut initial=vec![0;old.width()as usize];let mut domain=0u64;
   for lane in 0..64 {
    let v=batch*64+lane;let hm=(1i32<<HB)-1;let h=(v as i32)&hm;let sig=v>>(HB+8)!=0;
    let hp=if sig{(-h)&hm}else{(h-1)&hm};let hp=if hp>=(1<<(HB-1)){hp-(1<<HB)}else{hp};
    let pushes=sig&&h>=(1<<(HB-1))&&(h&31)<22;
    let empty_slot1=(v>>(HB+4))&15==0;
    if (-11..=(1<<(HB-1))-2).contains(&hp)&&(!sig||hp>=0)&&(!pushes||empty_slot1){domain|=1u64<<lane;}
    for(j,q)in w.h.iter().chain(w.log.iter()).chain(std::iter::once(&sg)).enumerate(){if v>>j&1!=0{initial[q.0 as usize]|=1u64<<lane;}}
   }
   let run=|b:&B,inp:&Vec<u64>|{let(_,nb,_,_)=crate::circuit::analyze_ops(b.ops.iter());let mut tape=Fixed(byte);let mut z=Simulator::new(inp.len(),(nb as usize).max(1),&mut tape);z.qubits.clone_from(inp);z.apply_iter(b.ops.iter());(z.qubits,z.phase)};
   let(a,ap)=run(&old,&initial);let(z,zp)=run(&new,&initial);let mut good=domain&!ap;
   for q in &clean{good&=!a[q.0 as usize];}
   for(x,y)in a.iter().zip(&z){assert_eq!((x^y)&good,0,"cap compact{compact} byte{byte} batch{batch}");}
   assert_eq!(zp&good,0);let(a2,ap2)=run(&oi,&a);let(z2,zp2)=run(&ni,&a);
   for(i,((x,y),want))in a2.iter().zip(&z2).zip(&initial).enumerate(){assert_eq!((x^want)&good,0,"old inverse values compact{compact} byte{byte} batch{batch} wire{i}");assert_eq!((y^want)&good,0,"new inverse values compact{compact} byte{byte} batch{batch} wire{i}");}
   assert_eq!(ap2&good,0,"old inverse phase compact{compact} byte{byte} batch{batch}");
   assert_eq!(zp2&good,0,"new inverse phase compact{compact} byte{byte} batch{batch}");supported+=good.count_ones();excluded+=64-good.count_ones();
  }}
 }
 c50_test_mask(None);eprintln!("C50_CAP supported={supported} excluded={excluded} layouts2 tapes4 forward_inverse PASS");
}

#[test]
fn c50_walk_paired() {
 use sha3::digest::XofReader;
 struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
 use super::lilypad::c50_test_mask;
 let requested=std::env::var("C50_TEST_MASK").ok().map(|s|s.parse::<u32>().unwrap()).unwrap_or(123);
 let sch=sched_g();let room=std::env::var("C50_TEST_ROOM").ok().map(|s|s.parse::<usize>().unwrap()).unwrap_or(0);
 let mut s0=setup_with_capq(&sch,13,false,true,11);let sc=PScr::alloc_inv_g(&mut s0.b,room);
 let mut rng=Rng::new(2);let xs:Vec<N>=(0..64).map(|_|rand_x(&mut rng)).collect();
 let mut xr=xof(b"c50-forward-reachable");let mut current=Simulator::new(s0.b.width()as usize,200000,&mut xr);
 for k in 0..64{put(&mut current.qubits,&s0.x,k,xs[k]);}
 init_g(&mut s0.b,&s0.w,&sch,&sc);current.apply_iter(s0.b.ops.iter());s0.b.ops.clear();
 let mut ms:Vec<Gm>=xs.iter().map(|&x|Gm::new(x)).collect();let mut checked=0;
 for t in 1..=sch.s {
  c50_test_mask(Some(0));let(p1,p3)=rec_regen_g(&mut s0.b,&s0.w,t,&sch,&sc,&GScr,None);
  s0.b.play(&p1,false);current.apply_iter(s0.b.ops.iter());s0.b.ops.clear();
  s0.b.play(&p3,false);let old=std::mem::take(&mut s0.b.ops);
  s0.b.play(&p3,true);let oldi=std::mem::take(&mut s0.b.ops);
  c50_test_mask(Some(requested));let(_,p3)=rec_regen_g(&mut s0.b,&s0.w,t,&sch,&sc,&GScr,None);
  s0.b.play(&p3,false);let new=std::mem::take(&mut s0.b.ops);
  s0.b.play(&p3,true);let newi=std::mem::take(&mut s0.b.ops);
  for m in &mut ms{m.tick(t,&sch,13);}
  let good=ms.iter().enumerate().filter(|(_,m)|!m.bad).map(|(k,_)|1u64<<k).sum::<u64>();
  for byte in [0,255,170,85] {
   let run=|ops:&Vec<crate::circuit::Op>,inp:&Vec<u64>|{let mut tape=Fixed(byte);let mut z=Simulator::new(inp.len(),200000,&mut tape);z.qubits.clone_from(inp);z.apply_iter(ops.iter());(z.qubits,z.phase)};
   let(a,ap)=run(&old,&current.qubits);let(z,zp)=run(&new,&current.qubits);
   for(i,(x,y))in a.iter().zip(&z).enumerate(){assert_eq!((x^y)&good,0,"tick{t} tape{byte} mask{requested} wire{i}");}
   assert_eq!((ap^zp)&good,0,"phase tick{t} tape{byte} mask{requested}");
   let(a2,ap2)=run(&oldi,&a);let(z2,zp2)=run(&newi,&a);
   for(i,((x,y),want))in a2.iter().zip(&z2).zip(&current.qubits).enumerate(){assert_eq!((x^want)&good,0,"old inverse t{t} wire{i}");assert_eq!((y^want)&good,0,"new inverse t{t} tape{byte} mask{requested} wire{i}");}
   assert_eq!((ap2^zp2)&good,0,"inverse phase tick{t}");checked+=2*good.count_ones()as usize;
  }
  current.apply_iter(old.iter());
 }
 c50_test_mask(None);eprintln!("C50_WALK_PAIRED mask={requested} room={room} ticks={} scalar_cases={checked} tapes4 directions2 all_wire_phase PASS",sch.s);
}

#[test]
fn c50_point_cut() {
 use super::lilypad::{c50_test_mask,c50_cap_tape_depth};
 let mask=std::env::var("C50_TEST_MASK").ok().map(|s|s.parse::<u32>().unwrap()).unwrap_or(191);
 let cap=std::env::var("C50_TEST_CAP").ok().map(|s|s.parse::<u64>().unwrap()).unwrap_or(875);
 pointadd_lilypad::test_peak(Some(cap));
 c50_test_mask(Some(mask));assert_eq!(c50_cap_tape_depth(),0);
 lilypad_point_add_end_to_end();
 assert_eq!(c50_cap_tape_depth(),0);c50_test_mask(None);pointadd_lilypad::test_peak(None);
}

#[test]
fn c50_native_census() {
 let mask=env_usize("C50_TEST_MASK",191)as u32;let cap=env_usize("C50_TEST_CAP",875)as u64;
 super::lilypad::c50_test_mask(Some(mask));pointadd_lilypad::test_peak(Some(cap));
 // The SEC profiler records callbacks, while C06 deliberately performs a
 // forward measurement outside recordings. Count its native whole trace;
 // attribute the delta to cap using the separately profiled U02 trace.
 super::frogstrip::SEC.with(|s|*s.borrow_mut()=if mask&128==0{Some(Default::default())}else{None});
 let mut b=B::new();pointadd_lilypad::point_add(&mut b);
 let(q,c,_,_)=analyze_ops(b.ops.iter());
 eprintln!("C50_NATIVE mask={mask} cap={cap} Q={q} C={c} ops={} nativeT={} condT={} expected={} allocatorQ={}",b.ops.len(),b.tof,b.tof_cond,b.tof as f64-0.5*b.tof_cond as f64,b.peak);
 let m=super::frogstrip::SEC.with(|s|s.borrow_mut().take().unwrap_or_default());
 for(name,(cost,n))in m{eprintln!("C50_SEC {name} {cost:.3} {n}");}
 super::lilypad::c50_test_mask(None);pointadd_lilypad::test_peak(None);
}

#[test]
fn c50_cap_receipt_contract() {
 use super::lilypad::{c50_test_mask,c50_cap_tape_depth,cap_logic};
 use sha3::digest::XofReader;
 struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
 c50_test_mask(Some(129));assert_eq!(c50_cap_tape_depth(),0);
 let mut b=B::new();let h=b.alloc_n(HB);let log=b.alloc_n(8);let e=b.alloc();let sg=b.alloc();
 let fsc=PScr{e,sg,d:vec![],tmp:b.alloc_n(8),sp:vec![],pool:vec![]};
 let isc=PScr{e,sg,d:b.alloc_n(1),tmp:vec![],sp:b.alloc_n(4),pool:vec![]};
 let w=PWalk{a:vec![],bb:vec![],q:vec![],h,capq:11,log};
 cap_logic(&mut b,&w,&fsc);assert_eq!(c50_cap_tape_depth(),1);
 b.begin();cap_logic(&mut b,&w,&isc);let inv=b.end();b.play(&inv,true);assert_eq!(c50_cap_tape_depth(),0);
 let(nq,nb,_,_)=analyze_ops(b.ops.iter());let mut count=0usize;
 for byte in [0,255,170,85] {for batch in 0..(1usize<<(HB+9))/64 {
  let mut tape=Fixed(byte);let mut sim=Simulator::new(nq as usize,nb as usize,&mut tape);let mut good=0u64;
  for lane in 0..64 {
   let v=batch*64+lane;let hm=(1i32<<HB)-1;let h=(v as i32)&hm;let sig=v>>(HB+8)!=0;
   let hp=if sig{(-h)&hm}else{(h-1)&hm};let hp=if hp>=(1<<(HB-1)){hp-(1<<HB)}else{hp};
   let push=sig&&h>=(1<<(HB-1))&&(h&31)<22;let empty=(v>>(HB+4))&15==0;
   if(-11..=(1<<(HB-1))-2).contains(&hp)&&(!sig||hp>=0)&&(!push||empty){good|=1u64<<lane;}
   for(j,q)in w.h.iter().chain(w.log.iter()).chain(std::iter::once(&sg)).enumerate(){if v>>j&1!=0{sim.qubits[q.0 as usize]|=1u64<<lane;}}
  }
  let before=sim.qubits.clone();sim.apply_iter(b.ops.iter());
  for(i,(x,y))in sim.qubits.iter().zip(&before).enumerate(){assert_eq!((x^y)&good,0,"receipt byte{byte} batch{batch} wire{i}");}
  assert_eq!(sim.phase&good,0,"receipt phase byte{byte} batch{batch}");count+=good.count_ones()as usize;
 }}
 c50_test_mask(None);eprintln!("C50_CAP_RECEIPT cases={count} tapes4 forward_measure_inverse_repay PASS");
}

#[test]
fn c50_marker_contract() {
 use super::lilypad::{inc_unctl,inc_mclear_fused,mclear,c50_test_mask};
 use sha3::digest::XofReader;
 struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
 let mut b=B::new();let a=b.alloc_n(16);let q=b.alloc_n(13);let h=b.alloc_n(HB);
 let w=PWalk{a,bb:vec![],q,h,log:vec![],capq:0};
 let sc=PScr{e:b.alloc(),sg:b.alloc(),d:b.alloc_n(1),tmp:b.alloc_n(8),sp:b.alloc_n(4),pool:vec![]};let t=127;
 b.begin();for &q in &w.h{b.cx(sc.sg,q);}inc_unctl(&mut b,&w.h,&sc.tmp);let hv=b.end();
 c50_test_mask(Some(0));b.begin();b.play(&hv,false);mclear(&mut b,&w,t,&sc,true);let old=b.end();
 let new=inc_mclear_fused(&mut b,&w,t,&sc,&hv,true);
 for inv in [false,true] {
  b.ops.clear();b.play(&old,inv);let oldops=std::mem::take(&mut b.ops);
  b.play(&new,inv);let newops=std::mem::take(&mut b.ops);
  let(nq,nb,_,_)=analyze_ops(oldops.iter().chain(newops.iter()));
  for byte in [0,255,170,85] {for batch in 0..16 {
   let mut initial=vec![0;nq as usize];
   for lane in 0..64 {let v=batch*64+lane;
    for(j,q)in w.h.iter().chain([w.asig(t+1,0),sc.sg,w.qfr(t)[12]].iter()).enumerate(){if v>>j&1!=0{initial[q.0 as usize]|=1u64<<lane;}}
   }
   let run=|ops:&Vec<crate::circuit::Op>|{let mut tape=Fixed(byte);let mut z=Simulator::new(nq as usize,nb as usize,&mut tape);z.qubits.clone_from(&initial);z.apply_iter(ops.iter());(z.qubits,z.phase)};
   let(a,ap)=run(&oldops);let(z,zp)=run(&newops);assert_eq!(a,z,"marker inverse{inv} tape{byte} batch{batch}");assert_eq!(ap,zp);assert_eq!(zp,0);
  }}
 }
 c50_test_mask(None);eprintln!("C50_MARKER h128 cf1 sigma Qtop exhaustive tapes4 directions2 PASS");
}

#[test]
fn c50_radix_contract() {
 use sha3::digest::XofReader;
 use super::lilypad::c50_test_mask;
 struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
 let mut checked=0usize;
 for n in [2usize,3,4,5,6,7,8,12] {for room in [1usize,8,12,16,20,26] {
  let mut b=B::new();let a=b.alloc_n(n-1);let q=b.alloc_n(n);let e=b.alloc();let c=b.alloc();let pool=b.alloc_n(room);
  b.begin();super::lilypad::c50_test_mask(Some(0));super::frogstrip::radix4_finish_mul(&mut b,&a,&q,e,c,&pool);let old=b.end();
  b.begin();super::lilypad::c50_test_mask(Some(64));super::frogstrip::radix4_finish_mul(&mut b,&a,&q,e,c,&pool);let new=b.end();
  for inv in [false,true] {
   b.ops.clear();b.play(&old,inv);let oldops=std::mem::take(&mut b.ops);b.play(&new,inv);let newops=std::mem::take(&mut b.ops);
   let(nq,nb,_,_)=analyze_ops(oldops.iter().chain(newops.iter()));
   let count=if n<=8{1usize<<(2*n)}else{(1usize<<(n+1))*16};
   for byte in [0,255,170,85] {for batch in 0..count.div_ceil(64) {
    let mut initial=vec![0;nq as usize];
    for lane in 0..64 {
     let v=batch*64+lane;let qv=v&((1<<n)-1);let ev=v>>n&1;
     let av=if n<=8{v>>(n+1)}else{let mode=v>>(n+1);match mode {0..=10=>1usize<<mode,11=>0,12=>(1<<(n-1))-1,13=>0x555&((1<<(n-1))-1),14=>0xaaa&((1<<(n-1))-1),_=>0x6d3&((1<<(n-1))-1)}};
     for(j,x)in a.iter().enumerate(){if av>>j&1!=0{initial[x.0 as usize]|=1u64<<lane;}}
     for(j,x)in q.iter().enumerate(){if qv>>j&1!=0{initial[x.0 as usize]|=1u64<<lane;}}
     if ev!=0{initial[e.0 as usize]|=1u64<<lane;}
    }
    let run=|ops:&Vec<crate::circuit::Op>|{let mut tape=Fixed(byte);let mut z=Simulator::new(nq as usize,nb as usize,&mut tape);z.qubits.clone_from(&initial);z.apply_iter(ops.iter());(z.qubits,z.phase)};
    let(a,ap)=run(&oldops);let(z,zp)=run(&newops);assert_eq!(a,z,"radix n{n} room{room} inv{inv} tape{byte} batch{batch}");assert_eq!(ap,zp);assert_eq!(zp,0);checked+=64;
   }}
  }
 }}
 c50_test_mask(None);eprintln!("C50_RADIX cases={checked} n2..8 exhaustive n12 allQ/16A/e tapes4 directions2 all_wire_phase PASS");
}

#[test]
fn c51_width_p3_compare() {
 use sha3::digest::XofReader;
 struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
 use super::lilypad::c50_test_mask;
 // Compare actual width owner views with four independent SP owners in the
 // same physical allocation. U24 has its separate forward/repay gate.
 c50_test_mask(Some(123));
 let sch=sched_g();let mut s0=setup_with_capq(&sch,13,false,true,11);
 let sc=PScr::alloc_inv_g(&mut s0.b,0);let mut reference=PScr{e:sc.e,sg:sc.sg,d:sc.d.clone(),tmp:sc.tmp.clone(),sp:sc.sp.clone(),pool:sc.pool.clone()};
 reference.sp.extend(s0.b.alloc_n(4-sc.sp.len()));
 if reference.d.is_empty(){reference.d=s0.b.alloc_n(1);}
 let mut rng=Rng::new(2);let xs:Vec<N>=(0..64).map(|_|rand_x(&mut rng)).collect();
 let mut xr=xof(b"c51-width-reachable");
 let mut current=Simulator::new(s0.b.width()as usize,200000,&mut xr);
 for k in 0..64{put(&mut current.qubits,&s0.x,k,xs[k]);}
 init_g(&mut s0.b,&s0.w,&sch,&reference);current.apply_iter(s0.b.ops.iter());s0.b.ops.clear();
 let mut ms:Vec<Gm>=xs.iter().map(|&x|Gm::new(x)).collect();let mut checked=0;
 for t in 1..=sch.s {
  let (rp1,rp3)=rec_regen_g(&mut s0.b,&s0.w,t,&sch,&reference,&GScr,None);
  let (np1,np3)=rec_regen_g(&mut s0.b,&s0.w,t,&sch,&sc,&GScr,None);
  let mut emit=|r:&Vec<super::builder::G>,inverse:bool|{s0.b.play(r,inverse);std::mem::take(&mut s0.b.ops)};
  let ro1=emit(&rp1,false);let no1=emit(&np1,false);
  let ro3=emit(&rp3,false);let no3=emit(&np3,false);
  let ri3=emit(&rp3,true);let ni3=emit(&np3,true);
  let good_pre=ms.iter().enumerate().filter(|(_,m)|!m.bad).map(|(k,_)|1u64<<k).sum::<u64>();
  let run=|ops:&Vec<crate::circuit::Op>,inp:&Vec<u64>,byte:u8|{let mut tape=Fixed(byte);let mut z=Simulator::new(inp.len(),200000,&mut tape);z.qubits.clone_from(inp);z.apply_iter(ops.iter());(z.qubits,z.phase)};
  for byte in [0,255,170,85] {
   let(a,ap)=run(&ro1,&current.qubits,byte);let(z,zp)=run(&no1,&current.qubits,byte);
   for(i,(x,y))in a.iter().zip(&z).enumerate(){assert_eq!((x^y)&good_pre,0,"p1 tick{t} tape{byte} wire{i}");}
   assert_eq!((ap^zp)&good_pre,0,"p1 phase tick{t}");
  }
  current.apply_iter(ro1.iter());
  for m in &mut ms{m.tick(t,&sch,13);}
  let good=ms.iter().enumerate().filter(|(_,m)|!m.bad).map(|(k,_)|1u64<<k).sum::<u64>();
  for byte in [0,255,170,85] {
   let(a,ap)=run(&ro3,&current.qubits,byte);let(z,zp)=run(&no3,&current.qubits,byte);
   for(i,(x,y))in a.iter().zip(&z).enumerate(){assert_eq!((x^y)&good,0,"p3 tick{t} tape{byte} wire{i}");}
   assert_eq!((ap^zp)&good,0,"p3 phase tick{t}");
   let(a2,ap2)=run(&ri3,&a,byte);let(z2,zp2)=run(&ni3,&a,byte);
   for(i,((x,y),want))in a2.iter().zip(&z2).zip(&current.qubits).enumerate(){assert_eq!((x^want)&good,0,"ref inverse t{t} wire{i}");assert_eq!((y^want)&good,0,"width inverse t{t} tape{byte} wire{i}");}
   assert_eq!((ap2^zp2)&good,0,"inverse phase tick{t}");checked+=2*good.count_ones()as usize;
  }
  current.apply_iter(ro3.iter());
 }
 c50_test_mask(None);eprintln!("C51_WIDTH_P3 ownedSP={} ticks={} scalar_cases={checked} tapes4 directions2 all_wire_phase PASS",sc.sp.len(),sch.s);
}
