//! Gate-level selftests and measurements: `SKYCOF_MM_SELFTEST=1 build_circuit`.
//!
//! Parts (`SKYCOF_MM_PARTS`, comma list, default all): `small` (exhaustive Horner modmul at
//! n = 8 / 10 over every (a, b, neg) and random at n = 12 / 16, exact and windowed, wide and
//! tight rooms, k in {0, n-ish, > n}), `park` (exhaustive fold/unfold and odometer at small n,
//! then a full-width post-park walk with random park index, forward and back), `full` (random
//! canonical inputs at n = 256 against the true product, every mode and room), `measure`
//! (Toffoli and scratch per call and per piece, TSV to `SKYCOF_MM_OUT`, default
//! skycof_mm_measure.tsv). Every check is against `model.rs` bit for bit; zero phase on every
//! event-free shot; every wire other than the named registers zero; inverse returns all to |0>.
use super::model::{mask, one, M, U512};
use super::*;
use crate::circuit::{Op, OperationType};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};
use sha3::Shake256;
use std::collections::HashSet;
use std::fmt::Write as _;
use std::sync::Mutex;

fn xof(tag: &str) -> sha3::Shake256Reader {
    let mut h = Shake256::default();
    h.update(b"skycof-mm-selftest-v1");
    h.update(tag.as_bytes());
    h.finalize_xof()
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn bits(&mut self, n: usize) -> U512 {
        let mut v = U512::ZERO;
        for i in 0..8 {
            v |= U512::from(self.next()) << (64 * i);
        }
        v & mask(n)
    }
    fn below(&mut self, p: U512, n: usize) -> U512 {
        loop {
            let v = self.bits(n);
            if v < p {
                return v;
            }
        }
    }
}

pub fn expected_t(ops: &[Op]) -> f64 {
    let mut depth = 0i32;
    let mut t = 0.0;
    for op in ops {
        match op.kind {
            OperationType::PushCondition => depth += 1,
            OperationType::PopCondition => depth -= 1,
            OperationType::CCX | OperationType::CCZ => t += 2f64.powi(-depth),
            _ => {}
        }
    }
    t
}

fn native_t(ops: &[Op]) -> usize {
    ops.iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count()
}

type Sim<'a> = Simulator<'a, sha3::Shake256Reader>;

fn set(sim: &mut Sim, r: &[Q], v: U512, shot: usize) {
    for (i, &q) in r.iter().enumerate() {
        let w = sim.qubit_mut(q);
        if v.bit(i) {
            *w |= 1u64 << shot;
        } else {
            *w &= !(1u64 << shot);
        }
    }
}

fn get(sim: &Sim, r: &[Q], shot: usize) -> U512 {
    let mut v = U512::ZERO;
    for (i, &q) in r.iter().enumerate() {
        if (sim.qubit(q) >> shot) & 1 == 1 {
            v.set_bit(i, true);
        }
    }
    v
}

/// Lanes with any nonzero wire outside `keep`.
fn garbage(sim: &Sim, nq: usize, keep: &HashSet<u64>) -> u64 {
    let mut bad = 0u64;
    for id in 0..nq {
        if !keep.contains(&(id as u64)) {
            bad |= sim.qubits[id];
        }
    }
    bad
}

fn keep_set(regs: &[&[Q]]) -> HashSet<u64> {
    regs.iter().flat_map(|r| r.iter().map(|q| q.0)).collect()
}

fn threads() -> usize {
    std::env::var("SKYCOF_MM_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(4).max(1)
}

// ─── modmul harness ─────────────────────────────────────────────────────────────────────────

pub struct MmBuild {
    ops_f: Vec<Op>,
    ops_i: Vec<Op>,
    a: Vec<Q>,
    bb: Vec<Q>,
    s: Option<Q>,
    out: Vec<Q>,
    out2: Vec<Q>,
    nq: usize,
    nb: usize,
    pub scratch_f: u32,
    pub scratch_i: u32,
    pub tf: f64,
    pub ti: f64,
    pub tf_native: usize,
}

pub fn build_mm(f: Field, cfg: Cfg, k: usize, neg: bool) -> MmBuild {
    let mut b = Builder::new();
    let a = b.alloc_qubits(f.n);
    let bb = b.alloc_qubits(f.n);
    let s = if neg { Some(b.alloc_qubit()) } else { None };
    let base = b.active_qubits();
    let (out, pf) = b.r3_peak(|b| mul_fwd(b, f, cfg, &a, &bb, k, s));
    let ops_f = b.take_ops();
    let (out2, pi) = b.r3_peak(|b| mul_inv(b, f, cfg, &a, &bb, k, s, out.clone()));
    let ops_i = b.take_ops();
    let (nq, nb) = b.i13_dims();
    let n = f.n as u32;
    MmBuild {
        tf: expected_t(&ops_f),
        ti: expected_t(&ops_i),
        tf_native: native_t(&ops_f),
        ops_f,
        ops_i,
        a,
        bb,
        s,
        out,
        out2,
        nq,
        nb: nb + 1,
        scratch_f: pf - base - n,
        scratch_i: pi - base - n,
    }
}

#[derive(Default, Debug, Clone)]
pub struct MmStats {
    pub shots: u64,
    pub value_fail: u64,
    pub inv_fail: u64,
    pub garbage_fail: u64,
    pub phase_fail: u64,
    pub event_shots_f: u64,
    pub event_shots_i: u64,
    pub residue_mismatch: u64,
    pub residue_mismatch_strict: u64,
    pub lazy_shots: u64,
    pub events_nonlazy: u64,
    pub canonical_inputs: u64,
    pub noncanonical_out: u64,
    pub exec_tf: f64,
    pub exec_ti: f64,
    pub full_batches: u64,
}

impl MmStats {
    fn add(&mut self, o: &MmStats) {
        self.shots += o.shots;
        self.value_fail += o.value_fail;
        self.inv_fail += o.inv_fail;
        self.garbage_fail += o.garbage_fail;
        self.phase_fail += o.phase_fail;
        self.event_shots_f += o.event_shots_f;
        self.event_shots_i += o.event_shots_i;
        self.residue_mismatch += o.residue_mismatch;
        self.residue_mismatch_strict += o.residue_mismatch_strict;
        self.lazy_shots += o.lazy_shots;
        self.events_nonlazy += o.events_nonlazy;
        self.canonical_inputs += o.canonical_inputs;
        self.noncanonical_out += o.noncanonical_out;
        self.exec_tf += o.exec_tf;
        self.exec_ti += o.exec_ti;
        self.full_batches += o.full_batches;
    }
    fn hard_fail(&self) -> u64 {
        self.value_fail + self.inv_fail + self.garbage_fail + self.phase_fail
    }
}

pub fn run_mm(bd: &MmBuild, m: &M, k: usize, inputs: &[(U512, U512, bool)], tag: &str) -> MmStats {
    let fixed: Vec<(U512, U512, bool)>;
    let inputs = if bd.s.is_none() {
        fixed = inputs.iter().map(|&(a, b, _)| (a, b, false)).collect();
        &fixed[..]
    } else {
        inputs
    };
    let batches: Vec<&[(U512, U512, bool)]> = inputs.chunks(64).collect();
    let nth = threads().min(batches.len()).max(1);
    let total = Mutex::new(MmStats::default());
    let p = m.p();
    let keep_f = keep_set(&[&bd.a, &bd.bb, bd.s.as_slice(), &bd.out]);
    let keep_i = keep_set(&[&bd.a, &bd.bb, bd.s.as_slice(), &bd.out2]);
    std::thread::scope(|sc| {
        for th in 0..nth {
            let (batches, total, keep_f, keep_i) = (&batches, &total, &keep_f, &keep_i);
            sc.spawn(move || {
                let mut rd = xof(&format!("{tag}/{th}"));
                let mut sim = Simulator::new(bd.nq, bd.nb, &mut rd);
                let mut st = MmStats::default();
                let mut printed = 0;
                for bi in (th..batches.len()).step_by(nth) {
                    let batch = batches[bi];
                    sim.clear_for_shot();
                    for (j, &(a, b, s)) in batch.iter().enumerate() {
                        set(&mut sim, &bd.a, a, j);
                        set(&mut sim, &bd.bb, b, j);
                        if let Some(sq) = bd.s {
                            set(&mut sim, &[sq], if s { one() } else { U512::ZERO }, j);
                        }
                    }
                    let t0 = sim.stats.toffoli_gates;
                    sim.apply_iter(bd.ops_f.iter());
                    let t1 = sim.stats.toffoli_gates;
                    let g1 = garbage(&sim, bd.nq, keep_f);
                    let ph1 = sim.phase;
                    let mut mos = Vec::with_capacity(batch.len());
                    for (j, &(a, b, s)) in batch.iter().enumerate() {
                        st.shots += 1;
                        let (mo, ev) = m.mul_fwd(a, b, k, s);
                        let lazy_any = m.lazy_touched(a, b, k, s);
                        mos.push((mo, ev, lazy_any));
                        if ev > 0 && !lazy_any {
                            st.events_nonlazy += 1;
                        }
                        let got = get(&sim, &bd.out, j);
                        let ok_in = get(&sim, &bd.a, j) == a && get(&sim, &bd.bb, j) == b;
                        if got != mo || !ok_in {
                            st.value_fail += 1;
                            if printed < 3 {
                                printed += 1;
                                eprintln!("  VALUE FAIL {tag}: a={a:#x} b={b:#x} s={s} got={got:#x} model={mo:#x}");
                            }
                        }
                        if (g1 >> j) & 1 == 1 {
                            st.garbage_fail += 1;
                        }
                        if ev > 0 {
                            st.event_shots_f += 1;
                        } else if (ph1 >> j) & 1 == 1 {
                            st.phase_fail += 1;
                        }
                        if a < p && b < p {
                            st.canonical_inputs += 1;
                            let tr = m.truth(a, b, k, s);
                            let lazy = lazy_any;
                            st.lazy_shots += lazy as u64;
                            if mo.reduce_mod(p) != tr {
                                st.residue_mismatch += 1;
                                st.residue_mismatch_strict += !lazy as u64;
                            }
                            if mo >= p {
                                st.noncanonical_out += 1;
                            }
                        }
                    }
                    sim.apply_iter(bd.ops_i.iter());
                    let t2 = sim.stats.toffoli_gates;
                    if batch.len() == 64 {
                        st.full_batches += 1;
                        st.exec_tf += (t1 - t0) as f64 / 64.0;
                        st.exec_ti += (t2 - t1) as f64 / 64.0;
                    }
                    let g2 = garbage(&sim, bd.nq, keep_i);
                    let ph2 = sim.phase;
                    for (j, &(a, b, s)) in batch.iter().enumerate() {
                        let (mo, ev, lazy_any) = mos[j];
                        let (mz, ev2) = m.mul_inv(a, b, k, s, mo);
                        if ev2 > 0 && !lazy_any {
                            st.events_nonlazy += 1;
                        }
                        let got = get(&sim, &bd.out2, j);
                        let ok_in = get(&sim, &bd.a, j) == a && get(&sim, &bd.bb, j) == b;
                        if got != mz || !ok_in || (ev == 0 && ev2 == 0 && !mz.is_zero()) {
                            st.inv_fail += 1;
                            if printed < 6 {
                                printed += 1;
                                eprintln!("  INV FAIL {tag}: a={a:#x} b={b:#x} s={s} got={got:#x} model={mz:#x}");
                            }
                        }
                        if (g2 >> j) & 1 == 1 {
                            st.garbage_fail += 1;
                        }
                        if ev2 > 0 {
                            st.event_shots_i += 1;
                        }
                        if ev == 0 && ev2 == 0 && (ph2 >> j) & 1 == 1 {
                            st.phase_fail += 1;
                        }
                    }
                }
                total.lock().unwrap().add(&st);
            });
        }
    });
    total.into_inner().unwrap()
}

pub struct Metrics { pub tf: f64, pub ti: f64, pub tf_native: usize, pub scratch_f: u32, pub scratch_i: u32 }

fn mm_case(f: Field, cfg: Cfg, k: usize, neg: bool, inputs: &[(U512, U512, bool)], label: &str, log: &mut String) -> (MmStats, Metrics) {
    let bd = build_mm(f, cfg, k, neg);
    let m = M::new(f, cfg);
    let st = run_mm(&bd, &m, k, inputs, label);
    assert!(bd.scratch_f as usize <= cfg.room && bd.scratch_i as usize <= cfg.room,
        "{label}: scratch {}/{} over room {}", bd.scratch_f, bd.scratch_i, cfg.room);
    let line = format!(
        "{label}\tn={} c={} w={} W={} room={} k={k} neg={neg}\tshots={} fail(value/inv/garbage/phase)={}/{}/{}/{} events(f/i)={}/{} residue_mismatch={}/{} (non-lazy {}, lazy shots {}, events on non-lazy shots {}) noncanon={} T_fwd={:.1} T_inv={:.1} scratch={}/{}",
        f.n, f.c, cfg.fold_w, cfg.cmp_w, cfg.room, st.shots, st.value_fail, st.inv_fail, st.garbage_fail, st.phase_fail,
        st.event_shots_f, st.event_shots_i, st.residue_mismatch, st.canonical_inputs, st.residue_mismatch_strict, st.lazy_shots, st.events_nonlazy,
        st.noncanonical_out, bd.tf, bd.ti,
        bd.scratch_f, bd.scratch_i);
    eprintln!("{line}");
    log.push_str(&line);
    log.push('\n');
    assert_eq!(st.hard_fail(), 0, "{label}: hard failures");
    if cfg.fold_w == f.n && cfg.cmp_w == f.n {
        // exact mode: every canonical input whose intermediates stay in [0, p) gives the true residue
        assert_eq!(st.residue_mismatch_strict, 0, "{label}: exact mode residue mismatch outside the lazy window");
        assert_eq!(st.events_nonlazy, 0, "{label}: exact mode erase event outside the lazy window");
    }
    (st, Metrics { tf: bd.tf, ti: bd.ti, tf_native: bd.tf_native, scratch_f: bd.scratch_f, scratch_i: bd.scratch_i })
}

fn all_inputs(n: usize, neg: bool) -> Vec<(U512, U512, bool)> {
    let mut v = Vec::new();
    for a in 0..(1u64 << n) {
        for b in 0..(1u64 << n) {
            v.push((U512::from(a), U512::from(b), false));
            if neg {
                v.push((U512::from(a), U512::from(b), true));
            }
        }
    }
    v
}

fn random_inputs(n: usize, p: U512, count: usize, neg: bool, canonical: bool, seed: u64) -> Vec<(U512, U512, bool)> {
    let mut r = Rng(seed);
    (0..count)
        .map(|_| {
            let (a, b) = if canonical { (r.below(p, n), r.below(p, n)) } else { (r.bits(n), r.bits(n)) };
            (a, b, neg && r.next() & 1 == 1)
        })
        .collect()
}

fn part_small(log: &mut String) {
    eprintln!("== small: exhaustive / random Horner modmul ==");
    // (n, c, guard, W, tight room)
    let fields = [(8usize, 5u128, 1usize, 2usize, 5usize), (10, 3, 2, 3, 6)];
    for &(n, c, g, ww, tight) in &fields {
        let f = Field { n, c };
        let inputs = all_inputs(n, true);
        let cfgs = [
            ("exact-wide", Cfg::exact(f, 4 * n)),
            ("exact-tight", Cfg::exact(f, tight)),
            ("win-wide", Cfg::windowed(f, g, ww, 4 * n)),
            ("win-tight", Cfg::windowed(f, g, ww, tight)),
        ];
        for (name, cfg) in cfgs {
            for k in [0usize, 3, n - 2, n, n + 3] {
                mm_case(f, cfg, k, true, &inputs, &format!("small-{n}-{name}"), log);
            }
        }
    }
    for &(n, c, g, ww, tight) in &[(12usize, 3u128, 3usize, 4usize, 7usize), (16, 15, 3, 5, 8)] {
        let f = Field { n, c };
        let p = M::new(f, Cfg::exact(f, 1)).p();
        let inputs = random_inputs(n, p, 1 << 17, true, false, 77 + n as u64);
        for (name, cfg) in [("exact-wide", Cfg::exact(f, 4 * n)), ("exact-tight", Cfg::exact(f, tight)),
                            ("win-wide", Cfg::windowed(f, g, ww, 4 * n)), ("win-tight", Cfg::windowed(f, g, ww, tight))] {
            for k in [0usize, 5, n - 3, n + 7] {
                mm_case(f, cfg, k, true, &inputs, &format!("rand-{n}-{name}"), log);
            }
        }
    }
}

// ─── park: fold/unfold, odometer, post-park walk ──────────────────────────────────────────

fn part_park(log: &mut String) {
    eprintln!("== park: fold/unfold and odometer (exhaustive) ==");
    for &(n, c, g) in &[(8usize, 5u128, 1usize), (10, 3, 2)] {
        let f = Field { n, c };
        for (name, cfg) in [("exact", Cfg::exact(f, 2 * n)), ("win", Cfg::windowed(f, g, n, 2 * n)), ("win-tight", Cfg::windowed(f, g, n, 3))] {
            let m = M::new(f, cfg);
            let mut b = Builder::new();
            let x = b.alloc_qubits(n + 1);
            let fl = b.alloc_qubit();
            let base = b.active_qubits();
            let (_, pk) = b.r3_peak(|b| park_fold(b, f, cfg, &x, fl, cfg.room));
            let ops_f = b.take_ops();
            let (_, pk2) = b.r3_peak(|b| park_unfold(b, f, cfg, &x, fl, cfg.room));
            let ops_i = b.take_ops();
            let (nq, nb) = b.i13_dims();
            let keep = keep_set(&[&x, &[fl]]);
            let mut ins = Vec::new();
            for v in 0..(1u64 << (n + 1)) {
                ins.push((U512::from(v), false));
                if v & 1 == 0 {
                    ins.push((U512::from(v), true));
                }
            }
            let mut rd = xof(&format!("park-{n}-{name}"));
            let mut sim = Simulator::new(nq, nb + 1, &mut rd);
            let mut fails = 0;
            for batch in ins.chunks(64) {
                sim.clear_for_shot();
                for (j, &(v, fv)) in batch.iter().enumerate() {
                    set(&mut sim, &x, v, j);
                    set(&mut sim, &[fl], if fv { one() } else { U512::ZERO }, j);
                }
                sim.apply_iter(ops_f.iter());
                let g1 = garbage(&sim, nq, &keep);
                let ph1 = sim.phase;
                let mut mid = Vec::new();
                for (j, &(v, fv)) in batch.iter().enumerate() {
                    let want = m.park_fold(v, fv);
                    let got = get(&sim, &x, j);
                    mid.push(got);
                    if got != want || (g1 >> j) & 1 == 1 || (ph1 >> j) & 1 == 1 || m.park_unfold(want, fv) != v {
                        fails += 1;
                    }
                }
                sim.apply_iter(ops_i.iter());
                let g2 = garbage(&sim, nq, &keep);
                for (j, &(v, _)) in batch.iter().enumerate() {
                    if get(&sim, &x, j) != v || (g2 >> j) & 1 == 1 || (sim.phase >> j) & 1 == 1 {
                        fails += 1;
                    }
                }
            }
            let line = format!("park-fold n={n} {name} w={} inputs={} fails={fails} T_fold={} T_unfold={} scratch={}/{}",
                cfg.fold_w, ins.len(), expected_t(&ops_f), expected_t(&ops_i), pk - base, pk2 - base);
            eprintln!("{line}");
            log.push_str(&line);
            log.push('\n');
            assert_eq!(fails, 0);
        }
    }
    for ob in [1usize, 2, 3, 7, 8] {
        let mut b = Builder::new();
        let odo = b.alloc_qubits(ob);
        let ctl = b.alloc_qubit();
        let tg = b.alloc_qubit();
        let room = ob + 2;
        odo_inc(&mut b, &odo, ctl, room);
        let ops1 = b.take_ops();
        odo_nonzero_xor(&mut b, &odo, tg, room);
        let ops2 = b.take_ops();
        odo_nonzero_xor(&mut b, &odo, tg, room);
        odo_dec(&mut b, &odo, ctl, room);
        let ops3 = b.take_ops();
        let (nq, nb) = b.i13_dims();
        let keep = keep_set(&[&odo, &[ctl, tg]]);
        let mut rd = xof(&format!("odo-{ob}"));
        let mut sim = Simulator::new(nq, nb + 1, &mut rd);
        let mut fails = 0;
        let ins: Vec<(u64, bool)> = (0..(1u64 << ob)).flat_map(|v| [(v, false), (v, true)]).collect();
        for batch in ins.chunks(64) {
            sim.clear_for_shot();
            for (j, &(v, cv)) in batch.iter().enumerate() {
                set(&mut sim, &odo, U512::from(v), j);
                set(&mut sim, &[ctl], if cv { one() } else { U512::ZERO }, j);
            }
            sim.apply_iter(ops1.iter());
            sim.apply_iter(ops2.iter());
            for (j, &(v, cv)) in batch.iter().enumerate() {
                let inc = (v + cv as u64) & ((1u64 << ob) - 1);
                if get(&sim, &odo, j) != U512::from(inc) || get(&sim, &[tg], j) != U512::from((inc != 0) as u64) {
                    fails += 1;
                }
            }
            let g = garbage(&sim, nq, &keep);
            sim.apply_iter(ops3.iter());
            let g2 = garbage(&sim, nq, &keep);
            for (j, &(v, _)) in batch.iter().enumerate() {
                if get(&sim, &odo, j) != U512::from(v) || get(&sim, &[tg], j) != U512::ZERO
                    || ((g | g2 | sim.phase) >> j) & 1 == 1 {
                    fails += 1;
                }
            }
        }
        let line = format!("odometer ob={ob} cases={} fails={fails} T_inc={} T_nonzero={} T_dec={}",
            ins.len(), expected_t(&ops1), expected_t(&ops2), expected_t(&ops3) - expected_t(&ops2));
        eprintln!("{line}");
        log.push_str(&line);
        log.push('\n');
        assert_eq!(fails, 0);
    }
    park_walk(log);
}

/// Full-width post-park walk: R ticks from t0 = R - 128; per shot a random park index k in
/// [t0, R) and s0 < 2^(n - (k - t0)). Forward tick t: relabel-double (unconditional), F = [k <= t]
/// (stand-in for the rails' zero test), odo_inc(F), park_fold(F), uncompute F. Reverse tick t:
/// F, odo_dec(F), P = [odo != 0] checked against [t > k] (the decoder's post-park bit),
/// park_unfold(F), relabel back, uncompute F.
fn park_walk(log: &mut String) {
    let f = Field::secp();
    let rr: usize = std::env::var("SKYCOF_MM_R").ok().and_then(|s| s.parse().ok()).unwrap_or(404);
    let span = 128usize;
    let t0 = rr - span;
    let ob = 7usize;
    let kb = 9usize; // park index register (stand-in), values < 512
    for (name, cfg) in [("tree", Cfg::windowed(f, 25, 24, 99)), ("exact", Cfg::exact(f, 99))] {
        let m = M::new(f, cfg);
        let mut b = Builder::new();
        let kreg = b.alloc_qubits(kb);
        let odo = b.alloc_qubits(ob);
        let mut s = b.alloc_qubits(f.n);
        let s_in = s.clone();
        let base = b.active_qubits();
        let mut tpark = 0.0f64;
        let mut tick_peak = 0u32;
        let kconst = |t: usize| const_ad(t as u128, kb, None);
        let mut ops_f: Vec<Op> = Vec::new();
        for t in t0..rr {
            // walk relabel: X = [fresh, s]
            let zq = b.alloc_qubit();
            let mut x = vec![zq];
            x.extend_from_slice(&s);
            let fl = b.alloc_qubit();
            lt(&mut b, &kreg, &kconst(t + 1), None, Act::Xor(fl, None), 20);
            ops_f.extend(b.take_ops());
            let (_, pk) = b.r3_peak(|b| {
                odo_inc(b, &odo, fl, cfg.room);
                park_fold(b, f, cfg, &x, fl, cfg.room);
            });
            tick_peak = tick_peak.max(pk - base);
            let seg = b.take_ops();
            tpark += expected_t(&seg);
            ops_f.extend(seg);
            lt(&mut b, &kreg, &kconst(t + 1), None, Act::Xor(fl, None), 20);
            b.release_clean(fl);
            let top = x[f.n];
            b.release_clean(top);
            s = x[..f.n].to_vec();
        }
        ops_f.extend(b.take_ops());
        let s_mid = s.clone();
        let mut checks = Vec::new();
        let mut trev = 0.0f64;
        let mut ops_i: Vec<Op> = Vec::new();
        for t in (t0..rr).rev() {
            let fl = b.alloc_qubit();
            lt(&mut b, &kreg, &kconst(t + 1), None, Act::Xor(fl, None), 20);
            ops_i.extend(b.take_ops());
            odo_dec(&mut b, &odo, fl, cfg.room);
            let pq = b.alloc_qubit();
            odo_nonzero_xor(&mut b, &odo, pq, cfg.room);
            let seg = b.take_ops();
            trev += expected_t(&seg);
            ops_i.extend(seg);
            // checker: pq ^= [k < t] (= [t > k]); must leave pq == 0
            lt(&mut b, &kreg, &kconst(t), None, Act::Xor(pq, None), 20);
            checks.push(pq);
            let topq = b.alloc_qubit();
            let mut x = s.clone();
            x.push(topq);
            ops_i.extend(b.take_ops());
            park_unfold(&mut b, f, cfg, &x, fl, cfg.room);
            let seg = b.take_ops();
            trev += expected_t(&seg);
            ops_i.extend(seg);
            lt(&mut b, &kreg, &kconst(t + 1), None, Act::Xor(fl, None), 20);
            b.release_clean(fl);
            b.release_clean(x[0]);
            s = x[1..].to_vec();
        }
        ops_i.extend(b.take_ops());
        let (nq, nb) = b.i13_dims();
        let s_out = s.clone();
        let keep_f = keep_set(&[&kreg, &odo, &s_mid]);
        let keep_i = keep_set(&[&kreg, &odo, &s_out, &checks]);
        let mut rng = Rng(4242);
        let shots = 64 * 16;
        let mut fails = 0;
        let mut rd = xof(&format!("parkwalk-{name}"));
        let mut sim = Simulator::new(nq, nb + 1, &mut rd);
        for _ in 0..shots / 64 {
            sim.clear_for_shot();
            let mut cases = Vec::new();
            for j in 0..64 {
                let k = t0 + 1 + (rng.next() as usize % (span - 1)); // R - k <= 127 = odometer capacity
                let s0 = rng.bits(f.n - (k - t0));
                set(&mut sim, &kreg, U512::from(k as u64), j);
                set(&mut sim, &s_in, s0, j);
                cases.push((k, s0));
            }
            sim.apply_iter(ops_f.iter());
            let g1 = garbage(&sim, nq, &keep_f);
            for (j, &(k, s0)) in cases.iter().enumerate() {
                let mut v = s0;
                for t in t0..rr {
                    v <<= 1;
                    v = m.park_fold(v, t >= k);
                }
                let truth = s0.mul_mod(U512::from(2u64).pow_mod(U512::from((rr - t0) as u64), m.p()), m.p());
                let ok = get(&sim, &s_mid, j) == v && get(&sim, &odo, j) == U512::from((rr - k) as u64)
                    && v.reduce_mod(m.p()) == truth && (g1 >> j) & 1 == 0 && (sim.phase >> j) & 1 == 0;
                if !ok {
                    fails += 1;
                    if fails <= 4 {
                        eprintln!("  WALK FAIL k={k} s0={s0:#x}: value {} odo {} residue {} garbage {} phase {}",
                            get(&sim, &s_mid, j) == v, get(&sim, &odo, j) == U512::from((rr - k) as u64),
                            v.reduce_mod(m.p()) == truth, (g1 >> j) & 1, (sim.phase >> j) & 1);
                    }
                }
            }
            sim.apply_iter(ops_i.iter());
            let g2 = garbage(&sim, nq, &keep_i);
            for (j, &(_, s0)) in cases.iter().enumerate() {
                let chk_ok = checks.iter().all(|&q| (sim.qubit(q) >> j) & 1 == 0);
                if get(&sim, &s_out, j) != s0 || !get(&sim, &odo, j).is_zero() || !chk_ok || (g2 >> j) & 1 == 1
                    || (sim.phase >> j) & 1 == 1 {
                    fails += 1;
                }
            }
        }
        let line = format!("park-walk {name} R={rr} ticks {t0}..{rr} shots={shots} fails={fails} T_fwd_tick(fold+odo)={:.1} T_rev_tick(unfold+odo+P)={:.1} tick_scratch={}",
            tpark / span as f64, trev / span as f64, tick_peak);
        eprintln!("{line}");
        log.push_str(&line);
        log.push('\n');
        assert_eq!(fails, 0);
    }
}

// ─── full width ─────────────────────────────────────────────────────────────────────────────

fn modes(f: Field, room: usize) -> Vec<(&'static str, Cfg)> {
    vec![
        ("tree-G25-W24", Cfg::windowed(f, 25, 24, room)),
        ("model-G30-W32", Cfg::windowed(f, 30, 32, room)),
        ("exactcmp-G25", Cfg { fold_w: 33 + 25, cmp_w: 256, room }),
        ("exact", Cfg::exact(f, room)),
    ]
}

fn rooms() -> Vec<usize> {
    std::env::var("SKYCOF_MM_ROOMS").ok().map(|s| s.split(',').filter_map(|x| x.trim().parse().ok()).collect())
        .unwrap_or_else(|| vec![600, 293, 200, 150, 110, 99, 88, 60, 40, 30])
}

fn part_full(log: &mut String, tsv: &mut String) {
    eprintln!("== full width: random canonical inputs, every mode and room ==");
    let f = Field::secp();
    let rr: usize = std::env::var("SKYCOF_MM_R").ok().and_then(|s| s.parse().ok()).unwrap_or(404);
    let p = M::new(f, Cfg::exact(f, 1)).p();
    let batches: usize = std::env::var("SKYCOF_MM_FULL_BATCHES").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let inputs = random_inputs(f.n, p, 64 * batches, true, true, 9001);
    let _ = writeln!(tsv, "mode\tfold_w\tcmp_w\troom\tk\tneg\tT_fwd_expected\tT_inv_expected\tT_fwd_native\tT_fwd_exec_avg\tT_inv_exec_avg\tscratch_fwd\tscratch_inv\tshots\tresidue_mismatch\tnoncanonical");
    for room in rooms() {
        for (name, cfg) in modes(f, room) {
            if cfg.cmp_w + 1 > room && room < 30 {
                continue;
            }
            for (k, neg) in [(0usize, false), (rr, true)] {
                let (st, bd) = mm_case(f, cfg, k, neg, &inputs, &format!("full-{name}"), log);
                let fb = st.full_batches.max(1) as f64;
                let _ = writeln!(tsv, "{name}\t{}\t{}\t{room}\t{k}\t{neg}\t{:.1}\t{:.1}\t{}\t{:.1}\t{:.1}\t{}\t{}\t{}\t{}\t{}",
                    cfg.fold_w, cfg.cmp_w, bd.tf, bd.ti, bd.tf_native, st.exec_tf / fb, st.exec_ti / fb, bd.scratch_f, bd.scratch_i,
                    st.shots, st.residue_mismatch, st.noncanonical_out);
                assert_eq!(st.residue_mismatch, 0, "full width residue mismatch");
                assert_eq!(st.noncanonical_out, 0, "full width non-canonical output");
            }
        }
    }
}

/// Per-piece costs at full width (expected Toffoli, scratch).
fn part_measure(log: &mut String) {
    eprintln!("== pieces at n = 256 ==");
    let f = Field::secp();
    for room in [600usize, 293, 99, 60, 30] {
        for (name, cfg) in modes(f, room) {
            let mut b = Builder::new();
            let a = b.alloc_qubits(f.n);
            let mut out = b.alloc_qubits(f.n);
            let e = b.alloc_qubit();
            let base = b.active_qubits();
            let mut row = format!("piece {name} room={room}");
            let mut meas = |b: &mut Builder, label: &str, body: &mut dyn FnMut(&mut Builder)| {
                b.take_ops();
                let (_, pk) = b.r3_peak(|b| body(b));
                let ops = b.take_ops();
                let _ = write!(row, " {label}={:.1}/{}", expected_t(&ops), pk - base);
            };
            meas(&mut b, "madd", &mut |b| madd(b, f, cfg, &out, &a, e, room));
            meas(&mut b, "msub", &mut |b| msub(b, f, cfg, &out, &a, e, room));
            meas(&mut b, "dbl", &mut |b| dbl(b, f, cfg, &mut out, room));
            meas(&mut b, "hlv", &mut |b| hlv(b, f, cfg, &mut out, room));
            meas(&mut b, "cneg", &mut |b| cneg(b, f, cfg, &out, e, room));
            let row2 = row.clone();
            eprintln!("{row2}");
            log.push_str(&row2);
            log.push('\n');
        }
    }
}

/// Model-only error rates at n = 256 with shrunken windows (the rates scale as 2^-G and 2^-W):
/// per call, P(output residue wrong), P(forward erase event) (a phase error with probability 1/2),
/// P(inverse event) on a correct forward value (garbage, reset to a phase error w.p. 1/2).
fn part_rates(log: &mut String) {
    eprintln!("== error rates (model, n = 256, shrunken windows) ==");
    let f = Field::secp();
    let rr: usize = std::env::var("SKYCOF_MM_R").ok().and_then(|s| s.parse().ok()).unwrap_or(404);
    let nsamp: usize = std::env::var("SKYCOF_MM_RATE_N").ok().and_then(|s| s.parse().ok()).unwrap_or(20000);
    let pts: Vec<(usize, usize)> = vec![(6, 256), (9, 256), (256, 6), (256, 9)];
    for (g, ww) in pts {
        let cfg = Cfg { fold_w: (33 + g).min(256), cmp_w: ww, room: 999 };
        let m = M::new(f, cfg);
        for (k, neg) in [(0usize, false), (rr, true)] {
            let res = Mutex::new((0u64, 0u64, 0u64));
            let nth = threads();
            std::thread::scope(|sc| {
                for th in 0..nth {
                    let (res, m) = (&res, &m);
                    sc.spawn(move || {
                        let mut r = Rng(1000 + th as u64);
                        let p = m.p();
                        let (mut bad, mut evf, mut evi) = (0u64, 0u64, 0u64);
                        for _ in (th..nsamp).step_by(nth) {
                            let (a, b) = (r.below(p, 256), r.below(p, 256));
                            let s = neg && r.next() & 1 == 1;
                            let (o, e) = m.mul_fwd(a, b, k, s);
                            if o.reduce_mod(p) != m.truth(a, b, k, s) { bad += 1; }
                            evf += (e > 0) as u64;
                            let (_, ei) = m.mul_inv(a, b, k, s, o);
                            evi += (ei > 0) as u64;
                        }
                        let mut g = res.lock().unwrap();
                        g.0 += bad; g.1 += evf; g.2 += evi;
                    });
                }
            });
            let (bad, evf, evi) = res.into_inner().unwrap();
            let nn = nsamp as f64;
            let line = format!("rate G={} W={ww} k={k}: P(value wrong)={:.3e} P(fwd erase event)={:.3e} P(inv event)={:.3e}  [n={nsamp}]",
                if g >= 223 { "exact".to_string() } else { g.to_string() }, bad as f64 / nn, evf as f64 / nn, evi as f64 / nn);
            eprintln!("{line}");
            log.push_str(&line);
            log.push_str("\n");
        }
    }
}

pub fn run() {
    let parts = std::env::var("SKYCOF_MM_PARTS").unwrap_or_else(|_| "small,park,full,measure,rates".into());
    let out_path = std::env::var("SKYCOF_MM_OUT").unwrap_or_else(|_| "skycof_mm_measure.tsv".into());
    let mut log = String::new();
    let mut tsv = String::new();
    let t0 = std::time::Instant::now();
    for part in parts.split(',') {
        match part.trim() {
            "small" => part_small(&mut log),
            "park" => part_park(&mut log),
            "full" => part_full(&mut log, &mut tsv),
            "measure" => part_measure(&mut log),
            "rates" => part_rates(&mut log),
            "" => {}
            other => panic!("unknown part {other}"),
        }
    }
    std::fs::write(&out_path, &tsv).ok();
    std::fs::write(format!("{out_path}.log"), &log).ok();
    eprintln!("SKYCOF_MM_SELFTEST PASS ({:.1}s)", t0.elapsed().as_secs_f64());
}
