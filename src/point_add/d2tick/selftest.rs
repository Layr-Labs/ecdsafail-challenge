//! Gate-level selftests of the D2 tick: `D2_TICK_SELFTEST=1 build_circuit` (read before the build clears the
//! environment; the default build never reaches this file).
//!
//! Every case builds the tick with the real [`Builder`], runs the op stream on the harness [`Simulator`]
//! (64 shots per pass) and checks, on every shot: the post-state against the classical walk model (rails,
//! signs, typ wires, stacks, count register, `s` clean), zero phase, every scratch wire zero; then the
//! reverse tick restores the input exactly, again with zero phase and zero scratch.
//!
//! 1. parity: the exhaustive runs of `jl-probe/out/d2tick_runs.txt` (same lanes, same Esw/Ead, same T).
//! 2. sweep: exhaustive over all value pairs (|v| < 2^vb) x every N in the window x 2 random stack/typ
//!    fillings, for every t in 0..=11 at A in {10, 12, 14, 16}.
//! 3. chain: whole walks of consecutive ticks (alternating relabel, typ wires chained through the freed LSB
//!    wires, stacks growing downward) forward then reverse.
//! 4. full: A = 288 at the design's per-tick windows (`win_A288.txt`, margin 0), random lanes.
//!
//! `D2_TICK_COST=<win file>`: per-tick Toffoli and scratch of the planned tick at every window of the file
//! (all margins), summed per traversal.

use super::*;
use crate::circuit::{Op, OperationType};
use crate::sim::Simulator;
use ruint::aliases::U512;
use sha3::{
    digest::{ExtendableOutput, Update},
    Shake256,
};

// ─── signed values (two's complement mod 2^512) ──────────────────────────────────────────

type V = U512;

fn neg(v: V) -> bool {
    v.bit(511)
}
fn nrm(v: V) -> V {
    if neg(v) {
        !v
    } else {
        v
    }
}
fn blen(v: V) -> usize {
    nrm(v).bit_len()
}
fn asr1(v: V) -> V {
    let mut r = v >> 1usize;
    if neg(v) {
        r.set_bit(511, true);
    }
    r
}
fn absv(v: V) -> V {
    if neg(v) {
        v.wrapping_neg()
    } else {
        v
    }
}
fn from_i64(x: i64) -> V {
    if x < 0 {
        V::from((-x) as u64).wrapping_neg()
    } else {
        V::from(x as u64)
    }
}

/// One D2 walk tick (`walk_tick` of d2tick.py). Returns (V', c, s).
fn walk_tick(v: [V; 2], xa: usize) -> ([V; 2], bool, bool) {
    let ya = 1 - xa;
    let mut v = v;
    let c = v[xa].bit(0);
    if c {
        v.swap(0, 1);
    }
    let h = asr1(v[xa]);
    let o = v[ya];
    let ag = neg(h) == neg(o);
    let op = if ag { o.wrapping_sub(h) } else { o.wrapping_add(h) };
    let s = ag ^ (neg(h) == neg(op));
    v[xa] = h;
    v[ya] = op;
    (v, c, s)
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
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    fn bits(&mut self, w: usize) -> V {
        let mut v = V::from_limbs([self.next(), self.next(), self.next(), self.next(), self.next(), 0, 0, 0]);
        if w < 512 {
            v &= (V::from(1u64) << w) - V::from(1u64);
        }
        v
    }
}

// ─── one-tick lanes ───────────────────────────────────────────────────────────────────────

#[derive(Clone)]
struct Lane {
    v: [V; 2],
    n: usize,
    c: bool,
    s: bool,
    typ: bool,
    vn: [V; 2],
    wad: usize,
    stack: [V; 2],
    typs: [V; 2],
}

/// The d2tick.py lane filter: Some(lane) iff (v, N) is a valid pre-state of tick t at array width a.
fn lane_of(a: usize, t: usize, v: [V; 2], n: usize) -> Option<Lane> {
    let xa = t % 2;
    let o = [t.div_ceil(2), t / 2];
    if (v[0].bit(0) as u8 + v[1].bit(0) as u8) != 1 {
        return None;
    }
    let sv = [n.div_ceil(2), n / 2];
    if (0..2).any(|k| o[k] + blen(v[k]) + sv[k] > a) {
        return None;
    }
    let (vn, c, s) = walk_tick(v, xa);
    let ya = 1 - xa;
    if c && o[0] + blen(v[0]).max(blen(v[1])) + sv[0] > a {
        return None;
    }
    // H, O as in the tick (after the exchange)
    let (h, oo) = {
        let mut w = v;
        if c {
            w.swap(0, 1);
        }
        (asr1(w[xa]), w[ya])
    };
    let hneg = neg(h);
    let r = nrm(oo).wrapping_sub(nrm(h)).wrapping_sub(V::from(hneg as u64));
    let wad = nrm(h).bit_len().max(nrm(oo).bit_len()).max(blen(r) + 1);
    if o[0] + sv[0] + 1 + wad > a {
        return None;
    }
    let typ = absv(vn[xa]) < absv(vn[ya]);
    if typ && s {
        return None;
    }
    let nn = n + (!typ) as usize;
    let sn = [nn.div_ceil(2), nn / 2];
    let on = [o[0] + (xa == 0) as usize, o[1] + (xa == 1) as usize];
    if (0..2).any(|k| on[k] + blen(vn[k]) + sn[k] > a) {
        return None;
    }
    Some(Lane { v, n, c, s, typ, vn, wad, stack: [V::ZERO; 2], typs: [V::ZERO; 2] })
}

fn esw_ead(lanes: &[Lane]) -> (usize, usize) {
    let esw = lanes.iter().filter(|l| l.c).map(|l| blen(l.v[0]).max(blen(l.v[1]))).max().unwrap_or(1);
    let ead = lanes.iter().map(|l| l.wad).max().unwrap();
    (esw, ead)
}

// ─── simulation harness ───────────────────────────────────────────────────────────────────

struct Built {
    regs: D2Regs,
    n_io: usize,
    nq: usize,
    nb: usize,
    fwd: Vec<Op>,
    rev: Vec<Op>,
    t_fwd: usize,
    t_rev: usize,
    scratch_plan: usize,
    scratch_meas: usize,
}

fn alloc_regs(b: &mut Builder, a: usize, kb: usize) -> D2Regs {
    let p0 = b.alloc_qubits(a);
    let p1 = b.alloc_qubits(a);
    let sig = [b.alloc_qubit(), b.alloc_qubit()];
    let n = b.alloc_qubits(kb);
    let s = b.alloc_qubit();
    let typ0 = b.alloc_qubit();
    D2Regs { p: [p0, p1], sig, n, s, typ0: Some(typ0) }
}

fn count_t(ops: &[Op]) -> usize {
    ops.iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count()
}

/// Build forward ticks `wins` in order, then the reverse ticks in reverse order.
fn build_chain(a: usize, kb: usize, wins: &[D2Win], mode: D2Mode) -> Built {
    let mut b = Builder::new();
    let regs = alloc_regs(&mut b, a, kb);
    let n_io = b.active_qubits() as usize;
    let plans: Vec<D2Plan> = wins.iter().map(|w| plan(w, mode)).collect();
    for pl in &plans {
        emit(&mut b, pl, &regs, Dir::Forward);
    }
    let fwd = b.take_ops();
    assert_eq!(b.active_qubits() as usize, n_io, "forward left scratch allocated");
    for pl in plans.iter().rev() {
        emit(&mut b, pl, &regs, Dir::Reverse);
    }
    let rev = b.take_ops();
    assert_eq!(b.active_qubits() as usize, n_io, "reverse left scratch allocated");
    let (nq, nb) = b.i13_dims();
    let scratch_meas = b.peak_total() as usize - n_io;
    let t_fwd = count_t(&fwd);
    let t_rev = count_t(&rev);
    assert_eq!(t_fwd, plans.iter().map(|p| p.t_fwd).sum::<usize>(), "plan forward T disagrees with the op stream");
    assert_eq!(t_rev, plans.iter().map(|p| p.t_rev).sum::<usize>(), "plan reverse T disagrees with the op stream");
    let scratch_plan = plans.iter().map(|p| p.scratch).max().unwrap_or(0);
    Built { regs, n_io, nq, nb: nb + 1, fwd, rev, t_fwd, t_rev, scratch_plan, scratch_meas }
}

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = Shake256::default();
    h.update(b"d2-tick-selftest-v1");
    h.update(tag);
    h.finalize_xof()
}

/// Expected wire values of one shot, keyed by qubit id.
type State = Vec<(QubitId, bool)>;

fn set_state(sim: &mut Simulator<'_, sha3::Shake256Reader>, st: &State, shot: usize) {
    for &(q, v) in st {
        let w = sim.qubit_mut(q);
        if v {
            *w |= 1u64 << shot;
        } else {
            *w &= !(1u64 << shot);
        }
    }
}

/// Run `cases` = (pre-state, post-state) through forward then reverse; returns the number of failing shots
/// (first few printed).
fn run_cases(bt: &Built, cases: &[(State, State)], label: &str) -> usize {
    let mut rng = xof(label.as_bytes());
    let mut sim = Simulator::new(bt.nq, bt.nb, &mut rng);
    let mut bad = 0usize;
    let mut shown = 0;
    for chunk_start in (0..cases.len()).step_by(64) {
        let chunk: Vec<&(State, State)> =
            (0..64).map(|j| &cases[(chunk_start + j).min(cases.len() - 1)]).collect();
        let valid = (cases.len() - chunk_start).min(64);
        sim.clear_for_shot();
        for (j, (pre, _)) in chunk.iter().enumerate() {
            set_state(&mut sim, pre, j);
        }
        sim.apply_iter(bt.fwd.iter());
        let mut lane_bad = 0u64;
        lane_bad |= sim.phase;
        for q in bt.n_io..bt.nq {
            lane_bad |= sim.qubit(QubitId(q as u64));
        }
        for (j, (_, post)) in chunk.iter().enumerate() {
            for &(q, v) in post {
                if ((sim.qubit(q) >> j) & 1 == 1) != v {
                    if shown < 6 && (lane_bad >> j) & 1 == 0 {
                        eprintln!("  {label}: case {} wire {} expected {} after forward", chunk_start + j, q.0, v as u8);
                        shown += 1;
                    }
                    lane_bad |= 1 << j;
                }
            }
        }
        sim.apply_iter(bt.rev.iter());
        lane_bad |= sim.phase;
        for q in bt.n_io..bt.nq {
            lane_bad |= sim.qubit(QubitId(q as u64));
        }
        for (j, (pre, _)) in chunk.iter().enumerate() {
            for &(q, v) in pre {
                if ((sim.qubit(q) >> j) & 1 == 1) != v {
                    if shown < 6 && (lane_bad >> j) & 1 == 0 {
                        eprintln!("  {label}: case {} wire {} not restored by the reverse", chunk_start + j, q.0);
                        shown += 1;
                    }
                    lane_bad |= 1 << j;
                }
            }
        }
        let mask = if valid == 64 { u64::MAX } else { (1u64 << valid) - 1 };
        bad += (lane_bad & mask).count_ones() as usize;
    }
    bad
}

/// Pre/post states of one single-tick lane (d2tick.py's init and check, wire for wire).
fn lane_states(regs: &D2Regs, a: usize, kb: usize, t: usize, l: &Lane) -> (State, State) {
    let xa = t % 2;
    let ya = 1 - xa;
    let o = [t.div_ceil(2), t / 2];
    let sv = [l.n.div_ceil(2), l.n / 2];
    let tp = l.typ ^ l.c ^ (t > 0);
    let mut pre = State::new();
    let mut post = State::new();
    let nn = l.n + (!l.typ) as usize;
    let sn = [nn.div_ceil(2), nn / 2];
    let on = [o[0] + (xa == 0) as usize, o[1] + (xa == 1) as usize];
    for k in 0..2 {
        for i in 0..a {
            let mut x = if i < o[k] {
                l.typs[k].bit(i)
            } else if i >= a - sv[k] {
                l.stack[k].bit(i)
            } else {
                nrm(l.v[k]).bit(i - o[k])
            };
            if t >= 1 && k == ya && i == o[ya] - 1 {
                x = tp;
            }
            pre.push((regs.p[k][i], x));
            let mut e = if i < o[k] {
                l.typs[k].bit(i)
            } else if k == xa && i == o[xa] {
                l.typ
            } else if i >= a - sn[k] {
                if i >= a - sv[k] {
                    l.stack[k].bit(i)
                } else {
                    l.s
                }
            } else {
                nrm(l.vn[k]).bit(i - on[k])
            };
            if t >= 1 && k == ya && i == o[ya] - 1 {
                e = tp;
            }
            post.push((regs.p[k][i], e));
        }
        pre.push((regs.sig[k], neg(l.v[k])));
        post.push((regs.sig[k], neg(l.vn[k])));
    }
    for j in 0..kb {
        pre.push((regs.n[j], ((l.n + 1) >> j) & 1 == 1));
        post.push((regs.n[j], ((nn + 1) >> j) & 1 == 1));
    }
    pre.push((regs.s, false));
    post.push((regs.s, false));
    let typ0 = regs.typ0.unwrap();
    let t0 = if t == 0 { tp } else { false };
    pre.push((typ0, t0));
    post.push((typ0, t0));
    (pre, post)
}

struct TickResult {
    mode: D2Mode,
    lanes: usize,
    bad: usize,
    win: D2Win,
    t_fwd: usize,
    t_rev: usize,
    scratch_plan: usize,
    scratch_meas: usize,
    by_tag: BTreeMap<Tag, usize>,
}

fn run_tick(win: D2Win, lanes: &[Lane], label: &str, mode: D2Mode) -> TickResult {
    let kb = win.kbits();
    let bt = build_chain(win.a, kb, &[win], mode);
    let cases: Vec<(State, State)> = lanes.iter().map(|l| lane_states(&bt.regs, win.a, kb, win.t, l)).collect();
    let bad = run_cases(&bt, &cases, label);
    TickResult {
        mode,
        lanes: lanes.len(),
        bad,
        win,
        t_fwd: bt.t_fwd,
        t_rev: bt.t_rev,
        scratch_plan: bt.scratch_plan,
        scratch_meas: bt.scratch_meas,
        by_tag: plan(&win, mode).by_tag,
    }
}

fn fill_random(lanes: &mut [Lane], a: usize, rng: &mut Rng) {
    for l in lanes.iter_mut() {
        l.stack = [rng.bits(a), rng.bits(a)];
        l.typs = [rng.bits(a), rng.bits(a)];
    }
}

/// Exhaustive lanes: every (v0, v1) in [-2^vb, 2^vb)^2 and every N in [nlo, nhi].
fn exhaustive_lanes(a: usize, t: usize, nlo: usize, nhi: usize, vb: usize) -> Vec<Lane> {
    let r = 1i64 << vb;
    let mut out = Vec::new();
    for v0 in -r..r {
        for v1 in -r..r {
            for n in nlo..=nhi {
                if let Some(l) = lane_of(a, t, [from_i64(v0), from_i64(v1)], n) {
                    out.push(l);
                }
            }
        }
    }
    out
}

fn tags(m: &BTreeMap<Tag, usize>) -> String {
    m.iter().map(|(k, v)| format!("{} {v}", k.name())).collect::<Vec<_>>().join(", ")
}

fn report(r: &TickResult, mode: &str) -> bool {
    let w = r.win;
    println!(
        "  {:?} A={} t={} N=[{},{}] Esw={} Ead={} lanes {} ({mode}): fwd T={} rev T={} scratch plan {} / builder {}  failing {}",
        r.mode, w.a, w.t, w.nlo, w.nhi, w.esw, w.ead, r.lanes, r.t_fwd, r.t_rev, r.scratch_plan, r.scratch_meas, r.bad
    );
    r.bad == 0 && r.t_fwd == r.t_rev && r.scratch_plan == r.scratch_meas
}

// ─── 1 + 2: exhaustive single ticks ───────────────────────────────────────────────────────

fn parity_runs() -> bool {
    // (A, t, Nlo, Nhi, vb, python lanes, Esw, Ead, python T)
    let runs: [(usize, usize, usize, usize, usize, usize, usize, usize, usize); 6] = [
        (12, 4, 3, 9, 4, 3456, 4, 5, 30),
        (14, 6, 4, 14, 5, 14752, 5, 6, 58),
        (14, 7, 4, 14, 5, 11232, 5, 6, 63),
        (16, 6, 6, 18, 5, 18848, 5, 6, 63),
        (16, 9, 4, 16, 5, 15328, 5, 6, 68),
        (16, 8, 8, 20, 5, 10746, 5, 6, 72),
    ];
    println!("D2_TICK_SELFTEST 1. parity with d2tick_runs.txt (exhaustive value pairs x all N)");
    let mut ok = true;
    let mut rng = Rng(11);
    for &(a, t, nlo, nhi, vb, py_lanes, py_esw, py_ead, py_t) in &runs {
        let mut lanes = exhaustive_lanes(a, t, nlo, nhi, vb);
        let (esw, ead) = esw_ead(&lanes);
        fill_random(&mut lanes, a, &mut rng);
        let win = D2Win { a, t, nlo, nhi, esw, ead };
        let r = run_tick(win, &lanes, &format!("parity-{a}-{t}"), D2Mode::Port);
        let good = report(&r, "exhaustive");
        let same = lanes.len() == py_lanes && esw == py_esw && ead == py_ead && r.t_fwd == py_t;
        println!(
            "    python: lanes {py_lanes} Esw={py_esw} Ead={py_ead} T={py_t} -> {}; by tag: {}",
            if same { "identical" } else { "MISMATCH" },
            tags(&r.by_tag)
        );
        ok &= good && same;
    }
    ok
}

fn sweep_runs() -> bool {
    println!("D2_TICK_SELFTEST 2. sweep (exhaustive value pairs x all N x 2 stack/typ fillings, every t)");
    let mut ok = true;
    let mut rng = Rng(22);
    let mut total = 0usize;
    for &(a, vb) in &[(10usize, 3usize), (12, 4), (14, 4), (16, 5)] {
        for t in 0..=11usize {
            let o0 = t.div_ceil(2);
            if a < o0 + 4 {
                continue;
            }
            let nhi_raw = 2 * a; // clamped below to what a valid shot can reach
            let base = D2Win { a, t, nlo: 0, nhi: nhi_raw, esw: 1, ead: 1 }.clamped();
            let mut lanes = exhaustive_lanes(a, t, base.nlo, base.nhi, vb);
            if lanes.is_empty() {
                continue;
            }
            let nmin = lanes.iter().map(|l| l.n).min().unwrap();
            let nmax = lanes.iter().map(|l| l.n).max().unwrap();
            let (esw, ead) = esw_ead(&lanes);
            let mut dup = lanes.clone();
            fill_random(&mut lanes, a, &mut rng);
            fill_random(&mut dup, a, &mut rng);
            lanes.extend(dup);
            let win = D2Win { a, t, nlo: nmin, nhi: nmax, esw, ead };
            for &mode in MODES {
                let r = run_tick(win, &lanes, &format!("sweep-{a}-{t}-{mode:?}"), mode);
                total += r.lanes;
                ok &= report(&r, "exhaustive");
            }
        }
    }
    println!("    sweep total {total} shots");
    ok
}

// ─── 3: chains of ticks ───────────────────────────────────────────────────────────────────

struct Walk {
    v: Vec<[V; 2]>, // v[t] = pre-state of tick t
    n: Vec<usize>,  // N before tick t
    c: Vec<bool>,
    s: Vec<bool>,
    typ: Vec<bool>,
    typ_m1: bool,
    stack: [V; 2],
    typs: [V; 2],
}

/// Why a start state was not kept for a chain.
#[derive(Debug, PartialEq, Eq)]
enum Reject {
    /// The lane filter failed at some tick (overflow of the arrays, an A letter with s = 1, ...).
    Filter,
    /// A rail reached 0 before the last tick (parked: the post-park ticks are not D2 ticks).
    Parked,
    /// Unparked, filter fine, but typ_t != c_t ^ typ_{t-1} ^ 1 at some tick.
    Typ,
}

/// Walk `ticks` ticks from `v`.
fn walk_chain(a: usize, ticks: usize, v: [V; 2]) -> Result<Walk, Reject> {
    let mut w = Walk { v: vec![v], n: vec![0], c: vec![], s: vec![], typ: vec![], typ_m1: false, stack: [V::ZERO; 2], typs: [V::ZERO; 2] };
    for t in 0..ticks {
        if w.v[t][0].is_zero() || w.v[t][1].is_zero() {
            return Err(Reject::Parked);
        }
        let l = lane_of(a, t, w.v[t], w.n[t]).ok_or(Reject::Filter)?;
        if t == 0 {
            w.typ_m1 = l.typ ^ l.c;
        } else if l.typ != l.c ^ w.typ[t - 1] ^ true {
            return Err(Reject::Typ); // the circuit's typ recurrence would disagree
        }
        w.c.push(l.c);
        w.s.push(l.s);
        w.typ.push(l.typ);
        w.v.push(l.vn);
        w.n.push(w.n[t] + (!l.typ) as usize);
    }
    Ok(w)
}

/// Wire values of a walk after `tt` ticks (tt = 0: the initial state).
fn walk_state(regs: &D2Regs, a: usize, kb: usize, w: &Walk, tt: usize) -> State {
    let mut st = State::new();
    let o = [tt.div_ceil(2), tt / 2];
    let n = w.n[tt];
    let sv = [n.div_ceil(2), n / 2];
    let mut wires: [Vec<bool>; 2] = [vec![false; a], vec![false; a]];
    for k in 0..2 {
        for i in 0..a {
            wires[k][i] = if i < o[k] {
                w.typs[k].bit(i)
            } else if i >= a - sv[k] {
                w.stack[k].bit(i)
            } else {
                nrm(w.v[tt][k]).bit(i - o[k])
            };
        }
    }
    // typ wires of ticks < tt: tick t' froze its typ at array t' % 2, position o_{t'%2}(t')
    for t in 0..tt {
        let x = t % 2;
        let ox = [t.div_ceil(2), t / 2][x];
        wires[x][ox] = w.typ[t];
    }
    // stacked s bits: the j-th push lands at P[j & 1][a - (j >> 1) - 1]
    let mut j = 0usize;
    for t in 0..tt {
        if !w.typ[t] {
            wires[j & 1][a - (j >> 1) - 1] = w.s[t];
            j += 1;
        }
    }
    assert_eq!(j, n);
    for k in 0..2 {
        for i in 0..a {
            st.push((regs.p[k][i], wires[k][i]));
        }
        st.push((regs.sig[k], neg(w.v[tt][k])));
    }
    for jb in 0..kb {
        st.push((regs.n[jb], ((n + 1) >> jb) & 1 == 1));
    }
    st.push((regs.s, false));
    st.push((regs.typ0.unwrap(), w.typ_m1));
    st
}

fn chain_runs() -> bool {
    println!("D2_TICK_SELFTEST 3. chains (consecutive ticks forward, then all reverse)");
    let mut ok = true;
    let mut rng = Rng(33);
    for &(a, ticks, w0, want) in &[(16usize, 6usize, 8usize, 2048usize), (24, 10, 12, 2048), (40, 20, 22, 2048), (64, 40, 40, 2048), (288, 300, 255, 512)] {
        let mut walks = Vec::new();
        let mut tried = 0usize;
        let (mut rejected_typ, mut parked, mut filtered) = (0usize, 0usize, 0usize);
        while walks.len() < want && tried < 400 * want {
            tried += 1;
            let wa = w0 - rng.below(4) as usize;
            let wb = w0 - rng.below(4) as usize;
            let mut v = [rng.bits(wa), rng.bits(wb)];
            for x in v.iter_mut() {
                if rng.next() & 1 == 1 {
                    *x = !*x;
                }
            }
            let odd = (rng.next() & 1) as usize;
            v[odd].set_bit(0, true);
            v[1 - odd].set_bit(0, false);
            match walk_chain(a, ticks, v) {
                Ok(mut w) => {
                    w.stack = [rng.bits(a), rng.bits(a)];
                    w.typs = [rng.bits(a), rng.bits(a)];
                    walks.push(w);
                }
                Err(Reject::Typ) => rejected_typ += 1,
                Err(Reject::Parked) => parked += 1,
                Err(Reject::Filter) => filtered += 1,
            }
        }
        if walks.is_empty() {
            println!("  A={a}: no walk of {ticks} ticks fits");
            ok = false;
            continue;
        }
        // per-tick windows from the kept walks
        let mut wins = Vec::new();
        for t in 0..ticks {
            let mut lanes = Vec::new();
            for w in &walks {
                lanes.push(lane_of(a, t, w.v[t], w.n[t]).unwrap());
            }
            let (esw, ead) = esw_ead(&lanes);
            let nlo = lanes.iter().map(|l| l.n).min().unwrap();
            let nhi = lanes.iter().map(|l| l.n).max().unwrap();
            wins.push(D2Win { a, t, nlo, nhi, esw, ead });
        }
        let kb = wins.iter().map(|w| w.kbits()).max().unwrap();
        for &mode in MODES {
        let bt = build_chain(a, kb, &wins, mode);
        let cases: Vec<(State, State)> =
            walks.iter().map(|w| (walk_state(&bt.regs, a, kb, w, 0), walk_state(&bt.regs, a, kb, w, ticks))).collect();
        let bad = run_cases(&bt, &cases, &format!("chain-{a}-{mode:?}"));
        println!(
            "  {mode:?} A={a} ticks 0..{ticks}: {} walks kept (starts not kept: {parked} parked early, {filtered} outside the arrays, {rejected_typ} typ-recurrence violations), fwd T={} rev T={} scratch peak plan {} / builder {}  failing {bad}",
            walks.len(), bt.t_fwd, bt.t_rev, bt.scratch_plan, bt.scratch_meas
        );
        ok &= bad == 0 && bt.t_fwd == bt.t_rev && bt.scratch_plan == bt.scratch_meas && rejected_typ == 0;
        }
    }
    ok
}

// ─── 4: full width at the design windows ──────────────────────────────────────────────────

/// `win_A288.txt` rows `k t nlo nhi esw ead` for margin index `k`.
fn read_windows(text: &str, a: usize, k: usize) -> Vec<D2Win> {
    let mut out = Vec::new();
    for l in text.lines() {
        if l.starts_with('#') || l.trim().is_empty() {
            continue;
        }
        let f: Vec<usize> = l.split_whitespace().map(|x| x.parse().unwrap()).collect();
        if f[0] == k {
            out.push(D2Win { a, t: f[1], nlo: f[2], nhi: f[3], esw: f[4], ead: f[5] });
        }
    }
    out
}

/// Constructions every sweep / chain / full case runs (Port, in place, in place with a Gidney bottom, in place
/// with every unmasked position on Gidney carries).
const MODES: &[D2Mode] = &[D2Mode::Port, D2Mode::LowRoom { gidney: 0 }, D2Mode::LowRoom { gidney: 3 }, D2Mode::LowRoom { gidney: 1000 }];

const WIN_A288: &str = include_str!("win_A288.txt");

fn random_lanes(win: &D2Win, want: usize, rng: &mut Rng) -> Vec<Lane> {
    let mut out = Vec::new();
    let mut tries = 0usize;
    while out.len() < want && tries < 2000 * want {
        tries += 1;
        let n = match rng.below(8) {
            0 => win.nlo,
            1 => win.nhi,
            _ => win.nlo + rng.below((win.nhi - win.nlo + 1) as u64) as usize,
        };
        let top = win.esw.max(win.ead).max(2);
        // widths aimed at this N's region top (so the masked windows are exercised) or spread
        let o0 = win.t.div_ceil(2);
        let ladd = win.a.saturating_sub(o0 + n.div_ceil(2) + 1).clamp(2, top);
        let mode = rng.below(3);
        let mut width = || match mode {
            0 => ladd - rng.below(ladd.min(6) as u64) as usize,
            1 => top - rng.below(top.min(16) as u64) as usize,
            _ => 1 + rng.below(top as u64) as usize,
        };
        let (wa, wb) = (width(), width());
        let mut v = [rng.bits(wa), rng.bits(wb)];
        for x in v.iter_mut() {
            if rng.next() & 1 == 1 {
                *x = !*x;
            }
        }
        let odd = (rng.next() & 1) as usize;
        v[odd].set_bit(0, true);
        v[1 - odd].set_bit(0, false);
        if let Some(l) = lane_of(win.a, win.t, v, n) {
            if l.c && blen(l.v[0]).max(blen(l.v[1])) > win.esw {
                continue;
            }
            if l.wad > win.ead {
                continue;
            }
            out.push(l);
        }
    }
    fill_random(&mut out, win.a, rng);
    out
}

fn full_runs(lanes_per_tick: usize) -> bool {
    println!("D2_TICK_SELFTEST 4. full width A=288 at the design windows (win_A288.txt margin 0, clamped), random lanes");
    let wins = read_windows(WIN_A288, 288, 0);
    let mut ok = true;
    let mut rng = Rng(44);
    for &t in &[0usize, 1, 2, 3, 50, 99, 100, 150, 200, 250, 300, 330, 331, 350, 360, 370, 380, 390, 394] {
        let win = wins[t].clamped();
        let lanes = random_lanes(&win, lanes_per_tick, &mut rng);
        if lanes.is_empty() {
            println!("  t={t}: no random lane fits {win:?}");
            ok = false;
            continue;
        }
        // N coverage of the lanes (informational)
        let nmin = lanes.iter().map(|l| l.n).min().unwrap();
        let nmax = lanes.iter().map(|l| l.n).max().unwrap();
        let o0 = t.div_ceil(2);
        let l0 = |l: &Lane| win.a as i64 - o0 as i64 - l.n.div_ceil(2) as i64;
        let add_masked = lanes.iter().filter(|l| l0(l) - 1 < win.ead as i64).count();
        let add_tap_in = lanes.iter().filter(|l| l0(l) - 1 <= win.ead as i64 && l0(l) - 1 >= l.wad as i64 && l0(l) - 1 < win.ead as i64).count();
        let swap_masked = lanes.iter().filter(|l| l.c && l0(l) < win.esw as i64).count();
        for &mode in MODES {
        let r = run_tick(win, &lanes, &format!("full-{t}-{mode:?}"), mode);
        ok &= report(&r, &format!("random, N seen {nmin}..{nmax}; region boundary inside the add window {add_masked} ({add_tap_in} tapped there), inside the swap window with c=1 {swap_masked}"));
        }
    }
    ok
}

/// Entry point (`D2_TICK_SELFTEST=1`). Panics on any failure.
pub fn run() {
    let lanes: usize = std::env::var("D2_TICK_SELFTEST_FULL_LANES").ok().and_then(|s| s.parse().ok()).unwrap_or(4096);
    let only = std::env::var("D2_TICK_SELFTEST_ONLY").unwrap_or_default();
    let want = |k: &str| only.is_empty() || only.split(',').any(|x| x == k);
    let mut ok = true;
    if want("parity") {
        ok &= parity_runs();
    }
    if want("sweep") {
        ok &= sweep_runs();
    }
    if want("chain") {
        ok &= chain_runs();
    }
    if want("full") {
        ok &= full_runs(lanes);
    }
    if ok {
        println!("D2_TICK_SELFTEST PASS");
    } else {
        println!("D2_TICK_SELFTEST FAIL");
        std::process::exit(1);
    }
}

/// `D2_TICK_COST=<win file>` (`k t nlo nhi esw ead` rows) with `D2_TICK_COST_A` (default 288): per-tick T and
/// scratch of the planned tick (window clamped), and per-traversal sums by margin index.
pub fn cost_table(path: &str, a: usize, dump: Option<&str>, mode: D2Mode) {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("D2_TICK_COST: {path}: {e}"));
    let ks: std::collections::BTreeSet<usize> = text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| l.split_whitespace().next().unwrap().parse().unwrap())
        .collect();
    let mut out = String::new();
    out.push_str("# k t nlo nhi esw ead (clamped) t_fwd t_rev scratch by-tag\n");
    for &k in &ks {
        let wins = read_windows(&text, a, k);
        let mut sum_f = 0usize;
        let mut sum_r = 0usize;
        let mut smax = (0usize, 0usize);
        let mut tag_sum: BTreeMap<Tag, usize> = BTreeMap::new();
        for w in &wins {
            let wc = w.clamped();
            let pl = plan(&wc, mode);
            sum_f += pl.t_fwd;
            sum_r += pl.t_rev;
            if pl.scratch > smax.0 {
                smax = (pl.scratch, w.t);
            }
            for (tg, v) in &pl.by_tag {
                *tag_sum.entry(*tg).or_insert(0) += v;
            }
            out.push_str(&format!(
                "{k} {} {} {} {} {} {} {} {} {}\n",
                w.t, wc.nlo, wc.nhi, wc.esw, wc.ead, pl.t_fwd, pl.t_rev, pl.scratch, tags(&pl.by_tag).replace(", ", ",").replace(' ', ":")
            ));
        }
        println!(
            "D2_TICK_COST {mode:?} A={a} margin index {k}: {} ticks, forward T per traversal {sum_f}, reverse {sum_r}, peak scratch {} (t={})",
            wins.len(), smax.0, smax.1
        );
        println!("  by tag: {}", tags(&tag_sum));
    }
    if let Some(d) = dump {
        std::fs::write(d, out).unwrap();
        println!("  wrote {d}");
    }
}
