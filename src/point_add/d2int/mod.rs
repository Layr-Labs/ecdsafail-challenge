//! D2 joint layout: the full division and multiplication legs of the point add (track D2, integration).
//!
//! Inert unless `D2_INT=1` (the recipe in `point_add::install_skywalk_submission_recipe` sets it). It replaces
//! the carry schedule's legs (`heo_carry::divide` / `multiply`) and reuses everything around the walk unchanged:
//! the FD seed / unseed (with the coordinate and back-seam fusions), the FD payload seed and its inverse (with the
//! y-sub / y-fin fusions), the payload cells (`cell_div` / `cell_mul`, keyed on the production tick index) and the
//! 256-Fredkin routes. What changes is the walk's storage:
//!
//! * the two rails live NORMALIZED in two flat arrays of `A` wires (`d2tick`), relabelled alternately, with one
//!   sign wire per array; the tick's typ bit stays in the freed LSB wire of the halved array;
//! * B/C letters push their s bit onto a downward stack at the top of the arrays, a park register records the
//!   checkpoint that saw the walk parked, and post-park ticks pop the newest s bit into their freed LSB wire
//!   (`d2_stack`);
//! * there is no tape codec, no batch and no loan: every payload cell is fused into its tick (division: after
//!   the forward tick; multiplication: before the reverse tick of the walk back).
//!
//! Tick indexing: production tick 0 is the FD seed (rails `(X, Y)` and `o_0 = [|X| < |Y|]`), production ticks
//! `1..R` are D2 ticks `0..R-1` with `typ_{-1} = o_0`. The D2 typ sequence equals the production one (the
//! alternation complements `c` on every tick after the first, and the D2 typ formula adds the same 1), so every
//! payload cell sees exactly the letter it sees in production.
//!
//! Per tick (forward): rail op (steps 1-3 of the D2 tick, `s` left on its wire) -> `fixup` -> payload cell +
//! route (division leg) -> `detect` (checkpoints) -> `push` -> `tick_pop` (after the first checkpoint).
//! The walk back emits the exact inverses in reverse order; the multiplication leg's cell and route sit between
//! the inverse push and the inverse fixup, where the tick's (typ, s) are on their wires again.
//!
//! Knobs (read once, recipe defaults in `install_skywalk_submission_recipe`):
//! `D2_A` (array width, 288), `D2_TICK_WIN_K` (window margin index of `win_A288.txt`: 0/1/2/3 = margin
//! 0/1/2/4), `D2_STACK_MARGIN` (stack-block window margin, 3), `D2_PEBBLES` (detector pebbles, 6),
//! `D2_GIDNEY` (Gidney bottom positions of the low-room add, 0), `D2_CELL_POOL` (lend the idle array wires to
//! the cells' low-room folds as dirty wires, 1).
//! Selftest: `D2_INT_SELFTEST=1 build_circuit` (see `selftest.rs`).
use super::super::super::d2_stack::{self, sched::D2Sched, D2Layout};
use super::super::super::d2tick::{self, D2Mode, D2Plan, D2Regs, D2Win, Dir};
use super::*;

pub mod selftest;

pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| env_bool("D2_INT", false))
}

/// The integration's public configuration (windows, schedule, construction).
pub struct D2Cfg {
    pub a: usize,
    /// D2 ticks per traversal (production rounds - 1).
    pub ticks: usize,
    pub wins: Vec<D2Win>,
    pub sched: D2Sched,
    pub mode: D2Mode,
    pub cell_pool: bool,
    pub cell_lend: bool,
    pub gidney_fill: bool,
}

/// Window table `k t nlo nhi esw ead` (jl-probe `windows.py`), rows of margin index `k`.
pub fn parse_wins(text: &str, k: usize, a: usize) -> Vec<D2Win> {
    let mut out: Vec<D2Win> = Vec::new();
    for l in text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let f: Vec<usize> = l.split_whitespace().map(|x| x.parse().expect("win_A288: integer")).collect();
        assert_eq!(f.len(), 6, "win_A288 line {l:?}");
        if f[0] != k {
            continue;
        }
        assert_eq!(f[1], out.len(), "win_A288: ticks out of order");
        out.push(D2Win { a, t: f[1], nlo: f[2], nhi: f[3], esw: f[4], ead: f[5] });
    }
    assert!(!out.is_empty(), "win_A288: no rows for margin index {k}");
    out
}

/// The stack schedule from the model table, truncated to `ticks` rows; checkpoints = the default list below `ticks`.
pub fn stack_sched(a: usize, ticks: usize, margin: u64, pebbles: usize) -> D2Sched {
    let text = include_str!("../d2_stack/tools/out/sched_A288_d2_win.tsv");
    let mut kept = String::new();
    let mut rows = 0usize;
    for l in text.lines() {
        if l.starts_with('#') || l.trim().is_empty() {
            kept.push_str(l);
            kept.push('\n');
            continue;
        }
        if rows < ticks {
            kept.push_str(l);
            kept.push('\n');
            rows += 1;
        }
    }
    assert_eq!(rows, ticks, "stack table has {rows} rows, need {ticks}");
    let cks: Vec<usize> = d2_stack::sched::default_checkpoints().into_iter().filter(|&d| d < ticks).collect();
    let s = D2Sched::from_model_table(&kept, a, &cks, margin, pebbles);
    if env_bool("D2_DETECT_AFTER_PUSH", false) {
        s.with_detect_after_push()
    } else {
        s
    }
}

/// Per checkpoint, the cheapest detector construction (pebbles, dirty selection levels; the membership test at the
/// act) whose temporaries fit `room`. Gate lists do not depend on wire identities, so a stand-in layout is used.
/// Checkpoints with no fitting construction keep their parameters (the build then reports the overshoot).
pub fn fit_detectors(s: &mut D2Sched, room: usize, high: bool) {
    let a = s.a;
    let pb = s.pbits();
    let mut next = 0u64;
    let mut ids = |n: usize| -> Vec<QubitId> {
        (0..n)
            .map(|_| {
                next += 1;
                QubitId(next)
            })
            .collect()
    };
    let p = [ids(a), ids(a)];
    let sig = ids(2);
    let lay = D2Layout::from_wires(a, p, [sig[0], sig[1]], ids(d2_stack::N_BITS), ids(pb), ids(1)[0]);
    let mut rows = Vec::new();
    if high {
        s.det_high = s.det.clone();
    }
    for t in 0..s.ticks {
        let Some(dp0) = (if high { s.det_high[t] } else { s.det[t] }) else { continue };
        let len = d2_stack::detect_ladder_len(&lay, t, &dp0);
        let mut best: Option<(f64, d2_stack::DetParams, u32)> = None;
        for dl in 0..=5usize {
            for peb in 1..=8usize {
                if len > 0 && d2_stack::pebble::visit_cost(len, peb).is_none() {
                    continue;
                }
                let dp = d2_stack::DetParams { pebbles: peb, dirty_lv: dl, late_memb: true, ..dp0 };
                let g = d2_stack::detect_gl(&lay, t, dp);
                if g.peak as usize > room {
                    continue;
                }
                let cost = g.t_expected();
                if best.as_ref().is_none_or(|b| cost < b.0) {
                    best = Some((cost, dp, g.peak));
                }
            }
        }
        match best {
            Some((cost, dp, peak)) => {
                rows.push(format!("{t}:p{}d{}/{peak}/{cost:.0}", dp.pebbles, dp.dirty_lv));
                if high {
                    s.det_high[t] = Some(dp);
                } else {
                    s.det[t] = Some(dp);
                }
            }
            None => rows.push(format!("{t}:NOFIT")),
        }
    }
    eprintln!("D2_DETECT_FIT high={high} room={room} {}", rows.join(" "));
}

pub fn d2cfg(rounds: usize) -> &'static D2Cfg {
    static CFG: OnceLock<D2Cfg> = OnceLock::new();
    let c = CFG.get_or_init(|| {
        let a = env_usize("D2_A", 288);
        assert_eq!(a, 288, "D2_A: the compiled-in windows are for A = 288");
        let ticks = rounds - 1;
        let k = env_usize("D2_TICK_WIN_K", 1);
        let all = parse_wins(include_str!("../d2tick/win_A288.txt"), k, a);
        assert!(all.len() >= ticks, "win_A288 has {} ticks, need {ticks}", all.len());
        let wins: Vec<D2Win> = all[..ticks].iter().map(|w| w.clamped()).collect();
        let margin = env_usize("D2_STACK_MARGIN", 3) as u64;
        let pebbles = env_usize("D2_PEBBLES", 6);
        let mut sched = stack_sched(a, ticks, margin, pebbles);
        if sched.detect_after_push {
            // the detector runs with the payload (2N) live and the clean s wire lent
            let lw = 2 * a + 2 + d2_stack::N_BITS + sched.pbits() + 1;
            fit_detectors(&mut sched, h7::cap() - N - lw + 1, true);
            fit_detectors(&mut sched, h7::cap() - 2 * N - lw + 1, false);
        }
        let mode = D2Mode::LowRoom { gidney: env_usize("D2_GIDNEY", 0) };
        let cell_pool = env_bool("D2_CELL_POOL", true);
        let cell_lend = env_bool("D2_CELL_LEND", true);
        let gidney_fill = env_bool("D2_GIDNEY_FILL", true);
        eprintln!("D2_CONFIG A={a} ticks={ticks} win_k={k} stack_margin={margin} pebbles={pebbles} mode={mode:?} checkpoints={} pbits={} cell_pool={cell_pool} cell_lend={cell_lend} gidney_fill={gidney_fill} detect_after_push={}",
            sched.cks.len(), sched.pbits(), sched.detect_after_push);
        D2Cfg { a, ticks, wins, sched, mode, cell_pool, cell_lend, gidney_fill }
    });
    assert_eq!(c.ticks + 1, rounds, "D2: both legs must have the same round count");
    c
}

/// Persistent wires of the D2 storage outside the payload: arrays, signs, N + 1, park register, s.
fn layout_wires(d: &D2Cfg) -> usize {
    2 * d.a + 2 + d2_stack::N_BITS + d.sched.pbits() + 1
}

/// The rail op of tick `t` (steps 1-3; tick 0 also erases o_0) with as many Gidney bottom positions as `room` allows.
fn plan_fit(d: &D2Cfg, t: usize, room: usize) -> D2Plan {
    let mk = |g: usize| {
        let m = match d.mode { D2Mode::LowRoom { .. } => D2Mode::LowRoom { gidney: g }, other => other };
        if t == 0 { d2tick::plan_rail_erase0(&d.wins[t], m) } else { d2tick::plan_rail(&d.wins[t], m) }
    };
    let base = mk(0);
    assert!(base.scratch <= room, "D2 tick {t}: rail op needs {} scratch, room {room}", base.scratch);
    if !matches!(d.mode, D2Mode::LowRoom { .. }) || !d.gidney_fill {
        return base;
    }
    let mut g = room - base.scratch;
    loop {
        let pl = mk(g);
        if pl.scratch <= room {
            return pl;
        }
        g -= 1;
    }
}

/// Rail-op plans per tick for the two room regimes. `low`: the traversal that carries the payload cells (division
/// forward, multiplication walk back: payload 512 live). `high`: the rails-only traversal (division walk back with
/// Del freed, multiplication forward before Del exists: payload 256 live). Any exact plan of a tick implements the
/// same map, so the walk back may run a different construction than the forward (only its exact inverse map).
pub struct RailPlans {
    pub low: Vec<D2Plan>,
    pub high: Vec<D2Plan>,
}

fn rail_plans(d: &D2Cfg) -> &'static RailPlans {
    static P: OnceLock<RailPlans> = OnceLock::new();
    P.get_or_init(|| {
        let cap = h7::cap();
        let lw = layout_wires(d);
        // tick 0 runs with the o_0 wire live
        let room = |pay: usize, t: usize| cap - pay - lw - usize::from(t == 0);
        let low: Vec<D2Plan> = (0..d.ticks).map(|t| plan_fit(d, t, room(2 * N, t))).collect();
        let high: Vec<D2Plan> = (0..d.ticks).map(|t| plan_fit(d, t, room(N, t))).collect();
        let tl: usize = low.iter().map(|p| p.t_fwd).sum();
        let tlr: usize = low.iter().map(|p| p.t_rev).sum();
        let th: usize = high.iter().map(|p| p.t_fwd).sum();
        let thr: usize = high.iter().map(|p| p.t_rev).sum();
        eprintln!("D2_RAIL_PLANS cap={cap} layout={lw} low: fwd {tl} rev {tlr} max scratch {} | high: fwd {th} rev {thr} max scratch {}",
            low.iter().map(|p| p.scratch).max().unwrap(), high.iter().map(|p| p.scratch).max().unwrap());
        RailPlans { low, high }
    })
}

/// D2 storage of one leg.
pub struct D2Walk {
    pub lay: D2Layout,
    /// `typ_{-1}` = o_0 (the FD seed's orientation bit): live from the seed to the end of the forward tick 0 (which
    /// erases it), and again from the reverse tick 0 (which rebuilds it) to the unseed.
    pub o0: Option<QubitId>,
}

impl D2Walk {
    fn regs(&self) -> D2Regs {
        D2Regs { p: self.lay.p.clone(), sig: self.lay.sig, n: self.lay.nreg.clone(), s: self.lay.s, typ0: self.o0 }
    }
}

/// Post-seed rails (two's complement, `N + 1` wires each, top wire = sign) -> D2 arrays. Clifford only.
/// Array k = rail k's low N wires (normalized: XOR the sign) + `a - N` fresh zero wires; sig[k] = rail k's top wire.
pub fn to_layout(c: &mut Builder, rails: Rails, o0: QubitId, a: usize, pbits: usize) -> D2Walk {
    let Rails { r1, r2 } = rails;
    assert!(r1.len() == N + 1 && r2.len() == N + 1, "D2: post-seed rails must be N + 1 wires (got {} / {})", r1.len(), r2.len());
    let mut p: [Vec<QubitId>; 2] = [Vec::with_capacity(a), Vec::with_capacity(a)];
    let mut sig = [r1[N], r2[N]];
    for (k, r) in [r1, r2].into_iter().enumerate() {
        let sg = r[N];
        for &q in &r[..N] {
            c.cx(sg, q);
        }
        p[k].extend_from_slice(&r[..N]);
        p[k].extend(c.alloc_qubits(a - N));
        sig[k] = sg;
    }
    let nreg = c.alloc_qubits(d2_stack::N_BITS);
    let preg = c.alloc_qubits(pbits);
    let s = c.alloc_qubit();
    let lay = D2Layout::from_wires(a, p, sig, nreg, preg, s);
    lay.init(c);
    D2Walk { lay, o0: Some(o0) }
}

/// Inverse of [`to_layout`] at the post-seed state (N = 0, preg all ones, no typ wires, gap zero).
pub fn from_layout(c: &mut Builder, w: D2Walk) -> (Rails, QubitId) {
    let D2Walk { lay, o0 } = w;
    lay.fini(c);
    c.free(lay.s);
    c.free_vec(&lay.preg);
    c.free_vec(&lay.nreg);
    let mut rails: Vec<Vec<QubitId>> = Vec::new();
    for k in 0..2 {
        let sg = lay.sig[k];
        for &q in &lay.p[k][..N] {
            c.cx(sg, q);
        }
        c.free_vec(&lay.p[k][N..]);
        let mut r = lay.p[k][..N].to_vec();
        r.push(sg);
        rails.push(r);
    }
    let r2 = rails.pop().unwrap();
    let r1 = rails.pop().unwrap();
    (Rails { r1, r2 }, o0.expect("D2: o_0 must be rebuilt before the unlayout"))
}

/// Forward / reverse rail op of D2 tick `t`. Tick 0 erases o_0 forward (the wire is released) and rebuilds it in
/// reverse (on a fresh wire).
fn rail(c: &mut Builder, w: &mut D2Walk, plans: &[D2Plan], t: usize, dir: Dir) {
    if t == 0 && dir == Dir::Reverse {
        assert!(w.o0.is_none());
        w.o0 = Some(c.alloc_qubit());
    }
    d2tick::emit(c, &plans[t], &w.regs(), dir);
    if t == 0 && dir == Dir::Forward {
        let o = w.o0.take().expect("o_0 wire");
        c.release_clean(o);
    }
}

/// Wires that hold a public constant at the cell slot of tick `t` (after the rail op and the fixup, before the
/// push; the multiplication walk back reaches the same state): `(clean zero wires, park-register wires = all ones)`.
/// Zero: the array gap above both rails' public bound (`o_k + ead + 1`) and below the deepest stack bottom
/// (`A - S_k` at the window's largest N), plus the count register's bits above the largest `N + 1`. Margin 2 on
/// N. The park register holds all ones before the first checkpoint.
pub fn cell_lendable(d: &D2Cfg, lay: &D2Layout, t: usize) -> (Vec<QubitId>, Vec<QubitId>) {
    let w = &d.wins[t];
    let nmax = w.nhi + 2;
    let o = [(t + 2) / 2, (t + 1) / 2];
    let smax = [nmax.div_ceil(2), nmax / 2];
    let mut zero = Vec::new();
    for k in 0..2 {
        let lo = o[k] + w.ead + 1;
        let hi = d.a.saturating_sub(smax[k]);
        for i in lo..hi {
            zero.push(lay.p[k][i]);
        }
    }
    let nb = usize::BITS as usize - (nmax + 1).leading_zeros() as usize;
    zero.extend_from_slice(&lay.nreg[nb.min(lay.nreg.len())..]);
    let ones = if d.sched.cks.first().is_some_and(|&ck| t < ck) { lay.preg.clone() } else { Vec::new() };
    (zero, ones)
}

/// Run a payload cell with (1) the public-constant wires of [`cell_lendable`] released to the builder as clean
/// room and (2) every other idle array wire lent to the low-room folds as a dirty wire.
fn d2_cell(c: &mut Builder, d: &D2Cfg, w: &D2Walk, t: usize, body: impl FnOnce(&mut Builder)) {
    let typ = w.lay.typ_wire(t);
    let (zero, ones) = if d.cell_lend { cell_lendable(d, &w.lay, t) } else { (Vec::new(), Vec::new()) };
    let lent: std::collections::BTreeSet<u64> = zero.iter().chain(ones.iter()).map(|q| q.0).collect();
    let pool: Vec<QubitId> = if d.cell_pool {
        w.lay.p.iter().flatten().copied().filter(|&q| q != typ && !lent.contains(&q.0)).collect()
    } else {
        Vec::new()
    };
    for &q in &ones {
        c.x(q);
    }
    for &q in zero.iter().chain(ones.iter()) {
        c.release_clean(q);
    }
    let loan = pool.last().copied();
    let mut body = Some(body);
    super::super::super::lowroom::with_pool(pool, || {
        super::super::super::dirty_boundary_probe::with_tape(c, loan, body.take().unwrap());
    });
    for &q in zero.iter().chain(ones.iter()) {
        c.reacquire(q);
    }
    for &q in &ones {
        c.x(q);
    }
}

/// `numerator /= denominator (mod p)` on the D2 layout.
pub fn divide(c: &mut Builder, numerator: &[QubitId], denominator: &[QubitId]) {
    let cfg = config();
    let k = carry_cfg();
    let r = cfg.rounds();
    let d = d2cfg(r);
    let plans = rail_plans(d);
    let sig = numerator;
    c.set_phase("heo_div_fwd");
    let (rails, o0, _) = book(c, "seeds", "fd seed", 0, |c| fd_seed(c, denominator, wpost(cfg, 0), false));
    let (xs, ys) = (*rails.r1.last().unwrap(), *rails.r2.last().unwrap());
    if r4_ysub_fuse() {
        r4_ysub_tail(c, sig, xs, ys, o0);
    }
    let del = book(c, "g1b", "div fd payload", 0, |c| fd_payload_div(c, sig, xs, ys, o0));
    let mut w = book(c, "seeds", "d2 layout", 0, |c| to_layout(c, rails, o0, d.a, d.sched.pbits()));
    for t in 0..d.ticks {
        let tp = t + 1;
        let blocks = d2_stack::tick_blocks(&w.lay, &d.sched, t);
        book(c, "rails", "div fwd rail", tp, |c| rail(c, &mut w, &plans.low, t, Dir::Forward));
        book(c, "park", "div fixup", tp, |c| d2_stack::after_tick_fwd(c, &blocks));
        let typ = w.lay.typ_wire(t);
        book(c, "cells", "div fused cell", tp, |c| d2_cell(c, d, &w, t, |c| cell_div(c, cfg, tp, typ, sig, &del)));
        if !(k.db_skip && tp + 1 == r) && !(k.db_skip2 && tp + 2 == r) {
            book(c, "routing", "div route", tp, |c| route(c, w.lay.s, sig, &del));
        }
        book(c, "stack", "div push/park", tp, |c| d2_stack::after_cell_fwd(c, &blocks));
    }
    c.set_phase("heo_div_endpoint");
    c.cx_pairs(sig, &del);
    c.free_vec(&del);
    c.set_phase("heo_div_walkback");
    for t in (0..d.ticks).rev() {
        let tp = t + 1;
        let blocks = d2_stack::tick_blocks_room(&w.lay, &d.sched, t, true);
        book(c, "stack", "div rev push/park", tp, |c| {
            d2_stack::before_cell_rev(c, &blocks);
            d2_stack::after_cell_rev(c, &blocks);
        });
        book(c, "rails", "div rev rail", tp, |c| rail(c, &mut w, &plans.high, t, Dir::Reverse));
    }
    c.set_phase("heo_div_unseed");
    let (rails, o0) = book(c, "seeds", "d2 unlayout", 0, |c| from_layout(c, w));
    let x = book(c, "seeds", "fd unseed", 0, |c| fd_unseed(c, rails, o0, None, super::super::super::back_seam::Leg::Div));
    restore_layout(c, &x, denominator);
}

/// `numerator *= denominator (mod p)` on the D2 layout: the inverse map, cells fused into the walk back.
pub fn multiply(c: &mut Builder, numerator: &[QubitId], denominator: &[QubitId]) {
    let cfg = super::super::config_mul();
    let k = carry_cfg();
    let r = cfg.rounds();
    let d = d2cfg(r);
    let plans = rail_plans(d);
    let sig = numerator;
    c.set_phase("heo_mul_fwd");
    let (rails, o0, _) = book(c, "seeds", "fd seed", 0, |c| fd_seed(c, denominator, wpost(cfg, 0), false));
    let mut w = book(c, "seeds", "d2 layout", 0, |c| to_layout(c, rails, o0, d.a, d.sched.pbits()));
    for t in 0..d.ticks {
        let tp = t + 1;
        let blocks = d2_stack::tick_blocks_room(&w.lay, &d.sched, t, true);
        book(c, "rails", "mul fwd rail", tp, |c| rail(c, &mut w, &plans.high, t, Dir::Forward));
        book(c, "stack", "mul push/park", tp, |c| {
            d2_stack::after_tick_fwd(c, &blocks);
            d2_stack::after_cell_fwd(c, &blocks);
        });
    }
    c.set_phase("heo_mul_fused");
    let del = c.alloc_qubits(N);
    c.cx_pairs(sig, &del);
    for t in (0..d.ticks).rev() {
        let tp = t + 1;
        let blocks = d2_stack::tick_blocks(&w.lay, &d.sched, t);
        book(c, "stack", "mul rev push/park", tp, |c| d2_stack::before_cell_rev(c, &blocks));
        if !(k.mb_skip2 && tp + 2 == r) {
            book(c, "routing", "mul fused route", tp, |c| route(c, w.lay.s, sig, &del));
        }
        let typ = w.lay.typ_wire(t);
        book(c, "cells", "mul fused cell", tp, |c| d2_cell(c, d, &w, t, |c| cell_mul(c, cfg, tp, typ, sig, &del)));
        book(c, "park", "mul rev fixup", tp, |c| d2_stack::after_cell_rev(c, &blocks));
        book(c, "rails", "mul rev rail", tp, |c| rail(c, &mut w, &plans.low, t, Dir::Reverse));
    }
    c.set_phase("heo_mul_unseed");
    let (rails, o0) = book(c, "seeds", "d2 unlayout", 0, |c| from_layout(c, w));
    let (xs, ys) = (*rails.r1.last().unwrap(), *rails.r2.last().unwrap());
    book(c, "g1b", "mul fd payload", 0, |c| fd_payload_div_inv(c, sig, &del, xs, ys, o0));
    if !r5_take_del_freed() {
        c.free_vec(&del);
    }
    let x = book(c, "seeds", "fd unseed", 0, |c| fd_unseed(c, rails, o0, None, super::super::super::back_seam::Leg::Mul));
    restore_layout(c, &x, denominator);
    if truthy("HEO_LEDGER_PRINT") {
        print_ledger();
    }
}
