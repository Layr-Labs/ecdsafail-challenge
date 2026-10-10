//! SKY-COF walk: seed the rails from `d`, R forward ticks (rail tick, decoder/history disposal of the
//! previous letter, cofactor update, post-park fold), park bookkeeping (rail zero test + odometer),
//! and the exact walk back. Research code; used only by `skycof::pointadd`.
//!
//! # Per-tick schedule (forward, tick t >= 1)
//! 1. `rail_fwd_t(typ_{t-1})` -> `typ_t`, `isC_t` (rails now post(t)).
//! 2. Dispose `typ_{t-1}` against the cofactor post-state of tick t-1 (still untouched):
//!    * t-1 = 0: `first_tick` (A or C only).
//!    * cofactor field below the clamp: decoder push without `en` (a walk parks only once `r = p` fits, i.e.
//!      on ticks whose field is at the clamp; an earlier park is an envelope miss).
//!    * field at the clamp: park test `z = [top park_j bits of r all one]` (= [r == p] = [t-1 >= park]: before
//!      park `r <= p/v < 2^255` for `v >= 2`, and for `v = 1` `p - r = u s` was never below 2^247 in
//!      0.24M walks); odometer step (`g = z & typ`, `odo += g`, `typ ^= g`, `g` erased against
//!      `z & [odo != 0]`); decoder push with `en = !z`. Post-park letters are A (`typ = 1`) and the park
//!      tick's letter is B or C (`typ = 0`), so the odometer ends at the number of post-park ticks.
//! 3. `cof_fwd_t(typ_t, isC_t)`, `isC` erased by measurement.
//! 4. If the cofactor came out at clamp+1 wires: fold `s <- s - p` when the top wire is set (constant add
//!    over the low `fold_w` bits; the top wire is 0 before park).
//!
//! `typ_{R-1}` is disposed the same way after the last tick. The parked rails (0, 1) and `r = p` are then
//! classical constants and are freed; the walk back re-creates them and runs the exact inverse of every step
//! in reverse order.
use super::adder;
use super::decoder::{self as dec, DecCfg, Hreg, TickIo};
use super::tick::{self, Cof, PrevWidths, TickWidths};
use crate::circuit::{BitId as B, QubitId as Q};
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;
use crate::point_add::skycof_mm as mm;
use crate::point_add::N;

pub const SEED_W: usize = N + 2;
pub const CLAMP: usize = N;

/// Walk parameters (source defaults; research overrides in `pointadd::params`).
#[derive(Clone, Copy, Debug)]
pub struct WalkParams {
    pub r: usize,
    /// bits of the park test on the top of `r`
    pub park_j: usize,
    pub w_dec: usize,
    pub fold_w: usize,
    pub odo_bits: usize,
    pub cap: usize,
}

/// Per-tick public widths: rail (post-tick), cofactor field (post-tick), history envelope.
#[derive(Clone)]
pub struct Envelope {
    pub rail: Vec<usize>,
    pub cof: Vec<usize>,
    pub h: Vec<usize>,
    pub micro: Option<RailMicroEnvelope>,
}

/// Absolute per-tick rail widths for a fitted microphase schedule.  The
/// common arithmetic width is kept separate from the two post-tick banks so
/// reverse execution can grow them only after decoder/cofactor cleanup.
#[derive(Clone)]
pub struct RailMicroEnvelope {
    pub swap: Vec<usize>,
    pub add: Vec<usize>,
    pub post_r1: Vec<usize>,
    pub post_r2: Vec<usize>,
}

impl Envelope {
    /// The design's public k=0 w=64 eps=1e-4 widths (rails srail+8, cofactors min(kcof+8, 256),
    /// history H_k0w64+10), extended to `r` ticks by repeating the last row.
    pub fn design(r: usize) -> Self {
        let txt = include_str!("design_widths_k0w64_1e-4.tsv");
        let (mut rail, mut cof, mut h) = (Vec::new(), Vec::new(), Vec::new());
        for l in txt.lines() {
            if l.starts_with('#') || l.starts_with('t') || l.trim().is_empty() {
                continue;
            }
            let f: Vec<usize> = l
                .split('\t')
                .take(4)
                .map(|x| x.trim().parse().unwrap())
                .collect();
            assert_eq!(f[0], rail.len(), "envelope rows out of order");
            rail.push(f[1]);
            cof.push(f[2]);
            h.push(f[3]);
        }
        assert!(!rail.is_empty());
        rail.truncate(r);
        cof.truncate(r);
        h.truncate(r);
        while rail.len() < r {
            rail.push(*rail.last().unwrap());
            cof.push(*cof.last().unwrap());
            h.push(*h.last().unwrap());
        }
        for t in 1..r {
            h[t] = h[t].max(h[t - 1]);
            cof[t] = cof[t].max(cof[t - 1]).min(CLAMP);
        }
        let baseline_h = h.clone();
        let mut micro = None;
        let micro_table = match super::pointadd::knob("SKYCOF_MICROPHASE_TABLE") {
            Some(v) if v == "legacy" => None,
            Some(path) => Some(
                std::fs::read_to_string(&path)
                    .unwrap_or_else(|e| panic!("read SKYCOF_MICROPHASE_TABLE={path}: {e}")),
            ),
            None => Some(include_str!("micro_widths_q1038_hlocal_minus1.tsv").to_owned()),
        };
        if let Some(table) = micro_table {
            assert_eq!(r, 404, "microphase table is frozen for R404");
            assert!(
                (1037..=1057).contains(&super::pointadd::params().walk.cap),
                "microphase table was fitted near cap 1057; wider cap changes its owner contract"
            );
            assert!(
                super::pointadd::knob("SKYCOF_HISTORY_TABLE").is_none(),
                "microphase table already owns the history schedule"
            );
            assert!(
                super::pointadd::knob("SKYCOF_ENVELOPE_EXTRA").is_none(),
                "microphase table is incompatible with envelope extra"
            );
            if let Some(trim) = super::pointadd::knob("SKYCOF_RAIL_TRIM") {
                assert_eq!(
                    trim, "2",
                    "microphase table may only name its railtrim2 reference recipe"
                );
            }
            let mut rows = table.lines();
            assert_eq!(
                rows.next(),
                Some("t\twsw\twadd\tpost_r1\tpost_r2\tH"),
                "unexpected microphase-table header"
            );
            let (mut swap, mut add, mut post_r1, mut post_r2, mut mh) = (
                Vec::with_capacity(r),
                Vec::with_capacity(r),
                Vec::with_capacity(r),
                Vec::with_capacity(r),
                Vec::with_capacity(r),
            );
            for (t, line) in rows.enumerate() {
                assert!(t < r, "microphase table has more than {r} rows");
                let fields: Vec<usize> = line
                    .split('\t')
                    .map(|x| x.parse().expect("microphase table integer"))
                    .collect();
                assert_eq!(fields.len(), 6, "microphase table row {t} field count");
                assert_eq!(fields[0], t, "microphase table row index");
                let (wsw, wad, p1, p2, hh) =
                    (fields[1], fields[2], fields[3], fields[4], fields[5]);
                assert!((3..=SEED_W).contains(&wsw));
                assert!((3..=SEED_W).contains(&wad));
                assert!((3..=SEED_W).contains(&p1));
                assert!((3..=SEED_W).contains(&p2));
                assert!(p1 <= wad && p2 <= wad, "post width exceeds add at {t}");
                if t == 0 {
                    assert_eq!(wsw, SEED_W);
                } else {
                    assert!(
                        wsw >= post_r1[t - 1] && wsw >= post_r2[t - 1],
                        "swap width misses prior post bank at {t}"
                    );
                    assert!(hh >= mh[t - 1], "history schedule decreases at {t}");
                }
                if t < 160 {
                    assert_eq!(hh, baseline_h[t], "early history changed at {t}");
                }
                swap.push(wsw);
                add.push(wad);
                post_r1.push(p1);
                post_r2.push(p2);
                mh.push(hh);
            }
            assert_eq!(swap.len(), r, "microphase table must have exactly {r} rows");
            h = mh;
            micro = Some(RailMicroEnvelope {
                swap,
                add,
                post_r1,
                post_r2,
            });
        }
        // Research-only public history schedule. The frozen table carries the
        // original H width and a replacement in its fifth column. Check every
        // baseline row so a table from another recipe cannot be applied.
        if let Some(path) = super::pointadd::knob("SKYCOF_HISTORY_TABLE") {
            assert_eq!(r, 404, "history table is frozen for R404");
            assert!(
                super::pointadd::knob("SKYCOF_ENVELOPE_EXTRA").is_none(),
                "history table is incompatible with envelope extra"
            );
            let table = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("read SKYCOF_HISTORY_TABLE={path}: {e}"));
            let mut rows = table.lines();
            assert_eq!(
                rows.next(),
                Some("t\tHbaseline\tHlate4\tHpeak4\tHcombo"),
                "unexpected history-table header"
            );
            let mut replacement = Vec::with_capacity(r);
            for (t, line) in rows.enumerate() {
                assert!(t < r, "history table has more than {r} rows");
                let fields: Vec<usize> = line
                    .split('\t')
                    .map(|x| x.parse().expect("history table integer"))
                    .collect();
                assert_eq!(fields.len(), 5, "history table row {t} field count");
                assert_eq!(fields[0], t, "history table row index");
                assert_eq!(fields[1], h[t], "history table baseline mismatch at {t}");
                replacement.push(fields[4]);
            }
            assert_eq!(
                replacement.len(),
                r,
                "history table must have exactly {r} rows"
            );
            assert!(replacement.iter().all(|&x| x > 0));
            assert!(replacement.windows(2).all(|x| x[0] <= x[1]));
            h = replacement;
        }
        // GCD-only research builds have substantially more room than the
        // embedded point-addition walk.  Let the probe spend that room on a
        // wider public envelope instead of relying on a nonce-selected tail.
        // The knob is captured only when SKYCOF_RESEARCH=1.
        if let Some(raw) = super::pointadd::knob("SKYCOF_ENVELOPE_EXTRA") {
            let extra: usize = raw.parse().expect("SKYCOF_ENVELOPE_EXTRA integer");
            for x in &mut rail {
                *x += extra;
            }
            for x in &mut cof {
                *x = (*x + extra).min(CLAMP);
            }
            for x in &mut h {
                *x += extra;
            }
        }
        // Bounded resource/accuracy experiment. This is an explicit narrowing
        // of the inherited fitted support, not an exact representation change.
        if micro.is_none() {
            let trim: usize = super::pointadd::knob("SKYCOF_RAIL_TRIM")
                .map(|raw| raw.parse().expect("SKYCOF_RAIL_TRIM integer"))
                .unwrap_or(2);
            assert!(trim <= 8, "rail trim requires a separate wider experiment");
            for width in &mut rail {
                *width = width.saturating_sub(trim).max(3);
            }
        }
        Envelope {
            rail,
            cof,
            h,
            micro,
        }
    }
    pub fn widths(&self, t: usize) -> TickWidths {
        let (wsw, wad, post_r1, post_r2) = self.micro.as_ref().map_or_else(
            || {
                let wad = self.rail[t];
                (
                    if t == 0 { SEED_W } else { self.rail[t - 1] },
                    wad,
                    wad,
                    wad,
                )
            },
            |m| (m.swap[t], m.add[t], m.post_r1[t], m.post_r2[t]),
        );
        TickWidths {
            wsw,
            wad,
            post_r1,
            post_r2,
            ecof: self.cof[t],
            clamp: CLAMP,
        }
    }
    pub fn post_widths(&self, t: usize) -> (usize, usize) {
        self.micro.as_ref().map_or(
            (self.rail[t], self.rail[t]),
            |m| (m.post_r1[t], m.post_r2[t]),
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TopFate {
    None,
    Freed,
    Folded,
}

/// State after the forward walk: `s` (256 wires, = -2^R / d mod p, lazily reduced), the history, the
/// odometer, and the book-keeping the walk back needs. Rails and `r` are freed (classical constants).
pub struct Parked {
    pub s: Vec<Q>,
    pub h: Hreg,
    pub odo: Vec<Q>,
    prev: Vec<PrevWidths>,
    tops: Vec<TopFate>,
}

fn room(c: &Builder, cap: usize) -> usize {
    cap.saturating_sub(c.active_qubits() as usize)
}

const GHOST_ODO_START: usize = 64;

fn ghost_odo() -> bool {
    super::pointadd::knob("SKYCOF_GHOST_ODO")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true)
}

fn implicit_r0() -> bool {
    super::pointadd::knob("SKYCOF_IMPLICIT_R0")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true)
}

fn check_ghost_odo(p: &WalkParams, env: &Envelope) {
    if !ghost_odo() {
        return;
    }
    let end = GHOST_ODO_START + p.odo_bits;
    assert!(p.odo_bits > 0 && end < CLAMP);
    assert!(
        dec::Window::new(CLAMP, p.w_dec).lo >= end,
        "embedded counter overlaps decoder field reads"
    );
    assert!(
        p.fold_w <= GHOST_ODO_START,
        "embedded counter overlaps the folded constant window"
    );
    assert!(
        CLAMP - p.park_j >= end,
        "embedded counter overlaps the park predicate"
    );
    let first_clamp = env
        .cof
        .iter()
        .position(|&e| e == CLAMP)
        .expect("embedded counter needs a clamped endpoint");
    assert!(
        p.r - first_clamp < (1usize << p.odo_bits),
        "embedded counter can overflow the public parked horizon"
    );
    let (r1, r2) = env.post_widths(p.r - 1);
    assert!(r1 > 0 && r2 > 0);
}

/// At clamp the middle R bits are ordinary cofactor data before park and the
/// odometer afterwards. The other R consumers exclude this interval while
/// parked. It is an alias, never independently allocated or freed.
fn odo_view<'a>(p: &WalkParams, cof: &'a Cof, owned: &'a [Q]) -> &'a [Q] {
    if ghost_odo() {
        if implicit_r0() {
            assert_eq!(cof.r.len() + 1, CLAMP);
            &cof.r[GHOST_ODO_START - 1..GHOST_ODO_START - 1 + p.odo_bits]
        } else {
            assert_eq!(cof.r.len(), CLAMP);
            &cof.r[GHOST_ODO_START..GHOST_ODO_START + p.odo_bits]
        }
    } else {
        owned
    }
}

/// Toggle the prime padding on the unique park-B/C event. In the forward
/// direction this turns known prime bits into zero counter storage. In the
/// inverse direction it restores the full prime before the park cofactor
/// update is undone. Erase g while typ is still unchanged.
fn ghost_odo_prime_xor(
    c: &mut Builder,
    p: &WalkParams,
    cof: &Cof,
    z: Q,
    typ: Q,
    host_r0: bool,
) {
    if !ghost_odo() {
        return;
    }
    if implicit_r0() {
        c.x(typ);
        let prime = crate::point_add::SECP256K1_P;
        for i in 0..p.odo_bits {
            if prime.bit(GHOST_ODO_START + i) {
                c.ccx(z, typ, cof.r[GHOST_ODO_START - 1 + i]);
            }
        }
        c.x(typ);
        return;
    }
    let g = if host_r0 {
        let r0 = cof.r[0];
        assert!(r0 != z && r0 != typ);
        c.x(r0);
        r0
    } else {
        c.alloc_qubit()
    };
    c.x(typ);
    c.ccx(z, typ, g);
    c.x(typ);
    let prime = crate::point_add::SECP256K1_P;
    for i in 0..p.odo_bits {
        if prime.bit(GHOST_ODO_START + i) {
            c.cx(g, cof.r[GHOST_ODO_START + i]);
        }
    }
    let m = c.alloc_bit();
    c.hmr(g, m);
    c.z_if(z, m);
    c.cz_if(z, typ, m);
    c.free_bit(m);
    if host_r0 {
        c.x(g);
    } else {
        c.release_clean(g);
    }
}

fn knob_on_by_default(name: &str) -> bool {
    super::pointadd::knob(name)
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true)
}

/// Post-rail the two low bits have opposite parity.  During decoder/odometer
/// work neither rail is read, so turn r2[0] into a clean temporary owner and
/// restore the exact physical ID before rail execution resumes.
pub(crate) fn with_rail_parity_loan<R>(
    c: &mut Builder,
    rails: &Rails,
    body: impl FnOnce(&mut Builder) -> R,
) -> R {
    if !knob_on_by_default("SKYCOF_RAIL_PARITY_LOAN") {
        return body(c);
    }
    let (a, q) = (rails.r1[0], rails.r2[0]);
    assert_ne!(a, q);
    assert_eq!(c.tracked_condition_depth(), Some(0));
    let live = c.active_qubits();
    c.cx(a, q);
    c.x(q);
    c.release_clean(q);
    let out = body(c);
    assert_eq!(c.active_qubits() + 1, live, "rail parity loan leaked a wire");
    c.reacquire(q);
    c.x(q);
    c.cx(a, q);
    assert_eq!(c.active_qubits(), live);
    out
}

fn secp_c() -> u128 {
    mm::Field::secp().c
}

/// Add a public constant while respecting the walk cap.  The ordinary
/// constant ladder is cheapest when all carries fit.  In low room, a single
/// prepared |1> turns the same constant into a controlled-constant add, which
/// lets `const_arith` use its exact chunked/HMR backend.
fn add_const_capped(c: &mut Builder, acc: &[Q], k: alloy_primitives::U256, cap: usize) {
    use crate::point_add::const_arith::{add_const, cadd_const_trunc};
    let carries = acc.len().saturating_sub(2);
    let room = cap.saturating_sub(c.active_qubits() as usize);
    if room >= carries {
        add_const(c, acc, k);
    } else {
        let one = c.alloc_qubit();
        c.x(one);
        cadd_const_trunc(c, acc, k, one, false);
        c.x(one);
        c.free(one);
    }
}

/// Rails `(d + p, d)` at width `SEED_W`; `R2` takes over `d`'s wires.
pub fn seed(c: &mut Builder, d: &[Q], cap: usize) -> Rails {
    use crate::point_add::modular::f;
    let r1 = c.alloc_qubits(SEED_W);
    c.cx_pairs(&d[..N], &r1[..N]);
    c.x(r1[N]); // d + 2^256
    c.x_all(&r1[..N + 1]); // r - f = NOT(NOT r + f)  (mod 2^257)
    add_const_capped(c, &r1[..N + 1], f(), cap);
    c.x_all(&r1[..N + 1]);
    let mut r2 = d.to_vec();
    r2.extend(c.alloc_qubits(SEED_W - N));
    Rails { r1, r2 }
}

/// Inverse of [`seed`]; returns the wires now holding `d`.
pub fn unseed(c: &mut Builder, rails: Rails, cap: usize) -> Vec<Q> {
    use crate::point_add::modular::f;
    let Rails { r1, r2 } = rails;
    assert_eq!(r1.len(), SEED_W);
    assert_eq!(r2.len(), SEED_W);
    add_const_capped(c, &r1[..N + 1], f(), cap); // d + 2^256
    c.x(r1[N]);
    c.cx_pairs(&r2[..N], &r1[..N]);
    c.free_vec(&r1);
    c.free_vec(&r2[N..]);
    r2[..N].to_vec()
}

// ─── park test ──────────────────────────────────────────────────────────────────────────────────

/// AND tree over `lits` with every internal node live. Returns (root, nodes bottom-up). `len - 1` Toffoli.
fn tree(c: &mut Builder, lits: &[Q]) -> (Q, Vec<(Q, Q, Q)>) {
    assert!(lits.len() >= 2);
    let mut nodes = Vec::new();
    let mut level: Vec<Q> = lits.to_vec();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2 + 1);
        let mut i = 0;
        while i + 1 < level.len() {
            let n = c.alloc_qubit();
            c.ccx(level[i], level[i + 1], n);
            nodes.push((n, level[i], level[i + 1]));
            next.push(n);
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    (level[0], nodes)
}

/// Erase tree nodes top-down by measurement (each node's children are still live): 0 Toffoli.
fn erase_nodes(c: &mut Builder, nodes: &[(Q, Q, Q)]) {
    for &(n, a, b) in nodes.iter().rev() {
        let m = c.alloc_bit();
        c.hmr(n, m);
        c.cz_if(a, b, m);
        c.free_bit(m);
        c.release_clean(n);
    }
}

/// A fresh wire holding AND(lits) with no other wire kept (`len - 1` Toffoli, `len - 1` wires transient).
fn and_frozen(c: &mut Builder, lits: &[Q]) -> Q {
    if lits.len() == 1 {
        let o = c.alloc_qubit();
        c.cx(lits[0], o);
        return o;
    }
    let (root, nodes) = tree(c, lits);
    erase_nodes(c, &nodes[..nodes.len() - 1]);
    root
}

/// Multi-controlled Z on `lits` (under the caller's condition): `len - 2` Toffoli.
fn mcz(c: &mut Builder, lits: &[Q]) {
    match lits.len() {
        0 => {}
        1 => c.z_if(lits[0], crate::circuit::NO_BIT),
        2 => c.cz(lits[0], lits[1]),
        n => {
            let (root, nodes) = tree(c, &lits[..n - 1]);
            c.cz(root, lits[n - 1]);
            erase_nodes(c, &nodes);
        }
    }
}

/// Erase a wire holding AND(lits) whose tree is gone: HMR, then MCZ under the outcome.
fn erase_frozen(c: &mut Builder, w: Q, lits: &[Q]) {
    if lits.len() == 1 {
        c.cx(lits[0], w);
        c.release_clean(w);
        return;
    }
    let m = c.alloc_bit();
    c.hmr(w, m);
    c.push_condition(m);
    mcz(c, lits);
    c.pop_condition();
    c.free_bit(m);
    c.release_clean(w);
}

/// Toggle `target` by the AND of `controls`, using every clean lane still
/// available below `cap` before falling back to arbitrary dirty wires.  A
/// clean prefix of length `k` collapses the first `k + 1` controls, saving
/// exactly two Toffolis per clean lane versus the all-dirty Barenco ladder;
/// all borrowed wires are restored exactly.
fn dirty_mcx(c: &mut Builder, controls: &[Q], target: Q, dirty: &[Q], cap: usize) {
    match controls.len() {
        0 => c.x(target),
        1 => c.cx(controls[0], target),
        2 => c.ccx(controls[0], controls[1], target),
        m => {
            let k = room(c, cap).min(m - 2);
            let clean = c.alloc_qubits(k);
            for i in 0..k {
                let a = if i == 0 { controls[0] } else { clean[i - 1] };
                c.ccx(a, controls[i + 1], clean[i]);
            }

            let mut reduced = Vec::with_capacity(m - k);
            reduced.push(if k == 0 { controls[0] } else { clean[k - 1] });
            reduced.extend_from_slice(&controls[k + 1..]);
            if reduced.len() == 2 {
                c.ccx(reduced[0], reduced[1], target);
            } else {
                let d = &dirty[..reduced.len() - 2];
                for bottom in [true, false] {
                    if bottom {
                        c.ccx(reduced[0], reduced[1], d[0]);
                    }
                    for i in 1..d.len() {
                        c.ccx(d[i - 1], reduced[i + 1], d[i]);
                    }
                    c.ccx(*d.last().unwrap(), *reduced.last().unwrap(), target);
                    for i in (1..d.len()).rev() {
                        c.ccx(d[i - 1], reduced[i + 1], d[i]);
                    }
                    if bottom {
                        c.ccx(reduced[0], reduced[1], d[0]);
                    }
                }
            }
            for i in (0..k).rev() {
                let a = if i == 0 { controls[0] } else { clean[i - 1] };
                c.ccx(a, controls[i + 1], clean[i]);
            }
            for q in clean {
                c.release_clean(q);
            }
        }
    }
}

/// Bits per part of the park test (each part's AND is a frozen wire; its tree is `PARK_PART - 1` wires).
const PARK_PART: usize = 5;

/// `z = AND(top j bits of r)`: frozen part ANDs `a_i` (parts of `PARK_PART` bits), `z = AND(a_i)` frozen,
/// then the parts are erased (frozen erasure) so only `z` is held while the odometer and the decoder run.
/// `j - 1` Toffoli plus `(len - 2)/2` expected per part; at most `PARK_PART + 1` wires transient. The
/// uncompute measures `z` and, under the outcome, recomputes the parts to apply `MCZ(a_i)` and erases
/// them again.
pub struct ParkTest {
    pub z: Q,
    parts: Vec<Vec<Q>>,
    dirty: Option<(Vec<Q>, Vec<Q>, usize)>,
}

impl ParkTest {
    pub fn compute(c: &mut Builder, r: &[Q], s: &[Q], j: usize, cap: usize) -> Self {
        assert!(r.len() == CLAMP || (implicit_r0() && r.len() + 1 == CLAMP));
        assert!(j > PARK_PART && j <= CLAMP);
        let bits = if implicit_r0() {
            &r[CLAMP - j - 1..]
        } else {
            &r[CLAMP - j..]
        };
        let dirty = match super::pointadd::knob("SKYCOF_DIRTY_PARK").as_deref() {
            Some("1" | "always") => true,
            Some("0" | "never") => false,
            _ => room(c, cap) < 6,
        };
        if dirty {
            assert!(s.len() >= j - 2);
            let z = c.alloc_qubit();
            let controls = bits.to_vec();
            let dirty = s[..j - 2].to_vec();
            assert!(!controls.contains(&z) && !dirty.contains(&z));
            assert!(controls.iter().all(|q| !dirty.contains(q)));
            dirty_mcx(c, &controls, z, &dirty, cap);
            return ParkTest {
                z,
                parts: Vec::new(),
                dirty: Some((controls, dirty, cap)),
            };
        }
        let parts: Vec<Vec<Q>> = bits.chunks(PARK_PART).map(|p| p.to_vec()).collect();
        let a: Vec<Q> = parts.iter().map(|p| and_frozen(c, p)).collect();
        let z = and_frozen(c, &a);
        for (ai, p) in a.iter().zip(&parts).rev() {
            erase_frozen(c, *ai, p);
        }
        ParkTest {
            z,
            parts,
            dirty: None,
        }
    }
    pub fn uncompute(self, c: &mut Builder) {
        if let Some((controls, dirty, cap)) = self.dirty {
            dirty_mcx(c, &controls, self.z, &dirty, cap);
            c.release_clean(self.z);
            return;
        }
        let m = c.alloc_bit();
        c.hmr(self.z, m);
        c.release_clean(self.z);
        c.push_condition(m);
        let a: Vec<Q> = self.parts.iter().map(|p| and_frozen(c, p)).collect();
        mcz(c, &a);
        for (ai, p) in a.iter().zip(&self.parts).rev() {
            erase_frozen(c, *ai, p);
        }
        c.pop_condition();
        c.free_bit(m);
    }
}

// ─── odometer step ──────────────────────────────────────────────────────────────────────────────

fn odo_room(c: &Builder, cap: usize) -> usize {
    room(c, cap).max(4)
}

/// Lend the invariant cofactor bit `r[0]=1` only across one closed odometer
/// update.  ParkTest's root, the type bit and the aliased odometer slice all
/// remain owned and are explicitly disjoint from the lender.
fn with_odo_r0_loan(
    c: &mut Builder,
    r0: Q,
    z: Q,
    typ: Q,
    odo: &[Q],
    body: impl FnOnce(&mut Builder),
) {
    let enabled = super::pointadd::knob("SKYCOF_R0_ODO_LOAN")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(true);
    if !enabled {
        body(c);
        return;
    }
    assert_eq!(c.tracked_condition_depth(), Some(0));
    assert!(r0 != z && r0 != typ && !odo.contains(&r0));
    let live = c.active_qubits();
    c.x(r0);
    c.release_clean(r0);
    body(c);
    assert_eq!(c.active_qubits() + 1, live, "odometer loan leaked a wire");
    c.reacquire(r0);
    c.x(r0);
    assert_eq!(c.active_qubits(), live);
}

/// `g = z & typ; odo += g; typ ^= g; g ^= z & [odo != 0]` (g ends 0).
fn odo_inc_dirty(c: &mut Builder, odo: &[Q], ctl: Q, dirty: &[Q], cap: usize) {
    for i in (1..odo.len()).rev() {
        let mut controls = Vec::with_capacity(i + 1);
        controls.push(ctl);
        controls.extend_from_slice(&odo[..i]);
        dirty_mcx(c, &controls, odo[i], dirty, cap);
    }
    c.cx(ctl, odo[0]);
}

fn odo_dec_dirty(c: &mut Builder, odo: &[Q], ctl: Q, dirty: &[Q], cap: usize) {
    c.cx(ctl, odo[0]);
    for i in 1..odo.len() {
        let mut controls = Vec::with_capacity(i + 1);
        controls.push(ctl);
        controls.extend_from_slice(&odo[..i]);
        dirty_mcx(c, &controls, odo[i], dirty, cap);
    }
}

fn odo_nonzero_dirty(
    c: &mut Builder,
    odo: &[Q],
    z: Q,
    target: Q,
    dirty: &[Q],
    cap: usize,
) {
    c.cx(z, target);
    c.x_all(odo);
    let mut controls = Vec::with_capacity(odo.len() + 1);
    controls.push(z);
    controls.extend_from_slice(odo);
    dirty_mcx(c, &controls, target, dirty, cap);
    c.x_all(odo);
}

fn implicit_mcx(c: &mut Builder, controls: &[Q], target: Q, dirty: &[Q]) {
    match controls.len() {
        0 => c.x(target),
        1 => c.cx(controls[0], target),
        2 => c.ccx(controls[0], controls[1], target),
        m => {
            let d = &dirty[..m - 2];
            for bottom in [true, false] {
                if bottom { c.ccx(controls[0], controls[1], d[0]); }
                for i in 1..d.len() { c.ccx(d[i - 1], controls[i + 1], d[i]); }
                c.ccx(*d.last().unwrap(), *controls.last().unwrap(), target);
                for i in (1..d.len()).rev() { c.ccx(d[i - 1], controls[i + 1], d[i]); }
                if bottom { c.ccx(controls[0], controls[1], d[0]); }
            }
        }
    }
}

fn implicit_odo_inc(c: &mut Builder, z: Q, typ: Q, odo: &[Q], dirty: &[Q]) {
    for i in (1..odo.len()).rev() {
        let mut controls = vec![z, typ];
        controls.extend_from_slice(&odo[..i]);
        implicit_mcx(c, &controls, odo[i], dirty);
    }
    c.ccx(z, typ, odo[0]);
}

fn implicit_odo_dec(c: &mut Builder, z: Q, typ: Q, odo: &[Q], dirty: &[Q]) {
    c.ccx(z, typ, odo[0]);
    for i in 1..odo.len() {
        let mut controls = vec![z, typ];
        controls.extend_from_slice(&odo[..i]);
        implicit_mcx(c, &controls, odo[i], dirty);
    }
}

fn implicit_odo_typ_nonzero(c: &mut Builder, z: Q, typ: Q, odo: &[Q], dirty: &[Q]) {
    c.cx(z, typ);
    c.x_all(odo);
    let mut controls = vec![z];
    controls.extend_from_slice(odo);
    implicit_mcx(c, &controls, typ, dirty);
    c.x_all(odo);
}

fn odo_fwd(c: &mut Builder, z: Q, typ: Q, odo: &[Q], dirty: &[Q], cap: usize) {
    if implicit_r0() {
        implicit_odo_inc(c, z, typ, odo, &dirty[..6]);
        implicit_odo_typ_nonzero(c, z, typ, odo, &dirty[..6]);
        return;
    }
    let dirty_mode = match super::pointadd::knob("SKYCOF_DIRTY_ODO").as_deref() {
        Some("1" | "always") => true,
        Some("0" | "never") => false,
        _ => room(c, cap) < 6,
    };
    let g = c.alloc_qubit();
    c.ccx(z, typ, g);
    if dirty_mode {
        odo_inc_dirty(c, odo, g, dirty, cap);
        c.cx(g, typ);
        odo_nonzero_dirty(c, odo, z, g, dirty, cap);
        c.release_clean(g);
        return;
    }
    let rm = odo_room(c, cap);
    mm::odo_inc(c, odo, g, rm);
    c.cx(g, typ);
    let nz = c.alloc_qubit();
    let rm = odo_room(c, cap);
    mm::odo_nonzero_xor(c, odo, nz, rm);
    c.ccx(z, nz, g);
    let rm = odo_room(c, cap);
    mm::odo_nonzero_xor(c, odo, nz, rm);
    c.release_clean(nz);
    c.release_clean(g);
}

/// Exact inverse of [`odo_fwd`].
fn odo_rev(c: &mut Builder, z: Q, typ: Q, odo: &[Q], dirty: &[Q], cap: usize) {
    if implicit_r0() {
        implicit_odo_typ_nonzero(c, z, typ, odo, &dirty[..6]);
        implicit_odo_dec(c, z, typ, odo, &dirty[..6]);
        return;
    }
    let dirty_mode = match super::pointadd::knob("SKYCOF_DIRTY_ODO").as_deref() {
        Some("1" | "always") => true,
        Some("0" | "never") => false,
        _ => room(c, cap) < 6,
    };
    let g = c.alloc_qubit();
    if dirty_mode {
        odo_nonzero_dirty(c, odo, z, g, dirty, cap);
        c.cx(g, typ);
        odo_dec_dirty(c, odo, g, dirty, cap);
        c.ccx(z, typ, g);
        c.release_clean(g);
        return;
    }
    let nz = c.alloc_qubit();
    let rm = odo_room(c, cap);
    mm::odo_nonzero_xor(c, odo, nz, rm);
    c.ccx(z, nz, g);
    let rm = odo_room(c, cap);
    mm::odo_nonzero_xor(c, odo, nz, rm);
    c.release_clean(nz);
    c.cx(g, typ);
    let rm = odo_room(c, cap);
    mm::odo_dec(c, odo, g, rm);
    c.ccx(z, typ, g);
    c.release_clean(g);
}

// ─── post-park fold ─────────────────────────────────────────────────────────────────────────────

fn implicit_const_bit(k: u64, i: usize) -> bool { (k >> i) & 1 != 0 }

fn implicit_const_carry(c: &mut Builder, b: Q, cin: Q, out: Q, k: bool) {
    if k { c.cx(b, out); c.cx(cin, out); }
    c.ccx(b, cin, out);
}

/// Exact conditional +/-K on the 57-bit fold tail with no clean owner. On the
/// active branch the low R tail is the known secp prime tail; off branch it is
/// arbitrary and restored exactly.
fn implicit_fold_constant(c: &mut Builder, top: Q, cof: &Cof, add: bool) {
    let target = &cof.s[1..58];
    let borrowers = &cof.r[..53];
    let k = (1u64 << 57) - (1u64 << 31) - 488;
    let constant = if add { k } else { (1u64 << 57) - k };
    let prime_tail = k - 1;
    for (i, &q) in borrowers.iter().enumerate() {
        if implicit_const_bit(prime_tail, i) { c.cx(top, q); }
    }
    c.cx(target[3], borrowers[0]);
    c.cx(top, target[3]);
    for i in 4..=55 {
        let cin = borrowers[i - 4];
        let cout = borrowers[i - 3];
        implicit_const_carry(c, target[i], cin, cout, implicit_const_bit(constant, i));
        if implicit_const_bit(constant, i) { c.cx(top, target[i]); }
        c.ccx(top, cin, target[i]);
    }
    let cin = borrowers[52];
    if implicit_const_bit(constant, 56) { c.cx(top, target[56]); }
    c.ccx(top, cin, target[56]);
    for i in (4..=55).rev() {
        let cin = borrowers[i - 4];
        let cout = borrowers[i - 3];
        c.cx(top, target[i]);
        implicit_const_carry(c, target[i], cin, cout, implicit_const_bit(constant, i));
        c.cx(top, target[i]);
    }
    c.cx(top, target[3]);
    c.cx(target[3], borrowers[0]);
    c.cx(top, target[3]);
    for (i, &q) in borrowers.iter().enumerate() {
        if implicit_const_bit(prime_tail, i) { c.cx(top, q); }
    }
}

/// `s` at clamp+1 wires: when the top wire is set, `s <- s - p` (= low bits + c, window `fold_w`);
/// the top wire is then `s[0]` (s even before, odd after) and is cleared and freed.
fn fold(c: &mut Builder, cof: &mut Cof, p: &WalkParams) {
    assert_eq!(cof.s.len(), CLAMP + 1);
    let top = cof.s.pop().unwrap();
    let w = p.fold_w;
    let rm = room(c, p.cap);
    if implicit_r0() {
        implicit_fold_constant(c, top, cof, false);
        c.cx(top, cof.s[0]);
    } else if rm >= 12 {
        mm::cadd_k(c, &cof.s[..w], secp_c(), top, rm);
    } else if tick::parity_source_carry() {
        adder::sub(
            c,
            Some(top),
            &cof.r[1..w],
            &cof.s[1..w],
            Some(cof.r[0]),
            Some(p.cap),
        );
        c.cx(top, cof.s[0]);
    } else {
        // r == p whenever the top wire can be set (park tick and after): s -= top * (p mod 2^w)
        adder::sub(c, Some(top), &cof.r[..w], &cof.s[..w], None, Some(p.cap));
    }
    c.cx(cof.s[0], top);
    c.release_clean(top);
}

/// Exact inverse of [`fold`].
fn unfold(c: &mut Builder, cof: &mut Cof, p: &WalkParams) {
    assert_eq!(cof.s.len(), CLAMP);
    let top = c.alloc_qubit();
    c.cx(cof.s[0], top);
    let w = p.fold_w;
    let rm = room(c, p.cap);
    if implicit_r0() {
        implicit_fold_constant(c, top, cof, true);
        c.cx(top, cof.s[0]);
    } else if rm >= 12 {
        mm::csub_k(c, &cof.s[..w], secp_c(), top, rm);
    } else if tick::parity_source_carry() {
        adder::add(
            c,
            Some(top),
            &cof.r[1..w],
            &cof.s[1..w],
            Some(cof.r[0]),
            Some(p.cap),
        );
        c.cx(top, cof.s[0]);
    } else {
        adder::add(c, Some(top), &cof.r[..w], &cof.s[..w], None, Some(p.cap));
    }
    cof.s.push(top);
}

// ─── letter disposal ────────────────────────────────────────────────────────────────────────────

fn dec_cfg(c: &Builder, p: &WalkParams, e: usize, en: bool) -> DecCfg {
    let n = dec::Window::new(e, p.w_dec).n();
    let floor = dec::min_room(en);
    let rm = room(c, p.cap).clamp(floor, n + floor);
    DecCfg {
        w: p.w_dec,
        room: rm,
    }
}

fn borrow_amb_disposal(t1: usize) -> bool {
    super::pointadd::knob("SKYCOF_DEC_BORROW_AMB")
        .unwrap_or_else(|| "320,321,322,323,324,331,332,334,336,337".to_owned())
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t1))
}

/// On the exact binding clamp calls, start the already-proved rail-parity loan
/// before materializing ParkTest instead of after it. ParkTest/odometer/decoder
/// do not read either rail, so the released physical ID may host the predicate
/// root and is restored before rail execution resumes.
fn parity_park_disposal(t1: usize) -> bool {
    super::pointadd::knob("SKYCOF_PARK_PARITY_LOAN")
        .unwrap_or_else(|| "320,321,322,323,331".to_owned())
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t1))
}

fn ghost_r0_host_disposal(t1: usize) -> bool {
    super::pointadd::knob("SKYCOF_GHOST_R0_HOST")
        .unwrap_or_else(|| {
            "320,321,322,323,324,327,328,329,330,331,332,334,336,337".to_owned()
        })
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t1))
}

fn virtual_d_amb_disposal(t1: usize) -> bool {
    super::pointadd::knob("SKYCOF_VIRTUAL_D_AMB")
        .unwrap_or_else(|| "320,321,322,323,324,327,328,329,330,332,334,336,337".to_owned())
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t1))
}

fn virtual_d_fresh_amb_fwd_disposal(t1: usize) -> bool {
    super::pointadd::knob("SKYCOF_VIRTUAL_D_FRESH_AMB_FWD")
        .unwrap_or_else(|| "324,332,334".to_owned())
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t1))
}

static R8_FWD_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static R8_REV_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static IMPLICIT_AMB_FWD_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static IMPLICIT_AMB_REV_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

pub(crate) fn reset_r8_dispatch_counts() {
    use std::sync::atomic::Ordering;
    R8_FWD_CALLS.store(0, Ordering::Relaxed);
    R8_REV_CALLS.store(0, Ordering::Relaxed);
    IMPLICIT_AMB_FWD_CALLS.store(0, Ordering::Relaxed);
    IMPLICIT_AMB_REV_CALLS.store(0, Ordering::Relaxed);
}

pub(crate) fn assert_r8_dispatch_counts() {
    use std::sync::atomic::Ordering;
    let fwd = R8_FWD_CALLS.load(Ordering::Relaxed);
    let rev = R8_REV_CALLS.load(Ordering::Relaxed);
    eprintln!("SKYCOF_R8_DISPATCH forward={fwd} reverse={rev}");
    let want = if implicit_r0() { (0, 0) } else { (6, 0) };
    assert_eq!((fwd, rev), want, "R8 dispatcher count drift");
    eprintln!("SKYCOF_IMPLICIT_AMB_DISPATCH forward={} reverse={}",
        IMPLICIT_AMB_FWD_CALLS.load(Ordering::Relaxed),
        IMPLICIT_AMB_REV_CALLS.load(Ordering::Relaxed));
}

/// Materialize only when the real allocator can afford one owner. DecCfg
/// deliberately clamps room upward, so it cannot establish this premise.
fn try_materialized_implicit_amb(
    c: &mut Builder, p: &WalkParams, rails: &Rails, io: &TickIo,
    h: &Hreg, cfg: DecCfg, inverse: bool,
) -> bool {
    if h.is_empty() || room(c, p.cap) == 0 { return false; }
    let dirty = [rails.r1[1], rails.r2[1], rails.r1[2]];
    let live = c.active_qubits();
    let ((), peak) = c.r3_peak(|c| {
        dec::implicit_r0_materialized_or_fixture(c, io, h, cfg, dirty, inverse)
    });
    assert_eq!(c.active_qubits(), live, "materialized ambiguity leaked an owner");
    assert!(peak as usize <= p.cap, "materialized ambiguity peak {peak} exceeds cap {}", p.cap);
    if inverse {
        IMPLICIT_AMB_REV_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    } else {
        IMPLICIT_AMB_FWD_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
    true
}

fn post318_constant_loan() -> bool {
    super::pointadd::knob("SKYCOF_T318_POST_LOAN")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(false)
}

fn recycle_cofzero_tick(t: usize) -> bool {
    super::pointadd::knob("SKYCOF_REV_COFZERO")
        .unwrap_or_else(|| "309,321,322,323,328,334".to_owned())
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t))
}

/// Forward peak rows where the last-use implicit-R0 `isC` owner replaces the
/// otherwise fresh cofactor zero head.  Keep this narrower than the reverse
/// reuse set: reverse-only reuse is valid for any ordinarily allocated head,
/// while every forward-hosted row requires the paired retained-head inverse.
fn rotate_isc_to_cofzero_tick(t: usize) -> bool {
    super::pointadd::knob("SKYCOF_FWD_COFZERO")
        .unwrap_or_else(|| "304,305,309,313,316,317,319,320,321,322,323,324".to_owned())
        .split(',')
        .any(|x| x.trim().parse::<usize>() == Ok(t))
}

fn retained_cofzero_tick(t: usize) -> bool {
    recycle_cofzero_tick(t) || rotate_isc_to_cofzero_tick(t)
}

thread_local! {
    static ENCODED_REFERENCE_ORDINARY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(crate) fn with_encoded_reference_ordinary<R>(body: impl FnOnce() -> R) -> R {
    ENCODED_REFERENCE_ORDINARY.with(|flag| {
        let old = flag.replace(true);
        let out = body();
        flag.set(old);
        out
    })
}

fn encoded_sign_tick(t: usize, w: &TickWidths) -> bool {
    if ENCODED_REFERENCE_ORDINARY.with(|flag| flag.get()) {
        if matches!(t, 318 | 321) {
            eprintln!("SKYCOF_ENCODED_PATH tick={t} mode=ordinary-reference");
        }
        return false;
    }
    if !matches!(t, 318 | 321) { return false; }
    assert!(implicit_r0(), "encoded-sign rows are frozen for implicit R0");
    assert_eq!(super::pointadd::params().walk.cap, 1037);
    let want = match t { 318 => (55,55,54,55), 321 => (53,53,52,53), _ => unreachable!() };
    assert_eq!((w.wsw,w.wad,w.post_r1,w.post_r2), want,
        "encoded-sign frozen geometry drift at tick {t}");
    eprintln!("SKYCOF_ENCODED_PATH tick={t} mode=encoded");
    true
}

fn sign_positive_tick(t:usize,w:&TickWidths)->bool{
    if ENCODED_REFERENCE_ORDINARY.with(|flag|flag.get()){return false;}
    let want=match t{
        322=>(53,52,52,52),323=>(52,52,51,52),324=>(52,52,51,51),
        335=>(47,47,46,46),_=>return false};
    assert_eq!((w.wsw,w.wad,w.post_r1,w.post_r2),want,"positive-role geometry drift {t}");
    eprintln!("SKYCOF_SIGN_ROLE tick={t} mode=positive");true
}

fn sign_closed_tick(t:usize,w:&TickWidths)->bool{
    if ENCODED_REFERENCE_ORDINARY.with(|flag|flag.get()){return false;}
    if t!=333{return false;}
    assert_eq!((w.wsw,w.wad,w.post_r1,w.post_r2),(49,49,48,48));
    eprintln!("SKYCOF_SIGN_ROLE tick=333 mode=closed");true
}

fn sign_owner_frame(c: &mut Builder, current_a: Q, source_top: Q, target_top: Q) {
    c.x(current_a);
    c.cx(target_top, source_top);
    c.ccx(current_a, source_top, target_top);
    c.cx(target_top, source_top);
    c.x(current_a);
}

#[allow(clippy::too_many_arguments)]
fn dispose_fwd_sign_history_fixture(
    c: &mut Builder, p: &WalkParams, env: &Envelope, t1: usize,
    current_a: Q, previous_typ: Q, rails: &mut Rails, cof: &Cof,
    h: &mut Hreg, odo: &[Q], borrower: Option<Q>,
) -> Q {
    assert_eq!(c.tracked_condition_depth(),Some(0),"sign/history loan needs empty condition stack");
    assert!(matches!(t1 + 1, 322 | 323 | 324 | 335));
    let old_h = if t1 == 0 { 0 } else { env.h[t1 - 1] };
    assert_eq!(h.len(), old_h);
    let delta = env.h[t1] - old_h;
    assert!(matches!((t1 + 1, delta), (322,1) | (323,1) | (324,1) | (335,3)));
    let source_top = *rails.r1.last().unwrap();
    let target_top = *rails.r2.last().unwrap();
    assert!(current_a != source_top && current_a != target_top);
    assert!(previous_typ != source_top && previous_typ != target_top);
    sign_owner_frame(c, current_a, source_top, target_top);
    let lender = rails.r2.pop().unwrap();
    assert_eq!(lender, target_top);
    c.release_clean(lender);
    c.reacquire(lender);
    h.wires.push(lender); // exact first grown H slot
    h.grow_to(c, env.h[t1]);
    dispose_fwd(c, p, env, t1, previous_typ, rails, cof, h, odo, borrower, None);
    // previous_typ was released at the final instruction of dispose_fwd.
    c.reacquire(previous_typ);
    rails.r2.push(previous_typ);
    sign_owner_frame(c, current_a, source_top, previous_typ);
    lender
}

#[allow(clippy::too_many_arguments)]
fn dispose_rev_sign_history_fixture(
    c: &mut Builder, p: &WalkParams, env: &Envelope, t1: usize,
    current_a: Q, rails: &mut Rails, cof: &Cof, h: &mut Hreg,
    odo: &[Q], borrower: Option<Q>,
) -> (Q, Q) {
    assert_eq!(c.tracked_condition_depth(),Some(0),"sign/history inverse needs empty condition stack");
    assert!(matches!(t1 + 1, 322 | 323 | 324 | 335));
    let old_h = if t1 == 0 { 0 } else { env.h[t1 - 1] };
    let delta = env.h[t1] - old_h;
    assert!(matches!((t1 + 1, delta), (322,1) | (323,1) | (324,1) | (335,3)));
    assert_eq!(h.len(), env.h[t1]);
    let lender = h.wires[old_h];
    let source_top = *rails.r1.last().unwrap();
    let type_owner = *rails.r2.last().unwrap();
    sign_owner_frame(c, current_a, source_top, type_owner);
    assert_eq!(rails.r2.pop(), Some(type_owner));
    c.release_clean(type_owner);
    c.reacquire(type_owner); // pre-owned zero output for dispose_rev
    let restored_typ = dispose_rev_into(
        c, p, env, t1, rails, cof, h, odo, borrower, type_owner);
    assert_eq!(restored_typ, type_owner);
    assert!(!h.wires.contains(&lender));
    c.reacquire(lender);
    rails.r2.push(lender);
    sign_owner_frame(c, current_a, source_top, lender);
    (restored_typ, lender)
}

#[allow(clippy::too_many_arguments)]
fn dispose_fwd_sign_closed_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,t1:usize,current_a:Q,previous_typ:Q,
    rails:&mut Rails,cof:&Cof,h:&mut Hreg,odo:&[Q],borrower:Option<Q>,
)->Q{
    assert_eq!(c.tracked_condition_depth(),Some(0),"closed sign loan needs empty condition stack");
    assert_eq!(t1+1,333);assert_eq!(env.h[t1],env.h[t1-1]);
    let live=c.active_qubits();let source_top=*rails.r1.last().unwrap();
    let lender=*rails.r2.last().unwrap();sign_owner_frame(c,current_a,source_top,lender);
    assert_eq!(rails.r2.pop(),Some(lender));c.release_clean(lender);
    dispose_fwd(c,p,env,t1,previous_typ,rails,cof,h,odo,borrower,None);
    assert_eq!(c.active_qubits()+2,live,"delta0 forward must have L and old T free");
    c.reacquire(lender);rails.r2.push(lender);sign_owner_frame(c,current_a,source_top,lender);
    lender
}

#[allow(clippy::too_many_arguments)]
fn dispose_rev_sign_closed_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,t1:usize,current_a:Q,expected_type:Option<Q>,
    rails:&mut Rails,cof:&Cof,h:&mut Hreg,odo:&[Q],borrower:Option<Q>,
)->Q{
    assert_eq!(c.tracked_condition_depth(),Some(0),"closed sign inverse needs empty condition stack");
    assert_eq!(t1+1,333);assert_eq!(env.h[t1],env.h[t1-1]);
    let typ=c.alloc_qubit();
    if let Some(expected)=expected_type{assert_eq!(typ,expected,"delta0 previous-type ID drift");}
    let source_top=*rails.r1.last().unwrap();let lender=*rails.r2.last().unwrap();
    sign_owner_frame(c,current_a,source_top,lender);assert_eq!(rails.r2.pop(),Some(lender));
    c.release_clean(lender);
    let out=dispose_rev_into(c,p,env,t1,rails,cof,h,odo,borrower,typ);assert_eq!(out,typ);
    c.reacquire(lender);rails.r2.push(lender);sign_owner_frame(c,current_a,source_top,lender);
    typ
}

fn assert_cofzero_disjoint(
    q: Q,
    typ: Q,
    rails: &Rails,
    cof: &Cof,
    h: &Hreg,
    odo: &[Q],
) {
    assert!(q != typ);
    assert!(!rails.r1.contains(&q) && !rails.r2.contains(&q));
    assert!(!cof.s.contains(&q) && !cof.r.contains(&q));
    assert!(!h.wires.contains(&q) && !odo.contains(&q));
}

/// Forward: erase `typ` (letter of tick `t1`) against the cofactor post-state of tick `t1`;
/// rails are post(t1 + 1).
#[allow(clippy::too_many_arguments)]
fn dispose_fwd(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    t1: usize,
    typ: Q,
    rails: &Rails,
    cof: &Cof,
    h: &mut Hreg,
    odo: &[Q],
    borrower: Option<Q>,
    constant_loans: Option<[Q; 2]>,
) {
    h.grow_to(c, env.h[t1]);
    let mut typ_released = false;
    if t1 == 0 {
        with_rail_parity_loan(c, rails, |c| dec::first_tick(c, &cof.s, typ, None));
    } else if env.cof[t1] == CLAMP {
        trace_step(c, "pre-park");
        let wide_loan = parity_park_disposal(t1);
        let run = |c: &mut Builder| {
          let zt = ParkTest::compute(c, &cof.r, &cof.s, p.park_j, p.cap);
          trace_step(c, "parktest");
          let body = |c: &mut Builder| {
            ghost_odo_prime_xor(c, p, cof, zt.z, typ,
                !implicit_r0() && ghost_r0_host_disposal(t1));
            let ov = odo_view(p, cof, odo);
            if implicit_r0() {
                odo_fwd(c, zt.z, typ, ov, &cof.s, p.cap)
            } else {
                with_odo_r0_loan(c, cof.r[0], zt.z, typ, ov, |c| {
                    odo_fwd(c, zt.z, typ, ov, &cof.s, p.cap)
                });
            }
            trace_step(c, "odo");
            c.x(zt.z);
            let cfg = dec_cfg(c, p, env.cof[t1], true);
            let io = TickIo {
                s: &cof.s,
                r: &cof.r,
                e: env.cof[t1],
                en: Some(zt.z),
                typ,
                cflag: None,
                park: None,
            };
            if implicit_r0() {
                if cfg.room == dec::min_room(true) {
                    let dirty = [rails.r1[1], rails.r2[1], rails.r1[2]];
                    let live = c.active_qubits();
                    if !try_materialized_implicit_amb(c, p, rails, &io, h, cfg, false) {
                        dec::push_implicit_r0_virtual_or_fixture(c, &io, h, cfg, dirty);
                    }
                    assert_eq!(c.active_qubits(), live);
                } else {
                    dec::push_implicit_r0_alias_enabled_fixture(c, &io, h, cfg);
                }
            } else if virtual_d_fresh_amb_fwd_disposal(t1) {
                assert!(virtual_d_amb_disposal(t1), "R8 must replace an existing R7 call");
                assert_eq!(p.cap, 1040);
                assert_eq!(env.cof[t1], CLAMP);
                assert_eq!(cfg.room, dec::min_room(true), "R8 requires floor room");
                assert_eq!(c.tracked_condition_depth(), Some(0));
                let dirty = rails.r1[1];
                assert!(dirty != rails.r1[0] && !rails.r2.contains(&dirty));
                assert!(dirty != zt.z && dirty != typ);
                assert!(!cof.s.contains(&dirty) && !cof.r.contains(&dirty));
                assert!(!h.wires.contains(&dirty) && !odo.contains(&dirty));
                let live = c.active_qubits();
                assert!(live <= 1039, "R8 entry has no fresh-amb room: {live}");
                let ((), peak) = c.r3_peak(|c| {
                    dec::push_virtual_d_fresh_amb_fixture(c, &io, h, cfg, dirty)
                });
                assert_eq!(c.active_qubits(), live, "R8 forward leaked an owner");
                assert!(peak <= 1040, "R8 forward peak {peak}");
                R8_FWD_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            } else if virtual_d_amb_disposal(t1) && cfg.room == dec::min_room(true) {
                let dirty = [rails.r1[1], rails.r2[1]];
                assert_ne!(dirty[0], dirty[1]);
                assert_eq!(cfg.room, dec::min_room(true), "R7 binding room changed");
                let live = c.active_qubits();
                dec::push_virtual_d_amb_fixture(c, &io, h, cfg, dirty);
                assert_eq!(c.active_qubits(), live, "R7 forward allocated an owner");
            } else if borrow_amb_disposal(t1) {
                let q = borrower.expect("binding decoder needs current-tick isc borrower");
                dec::push_borrow_amb(c, &io, h, cfg, q);
            } else {
                dec::push(c, &io, h, cfg);
            }
            trace_step(c, "dec");
            c.x(zt.z);
          };
          if wide_loan {
              body(c);
          } else {
              with_rail_parity_loan(c, rails, body);
          }
          zt.uncompute(c);
          trace_step(c, "unpark");
        };
        if wide_loan {
            with_rail_parity_loan(c, rails, run);
        } else {
            run(c);
        }
    } else {
        let mut body = |c: &mut Builder| {
            if let Some([qs, qr]) = constant_loans {
                assert!(borrower != Some(qs) && borrower != Some(qr));
                assert!(typ != qs && typ != qr);
                assert!(!rails.r1.contains(&qs) && !rails.r2.contains(&qs));
                assert!(!rails.r1.contains(&qr) && !rails.r2.contains(&qr));
                assert!(!h.wires.contains(&qs) && !h.wires.contains(&qr));
                assert!(!odo.contains(&qs) && !odo.contains(&qr));
                let live = c.active_qubits();
                c.reacquire(qs);
                c.reacquire(qr);
                c.x(qr);
                c.set_avoid(&[]);
                assert_eq!(c.active_qubits(), live + 2, "R3 repayment count");
            }
            let cfg = dec_cfg(c, p, env.cof[t1], false);
            if implicit_r0() {
                let n = dec::Window::new(env.cof[t1], p.w_dec).n();
                if n >= 2 && cfg.room > dec::min_room(false) {
                    let io = TickIo { s:&cof.s, r:&cof.r, e:env.cof[t1], en:None,
                        typ, cflag:None, park:None };
                    dec::push_implicit_r0_alias_noen_fixture(c, &io, h, cfg);
                } else {
                    let io=TickIo{s:&cof.s,r:&cof.r,e:env.cof[t1],en:None,typ,cflag:None,park:None};
                    if !try_materialized_implicit_amb(c, p, rails, &io, h, cfg, false) {
                        dec::push_implicit_r0_virtual_or_noen_fixture(c,&io,h,cfg,
                            [rails.r1[1],rails.r2[1]]);
                    }
                }
            } else if borrow_amb_disposal(t1) {
                let io = TickIo { s:&cof.s, r:&cof.r, e:env.cof[t1], en:None,
                    typ, cflag:None, park:None };
                let q = borrower.expect("binding decoder needs current-tick isc borrower");
                dec::push_borrow_amb(c, &io, h, cfg, q)
            } else {
                let io = TickIo { s:&cof.s, r:&cof.r, e:env.cof[t1], en:None,
                    typ, cflag:None, park:None };
                dec::push(c, &io, h, cfg)
            }
            if constant_loans.is_some() {
                c.release_clean(typ);
                typ_released = true;
            }
        };
        if constant_loans.is_some() {
            let (a, q) = (rails.r1[0], rails.r2[0]);
            assert_ne!(a, q);
            assert_eq!(c.tracked_condition_depth(), Some(0));
            let live = c.active_qubits();
            c.cx(a, q);
            c.x(q);
            c.release_clean(q);
            body(c);
            assert_eq!(c.active_qubits(), live, "R3 decoder repayment/typ balance");
            c.reacquire(q);
            c.x(q);
            c.cx(a, q);
            assert_eq!(c.active_qubits(), live + 1, "R3 decoder final live delta");
        } else {
            with_rail_parity_loan(c, rails, body);
        }
    }
    if !typ_released {
        c.release_clean(typ);
    }
}

/// Reverse: re-create the letter of tick `t1` (exact inverse of [`dispose_fwd`]).
#[allow(clippy::too_many_arguments)]
fn dispose_rev(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    t1: usize,
    rails: &Rails,
    cof: &Cof,
    h: &mut Hreg,
    odo: &[Q],
    borrower: Option<Q>,
) -> Q {
    dispose_rev_impl(c, p, env, t1, rails, cof, h, odo, borrower, None)
}

#[allow(clippy::too_many_arguments)]
fn dispose_rev_into(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    t1: usize,
    rails: &Rails,
    cof: &Cof,
    h: &mut Hreg,
    odo: &[Q],
    borrower: Option<Q>,
    typ: Q,
) -> Q {
    dispose_rev_impl(c, p, env, t1, rails, cof, h, odo, borrower, Some(typ))
}

#[allow(clippy::too_many_arguments)]
fn dispose_rev_impl(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    t1: usize,
    rails: &Rails,
    cof: &Cof,
    h: &mut Hreg,
    odo: &[Q],
    borrower: Option<Q>,
    typ_out: Option<Q>,
) -> Q {
    h.shrink_to(c, env.h[t1]);
    let typ = typ_out.unwrap_or_else(|| c.alloc_qubit());
    assert!(!rails.r1.contains(&typ) && !rails.r2.contains(&typ));
    assert!(!cof.s.contains(&typ) && !cof.r.contains(&typ));
    assert!(!h.wires.contains(&typ) && !odo.contains(&typ));
    if t1 == 0 {
        with_rail_parity_loan(c, rails, |c| dec::first_tick(c, &cof.s, typ, None));
    } else if env.cof[t1] == CLAMP {
        let wide_loan = parity_park_disposal(t1);
        let run = |c: &mut Builder| {
          let zt = ParkTest::compute(c, &cof.r, &cof.s, p.park_j, p.cap);
          let body = |c: &mut Builder| {
            c.x(zt.z);
            let cfg = dec_cfg(c, p, env.cof[t1], true);
            let io = TickIo {
                s: &cof.s,
                r: &cof.r,
                e: env.cof[t1],
                en: Some(zt.z),
                typ,
                cflag: None,
                park: None,
            };
            if implicit_r0() {
                if cfg.room == dec::min_room(true) {
                    let dirty = [rails.r1[1], rails.r2[1], rails.r1[2]];
                    let live = c.active_qubits();
                    if !try_materialized_implicit_amb(c, p, rails, &io, h, cfg, true) {
                        dec::pop_implicit_r0_virtual_or_fixture(c, &io, h, cfg, dirty);
                    }
                    assert_eq!(c.active_qubits(), live);
                } else {
                    dec::pop_implicit_r0_alias_enabled_fixture(c, &io, h, cfg);
                }
            } else if virtual_d_amb_disposal(t1) && cfg.room == dec::min_room(true) {
                let dirty = [rails.r1[1], rails.r2[1]];
                assert_ne!(dirty[0], dirty[1]);
                assert_eq!(cfg.room, dec::min_room(true), "R7 binding room changed");
                let live = c.active_qubits();
                dec::pop_virtual_d_amb_fixture(c, &io, h, cfg, dirty);
                assert_eq!(c.active_qubits(), live, "R7 reverse allocated an owner");
            } else if borrow_amb_disposal(t1) {
                let q = borrower.expect("binding decoder needs current-tick isc borrower");
                dec::pop_borrow_amb(c, &io, h, cfg, q);
            } else {
                dec::pop(c, &io, h, cfg);
            }
            c.x(zt.z);
            let ov = odo_view(p, cof, odo);
            if implicit_r0() {
                odo_rev(c, zt.z, typ, ov, &cof.s, p.cap)
            } else {
                with_odo_r0_loan(c, cof.r[0], zt.z, typ, ov, |c| {
                    odo_rev(c, zt.z, typ, ov, &cof.s, p.cap)
                });
            }
            ghost_odo_prime_xor(c, p, cof, zt.z, typ,
                !implicit_r0() && ghost_r0_host_disposal(t1));
          };
          if wide_loan {
              body(c);
          } else {
              with_rail_parity_loan(c, rails, body);
          }
          zt.uncompute(c);
        };
        if wide_loan {
            with_rail_parity_loan(c, rails, run);
        } else {
            run(c);
        }
    } else {
        with_rail_parity_loan(c, rails, |c| {
            let cfg = dec_cfg(c, p, env.cof[t1], false);
            if implicit_r0() {
                let n = dec::Window::new(env.cof[t1], p.w_dec).n();
                if n >= 2 && cfg.room > dec::min_room(false) {
                    let io = TickIo { s:&cof.s, r:&cof.r, e:env.cof[t1], en:None,
                        typ, cflag:None, park:None };
                    dec::pop_implicit_r0_alias_noen_fixture(c, &io, h, cfg);
                } else {
                    let io=TickIo{s:&cof.s,r:&cof.r,e:env.cof[t1],en:None,typ,cflag:None,park:None};
                    if !try_materialized_implicit_amb(c, p, rails, &io, h, cfg, true) {
                        dec::pop_implicit_r0_virtual_or_noen_fixture(c,&io,h,cfg,
                            [rails.r1[1],rails.r2[1]]);
                    }
                }
            } else {
                let io = TickIo { s:&cof.s, r:&cof.r, e:env.cof[t1], en:None,
                    typ, cflag:None, park:None };
                dec::pop(c, &io, h, cfg)
            }
        });
    }
    // `push` grew the history from the preceding public-clock capacity to
    // `env.h[t1]`.  Once its exact inverse and all consumers of the popped
    // cell have closed, the now-zero padding is dead before the inverse rail
    // cell.  Restore the entry capacity here, symmetrically with the forward
    // pre-push state, instead of retaining zeros through `rail_rev`.
    let h_prev = if t1 == 0 { 0 } else { env.h[t1 - 1] };
    h.shrink_to(c, h_prev);
    typ
}

/// Research: tick-boundary snapshots (the ops so far plus the walk registers), recorded only when a probe
/// enables the recorder. Order: rails r1, r2, cof s, r, history, odometer, typ.
pub type Snap = (String, Vec<crate::circuit::Op>, Vec<Vec<Q>>);
thread_local! {
    pub static SNAPS: std::cell::RefCell<Option<Vec<Snap>>> = const { std::cell::RefCell::new(None) };
}

fn snap(
    c: &mut Builder,
    tag: String,
    rails: &Rails,
    cof: &Cof,
    h: &Hreg,
    odo: &[Q],
    typ: Option<Q>,
) {
    SNAPS.with(|s| {
        if let Some(v) = s.borrow_mut().as_mut() {
            let ops = c.take_ops();
            v.push((
                tag,
                ops,
                vec![
                    rails.r1.clone(),
                    rails.r2.clone(),
                    cof.s.clone(),
                    cof.r.clone(),
                    h.wires.clone(),
                    odo.to_vec(),
                    typ.into_iter().collect(),
                ],
            ));
        }
    });
}

fn trace_step(c: &mut Builder, what: &str) {
    if super::pointadd::knob_flag("SKYCOF_STEP_TRACE") {
        let pk = c.take_win_peak();
        eprintln!("SKYCOF_STEP {what} live={} peak={pk}", c.active_qubits());
    }
}

/// Research-only per-component expected-Toffoli delta. This observes the
/// phase-report counters and therefore cannot alter the emitted operation
/// stream.
fn trace_cost(c: &Builder, dir: &str, t: usize, what: &str, before: f64) {
    if super::pointadd::knob_flag("SKYCOF_PART_COST_TRACE") {
        let after = c.report_totals().map_or(before, |x| x.1);
        eprintln!("SKYCOF_PART_COST {dir} {t} {what} {:.3}", after - before);
    }
}

/// Phase label hook: per-tick trace under `SKYCOF_TICK_TRACE` (research).
fn trace_tick(c: &mut Builder, dir: &str, t: usize) {
    if super::pointadd::knob_flag("SKYCOF_TICK_TRACE") {
        let pk = c.take_win_peak();
        eprintln!(
            "SKYCOF_TICK {dir} {t} live={} peak={pk} ops={}",
            c.active_qubits(),
            c.op_count()
        );
    }
}

// ─── the walk ───────────────────────────────────────────────────────────────────────────────────

/// Live state at a public forward cut.  This is the integration seam for a
/// packed tail: every quantum owner needed by the exact reverse is explicit,
/// while the caller-owned numerator remains outside this object and live.
pub struct ActiveWalk {
    pub rails: Rails,
    pub cof: Cof,
    pub h: Hreg,
    pub odo: Vec<Q>,
    pub typ: Option<Q>,
    pub next_t: usize,
    pub(crate) prev: Vec<PrevWidths>,
    pub(crate) tops: Vec<TopFate>,
}

impl ActiveWalk {
    /// Persistent GCD state at the cut, excluding caller-owned passengers.
    pub fn live_width(&self) -> usize {
        self.rails.r1.len()
            + self.rails.r2.len()
            + self.cof.s.len()
            + self.cof.r.len()
            + self.h.wires.len()
            + self.odo.len()
            + usize::from(self.typ.is_some())
    }
}

fn forward_ticks(c: &mut Builder, p: &WalkParams, env: &Envelope, st: &mut ActiveWalk, end: usize) {
    assert!(st.next_t <= end && end <= p.r);
    let mut constant_loans: Option<[Q; 2]> = None;
    for t in st.next_t..end {
        let w = env.widths(t);
        let encoded_sign = encoded_sign_tick(t, &w);
        let positive_role = sign_positive_tick(t, &w);
        let closed_role = sign_closed_tick(t, &w);
        st.prev.push(PrevWidths {
            r1: st.rails.r1.len(),
            r2: st.rails.r2.len(),
            cof: st.cof.s.len(),
        });
        trace_step(c, "tick-start");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        let (typ_t, isc, _) = if positive_role && t == 324 {
            let tp=st.typ.expect("tick324 contract role needs previous typ");
            tick::rail_fwd_normalized_contract324_fixture(c,&mut st.rails,tp,&w,Some(p.cap))
        } else if encoded_sign {
            let tp = st.typ.expect("encoded-sign tick needs previous typ");
            tick::rail_fwd_encoded_sign_fixture(
                c, &mut st.rails, tp, &w, Some(p.cap))
        } else if t == 319 {
            if let Some(loans) = constant_loans {
                tick::rail_fwd_micro_signext_loans(
                    c,
                    &mut st.rails,
                    st.typ,
                    &w,
                    Some(p.cap),
                    loans,
                )
            } else {
                tick::rail_fwd_micro(
                    c,
                    &mut st.rails,
                    st.typ,
                    &w,
                    Some(p.cap),
                    if implicit_r0() { None } else { Some(st.cof.r[0]) },
                    Some(t),
                )
            }
        } else {
            tick::rail_fwd_micro(
                c,
                &mut st.rails,
                st.typ,
                &w,
                Some(p.cap),
                if implicit_r0() { None } else { Some(st.cof.r[0]) },
                Some(t),
            )
        };
        trace_cost(c, "fwd", t, "rail", t0);
        trace_step(c, "rail");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        if let Some(tp) = st.typ {
            if positive_role {
                dispose_fwd_sign_history_fixture(c,p,env,t-1,typ_t,tp,&mut st.rails,
                    &st.cof,&mut st.h,&st.odo,Some(isc));
            } else if closed_role {
                dispose_fwd_sign_closed_fixture(c,p,env,t-1,typ_t,tp,&mut st.rails,
                    &st.cof,&mut st.h,&st.odo,Some(isc));
            } else {
                dispose_fwd(c,p,env,t-1,tp,&st.rails,&st.cof,&mut st.h,&st.odo,
                    Some(isc),constant_loans);
            }
            if constant_loans.is_some() {
                assert_eq!(t, 319, "R3 constants repaid at wrong tick");
                constant_loans = None;
            }
        }
        trace_cost(c, "fwd", t, "decoder", t0);
        trace_step(c, "dispose");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        let retained_zero_head = implicit_r0() && !encoded_sign && rotate_isc_to_cofzero_tick(t);
        if encoded_sign {
            let _ = tick::cof_fwd_at_implicit_r0_encoded_sign_fixture(
                c, &mut st.cof, typ_t, isc, &mut st.rails.r1, &mut st.rails.r2,
                &w, Some(p.cap), t);
        } else if retained_zero_head {
            tick::cof_fwd_at_implicit_r0_zero_head(
                c, &mut st.cof, typ_t, isc, &w, Some(p.cap), t);
        } else if implicit_r0() {
            tick::cof_fwd_at_implicit_r0(c, &mut st.cof, typ_t, isc, &w, Some(p.cap), t);
        } else {
            tick::cof_fwd_at(c, &mut st.cof, typ_t, isc, &w, Some(p.cap), t);
        }
        trace_cost(c, "fwd", t, "cofactor", t0);
        trace_step(c, "cof");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        if !retained_zero_head && !encoded_sign {
            tick::erase_isc(c, &st.cof, typ_t, isc);
        }
        let r_logical = st.cof.r.len() + usize::from(implicit_r0());
        let fate = if st.cof.s.len() > r_logical {
            fold(c, &mut st.cof, p);
            TopFate::Folded
        } else {
            TopFate::None
        };
        trace_cost(c, "fwd", t, "erase_fold", t0);
        st.tops.push(fate);
        if !implicit_r0() && t == 318 && end > 319 && post318_constant_loan() {
            assert_eq!(fate, TopFate::None, "R3 tick318 crossed a fold");
            assert_eq!(st.tops.get(317), Some(&TopFate::None));
            let qs = st.cof.s[0];
            let qr = st.cof.r[0];
            assert_ne!(qs, qr);
            assert!(!st.rails.r1.contains(&qs) && !st.rails.r2.contains(&qs));
            assert!(!st.rails.r1.contains(&qr) && !st.rails.r2.contains(&qr));
            c.release_clean(qs);
            c.x(qr);
            c.release_clean(qr);
            c.set_avoid(&[qs, qr]);
            constant_loans = Some([qs, qr]);
        }
        st.typ = Some(typ_t);
        st.next_t = t + 1;
        trace_tick(c, "fwd", t);
        snap(
            c,
            format!("F{t}"),
            &st.rails,
            &st.cof,
            &st.h,
            &st.odo,
            st.typ,
        );
    }
    assert!(constant_loans.is_none(), "R3 constants left parked across a public cut");
}

/// Execute the exact public-layout prefix and stop at `cut` before tick
/// `cut`.  No caller-owned passenger is allocated or released here.
pub fn forward_to(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    d: &[Q],
    cut: usize,
) -> ActiveWalk {
    assert!(cut <= p.r);
    check_ghost_odo(p, env);
    let rails = seed(c, d, p.cap);
    let cof = Cof {
        s: c.alloc_qubits(2),
        r: c.alloc_qubits(if implicit_r0() { 1 } else { 2 }),
    };
    if !implicit_r0() { c.x(cof.r[0]); }
    let mut st = ActiveWalk {
        rails,
        cof,
        h: Hreg::new(),
        odo: c.alloc_qubits(if ghost_odo() { 0 } else { p.odo_bits }),
        typ: None,
        next_t: 0,
        prev: Vec::with_capacity(p.r),
        tops: Vec::with_capacity(p.r),
    };
    forward_ticks(c, p, env, &mut st, cut);
    st
}

/// Resume an [`ActiveWalk`] through the endpoint using the original layout.
/// A packed backend will implement the same input/output contract.
pub fn forward_from(c: &mut Builder, p: &WalkParams, env: &Envelope, mut st: ActiveWalk) -> Parked {
    let r = p.r;
    forward_ticks(c, p, env, &mut st, r);
    let ActiveWalk {
        rails,
        cof,
        mut h,
        mut odo,
        typ,
        prev,
        tops,
        ..
    } = st;
    dispose_fwd(
        c,
        p,
        env,
        r - 1,
        typ.unwrap(),
        &rails,
        &cof,
        &mut h,
        &odo,
        None,
        None,
    );
    // parked rails (R1, R2) = (0, 1) and r = p: classical constants
    let (post_r1, post_r2) = env.post_widths(r - 1);
    assert_eq!(rails.r1.len(), post_r1);
    assert_eq!(rails.r2.len(), post_r2);
    c.x(rails.r2[0]);
    c.free_vec(&rails.r1);
    c.free_vec(&rails.r2);
    assert_eq!(cof.r.len() + usize::from(implicit_r0()), N);
    assert_eq!(cof.s.len(), N);
    let pv = crate::point_add::SECP256K1_P;
    if ghost_odo() {
        assert!(odo.is_empty());
        let start = GHOST_ODO_START - usize::from(implicit_r0());
        odo = cof.r[start..start + p.odo_bits].to_vec();
    }
    for i in usize::from(implicit_r0())..N {
        if ghost_odo() && (GHOST_ODO_START..GHOST_ODO_START + p.odo_bits).contains(&i) {
            // These owners contain the endpoint counter, not prime padding.
            continue;
        }
        if pv.bit(i) {
            c.x(cof.r[i - usize::from(implicit_r0())]);
        }
        if ghost_odo() {
            c.free(cof.r[i - usize::from(implicit_r0())]);
        }
    }
    if !ghost_odo() {
        c.free_vec(&cof.r);
    }
    Parked {
        s: cof.s,
        h,
        odo,
        prev,
        tops,
    }
}

/// Forward walk on `d` (its wires become R2). Returns the parked state.
pub fn forward(c: &mut Builder, p: &WalkParams, env: &Envelope, d: &[Q]) -> Parked {
    let st = forward_to(c, p, env, d, 0);
    forward_from(c, p, env, st)
}

/// Exact inverse of [`forward_to`].  This is the integration counterpart of a
/// packed suffix seam: after that suffix is undone, the public prefix can be
/// reversed directly without constructing the parked endpoint.
pub fn backward_from_active(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    st: ActiveWalk,
) -> Vec<Q> {
    let ActiveWalk {
        mut rails,
        mut cof,
        mut h,
        odo,
        typ,
        next_t,
        prev,
        tops,
    } = st;
    assert!(next_t > 0 && next_t <= p.r);
    assert_eq!(prev.len(), next_t);
    assert_eq!(tops.len(), next_t);
    let mut typ = typ.expect("nonempty prefix has a current type bit");
    for t in (0..next_t).rev() {
        let w = env.widths(t);
        let positive_role=sign_positive_tick(t,&w);
        let closed_role=sign_closed_tick(t,&w);
        if !implicit_r0() && t == 328 && recycle_cofzero_tick(t) {
            assert_eq!(tops[t], TopFate::Folded, "tick328 role order requires unfold first");
            assert!(w.post_r1 < w.wad, "tick328 sign-extension host geometry drifted");
        }
        match tops[t] {
            TopFate::Folded => unfold(c, &mut cof, p),
            TopFate::Freed => {
                let q = c.alloc_qubit();
                cof.s.push(q);
            }
            TopFate::None => {}
        }
        trace_step(c, "rev-unfold");
        let encoded_sign = encoded_sign_tick(t, &w);
        let recycle_zero = !encoded_sign && retained_cofzero_tick(t);
        let isc = if encoded_sign {
            let (q, _) = tick::cof_rev_at_implicit_r0_encoded_sign_fixture(
                c, &mut cof, typ, &mut rails.r1, &mut rails.r2,
                prev[t].cof, Some(p.cap), t);
            q
        } else if recycle_zero {
            tick::isc_recompute_from_zero_head(c, &mut cof, typ)
        } else {
            tick::isc_recompute(c, &cof, typ)
        };
        if encoded_sign {
            // The paired encoded cofactor inverse above already removed the
            // ordinary fresh head and undid the C-controlled cell.
        } else if recycle_zero {
            assert_cofzero_disjoint(isc, typ, &rails, &cof, &h, &odo);
            if implicit_r0() {
                tick::cof_rev_at_implicit_r0_zero_head(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap), t);
            } else {
                tick::cof_rev_at_zero_head(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap), t);
            }
        } else if implicit_r0() {
            tick::cof_rev_at_implicit_r0(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap), t);
        } else {
            tick::cof_rev_at(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap), t);
        }
        trace_step(c, "rev-cof");
        let tprev = if t >= 1 {
            Some(if positive_role {
                dispose_rev_sign_history_fixture(c,p,env,t-1,typ,&mut rails,&cof,
                    &mut h,&odo,Some(isc)).0
            } else if closed_role {
                dispose_rev_sign_closed_fixture(c,p,env,t-1,typ,None,&mut rails,&cof,
                    &mut h,&odo,Some(isc))
            } else {
                dispose_rev(c,p,env,t-1,&rails,&cof,&mut h,&odo,Some(isc))
            })
        } else {
            None
        };
        trace_step(c, "rev-dec");
        if positive_role && t==324 {
            let tp=tprev.expect("promoted tick324 needs previous typ");
            tick::rail_rev_normalized_contract324_fixture(c,&mut rails,typ,isc,tp,&w,
                (prev[t].r1,prev[t].r2),Some(p.cap));
        } else if encoded_sign {
            let tp = tprev.expect("encoded-sign inverse needs previous typ");
            tick::rail_rev_encoded_sign_fixture(
                c, &mut rails, typ, tp, &w, (prev[t].r1, prev[t].r2), Some(p.cap));
        } else if implicit_r0() && t == 324 {
            let tp=tprev.expect("implicit rail324 needs previous typ");
            let park=&cof.r[cof.r.len()-14..];let dirty=&cof.s[1..14];
            tick::rail_rev_dirty_s0_implicit(c,&mut rails,typ,isc,tp,cof.s[0],park,dirty,
                w.wad,p.cap);
        } else {
            tick::rail_rev_micro(c,&mut rails,typ,isc,tprev,&w,(prev[t].r1,prev[t].r2),
                Some(p.cap),if implicit_r0(){None}else{Some(cof.r[0])},Some(t));
        }
        trace_step(c, "rev-rail");
        if let Some(tq) = tprev {
            typ = tq;
        }
    }
    assert_eq!(cof.s.len(), 2);
    if !implicit_r0() { c.x(cof.r[0]); }
    c.free_vec(&cof.s);
    c.free_vec(&cof.r);
    h.shrink_to(c, 0);
    c.free_vec(&odo);
    unseed(c, rails, p.cap)
}

/// Research-only source-bound roundtrip for the encoded-sign/cofactor seam.
/// It executes one real public tick's rail producer, actual default disposal,
/// implicit-R0 cofactor update and fold, then a separately ordered inverse.
/// Production traversal never calls this function.
pub(crate) struct EncodedSeamView {
    pub r1: Vec<Q>, pub r2: Vec<Q>, pub s: Vec<Q>, pub r: Vec<Q>,
    pub h: Vec<Q>, pub odo: Vec<Q>, pub typ: Q,
    pub pre_fold_s: Vec<Q>,
}

pub(crate) fn encoded_sign_seam_roundtrip_fixture(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    mut st: ActiveWalk,
    t: usize,
) -> (ActiveWalk, EncodedSeamView, B, usize, usize, usize, u32) {
    assert!(matches!(t, 318 | 321), "encoded seam fixture scope drift");
    assert_eq!(st.next_t, t);
    assert_eq!(p.cap, 1037);
    assert!(implicit_r0());
    let w = env.widths(t);
    assert_eq!(w.wsw, w.wad);
    assert_eq!((w.post_r1, w.post_r2), (w.wad - 1, w.wad));
    let prev_widths = (st.rails.r1.len(), st.rails.r2.len());
    let prev_cof = st.cof.s.len();
    let typ_prev = st.typ.expect("encoded seam needs previous typ");
    let entry_r1 = st.rails.r1.clone();
    let entry_r2 = st.rails.r2.clone();
    let entry_s = st.cof.s.clone();
    let entry_r = st.cof.r.clone();
    let entry_h = st.h.wires.clone();
    let entry_odo = st.odo.clone();
    let entry_live = c.active_qubits();

    let ((view, receipt, encoded_end, graph_end, forward_end, restored_typ), peak) = c.r3_peak(|c| {
        let (typ, cflag, _) = tick::rail_fwd_encoded_sign_fixture(
            c, &mut st.rails, typ_prev, &w, Some(p.cap));
        assert_eq!(st.rails.r2.last().copied(), Some(cflag));
        let encoded_end = c.op_count();
        dispose_fwd(c, p, env, t - 1, typ_prev, &st.rails, &st.cof,
            &mut st.h, &st.odo, Some(cflag), None);
        let (_, receipt) = tick::cof_fwd_at_implicit_r0_encoded_sign_fixture(
            c, &mut st.cof, typ, cflag, &mut st.rails.r1, &mut st.rails.r2,
            &w, Some(p.cap), t);
        // Freeze the graph-C classical receipt before fold or any later HMR
        // can reuse this freed BitId.
        let graph_end = c.op_count();
        let pre_fold_s = st.cof.s.clone();
        let logical_r = st.cof.r.len() + 1;
        let fate = if st.cof.s.len() > logical_r {
            fold(c, &mut st.cof, p);
            TopFate::Folded
        } else {
            TopFate::None
        };
        let forward_end = c.op_count();
        let view = EncodedSeamView {
            r1: st.rails.r1.clone(), r2: st.rails.r2.clone(),
            s: st.cof.s.clone(), r: st.cof.r.clone(), h: st.h.wires.clone(),
            odo: st.odo.clone(), typ, pre_fold_s,
        };

        if fate == TopFate::Folded { unfold(c, &mut st.cof, p); }
        let (cflag2, _) = tick::cof_rev_at_implicit_r0_encoded_sign_fixture(
            c, &mut st.cof, typ, &mut st.rails.r1, &mut st.rails.r2,
            prev_cof, Some(p.cap), t);
        assert_eq!(cflag2, cflag, "encoded C physical owner drift");
        let restored_typ = dispose_rev(c, p, env, t - 1, &st.rails, &st.cof,
            &mut st.h, &st.odo, Some(cflag2));
        tick::rail_rev_encoded_sign_fixture(
            c, &mut st.rails, typ, restored_typ, &w, prev_widths, Some(p.cap));
        (view, receipt, encoded_end, graph_end, forward_end, restored_typ)
    });

    assert_eq!(st.rails.r1, entry_r1, "encoded seam r1 ID order");
    assert_eq!(st.rails.r2, entry_r2, "encoded seam r2 ID order");
    assert_eq!(st.cof.s, entry_s, "encoded seam cofactor S ID order");
    assert_eq!(st.cof.r, entry_r, "encoded seam cofactor R ID order");
    assert_eq!(st.h.wires, entry_h, "encoded seam H ID order");
    assert_eq!(st.odo, entry_odo, "encoded seam odometer ID order");
    assert_eq!(c.active_qubits(), entry_live, "encoded seam owner leak");
    st.typ = Some(restored_typ);
    (st, view, receipt, encoded_end, graph_end, forward_end, peak)
}

/// Source-bound native roundtrip for the sign->H, previous-type->sign owner
/// rotation.  Production traversal does not call this function.
pub(crate) fn sign_history_seam_roundtrip_fixture(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    mut st: ActiveWalk,
    t: usize,
) -> (ActiveWalk, EncodedSeamView, usize, u32, Q, Q) {
    assert!(matches!(t, 322 | 323 | 324 | 335));
    assert_eq!(st.next_t, t);
    let w = env.widths(t);
    let prev_widths = (st.rails.r1.len(), st.rails.r2.len());
    let prev_cof = st.cof.s.len();
    let previous_typ = st.typ.unwrap();
    let old_h = st.h.len();
    let entry_r1 = st.rails.r1.clone(); let entry_r2 = st.rails.r2.clone();
    let entry_s = st.cof.s.clone(); let entry_r = st.cof.r.clone();
    let entry_h = st.h.wires.clone(); let entry_odo = st.odo.clone();
    let entry_live = c.active_qubits();
    let ((view, forward_end, lender, type_owner, restored_typ), peak) = c.r3_peak(|c| {
        let (typ, isc, _) = tick::rail_fwd_micro(
            c, &mut st.rails, Some(previous_typ), &w, Some(p.cap), None, Some(t));
        let lender = dispose_fwd_sign_history_fixture(
            c, p, env, t - 1, typ, previous_typ, &mut st.rails, &st.cof,
            &mut st.h, &st.odo, Some(isc));
        let type_owner = *st.rails.r2.last().unwrap();
        assert_eq!(type_owner, previous_typ);
        assert_eq!(st.h.wires[old_h], lender);
        let retained_zero_head = rotate_isc_to_cofzero_tick(t);
        if retained_zero_head {
            tick::cof_fwd_at_implicit_r0_zero_head(
                c, &mut st.cof, typ, isc, &w, Some(p.cap), t);
        } else {
            tick::cof_fwd_at_implicit_r0(c, &mut st.cof, typ, isc, &w, Some(p.cap), t);
            tick::erase_isc(c, &st.cof, typ, isc);
        }
        let logical_r = st.cof.r.len() + 1;
        let pre_fold_s = st.cof.s.clone();
        let fate = if st.cof.s.len() > logical_r {
            fold(c, &mut st.cof, p); TopFate::Folded
        } else { TopFate::None };
        let forward_end = c.op_count();
        let view = EncodedSeamView {
            r1:st.rails.r1.clone(),r2:st.rails.r2.clone(),s:st.cof.s.clone(),
            r:st.cof.r.clone(),h:st.h.wires.clone(),odo:st.odo.clone(),typ,
            pre_fold_s,
        };

        if fate == TopFate::Folded { unfold(c, &mut st.cof, p); }
        let recycle_zero = retained_cofzero_tick(t);
        let isc2 = if recycle_zero {
            tick::isc_recompute_from_zero_head(c, &mut st.cof, typ)
        } else { tick::isc_recompute(c, &st.cof, typ) };
        if recycle_zero {
            tick::cof_rev_at_implicit_r0_zero_head(
                c,&mut st.cof,typ,isc2,prev_cof,Some(p.cap),t);
        } else {
            tick::cof_rev_at_implicit_r0(c,&mut st.cof,typ,isc2,prev_cof,Some(p.cap),t);
        }
        let (restored_typ, lender2) = dispose_rev_sign_history_fixture(
            c,p,env,t-1,typ,&mut st.rails,&st.cof,&mut st.h,&st.odo,Some(isc2));
        assert_eq!(lender2,lender);
        assert_eq!(st.rails.r2.last().copied(),Some(lender),
            "sign/history lender was not restored before inverse rail");
        if t == 324 {
            let park=&st.cof.r[st.cof.r.len()-14..]; let dirty=&st.cof.s[1..14];
            tick::rail_rev_dirty_s0_implicit(c,&mut st.rails,typ,isc2,restored_typ,
                st.cof.s[0],park,dirty,w.wad,p.cap);
        } else {
            tick::rail_rev_micro(c,&mut st.rails,typ,isc2,Some(restored_typ),&w,
                prev_widths,Some(p.cap),None,Some(t));
        }
        (view,forward_end,lender,type_owner,restored_typ)
    });
    if t != 324 {
        assert_eq!(st.rails.r1,entry_r1); assert_eq!(st.rails.r2,entry_r2);
    } else {
        // The separately audited dirty-S0 inverse rail deliberately rotates
        // its own target-top donor after this seam has repaid L.
        assert_eq!((st.rails.r1.len(),st.rails.r2.len()),(entry_r1.len(),entry_r2.len()));
    }
    assert_eq!(st.cof.s,entry_s); assert_eq!(st.cof.r,entry_r);
    assert_eq!(st.h.wires,entry_h); assert_eq!(st.odo,entry_odo);
    assert_eq!(c.active_qubits(),entry_live);
    st.typ=Some(restored_typ);
    (st,view,forward_end,peak,lender,type_owner)
}

/// Delta-zero closed sign-owner loan at tick333.  Previous type is allocated
/// before the reverse loan and supplied to `dispose_rev_into`.
pub(crate) fn sign_closed333_roundtrip_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,mut st:ActiveWalk,expected_id_check:bool,
)->(ActiveWalk,EncodedSeamView,usize,SignHistory324Peaks,Q,Q){
    let t=333usize;assert_eq!(st.next_t,t);let w=env.widths(t);
    let prev=(st.rails.r1.len(),st.rails.r2.len());let prev_cof=st.cof.s.len();
    let previous_typ=st.typ.unwrap();let er1=st.rails.r1.clone();let er2=st.rails.r2.clone();
    let es=st.cof.s.clone();let er=st.cof.r.clone();let eh=st.h.wires.clone();let eo=st.odo.clone();
    let live=c.active_qubits();
    let((typ,isc,_),rail_fwd)=c.r3_peak(|c|tick::rail_fwd_micro(
        c,&mut st.rails,Some(previous_typ),&w,Some(p.cap),None,Some(t)));
    let(lender,dispose_fwd_peak)=c.r3_peak(|c|dispose_fwd_sign_closed_fixture(
        c,p,env,t-1,typ,previous_typ,&mut st.rails,&st.cof,&mut st.h,&st.odo,Some(isc)));
    let type_owner=previous_typ;
    let(_,cof_fwd)=c.r3_peak(|c|tick::cof_fwd_at_implicit_r0(
        c,&mut st.cof,typ,isc,&w,Some(p.cap),t));
    tick::erase_isc(c,&st.cof,typ,isc);
    let pre_fold_s=st.cof.s.clone();let logical_r=st.cof.r.len()+1;
    let(fate,fold_peak)=c.r3_peak(|c|if st.cof.s.len()>logical_r{
        fold(c,&mut st.cof,p);TopFate::Folded}else{TopFate::None});
    let end=c.op_count();let view=EncodedSeamView{r1:st.rails.r1.clone(),r2:st.rails.r2.clone(),
        s:st.cof.s.clone(),r:st.cof.r.clone(),h:st.h.wires.clone(),odo:st.odo.clone(),typ,pre_fold_s};
    let(_,unfold_peak)=c.r3_peak(|c|if fate==TopFate::Folded{unfold(c,&mut st.cof,p)});
    let(isc2,cof_rev)=c.r3_peak(|c|{let q=tick::isc_recompute(c,&st.cof,typ);
        tick::cof_rev_at_implicit_r0(c,&mut st.cof,typ,q,prev_cof,Some(p.cap),t);q});
    let expected=expected_id_check.then_some(type_owner);
    let(restored_typ,dispose_rev)=c.r3_peak(|c|dispose_rev_sign_closed_fixture(
        c,p,env,t-1,typ,expected,&mut st.rails,&st.cof,&mut st.h,&st.odo,Some(isc2)));
    let(_,rail_rev)=c.r3_peak(|c|tick::rail_rev_micro(c,&mut st.rails,typ,isc2,Some(restored_typ),
        &w,prev,Some(p.cap),None,Some(t)));
    assert_eq!(st.rails.r1,er1);assert_eq!(st.rails.r2,er2);assert_eq!(st.cof.s,es);
    assert_eq!(st.cof.r,er);assert_eq!(st.h.wires,eh);assert_eq!(st.odo,eo);assert_eq!(c.active_qubits(),live);
    st.typ=Some(restored_typ);let peaks=SignHistory324Peaks{rail_fwd,dispose_fwd:dispose_fwd_peak,
        cof_fwd,fold:fold_peak,unfold:unfold_peak,cof_rev,dispose_rev,rail_rev};
    (st,view,end,peaks,lender,type_owner)
}

#[derive(Clone,Copy,Debug)]
pub(crate) struct SignHistory324Peaks{
    pub rail_fwd:u32,pub dispose_fwd:u32,pub cof_fwd:u32,pub fold:u32,
    pub unfold:u32,pub cof_rev:u32,pub dispose_rev:u32,pub rail_rev:u32,
}
impl SignHistory324Peaks{pub fn max(self)->u32{[
    self.rail_fwd,self.dispose_fwd,self.cof_fwd,self.fold,self.unfold,
    self.cof_rev,self.dispose_rev,self.rail_rev].into_iter().max().unwrap()}}

/// Combined bounded tick324 diagnostic: normalized contract rail plus the
/// sign/history/type rotation, explicitly bypassing the production dirty-S0
/// inverse rail.  Production traversal remains unchanged.
pub(crate) fn sign_history_contract324_roundtrip_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,mut st:ActiveWalk,
)->(ActiveWalk,EncodedSeamView,usize,SignHistory324Peaks,Q,Q){
    let t=324usize;assert_eq!(st.next_t,t);let w=env.widths(t);
    let prev=(st.rails.r1.len(),st.rails.r2.len());let prev_cof=st.cof.s.len();
    let previous_typ=st.typ.unwrap();let old_h=st.h.len();
    let er1=st.rails.r1.clone();let er2=st.rails.r2.clone();let es=st.cof.s.clone();
    let er=st.cof.r.clone();let eh=st.h.wires.clone();let eo=st.odo.clone();
    let live=c.active_qubits();
    let((typ,isc,_),rail_fwd)=c.r3_peak(|c|tick::rail_fwd_normalized_contract324_fixture(
        c,&mut st.rails,previous_typ,&w,Some(p.cap)));
    let(lender,dispose_fwd_peak)=c.r3_peak(|c|dispose_fwd_sign_history_fixture(
        c,p,env,t-1,typ,previous_typ,&mut st.rails,&st.cof,&mut st.h,&st.odo,Some(isc)));
    let type_owner=*st.rails.r2.last().unwrap();assert_eq!(st.h.wires[old_h],lender);
    let(_,cof_fwd)=c.r3_peak(|c|tick::cof_fwd_at_implicit_r0_zero_head(
        c,&mut st.cof,typ,isc,&w,Some(p.cap),t));
    let pre_fold_s=st.cof.s.clone();let logical_r=st.cof.r.len()+1;
    let(fate,fold_peak)=c.r3_peak(|c|if st.cof.s.len()>logical_r{
        fold(c,&mut st.cof,p);TopFate::Folded}else{TopFate::None});
    let end=c.op_count();let view=EncodedSeamView{r1:st.rails.r1.clone(),r2:st.rails.r2.clone(),
        s:st.cof.s.clone(),r:st.cof.r.clone(),h:st.h.wires.clone(),odo:st.odo.clone(),
        typ,pre_fold_s};
    let(_,unfold_peak)=c.r3_peak(|c|if fate==TopFate::Folded{unfold(c,&mut st.cof,p)});
    let(isc2,cof_rev_peak)=c.r3_peak(|c|{
        let q=tick::isc_recompute_from_zero_head(c,&mut st.cof,typ);
        tick::cof_rev_at_implicit_r0_zero_head(c,&mut st.cof,typ,q,prev_cof,Some(p.cap),t);q});
    let((restored_typ,lender2),dispose_rev_peak)=c.r3_peak(|c|dispose_rev_sign_history_fixture(
        c,p,env,t-1,typ,&mut st.rails,&st.cof,&mut st.h,&st.odo,Some(isc2)));
    assert_eq!(lender2,lender);assert_eq!(st.rails.r2.last().copied(),Some(lender));
    let(_,rail_rev)=c.r3_peak(|c|tick::rail_rev_normalized_contract324_fixture(
        c,&mut st.rails,typ,isc2,restored_typ,&w,prev,Some(p.cap)));
    assert_eq!(st.rails.r1,er1);assert_eq!(st.rails.r2,er2);assert_eq!(st.cof.s,es);
    assert_eq!(st.cof.r,er);assert_eq!(st.h.wires,eh);assert_eq!(st.odo,eo);
    assert_eq!(c.active_qubits(),live);st.typ=Some(restored_typ);
    let peaks=SignHistory324Peaks{rail_fwd,dispose_fwd:dispose_fwd_peak,cof_fwd,fold:fold_peak,
        unfold:unfold_peak,cof_rev:cof_rev_peak,dispose_rev:dispose_rev_peak,rail_rev};
    (st,view,end,peaks,lender,type_owner)
}

fn local_abi_values(case_id: usize) -> (usize, usize, alloy_primitives::U256, alloy_primitives::U256) {
    let pv = crate::point_add::SECP256K1_P;
    let one = alloy_primitives::U256::from(1u64);
    match case_id {
        1 => (319, 55, (pv + one) >> 2usize,
            (pv - alloy_primitives::U256::from(3u64)) >> 2usize),
        2 => {
            let s = (pv / alloy_primitives::U256::from(5u64)) & !one;
            (320, 54, s, pv - alloy_primitives::U256::from(3u64) * s)
        }
        _ => panic!("unknown encoded local ABI case {case_id}"),
    }
}

fn local_abi_state(c: &mut Builder, env: &Envelope, case_id: usize) -> ActiveWalk {
    let (start, r2w, sv, rv) = local_abi_values(case_id);
    let rails = Rails { r1: c.alloc_qubits(54), r2: c.alloc_qubits(r2w) };
    c.x(rails.r1[2]); // +4
    for (i, &q) in rails.r2.iter().enumerate() {
        if i != 1 { c.x(q); } // -3 in signed width55
    }
    let e = env.cof[start - 1];
    let s = c.alloc_qubits(e);
    let r = c.alloc_qubits(e - 1); // implicit logical R0=1; r[j]=R[j+1]
    for (i, &q) in s.iter().enumerate() { if sv.bit(i) { c.x(q); } }
    for (j, &q) in r.iter().enumerate() { if rv.bit(j + 1) { c.x(q); } }
    let h = Hreg { wires: c.alloc_qubits(env.h[start - 2]) };
    let typ = c.alloc_qubit(); // previousType=0
    let dummy_prev = PrevWidths { r1: 0, r2: 0, cof: 0 };
    ActiveWalk {
        rails, cof: Cof { s, r }, h, odo: Vec::new(), typ: Some(typ), next_t: start,
        prev: vec![dummy_prev; start], tops: vec![TopFate::None; start],
    }
}

fn reverse_local_ticks(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    st: &mut ActiveWalk,
    start: usize,
    end: usize,
) {
    assert_eq!(st.next_t, end);
    let mut typ = st.typ.unwrap();
    for t in (start..end).rev() {
        let w = env.widths(t);
        match st.tops[t] {
            TopFate::Folded => unfold(c, &mut st.cof, p),
            TopFate::Freed => st.cof.s.push(c.alloc_qubit()),
            TopFate::None => {}
        }
        let recycle_zero = retained_cofzero_tick(t);
        let isc = if recycle_zero {
            tick::isc_recompute_from_zero_head(c, &mut st.cof, typ)
        } else {
            tick::isc_recompute(c, &st.cof, typ)
        };
        if recycle_zero {
            assert_cofzero_disjoint(isc, typ, &st.rails, &st.cof, &st.h, &st.odo);
            tick::cof_rev_at_implicit_r0_zero_head(
                c, &mut st.cof, typ, isc, st.prev[t].cof, Some(p.cap), t);
        } else {
            tick::cof_rev_at_implicit_r0(
                c, &mut st.cof, typ, isc, st.prev[t].cof, Some(p.cap), t);
        }
        let tprev = dispose_rev(c, p, env, t - 1, &st.rails, &st.cof,
            &mut st.h, &st.odo, Some(isc));
        tick::rail_rev_micro(c, &mut st.rails, typ, isc, Some(tprev), &w,
            (st.prev[t].r1, st.prev[t].r2), Some(p.cap), None, Some(t));
        typ = tprev;
    }
    st.typ = Some(typ);
    st.next_t = start;
    st.prev.truncate(start);
    st.tops.truncate(start);
}

fn local_view(st: &ActiveWalk) -> EncodedSeamView {
    EncodedSeamView {
        r1: st.rails.r1.clone(), r2: st.rails.r2.clone(),
        s: st.cof.s.clone(), r: st.cof.r.clone(), h: st.h.wires.clone(),
        odo: st.odo.clone(), typ: st.typ.unwrap(), pre_fold_s: st.cof.s.clone(),
    }
}

/// Literal promised-domain path: initialize the accepted pre319 local ABI,
/// execute ordinary319/320, then the encoded321 seam and reverse all three
/// local ticks.  The caller owns arbitrary passengers outside this state.
pub(crate) fn encoded_sign_local_abi_fixture(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    case_id: usize,
) -> (EncodedSeamView, B, usize, usize, usize, u32) {
    let (start, _, sv, rv) = local_abi_values(case_id);
    let mut st = local_abi_state(c, env, case_id);
    let entry_r1 = st.rails.r1.clone();
    let entry_r2 = st.rails.r2.clone();
    let entry_s = st.cof.s.clone();
    let entry_r = st.cof.r.clone();
    let entry_h = st.h.wires.clone();
    let entry_typ = st.typ.unwrap();
    let entry_live = c.active_qubits();
    forward_ticks(c, p, env, &mut st, 321);
    let (mut st, view, receipt, encoded_end, graph_end, forward_end, peak) =
        encoded_sign_seam_roundtrip_fixture(c, p, env, st, 321);
    reverse_local_ticks(c, p, env, &mut st, start, 321);
    assert_eq!(st.rails.r1, entry_r1);
    assert_eq!(st.rails.r2, entry_r2);
    assert_eq!(st.cof.s, entry_s);
    assert_eq!(st.cof.r, entry_r);
    assert_eq!(st.h.wires, entry_h);
    assert_eq!(st.typ, Some(entry_typ));
    assert_eq!(c.active_qubits(), entry_live);

    // Return the local ABI owners to zero and release them.  A fixture caller
    // may keep arbitrary passenger owners live across the whole chain.
    c.x(st.rails.r1[2]);
    for (i, &q) in st.rails.r2.iter().enumerate() { if i != 1 { c.x(q); } }
    for (i, &q) in st.cof.s.iter().enumerate() { if sv.bit(i) { c.x(q); } }
    for (j, &q) in st.cof.r.iter().enumerate() { if rv.bit(j + 1) { c.x(q); } }
    c.free_vec(&st.rails.r1); c.free_vec(&st.rails.r2);
    c.free_vec(&st.cof.s); c.free_vec(&st.cof.r); c.free_vec(&st.h.wires);
    c.free(entry_typ);
    (view, receipt, encoded_end, graph_end, forward_end, peak)
}

/// Ordinary local ABI reference through ticks319,320,321.  It deliberately
/// leaves the forward state live for value comparison in the simulator.
pub(crate) fn ordinary_sign_local_abi_fixture(
    c: &mut Builder,
    p: &WalkParams,
    env: &Envelope,
    case_id: usize,
) -> EncodedSeamView {
    let mut st = local_abi_state(c, env, case_id);
    with_encoded_reference_ordinary(|| forward_ticks(c, p, env, &mut st, 322));
    local_view(&st)
}

/// Parked-odd-S0/ghost-counter local path into the combined tick324 seam.
pub(crate) fn sign_history_contract324_local_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->(EncodedSeamView,usize,SignHistory324Peaks,Q,Q){
    let(_,_,sv,rv)=local_abi_values(1);let mut st=local_abi_state(c,env,1);
    let er1=st.rails.r1.clone();let er2=st.rails.r2.clone();let es=st.cof.s.clone();
    let er=st.cof.r.clone();let eh=st.h.wires.clone();let et=st.typ.unwrap();let live=c.active_qubits();
    forward_ticks(c,p,env,&mut st,324);
    assert!(st.cof.s[0]!=st.cof.r[0]); // physical owners distinct; values checked in simulator
    let(mut st,view,end,peaks,lender,type_owner)=sign_history_contract324_roundtrip_fixture(c,p,env,st);
    reverse_local_ticks(c,p,env,&mut st,319,324);
    assert_eq!((st.rails.r1.len(),st.rails.r2.len()),(er1.len(),er2.len()));
    assert_eq!(st.cof.s,es);
    assert_eq!(st.cof.r,er);assert_eq!(st.h.wires,eh);assert_eq!(st.typ,Some(et));assert_eq!(c.active_qubits(),live);
    c.x(st.rails.r1[2]);for(i,&q)in st.rails.r2.iter().enumerate(){if i!=1{c.x(q);}}
    for(i,&q)in st.cof.s.iter().enumerate(){if sv.bit(i){c.x(q);}}
    for(j,&q)in st.cof.r.iter().enumerate(){if rv.bit(j+1){c.x(q);}}
    c.free_vec(&st.rails.r1);c.free_vec(&st.rails.r2);c.free_vec(&st.cof.s);c.free_vec(&st.cof.r);
    c.free_vec(&st.h.wires);c.free(et);
    (view,end,peaks,lender,type_owner)
}

pub(crate) fn sign_history_contract324_local_ordinary_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->EncodedSeamView{
    let mut st=local_abi_state(c,env,1);with_encoded_reference_ordinary(||forward_ticks(c,p,env,&mut st,325));local_view(&st)
}

pub(crate) fn sign_closed333_local_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->(EncodedSeamView,usize,SignHistory324Peaks,Q,Q){
    let(_,_,sv,rv)=local_abi_values(1);let mut st=local_abi_state(c,env,1);
    let er1=st.rails.r1.len();let er2=st.rails.r2.len();let es=st.cof.s.clone();let er=st.cof.r.clone();
    let eh=st.h.wires.clone();let et=st.typ.unwrap();let live=c.active_qubits();
    forward_ticks(c,p,env,&mut st,333);let(mut st,view,end,peaks,lender,type_owner)=
        sign_closed333_roundtrip_fixture(c,p,env,st,false);reverse_local_ticks(c,p,env,&mut st,319,333);
    assert_eq!((st.rails.r1.len(),st.rails.r2.len()),(er1,er2));
    assert_eq!((st.cof.s.len(),st.cof.r.len()),(es.len(),er.len()));
    assert_eq!(st.h.wires,eh);assert_eq!(st.typ,Some(et));assert_eq!(c.active_qubits(),live);
    c.x(st.rails.r1[2]);for(i,&q)in st.rails.r2.iter().enumerate(){if i!=1{c.x(q);}}
    for(i,&q)in st.cof.s.iter().enumerate(){if sv.bit(i){c.x(q);}}
    for(j,&q)in st.cof.r.iter().enumerate(){if rv.bit(j+1){c.x(q);}}
    c.free_vec(&st.rails.r1);c.free_vec(&st.rails.r2);c.free_vec(&st.cof.s);c.free_vec(&st.cof.r);
    c.free_vec(&st.h.wires);c.free(et);(view,end,peaks,lender,type_owner)
}

pub(crate) fn sign_closed333_local_ordinary_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->EncodedSeamView{let mut st=local_abi_state(c,env,1);with_encoded_reference_ordinary(||forward_ticks(c,p,env,&mut st,334));local_view(&st)}

fn sign_history_l1_state(c:&mut Builder,env:&Envelope)->ActiveWalk{
    let rails=Rails{r1:c.alloc_qubits(52),r2:c.alloc_qubits(53)};
    c.x(rails.r1[2]);
    for(i,&q)in rails.r2.iter().enumerate(){if i!=1{c.x(q);}}
    let pv=crate::point_add::SECP256K1_P;
    let one=alloy_primitives::U256::from(1u64);
    let sv=(pv/alloy_primitives::U256::from(5u64))&!one;
    let rv=pv-alloy_primitives::U256::from(3u64)*sv;
    let s=c.alloc_qubits(256);let r=c.alloc_qubits(255);
    for(i,&q)in s.iter().enumerate(){if sv.bit(i){c.x(q);}}
    for(j,&q)in r.iter().enumerate(){if rv.bit(j+1){c.x(q);}}
    let h=Hreg{wires:c.alloc_qubits(env.h[320])};
    c.x(*h.wires.last().unwrap()); // only old H top is one
    let typ=c.alloc_qubit();
    let dummy=PrevWidths{r1:0,r2:0,cof:0};
    ActiveWalk{rails,cof:Cof{s,r},h,odo:Vec::new(),typ:Some(typ),next_t:322,
        prev:vec![dummy;322],tops:vec![TopFate::None;322]}
}

/// Literal local H-top-one / ambiguous-B tick322 case.
pub(crate) fn sign_history_l1_local_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->(EncodedSeamView,usize,u32,Q,Q){
    let mut st=sign_history_l1_state(c,env);
    let er1=st.rails.r1.clone();let er2=st.rails.r2.clone();
    let es=st.cof.s.clone();let er=st.cof.r.clone();let eh=st.h.wires.clone();
    let et=st.typ.unwrap();let live=c.active_qubits();
    let(mut st,view,end,peak,lender,type_owner)=
        sign_history_seam_roundtrip_fixture(c,p,env,st,322);
    assert_eq!(st.rails.r1,er1);assert_eq!(st.rails.r2,er2);
    assert_eq!(st.cof.s,es);assert_eq!(st.cof.r,er);assert_eq!(st.h.wires,eh);
    assert_eq!(st.typ,Some(et));assert_eq!(c.active_qubits(),live);
    c.x(st.rails.r1[2]);for(i,&q)in st.rails.r2.iter().enumerate(){if i!=1{c.x(q);}}
    let pv=crate::point_add::SECP256K1_P;let one=alloy_primitives::U256::from(1u64);
    let sv=(pv/alloy_primitives::U256::from(5u64))&!one;
    let rv=pv-alloy_primitives::U256::from(3u64)*sv;
    for(i,&q)in st.cof.s.iter().enumerate(){if sv.bit(i){c.x(q);}}
    for(j,&q)in st.cof.r.iter().enumerate(){if rv.bit(j+1){c.x(q);}}
    c.x(*st.h.wires.last().unwrap());
    c.free_vec(&st.rails.r1);c.free_vec(&st.rails.r2);c.free_vec(&st.cof.s);
    c.free_vec(&st.cof.r);c.free_vec(&st.h.wires);c.free(et);
    (view,end,peak,lender,type_owner)
}

pub(crate) fn sign_history_l1_ordinary_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->EncodedSeamView{
    let mut st=sign_history_l1_state(c,env);with_encoded_reference_ordinary(||forward_ticks(c,p,env,&mut st,323));local_view(&st)
}

fn sign_history_l1_323_state(c:&mut Builder,env:&Envelope)->ActiveWalk{
    let rails=Rails{r1:c.alloc_qubits(52),r2:c.alloc_qubits(52)};c.x(rails.r1[2]);
    for(i,&q)in rails.r2.iter().enumerate(){if i!=1{c.x(q);}}
    let pv=crate::point_add::SECP256K1_P;let one=alloy_primitives::U256::from(1u64);
    let sv=(pv/alloy_primitives::U256::from(5u64))&!one;let rv=pv-alloy_primitives::U256::from(3u64)*sv;
    let s=c.alloc_qubits(256);let r=c.alloc_qubits(255);for(i,&q)in s.iter().enumerate(){if sv.bit(i){c.x(q);}}
    for(j,&q)in r.iter().enumerate(){if rv.bit(j+1){c.x(q);}}
    let h=Hreg{wires:c.alloc_qubits(env.h[321])};c.x(*h.wires.last().unwrap());let typ=c.alloc_qubit();
    let dummy=PrevWidths{r1:0,r2:0,cof:0};ActiveWalk{rails,cof:Cof{s,r},h,odo:Vec::new(),typ:Some(typ),
        next_t:323,prev:vec![dummy;323],tops:vec![TopFate::None;323]}
}

pub(crate) fn sign_history_l1_323_local_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->(EncodedSeamView,usize,u32,Q,Q){
    let mut st=sign_history_l1_323_state(c,env);let er1=st.rails.r1.clone();let er2=st.rails.r2.clone();
    let es=st.cof.s.clone();let er=st.cof.r.clone();let eh=st.h.wires.clone();let et=st.typ.unwrap();let live=c.active_qubits();
    let(mut st,view,end,peak,lender,type_owner)=sign_history_seam_roundtrip_fixture(c,p,env,st,323);
    assert_eq!(st.rails.r1,er1);assert_eq!(st.rails.r2,er2);assert_eq!(st.cof.s,es);assert_eq!(st.cof.r,er);
    assert_eq!(st.h.wires,eh);assert_eq!(st.typ,Some(et));assert_eq!(c.active_qubits(),live);
    c.x(st.rails.r1[2]);for(i,&q)in st.rails.r2.iter().enumerate(){if i!=1{c.x(q);}}
    let pv=crate::point_add::SECP256K1_P;let one=alloy_primitives::U256::from(1u64);
    let sv=(pv/alloy_primitives::U256::from(5u64))&!one;let rv=pv-alloy_primitives::U256::from(3u64)*sv;
    for(i,&q)in st.cof.s.iter().enumerate(){if sv.bit(i){c.x(q);}}for(j,&q)in st.cof.r.iter().enumerate(){if rv.bit(j+1){c.x(q);}}
    c.x(*st.h.wires.last().unwrap());c.free_vec(&st.rails.r1);c.free_vec(&st.rails.r2);c.free_vec(&st.cof.s);
    c.free_vec(&st.cof.r);c.free_vec(&st.h.wires);c.free(et);(view,end,peak,lender,type_owner)
}

pub(crate) fn sign_history_l1_323_ordinary_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->EncodedSeamView{let mut st=sign_history_l1_323_state(c,env);with_encoded_reference_ordinary(||forward_ticks(c,p,env,&mut st,324));local_view(&st)}

fn sign_history_l1_335_state(c:&mut Builder,env:&Envelope)->ActiveWalk{
    let rails=Rails{r1:c.alloc_qubits(47),r2:c.alloc_qubits(47)};c.x(rails.r1[2]);
    for(i,&q)in rails.r2.iter().enumerate(){if i!=1{c.x(q);}}
    let pv=crate::point_add::SECP256K1_P;let one=alloy_primitives::U256::from(1u64);
    let sv=(pv/alloy_primitives::U256::from(5u64))&!one;let rv=pv-alloy_primitives::U256::from(3u64)*sv;
    let s=c.alloc_qubits(256);let r=c.alloc_qubits(255);for(i,&q)in s.iter().enumerate(){if sv.bit(i){c.x(q);}}
    for(j,&q)in r.iter().enumerate(){if rv.bit(j+1){c.x(q);}}
    let h=Hreg{wires:c.alloc_qubits(env.h[333])};c.x(*h.wires.last().unwrap());let typ=c.alloc_qubit();
    let dummy=PrevWidths{r1:0,r2:0,cof:0};ActiveWalk{rails,cof:Cof{s,r},h,odo:Vec::new(),typ:Some(typ),
        next_t:335,prev:vec![dummy;335],tops:vec![TopFate::None;335]}
}

pub(crate) fn sign_history_l1_335_local_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->(EncodedSeamView,usize,u32,Q,Q){
    let mut st=sign_history_l1_335_state(c,env);let er1=st.rails.r1.clone();let er2=st.rails.r2.clone();
    let es=st.cof.s.clone();let er=st.cof.r.clone();let eh=st.h.wires.clone();let et=st.typ.unwrap();let live=c.active_qubits();
    let(mut st,view,end,peak,lender,type_owner)=sign_history_seam_roundtrip_fixture(c,p,env,st,335);
    assert_eq!(st.rails.r1,er1);assert_eq!(st.rails.r2,er2);assert_eq!(st.cof.s,es);assert_eq!(st.cof.r,er);
    assert_eq!(st.h.wires,eh);assert_eq!(st.typ,Some(et));assert_eq!(c.active_qubits(),live);
    c.x(st.rails.r1[2]);for(i,&q)in st.rails.r2.iter().enumerate(){if i!=1{c.x(q);}}
    let pv=crate::point_add::SECP256K1_P;let one=alloy_primitives::U256::from(1u64);
    let sv=(pv/alloy_primitives::U256::from(5u64))&!one;let rv=pv-alloy_primitives::U256::from(3u64)*sv;
    for(i,&q)in st.cof.s.iter().enumerate(){if sv.bit(i){c.x(q);}}for(j,&q)in st.cof.r.iter().enumerate(){if rv.bit(j+1){c.x(q);}}
    c.x(*st.h.wires.last().unwrap());c.free_vec(&st.rails.r1);c.free_vec(&st.rails.r2);c.free_vec(&st.cof.s);
    c.free_vec(&st.cof.r);c.free_vec(&st.h.wires);c.free(et);(view,end,peak,lender,type_owner)
}

pub(crate) fn sign_history_l1_335_ordinary_fixture(
    c:&mut Builder,p:&WalkParams,env:&Envelope,
)->EncodedSeamView{let mut st=sign_history_l1_335_state(c,env);with_encoded_reference_ordinary(||forward_ticks(c,p,env,&mut st,336));local_view(&st)}

/// Exact walk back from [`forward`]'s parked state; returns the wires holding `d`.
pub fn backward(c: &mut Builder, p: &WalkParams, env: &Envelope, pk: Parked) -> Vec<Q> {
    let r = p.r;
    let Parked {
        s,
        mut h,
        mut odo,
        prev,
        tops,
    } = pk;
    let (post_r1, post_r2) = env.post_widths(r - 1);
    let mut rails = Rails {
        r1: c.alloc_qubits(post_r1),
        r2: c.alloc_qubits(post_r2),
    };
    c.x(rails.r2[0]);
    let rstart = usize::from(implicit_r0());
    let rr = if ghost_odo() {
        assert_eq!(odo.len(), p.odo_bits);
        (rstart..N)
            .map(|i| {
                if (GHOST_ODO_START..GHOST_ODO_START + p.odo_bits).contains(&i) {
                    odo[i - GHOST_ODO_START]
                } else {
                    c.alloc_qubit()
                }
            })
            .collect::<Vec<_>>()
    } else {
        c.alloc_qubits(N - rstart)
    };
    let pv = crate::point_add::SECP256K1_P;
    for i in rstart..N {
        if pv.bit(i)
            && !(ghost_odo() && (GHOST_ODO_START..GHOST_ODO_START + p.odo_bits).contains(&i))
        {
            c.x(rr[i - rstart]);
        }
    }
    if ghost_odo() {
        // Ownership has returned to R. Do not free these aliased IDs twice.
        odo.clear();
    }
    let mut cof = Cof { s, r: rr };
    let mut typ = dispose_rev(c, p, env, r - 1, &rails, &cof, &mut h, &odo, None);
    for t in (0..r).rev() {
        let w = env.widths(t);
        let positive_role=sign_positive_tick(t,&w);
        let closed_role=sign_closed_tick(t,&w);
        if !implicit_r0() && t == 328 && recycle_cofzero_tick(t) {
            assert_eq!(tops[t], TopFate::Folded, "tick328 role order requires unfold first");
            assert!(w.post_r1 < w.wad, "tick328 sign-extension host geometry drifted");
        }
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        match tops[t] {
            TopFate::Folded => unfold(c, &mut cof, p),
            TopFate::Freed => {
                let q = c.alloc_qubit();
                cof.s.push(q);
            }
            TopFate::None => {}
        }
        trace_cost(c, "rev", t, "unfold", t0);
        trace_step(c, "rev-unfold");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        let encoded_sign = encoded_sign_tick(t, &w);
        let recycle_zero = !encoded_sign && retained_cofzero_tick(t);
        let isc = if encoded_sign {
            let (q, _) = tick::cof_rev_at_implicit_r0_encoded_sign_fixture(
                c, &mut cof, typ, &mut rails.r1, &mut rails.r2,
                prev[t].cof, Some(p.cap), t);
            q
        } else if recycle_zero {
            tick::isc_recompute_from_zero_head(c, &mut cof, typ)
        } else {
            tick::isc_recompute(c, &cof, typ)
        };
        if encoded_sign {
            // Paired encoded cofactor inverse already complete.
        } else if recycle_zero {
            assert_cofzero_disjoint(isc, typ, &rails, &cof, &h, &odo);
            if implicit_r0() {
                tick::cof_rev_at_implicit_r0_zero_head(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap), t);
            } else {
                tick::cof_rev_at_zero_head(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap), t);
            }
        } else if implicit_r0() {
            tick::cof_rev_at_implicit_r0(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap), t);
        } else {
            tick::cof_rev_at(c, &mut cof, typ, isc, prev[t].cof, Some(p.cap), t);
        }
        trace_cost(c, "rev", t, "cofactor", t0);
        trace_step(c, "rev-cof");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        let tprev = if t >= 1 {
            Some(if positive_role {
                dispose_rev_sign_history_fixture(c,p,env,t-1,typ,&mut rails,&cof,
                    &mut h,&odo,Some(isc)).0
            } else if closed_role {
                dispose_rev_sign_closed_fixture(c,p,env,t-1,typ,None,&mut rails,&cof,
                    &mut h,&odo,Some(isc))
            } else {
                dispose_rev(c,p,env,t-1,&rails,&cof,&mut h,&odo,Some(isc))
            })
        } else {
            None
        };
        trace_cost(c, "rev", t, "decoder", t0);
        trace_step(c, "rev-dec");
        let t0 = c.report_totals().map_or(0.0, |x| x.1);
        if positive_role && t==324 {
            let tp=tprev.expect("promoted tick324 needs previous typ");
            tick::rail_rev_normalized_contract324_fixture(c,&mut rails,typ,isc,tp,&w,
                (prev[t].r1,prev[t].r2),Some(p.cap));
        } else if encoded_sign {
            let tp = tprev.expect("encoded-sign inverse needs previous typ");
            tick::rail_rev_encoded_sign_fixture(
                c, &mut rails, typ, tp, &w, (prev[t].r1, prev[t].r2), Some(p.cap));
        } else if implicit_r0() && t == 324 {
            let tp=tprev.expect("implicit rail324 needs previous typ");
            let park=&cof.r[cof.r.len()-14..];let dirty=&cof.s[1..14];
            tick::rail_rev_dirty_s0_implicit(c,&mut rails,typ,isc,tp,cof.s[0],park,dirty,
                w.wad,p.cap);
        } else {
            tick::rail_rev_micro(c,&mut rails,typ,isc,tprev,&w,(prev[t].r1,prev[t].r2),
                Some(p.cap),if implicit_r0(){None}else{Some(cof.r[0])},Some(t));
        }
        trace_cost(c, "rev", t, "rail", t0);
        trace_step(c, "rev-rail");
        trace_tick(c, "rev", t);
        if let Some(tq) = tprev {
            typ = tq;
        }
        if t >= 1 {
            snap(c, format!("B{}", t - 1), &rails, &cof, &h, &odo, Some(typ));
        }
    }
    // cofactors back at (s, r) = (0, 1), width 2; history and odometer empty
    assert_eq!(cof.s.len(), 2);
    if !implicit_r0() { c.x(cof.r[0]); }
    c.free_vec(&cof.s);
    c.free_vec(&cof.r);
    h.shrink_to(c, 0);
    c.free_vec(&odo);
    unseed(c, rails, p.cap)
}
