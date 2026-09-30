//! HEO(S,u) walk + payload replay: the B3a research seam on the head's tree.
//!
//! Design: `round2-build/B3a/HEO-INTEGRATION-DESIGN.md`. This module is INERT in
//! the default build: every entry point below is gated on process environment
//! variables that the submission never sets, and `point_add::build` only calls
//! [`divide`] / [`multiply`] when [`enabled`] is true. With no `HEO_*` variable
//! set the emitted stream is byte-identical to the head (checked by B3a).
//!
//! # Knobs (process environment; research builds only)
//!
//! | variable | effect |
//! |---|---|
//! | `HEO_WALK=1` | route `divide`/`multiply` through this module (implies the overlay) |
//! | `HEO_RESEARCH=1` | turn on the overlay without HEO: diagnostics on the head circuit |
//! | `HEO_PIN_<NAME>=v` | overlay: override the head's pinned `<NAME>` (e.g. `HEO_PIN_PP_WALK_MAX_QUBITS`) |
//! | unpinned names | overlay: read from the environment (`PEAK_CENSUS_*`, `TRACE_CCX_SITES`, ...) |
//! | `HEO_PHASE_REPORT=1` | per-phase native/expected Toffoli + peak lines on stderr (`HEO_PHASE`, `HEO_TOTAL`) |
//! | `HEO_ENVELOPE=path` | rail envelope, one `esw ead` pair per tick (widths include the sign bit) |
//! | `HEO_R=n` | truncate the envelope to `n` ticks |
//! | `HEO_SCHEDULE` | `fused` (v0, the only one built): every payload cell fused, raw 2-wire tape |
//!
//! # The walk (ported gate for gate from `work/WP-A/heo_gates.py`)
//!
//! Rails `(R1, R2)` start at `(d + p, d)`, two's complement, LSB first. Tick t:
//! `c = R1[0]`; Fredkin `R1[i] <-> R2[i]` on `c` for `i >= 1`; `R2[0] ^= c`;
//! `E/2 = R1[1..]` (a relabel); `R2 <- R2 -+ E/2` with the subtract chosen when
//! the signs agree; the `c` wire leaves the rail as the tape's type bit
//! `typ_t = typ_{t-1} ^ c_t` and the add's sign-flip wire is the tape's `s_t`.
//! Cost per tick: `(esw - 1) + (ead - 1)` CCX, exactly.
//!
//! # The payload (butterfly frame, `chk_sd_identities`)
//!
//! `Sig <- (Sig - (-1)^g Del) / 2 (mod p)`, then `swap(Sig, Del)` if `s`, with
//! `g = typ_t`. Seed `(Sig, Del) = (2N, 0)`; at park `Sig == Del == N/d`, so the
//! endpoint is `Del ^= Sig` at 0 CCX. The cell is the head's own division replay
//! cell (`pingpong::replay_add_halve`, every lever) called with `sign = !typ`,
//! `source = Del`, `target = Sig`, at the H7 proxy round of the rail width.
use super::builder::Builder;
use super::const_arith::add_const;
use super::modular::f;
use super::pingpong::heo_hooks as h7;
use super::N;
use crate::circuit::{Op, QubitId};
use std::collections::{BTreeSet, HashMap};
use std::sync::{Mutex, OnceLock};

// ─── Research environment overlay ──────────────────────────────────────────

fn truthy(var: &str) -> bool {
    std::env::var(var).is_ok_and(|v| !matches!(v.trim().to_ascii_lowercase().as_str(), "" | "0" | "false" | "no" | "off"))
}

/// True iff the process asked for research behaviour. Read once.
pub fn research_on() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| truthy("HEO_RESEARCH") || truthy("HEO_WALK"))
}

/// Route the two pingpong legs through HEO.
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| research_on() && truthy("HEO_WALK"))
}

/// B3b: fit the square's wide exact adds under the cap (`HEO_FIT_ADDS`, default on).
pub fn fit_adds() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| (enabled() && std::env::var("HEO_FIT_ADDS").map_or(true, |v| v.trim() != "0"))
        || (research_on() && truthy("HEO_FIT_ON_HEAD")))
}

/// B3b: `HEO_FIT_MODE` = `wc` (width_composition for window/fold adds, exact split
/// elsewhere), `split` (every wide ripple chunked exactly inside `ripple_add_proved`)
/// or `win` (chunked, boundaries erased immediately by `HEO_FIT_K`-bit windows).
pub fn fit_mode_split() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| matches!(std::env::var("HEO_FIT_MODE").as_deref(), Ok("split") | Ok("win")))
}
pub fn fit_window() -> usize {
    static K: OnceLock<usize> = OnceLock::new();
    *K.get_or_init(|| if std::env::var("HEO_FIT_MODE").as_deref() == Ok("win") {
        std::env::var("HEO_FIT_K").ok().and_then(|s| s.parse().ok()).unwrap_or(24)
    } else { 0 })
}

/// Builder phase report switch (see `Builder::report_phase`).
pub fn phase_report_enabled() -> bool {
    research_on() && truthy("HEO_PHASE_REPORT")
}

fn log_once(kind: &str, name: &str, value: &str) {
    static SEEN: OnceLock<Mutex<BTreeSet<String>>> = OnceLock::new();
    let key = format!("{kind} {name}");
    if SEEN.get_or_init(Default::default).lock().unwrap().insert(key) {
        eprintln!("HEO_OVERLAY {kind} {name}={value}");
    }
}

/// `HEO_PIN_<name>` overrides a pinned head setting. None when the overlay is off.
/// K3b: per-cell pin overrides (set by `heo_carry` around one payload cell). Consulted before `HEO_PIN_*`.
thread_local! { pub static CELL_PINS: std::cell::RefCell<Option<HashMap<String, String>>> = const { std::cell::RefCell::new(None) }; }
pub fn cell_pin(name: &str) -> Option<String> {
    CELL_PINS.with(|m| m.borrow().as_ref().and_then(|m| m.get(name).cloned()))
}

pub fn pinned_override(name: &str) -> Option<String> {
    if !research_on() {
        return None;
    }
    if let Some(v) = cell_pin(name) {
        return Some(v);
    }
    let v = std::env::var(format!("HEO_PIN_{name}")).ok()?;
    log_once("pin", name, &v);
    Some(v)
}

/// Unpinned names read the process environment under the overlay (cached).
pub fn passthrough(name: &str) -> Option<String> {
    if !research_on() {
        return None;
    }
    static CACHE: OnceLock<Mutex<HashMap<String, Option<String>>>> = OnceLock::new();
    let mut cache = CACHE.get_or_init(Default::default).lock().unwrap();
    let v = cache.entry(name.to_string()).or_insert_with(|| std::env::var(name).ok()).clone();
    drop(cache);
    if let Some(v) = &v {
        log_once("env", name, v);
    }
    v
}

// ─── Configuration ─────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Schedule {
    /// v0: every cell fused into its own tick (division forward, multiply
    /// walkback), raw two-wire tape, no head/trailing batches. Functional
    /// reference; its peak is NOT the carry row's.
    FusedRaw,
    /// B3b: B1's CARRY schedule (servo splits, C10 codec, batches, loan, G1b/G3).
    Carry,
}

/// B3b: the CARRY schedule (`HEO_SCHEDULE=carry`).
#[path = "heo_carry.rs"]
pub mod carry;

pub struct HeoConfig {
    pub esw: Vec<usize>,
    pub ead: Vec<usize>,
    pub schedule: Schedule,
    /// Cells at ticks `< tie_ticks` run tie-safe (`HEO_TIE_TICKS`, default 64).
    /// B3a FINDING: Del is seeded 0 (Delta = lambda*p = 0 mod p), and the first
    /// A- swap moves that zero into Sig, so exactly one early cell per walk has
    /// target 0, where the head's seeded top-k compares tie and guess (~25% of
    /// shots failed phase in v0). P(first A- after tick 63) ~ 0.73^63 ~ 2e-9.
    pub tie_ticks: usize,
    /// Rail/payload seed (`HEO_SEED`): `base` = (d+p, d) with (Sig, Del) = (2N, 0);
    /// `3dpp` = (3d+p, d) with (4N, 2N), which never has a zero payload operand.
    pub seed: Seed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Seed {
    Base,
    ThreeDPlusP,
    /// `(p - d, d)` with (Sig, Del) = (0, -2N): the only zero operand is Sig at the
    /// PUBLIC tick 0 (an exact closed form); Del ends at (-1)^(1 - typ_last) q.
    PMinusD,
}

impl HeoConfig {
    pub fn rounds(&self) -> usize {
        self.esw.len()
    }
}

pub fn parse_envelope(text: &str) -> (Vec<usize>, Vec<usize>) {
    let (mut esw, mut ead) = (Vec::new(), Vec::new());
    for line in text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let f: Vec<usize> = line.split_whitespace().map(|x| x.parse().expect("envelope: integer widths")).collect();
        assert_eq!(f.len(), 2, "envelope line {line:?} is not `esw ead`");
        assert!(f[0] >= 3 && f[1] >= 2 && f[0] <= N + 3 && f[1] <= N + 3, "envelope widths out of range: {line:?}");
        esw.push(f[0]);
        ead.push(f[1]);
    }
    assert!(!esw.is_empty(), "empty envelope");
    (esw, ead)
}

pub fn config() -> &'static HeoConfig {
    static CFG: OnceLock<HeoConfig> = OnceLock::new();
    CFG.get_or_init(|| {
        let path = std::env::var("HEO_ENVELOPE").expect("HEO_WALK needs HEO_ENVELOPE=<path to `esw ead` lines>");
        let text = include_str!("skywalk_data/extended-middle-0_R395_d0_m10.txt").to_owned();
        let (mut esw, mut ead) = parse_envelope(&text);
        if let Some(r) = std::env::var("HEO_R").ok().and_then(|s| s.parse::<usize>().ok()) {
            assert!(r <= esw.len(), "HEO_R {r} exceeds the envelope's {} ticks", esw.len());
            esw.truncate(r);
            ead.truncate(r);
        }
        let schedule = match std::env::var("HEO_SCHEDULE").unwrap_or_else(|_| "fused".into()).as_str() {
            "fused" => Schedule::FusedRaw,
            "carry" => Schedule::Carry,
            other => panic!("HEO_SCHEDULE {other:?}: fused | carry"),
        };
        let seed = match std::env::var("HEO_SEED").unwrap_or_else(|_| "base".into()).as_str() {
            "base" => Seed::Base,
            "3dpp" => Seed::ThreeDPlusP,
            "pmd" => Seed::PMinusD,
            other => panic!("HEO_SEED {other:?}: base | 3dpp | pmd"),
        };
        let tie_default = if seed == Seed::Base { 64 } else { 0 };
        let tie_ticks = std::env::var("HEO_TIE_TICKS").ok().and_then(|s| s.parse().ok()).unwrap_or(tie_default);
        eprintln!("HEO_CONFIG R={} sum_esw={} sum_ead={} schedule={:?} cap={} tie_ticks={tie_ticks} seed={seed:?}", esw.len(),
            esw.iter().sum::<usize>(), ead.iter().sum::<usize>(), schedule, h7::cap());
        HeoConfig { esw, ead, schedule, tie_ticks, seed }
    })
}

/// B4: per-leg envelope for the multiply leg (`HEO_ENVELOPE_MUL`, optional `HEO_R_MUL`); falls back to
/// [`config`]. Everything but the widths is shared with the division leg's config.
pub fn config_mul() -> &'static HeoConfig {
    static CFG: OnceLock<HeoConfig> = OnceLock::new();
    CFG.get_or_init(|| {
        let base = config();
        let (mut esw, mut ead) = match std::env::var("HEO_ENVELOPE_MUL") {
            Ok(path) => {
                let text = include_str!("skywalk_data/extended-middle-1_R395_d0_m10.txt").to_owned();
                parse_envelope(&text)
            }
            Err(_) => (base.esw.clone(), base.ead.clone()),
        };
        if let Some(r) = std::env::var("HEO_R_MUL").ok().and_then(|s| s.parse::<usize>().ok()) {
            assert!(r <= esw.len(), "HEO_R_MUL {r} exceeds the envelope's {} ticks", esw.len());
            esw.truncate(r);
            ead.truncate(r);
        }
        eprintln!("HEO_CONFIG_MUL R={} sum_esw={} sum_ead={}", esw.len(), esw.iter().sum::<usize>(), ead.iter().sum::<usize>());
        HeoConfig { esw, ead, schedule: base.schedule, tie_ticks: base.tie_ticks, seed: base.seed }
    })
}

// ─── Rail primitives (heo_gates.py, gate for gate) ─────────────────────────

pub struct Rails {
    pub r1: Vec<QubitId>,
    pub r2: Vec<QubitId>,
}

fn fredkin(c: &mut Builder, ctrl: QubitId, a: QubitId, b: QubitId) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

/// Measurement-based uncompute of `t = a & b`: HMR, then the CZ phase repair.
fn and_meas(c: &mut Builder, t: QubitId, a: QubitId, b: QubitId) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.cz_if(a, b, m);
    c.free_bit(m);
    c.free(t);
}

/// `b += a + cin (mod 2^n)`, `a` restored; `n - 1` CCX; carries HMR-erased.
pub(crate) fn gidney_add(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>) {
    let n = a.len();
    assert!(n >= 1 && b.len() == n);
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    carry[0] = cin;
    for i in 0..n - 1 {
        if let Some(ci) = carry[i] {
            c.cx(ci, a[i]);
            c.cx(ci, b[i]);
        }
        let t = c.alloc_qubit();
        c.ccx(a[i], b[i], t);
        carry[i + 1] = Some(t);
        if let Some(ci) = carry[i] {
            c.cx(ci, t);
        }
    }
    c.cx(a[n - 1], b[n - 1]);
    if let Some(cl) = carry[n - 1] {
        c.cx(cl, b[n - 1]);
    }
    for i in (0..n - 1).rev() {
        let next = carry[i + 1].unwrap();
        if let Some(ci) = carry[i] {
            c.cx(ci, next);
        }
        and_meas(c, next, a[i], b[i]);
        c.cx(a[i], b[i]);
        if let Some(ci) = carry[i] {
            c.cx(ci, a[i]);
            c.cx(ci, b[i]);
        }
    }
}

/// `b -= a + cin`, as NOT(NOT b + a + cin).
fn gidney_sub(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>) {
    c.x_all(b);
    gidney_add(c, a, b, cin);
    c.x_all(b);
}

/// Two's-complement resize: grow = sign-extend (alloc + CX), trim = CX from the
/// new top + free (the trimmed wire must be a sign copy: the envelope's promise).
fn resize(c: &mut Builder, reg: &mut Vec<QubitId>, w: usize) {
    while reg.len() < w {
        let q = c.alloc_qubit();
        c.cx(*reg.last().unwrap(), q);
        reg.push(q);
    }
    while reg.len() > w {
        let top = reg.pop().unwrap();
        c.cx(*reg.last().unwrap(), top);
        c.free(top);
    }
}

/// One forward rail tick. Returns the tape pair `(typ_t, s_t)`.
pub fn fwd_tick(c: &mut Builder, rails: &mut Rails, typ_prev: Option<QubitId>, wsw: usize, wad: usize) -> (QubitId, QubitId) {
    resize(c, &mut rails.r1, wsw);
    resize(c, &mut rails.r2, wsw);
    let (r1, r2) = (&rails.r1, &rails.r2);
    let ctl = r1[0];
    for i in 1..wsw {
        fredkin(c, ctl, r1[i], r2[i]);
    }
    c.cx(ctl, r2[0]);
    let mut e2 = r1[1..].to_vec();
    resize(c, &mut e2, wad);
    resize(c, &mut rails.r2, wad);
    let r2 = &rails.r2;
    let tau = c.alloc_qubit();
    c.cx(e2[wad - 1], tau);
    c.cx(r2[wad - 1], tau);
    c.x(tau);
    c.cx_all(tau, &e2);
    gidney_add(c, &e2, r2, Some(tau));
    c.cx_all(tau, &e2);
    c.x(tau);
    c.cx(e2[wad - 1], tau);
    c.cx(r2[wad - 1], tau);
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    rails.r1 = e2;
    (ctl, tau)
}

/// Exact inverse of [`fwd_tick`]; `prev` are the rail lengths before it.
#[allow(clippy::too_many_arguments)]
pub fn rev_tick(c: &mut Builder, rails: &mut Rails, typ: QubitId, s: QubitId, typ_prev: Option<QubitId>,
                wsw: usize, prev: (usize, usize)) {
    let wad = rails.r1.len();
    assert_eq!(rails.r2.len(), wad, "rev_tick: rails must both be at the add width");
    let tau = s;
    c.cx(rails.r1[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.x(tau);
    c.cx_all(tau, &rails.r1);
    gidney_sub(c, &rails.r1, &rails.r2, Some(tau));
    c.cx_all(tau, &rails.r1);
    c.x(tau);
    c.cx(rails.r1[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.free(tau);
    let ctl = typ;
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    resize(c, &mut rails.r1, wsw - 1);
    resize(c, &mut rails.r2, wsw);
    rails.r1.insert(0, ctl);
    c.cx(ctl, rails.r2[0]);
    for i in 1..wsw {
        fredkin(c, ctl, rails.r1[i], rails.r2[i]);
    }
    resize(c, &mut rails.r1, prev.0);
    resize(c, &mut rails.r2, prev.1);
}

/// `(R1, R2) = (d + p, d)` at width `max(esw[0], N + 2)`. `R2` takes over the
/// denominator's own wires.
///
/// B3a FINDING: `const_arith::sub_const` negates its constant in 256 bits, so on
/// a register wider than 256 it ADDS `2^256 - c` instead of subtracting `c`
/// (the head only calls it at width <= 256). The rail is 259 wide, so both
/// directions are written with `add_const` of `f = 2^256 - p` over the low 257
/// wires: `d + p = d + 2^256 - f` and `(d + p) + f = d + 2^256`, exact because
/// `d + p < 2^257`. Wires 257.. stay the zero sign extension.
pub fn seed_rails(c: &mut Builder, d: &[QubitId], esw0: usize, seed: Seed) -> Rails {
    if seed == Seed::ThreeDPlusP {
        return seed_rails_3dpp(c, d, esw0);
    }
    if seed == Seed::PMinusD {
        // r <- p - r is an involution: NOT r + (p + 1) = 2^w + p - r.
        let w0 = esw0.max(N + 1);
        let r1 = c.alloc_qubits(w0);
        c.cx_pairs(&d[..N], &r1[..N]);
        p_minus(c, &r1);
        let mut r2 = d.to_vec();
        r2.extend(c.alloc_qubits(w0 - N));
        return Rails { r1, r2 };
    }
    let w0 = esw0.max(N + 2);
    let r1 = c.alloc_qubits(w0);
    c.cx_pairs(&d[..N], &r1[..N]);
    c.x(r1[N]); // d + 2^256
    c.x_all(&r1[..N + 1]); // r - f = NOT(NOT r + f)  (mod 2^257)
    add_const(c, &r1[..N + 1], f());
    c.x_all(&r1[..N + 1]);
    let mut r2 = d.to_vec();
    r2.extend(c.alloc_qubits(w0 - N));
    Rails { r1, r2 }
}

/// Inverse of [`seed_rails`], then put `d` back on its ABI wires.
pub fn unseed_rails(c: &mut Builder, rails: Rails, d: &[QubitId], seed: Seed) {
    if seed == Seed::ThreeDPlusP {
        return unseed_rails_3dpp(c, rails, d);
    }
    if seed == Seed::PMinusD {
        let Rails { r1, r2 } = rails;
        p_minus(c, &r1); // p - (p - d) = d
        c.cx_pairs(&r2[..N], &r1[..N]);
        c.free_vec(&r1);
        c.free_vec(&r2[N..]);
        restore_layout(c, &r2[..N], d);
        return;
    }
    let Rails { r1, r2 } = rails;
    add_const(c, &r1[..N + 1], f()); // d + 2^256
    c.x(r1[N]);
    c.cx_pairs(&r2[..N], &r1[..N]);
    c.free_vec(&r1);
    c.free_vec(&r2[N..]);
    restore_layout(c, &r2[..N], d);
}

/// `(R1, R2) = (3d + p, d)`: v = p + 2d, so Delta = lambda*v = 2N and Sigma =
/// 4N are never 0 mod p (B3a `seed_zeros.py`: 0/5000 walks hit a zero operand).
/// `3d + p < 2^258`, so R1 needs 258 magnitude bits + sign = 259 wires.
fn seed_rails_3dpp(c: &mut Builder, d: &[QubitId], esw0: usize) -> Rails {
    let w0 = esw0.max(N + 3);
    let r1 = c.alloc_qubits(w0);
    c.cx_pairs(&d[..N], &r1[..N]); // d
    let z = c.alloc_qubits(2);
    let two_d: Vec<QubitId> = std::iter::once(z[0]).chain(d[..N].iter().copied()).chain(std::iter::once(z[1])).collect();
    gidney_add(c, &two_d, &r1[..N + 2], None); // 3d  (< 2^258)
    c.free_vec(&z);
    add_const(c, &r1, super::SECP256K1_P); // 3d + p
    let mut r2 = d.to_vec();
    r2.extend(c.alloc_qubits(w0 - N));
    Rails { r1, r2 }
}

fn unseed_rails_3dpp(c: &mut Builder, rails: Rails, d: &[QubitId]) {
    let Rails { r1, r2 } = rails;
    c.x_all(&r1); // r - p = NOT(NOT r + p)  (mod 2^w0; p < 2^256 so add_const is exact)
    add_const(c, &r1, super::SECP256K1_P);
    c.x_all(&r1); // 3d
    let z = c.alloc_qubits(2);
    let two_d: Vec<QubitId> = std::iter::once(z[0]).chain(r2[..N].iter().copied()).chain(std::iter::once(z[1])).collect();
    gidney_sub(c, &two_d, &r1[..N + 2], None); // d
    c.free_vec(&z);
    c.cx_pairs(&r2[..N], &r1[..N]);
    c.free_vec(&r1);
    c.free_vec(&r2[N..]);
    restore_layout(c, &r2[..N], d);
}

/// `r <- p - r (mod 2^len)`: NOT r, then + (p + 1). `len - 2` CCX.
fn p_minus(c: &mut Builder, r: &[QubitId]) {
    c.x_all(r);
    add_const(c, r, super::SECP256K1_P + alloy_primitives::U256::from(1u64));
}

/// Unconditional `value <- p - value` through the head's controlled negate.
fn negate(c: &mut Builder, value: &[QubitId]) {
    let one = c.alloc_qubit();
    c.x(one);
    h7::cond_negate(c, one, value);
    c.x(one);
    c.release_clean(one);
}

/// `value <- (-1)^(1 - g) value`, i.e. negate when the tape bit `g` is 0.
fn negate_if_zero(c: &mut Builder, g: QubitId, value: &[QubitId]) {
    c.x(g);
    h7::cond_negate(c, g, value);
    c.x(g);
}

/// Payload seed for the division: Base -> (2N, 0); 3dpp -> (4N, 2N).
fn seed_payload(c: &mut Builder, cfg: &HeoConfig, sig: &[QubitId]) -> Vec<QubitId> {
    h7::mod_double(c, sig); // 2N
    let del = c.alloc_qubits(N);
    if cfg.seed == Seed::ThreeDPlusP {
        c.cx_pairs(sig, &del); // Del = 2N
        h7::mod_double(c, sig); // Sig = 4N
    }
    del
}

/// Inverse of [`seed_payload`] for the multiply leg's end state
/// (Base: (2N', 0); 3dpp: (4N', 2N')): leaves Sig = N' and frees Del.
fn unseed_payload(c: &mut Builder, cfg: &HeoConfig, sig: &[QubitId], del: &[QubitId]) {
    if cfg.seed == Seed::ThreeDPlusP {
        h7::mod_halve(c, sig); // 2N' == Del
        c.cx_pairs(sig, del);
    }
    c.free_vec(del);
    h7::mod_halve(c, sig);
}

/// Move the values on `current` onto the wires `wanted` (same order). A wanted
/// wire is either later in `current` (swap) or free (reacquire, swap, free).
fn restore_layout(c: &mut Builder, current: &[QubitId], wanted: &[QubitId]) {
    let mut cur = current.to_vec();
    for i in 0..cur.len() {
        let want = wanted[i];
        if cur[i] == want {
            continue;
        }
        if let Some(j) = cur[i + 1..].iter().position(|&q| q == want) {
            let j = i + 1 + j;
            c.swap(cur[i], cur[j]);
            cur.swap(i, j);
        } else {
            c.reacquire(want);
            c.swap(cur[i], want);
            c.free(cur[i]);
            cur[i] = want;
        }
    }
}

/// Forward walk of ticks `range`, pushing the tape and the pre-tick widths.
fn walk_forward(c: &mut Builder, cfg: &HeoConfig, rails: &mut Rails, tape: &mut Vec<(QubitId, QubitId)>,
                widths: &mut Vec<(usize, usize)>, t: usize) -> (QubitId, QubitId) {
    widths.push((rails.r1.len(), rails.r2.len()));
    let prev = tape.last().map(|&(typ, _)| typ);
    let pair = fwd_tick(c, rails, prev, cfg.esw[t], cfg.ead[t]);
    tape.push(pair);
    pair
}

fn walk_back_tick(c: &mut Builder, cfg: &HeoConfig, rails: &mut Rails, tape: &[(QubitId, QubitId)],
                  widths: &[(usize, usize)], t: usize) {
    let (typ, s) = tape[t];
    let prev = if t > 0 { Some(tape[t - 1].0) } else { None };
    rev_tick(c, rails, typ, s, prev, cfg.esw[t], widths[t]);
}

/// Per-tick op markers `(t, rail_start, cell_start, tick_end)` recorded under
/// `HEO_TICK_TRACE` for the probe's phase checkpoints.
pub static TICK_MARKS: Mutex<Vec<(usize, usize, usize, usize)>> = Mutex::new(Vec::new());

// ─── Payload cell (the head's replay cell + 256-Fredkin role routing) ─────

/// Forward payload cell of tick `t`. B2's HEO-specialised cell replaces the
/// `h7::add_halve` call; the routing is at its MC floor (256 CCX).
pub fn cell_fwd(c: &mut Builder, cfg: &HeoConfig, t: usize, typ: QubitId, s: QubitId, sig: &[QubitId], del: &[QubitId]) {
    let proxy = h7::proxy_round(cfg.esw[t]);
    let fw = h7::fold_window(proxy, false);
    c.x(typ); // the head cell adds (-1)^sign * source; HEO wants -(-1)^g Del
    let tie = (t < cfg.tie_ticks).then_some(typ);
    h7::with_tie(tie, || h7::add_halve(c, typ, del, sig, fw, proxy));
    c.x(typ);
    route(c, s, sig, del);
}

/// Inverse payload cell of tick `t` (multiply leg).
pub fn cell_rev(c: &mut Builder, cfg: &HeoConfig, t: usize, typ: QubitId, s: QubitId, sig: &[QubitId], del: &[QubitId]) {
    route(c, s, sig, del);
    let proxy = h7::proxy_round(cfg.esw[t]);
    let fw = h7::fold_window(proxy, true);
    let tie = (t < cfg.tie_ticks).then_some(typ);
    h7::with_tie(tie, || h7::double_add(c, typ, del, sig, fw, proxy)); // Sig = 2 Sig' + (-1)^g Del
}

fn route(c: &mut Builder, s: QubitId, sig: &[QubitId], del: &[QubitId]) {
    for i in 0..N {
        h7::cswap(c, s, sig[i], del[i]);
    }
}

// ─── The two legs ──────────────────────────────────────────────────────────

/// `numerator /= denominator (mod p)`.
pub fn divide(c: &mut Builder, numerator: &[QubitId], denominator: &[QubitId]) {
    let cfg = config();
    if cfg.schedule == Schedule::Carry {
        return carry::divide(c, numerator, denominator);
    }
    let r = cfg.rounds();
    c.set_phase("heo_div_seed");
    let mut rails = seed_rails(c, denominator, cfg.esw[0], cfg.seed);
    if cfg.seed == Seed::PMinusD {
        return divide_pmd(c, cfg, rails, numerator, denominator);
    }
    let sig = numerator;
    let del = seed_payload(c, cfg, sig); // (2N, 0) or (4N, 2N)
    c.set_phase("heo_div_walk");
    let (mut tape, mut widths) = (Vec::with_capacity(r), Vec::with_capacity(r));
    let trace = truthy("HEO_TICK_TRACE");
    for t in 0..r {
        let o0 = c.op_count();
        let (typ, s) = walk_forward(c, cfg, &mut rails, &mut tape, &mut widths, t);
        let o1 = c.op_count();
        cell_fwd(c, cfg, t, typ, s, sig, &del);
        if trace {
            eprintln!("HEO_TICK div {t} rail={o0} cell={o1} end={} proxy={} live={}", c.op_count(),
                h7::proxy_round(cfg.esw[t]), c.active_qubits());
            TICK_MARKS.lock().unwrap().push((t, o0, o1, c.op_count()));
        }
    }
    c.set_phase("heo_div_endpoint");
    c.cx_pairs(sig, &del); // Sig == Del == N/d at park: 0 CCX
    c.free_vec(&del);
    c.set_phase("heo_div_walkback");
    for t in (0..r).rev() {
        walk_back_tick(c, cfg, &mut rails, &tape, &widths, t);
    }
    c.set_phase("heo_div_unseed");
    unseed_rails(c, rails, denominator, cfg.seed);
}

/// `numerator *= denominator (mod p)`: the inverse map from `(y, y)`.
pub fn multiply(c: &mut Builder, numerator: &[QubitId], denominator: &[QubitId]) {
    let cfg = config();
    if cfg.schedule == Schedule::Carry {
        return carry::multiply(c, numerator, denominator);
    }
    let r = cfg.rounds();
    c.set_phase("heo_mul_seed");
    let mut rails = seed_rails(c, denominator, cfg.esw[0], cfg.seed);
    if cfg.seed == Seed::PMinusD {
        return multiply_pmd(c, cfg, rails, numerator, denominator);
    }
    c.set_phase("heo_mul_walk");
    let (mut tape, mut widths) = (Vec::with_capacity(r), Vec::with_capacity(r));
    for t in 0..r {
        walk_forward(c, cfg, &mut rails, &mut tape, &mut widths, t);
    }
    c.set_phase("heo_mul_replay");
    let sig = numerator;
    let del = c.alloc_qubits(N);
    c.cx_pairs(sig, &del); // (Sig, Del) = (y, y)
    let trace = truthy("HEO_TICK_TRACE");
    for t in (0..r).rev() {
        let (typ, s) = tape[t];
        let o0 = c.op_count();
        cell_rev(c, cfg, t, typ, s, sig, &del);
        let o1 = c.op_count();
        walk_back_tick(c, cfg, &mut rails, &tape, &widths, t);
        if trace {
            TICK_MARKS.lock().unwrap().push((t, o0, o1, c.op_count()));
        }
    }
    c.set_phase("heo_mul_unseed");
    unseed_payload(c, cfg, sig, &del); // Sig = y d, Del freed
    unseed_rails(c, rails, denominator, cfg.seed);
}

/// Tick-0 closed form for the `pmd` seed: from (Sig, Del) = (0, -2N) the cell gives
/// Sig = -(-1)^g0 Del / 2 = (-1)^g0 N exactly; written into the zero register `out`.
fn tick0_closed_form_into(c: &mut Builder, g0: QubitId, del: &[QubitId], out: &[QubitId]) {
    c.cx_pairs(del, out); // -2N
    h7::mod_halve(c, out); // -N
    negate_if_zero(c, g0, out); // (-1)^g0 N
}

fn divide_pmd(c: &mut Builder, cfg: &HeoConfig, mut rails: Rails, numerator: &[QubitId], denominator: &[QubitId]) {
    let r = cfg.rounds();
    let del = numerator; // Del lives on the ABI wires: -2N
    h7::mod_double(c, del);
    negate(c, del);
    let sig = c.alloc_qubits(N); // Sig = 0 (the public zero, tick 0 only)
    c.set_phase("heo_div_walk");
    let (mut tape, mut widths) = (Vec::with_capacity(r), Vec::with_capacity(r));
    let trace = truthy("HEO_TICK_TRACE");
    for t in 0..r {
        let o0 = c.op_count();
        let (typ, s) = walk_forward(c, cfg, &mut rails, &mut tape, &mut widths, t);
        let o1 = c.op_count();
        if t == 0 {
            tick0_closed_form_into(c, typ, del, &sig);
            route(c, s, &sig, del);
        } else {
            cell_fwd(c, cfg, t, typ, s, &sig, del);
        }
        if trace {
            TICK_MARKS.lock().unwrap().push((t, o0, o1, c.op_count()));
        }
    }
    c.set_phase("heo_div_endpoint");
    negate_if_zero(c, tape[r - 1].0, del); // Del = (-1)^(1-typ_last) q -> q
    c.cx_pairs(del, &sig); // Sig == Del == q
    c.free_vec(&sig);
    c.set_phase("heo_div_walkback");
    for t in (0..r).rev() {
        walk_back_tick(c, cfg, &mut rails, &tape, &widths, t);
    }
    c.set_phase("heo_div_unseed");
    unseed_rails(c, rails, denominator, cfg.seed);
}

fn multiply_pmd(c: &mut Builder, cfg: &HeoConfig, mut rails: Rails, numerator: &[QubitId], denominator: &[QubitId]) {
    let r = cfg.rounds();
    c.set_phase("heo_mul_walk");
    let (mut tape, mut widths) = (Vec::with_capacity(r), Vec::with_capacity(r));
    for t in 0..r {
        walk_forward(c, cfg, &mut rails, &mut tape, &mut widths, t);
    }
    c.set_phase("heo_mul_replay");
    let del = numerator;
    let sig = c.alloc_qubits(N);
    c.cx_pairs(del, &sig); // Sig = y
    negate_if_zero(c, tape[r - 1].0, del); // Del = (-1)^(1-typ_last) y
    let trace = truthy("HEO_TICK_TRACE");
    for t in (1..r).rev() {
        let (typ, s) = tape[t];
        let o0 = c.op_count();
        cell_rev(c, cfg, t, typ, s, &sig, del);
        let o1 = c.op_count();
        walk_back_tick(c, cfg, &mut rails, &tape, &widths, t);
        if trace {
            TICK_MARKS.lock().unwrap().push((t, o0, o1, c.op_count()));
        }
    }
    let (g0, s0) = tape[0];
    route(c, s0, &sig, del);
    let tmp = c.alloc_qubits(N);
    tick0_closed_form_into(c, g0, del, &tmp); // (-1)^g0 N'
    c.cx_pairs(&tmp, &sig); // Sig -> 0 exactly
    negate_if_zero(c, g0, &tmp); // undo the closed form on tmp
    h7::mod_double(c, &tmp);
    c.cx_pairs(del, &tmp);
    c.free_vec(&tmp);
    walk_back_tick(c, cfg, &mut rails, &tape, &widths, 0);
    c.set_phase("heo_mul_unseed");
    c.free_vec(&sig);
    negate(c, del); // 2N'
    h7::mod_halve(c, del); // N' = y d
    unseed_rails(c, rails, denominator, cfg.seed);
}

/// Rails only: seed, R forward ticks, R reverse ticks, unseed (the A2 check).
pub fn rails_roundtrip(c: &mut Builder, denominator: &[QubitId]) {
    let cfg = config();
    let r = cfg.rounds();
    c.set_phase("heo_rails_seed");
    let mut rails = seed_rails(c, denominator, cfg.esw[0], cfg.seed);
    c.set_phase("heo_rails_fwd");
    let (mut tape, mut widths) = (Vec::with_capacity(r), Vec::with_capacity(r));
    for t in 0..r {
        walk_forward(c, cfg, &mut rails, &mut tape, &mut widths, t);
    }
    c.set_phase("heo_rails_rev");
    for t in (0..r).rev() {
        walk_back_tick(c, cfg, &mut rails, &tape, &widths, t);
    }
    c.set_phase("heo_rails_unseed");
    unseed_rails(c, rails, denominator, cfg.seed);
}

// ─── Probe circuits for `examples/heo_probe.rs` ────────────────────────────

/// B3b: the classical offset `sub_square` leaves in its output (added back by the shell).
pub fn square_offset() -> alloy_primitives::U256 {
    super::square::sub_square_offset()
}

pub struct Probe {
    pub ops: Vec<Op>,
    pub x: Vec<QubitId>,
    pub y: Vec<QubitId>,
    pub num_qubits: usize,
    pub num_bits: usize,
    pub peak: u32,
}

/// Build one leg on a bare `(x, y)` pair: `rails`, `div` (y /= x), `mul`
/// (y *= x) or `divmul` (both; y must come back).
pub fn probe(kind: &str) -> Probe {
    let mut b = Builder::new();
    let x = b.alloc_qubits(N);
    let y = b.alloc_qubits(N);
    match kind {
        "rails" => rails_roundtrip(&mut b, &x),
        "seed" => {
            let rails = seed_rails(&mut b, &x, config().esw[0], config().seed);
            unseed_rails(&mut b, rails, &x, config().seed);
        }
        "gidney" => {
            // one width-wad add/sub pair on scratch copies: b += a + cin then undone
            let w = 64;
            let a: Vec<QubitId> = b.alloc_qubits(w);
            let acc: Vec<QubitId> = b.alloc_qubits(w);
            b.cx_pairs(&x[..w], &a);
            b.cx_pairs(&x[w..2 * w], &acc);
            gidney_add(&mut b, &a, &acc, Some(y[0]));
            gidney_sub(&mut b, &a, &acc, Some(y[0]));
            b.cx_pairs(&x[w..2 * w], &acc);
            b.cx_pairs(&x[..w], &a);
            b.free_vec(&acc);
            b.free_vec(&a);
        }
        "square" => super::square::sub_square(&mut b, &x, &y),
        "div" => divide(&mut b, &y, &x),
        "mul" => multiply(&mut b, &y, &x),
        "divmul" => {
            divide(&mut b, &y, &x);
            multiply(&mut b, &y, &x);
        }
        other => panic!("probe kind {other:?}"),
    }
    b.finalize_records();
    let (num_qubits, num_bits) = b.i13_dims();
    let peak = b.peak_total();
    Probe { ops: b.take_ops(), x, y, num_qubits, num_bits, peak }
}
