//! SKY-COF masked-ring point addition: `(x, y) += (ox, oy)` on secp256k1, affine, `(ox, oy)` classical.
//!
//! Same legs as [`crate::point_add::skycof::pointadd`], with the walk on the shared ring registers
//! ([`super::rwalk`]):
//! 1. `x -= ox` (d), `y -= oy` (dy).
//! 2. Division leg: walk forward on d with dy held -> `s = sigma 2^R / d` (`sigma = +1` iff the C-parity wire
//!    is set); `lam = dy * s * 2^-R * sigma` (modmul #1, negation controlled by NOT sign); HMR dy; walk back;
//!    debt `t = lam * d` (#2), `Z^m t`, uncompute (#3).
//! 3. `x += 3 ox`, `x -= lam^2` (Skywalk's square): x = D' = ox - x3.
//! 4. Multiply leg: `tmp = lam * D'` (#4); HMR lam; walk forward on D'; `lam' = tmp * s' * 2^-R * sigma'` (#5),
//!    `Z^m lam'`, uncompute (#6); walk back.
//! 5. `y = tmp - oy`, `x = ox - x`.
//!
//! The recipe is fixed in source; research overrides (`SKYCOF_*`) only under `SKYCOF_RESEARCH=1`.
use super::rwalk::{self, WEnv};
use crate::circuit::{BitId, Op, QubitId as Q};
use crate::point_add::builder::Builder;
use crate::point_add::classical::{coord_add3x, coord_rsub, coord_sub};
use crate::point_add::skycof::pointadd::{hmr_all, knob, pay_debt, place};
use crate::point_add::skycof_mm as mm;
use crate::point_add::square::sub_square;
use crate::point_add::N;
use std::sync::OnceLock;

thread_local! {
    /// Research: section boundaries `(name, op index)` of the last build, when enabled.
    pub static MARKS: std::cell::RefCell<Option<Vec<(&'static str, usize)>>> = const { std::cell::RefCell::new(None) };
}

fn mark(c: &mut Builder, name: &'static str) {
    MARKS.with(|m| {
        if let Some(v) = m.borrow_mut().as_mut() {
            v.push((name, c.op_count()));
        }
    });
    c.set_phase(name);
}

/// Source defaults.
pub const CAP: usize = 1002;
pub const PARK_J: usize = 16;
pub const ODO_BITS: usize = 7;
pub const MM_GUARD: usize = 25;
pub const MM_CMPW: usize = 24;

fn knob_usize(name: &str, default: usize) -> usize {
    knob(name).map(|v| v.parse().unwrap_or_else(|_| panic!("{name}={v}: not an integer"))).unwrap_or(default)
}

pub struct Params {
    pub cap: usize,
    pub mm_guard: usize,
    pub mm_cmpw: usize,
}

pub fn params() -> &'static Params {
    static P: OnceLock<Params> = OnceLock::new();
    P.get_or_init(|| {
        let p = Params {
            cap: knob_usize("SKYCOF_CAP", CAP),
            mm_guard: knob_usize("SKYCOF_MM_GUARD", MM_GUARD),
            mm_cmpw: knob_usize("SKYCOF_MM_CMPW", MM_CMPW),
        };
        eprintln!("SKYCOF_RING_PARAMS cap={} mm_guard={} mm_cmpw={}", p.cap, p.mm_guard, p.mm_cmpw);
        p
    })
}

/// Decoder lookback (0 or 1), fixed in source; research override `SKYCOF_RING_K`.
pub const K: usize = 1;

pub fn envelope() -> &'static WEnv {
    static E: OnceLock<WEnv> = OnceLock::new();
    E.get_or_init(|| {
        let k = knob_usize("SKYCOF_RING_K", K);
        let txt = if k == 1 { include_str!("env_k1.tsv") } else { include_str!("env_k0.tsv") };
        let mut env = WEnv::from_tsv(txt, Some(params().cap), PARK_J, ODO_BITS);
        let t1 = t1();
        if t1 > 0 {
            // hybrid: the history width from the switch on is the hybrid walk's (public k2 decoder before t1)
            let tab = include_str!("env_hyb_h.tsv");
            let mut col = None;
            let mut rows: Vec<usize> = Vec::new();
            for l in tab.lines() {
                if l.starts_with('#') || l.trim().is_empty() {
                    continue;
                }
                let f: Vec<&str> = l.split(char::from(9u8)).collect();
                if f[0] == "t" {
                    col = f.iter().position(|x| *x == format!("T1_{t1}"));
                    assert!(col.is_some(), "no hybrid history column for T1={t1}");
                    continue;
                }
                rows.push(f[col.unwrap()].trim().parse().unwrap());
            }
            assert_eq!(rows.len(), env.r);
            // the whole column: before t1 it is the public walk's history (the ring part never reads it)
            for t in 0..env.r {
                env.h[t] = rows[t];
            }
            for t in 1..env.r {
                env.h[t] = env.h[t].max(env.h[t - 1]);
            }
        }
        env
    })
}

/// Switch tick of the hybrid walk (0 = the ring walk from the start), fixed in source; research override
/// `SKYCOF_HYB_T1`.
pub const T1: usize = 270;

pub fn t1() -> usize {
    knob_usize("SKYCOF_HYB_T1", T1)
}

fn walk_fwd(c: &mut Builder, d: &[Q]) -> super::hwalk::HParked {
    let env = envelope();
    let t1 = t1();
    assert!(t1 > 0, "walk_fwd: hybrid only");
    let pp = crate::point_add::skycof::pointadd::params();
    let penv = crate::point_add::skycof::pointadd::envelope();
    super::hwalk::forward(c, env, &pp.walk, penv, d, t1)
}

fn walk_back(c: &mut Builder, hp: super::hwalk::HParked) -> Vec<Q> {
    let env = envelope();
    let pp = crate::point_add::skycof::pointadd::params();
    let penv = crate::point_add::skycof::pointadd::envelope();
    super::hwalk::backward(c, env, &pp.walk, penv, hp, t1())
}

/// Fixed recipe for the shared parts (coordinate ops, Skywalk's square), with this circuit's cap.
pub fn install_recipe() {
    crate::point_add::skycof::pointadd::install_recipe();
    std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", params().cap.to_string());
}

fn mm_cfg(c: &Builder, extra_live: usize) -> mm::Cfg {
    let p = params();
    let room = p.cap.saturating_sub(c.active_qubits() as usize + extra_live);
    assert!(room >= 8, "ring modmul: room {room} too small (live {})", c.active_qubits());
    mm::Cfg::windowed(mm::Field::secp(), p.mm_guard, p.mm_cmpw, room)
}

/// `out = a * b * 2^-k * (-1)^neg`, out fresh; `neg` a wire (or constant false when None).
fn mulf(c: &mut Builder, a: &[Q], b: &[Q], k: usize, neg: Option<Q>) -> Vec<Q> {
    let cfg = mm_cfg(c, N);
    mm::mul_fwd(c, mm::Field::secp(), cfg, a, b, k, neg)
}

/// Exact inverse of [`mulf`]: clears and frees `out`.
fn mulf_inv(c: &mut Builder, a: &[Q], b: &[Q], k: usize, neg: Option<Q>, out: Vec<Q>) {
    let cfg = mm_cfg(c, 0);
    let out = mm::mul_inv(c, mm::Field::secp(), cfg, a, b, k, neg, out);
    c.free_vec(&out);
}

/// `y <- y / x` (division leg). Returns (x wires, lam wires).
fn div_leg(c: &mut Builder, d: Vec<Q>, dy: Vec<Q>) -> (Vec<Q>, Vec<Q>) {
    let env = envelope();
    mark(c, "sc_div_fwd");
    let hyb = t1() > 0;
    let (pk, hp) = if hyb { let hp = walk_fwd(c, &d); (None, Some(hp)) } else { (Some(rwalk::forward(c, env, &d)), None) };
    let (s_w, sign_w) = match (&pk, &hp) { (Some(p), _) => (p.s.clone(), p.sign), (_, Some(h)) => (h.pk.s.clone(), h.pk.sign), _ => unreachable!() };
    mark(c, "sc_div_mm1");
    // s = +2^R/d when sign = 1, -2^R/d when sign = 0: negate when NOT sign
    c.x(sign_w);
    let lam = mulf(c, &dy, &s_w, env.r, Some(sign_w));
    c.x(sign_w);
    mark(c, "sc_div_hmr");
    let m = hmr_all(c, &dy);
    mark(c, "sc_div_back");
    let d = match (pk, hp) { (Some(p), _) => rwalk::backward(c, env, p), (_, Some(h)) => walk_back(c, h), _ => unreachable!() };
    mark(c, "sc_div_debt");
    let t = mulf(c, &lam, &d, 0, None);
    pay_debt(c, &t, &m);
    mulf_inv(c, &lam, &d, 0, None, t);
    c.free_bit_vec(&m);
    (d, lam)
}

/// `y <- y * x` given y = lam, x = D' (multiply leg). Returns (x wires, y wires = lam * D').
fn mul_leg(c: &mut Builder, dp: Vec<Q>, lam: Vec<Q>) -> (Vec<Q>, Vec<Q>) {
    let env = envelope();
    mark(c, "sc_mul_mm4");
    let tmp = mulf(c, &lam, &dp, 0, None);
    mark(c, "sc_mul_hmr");
    let m = hmr_all(c, &lam);
    mark(c, "sc_mul_fwd");
    let hyb = t1() > 0;
    let (pk, hp) = if hyb { let hp = walk_fwd(c, &dp); (None, Some(hp)) } else { (Some(rwalk::forward(c, env, &dp)), None) };
    let (s_w, sign_w) = match (&pk, &hp) { (Some(p), _) => (p.s.clone(), p.sign), (_, Some(h)) => (h.pk.s.clone(), h.pk.sign), _ => unreachable!() };
    mark(c, "sc_mul_mm5");
    c.x(sign_w);
    let lam2 = mulf(c, &tmp, &s_w, env.r, Some(sign_w));
    pay_debt(c, &lam2, &m);
    mulf_inv(c, &tmp, &s_w, env.r, Some(sign_w), lam2);
    c.x(sign_w);
    c.free_bit_vec(&m);
    mark(c, "sc_mul_back");
    let dp = match (pk, hp) { (Some(p), _) => rwalk::backward(c, env, p), (_, Some(h)) => walk_back(c, h), _ => unreachable!() };
    (dp, tmp)
}

/// The SKY-COF masked-ring candidate circuit.
pub fn build_point_add() -> Vec<Op> {
    build_point_add_regs().0
}

/// [`build_point_add`] with the ABI registers and the simulator dimensions (probes).
#[allow(clippy::type_complexity)]
pub fn build_point_add_regs() -> (Vec<Op>, Vec<Q>, Vec<Q>, Vec<BitId>, Vec<BitId>, usize, usize) {
    let _ = params();
    let circ = &mut Builder::new();
    let x: Vec<Q> = circ.alloc_qubits(N);
    let y: Vec<Q> = circ.alloc_qubits(N);
    let ox: Vec<BitId> = circ.alloc_bits(N);
    let oy: Vec<BitId> = circ.alloc_bits(N);

    mark(circ, "coord_x_sub");
    coord_sub(circ, &x, &ox);
    mark(circ, "coord_y_sub");
    coord_sub(circ, &y, &oy);

    let (x1, y1) = div_leg(circ, x.clone(), y.clone());

    mark(circ, "coord_add3x");
    coord_add3x(circ, &x1, &ox);
    mark(circ, "square");
    sub_square(circ, &x1, &y1);

    let (x2, y2) = mul_leg(circ, x1, y1);

    mark(circ, "coord_y_sub_final");
    coord_sub(circ, &y2, &oy);
    mark(circ, "coord_rsub_final");
    coord_rsub(circ, &x2, &ox);
    mark(circ, "place");
    place(circ, x2, y2, &x, &y);
    mark(circ, "end");

    circ.declare_qubit_register(&x);
    circ.declare_qubit_register(&y);
    circ.declare_bit_register(&ox);
    circ.declare_bit_register(&oy);
    circ.finalize_records();
    let ops = circ.take_ops();
    let (nq, nb) = circ.i13_dims();
    (ops, x, y, ox, oy, nq, nb)
}
