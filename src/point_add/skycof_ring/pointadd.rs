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

/// Source defaults.
pub const CAP: usize = 998;
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
        WEnv::from_tsv(txt, Some(params().cap), PARK_J, ODO_BITS)
    })
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
    c.set_phase("sc_div_fwd");
    let pk = rwalk::forward(c, env, &d);
    c.set_phase("sc_div_mm1");
    // s = +2^R/d when sign = 1, -2^R/d when sign = 0: negate when NOT sign
    c.x(pk.sign);
    let lam = mulf(c, &dy, &pk.s, env.r, Some(pk.sign));
    c.x(pk.sign);
    c.set_phase("sc_div_hmr");
    let m = hmr_all(c, &dy);
    c.set_phase("sc_div_back");
    let d = rwalk::backward(c, env, pk);
    c.set_phase("sc_div_debt");
    let t = mulf(c, &lam, &d, 0, None);
    pay_debt(c, &t, &m);
    mulf_inv(c, &lam, &d, 0, None, t);
    c.free_bit_vec(&m);
    (d, lam)
}

/// `y <- y * x` given y = lam, x = D' (multiply leg). Returns (x wires, y wires = lam * D').
fn mul_leg(c: &mut Builder, dp: Vec<Q>, lam: Vec<Q>) -> (Vec<Q>, Vec<Q>) {
    let env = envelope();
    c.set_phase("sc_mul_mm4");
    let tmp = mulf(c, &lam, &dp, 0, None);
    c.set_phase("sc_mul_hmr");
    let m = hmr_all(c, &lam);
    c.set_phase("sc_mul_fwd");
    let pk = rwalk::forward(c, env, &dp);
    c.set_phase("sc_mul_mm5");
    c.x(pk.sign);
    let lam2 = mulf(c, &tmp, &pk.s, env.r, Some(pk.sign));
    pay_debt(c, &lam2, &m);
    mulf_inv(c, &tmp, &pk.s, env.r, Some(pk.sign), lam2);
    c.x(pk.sign);
    c.free_bit_vec(&m);
    c.set_phase("sc_mul_back");
    let dp = rwalk::backward(c, env, pk);
    (dp, tmp)
}

/// The SKY-COF masked-ring candidate circuit.
pub fn build_point_add() -> Vec<Op> {
    let _ = params();
    let circ = &mut Builder::new();
    let x: Vec<Q> = circ.alloc_qubits(N);
    let y: Vec<Q> = circ.alloc_qubits(N);
    let ox: Vec<BitId> = circ.alloc_bits(N);
    let oy: Vec<BitId> = circ.alloc_bits(N);

    circ.set_phase("coord_x_sub");
    coord_sub(circ, &x, &ox);
    circ.set_phase("coord_y_sub");
    coord_sub(circ, &y, &oy);

    let (x1, y1) = div_leg(circ, x.clone(), y.clone());

    circ.set_phase("coord_add3x");
    coord_add3x(circ, &x1, &ox);
    circ.set_phase("square");
    sub_square(circ, &x1, &y1);

    let (x2, y2) = mul_leg(circ, x1, y1);

    circ.set_phase("coord_y_sub_final");
    coord_sub(circ, &y2, &oy);
    circ.set_phase("coord_rsub_final");
    coord_rsub(circ, &x2, &ox);
    circ.set_phase("place");
    place(circ, x2, y2, &x, &y);
    circ.set_phase("end");

    circ.declare_qubit_register(&x);
    circ.declare_qubit_register(&y);
    circ.declare_bit_register(&ox);
    circ.declare_bit_register(&oy);
    circ.finalize_records();
    circ.take_ops()
}
