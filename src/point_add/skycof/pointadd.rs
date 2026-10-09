//! SKY-COF point addition: `(x, y) += (ox, oy)` on secp256k1, affine, `(ox, oy)` classical.
//!
//! Phases:
//! 1. `x -= ox` (d), `y -= oy` (dy).
//! 2. Division leg: walk forward on d with dy held -> `s = -2^R / d`; `lam = dy * s * (-2^-R)` (modmul #1);
//!    HMR dy (phase debt `m . dy`); walk back (d restored); debt: `t = lam * d` (#2), `Z^m t`, uncompute (#3).
//! 3. `x += 3 ox`, `x -= lam^2` (Skywalk's square): x = D' = ox - x3.
//! 4. Multiply leg: `tmp = lam * D'` (#4); HMR lam; walk forward on D' with tmp held; `lam' = tmp * s' * (-2^-R)`
//!    (#5), `Z^m lam'`, uncompute (#6); walk back.
//! 5. `y = tmp - oy`, `x = ox - x`.
//!
//! The recipe is fixed in source (an empty environment builds it). Research overrides (`SKYCOF_*`) are read
//! only when `SKYCOF_RESEARCH=1` was set in the process environment before `build()` cleared it.
use super::walk::{self, Envelope, WalkParams};
use crate::circuit::{BitId, Op, QubitId as Q};
use crate::point_add::builder::Builder;
use crate::point_add::classical::{coord_add3x, coord_rsub, coord_sub};
use crate::point_add::skycof_mm as mm;
use crate::point_add::square::sub_square;
use crate::point_add::N;
use std::collections::HashMap;
use std::sync::OnceLock;

static KNOBS: OnceLock<HashMap<String, String>> = OnceLock::new();

/// Snapshot the research knobs before `build()` clears the environment.
pub fn snapshot_knobs() {
    let on = std::env::var("SKYCOF_RESEARCH").is_ok_and(|v| v == "1");
    let mut m = HashMap::new();
    if on {
        for (k, v) in std::env::vars() {
            if k.starts_with("SKYCOF_") {
                m.insert(k, v);
            }
        }
    }
    let _ = KNOBS.set(m);
}

pub fn knob(name: &str) -> Option<String> {
    KNOBS.get().and_then(|m| m.get(name).cloned())
}

pub fn knob_flag(name: &str) -> bool {
    knob(name).is_some_and(|v| v != "0" && !v.is_empty())
}

fn knob_usize(name: &str, default: usize) -> usize {
    knob(name).map(|v| v.parse().unwrap_or_else(|_| panic!("{name}={v}: not an integer"))).unwrap_or(default)
}

/// Source defaults.
pub const CAP: usize = 1005;
pub const R: usize = 404;
pub const PARK_J: usize = 14;
pub const W_DEC: usize = 64;
/// Window of the k2 decoder (and of the k = 0 decoder on the ticks it still disposes).
pub const W_DEC_K2: usize = 56;
pub const FOLD_W: usize = 58;
pub const ODO_BITS: usize = 7;
pub const MM_GUARD: usize = 25;
pub const MM_CMPW: usize = 24;

pub struct Params {
    pub walk: WalkParams,
    pub mm_guard: usize,
    pub mm_cmpw: usize,
}

pub fn params() -> &'static Params {
    static P: OnceLock<Params> = OnceLock::new();
    P.get_or_init(|| {
        let walk = WalkParams {
            r: knob_usize("SKYCOF_R", R),
            park_j: knob_usize("SKYCOF_PARKJ", PARK_J),
            w_dec: knob_usize("SKYCOF_WDEC", if super::walk::k2_on() { W_DEC_K2 } else { W_DEC }),
            fold_w: knob_usize("SKYCOF_FOLDW", FOLD_W),
            odo_bits: knob_usize("SKYCOF_ODO", ODO_BITS),
            cap: knob_usize("SKYCOF_CAP", CAP),
        };
        let p = Params { walk, mm_guard: knob_usize("SKYCOF_MM_GUARD", MM_GUARD), mm_cmpw: knob_usize("SKYCOF_MM_CMPW", MM_CMPW) };
        eprintln!("SKYCOF_PARAMS {:?} mm_guard={} mm_cmpw={}", p.walk, p.mm_guard, p.mm_cmpw);
        p
    })
}

pub fn envelope() -> &'static Envelope {
    static E: OnceLock<Envelope> = OnceLock::new();
    E.get_or_init(|| Envelope::design(params().walk.r))
}

/// Fixed recipe for the parts shared with the head tree (coordinate ops, Skywalk's square, post-passes).
pub fn install_recipe() {
    let cap = params().walk.cap.to_string();
    match knob("SKYCOF_SQ_RECIPE").as_deref() {
        Some("base") => {}
        None | Some("sky") => {
            // the 1145 tree's full recipe, minus the legs' fusions into the coordinate ops
            crate::point_add::install_skywalk_submission_recipe();
            // NATIVE_SFUSE_B fuses the square's last B fold into the head multiply's round 0: off here, the
            // square must be complete on its own (x -= y^2 exactly).
            for k in ["BACK_SEAM_FUSE", "FD_COORD_FUSE", "FD_COORD_LOW_ONE", "R4_YSUB_FUSE", "R4_YFIN_FUSE", "R5_YFIN2", "R4_FDP_FUSE", "NATIVE_SFUSE_B"] {
                std::env::remove_var(k);
            }
            // research: extra names to drop / set (SKYCOF_SQ_DROP=a,b  SKYCOF_SQ_SET=k=v,k=v)
            if let Some(v) = knob("SKYCOF_SQ_DROP") {
                for k in v.split(',').filter(|k| !k.is_empty()) {
                    std::env::remove_var(k);
                }
            }
            if let Some(v) = knob("SKYCOF_SQ_SET") {
                for kv in v.split(',').filter(|k| !k.is_empty()) {
                    let (k, val) = kv.split_once('=').expect("SKYCOF_SQ_SET k=v");
                    std::env::set_var(k, val);
                }
            }
        }
        Some(o) => panic!("SKYCOF_SQ_RECIPE={o}"),
    }
    for (k, v) in [
        ("HEO_RESEARCH", "1"),
        ("HEO_PIN_PP_WALK_MAX_QUBITS", cap.as_str()),
        ("SKY_NORW", "1"),
        ("HEO_MABSORB", "1"),
        ("HEO_PHASE_REPORT", "1"),
    ] {
        std::env::set_var(k, v);
    }
}

fn mm_cfg(c: &Builder, extra_live: usize) -> mm::Cfg {
    let p = params();
    let room = p.walk.cap.saturating_sub(c.active_qubits() as usize + extra_live);
    assert!(room >= 8, "skycof modmul: room {room} too small (live {})", c.active_qubits());
    mm::Cfg::windowed(mm::Field::secp(), p.mm_guard, p.mm_cmpw, room)
}

/// `out = a * b * 2^-k * (-1)^neg`, out fresh.
pub(crate) fn mulf(c: &mut Builder, a: &[Q], b: &[Q], k: usize, neg: bool) -> Vec<Q> {
    let f = mm::Field::secp();
    let ng = neg.then(|| {
        let q = c.alloc_qubit();
        c.x(q);
        q
    });
    let cfg = mm_cfg(c, N);
    let out = mm::mul_fwd(c, f, cfg, a, b, k, ng);
    if let Some(q) = ng {
        c.x(q);
        c.release_clean(q);
    }
    out
}

/// Exact inverse of [`mulf`]: clears and frees `out`.
pub(crate) fn mulf_inv(c: &mut Builder, a: &[Q], b: &[Q], k: usize, neg: bool, out: Vec<Q>) {
    let f = mm::Field::secp();
    let ng = neg.then(|| {
        let q = c.alloc_qubit();
        c.x(q);
        q
    });
    let cfg = mm_cfg(c, 0);
    let out = mm::mul_inv(c, f, cfg, a, b, k, ng, out);
    if let Some(q) = ng {
        c.x(q);
        c.release_clean(q);
    }
    c.free_vec(&out);
}

/// HMR every wire of `v` (X-basis measurement); returns the outcome bits. The wires are released.
pub(crate) fn hmr_all(c: &mut Builder, v: &[Q]) -> Vec<BitId> {
    let m = c.alloc_bits(v.len());
    for (&q, &b) in v.iter().zip(&m) {
        c.hmr(q, b);
        c.release_clean(q);
    }
    m
}

/// Pay the HMR phase debt: `Z^m` on a register that holds the measured value again.
pub(crate) fn pay_debt(c: &mut Builder, v: &[Q], m: &[BitId]) {
    for (&q, &b) in v.iter().zip(m) {
        c.z_if(q, b);
    }
}

/// `y <- y / x` (division leg). Returns (x wires, lam wires).
fn div_leg(c: &mut Builder, d: Vec<Q>, dy: Vec<Q>) -> (Vec<Q>, Vec<Q>) {
    let p = params();
    let env = envelope();
    let r = p.walk.r;
    c.set_phase("sc_div_fwd");
    let pk = walk::forward(c, &p.walk, env, &d);
    c.set_phase("sc_div_mm1");
    let lam = mulf(c, &dy, &pk.s, r, true);
    c.set_phase("sc_div_hmr");
    let m = hmr_all(c, &dy);
    c.set_phase("sc_div_back");
    let d = walk::backward(c, &p.walk, env, pk);
    c.set_phase("sc_div_debt");
    let t = mulf(c, &lam, &d, 0, false);
    pay_debt(c, &t, &m);
    mulf_inv(c, &lam, &d, 0, false, t);
    c.free_bit_vec(&m);
    (d, lam)
}

/// `y <- y * x` given y = lam, x = D' (multiply leg). Returns (x wires, y wires = lam * D').
fn mul_leg(c: &mut Builder, dp: Vec<Q>, lam: Vec<Q>) -> (Vec<Q>, Vec<Q>) {
    let p = params();
    let env = envelope();
    let r = p.walk.r;
    c.set_phase("sc_mul_mm4");
    let tmp = mulf(c, &lam, &dp, 0, false);
    c.set_phase("sc_mul_hmr");
    let m = hmr_all(c, &lam);
    c.set_phase("sc_mul_fwd");
    let pk = walk::forward(c, &p.walk, env, &dp);
    c.set_phase("sc_mul_mm5");
    let lam2 = mulf(c, &tmp, &pk.s, r, true);
    pay_debt(c, &lam2, &m);
    mulf_inv(c, &tmp, &pk.s, r, true, lam2);
    c.free_bit_vec(&m);
    c.set_phase("sc_mul_back");
    let dp = walk::backward(c, &p.walk, env, pk);
    (dp, tmp)
}

/// Move the values on `cur_x`/`cur_y` onto the ABI wires `want_x`/`want_y` (swaps; nothing else live).
pub(crate) fn place(c: &mut Builder, cur_x: Vec<Q>, cur_y: Vec<Q>, want_x: &[Q], want_y: &[Q]) {
    let mut cur: Vec<Q> = cur_x.into_iter().chain(cur_y).collect();
    let want: Vec<Q> = want_x.iter().chain(want_y).copied().collect();
    for i in 0..cur.len() {
        let w = want[i];
        if cur[i] == w {
            continue;
        }
        if let Some(j) = cur.iter().position(|&q| q == w) {
            assert!(j > i, "place: wire already placed");
            c.swap(cur[i], cur[j]);
            cur.swap(i, j);
        } else {
            c.reacquire(w);
            c.swap(cur[i], w);
            c.release_clean(cur[i]);
            cur[i] = w;
        }
    }
}

/// The SKY-COF candidate circuit.
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

/// Research probe (`SKYCOF_PROBE=square`): `x += 3 ox; x -= y^2` alone, phase report on stderr.
pub fn probe_square() {
    let circ = &mut Builder::new();
    let x: Vec<Q> = circ.alloc_qubits(N);
    let y: Vec<Q> = circ.alloc_qubits(N);
    let ox: Vec<BitId> = circ.alloc_bits(N);
    circ.set_phase("coord_add3x");
    coord_add3x(circ, &x, &ox);
    circ.set_phase("square");
    sub_square(circ, &x, &y);
    circ.set_phase("end");
    eprintln!("SKYCOF_PROBE square peak={} ops={} k3b={:?} win={:?}", circ.peak_total(), circ.op_count(), circ.k3b_sites,
        crate::point_add::modular::WIN_STATS.with(|w| w.get()));
    circ.finalize_records();
    // simulate: x' = x + 3 ox - y^2 (mod p) on random canonical inputs; every other wire must end at 0
    use crate::point_add::skycof_mm::model::U512;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    let ops = circ.take_ops();
    let (nq, nb) = circ.i13_dims();
    let p = U512::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    let mut rd = {
        let mut h = sha3::Shake256::default();
        h.update(b"skycof-square-probe");
        h.finalize_xof()
    };
    let mut sim = Simulator::new(nq, nb + 1, &mut rd);
    let mut seed = 77u64;
    let mut rnd = || {
        let mut v = U512::ZERO;
        for i in 0..4 {
            seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            v |= U512::from(z ^ (z >> 31)) << (64 * i);
        }
        v.reduce_mod(p)
    };
    let keep: std::collections::HashSet<u64> = x.iter().chain(&y).map(|q| q.0).collect();
    let (mut bad, mut noncanon, mut garb, mut ph) = (0, 0, 0, 0);
    let batches = knob_usize("SKYCOF_PROBE_BATCHES", 4);
    for _ in 0..batches {
        sim.clear_for_shot();
        let mut cases = Vec::new();
        for j in 0..64 {
            let (xv, yv, ov) = (rnd(), rnd(), rnd());
            for i in 0..N {
                if xv.bit(i) { *sim.qubit_mut(x[i]) |= 1 << j; }
                if yv.bit(i) { *sim.qubit_mut(y[i]) |= 1 << j; }
                if ov.bit(i) { *sim.bit_mut(ox[i]) |= 1 << j; }
            }
            cases.push((xv, yv, ov));
        }
        let chunk = knob_usize("SKYCOF_SQ_CHUNK", 0);
        if chunk > 0 {
            // phase mask after every chunk boundary outside conditional blocks
            let mut depth = 0i32;
            let mut a = 0usize;
            let mut hist: Vec<(usize, u64)> = Vec::new();
            for (i, op) in ops.iter().enumerate() {
                if i >= a + chunk && depth == 0 {
                    sim.apply_iter(ops[a..i].iter());
                    hist.push((i, sim.phase));
                    a = i;
                }
                match op.kind {
                    crate::circuit::OperationType::PushCondition => depth += 1,
                    crate::circuit::OperationType::PopCondition => depth -= 1,
                    _ => {}
                }
            }
            sim.apply_iter(ops[a..].iter());
            let fin = sim.phase;
            for j in 0..64 {
                if (fin >> j) & 1 == 1 {
                    // last boundary where this lane's phase was 0
                    let last0 = hist.iter().rev().find(|(_, ph)| (ph >> j) & 1 == 0).map(|x| x.0).unwrap_or(0);
                    let flips: Vec<usize> = hist.windows(2).filter(|w| ((w[0].1 ^ w[1].1) >> j) & 1 == 1).map(|w| w[1].0).collect();
                    eprintln!("SQ_PHASE lane={j} settles_after={last0} flips={}", flips.len());
                }
            }
        } else {
            sim.apply_iter(ops.iter());
        }
        let mut g = 0u64;
        for id in 0..nq {
            if !keep.contains(&(id as u64)) {
                g |= sim.qubits[id];
            }
        }
        for (j, &(xv, yv, ov)) in cases.iter().enumerate() {
            let mut got = U512::ZERO;
            for i in 0..N {
                if (sim.qubit(x[i]) >> j) & 1 == 1 { got.set_bit(i, true); }
            }
            let three = ov.mul_mod(U512::from(3u64), p);
            let want = xv.add_mod(three, p).add_mod(p - yv.mul_mod(yv, p), p);
            if got.reduce_mod(p) != want { bad += 1; }
            if got >= p { noncanon += 1; }
            if (g >> j) & 1 == 1 { garb += 1; }
            if (sim.phase >> j) & 1 == 1 { ph += 1; }
        }
    }
    eprintln!("SKYCOF_PROBE square sim shots={} wrong={bad} noncanonical={noncanon} garbage={garb} phase={ph}", batches * 64);
}
