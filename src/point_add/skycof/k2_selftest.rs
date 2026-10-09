//! Gate-level selftests of the k2 decoder: `SKYCOF_K2_SELFTEST=1 build_circuit` (exits after the tests).
//!
//! 1. exhaustive: every input (all s, r < 2^e, en, typ, every Hreg value) for small geometries (several
//!    windows, rooms from the floor up), push / pop / push+pop: outputs equal the classical replica bit for
//!    bit, every scratch wire returns to 0, zero phase, and the cap is never exceeded.
//! 2. certificates: on every valid post-state (s even, r odd) at e <= 12, every window, and on random
//!    full-width post-states, `GA` implies an exact A condition and `GB` the exact B condition.
//! 3. fullwidth: random full-width inputs through push / pop / push+pop against the replica.
//! 4. walk: real Kaliski walks decoded forward (k0 at t <= 2, k2 after) and back from the parked state
//!    using only the replica's decisions and the pushed bits; every walk must return to its start.
use super::decoder::{Hreg, TickIo};
use super::k2dec::{self, model, K2Cfg};
use crate::circuit::{Op, OperationType, QubitId as Q};
use crate::point_add::builder::Builder;
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput, Update}, Shake256};

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.trim().parse().ok()).unwrap_or(d)
}

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = Shake256::default();
    h.update(b"skycof-k2-selftest-v1");
    h.update(tag);
    h.finalize_xof()
}

fn ccx_count(ops: &[Op]) -> usize {
    ops.iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count()
}

const NL: usize = 5;
type U = [u64; NL];
fn bit_of(a: &U, i: usize) -> bool { i < 64 * NL && (a[i / 64] >> (i % 64)) & 1 == 1 }
fn mask_bits(a: &U, e: usize) -> U { let mut o = *a; for i in 0..NL { let lo = 64 * i; if e <= lo { o[i] = 0; } else if e < lo + 64 { o[i] &= (1u64 << (e - lo)) - 1; } } o }

struct Rng(u64, u64, u64, u64);
impl Rng {
    fn new(seed: u64) -> Rng {
        let mut z = seed;
        let mut nx = || { z = z.wrapping_add(0x9E3779B97F4A7C15); let mut x = z;
            x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9); x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB); x ^ (x >> 31) };
        Rng(nx(), nx(), nx(), nx())
    }
    fn next(&mut self) -> u64 {
        let r = self.1.wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = self.1 << 17; self.2 ^= self.0; self.3 ^= self.1; self.1 ^= self.2; self.0 ^= self.3; self.2 ^= t; self.3 = self.3.rotate_left(45);
        r
    }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
    fn bits_u(&mut self, e: usize) -> U { let mut a = [0u64; NL]; for i in 0..NL { a[i] = self.next(); } mask_bits(&a, e) }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode { Push, Pop, PushPop }

#[derive(Clone, Copy, Debug)]
struct Geo { e: usize, w: usize, room: usize, m: usize, has_en: bool, dgiven: bool, nd: usize, hint: bool }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
struct Val { s: U, r: U, en: bool, typ: bool, h: u64, dv: bool, dw: u64, ov: bool }

struct Built { ops: Vec<Op>, nq: usize, nb: usize, io: Vec<Q>, toff: usize, scratch: u32 }

/// Floor of the room a call needs (held wires + the largest transient).
pub fn min_room(e: usize, w: usize, has_en: bool, dgiven: bool, hint: bool) -> usize {
    let (lo, _) = k2dec::geom(e, w);
    1 + (!dgiven && (has_en || lo == 1)) as usize + if lo == 1 { 3 } else { 0 } + (!hint) as usize
}

fn val_bits(g: &Geo, x: &Val) -> Vec<bool> {
    let mut v: Vec<bool> = (0..g.e).map(|i| bit_of(&x.s, i)).collect();
    v.extend((0..g.e).map(|i| bit_of(&x.r, i)));
    if g.has_en { v.push(x.en); }
    v.push(x.typ);
    v.extend((0..g.m).map(|i| (x.h >> i) & 1 == 1));
    if g.dgiven { v.push(x.dv); }
    if g.hint { v.push(x.ov); }
    v.extend((0..g.nd).map(|i| (x.dw >> i) & 1 == 1));
    v
}

fn val_from_bits(g: &Geo, b: &[bool]) -> Val {
    let mut x = Val::default();
    let mut k = 0;
    for i in 0..g.e { if b[k] { x.s[i / 64] |= 1 << (i % 64); } k += 1; }
    for i in 0..g.e { if b[k] { x.r[i / 64] |= 1 << (i % 64); } k += 1; }
    if g.has_en { x.en = b[k]; k += 1; }
    x.typ = b[k]; k += 1;
    for i in 0..g.m { if b[k] { x.h |= 1 << i; } k += 1; }
    if g.dgiven { x.dv = b[k]; k += 1; }
    if g.hint { x.ov = b[k]; k += 1; }
    for i in 0..g.nd { if b[k] { x.dw |= 1 << i; } k += 1; }
    x
}

fn build(g: &Geo, mode: Mode) -> Built {
    let mut c = Builder::new();
    let s = c.alloc_qubits(g.e);
    let r = c.alloc_qubits(g.e);
    let en = g.has_en.then(|| c.alloc_qubit());
    let typ = c.alloc_qubit();
    let mut h = Hreg::new();
    h.grow_to(&mut c, g.m);
    let mut io: Vec<Q> = s.clone();
    io.extend_from_slice(&r);
    io.extend(en);
    io.push(typ);
    io.extend_from_slice(&h.wires);
    let dw = g.dgiven.then(|| c.alloc_qubit());
    io.extend(dw);
    let hw = g.hint.then(|| c.alloc_qubit());
    io.extend(hw);
    let dirty = c.alloc_qubits(g.nd);
    io.extend_from_slice(&dirty);
    let t = TickIo { s: &s, r: &r, e: g.e, en, typ, cflag: None, park: None };
    let base = c.active_qubits();
    let cfg = K2Cfg { w: g.w, cap: base as usize + g.room, zero_hint: hw };
    let ((), peak) = c.r3_peak(|c| match mode {
        Mode::Push => k2dec::push(c, &t, &h, cfg, dw, &dirty),
        Mode::Pop => k2dec::pop(c, &t, &h, cfg, dw, &dirty),
        Mode::PushPop => { k2dec::push(c, &t, &h, cfg, dw, &dirty); k2dec::pop(c, &t, &h, cfg, dw, &dirty); }
    });
    assert_eq!(c.active_qubits(), base, "k2 decoder call leaked wires");
    let (nq, nb) = c.i13_dims();
    let ops = c.take_ops();
    let toff = ccx_count(&ops);
    Built { ops, nq, nb: nb + 1, io, toff, scratch: peak - base }
}

fn spec(g: &Geo, mode: Mode, x: &Val) -> Val {
    let mut y = *x;
    let en = if g.has_en { x.en } else { true };
    let (d0, ga, gb) = model::decide_o(&x.s, &x.r, g.e, g.w, en, g.hint && x.ov);
    let d = if g.dgiven { x.dv } else { d0 };
    // the circuit accumulates K = D & (GA xor GB): amb = D & !K, typ ^= D & GA (GA, GB exclusive on valid states)
    let (amb, tclr) = (d && !(ga ^ gb), d && ga);
    let mask = if g.m == 64 { u64::MAX } else { (1u64 << g.m) - 1 };
    match mode {
        Mode::Push => {
            // the circuit clears a certain A before the shift (the two never meet on a valid post-state)
            y.typ ^= tclr;
            if amb && g.m > 0 {
                let top = (y.h >> (g.m - 1)) & 1 == 1;
                y.h = ((y.h << 1) | y.typ as u64) & mask;
                y.typ = top;
            }
        }
        Mode::Pop => {
            y.typ ^= tclr;
            if amb && g.m > 0 {
                let low = y.h & 1 == 1;
                y.h = (y.h >> 1) | ((y.typ as u64) << (g.m - 1));
                y.typ = low;
            }
        }
        Mode::PushPop => {}
    }
    y
}

/// Inputs on which both an A and a B certificate hold (impossible on a valid post-state; push and pop
/// are inverse everywhere else).
fn both_certain(g: &Geo, x: &Val) -> bool {
    let en = if g.has_en { x.en } else { true };
    let (d0, ga, gb) = model::decide_o(&x.s, &x.r, g.e, g.w, en, g.hint && x.ov);
    let d = if g.dgiven { x.dv } else { d0 };
    d && ga && gb
}

fn run_batches(b: &Built, g: &Geo, mode: Mode, inputs: &[Val], tag: &[u8]) -> usize {
    let mut rd = xof(tag);
    let mut sim = Simulator::new(b.nq, b.nb, &mut rd);
    let mut is_io = vec![false; b.nq];
    for q in &b.io { is_io[q.0 as usize] = true; }
    let mut bad = 0;
    for chunk in inputs.chunks(64) {
        sim.clear_for_shot();
        let nb = chunk.len();
        let ib: Vec<Vec<bool>> = chunk.iter().map(|x| val_bits(g, x)).collect();
        for (k, q) in b.io.iter().enumerate() {
            let mut wv = 0u64;
            for (sh, v) in ib.iter().enumerate() { if v[k] { wv |= 1 << sh; } }
            *sim.qubit_mut(*q) = wv;
        }
        sim.apply_iter(b.ops.iter());
        let live = if nb == 64 { u64::MAX } else { (1u64 << nb) - 1 };
        let mut garbage = sim.phase & live;
        for q in 0..b.nq { if !is_io[q] { garbage |= sim.qubits[q] & live; } }
        let words: Vec<u64> = b.io.iter().map(|q| sim.qubit(*q)).collect();
        for (sh, x) in chunk.iter().enumerate() {
            let ob: Vec<bool> = words.iter().map(|w| (w >> sh) & 1 == 1).collect();
            let got = val_from_bits(g, &ob);
            let want = spec(g, mode, x);
            let skip = mode == Mode::PushPop && both_certain(g, x) && (garbage >> sh) & 1 == 0;
            if !skip && (got != want || (garbage >> sh) & 1 == 1) {
                if bad < 3 {
                    eprintln!("SKYCOF_K2 mismatch {mode:?} {g:?}\n   in   {x:?}\n   got  {got:?}\n   want {want:?}\n   garbage {}", (garbage >> sh) & 1);
                }
                bad += 1;
            }
        }
    }
    bad
}

fn exhaustive() -> bool {
    let maxe = env_usize("SKYCOF_K2_EXH_MAXE", 8);
    let (mut configs, mut cases, mut ok) = (0usize, 0u64, true);
    let mut tmin = usize::MAX;
    let mut tmax = 0usize;
    for e in 6..=maxe {
        for &w in &[5usize, 6, 7, 64] {
            let (_, n) = k2dec::geom(e, w);
            if n < k2dec::MIN_N { continue; }
            for &(has_en, dgiven, hint) in &[(false, false, false), (true, false, true), (false, true, true), (false, false, true)] {
                let floor = min_room(e, w, has_en, dgiven, hint);
                let rooms: Vec<usize> = if e == maxe { vec![floor, floor + n + 8] } else { (floor..=floor + n + 8).step_by(3).collect() };
                for &room in &rooms {
                    for &m in &[0usize, 2] {
                        let g = Geo { e, w, room, m, has_en, dgiven, nd: 10, hint };
                        let nbits = 2 * e + has_en as usize + 1 + m + dgiven as usize + hint as usize;
                        let mut rng = Rng::new(0xd1e7 ^ (e * 1000 + w * 10 + room) as u64);
                        let inputs: Vec<Val> = (0..1u64 << nbits)
                            .map(|i| {
                                let mut bits: Vec<bool> = (0..nbits).map(|k| (i >> k) & 1 == 1).collect();
                                let dwv = rng.next();
                                bits.extend((0..g.nd).map(|k| (dwv >> k) & 1 == 1));
                                val_from_bits(&g, &bits)
                            })
                            .collect();
                        for mode in [Mode::Push, Mode::Pop, Mode::PushPop] {
                            let b = build(&g, mode);
                            if b.scratch as usize > room {
                                ok = false;
                                eprintln!("SKYCOF_K2 cap exceeded {mode:?} {g:?}: scratch {} > room {room}", b.scratch);
                            }
                            if mode == Mode::Push { tmin = tmin.min(b.toff); tmax = tmax.max(b.toff); }
                            let bad = run_batches(&b, &g, mode, &inputs, format!("exh{e}-{w}-{room}-{m}-{has_en}-{mode:?}").as_bytes());
                            if bad > 0 { ok = false; eprintln!("SKYCOF_K2 exhaustive FAIL {mode:?} {g:?}: {bad} of {}", inputs.len()); }
                            cases += inputs.len() as u64;
                        }
                        configs += 1;
                    }
                }
            }
        }
    }
    eprintln!("SKYCOF_K2 exhaustive: {configs} geometries x (push, pop, push+pop), {cases} input cases, Toffoli per push {tmin}..{tmax}: {}",
        if ok { "all exact (replica outputs, 0 scratch garbage, 0 phase, within the cap)" } else { "FAIL" });
    ok
}

/// Exact k2 conditions on a valid post-state (rational compares).
fn exact_ab(s: &U, r: &U) -> (bool, bool) {
    // compare 8r vs j s exactly with u128 on values < 2^120, else limb arithmetic
    let mul = |a: &U, k: u64| -> [u64; NL + 1] {
        let mut o = [0u64; NL + 1]; let mut cr = 0u128;
        for i in 0..NL { let t = a[i] as u128 * k as u128 + cr; o[i] = t as u64; cr = t >> 64; }
        o[NL] = cr as u64; o
    };
    let cmpv = |a: &[u64; NL + 1], b: &[u64; NL + 1]| { for i in (0..=NL).rev() { if a[i] != b[i] { return a[i].cmp(&b[i]); } } std::cmp::Ordering::Equal };
    let r8 = mul(r, 8);
    let lt = |j: u64| cmpv(&r8, &mul(s, j)) == std::cmp::Ordering::Less;
    let gt = |j: u64| cmpv(&r8, &mul(s, j)) == std::cmp::Ordering::Greater;
    let b2 = bit_of(s, 2); let b3 = bit_of(s, 3); let beta = bit_of(r, 1) ^ b3;
    let a = lt(4) || (!b2 && b3 && lt(5)) || (b2 && lt(6)) || (b2 && !beta && gt(10));
    let b = b2 && beta && gt(6);
    (a, b)
}

fn certificates() -> bool {
    let mut ok = true;
    let (mut n, mut nga, mut ngb) = (0u64, 0u64, 0u64);
    for e in 6..=12usize {
        for w in 5..=e + 1 {
            let (_, nn) = k2dec::geom(e, w);
            if nn < k2dec::MIN_N { continue; }
            for sv in (0..1u64 << e).step_by(4) { // s even and bit1(s) = 0 (not C)
                for rv in (1..1u64 << e).step_by(2) {
                    let mut s = [0u64; NL]; s[0] = sv;
                    let mut r = [0u64; NL]; r[0] = rv;
                    let (_, ga, gb) = model::decide(&s, &r, e, w, true);
                    let (ea, eb) = exact_ab(&s, &r);
                    if (ga && !ea) || (gb && !eb) || (ga && gb) {
                        ok = false;
                        if n < 5 { eprintln!("SKYCOF_K2 certificate FAIL e={e} w={w} s={sv} r={rv}: GA={ga} GB={gb} exact A={ea} B={eb}"); }
                    }
                    nga += ga as u64; ngb += gb as u64; n += 1;
                }
            }
        }
    }
    let mut rng = Rng::new(0xce57_12);
    let mut nf = 0u64;
    for i in 0..2_000_000u64 {
        let e = [256usize, 255, 240, 200, 130, 64, 57, 56, 30, 13][rng.below(10) as usize];
        let w = [56usize, 64, 48, 32][rng.below(4) as usize];
        let (_, nn) = k2dec::geom(e, w);
        if nn < k2dec::MIN_N { continue; }
        let mut s = rng.bits_u(e);
        let mut r = rng.bits_u(e);
        if i % 3 == 0 { // r near theta * s for the four thresholds
            let th = [4u64, 5, 6, 10][rng.below(4) as usize];
            let k = rng.below(e as u64 / 2) as usize;
            s = mask_bits(&s, e - k - 1);
            // r = th * s / 8 + small
            let mut o = [0u64; NL]; let mut cr = 0u128;
            for j in 0..NL { let t = s[j] as u128 * th as u128 + cr; o[j] = t as u64; cr = t >> 64; }
            for _ in 0..3 { for j in 0..NL { o[j] = (o[j] >> 1) | if j + 1 < NL { o[j + 1] << 63 } else { 0 }; } }
            let dlt = rng.below(64);
            let mut c2 = dlt as u128;
            for j in 0..NL { let t = o[j] as u128 + c2; o[j] = t as u64; c2 = t >> 64; }
            r = mask_bits(&o, e);
        }
        s[0] &= !3; r[0] |= 1;
        let (_, ga, gb) = model::decide(&s, &r, e, w, true);
        let (ea, eb) = exact_ab(&s, &r);
        if (ga && !ea) || (gb && !eb) || (ga && gb) { ok = false; eprintln!("SKYCOF_K2 full-width certificate FAIL e={e} w={w}"); }
        nf += 1;
    }
    eprintln!("SKYCOF_K2 certificates: {n} exhaustive valid post-states (e<=12, every window; GA {nga}, GB {ngb}) and {nf} full-width \
               (incl. near-threshold) post-states: GA => exact A, GB => exact B, never both: {}", if ok { "OK" } else { "FAIL" });
    ok
}

fn fullwidth() -> bool {
    let mut ok = true;
    let mut total = 0usize;
    let mut rng = Rng::new(0xF011_2D7E);
    let geos = [
        Geo { e: 256, w: 56, room: 2, m: 40, has_en: false, dgiven: false, nd: 12, hint: true },
        Geo { e: 256, w: 56, room: 2, m: 40, has_en: false, dgiven: true, nd: 12, hint: true },
        Geo { e: 256, w: 56, room: 3, m: 40, has_en: true, dgiven: false, nd: 12, hint: true },
        Geo { e: 256, w: 56, room: 30, m: 63, has_en: true, dgiven: false, nd: 12, hint: true },
        Geo { e: 256, w: 56, room: 70, m: 63, has_en: false, dgiven: false, nd: 12, hint: true },
        Geo { e: 230, w: 64, room: 6, m: 30, has_en: false, dgiven: true, nd: 12, hint: true },
        Geo { e: 57, w: 56, room: 6, m: 20, has_en: false, dgiven: false, nd: 12, hint: true },
        Geo { e: 40, w: 56, room: 50, m: 20, has_en: false, dgiven: false, nd: 12, hint: true },
        Geo { e: 13, w: 56, room: 6, m: 8, has_en: true, dgiven: false, nd: 12, hint: true },
    ];
    for g in &geos {
        let mut inputs = Vec::with_capacity(2048);
        for i in 0..2048 {
            let mut x = Val { s: rng.bits_u(g.e), r: rng.bits_u(g.e), en: rng.next() & 1 == 1, typ: rng.next() & 1 == 1,
                h: rng.next() & ((1u64 << g.m) - 1), dv: rng.next() & 1 == 1, dw: rng.next() & ((1u64 << g.nd) - 1),
                ov: rng.next() & 3 == 0 };
            if !g.dgiven { x.dv = false; }
            if i % 2 == 0 { x.s[0] &= !1; x.r[0] |= 1; }
            if i % 4 == 0 { x.s[0] &= !2; }
            if !g.has_en { x.en = false; }
            inputs.push(x);
        }
        for mode in [Mode::Push, Mode::Pop, Mode::PushPop] {
            let b = build(g, mode);
            if b.scratch as usize > g.room { ok = false; eprintln!("SKYCOF_K2 fullwidth cap exceeded {mode:?} {g:?}"); }
            let bad = run_batches(&b, g, mode, &inputs, format!("fw{}-{}-{}-{mode:?}", g.e, g.w, g.room).as_bytes());
            if bad > 0 { ok = false; eprintln!("SKYCOF_K2 fullwidth FAIL {mode:?} {g:?}: {bad}"); }
            if mode == Mode::Push { eprintln!("SKYCOF_K2 fullwidth {g:?}: push Toffoli {} scratch {}", b.toff, b.scratch); }
            total += inputs.len();
        }
    }
    eprintln!("SKYCOF_K2 fullwidth: {total} cases: {}", if ok { "OK" } else { "FAIL" });
    ok
}

// ─── 4. classical walks with the replica ────────────────────────────────────────────────────
mod walk {
    use super::super::k2dec::model;
    use super::super::decoder::model as m0;
    pub const NL: usize = 5;
    pub type U = [u64; NL];
    const P: U = [0xFFFFFFFEFFFFFC2F, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0];
    const TOP: U = [0, 0, 0, 0, 1];
    fn zero() -> U { [0; NL] }
    fn from_u64(x: u64) -> U { let mut a = zero(); a[0] = x; a }
    fn is_zero(a: &U) -> bool { a.iter().all(|&x| x == 0) }
    fn add(a: &U, b: &U) -> U { let mut o = zero(); let mut c = 0u128; for i in 0..NL { let t = a[i] as u128 + b[i] as u128 + c; o[i] = t as u64; c = t >> 64; } o }
    fn sub(a: &U, b: &U) -> U { let mut o = zero(); let mut br = 0i128; for i in 0..NL { let t = a[i] as i128 - b[i] as i128 - br; o[i] = t as u64; br = (t < 0) as i128; } o }
    fn shr1(a: &U) -> U { let mut o = zero(); for i in 0..NL { o[i] = (a[i] >> 1) | if i + 1 < NL { a[i + 1] << 63 } else { 0 }; } o }
    fn shl1(a: &U) -> U { let mut o = zero(); for i in 0..NL { o[i] = (a[i] << 1) | if i > 0 { a[i - 1] >> 63 } else { 0 }; } o }
    fn cmp(a: &U, b: &U) -> std::cmp::Ordering { for i in (0..NL).rev() { if a[i] != b[i] { return a[i].cmp(&b[i]); } } std::cmp::Ordering::Equal }
    fn ge(a: &U, b: &U) -> bool { cmp(a, b) != std::cmp::Ordering::Less }
    fn bits(a: &U) -> usize { for i in (0..NL).rev() { if a[i] != 0 { return 64 * i + 64 - a[i].leading_zeros() as usize; } } 0 }
    fn fold(x: &U) -> U { if ge(x, &TOP) { sub(x, &P) } else { *x } }
    fn unfold(x: &U) -> U { if x[0] & 1 == 1 { add(x, &P) } else { *x } }
    fn mod_dbl(s: &U) -> U { fold(&shl1(s)) }
    fn mod_half(s: &U) -> U { shr1(&unfold(s)) }

    /// Decision on a post-state: (amb, letter-if-certain) with letter 0 = A, 1 = B, 2 = C.
    fn decide(s: &U, r: &U, t: usize, e: usize, w0: usize, w2: usize, k2_from: usize, k2_to: usize) -> (bool, u8) {
        if (s[0] >> 1) & 1 == 1 { return (false, 2); }
        if t == 0 { return (false, 0); }
        if t >= k2_from && t <= k2_to {
            let (_, amb, a) = model::letters(s, r, e, w2, true);
            if amb { (true, 9) } else if a { (false, 0) } else { (false, 1) }
        } else {
            let (_, amb) = m0::decide(s, r, e, w0, true);
            (amb, if amb { 9 } else { 0 })
        }
    }

    /// Forward walk with decoder pushes, then the reverse from (s, stack, park) alone. Returns
    /// Ok(pushes) / Err(reason); Err("env") when a value leaves its field.
    pub fn roundtrip(d: &U, ecof: &[usize], r_ticks: usize, w0: usize, w2: usize, k2_from: usize, k2_to: usize) -> Result<usize, &'static str> {
        let (mut u, mut v, mut s, mut r) = (*d, P, zero(), from_u64(1));
        let mut stack: Vec<u8> = Vec::new();
        let mut park: Option<usize> = None;
        for t in 0..r_ticks {
            let case;
            if is_zero(&u) { s = mod_dbl(&s); case = 3; }
            else if u[0] & 1 == 0 { u = shr1(&u); s = shl1(&s); case = 0; }
            else if ge(&u, &v) { u = shr1(&sub(&u, &v)); r = add(&r, &s); s = shl1(&s); case = 1; }
            else { let nu = shr1(&sub(&v, &u)); v = u; u = nu; let ns = shl1(&r); r = add(&r, &s); s = ns; case = 2; }
            if is_zero(&u) && park.is_none() { park = Some(t); s = fold(&s); }
            if case != 3 && !is_zero(&u) {
                if bits(&s).max(bits(&r)) > ecof[t] { return Err("env"); }
                let (amb, l) = decide(&s, &r, t, ecof[t], w0, w2, k2_from, k2_to);
                if amb { stack.push(case as u8); } else if l != case as u8 { return Err("misdecode"); }
            }
        }
        let Some(pk) = park else { return Err("env") };
        let pushes = stack.len();
        let mut odo = r_ticks - 1 - pk;
        for t in (0..r_ticks).rev() {
            if odo > 0 { s = mod_half(&s); odo -= 1; continue; }
            let parked = is_zero(&u);
            if parked { s = unfold(&s); }
            let case = if parked {
                1 // the park tick (u = v = 1) is a B step in the Kaliski frame
            } else {
                let (amb, l) = decide(&s, &r, t, ecof[t], w0, w2, k2_from, k2_to);
                if amb { match stack.pop() { Some(x) => x, None => return Err("underflow") } } else { l }
            };
            if s[0] & 1 == 1 { return Err("odd s"); }
            let a = shr1(&s);
            match case {
                0 => { u = shl1(&u); s = a; }
                1 => { u = add(&shl1(&u), &v); if !ge(&r, &a) { return Err("B r<a"); } r = sub(&r, &a); s = a; }
                _ => { if !ge(&r, &a) { return Err("C r<a"); } let nu = v; v = add(&shl1(&u), &v); u = nu; let ns = sub(&r, &a); r = a; s = ns; }
            }
        }
        if !stack.is_empty() { return Err("stack"); }
        if !(u == *d && v == P && is_zero(&s) && r == from_u64(1)) { return Err("start"); }
        Ok(pushes)
    }
}

fn walks() -> bool {
    let n = env_usize("SKYCOF_K2_WALKS", 200_000);
    let env = super::pointadd::envelope();
    let ecof: Vec<usize> = env.cof.clone();
    let rt = super::pointadd::params().walk.r;
    let w2 = super::pointadd::params().walk.w_dec;
    let (k2_from, k2_to) = super::walk::k2_range();
    let mut rng = Rng::new(0x3a1c_0de);
    let (mut okc, mut envc, mut bad, mut pushes) = (0u64, 0u64, 0u64, 0u64);
    for _ in 0..n {
        let d = loop {
            let mut d = [0u64; NL];
            for i in 0..4 { d[i] = rng.next(); }
            let p = [0xFFFFFFFEFFFFFC2Fu64, u64::MAX, u64::MAX, u64::MAX, 0];
            let lt = (0..NL).rev().find(|&i| d[i] != p[i]).map(|i| d[i] < p[i]).unwrap_or(false);
            if lt && d.iter().any(|&x| x != 0) { break d; }
        };
        match walk::roundtrip(&d, &ecof, rt, 64, w2, k2_from, k2_to) {
            Ok(p) => { okc += 1; pushes += p as u64; }
            Err("env") => envc += 1,
            Err(e) => { bad += 1; if bad < 5 { eprintln!("SKYCOF_K2 walk FAIL: {e}"); } }
        }
    }
    eprintln!("SKYCOF_K2 walks: {n} random walks (R={rt}, k2 on ticks {k2_from}..={k2_to}, w={w2}): {okc} decoded back to the start, \
               {envc} outside the cofactor field, {bad} failures; mean pushes {:.2}", pushes as f64 / okc.max(1) as f64);
    bad == 0
}

pub fn run() {
    let which = std::env::var("SKYCOF_K2_SELFTEST").unwrap_or_default();
    let all = which == "1" || which == "all";
    let mut ok = true;
    if all || which.contains("cert") { ok &= certificates(); }
    if all || which.contains("walk") { ok &= walks(); }
    if all || which.contains("exh") { ok &= exhaustive(); }
    if all || which.contains("full") { ok &= fullwidth(); }
    eprintln!("SKYCOF_K2_SELFTEST {}", if ok { "PASS" } else { "FAIL" });
}
