//! Gate-level selftests of the SKY-COF decoder and history accumulator:
//! `SKYCOF_DEC_SELFTEST=1 build_circuit` (exits after the tests; writes no ops.bin).
//!
//! 1. exhaustive: every input (all s, r < 2^e, en, typ, cflag, park flag/bit, every Hreg
//!    value) for every small geometry (e <= SKYCOF_DEC_EXH_MAXE, default 6; several windows,
//!    every room from the floor to full, Hreg widths 0..3, with/without en, cflag, park), for
//!    push, pop and push+pop: outputs equal the classical spec bit for bit, every scratch
//!    wire returns to 0, zero phase; Toffoli count and scratch equal the cost formulas.
//! 2. deciders: the circuit's decision equals the deciders' k = 0 windowed test (scd.rs
//!    `decode`) exhaustively on all post-states (s even, r odd) at e <= 11 and every window,
//!    and on random / near-tie post-states at full width; ge = 0 always proves 2r < s.
//! 3. fullwidth: random and adversarial full-width inputs (e up to 256, w = 64/48/32,
//!    several rooms) through push / pop / push+pop against the spec.
//! 4. walk: SKYCOF_DEC_WALKS real Kaliski walks (R = 400, field and Hreg widths from the
//!    deciders' envelope tables), the decoder chained over all ticks forward (letters
//!    erased, history pushed) and back (letters popped, the cofactors un-stepped from the
//!    popped letters alone), checking every letter, the park bit, the start state, a
//!    clean Hreg, clean scratch and zero phase. Shots outside the envelope are reported.
//! 5. cost: per-call Toffoli/scratch at the design widths and per-traversal totals.

use super::decoder::{self as dec, model, DecCfg, Hreg, TickIo, Window};
use crate::circuit::{Op, OperationType, QubitId as Q};
use crate::point_add::builder::Builder;
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update},
    Shake256,
};

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k)
        .ok()
        .and_then(|v| v.trim().parse().ok())
        .unwrap_or(d)
}
fn env_str(k: &str, d: &str) -> String {
    std::env::var(k).unwrap_or_else(|_| d.to_string())
}

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = Shake256::default();
    h.update(b"skycof-decoder-selftest-v1");
    h.update(tag);
    h.finalize_xof()
}

fn ccx_count(ops: &[Op]) -> usize {
    ops.iter()
        .filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ))
        .count()
}

// ─── 320-bit helpers (scd.rs arithmetic) ────────────────────────────────────────────────
const NL: usize = 5;
type U = [u64; NL];
const P: U = [
    0xFFFFFFFEFFFFFC2F,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0,
];
const TOP: U = [0, 0, 0, 0, 1];
fn zero() -> U {
    [0; NL]
}
fn from_u64(x: u64) -> U {
    let mut a = zero();
    a[0] = x;
    a
}
fn is_zero(a: &U) -> bool {
    a.iter().all(|&x| x == 0)
}
fn add(a: &U, b: &U) -> U {
    let mut o = zero();
    let mut c = 0u128;
    for i in 0..NL {
        let t = a[i] as u128 + b[i] as u128 + c;
        o[i] = t as u64;
        c = t >> 64;
    }
    o
}
fn sub(a: &U, b: &U) -> U {
    let mut o = zero();
    let mut br = 0i128;
    for i in 0..NL {
        let t = a[i] as i128 - b[i] as i128 - br;
        o[i] = t as u64;
        br = (t < 0) as i128;
    }
    o
}
fn shr1(a: &U) -> U {
    let mut o = zero();
    for i in 0..NL {
        o[i] = (a[i] >> 1) | if i + 1 < NL { a[i + 1] << 63 } else { 0 };
    }
    o
}
fn shl1(a: &U) -> U {
    let mut o = zero();
    for i in 0..NL {
        o[i] = (a[i] << 1) | if i > 0 { a[i - 1] >> 63 } else { 0 };
    }
    o
}
fn cmp(a: &U, b: &U) -> std::cmp::Ordering {
    for i in (0..NL).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    std::cmp::Ordering::Equal
}
fn ge(a: &U, b: &U) -> bool {
    cmp(a, b) != std::cmp::Ordering::Less
}
fn bits(a: &U) -> usize {
    for i in (0..NL).rev() {
        if a[i] != 0 {
            return 64 * i + 64 - a[i].leading_zeros() as usize;
        }
    }
    0
}
fn fold(x: &U) -> U {
    if ge(x, &TOP) {
        sub(x, &P)
    } else {
        *x
    }
}
fn unfold(x: &U) -> U {
    if x[0] & 1 == 1 {
        add(x, &P)
    } else {
        *x
    }
}
fn mod_dbl(s: &U) -> U {
    fold(&shl1(s))
}
fn mod_half(s: &U) -> U {
    shr1(&unfold(s))
}
fn bit_of(a: &U, i: usize) -> bool {
    i < 64 * NL && (a[i / 64] >> (i % 64)) & 1 == 1
}
fn shr_bits(a: &U, b: usize) -> U {
    let mut o = *a;
    for _ in 0..b {
        o = shr1(&o);
    }
    o
}
fn mask_bits(a: &U, e: usize) -> U {
    let mut o = *a;
    for i in 0..NL {
        let lo = 64 * i;
        if e <= lo {
            o[i] = 0;
        } else if e < lo + 64 {
            o[i] &= (1u64 << (e - lo)) - 1;
        }
    }
    o
}

/// The deciders' k = 0 decision (scd.rs `decode`, `Ctx::r_ge_a` on the root node), on a
/// post-state at tick t >= 1 that is not parked: true = ambiguous.
fn scd_amb(s: &U, r: &U, w: usize, e: usize) -> bool {
    if (s[0] >> 1) & 1 == 1 {
        return false;
    }
    let b = e.saturating_sub(w);
    // st, rt fit in 128 bits whenever the values fit in e bits and w <= 126
    let st = shr_bits(s, b);
    let rt = shr_bits(r, b);
    let st = st[0] as i128 | ((st[1] as i128) << 64);
    let rt = rt[0] as i128 | ((rt[1] as i128) << 64);
    // c1 = -SC, c2 = 2 SC, pos = 2 SC with SC = 64: -64 st + 128 rt + 128 > 0
    -st + 2 * rt + 2 > 0
}

// ─── rng (scd.rs) ───────────────────────────────────────────────────────────────────────
struct Rng(u64, u64, u64, u64);
impl Rng {
    fn new(seed: u64) -> Rng {
        let mut z = seed;
        let mut nx = || {
            z = z.wrapping_add(0x9E3779B97F4A7C15);
            let mut x = z;
            x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB);
            x ^ (x >> 31)
        };
        Rng(nx(), nx(), nx(), nx())
    }
    fn next(&mut self) -> u64 {
        let r = self.1.wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = self.1 << 17;
        self.2 ^= self.0;
        self.3 ^= self.1;
        self.1 ^= self.2;
        self.0 ^= self.3;
        self.2 ^= t;
        self.3 = self.3.rotate_left(45);
        r
    }
    fn scalar(&mut self) -> U {
        loop {
            let mut d = zero();
            for i in 0..4 {
                d[i] = self.next();
            }
            if !is_zero(&d) && cmp(&d, &P) == std::cmp::Ordering::Less {
                return d;
            }
        }
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn bits_u(&mut self, e: usize) -> U {
        let mut a = zero();
        for i in 0..NL {
            a[i] = self.next();
        }
        mask_bits(&a, e)
    }
}

// ─── one decoder call as a standalone circuit ───────────────────────────────────────────
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode {
    Push,
    Pop,
    PushPop,
    First,
}

#[derive(Clone, Copy, Debug)]
struct Geo {
    e: usize,
    w: usize,
    room: usize,
    m: usize,
    has_en: bool,
    has_cf: bool,
    has_park: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
struct Val {
    s: U,
    r: U,
    en: bool,
    typ: bool,
    cf: bool,
    flag: bool,
    bit: bool,
    h: u64,
}

struct Built {
    ops: Vec<Op>,
    nq: usize,
    nb: usize,
    io: Vec<Q>,
    toff: usize,
    scratch: u32,
}

fn io_list(
    g: &Geo,
    s: &[Q],
    r: &[Q],
    en: Option<Q>,
    typ: Q,
    cf: Option<Q>,
    park: Option<(Q, Q)>,
    h: &[Q],
) -> Vec<Q> {
    let mut v: Vec<Q> = s[..g.e].to_vec();
    v.extend_from_slice(&r[..g.e]);
    v.extend(en);
    v.push(typ);
    v.extend(cf);
    if let Some((f, b)) = park {
        v.push(f);
        v.push(b);
    }
    v.extend_from_slice(h);
    v
}

fn val_bits(g: &Geo, x: &Val) -> Vec<bool> {
    let mut v: Vec<bool> = (0..g.e).map(|i| bit_of(&x.s, i)).collect();
    v.extend((0..g.e).map(|i| bit_of(&x.r, i)));
    if g.has_en {
        v.push(x.en);
    }
    v.push(x.typ);
    if g.has_cf {
        v.push(x.cf);
    }
    if g.has_park {
        v.push(x.flag);
        v.push(x.bit);
    }
    v.extend((0..g.m).map(|i| (x.h >> i) & 1 == 1));
    v
}

fn val_from_bits(g: &Geo, b: &[bool]) -> Val {
    let mut x = Val::default();
    let mut k = 0;
    for i in 0..g.e {
        if b[k] {
            x.s[i / 64] |= 1 << (i % 64);
        }
        k += 1;
    }
    for i in 0..g.e {
        if b[k] {
            x.r[i / 64] |= 1 << (i % 64);
        }
        k += 1;
    }
    if g.has_en {
        x.en = b[k];
        k += 1;
    }
    x.typ = b[k];
    k += 1;
    if g.has_cf {
        x.cf = b[k];
        k += 1;
    }
    if g.has_park {
        x.flag = b[k];
        x.bit = b[k + 1];
        k += 2;
    }
    for i in 0..g.m {
        if b[k] {
            x.h |= 1 << i;
        }
        k += 1;
    }
    x
}

fn build(g: &Geo, mode: Mode) -> Built {
    let mut c = Builder::new();
    let s = c.alloc_qubits(g.e);
    let r = c.alloc_qubits(g.e);
    let en = g.has_en.then(|| c.alloc_qubit());
    let typ = c.alloc_qubit();
    let cf = g.has_cf.then(|| c.alloc_qubit());
    let park = g.has_park.then(|| (c.alloc_qubit(), c.alloc_qubit()));
    let mut h = Hreg::new();
    h.grow_to(&mut c, g.m);
    let io = io_list(g, &s, &r, en, typ, cf, park, &h.wires);
    let t = TickIo {
        s: &s,
        r: &r,
        e: g.e,
        en,
        typ,
        cflag: cf,
        park,
    };
    let cfg = DecCfg {
        w: g.w,
        room: g.room,
    };
    let base = c.active_qubits();
    let ((), peak) = c.r3_peak(|c| match mode {
        Mode::Push => dec::push(c, &t, &h, cfg),
        Mode::Pop => dec::pop(c, &t, &h, cfg),
        Mode::PushPop => {
            dec::push(c, &t, &h, cfg);
            dec::pop(c, &t, &h, cfg);
        }
        Mode::First => dec::first_tick(c, &s, typ, cf),
    });
    assert_eq!(c.active_qubits(), base, "decoder call leaked wires");
    let (nq, nb) = c.i13_dims();
    let ops = c.take_ops();
    let toff = ccx_count(&ops);
    Built {
        ops,
        nq,
        nb: nb + 1,
        io,
        toff,
        scratch: peak - base,
    }
}

fn spec(g: &Geo, mode: Mode, x: &Val) -> Val {
    let mut y = *x;
    let s1 = bit_of(&x.s, 1);
    let en = if g.has_en { x.en } else { true };
    let cf_flip = if g.has_en { x.en & s1 } else { s1 };
    let mask = if g.m == 64 {
        u64::MAX
    } else {
        (1u64 << g.m) - 1
    };
    match mode {
        Mode::First => {
            y.typ ^= !s1;
            if g.has_cf {
                y.cf ^= s1;
            }
        }
        Mode::Push => {
            if g.has_park && y.flag {
                std::mem::swap(&mut y.bit, &mut y.typ);
            }
            let (d, amb) = model::decide(&x.s, &x.r, g.e, g.w, en);
            let ctrl = amb ^ (g.has_park && y.flag);
            if ctrl && g.m > 0 {
                let top = (y.h >> (g.m - 1)) & 1 == 1;
                y.h = ((y.h << 1) | y.typ as u64) & mask;
                y.typ = top;
            }
            y.typ ^= d ^ amb;
            if g.has_cf {
                y.cf ^= cf_flip;
            }
        }
        Mode::Pop => {
            let (d, amb) = model::decide(&x.s, &x.r, g.e, g.w, en);
            if g.has_cf {
                y.cf ^= cf_flip;
            }
            y.typ ^= d ^ amb;
            let ctrl = amb ^ (g.has_park && y.flag);
            if ctrl && g.m > 0 {
                let low = y.h & 1 == 1;
                y.h = (y.h >> 1) | ((y.typ as u64) << (g.m - 1));
                y.typ = low;
            }
            if g.has_park && y.flag {
                std::mem::swap(&mut y.bit, &mut y.typ);
            }
        }
        Mode::PushPop => {}
    }
    y
}

/// Run `inputs` (any count) through a built circuit; returns the number of mismatching shots.
fn run_batches(b: &Built, g: &Geo, mode: Mode, inputs: &[Val], tag: &[u8]) -> usize {
    let mut rd = xof(tag);
    let mut sim = Simulator::new(b.nq, b.nb, &mut rd);
    let mut is_io = vec![false; b.nq];
    for q in &b.io {
        is_io[q.0 as usize] = true;
    }
    let mut bad = 0;
    for chunk in inputs.chunks(64) {
        sim.clear_for_shot();
        let nb = chunk.len();
        let ib: Vec<Vec<bool>> = chunk.iter().map(|x| val_bits(g, x)).collect();
        for (k, q) in b.io.iter().enumerate() {
            let mut wv = 0u64;
            for (sh, v) in ib.iter().enumerate() {
                if v[k] {
                    wv |= 1 << sh;
                }
            }
            *sim.qubit_mut(*q) = wv;
        }
        sim.apply_iter(b.ops.iter());
        let live = if nb == 64 { u64::MAX } else { (1u64 << nb) - 1 };
        let mut garbage = sim.phase & live;
        for q in 0..b.nq {
            if !is_io[q] {
                garbage |= sim.qubits[q] & live;
            }
        }
        let words: Vec<u64> = b.io.iter().map(|q| sim.qubit(*q)).collect();
        for (sh, x) in chunk.iter().enumerate() {
            let ob: Vec<bool> = words.iter().map(|w| (w >> sh) & 1 == 1).collect();
            let got = val_from_bits(g, &ob);
            let want = spec(g, mode, x);
            if got != want || (garbage >> sh) & 1 == 1 {
                if bad < 3 {
                    eprintln!("SKYCOF_DEC mismatch {mode:?} {g:?}\n   in   {x:?}\n   got  {got:?}\n   want {want:?}\n   garbage {}", (garbage >> sh) & 1);
                }
                bad += 1;
            }
        }
    }
    bad
}

struct BorrowBuilt {
    ops: Vec<Op>,
    nq: usize,
    nb: usize,
    io: Vec<Q>,
    peak: u32,
}

fn build_borrow_diff(e: usize, room: usize, m: usize, mode: Mode, borrowed: bool) -> BorrowBuilt {
    let mut c = Builder::new();
    let s = c.alloc_qubits(e);
    let r = c.alloc_qubits(e);
    let en = c.alloc_qubit();
    let typ = c.alloc_qubit();
    let mut h = Hreg::new();
    h.grow_to(&mut c, m);
    let borrower = c.alloc_qubit();
    let io = TickIo {
        s: &s,
        r: &r,
        e,
        en: Some(en),
        typ,
        cflag: None,
        park: None,
    };
    let cfg = DecCfg { w: e, room };
    let base = c.active_qubits();
    let ((), peak) = c.r3_peak(|c| match (mode, borrowed) {
        (Mode::Push, false) => dec::push(c, &io, &h, cfg),
        (Mode::Pop, false) => dec::pop(c, &io, &h, cfg),
        (Mode::PushPop, false) => {
            dec::push(c, &io, &h, cfg);
            dec::pop(c, &io, &h, cfg);
        }
        (Mode::Push, true) => dec::push_borrow_amb(c, &io, &h, cfg, borrower),
        (Mode::Pop, true) => dec::pop_borrow_amb(c, &io, &h, cfg, borrower),
        (Mode::PushPop, true) => {
            dec::push_borrow_amb(c, &io, &h, cfg, borrower);
            dec::pop_borrow_amb(c, &io, &h, cfg, borrower);
        }
        (Mode::First, _) => unreachable!(),
    });
    assert_eq!(c.active_qubits(), base, "borrowed decoder leaked owners");
    let mut ios = s;
    ios.extend(r);
    ios.push(en);
    ios.push(typ);
    ios.extend(h.wires);
    ios.push(borrower);
    let (nq, nb) = c.i13_dims();
    BorrowBuilt {
        ops: c.take_ops(),
        nq,
        nb: nb + 1,
        io: ios,
        peak,
    }
}

fn borrow_amb_exhaustive() -> bool {
    // Borrowed-decoder integration asserts an empty tracked condition stack.
    std::env::set_var("HEO_RESEARCH", "1");
    std::env::set_var("HEO_PHASE_REPORT", "1");
    let mut cases = 0u64;
    let mut ok = true;
    for e in 2usize..=6 {
        let n = Window::new(e, e).n();
        for room in [dec::min_room(true), dec::min_room(true) + n] {
            let m = 3usize;
            let nbits = 2 * e + 1 + 1 + m + 1;
            let total = 1u64 << nbits;
            cases += total * 3;
            for mode in [Mode::Push, Mode::Pop, Mode::PushPop] {
                let ordinary = build_borrow_diff(e, room, m, mode, false);
                let borrowed = build_borrow_diff(e, room, m, mode, true);
                assert_eq!(ordinary.io.len(), borrowed.io.len());
                for lo in (0..total).step_by(64) {
                    let hi = (lo + 64).min(total);
                    let mut ro = xof(format!("borrow-ordinary-{e}-{room}-{mode:?}-{lo}").as_bytes());
                    let mut rb = xof(format!("borrow-special-{e}-{room}-{mode:?}-{lo}").as_bytes());
                    let mut so = Simulator::new(ordinary.nq, ordinary.nb, &mut ro);
                    let mut sb = Simulator::new(borrowed.nq, borrowed.nb, &mut rb);
                    for (bit, (&qo, &qb)) in ordinary.io.iter().zip(&borrowed.io).enumerate() {
                        let mut word = 0u64;
                        for case in lo..hi {
                            if (case >> bit) & 1 == 1 {
                                word |= 1u64 << (case - lo);
                            }
                        }
                        *so.qubit_mut(qo) = word;
                        *sb.qubit_mut(qb) = word;
                    }
                    so.apply_iter(ordinary.ops.iter());
                    sb.apply_iter(borrowed.ops.iter());
                    let live = if hi - lo == 64 {
                        u64::MAX
                    } else {
                        (1u64 << (hi - lo)) - 1
                    };
                    let mut go = so.phase & live;
                    let mut gb = sb.phase & live;
                    for q in 0..ordinary.nq {
                        if !ordinary.io.iter().any(|x| x.0 as usize == q) {
                            go |= so.qubits[q] & live;
                        }
                    }
                    for q in 0..borrowed.nq {
                        if !borrowed.io.iter().any(|x| x.0 as usize == q) {
                            gb |= sb.qubits[q] & live;
                        }
                    }
                    if go != 0 || gb != 0 {
                        eprintln!(
                            "SKYCOF_DEC_BORROW garbage e={e} room={room} mode={mode:?} lo={lo} ordinary={go:#x} borrowed={gb:#x}"
                        );
                        ok = false;
                        break;
                    }
                    for (&qo, &qb) in ordinary.io.iter().zip(&borrowed.io) {
                        if (so.qubit(qo) ^ sb.qubit(qb)) & live != 0 {
                            eprintln!(
                                "SKYCOF_DEC_BORROW state mismatch e={e} room={room} mode={mode:?} lo={lo}"
                            );
                            ok = false;
                            break;
                        }
                    }
                }
                println!(
                    "{{\"kind\":\"skycof-decoder-borrow-amb\",\"e\":{e},\"room\":{room},\"mode\":\"{mode:?}\",\"cases\":{total},\"ordinary_peak\":{},\"borrowed_peak\":{},\"result\":\"{}\"}}",
                    ordinary.peak,
                    borrowed.peak,
                    if ok { "PASS" } else { "FAIL" }
                );
                if !ok {
                    return false;
                }
            }
        }
    }
    println!(
        "{{\"kind\":\"skycof-decoder-borrow-amb-summary\",\"e_min\":2,\"e_max\":6,\"cases\":{cases},\"borrower_values\":2,\"result\":\"PASS\"}}"
    );
    true
}

// ─── 1. exhaustive ──────────────────────────────────────────────────────────────────────
fn exhaustive() -> bool {
    let maxe = env_usize("SKYCOF_DEC_EXH_MAXE", 6);
    let mut configs = 0usize;
    let mut cases = 0u64;
    let mut ok = true;
    for e in 2..=maxe {
        for &w in &[1usize, 2, 3, 4, 8] {
            if w > 2 && w >= e + 1 && w != 8 {
                continue;
            }
            for &has_en in &[false, true] {
                let n = Window::new(e, w).n();
                let floor = dec::min_room(has_en);
                for room in floor..=floor + n + 1 {
                    for &m in &[0usize, 1, 3] {
                        for &(has_cf, has_park) in &[(true, true), (true, false), (false, false)] {
                            // keep e = maxe affordable: full room grid only at m = 3 with all options
                            if e == maxe
                                && !(has_cf && has_park && m == 3)
                                && room != floor
                                && room != floor + n
                            {
                                continue;
                            }
                            let g = Geo {
                                e,
                                w,
                                room,
                                m,
                                has_en,
                                has_cf,
                                has_park,
                            };
                            let nbits = 2 * e
                                + has_en as usize
                                + 1
                                + has_cf as usize
                                + 2 * has_park as usize
                                + m;
                            let inputs: Vec<Val> = (0..1u64 << nbits)
                                .map(|i| {
                                    val_from_bits(
                                        &g,
                                        &(0..nbits).map(|k| (i >> k) & 1 == 1).collect::<Vec<_>>(),
                                    )
                                })
                                .collect();
                            for mode in [Mode::Push, Mode::Pop, Mode::PushPop] {
                                let b = build(&g, mode);
                                let want_t = match mode {
                                    Mode::PushPop => {
                                        2 * dec::toffoli_cost(e, w, m, room, has_en, has_park)
                                    }
                                    _ => dec::toffoli_cost(e, w, m, room, has_en, has_park),
                                };
                                if b.toff != want_t
                                    || b.scratch as usize != dec::scratch_cost(e, w, room, has_en)
                                {
                                    eprintln!("SKYCOF_DEC cost mismatch {mode:?} {g:?}: toffoli {} (formula {want_t}), scratch {} (formula {})",
                                        b.toff, b.scratch, dec::scratch_cost(e, w, room, has_en));
                                    ok = false;
                                }
                                let bad = run_batches(&b, &g, mode, &inputs, format!("exh{e}-{w}-{room}-{m}-{has_en}-{has_cf}-{has_park}-{mode:?}").as_bytes());
                                if bad > 0 {
                                    ok = false;
                                    eprintln!(
                                        "SKYCOF_DEC exhaustive FAIL {mode:?} {g:?}: {bad} of {}",
                                        inputs.len()
                                    );
                                }
                                cases += inputs.len() as u64;
                            }
                            configs += 1;
                        }
                    }
                }
            }
        }
        // tick 0
        for &has_cf in &[false, true] {
            let g = Geo {
                e,
                w: 4,
                room: 1,
                m: 0,
                has_en: false,
                has_cf,
                has_park: false,
            };
            let nbits = 2 * e + 1 + has_cf as usize;
            let inputs: Vec<Val> = (0..1u64 << nbits)
                .map(|i| {
                    val_from_bits(
                        &g,
                        &(0..nbits).map(|k| (i >> k) & 1 == 1).collect::<Vec<_>>(),
                    )
                })
                .collect();
            let b = build(&g, Mode::First);
            if b.toff != 0 || b.scratch != 0 {
                ok = false;
                eprintln!("SKYCOF_DEC first_tick cost {} / {}", b.toff, b.scratch);
            }
            let bad = run_batches(&b, &g, Mode::First, &inputs, b"first");
            if bad > 0 {
                ok = false;
                eprintln!("SKYCOF_DEC first_tick FAIL e={e}: {bad}");
            }
            cases += inputs.len() as u64;
        }
    }
    eprintln!("SKYCOF_DEC exhaustive: {configs} geometries x (push, pop, push+pop) + tick 0, {cases} input cases: {}",
        if ok { "all exact (spec outputs, 0 scratch garbage, 0 phase, cost formula)" } else { "FAIL" });
    ok
}

// ─── 2. decision vs the deciders ────────────────────────────────────────────────────────
fn deciders() -> bool {
    let mut ok = true;
    let mut n_ex = 0u64;
    let mut n_amb = 0u64;
    for e in 2..=11usize {
        for w in 1..=e + 2 {
            for sv in (0..1u64 << e).step_by(2) {
                for rv in (1..1u64 << e).step_by(2) {
                    let (s, r) = (from_u64(sv), from_u64(rv));
                    let (_, amb) = model::decide(&s, &r, e, w, true);
                    let want = scd_amb(&s, &r, w, e);
                    let gec = model::ge_circuit(&s, &r, e, w);
                    // conservative: ge = 0 must prove 2r < s
                    if !gec && 2 * rv >= sv {
                        ok = false;
                        if n_ex < 5 {
                            eprintln!("SKYCOF_DEC not conservative e={e} w={w} s={sv} r={rv}");
                        }
                    }
                    if amb != want {
                        ok = false;
                        if n_ex < 5 {
                            eprintln!("SKYCOF_DEC deciders mismatch e={e} w={w} s={sv} r={rv}: circuit {amb} scd {want}");
                        }
                    }
                    n_amb += amb as u64;
                    n_ex += 1;
                }
            }
        }
    }
    // full width: random, near-tie and top-heavy post-states
    let mut rng = Rng::new(0x5c0f_dec0);
    let mut n_fw = 0u64;
    let mut ties = 0u64;
    for _ in 0..2_000_000u64 {
        let e = [256usize, 255, 230, 200, 129, 100, 66, 65, 64, 40][rng.below(10) as usize];
        let w = [64usize, 48, 32, 63, 65][rng.below(5) as usize];
        let kind = rng.below(4);
        let mut s = rng.bits_u(e);
        let mut r = rng.bits_u(e);
        match kind {
            0 => {}
            1 => {
                // s ~ 2r: windows equal or off by one
                r = rng.bits_u(e - 1);
                let d = rng.below(9) as i64 - 4;
                let two_r = shl1(&r);
                s = if d >= 0 {
                    add(&two_r, &from_u64(d as u64))
                } else {
                    sub(&two_r, &from_u64((-d) as u64))
                };
                s = mask_bits(&s, e);
            }
            2 => {
                // leading zeros of random depth
                let k = rng.below(e as u64) as usize;
                s = mask_bits(&s, e - k);
                r = mask_bits(&r, e - k.min(e - 1));
            }
            _ => {
                // equal window tops, random below
                let lo = e.saturating_sub(w).max(1);
                let lows = mask_bits(&rng.bits_u(e), lo + 1);
                let lowr = mask_bits(&rng.bits_u(e), lo);
                let x = shr_bits(&mask_bits(&r, e), lo);
                let mut xs = x;
                for _ in 0..lo + 1 {
                    xs = shl1(&xs);
                } // s window = x
                s = mask_bits(&add(&xs, &lows), e);
                let mut xr = x;
                for _ in 0..lo {
                    xr = shl1(&xr);
                }
                r = mask_bits(&add(&xr, &lowr), e);
            }
        }
        s[0] &= !1;
        r[0] |= 1;
        let (_, amb) = model::decide(&s, &r, e, w, true);
        let want = scd_amb(&s, &r, w, e);
        let gec = model::ge_circuit(&s, &r, e, w);
        let exact_ge = ge(&shl1(&r), &s);
        if !gec && exact_ge {
            ok = false;
            eprintln!("SKYCOF_DEC full-width not conservative e={e} w={w}");
        }
        if amb != want {
            ok = false;
            eprintln!("SKYCOF_DEC full-width deciders mismatch e={e} w={w}");
        }
        if amb && !exact_ge {
            ties += 1;
        }
        n_fw += 1;
    }
    eprintln!("SKYCOF_DEC deciders: {n_ex} exhaustive post-states (e<=11, every window; {n_amb} ambiguous) and {n_fw} full-width \
              (incl. near-tie) post-states: circuit decision == scd k=0 decode, ge=0 always proves 2r<s ({ties} window ties in the \
              adversarial set): {}", if ok { "OK" } else { "FAIL" });
    ok
}

// ─── 3. full width ──────────────────────────────────────────────────────────────────────
fn fullwidth() -> bool {
    let mut ok = true;
    let mut total = 0usize;
    let mut rng = Rng::new(0xF011_3D7E);
    let geos: Vec<Geo> = vec![
        Geo {
            e: 256,
            w: 64,
            room: 2,
            m: 40,
            has_en: true,
            has_cf: true,
            has_park: true,
        },
        Geo {
            e: 256,
            w: 64,
            room: 3,
            m: 40,
            has_en: true,
            has_cf: true,
            has_park: true,
        },
        Geo {
            e: 256,
            w: 64,
            room: 20,
            m: 63,
            has_en: true,
            has_cf: true,
            has_park: true,
        },
        Geo {
            e: 256,
            w: 64,
            room: 66,
            m: 63,
            has_en: true,
            has_cf: true,
            has_park: true,
        },
        Geo {
            e: 256,
            w: 64,
            room: 1,
            m: 63,
            has_en: false,
            has_cf: true,
            has_park: false,
        },
        Geo {
            e: 256,
            w: 64,
            room: 65,
            m: 63,
            has_en: false,
            has_cf: true,
            has_park: false,
        },
        Geo {
            e: 230,
            w: 48,
            room: 10,
            m: 30,
            has_en: true,
            has_cf: true,
            has_park: false,
        },
        Geo {
            e: 200,
            w: 32,
            room: 34,
            m: 30,
            has_en: false,
            has_cf: false,
            has_park: true,
        },
        Geo {
            e: 65,
            w: 64,
            room: 66,
            m: 20,
            has_en: true,
            has_cf: true,
            has_park: true,
        },
        Geo {
            e: 40,
            w: 64,
            room: 5,
            m: 20,
            has_en: true,
            has_cf: true,
            has_park: true,
        },
        Geo {
            e: 10,
            w: 64,
            room: 2,
            m: 8,
            has_en: true,
            has_cf: true,
            has_park: true,
        },
    ];
    for g in &geos {
        let mut inputs = Vec::with_capacity(4096);
        for i in 0..4096 {
            let mut x = Val {
                s: rng.bits_u(g.e),
                r: rng.bits_u(g.e),
                en: rng.next() & 1 == 1,
                typ: rng.next() & 1 == 1,
                cf: rng.next() & 1 == 1,
                flag: rng.next() & 3 == 0,
                bit: rng.next() & 1 == 1,
                h: rng.next() & ((1u64 << g.m) - 1),
            };
            if i % 2 == 0 {
                // valid post-states, half of them near a tie
                x.s[0] &= !1;
                x.r[0] |= 1;
                if i % 4 == 0 && g.e > 2 {
                    let r = rng.bits_u(g.e - 1);
                    let s = add(&shl1(&r), &from_u64(rng.below(5)));
                    x.r = r;
                    x.r[0] |= 1;
                    x.s = mask_bits(&s, g.e);
                    x.s[0] &= !1;
                }
            }
            if !g.has_en {
                x.en = false;
            }
            if !g.has_cf {
                x.cf = false;
            }
            if !g.has_park {
                x.flag = false;
                x.bit = false;
            }
            inputs.push(x);
        }
        for mode in [Mode::Push, Mode::Pop, Mode::PushPop] {
            let b = build(g, mode);
            let want_t = dec::toffoli_cost(g.e, g.w, g.m, g.room, g.has_en, g.has_park)
                * if mode == Mode::PushPop { 2 } else { 1 };
            if b.toff != want_t {
                ok = false;
                eprintln!(
                    "SKYCOF_DEC full-width cost mismatch {g:?} {mode:?}: {} vs {want_t}",
                    b.toff
                );
            }
            let bad = run_batches(&b, g, mode, &inputs, format!("fw{g:?}{mode:?}").as_bytes());
            if bad > 0 {
                ok = false;
                eprintln!("SKYCOF_DEC full-width FAIL {mode:?} {g:?}: {bad}");
            }
            total += inputs.len();
        }
    }
    eprintln!("SKYCOF_DEC full-width: {} geometries, {total} random/near-tie cases through push, pop, push+pop: {}",
        geos.len(), if ok { "all exact" } else { "FAIL" });
    ok
}

// ─── 4. chained walks ───────────────────────────────────────────────────────────────────
const R: usize = 400;

struct Env {
    e: Vec<usize>,
    m: Vec<usize>,
}

fn load_env() -> Env {
    let path = env_str(
        "SKYCOF_DEC_BASES",
        "R:/Coding/shor2/barrier/skycof-deciders/scd_n10M_s20261001_bases.tsv",
    );
    let txt =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("SKYCOF_DEC_BASES {path}: {e}"));
    let mut lines = txt.lines();
    let head: Vec<&str> = lines.next().unwrap().split('\t').collect();
    let ci = |name: &str| {
        head.iter()
            .position(|h| *h == name)
            .unwrap_or_else(|| panic!("column {name}"))
    };
    let (kc, hc) = (ci("kcof"), ci(&env_str("SKYCOF_DEC_HCOL", "H_k0w64")));
    let (mcof, mh) = (
        env_usize("SKYCOF_DEC_MCOF", 8),
        env_usize("SKYCOF_DEC_MH", 10),
    );
    let mut e = vec![];
    let mut m = vec![];
    for l in lines {
        let f: Vec<&str> = l.split('\t').collect();
        if f.len() < head.len() {
            continue;
        }
        e.push((f[kc].parse::<usize>().unwrap() + mcof).min(256).max(2));
        m.push(f[hc].parse::<usize>().unwrap() + mh);
    }
    assert_eq!(e.len(), R);
    for t in 1..R {
        m[t] = m[t].max(m[t - 1]);
    }
    Env { e, m }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum L {
    A,
    B,
    C,
    Parked,
}

struct Walk {
    post: Vec<(U, U)>,
    letter: Vec<L>,
    park: Option<usize>,
}

fn walk(d: &U) -> Walk {
    let (mut u, mut v, mut s, mut r) = (*d, P, zero(), from_u64(1));
    let mut post = Vec::with_capacity(R);
    let mut letter = Vec::with_capacity(R);
    let mut park = None;
    for t in 0..R {
        let k;
        if is_zero(&u) {
            s = mod_dbl(&s);
            k = L::Parked;
        } else if u[0] & 1 == 0 {
            u = shr1(&u);
            s = shl1(&s);
            k = L::A;
        } else if ge(&u, &v) {
            u = shr1(&sub(&u, &v));
            r = add(&r, &s);
            s = shl1(&s);
            k = L::B;
        } else {
            let nu = shr1(&sub(&v, &u));
            v = u;
            u = nu;
            let ns = shl1(&r);
            r = add(&r, &s);
            s = ns;
            k = L::C;
        }
        if is_zero(&u) && park.is_none() {
            park = Some(t);
            s = fold(&s);
        }
        post.push((s, r));
        letter.push(k);
    }
    Walk { post, letter, park }
}

struct WalkCircuit {
    ops: Vec<Op>,
    fwd: Vec<(usize, usize)>,
    rev: Vec<(usize, usize)>,
    nq: usize,
    nb: usize,
    s: Vec<Q>,
    r: Vec<Q>,
    en: Q,
    typ: Q,
    cf: Q,
    flag: Q,
    bit: Q,
    h: Vec<Q>,
    room: Vec<usize>,
    toff_fwd: Vec<usize>,
    toff_rev: Vec<usize>,
    scratch: Vec<u32>,
}

fn room_profile(env: &Env, w: usize, t_en: usize) -> Vec<usize> {
    let mode = env_str("SKYCOF_DEC_ROOM", "rand");
    let mut rng = Rng::new(77);
    (0..R)
        .map(|t| {
            let has_en = t >= t_en;
            let n = Window::new(env.e[t], w).n();
            let floor = dec::min_room(has_en);
            match mode.as_str() {
                "full" => floor + n,
                "floor" => floor,
                _ => floor + rng.below(n as u64 + 2) as usize,
            }
        })
        .collect()
}

fn build_walk(env: &Env, w: usize, t_en: usize) -> WalkCircuit {
    let mut c = Builder::new();
    let s = c.alloc_qubits(256);
    let r = c.alloc_qubits(256);
    let (en, typ, cf, flag, bit) = (
        c.alloc_qubit(),
        c.alloc_qubit(),
        c.alloc_qubit(),
        c.alloc_qubit(),
        c.alloc_qubit(),
    );
    let mut h = Hreg::new();
    let room = room_profile(env, w, t_en);
    let mut fwd = vec![];
    let mut rev = vec![(0, 0); R];
    let mut scratch = vec![0u32; R];
    for t in 0..R {
        h.grow_to(&mut c, env.m[t]);
        let a = c.op_count();
        let base = c.active_qubits();
        let ((), pk) = c.r3_peak(|c| {
            if t == 0 {
                dec::first_tick(c, &s, typ, Some(cf));
            } else {
                let has_en = t >= t_en;
                let tio = TickIo {
                    s: &s,
                    r: &r,
                    e: env.e[t],
                    en: has_en.then_some(en),
                    typ,
                    cflag: Some(cf),
                    park: has_en.then_some((flag, bit)),
                };
                dec::push(c, &tio, &h, DecCfg { w, room: room[t] });
            }
        });
        scratch[t] = pk - base;
        fwd.push((a, c.op_count()));
    }
    for t in (0..R).rev() {
        let a = c.op_count();
        let hw = Hreg {
            wires: h.wires[..env.m[t]].to_vec(),
        };
        if t == 0 {
            dec::first_tick(&mut c, &s, typ, Some(cf));
        } else {
            let has_en = t >= t_en;
            let tio = TickIo {
                s: &s,
                r: &r,
                e: env.e[t],
                en: has_en.then_some(en),
                typ,
                cflag: Some(cf),
                park: has_en.then_some((flag, bit)),
            };
            dec::pop(&mut c, &tio, &hw, DecCfg { w, room: room[t] });
        }
        rev[t] = (a, c.op_count());
    }
    let (nq, nb) = c.i13_dims();
    let ops = c.take_ops();
    let toff_fwd = fwd.iter().map(|&(a, b)| ccx_count(&ops[a..b])).collect();
    let toff_rev = rev.iter().map(|&(a, b)| ccx_count(&ops[a..b])).collect();
    WalkCircuit {
        ops,
        fwd,
        rev,
        nq,
        nb: nb + 1,
        s,
        r,
        en,
        typ,
        cf,
        flag,
        bit,
        h: h.wires,
        room,
        toff_fwd,
        toff_rev,
        scratch,
    }
}

#[derive(Default, Clone, Debug)]
struct WalkStats {
    walks: u64,
    valid: u64,
    env_field: u64,
    env_hreg: u64,
    unparked: u64,
    early_park: u64,
    fail_valid: u64,
    fail_invalid_but_passed: u64,
    pushes: u64,
    park_min: usize,
    letters_checked: u64,
    toff_exec: u64,
}

fn put_u(sim: &mut Simulator<'_, sha3::Shake256Reader>, wires: &[Q], vals: &[U]) {
    for (i, q) in wires.iter().enumerate() {
        let (li, sh) = (i / 64, i % 64);
        let mut wv = 0u64;
        for (k, v) in vals.iter().enumerate() {
            wv |= ((v[li] >> sh) & 1) << k;
        }
        *sim.qubit_mut(*q) = wv;
    }
}
fn get_u(sim: &Simulator<'_, sha3::Shake256Reader>, wires: &[Q], k: usize) -> U {
    let mut v = zero();
    for (i, q) in wires.iter().enumerate() {
        if (sim.qubit(*q) >> k) & 1 == 1 {
            v[i / 64] |= 1 << (i % 64);
        }
    }
    v
}
fn word(f: impl Fn(usize) -> bool, n: usize) -> u64 {
    (0..n).fold(0u64, |a, k| a | ((f(k) as u64) << k))
}

fn walk_batch(
    wc: &WalkCircuit,
    env: &Env,
    w: usize,
    t_en: usize,
    ds: &[U],
    agree: u64,
    st: &mut WalkStats,
    tag: u64,
) {
    let nw = ds.len();
    let walks: Vec<Walk> = ds.iter().map(walk).collect();
    // classical envelope classification
    let mut valid = vec![true; nw];
    for (k, wk) in walks.iter().enumerate() {
        st.walks += 1;
        let Some(pk) = wk.park else {
            st.unparked += 1;
            valid[k] = false;
            continue;
        };
        st.park_min = st.park_min.min(pk);
        if pk < t_en {
            st.early_park += 1;
            valid[k] = false;
        }
        let mut cnt = 0usize;
        let mut fld = false;
        let mut hr = false;
        for t in 1..R {
            let (s, r) = &wk.post[t];
            if t < pk {
                if bits(s).max(bits(r)) > env.e[t] {
                    fld = true;
                }
                let (_, amb) = model::decide(s, r, env.e[t], w, true);
                cnt += amb as usize;
            } else if t == pk && t >= t_en {
                cnt += 1;
            }
            if cnt > env.m[t] {
                hr = true;
            }
        }
        st.pushes += cnt as u64;
        if fld {
            st.env_field += 1;
            valid[k] = false;
        }
        if hr {
            st.env_hreg += 1;
            valid[k] = false;
        }
    }
    let mut rd = xof(&tag.to_le_bytes());
    let mut sim = Simulator::new(wc.nq, wc.nb, &mut rd);
    sim.clear_for_shot();
    let live = if nw == 64 { u64::MAX } else { (1u64 << nw) - 1 };
    let mut bad = 0u64; // per-shot failure mask
    let parked_at = |k: usize, t: usize| walks[k].park.is_some_and(|p| t >= p);
    let is_park = |k: usize, t: usize| walks[k].park == Some(t);
    // forward
    for t in 0..R {
        let sv: Vec<U> = walks.iter().map(|wk| wk.post[t].0).collect();
        let rv: Vec<U> = walks.iter().map(|wk| wk.post[t].1).collect();
        put_u(&mut sim, &wc.s, &sv);
        put_u(&mut sim, &wc.r, &rv);
        let has_en = t >= t_en && t > 0;
        *sim.qubit_mut(wc.en) = if has_en {
            word(|k| !parked_at(k, t), nw)
        } else {
            0
        };
        *sim.qubit_mut(wc.typ) = word(|k| walks[k].letter[t] == L::A, nw);
        *sim.qubit_mut(wc.cf) = word(|k| walks[k].letter[t] == L::C, nw);
        *sim.qubit_mut(wc.flag) = if has_en {
            word(|k| is_park(k, t), nw)
        } else {
            0
        };
        *sim.qubit_mut(wc.bit) = if has_en {
            word(|k| is_park(k, t), nw) & agree
        } else {
            0
        };
        let (a, b) = wc.fwd[t];
        sim.apply_iter(wc.ops[a..b].iter());
        bad |= sim.qubit(wc.typ) | sim.qubit(wc.cf) | sim.qubit(wc.bit);
        for k in 0..nw {
            if get_u(&sim, &wc.s, k) != sv[k] || get_u(&sim, &wc.r, k) != rv[k] {
                bad |= 1 << k;
            }
        }
        *sim.qubit_mut(wc.typ) = 0;
        *sim.qubit_mut(wc.cf) = 0;
        *sim.qubit_mut(wc.bit) = 0;
    }
    // reverse: the cofactors are un-stepped from the POPPED letters only
    let mut cur: Vec<(U, U)> = walks.iter().map(|wk| wk.post[R - 1]).collect();
    for t in (0..R).rev() {
        let sv: Vec<U> = cur.iter().map(|x| x.0).collect();
        let rv: Vec<U> = cur.iter().map(|x| x.1).collect();
        put_u(&mut sim, &wc.s, &sv);
        put_u(&mut sim, &wc.r, &rv);
        let has_en = t >= t_en && t > 0;
        *sim.qubit_mut(wc.en) = if has_en {
            word(|k| !parked_at(k, t), nw)
        } else {
            0
        };
        *sim.qubit_mut(wc.flag) = if has_en {
            word(|k| is_park(k, t), nw)
        } else {
            0
        };
        let (a, b) = wc.rev[t];
        sim.apply_iter(wc.ops[a..b].iter());
        let (ty, cfw, bw) = (sim.qubit(wc.typ), sim.qubit(wc.cf), sim.qubit(wc.bit));
        // Hreg above the previous tick's width must be empty
        if t >= 1 {
            for q in &wc.h[env.m[t - 1]..env.m[t]] {
                bad |= sim.qubit(*q);
            }
        }
        for k in 0..nw {
            let (pt, pc, pb) = ((ty >> k) & 1 == 1, (cfw >> k) & 1 == 1, (bw >> k) & 1 == 1);
            let truth = walks[k].letter[t];
            let (mut s, mut r) = cur[k];
            if walks[k].park.is_some_and(|p| t > p) {
                if pt || pc || pb {
                    bad |= 1 << k;
                }
                s = mod_half(&s);
            } else {
                let mut lt = if pc && !pt {
                    L::C
                } else if pt && !pc {
                    L::A
                } else if !pt && !pc {
                    L::B
                } else {
                    bad |= 1 << k;
                    L::B
                };
                if is_park(k, t) {
                    if has_en && pb != ((agree >> k) & 1 == 1) {
                        bad |= 1 << k;
                    }
                    if !has_en && pb {
                        bad |= 1 << k;
                    }
                    s = unfold(&s);
                    lt = L::B;
                } else if pb {
                    bad |= 1 << k;
                }
                if lt != truth && !(truth == L::B && is_park(k, t)) {
                    bad |= 1 << k;
                }
                st.letters_checked += 1;
                if s[0] & 1 == 1 {
                    bad |= 1 << k;
                }
                let a2 = shr1(&s);
                match lt {
                    L::A => {
                        s = a2;
                    }
                    L::B => {
                        if !ge(&r, &a2) {
                            bad |= 1 << k;
                        } else {
                            r = sub(&r, &a2);
                            s = a2;
                        }
                    }
                    _ => {
                        if !ge(&r, &a2) {
                            bad |= 1 << k;
                        } else {
                            let ns = sub(&r, &a2);
                            r = a2;
                            s = ns;
                        }
                    }
                }
            }
            if t > 0 && (s, r) != walks[k].post[t - 1] {
                bad |= 1 << k;
            }
            cur[k] = (s, r);
        }
        *sim.qubit_mut(wc.typ) = 0;
        *sim.qubit_mut(wc.cf) = 0;
        *sim.qubit_mut(wc.bit) = 0;
    }
    for k in 0..nw {
        if cur[k] != (zero(), from_u64(1)) {
            bad |= 1 << k;
        }
    }
    // every non-register wire (scratch, Hreg, flags) must be 0, and the phase too
    let mut garbage = sim.phase;
    let reg: std::collections::HashSet<u64> = wc.s.iter().chain(wc.r.iter()).map(|q| q.0).collect();
    for q in 0..wc.nq {
        if !reg.contains(&(q as u64)) {
            garbage |= sim.qubits[q];
        }
    }
    bad |= garbage;
    bad &= live;
    st.toff_exec += sim.stats.toffoli_gates;
    for k in 0..nw {
        let b = (bad >> k) & 1 == 1;
        if valid[k] {
            st.valid += 1;
            if b {
                st.fail_valid += 1;
            }
        } else if !b {
            st.fail_invalid_but_passed += 1;
        }
    }
}

fn walks_test() -> bool {
    let n = env_usize("SKYCOF_DEC_WALKS", 20_000);
    if n == 0 {
        return true;
    }
    let w = env_usize("SKYCOF_DEC_W", 64);
    let t_en = env_usize("SKYCOF_DEC_TEN", 250);
    let nth = env_usize("SKYCOF_DEC_THREADS", 3).max(1);
    let seed = env_usize("SKYCOF_DEC_SEED", 20261001) as u64;
    let env = load_env();
    let wc = build_walk(&env, w, t_en);
    // per-tick cost check against the formula
    let mut ok = true;
    for t in 1..R {
        let has_en = t >= t_en;
        let f = dec::toffoli_cost(env.e[t], w, env.m[t], wc.room[t], has_en, has_en);
        if wc.toff_fwd[t] != f
            || wc.toff_rev[t] != f
            || wc.scratch[t] as usize != dec::scratch_cost(env.e[t], w, wc.room[t], has_en)
        {
            ok = false;
            eprintln!(
                "SKYCOF_DEC walk cost mismatch t={t}: fwd {} rev {} formula {f}",
                wc.toff_fwd[t], wc.toff_rev[t]
            );
        }
    }
    let per = n.div_ceil(nth);
    let t0 = std::time::Instant::now();
    let stats: Vec<WalkStats> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..nth)
            .map(|th| {
                let (wc, env) = (&wc, &env);
                sc.spawn(move || {
                    let mut rng = Rng::new(seed.wrapping_mul(1_000_003).wrapping_add(th as u64));
                    let mut st = WalkStats {
                        park_min: usize::MAX,
                        ..Default::default()
                    };
                    let mut done = 0;
                    let mut b = 0u64;
                    while done < per {
                        let k = 64.min(per - done);
                        let ds: Vec<U> = (0..k).map(|_| rng.scalar()).collect();
                        let agree = rng.next();
                        walk_batch(wc, env, w, t_en, &ds, agree, &mut st, (th as u64) << 40 | b);
                        done += k;
                        b += 1;
                        if th == 0 && b % 200 == 0 {
                            eprintln!(
                                "SKYCOF_DEC walk progress {} / {per} ({:.0}s)",
                                done,
                                t0.elapsed().as_secs_f64()
                            );
                        }
                    }
                    st
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut t = WalkStats {
        park_min: usize::MAX,
        ..Default::default()
    };
    for s in stats {
        t.walks += s.walks;
        t.valid += s.valid;
        t.env_field += s.env_field;
        t.env_hreg += s.env_hreg;
        t.unparked += s.unparked;
        t.early_park += s.early_park;
        t.fail_valid += s.fail_valid;
        t.fail_invalid_but_passed += s.fail_invalid_but_passed;
        t.pushes += s.pushes;
        t.park_min = t.park_min.min(s.park_min);
        t.letters_checked += s.letters_checked;
        t.toff_exec += s.toff_exec;
    }
    let ftot: usize = wc.toff_fwd.iter().sum();
    let rtot: usize = wc.toff_rev.iter().sum();
    eprintln!("SKYCOF_DEC walks: {} walks (w={w}, en/park wires from t={t_en}, room profile {}), {:.0}s: valid {} -> {} failures; \
              {} letters popped and checked; outside the envelope: field {} hreg {} unparked {} early-park {} ({} of those still clean); \
              stored bits/walk {:.2} (incl. park bit); earliest park {}; circuit Toffoli fwd {ftot} rev {rtot} (executed/walk {:.0})",
        t.walks, env_str("SKYCOF_DEC_ROOM", "rand"), t0.elapsed().as_secs_f64(), t.valid, t.fail_valid, t.letters_checked,
        t.env_field, t.env_hreg, t.unparked, t.early_park, t.fail_invalid_but_passed,
        t.pushes as f64 / t.walks as f64, t.park_min, t.toff_exec as f64 / t.walks as f64);
    ok && t.fail_valid == 0 && t.valid > 0
}

// ─── 5. cost at the design widths ───────────────────────────────────────────────────────
fn cost_report() {
    let w = env_usize("SKYCOF_DEC_W", 64);
    let t_en = env_usize("SKYCOF_DEC_TEN", 250);
    eprintln!("SKYCOF_DEC cost per call (measured gate counts == formula), e = 256, w = {w}:");
    for &(en, park) in &[(false, false), (true, false), (true, true)] {
        let line: Vec<String> = [1usize, 2, 3, 4, 8, 16, 32, 48, 64, 65, 66, 67]
            .iter()
            .filter(|&&rm| rm >= dec::min_room(en))
            .map(|&rm| {
                let g = Geo {
                    e: 256,
                    w,
                    room: rm,
                    m: 0,
                    has_en: en,
                    has_cf: true,
                    has_park: park,
                };
                let b = build(&g, Mode::Push);
                assert_eq!(b.toff, dec::toffoli_cost(256, w, 0, rm, en, park));
                format!("room {rm}: {} T/{} wires", b.toff, b.scratch)
            })
            .collect();
        eprintln!(
            "   en={en} park={park} (+ m Fredkins for Hreg width m): {}",
            line.join(", ")
        );
    }
    let env = load_env();
    let rooms: Option<Vec<usize>> = std::env::var("SKYCOF_DEC_ROOMS").ok().map(|p| {
        std::fs::read_to_string(&p)
            .unwrap()
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| l.trim().parse().unwrap())
            .collect()
    });
    let mut rows = vec![];
    for (name, f) in [("full", 0usize), ("floor", 1), ("profile", 2)] {
        if f == 2 && rooms.is_none() {
            continue;
        }
        let (mut dsum, mut psum) = (0usize, 0usize);
        for t in 1..R {
            let has_en = t >= t_en;
            let n = Window::new(env.e[t], w).n();
            let fl = dec::min_room(has_en);
            let rm = match f {
                0 => fl + n,
                1 => fl,
                _ => (rooms.as_ref().unwrap()[t] + 1).max(fl),
            };
            let tot = dec::toffoli_cost(env.e[t], w, env.m[t], rm, has_en, has_en);
            psum += env.m[t];
            dsum += tot - env.m[t];
        }
        rows.push(format!(
            "{name}: decode {:.1}k + push {:.1}k = {:.1}k",
            dsum as f64 / 1e3,
            psum as f64 / 1e3,
            (dsum + psum) as f64 / 1e3
        ));
    }
    eprintln!("SKYCOF_DEC per traversal (400 ticks; e = min(kcof+{}, 256), Hreg = {}+{}; en+park from t={t_en}): {}",
        env_usize("SKYCOF_DEC_MCOF", 8), env_str("SKYCOF_DEC_HCOL", "H_k0w64"), env_usize("SKYCOF_DEC_MH", 10), rows.join(" | "));
}

pub fn run() {
    let which = env_str("SKYCOF_DEC_SELFTEST", "all");
    if which == "borrow-amb" {
        if !borrow_amb_exhaustive() {
            std::process::exit(1);
        }
        return;
    }
    let all = which == "1" || which == "all";
    let mut ok = true;
    if all || which.contains("exh") {
        ok &= exhaustive();
    }
    if all || which.contains("dec") {
        ok &= deciders();
    }
    if all || which.contains("full") {
        ok &= fullwidth();
    }
    if all || which.contains("walk") {
        ok &= walks_test();
    }
    if all || which.contains("cost") {
        cost_report();
    }
    eprintln!("SKYCOF_DEC_SELFTEST {}", if ok { "PASS" } else { "FAIL" });
    if !ok {
        std::process::exit(1);
    }
}
