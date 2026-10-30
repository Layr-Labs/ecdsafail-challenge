//! greedyfrog diagnostics against the grader's shots: regenerate eval_circuit's inputs from an ops.bin (same Fiat-Shamir
//! hash), replay both divisions of every shot through the lane model and flag the first slot where the circuit's
//! classical shortcuts (windows, 40-lane top compares, the decode emulated bit for bit, the slot count) disagree with
//! the exact walk.
//! Run: GREEDYFROG_DIAG_OPS=path/to/ops.bin cargo test --release --bin build_circuit greedyfrog_diag -- --nocapture

use super::greedyfrog::{windows, Win, NB, NSLOTS, WC};
use super::greedyfrog_model::{p, rho_of, Lanes, Spec, N, W};
use alloy_primitives::U256;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use std::io::Read;

fn load_ops(path: &str) -> Vec<crate::circuit::Op> {
    use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
    let mut file = std::fs::File::open(path).unwrap();
    let mut header = [0u8; 16];
    file.read_exact(&mut header).unwrap();
    assert_eq!(&header[..8], b"QECCOPSZ");
    let n = u64::from_le_bytes(header[8..].try_into().unwrap()) as usize;
    let mut dec = zstd::stream::read::Decoder::new(std::io::BufReader::new(file)).unwrap();
    let mut ops = Vec::with_capacity(n);
    let mut rec = [0u8; 56];
    let rd = |r: &[u8], o: usize| u64::from_le_bytes(r[o..o + 8].try_into().unwrap());
    for _ in 0..n {
        dec.read_exact(&mut rec).unwrap();
        let kind_raw = u32::from_le_bytes(rec[0..4].try_into().unwrap());
        // OperationType discriminants are 0..=17 in declaration order
        let kind: OperationType = unsafe { std::mem::transmute(kind_raw as u8) };
        ops.push(Op { kind, q_control2: QubitId(rd(&rec, 8)), q_control1: QubitId(rd(&rec, 16)),
                      q_target: QubitId(rd(&rec, 24)), c_target: BitId(rd(&rec, 32)),
                      c_condition: BitId(rd(&rec, 40)), r_target: RegisterId(rd(&rec, 48)) });
    }
    ops
}

fn seed(ops: &[crate::circuit::Op]) -> sha3::Shake256Reader {
    let mut h = sha3::Shake256::default();
    h.update(b"quantum_ecc-fiat-shamir-v2");
    h.update(&(ops.len() as u64).to_le_bytes());
    for op in ops {
        h.update(&[op.kind as u8]);
        h.update(&op.q_control2.0.to_le_bytes());
        h.update(&op.q_control1.0.to_le_bytes());
        h.update(&op.q_target.0.to_le_bytes());
        h.update(&op.c_target.0.to_le_bytes());
        h.update(&op.c_condition.0.to_le_bytes());
        h.update(&op.r_target.0.to_le_bytes());
    }
    h.finalize_xof()
}

fn curve() -> crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
    let h = |s: &str| U256::from_str_radix(s, 16).unwrap();
    crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
        modulus: h("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U256::from(0),
        b: U256::from(7),
        gx: h("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: h("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: h("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    }
}

fn to_n(v: U256) -> N {
    let mut r = N::ZERO;
    for (i, limb) in v.as_limbs().iter().enumerate() {
        r |= N::from(*limb) << (64 * i);
    }
    r
}

/// Ring lanes [lo, lo + n) read MSB-first from lane lo (bit-reversed cofactor windows).
fn msb_first(ring: &[u8], lo: usize, n: usize) -> u64 {
    (0..n).fold(0u64, |a, i| (a << 1) | ring.get(lo + i).copied().unwrap_or(0) as u64)
}

/// Top-window compare of the circuit: [Y > X] over lanes W-WC..W-1 (masked to the top lb lanes when masked).
fn top_cmp(st: &Lanes, masked: bool) -> bool {
    let n = if masked { st.lb.min(WC) } else { WC };
    for i in 0..n {
        let (yv, xv) = (st.y[W - 1 - i], st.x[W - 1 - i]);
        if yv != xv {
            return yv > xv;
        }
    }
    false
}

/// The inverse slot's decode, bit for bit: normalised windows, sw, non-restoring rows (masked per row where the
/// window says so), the last-row sweep and r = sX - sY - jl (mod 32).
fn emu_decode(st: &Lanes, w: &Win) -> (bool, usize) {
    let slack = |ring: &[u8]| (0..31).take_while(|&j| ring[j] == 0).count();
    let (mut x, mut y) = (st.x.clone(), st.y.clone());
    let (mut la, mut lb) = (st.la, st.lb);
    let (mut sx, mut sy) = (slack(&x), slack(&y));
    let win = |ring: &[u8], s: usize| -> Vec<u8> { (0..NB).map(|i| ring[s + i]).collect() };
    let u = (la + sx) % 512;
    let v = (lb + sy) % 512;
    let mx = W as isize - 1 - u as isize;
    let (wx, wy) = (win(&x, sx), win(&y, sy));
    let gt = {
        let n = if w.mxp >= NB + 1 { NB } else { mx.clamp(0, NB as isize) as usize };
        let a = msb_first(&wy, 0, n);
        let b = msb_first(&wx, 0, n);
        a > b
    };
    let sw = u < v || (u == v && !gt);
    if sw {
        std::mem::swap(&mut x, &mut y);
        std::mem::swap(&mut la, &mut lb);
        std::mem::swap(&mut sx, &mut sy);
    }
    let u = (la + sx) % 512;
    let kt5 = (u + 512 - (lb + sy) % 512) % 512 % 32;
    let mx = W as isize - 1 - u as isize;
    // rem: index 0 = s0 (sign above lane 0), index i + 1 = window lane i
    let mut rem: Vec<u8> = std::iter::once(0).chain(win(&y, sy)).collect();
    let div = win(&x, sx);
    for j in 0..w.k {
        let top = j; // rem index of lane j - 1
        let mut bot = NB; // rem index of lane NB - 1
        if w.mx < NB - j + 1 {
            let up = mx as isize - (NB - j + 1) as isize; // >= 0: mask on from the start
            if up < 0 {
                let l = mx + j as isize - 1; // the divisor's LSB lane
                if l < j as isize - 1 {
                    continue; // mask never on: the row is the identity
                }
                bot = (l + 1) as usize;
            }
        }
        let width = bot - top + 1;
        let sign_prev = if j == 0 { 0 } else { rem[j - 1] };
        let r = rem[top..=bot].iter().fold(0u128, |a, &b| (a << 1) | b as u128);
        let d = (top..=bot).fold(0u128, |a, ri| {
            let lane = ri as isize - 1;
            let bit = if lane >= j as isize { div[lane as usize - j] } else { 0 };
            (a << 1) | bit as u128
        });
        let m = 1u128 << width;
        let nr = if sign_prev == 0 { (r + m - d) % m } else { (r + d) % m };
        for (k, ri) in (top..=bot).enumerate() {
            rem[ri] = ((nr >> (width - 1 - k)) & 1) as u8;
        }
    }
    let mut jl = 0;
    for j in (0..w.k).rev() {
        if kt5 >= j && rem[j] == 0 {
            jl = j;
            break;
        }
    }
    (sw, (sx + 64 - sy - jl) % 32)
}

/// Walk-lane invariants on the decode's view of a post-state: (kt = u - v as a signed 9-bit value, the target's slack
/// sY after the un-swap).
fn emu_lanes(st: &Lanes, w: &Win) -> (isize, usize) {
    let slack = |ring: &[u8]| (0..31).take_while(|&j| ring[j] == 0).count();
    let (x, y) = (&st.x, &st.y);
    let (sx, sy) = (slack(x), slack(y));
    let u = (st.la + sx) % 512;
    let v = (st.lb + sy) % 512;
    let mx = W as isize - 1 - u as isize;
    let win = |ring: &[u8], s: usize| -> Vec<u8> { (0..NB).map(|i| ring[s + i]).collect() };
    let gt = {
        let n = if w.mxp >= NB + 1 { NB } else { mx.clamp(0, NB as isize) as usize };
        msb_first(&win(y, sy), 0, n) > msb_first(&win(x, sx), 0, n)
    };
    let sw = u < v || (u == v && !gt);
    let (la, lb, sx, sy) = if sw { (st.lb, st.la, sy, sx) } else { (st.la, st.lb, sx, sy) };
    let kt = ((la + sx) % 512 + 512 - (lb + sy) % 512) % 512;
    let kt = if kt >= 256 { kt as isize - 512 } else { kt as isize };
    (kt, sy)
}

/// The decode's sw on a post-state (as emu_lanes).
fn la_sw(st: &Lanes, w: &Win) -> bool {
    let slack = |ring: &[u8]| (0..31).take_while(|&j| ring[j] == 0).count();
    let (x, y) = (&st.x, &st.y);
    let (sx, sy) = (slack(x), slack(y));
    let u = (st.la + sx) % 512;
    let v = (st.lb + sy) % 512;
    let mx = W as isize - 1 - u as isize;
    let win = |ring: &[u8], s: usize| -> Vec<u8> { (0..NB).map(|i| ring[s + i]).collect() };
    let gt = {
        let n = if w.mxp >= NB + 1 { NB } else { mx.clamp(0, NB as isize) as usize };
        msb_first(&win(y, sy), 0, n) > msb_first(&win(x, sx), 0, n)
    };
    u < v || (u == v && !gt)
}

/// The walk-lane levers' extra failure predicate: hosted lanes that are not |0> on an active shot.
fn lanes_break(st: &Lanes, w: &Win) -> Option<String> {
    let (kt, sy) = emu_lanes(st, w);
    if super::greedyfrog::lb_host() && !(0..32).contains(&kt) {
        return Some(format!("KT-HOST kt {kt} outside 0..32"));
    }
    if super::greedyfrog::sy_host() && sy > 1 {
        return Some(format!("SY-HOST sY {sy} > 1"));
    }
    if super::greedyfrog::div_top_bound() && w.mx < NB + 1 {
        // mX after the un-swap = W - 1 - u
        let slack = |ring: &[u8]| (0..31).take_while(|&j| ring[j] == 0).count();
        let (sx, sy) = (slack(&st.x), slack(&st.y));
        let u = (st.la + sx) % 512;
        let v = (st.lb + sy) % 512;
        let mxv = W as isize - 1 - u as isize;
        let mxw = W as isize - 1 - v as isize;
        // the divisor after the un-swap is the shorter cofactor (kt >= 0)
        let mdiv = if la_sw(st, w) { mxw } else { mxv };
        if super::greedyfrog::la_host() && !w.dtop_tight && w.dtop_near && w.act_const && mdiv > NB as isize + 32 {
            return Some(format!("LA-HOST mX {mdiv} > NB + 32"));
        }
        // a parked window keeps junk below its floor (park_lo): count it as a failure on every masked slot
        let floor = if super::greedyfrog::park_lo_zero() { w.mx.saturating_sub(1) } else { w.mx } as isize;
        if mdiv < floor {
            return Some(format!("PARK floor: mX {mdiv} < {floor}"));
        }
        if w.dtop_tight && mdiv > w.dtop as isize {
            return Some(format!("DIV-TOP mX {mdiv} > dtop {}", w.dtop));
        }
    }
    None
}

/// Replay one division's walk; returns the first disagreement (slot, reason).
fn diag_walk(x: N, ws: &[Win]) -> Option<String> {
    let mut sp = Spec::new(x);
    let mut ln = Lanes::from_spec(&sp);
    for (s, w) in ws.iter().enumerate() {
        let pre = ln.clone();
        let act = pre.la != 0;
        let step = act && pre.x[W - 1] == 1;
        sp.fwd();
        let (d, rho, sw, a1) = ln.fwd();
        // F9's unmasked WC-lane compare (only read when LA == LB after the renormalisation): a tie on the top WC lanes
        // of two different values would decide wrong. Pre-swap rings are the post-state rings swapped back.
        if act && ln.la != 0 {
            let (px, py, pla, plb) = if sw { (&ln.y, &ln.x, ln.lb, ln.la) } else { (&ln.x, &ln.y, ln.la, ln.lb) };
            if pla == plb && plb > 1 && px[W - 1] == 1 && (0..WC).all(|i| px[W - 1 - i] == py[W - 1 - i]) {
                return Some(format!("slot {s}: F9 top-{WC} tie"));
            }
        }
        if !act {
            continue;
        }
        if step {
            if pre.lb < w.lb.0 || pre.lb > w.lb.1 {
                return Some(format!("slot {s}: LB {} outside window {:?}", pre.lb, w.lb));
            }
            if pre.la - d < w.lad.0 || pre.la - d > w.lad.1 {
                return Some(format!("slot {s}: LA-d {} outside window {:?}", pre.la - d, w.lad));
            }
            let dc = usize::from(top_cmp(&pre, w.lb.0 < WC));
            if dc != d {
                return Some(format!("slot {s}: top compare d {dc} != {d}"));
            }
        }
        let (dsw, dr) = emu_decode(&ln, w);
        if dsw != sw || rho_of(dr) != (rho, a1) {
            return Some(format!("slot {s}: decode (sw {dsw}, r {dr}) != (sw {sw}, rho {rho}, a1 {a1})"));
        }
        if let Some(e) = lanes_break(&ln, w) {
            return Some(format!("slot {s}: {e}"));
        }
    }
    if ln.la != 0 {
        return Some(format!("walk not finished in {NSLOTS} slots"));
    }
    None
}

#[test]
fn greedyfrog_diag_shots() {
    let Ok(path) = std::env::var("GREEDYFROG_DIAG_OPS") else { return; };
    let ops = load_ops(&path);
    let mut xof = seed(&ops);
    let c = curve();
    let pp = p();
    let ws = windows();
    let mut bad = 0;
    let mut shot = 0;
    for _ in 0..9024 {
        let mut rb = [[0u8; 32]; 2];
        XofReader::read(&mut xof, &mut rb[0]);
        XofReader::read(&mut xof, &mut rb[1]);
        let (k1, k2) = (U256::from_le_bytes(rb[0]), U256::from_le_bytes(rb[1]));
        let t = c.mul(c.gx, c.gy, k1);
        let o = c.mul(c.gx, c.gy, k2);
        if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) {
            continue;
        }
        let e = c.add(t.0, t.1, o.0, o.1);
        let (tx, ox, ex) = (to_n(t.0), to_n(o.0), to_n(e.0));
        for (div, a) in [(1, tx), (2, ex)] {
            let dx = (a + pp - ox) % pp;
            let xr = if dx < pp - dx { dx } else { pp - dx };
            if let Some(why) = diag_walk(xr, &ws) {
                bad += 1;
                eprintln!("shot {shot} division {div}: {why}");
            }
        }
        shot += 1;
    }
    eprintln!("greedyfrog diag: {shot} shots, {bad} divisions flagged");
}

/// Random walks: the emulated circuit decode against the exact walk at every active slot; prints the first few
/// disagreements with the quotient detail (GREEDYFROG_DIAG_WALKS walks).
#[test]
fn greedyfrog_diag_decode_rate() {
    let Ok(n) = std::env::var("GREEDYFROG_DIAG_WALKS").map(|v| v.parse::<usize>().unwrap()) else { return; };
    let ws = windows();
    let pp = p();
    let mut s64 = 0x1234_5678_9abc_def1u64;
    let mut next = || { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; s64 };
    let mut bad = 0;
    let mut shown = 0;
    for _ in 0..n {
        let mut v = N::ZERO;
        for i in 0..4 {
            v |= N::from(next()) << (64 * i);
        }
        let v = v % pp;
        if v == N::ZERO {
            continue;
        }
        let x = if v < pp - v { v } else { pp - v };
        let mut sp = Spec::new(x);
        let mut ln = Lanes::from_spec(&sp);
        let mut last_ep = 0;
        for (s, w) in ws.iter().enumerate() {
            let act = ln.la != 0;
            let rec = sp.fwd();
            if let super::greedyfrog_model::Slot::Step { ep, .. } = rec {
                last_ep = ep;
            }
            let (_, rho, sw, a1) = ln.fwd();
            if !act {
                continue;
            }
            let (dsw, dr) = emu_decode(&ln, w);
            if dsw != sw || rho_of(dr) != (rho, a1) {
                bad += 1;
                if shown < 6 {
                    shown += 1;
                    let (tau, tbu) = if sw { (sp.tb, sp.ta) } else { (sp.ta, sp.tb) };
                    let q = tau / tbu;
                    let kt = tau.bit_len() as isize - tbu.bit_len() as isize;
                    let sl = |ring: &[u8]| (0..W).take_while(|&j| ring[j] == 0).count();
                    eprintln!("slot {s}: emu (sw {dsw}, r {dr}) truth (sw {sw}, rho {rho}, a1 {a1}); kt {kt} e' {last_ep} \
                               Q {q:#b} tA bits {} tB bits {} slacks X {} Y {} LA {} LB {} lag {} w {:?}",
                              tau.bit_len(), tbu.bit_len(), sl(&ln.x), sl(&ln.y), ln.la, ln.lb, sp.lag, w);
                }
                break;
            }
        }
    }
    eprintln!("greedyfrog diag decode: {n} walks, {bad} with a decode disagreement");
}

/// Failure rate of the whole predictor (windows, compares, decode, slot count) on random reflected inputs,
/// GREEDYFROG_DIAG_N walks on 4 threads; prints counts by reason and the expected failing shots per 9,024-shot run.
#[test]
fn greedyfrog_diag_rate() {
    let Ok(n) = std::env::var("GREEDYFROG_DIAG_N").map(|v| v.parse::<usize>().unwrap()) else { return; };
    let ws = windows();
    let pp = p();
    let res: Vec<Vec<String>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..4u64).map(|t| {
            let ws = &ws;
            sc.spawn(move || {
                let mut s64 = 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(t + 7) | 1;
                let mut out = vec![];
                for _ in 0..n / 4 {
                    let mut v = N::ZERO;
                    for i in 0..4 {
                        s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17;
                        v |= N::from(s64) << (64 * i);
                    }
                    let v = v % pp;
                    if v == N::ZERO { continue; }
                    let x = if v < pp - v { v } else { pp - v };
                    if let Some(why) = diag_walk(x, ws) {
                        out.push(why);
                    }
                }
                out
            })
        }).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let all: Vec<String> = res.into_iter().flatten().collect();
    let mut cats: std::collections::BTreeMap<String, usize> = Default::default();
    for w in &all {
        let key = w.split(": ").nth(1).unwrap_or(w).split(|c: char| c.is_ascii_digit()).next().unwrap_or("").to_string();
        *cats.entry(key).or_default() += 1;
    }
    for (k, c) in &cats {
        eprintln!("  {c:6}  {k}");
    }
    eprintln!("greedyfrog diag rate: {n} walks, {} fail = {:.2e} per walk = {:.2} expected failing shots per 9,024 (2 divisions)",
              all.len(), all.len() as f64 / n as f64, all.len() as f64 / n as f64 * 18048.0);
}

/// Fiat-Shamir tail-nonce scan (the scheme of prefilter-shadow/predict_fast.rs): hash the ops.bin prefix once (all but
/// the 96 tail X ops of mod.rs `append_tail_nonce`), then per nonce feed only the tail, derive the 9,024 shots with a
/// fixed-base table, and run the exact predictor on both divisions of each shot, stopping at the first predicted
/// failure. 4 threads. GREEDYFROG_SCAN_OPS = ops.bin, GREEDYFROG_SCAN_START (default 1), GREEDYFROG_SCAN_MAX (default 20000), GREEDYFROG_SCAN_WANT
/// (clean nonces to report, default 3).
#[test]
fn greedyfrog_nonce_scan() {
    let Ok(path) = std::env::var("GREEDYFROG_SCAN_OPS") else { return; };
    let start: u64 = std::env::var("GREEDYFROG_SCAN_START").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    let max: u64 = std::env::var("GREEDYFROG_SCAN_MAX").ok().and_then(|v| v.parse().ok()).unwrap_or(20000);
    let want: usize = std::env::var("GREEDYFROG_SCAN_WANT").ok().and_then(|v| v.parse().ok()).unwrap_or(3);
    let ops = load_ops(&path);
    let n = ops.len();
    const TAIL: usize = 96;
    let tail = ops[n - TAIL..].to_vec();
    assert!(tail.iter().all(|o| o.kind == crate::circuit::OperationType::X && o.q_target.0 <= 1));
    let mut prefix = sha3::Shake256::default();
    prefix.update(b"quantum_ecc-fiat-shamir-v2");
    prefix.update(&(n as u64).to_le_bytes());
    for op in &ops[..n - TAIL] {
        prefix.update(&[op.kind as u8]);
        prefix.update(&op.q_control2.0.to_le_bytes());
        prefix.update(&op.q_control1.0.to_le_bytes());
        prefix.update(&op.q_target.0.to_le_bytes());
        prefix.update(&op.c_target.0.to_le_bytes());
        prefix.update(&op.c_condition.0.to_le_bytes());
        prefix.update(&op.r_target.0.to_le_bytes());
    }
    drop(ops);
    let c = curve();
    let mut table = Vec::with_capacity(256);
    let mut g = (c.gx, c.gy);
    for _ in 0..256 {
        table.push(g);
        g = c.add(g.0, g.1, g.0, g.1);
    }
    let mulg = |k: U256| {
        let mut r = (U256::ZERO, U256::ZERO);
        for (i, t) in table.iter().enumerate() {
            if k.bit(i) {
                r = c.add(r.0, r.1, t.0, t.1);
            }
        }
        r
    };
    let ws = windows();
    let pp = p();
    let found = std::sync::Mutex::new(Vec::<u64>::new());
    let tried = std::sync::atomic::AtomicU64::new(0);
    let nth: u64 = std::env::var("GREEDYFROG_SCAN_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
    std::thread::scope(|sc| {
        for t in 0..nth {
            let (prefix, tail, ws, found, tried, mulg, c) = (&prefix, &tail, &ws, &found, &tried, &mulg, &c);
            sc.spawn(move || {
                let mut nonce = start + t;
                while nonce < start + max && found.lock().unwrap().len() < want {
                    let mut h = prefix.clone();
                    for (i, op) in tail.iter().enumerate() {
                        let mut op = *op;
                        op.q_target = crate::circuit::QubitId((nonce >> (i / 2)) & 1);
                        h.update(&[op.kind as u8]);
                        h.update(&op.q_control2.0.to_le_bytes());
                        h.update(&op.q_control1.0.to_le_bytes());
                        h.update(&op.q_target.0.to_le_bytes());
                        h.update(&op.c_target.0.to_le_bytes());
                        h.update(&op.c_condition.0.to_le_bytes());
                        h.update(&op.r_target.0.to_le_bytes());
                    }
                    let mut xof = h.finalize_xof();
                    let mut clean = true;
                    for _ in 0..9024 {
                        let mut rb = [[0u8; 32]; 2];
                        XofReader::read(&mut xof, &mut rb[0]);
                        XofReader::read(&mut xof, &mut rb[1]);
                        let tp = mulg(U256::from_le_bytes(rb[0]));
                        let op_ = mulg(U256::from_le_bytes(rb[1]));
                        if tp.0 == op_.0 || (tp.0.is_zero() && tp.1.is_zero()) || (op_.0.is_zero() && op_.1.is_zero()) {
                            continue;
                        }
                        let e = c.add(tp.0, tp.1, op_.0, op_.1);
                        let (tx, ox, ex) = (to_n(tp.0), to_n(op_.0), to_n(e.0));
                        for a in [tx, ex] {
                            let dx = (a + pp - ox) % pp;
                            let xr = if dx < pp - dx { dx } else { pp - dx };
                            if diag_walk(xr, ws).is_some() {
                                clean = false;
                                break;
                            }
                        }
                        if !clean {
                            break;
                        }
                    }
                    let k = tried.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                    if clean {
                        eprintln!("CLEAN nonce {nonce} (after {k} tried)");
                        found.lock().unwrap().push(nonce);
                    } else if k % 50 == 0 {
                        eprintln!("  {k} tried, last {nonce}");
                    }
                    nonce += nth;
                }
            });
        }
    });
    let mut f = found.into_inner().unwrap();
    f.sort();
    eprintln!("greedyfrog nonce scan: {} tried, clean {:?}", tried.into_inner(), f);
}

/// The reflected dx of both divisions of every eval shot of an ops.bin (same Fiat-Shamir stream as eval_circuit).
fn eval_dxs(path: &str) -> Vec<N> {
    let ops = load_ops(path);
    let mut xof = seed(&ops);
    drop(ops);
    let c = curve();
    let mut table = Vec::with_capacity(256);
    let mut g = (c.gx, c.gy);
    for _ in 0..256 {
        table.push(g);
        g = c.add(g.0, g.1, g.0, g.1);
    }
    let mulg = |k: U256| {
        let mut r = (U256::ZERO, U256::ZERO);
        for (i, t) in table.iter().enumerate() {
            if k.bit(i) {
                r = c.add(r.0, r.1, t.0, t.1);
            }
        }
        r
    };
    let pp = p();
    let mut xs = vec![];
    for _ in 0..9024 {
        let mut rb = [[0u8; 32]; 2];
        XofReader::read(&mut xof, &mut rb[0]);
        XofReader::read(&mut xof, &mut rb[1]);
        let tp = mulg(U256::from_le_bytes(rb[0]));
        let op_ = mulg(U256::from_le_bytes(rb[1]));
        if tp.0 == op_.0 || (tp.0.is_zero() && tp.1.is_zero()) || (op_.0.is_zero() && op_.1.is_zero()) {
            continue;
        }
        let e = c.add(tp.0, tp.1, op_.0, op_.1);
        let (tx, ox, ex) = (to_n(tp.0), to_n(op_.0), to_n(e.0));
        for a in [tx, ex] {
            let dx = (a + pp - ox) % pp;
            xs.push(if dx < pp - dx { dx } else { pp - dx });
        }
    }
    xs
}

/// Per walk: (max kt, min kt, max sY, #kt outside 0..32, #sY >= 2, #decoded active slots, receiver-clean, clean with levers)
fn inv_walk(x: N, ws: &[Win]) -> (isize, isize, usize, u64, u64, u64, bool) {
    let mut sp = Spec::new(x);
    let mut ln = Lanes::from_spec(&sp);
    let (mut mk, mut mink, mut ms, mut bk, mut bs, mut nst) = (isize::MIN, isize::MAX, 0usize, 0u64, 0u64, 0u64);
    for w in ws.iter() {
        let act = ln.la != 0;
        sp.fwd();
        let (_d, rho, sw, a1) = ln.fwd();
        if !act {
            continue;
        }
        let (dsw, dr) = emu_decode(&ln, w);
        if dsw != sw || rho_of(dr) != (rho, a1) {
            continue; // an already failing slot is not counted
        }
        let (kt, sy) = emu_lanes(&ln, w);
        nst += 1;
        mk = mk.max(kt);
        mink = mink.min(kt);
        ms = ms.max(sy);
        if !(0..32).contains(&kt) {
            bk += 1;
        }
        if sy > 1 {
            bs += 1;
        }
    }
    (mk, mink, ms, bk, bs, nst, diag_walk(x, ws).is_none())
}

#[derive(Default, Clone, Copy)]
struct InvAcc { walks: u64, clean: u64, slots: u64, kt_max: isize, kt_min: isize, sy_max: usize, kt_bad: u64, sy_bad: u64 }
impl InvAcc {
    fn new() -> InvAcc { InvAcc { kt_max: isize::MIN, kt_min: isize::MAX, ..Default::default() } }
    fn add(&mut self, r: (isize, isize, usize, u64, u64, u64, bool)) {
        self.kt_max = self.kt_max.max(r.0);
        self.kt_min = self.kt_min.min(r.1);
        self.sy_max = self.sy_max.max(r.2);
        self.kt_bad += r.3;
        self.sy_bad += r.4;
        self.slots += r.5;
        self.walks += 1;
        if r.6 { self.clean += 1; }
    }
    fn merge(&mut self, o: &InvAcc) {
        self.kt_max = self.kt_max.max(o.kt_max);
        self.kt_min = self.kt_min.min(o.kt_min);
        self.sy_max = self.sy_max.max(o.sy_max);
        self.kt_bad += o.kt_bad;
        self.sy_bad += o.sy_bad;
        self.slots += o.slots;
        self.walks += o.walks;
        self.clean += o.clean;
    }
    fn print(&self, tag: &str) {
        eprintln!("WALKLANES_INV {tag}: walks {} clean(with active levers) {} decoded_active_slots {} kt_max {} kt_min {} kt_outside_0_32 {} sY_max {} sY_ge2 {}",
                  self.walks, self.clean, self.slots, self.kt_max, self.kt_min, self.kt_bad, self.sy_max, self.sy_bad);
    }
}

/// Walk-lane invariant census (B-WALKLANES): kt and sY (after the un-swap) on every active, correctly decoded inverse
/// slot of GREEDYFROG_INV_WALKS random walks and (GREEDYFROG_INV_OPS) of both divisions of every eval shot of an ops.bin;
/// plus constructed big-quotient inputs.
/// Run: GREEDYFROG_INV_WALKS=1000000 cargo test --release --bin build_circuit walklanes_invariants -- --nocapture
#[test]
fn walklanes_invariants() {
    let n: usize = std::env::var("GREEDYFROG_INV_WALKS").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let ops_path = std::env::var("GREEDYFROG_INV_OPS").ok();
    if n == 0 && ops_path.is_none() {
        return;
    }
    let ws = windows();
    if n > 0 {
        let threads: usize = std::env::var("GREEDYFROG_INV_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(8);
        let accs: Vec<InvAcc> = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..threads).map(|t| {
                let ws = &ws;
                sc.spawn(move || {
                    let mut rng = 0x5eed_0123_4567_89abu64 ^ (0x9e37_79b9_7f4a_7c15u64.wrapping_mul(t as u64 + 1));
                    let mut nx = || { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; rng };
                    let pp = p();
                    let mut a = InvAcc::new();
                    for _ in 0..n / threads {
                        let x = loop {
                            let mut v = N::ZERO;
                            for i in 0..4 {
                                v |= N::from(nx()) << (64 * i);
                            }
                            if v != N::ZERO && v < pp {
                                let w = pp - v;
                                break if w < v { w } else { v };
                            }
                        };
                        a.add(inv_walk(x, ws));
                    }
                    a
                })
            }).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut a = InvAcc::new();
        for o in &accs {
            a.merge(o);
        }
        a.print("random");
    }
    // constructed big-quotient inputs: x ~ p / 2^e, so the first step's quotient is ~2^e
    for e in [20usize, 26, 30, 31, 32, 33, 36, 40, 48, 60] {
        let x = (p() >> e) - N::from(12345u64);
        let r = inv_walk(x, &ws);
        let mut sp = Spec::new(x);
        let mut ln = Lanes::from_spec(&sp);
        sp.fwd();
        let (_d, rho, sw, a1) = ln.fwd();
        let (dsw, dr) = emu_decode(&ln, &ws[0]);
        let (kt, sy) = emu_lanes(&ln, &ws[0]);
        eprintln!("WALKLANES_BIGQ e {e}: slot0 decode_ok {} kt {kt} sY {sy}; walk kt_max {} clean(with active levers) {} first-diag {:?}",
                  dsw == sw && rho_of(dr) == (rho, a1), r.0, r.6, diag_walk(x, &ws));
    }
    if let Some(path) = ops_path {
        let mut a = InvAcc::new();
        for x in eval_dxs(&path) {
            a.add(inv_walk(x, &ws));
        }
        a.print("eval-corpus");
    }
}

/// GREEDYFROG_SHOT_OPS=ops.bin GREEDYFROG_SHOT_IDX=i,j: print both divisions' reflected dx of eval shots i, j and the
/// emulator's verdict per division.
#[test]
fn walklanes_shot_inputs() {
    let Ok(path) = std::env::var("GREEDYFROG_SHOT_OPS") else { return; };
    let idx: Vec<usize> = std::env::var("GREEDYFROG_SHOT_IDX").unwrap().split(',').map(|t| t.trim().parse().unwrap()).collect();
    let ops = load_ops(&path);
    let mut xof = seed(&ops);
    drop(ops);
    let c = curve();
    let pp = p();
    let ws = windows();
    for shot in 0..9024usize {
        let mut rb = [[0u8; 32]; 2];
        XofReader::read(&mut xof, &mut rb[0]);
        XofReader::read(&mut xof, &mut rb[1]);
        if !idx.contains(&shot) { continue; }
        let k1 = U256::from_le_bytes(rb[0]);
        let k2 = U256::from_le_bytes(rb[1]);
        let mut table = vec![];
        let mut g = (c.gx, c.gy);
        for _ in 0..256 { table.push(g); g = c.add(g.0, g.1, g.0, g.1); }
        let mulg = |k: U256| { let mut r = (U256::ZERO, U256::ZERO); for (i, t) in table.iter().enumerate() { if k.bit(i) { r = c.add(r.0, r.1, t.0, t.1); } } r };
        let tp = mulg(k1);
        let op_ = mulg(k2);
        let e = c.add(tp.0, tp.1, op_.0, op_.1);
        let (tx, ox, ex) = (to_n(tp.0), to_n(op_.0), to_n(e.0));
        for (dv, a) in [tx, ex].into_iter().enumerate() {
            let dx = (a + pp - ox) % pp;
            let xr = if dx < pp - dx { dx } else { pp - dx };
            eprintln!("SHOT {shot} div {} x 0x{:x} diag {:?}", dv + 1, xr, diag_walk(xr, &ws));
        }
    }
}
