//! greedyfrog diagnostics against the grader's shots: regenerate eval_circuit's inputs from an ops.bin (same Fiat-Shamir
//! hash), replay both divisions of every shot through the lane model and flag the first slot where the circuit's
//! classical shortcuts (windows, 40-lane top compares, the decode emulated bit for bit, the slot count) disagree with
//! the exact walk.
//! Run: GREEDYFROG_DIAG_OPS=path/to/ops.bin cargo test --release --bin build_circuit greedyfrog_diag -- --nocapture

use super::greedyfrog::{windows, Win, nb, nslots, wc};
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
    let n = if masked { st.lb.min(wc()) } else { wc() };
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
    let win = |ring: &[u8], s: usize| -> Vec<u8> { (0..nb()).map(|i| ring[s + i]).collect() };
    let u = (la + sx) % 512;
    let v = (lb + sy) % 512;
    let mx = W as isize - 1 - u as isize;
    let (wx, wy) = (win(&x, sx), win(&y, sy));
    let gt = {
        let n = if w.mxp >= nb() + 1 { nb() } else { mx.clamp(0, nb() as isize) as usize };
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
        let mut bot = nb(); // rem index of lane NB - 1
        if w.mx < nb() - j + 1 {
            let up = mx as isize - (nb() - j + 1) as isize; // >= 0: mask on from the start
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

/// Replay one division's walk; returns the first disagreement (slot, reason).
fn diag_walk(x: N, ws: &[Win]) -> Option<String> {
    let mut sp = Spec::new(x);
    let mut ln = Lanes::from_spec(&sp);
    for (s, w) in ws.iter().enumerate() {
        let pre = ln.clone();
        let act = pre.la != 0;
        if w.act_const && !act {
            return Some(format!("slot {s}: done in an act-constant slot"));
        }
        let step = act && pre.x[W - 1] == 1;
        sp.fwd();
        let (d, rho, sw, a1) = ln.fwd();
        if super::greedyfrog::lb_bits() < 9 && act {
            let lim = 1usize << (super::greedyfrog::lb_bits() - 1);
            let ok = |v: usize| v >= w.base && v < w.base + lim;
            if !(ok(pre.la) && ok(pre.lb) && (ln.la == 0 || (ok(ln.la) && ok(ln.lb)))) {
                return Some(format!("slot {s}: offset overflow (LA {} LB {} -> {} {}, base {})", pre.la, pre.lb, ln.la, ln.lb, w.base));
            }
            // a masked decode reads u' = NB - mX as a signed lb_bits()-bit value
            let nbv = super::greedyfrog::nb();
            if w.mx < nbv + 1 || w.mxp < nbv + 1 {
                let sl = |ring: &[u8], l: usize| (0..W - l - 1).take_while(|&j| ring[j] == 0).count();
                let (mx_, my_) = (W - 1 - ln.la - sl(&ln.x, ln.la), W - 1 - ln.lb - sl(&ln.y, ln.lb));
                if mx_.max(my_) > nbv + lim {
                    return Some(format!("slot {s}: offset overflow (masked decode, cofactor bits {} {})", mx_, my_));
                }
            }
        }
        // F9's unmasked WC-lane compare (only read when LA == LB after the renormalisation): a tie on the top WC lanes
        // of two different values would decide wrong. Pre-swap rings are the post-state rings swapped back.
        if act && ln.la != 0 {
            let (px, py, pla, plb) = if sw { (&ln.y, &ln.x, ln.lb, ln.la) } else { (&ln.x, &ln.y, ln.la, ln.lb) };
            if pla == plb && plb > 1 && px[W - 1] == 1 && (0..wc()).all(|i| px[W - 1 - i] == py[W - 1 - i]) {
                return Some(format!("slot {s}: F9 top-{} tie", wc()));
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
            let dc = usize::from(top_cmp(&pre, w.lb.0 < wc()));
            if dc != d {
                return Some(format!("slot {s}: top compare d {dc} != {d}"));
            }
        }
        let (dsw, dr) = emu_decode(&ln, w);
        if dsw != sw || rho_of(dr) != (rho, a1) {
            // gf: which limit decided it? rows: all 31 rows fix it; mask: unmasked windows (mx, mxp = NB + 1) fix it
            let ok = |w2: &Win| { let (a, b) = emu_decode(&ln, w2); a == sw && rho_of(b) == (rho, a1) };
            let mut wr = w.clone();
            wr.k = 31.min(nb());
            let mut wm = w.clone();
            wm.mx = 0;
            wm.mxp = 0;
            let mut wb = wr.clone();
            wb.mx = 0;
            wb.mxp = 0;
            let why = if ok(&wr) { "rows" } else if ok(&wm) { "mask" } else if ok(&wb) { "rows+mask" } else { "window bits" };
            return Some(format!("slot {s}: decode/{why} (sw {dsw}, r {dr}) != (sw {sw}, rho {rho}, a1 {a1})"));
        }
    }
    if ln.la != 0 {
        return Some(format!("walk not finished in {} slots", nslots()));
    }
    None
}

/// gf: diag_walk with the rings rebuilt from the integer spec after each slot (Lanes::from_spec) instead of the lane
/// model's slot; greedyfrog_model_lanes_and_decode asserts that the two agree. Same checks, same order, same text.
/// `gf_diag_fast_check` compares the two on GF_FASTCHECK_N walks.
fn diag_walk_fast(x: N, ws: &[Win]) -> Option<String> {
    use super::greedyfrog_model::Slot;
    let mut sp = Spec::new(x);
    let mut ln = Lanes::from_spec(&sp);
    for (s, w) in ws.iter().enumerate() {
        let act = ln.la != 0;
        if w.act_const && !act {
            return Some(format!("slot {s}: done in an act-constant slot"));
        }
        let step = act && ln.x[W - 1] == 1;
        let (d, rho, sw, a1) = match sp.fwd() {
            Slot::Done => (0, 0, false, false),
            Slot::Stall { rho, sw } => (0, rho, sw, false),
            Slot::Step { d, rho, sw, .. } => (d, rho, sw, true),
        };
        if !act {
            ln.la = 0;
            continue;
        }
        let pre = std::mem::replace(&mut ln, Lanes::from_spec(&sp));
        if super::greedyfrog::lb_bits() < 9 && act {
            let lim = 1usize << (super::greedyfrog::lb_bits() - 1);
            let ok = |v: usize| v >= w.base && v < w.base + lim;
            if !(ok(pre.la) && ok(pre.lb) && (ln.la == 0 || (ok(ln.la) && ok(ln.lb)))) {
                return Some(format!("slot {s}: offset overflow (LA {} LB {} -> {} {}, base {})", pre.la, pre.lb, ln.la, ln.lb, w.base));
            }
            // a masked decode reads u' = NB - mX as a signed lb_bits()-bit value
            let nbv = super::greedyfrog::nb();
            if w.mx < nbv + 1 || w.mxp < nbv + 1 {
                let sl = |ring: &[u8], l: usize| (0..W - l - 1).take_while(|&j| ring[j] == 0).count();
                let (mx_, my_) = (W - 1 - ln.la - sl(&ln.x, ln.la), W - 1 - ln.lb - sl(&ln.y, ln.lb));
                if mx_.max(my_) > nbv + lim {
                    return Some(format!("slot {s}: offset overflow (masked decode, cofactor bits {} {})", mx_, my_));
                }
            }
        }
        if ln.la != 0 {
            let (px, py, pla, plb) = if sw { (&ln.y, &ln.x, ln.lb, ln.la) } else { (&ln.x, &ln.y, ln.la, ln.lb) };
            if pla == plb && plb > 1 && px[W - 1] == 1 && (0..wc()).all(|i| px[W - 1 - i] == py[W - 1 - i]) {
                return Some(format!("slot {s}: F9 top-{} tie", wc()));
            }
        }
        if step {
            if pre.lb < w.lb.0 || pre.lb > w.lb.1 {
                return Some(format!("slot {s}: LB {} outside window {:?}", pre.lb, w.lb));
            }
            if pre.la - d < w.lad.0 || pre.la - d > w.lad.1 {
                return Some(format!("slot {s}: LA-d {} outside window {:?}", pre.la - d, w.lad));
            }
            let dc = usize::from(top_cmp(&pre, w.lb.0 < wc()));
            if dc != d {
                return Some(format!("slot {s}: top compare d {dc} != {d}"));
            }
        }
        let (dsw, dr) = emu_decode(&ln, w);
        if dsw != sw || rho_of(dr) != (rho, a1) {
            let ok = |w2: &Win| { let (a, b) = emu_decode(&ln, w2); a == sw && rho_of(b) == (rho, a1) };
            let mut wr = w.clone();
            wr.k = 31.min(nb());
            let mut wm = w.clone();
            wm.mx = 0;
            wm.mxp = 0;
            let mut wb = wr.clone();
            wb.mx = 0;
            wb.mxp = 0;
            let why = if ok(&wr) { "rows" } else if ok(&wm) { "mask" } else if ok(&wb) { "rows+mask" } else { "window bits" };
            return Some(format!("slot {s}: decode/{why} (sw {dsw}, r {dr}) != (sw {sw}, rho {rho}, a1 {a1})"));
        }
    }
    if ln.la != 0 {
        return Some(format!("walk not finished in {} slots", nslots()));
    }
    None
}

/// gf: the fast diag must return exactly what diag_walk returns (GF_FASTCHECK_N walks of the diag_rate streams, plus
/// GF_FASTCHECK_NARROW=1 to run it on a deliberately narrow setting chosen by the caller's GF_* knobs).
#[test]
fn gf_diag_fast_check() {
    let Ok(n) = std::env::var("GF_FASTCHECK_N").map(|v| v.parse::<usize>().unwrap()) else { return; };
    let seed_x: u64 = std::env::var("GF_DIAG_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let ws = windows();
    let pp = p();
    let (mut same, mut fails) = (0usize, 0usize);
    for t in 0..4u64 {
        let mut s64 = (0x9e37_79b9_7f4a_7c15u64.wrapping_mul(t + 7) ^ seed_x) | 1;
        for _ in 0..n / 4 {
            let mut v = N::ZERO;
            for i in 0..4 {
                s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17;
                v |= N::from(s64) << (64 * i);
            }
            let v = v % pp;
            if v == N::ZERO { continue; }
            let x = if v < pp - v { v } else { pp - v };
            let a = diag_walk(x, &ws);
            let b = diag_walk_fast(x, &ws);
            assert_eq!(a, b, "fast diag differs");
            same += 1;
            fails += a.is_some() as usize;
        }
    }
    eprintln!("GF_FASTCHECK {{\"walks\": {same}, \"identical\": {same}, \"failing\": {fails}}}");
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
    // gf: the 4 seeded streams run on GF_DIAG_THREADS OS threads (default 4); GF_DIAG_SEED is XORed into each seed
    let nthreads: u64 = std::env::var("GF_DIAG_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(4).clamp(1, 4);
    let seed_x: u64 = std::env::var("GF_DIAG_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let fast = std::env::var("GF_DIAG_FAST").is_ok();
    let res: Vec<Vec<String>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..nthreads).map(|th| {
            let ws = &ws;
            sc.spawn(move || {
              let mut out = vec![];
              for t in (th..4u64).step_by(nthreads as usize) {
                let mut s64 = (0x9e37_79b9_7f4a_7c15u64.wrapping_mul(t + 7) ^ seed_x) | 1;
                for _ in 0..n / 4 {
                    let mut v = N::ZERO;
                    for i in 0..4 {
                        s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17;
                        v |= N::from(s64) << (64 * i);
                    }
                    let v = v % pp;
                    if v == N::ZERO { continue; }
                    let x = if v < pp - v { v } else { pp - v };
                    if let Some(why) = if fast { diag_walk_fast(x, ws) } else { diag_walk(x, ws) } {
                        out.push(why);
                    }
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
    let coarse = |w: &str| -> &'static str {
        let tail = w.split(": ").nth(1).unwrap_or(w);
        for (p, k) in [("walk not finished", "slots"), ("LB ", "lb_window"), ("LA-d ", "lad_window"),
                       ("top compare", "top_compare"), ("F9 ", "f9_tie"), ("decode/rows+mask", "decode_rows_mask"),
                       ("decode/rows", "decode_rows"), ("decode/mask", "decode_mask"),
                       ("decode/window bits", "decode_window_bits"),
                       ("done in an act-constant", "early_finish"), ("offset overflow", "offset_overflow")] {
            if tail.starts_with(p) || w.starts_with(p) { return k; }
        }
        "other"
    };
    let mut cc: std::collections::BTreeMap<&'static str, usize> = Default::default();
    for w in &all { *cc.entry(coarse(w)).or_default() += 1; }
    let cj: Vec<String> = cc.iter().map(|(k, c)| format!("\"{k}\": {c}")).collect();
    eprintln!("GF_RATE {{\"fast\": {fast}, \"walks\": {n}, \"fail\": {}, \"seed_x\": {seed_x}, \"wc\": {}, \"margin\": {}, \"nslots\": {}, \"nb\": {}, \"krows\": {}, \"kmin\": {}, \"cats\": {{{}}}}}",
              all.len(), wc(), super::greedyfrog::margin(), nslots(), nb(), super::greedyfrog::krows(),
              super::greedyfrog::kmin(), cj.join(", "));
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
    std::thread::scope(|sc| {
        for t in 0..4u64 {
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
                    nonce += 4;
                }
            });
        }
    });
    let mut f = found.into_inner().unwrap();
    f.sort();
    eprintln!("greedyfrog nonce scan: {} tried, clean {:?}", tried.into_inner(), f);
}

/// gf: slots each walk needs (integer spec only, the 4 seeded streams of greedyfrog_diag_rate, GF_DIAG_SEED applied).
/// Prints GF_SLOTS {walks, need: {slots: walks needing exactly that many}}; a walk fails the slot count iff it needs
/// more than NSLOTS slots.
#[test]
fn gf_slot_hist() {
    let Ok(n) = std::env::var("GF_SLOTHIST_N").map(|v| v.parse::<usize>().unwrap()) else { return; };
    let seed_x: u64 = std::env::var("GF_DIAG_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let pp = p();
    let mut hist = vec![0u64; 1024];
    for t in 0..4u64 {
        let mut s64 = (0x9e37_79b9_7f4a_7c15u64.wrapping_mul(t + 7) ^ seed_x) | 1;
        for _ in 0..n / 4 {
            let mut v = N::ZERO;
            for i in 0..4 {
                s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17;
                v |= N::from(s64) << (64 * i);
            }
            let v = v % pp;
            if v == N::ZERO { continue; }
            let x = if v < pp - v { v } else { pp - v };
            let mut sp = Spec::new(x);
            let mut s = 0usize;
            while sp.la != 0 {
                sp.fwd();
                s += 1;
            }
            hist[s.min(1023)] += 1;
        }
    }
    let parts: Vec<String> = (0..1024).filter(|&i| hist[i] > 0).map(|i| format!("\"{i}\": {}", hist[i])).collect();
    eprintln!("GF_SLOTS {{\"walks\": {n}, \"seed_x\": {seed_x}, \"need\": {{{}}}}}", parts.join(", "));
}

/// gf: per-walk requirements of the integer walk against the raw envelope (no margin), from the integer spec only:
/// slots needed; the LB and LA-d window excess (the walk fails the LB window iff its excess > MARGIN); and the row
/// capacity it needs (it fails the rows iff need > KROWS, for the current GF_KMIN). Slot 0 (4 rows, fixed) is counted
/// apart. One pass prices every NSLOTS, MARGIN (for the LB and LA-d windows) and KROWS. The decode's window bits, its
/// masks and the WC compares need the rings: use greedyfrog_diag_rate for them. GF_REQ_N walks, the diag_rate streams.
#[test]
fn gf_requirements() {
    use super::greedyfrog::{env_text, kmin};
    use super::greedyfrog_model::{bl, Slot};
    let Ok(n) = std::env::var("GF_REQ_N").map(|v| v.parse::<usize>().unwrap()) else { return; };
    let seed_x: u64 = std::env::var("GF_DIAG_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    // raw envelope rows: (n_active, lb_min, lb_max, lad_min, lad_max)
    let mut env: Vec<[isize; 5]> = vec![];
    let mut walks0 = 0.0;
    for line in env_text().lines().filter(|l| !l.starts_with('#')) {
        let c: Vec<isize> = line.split_whitespace().map(|t| t.parse().unwrap()).collect();
        if c[0] == 0 { walks0 = c[1] as f64; }
        env.push([c[1], c[2], c[3], c[4], c[5]]);
    }
    let row = |s: usize| env[s.min(env.len() - 1)];
    let off = |s: usize| -> isize { let f = row(s)[0] as f64 / walks0; (1.0 / f).log2().floor() as isize };
    let km = kmin() as isize;
    let pp = p();
    let mut h_slots = vec![0u64; 1024];
    let mut h_lb = vec![0u64; 300];
    let mut h_lad = vec![0u64; 300];
    let mut h_rows = vec![0u64; 300];
    let mut slot0_rows_fail = 0u64;
    let mut walks = 0u64;
    let mut tails: Vec<String> = vec![];
    for t in 0..4u64 {
        let mut s64 = (0x9e37_79b9_7f4a_7c15u64.wrapping_mul(t + 7) ^ seed_x) | 1;
        for _ in 0..n / 4 {
            let mut v = N::ZERO;
            for i in 0..4 {
                s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17;
                v |= N::from(s64) << (64 * i);
            }
            let v = v % pp;
            if v == N::ZERO { continue; }
            let x = if v < pp - v { v } else { pp - v };
            walks += 1;
            let mut sp = Spec::new(x);
            let (mut s, mut lbx, mut ladx, mut need) = (0usize, 0isize, 0isize, 0isize);
            let mut last_ep = 0usize;
            let mut s0fail = false;
            while sp.la != 0 {
                let (la, lb) = (sp.la as isize, sp.lb as isize);
                let slot = sp.fwd();
                let e = row(s);
                let sw = match slot {
                    Slot::Step { ep, d, sw, .. } => {
                        last_ep = ep;
                        lbx = lbx.max(e[1] - lb).max(lb - e[2]);
                        let lad = la - d as isize;
                        ladx = ladx.max(e[3] - lad).max(lad - e[4]);
                        sw
                    }
                    Slot::Stall { sw, .. } => sw,
                    Slot::Done => unreachable!(),
                };
                let (tau, tbu) = if sw { (sp.tb, sp.ta) } else { (sp.ta, sp.tb) };
                let rows = bl(&tau) as isize - bl(&tbu) as isize - last_ep as isize + 1;
                if s == 0 {
                    s0fail |= rows > 4;
                } else if rows > km {
                    need = need.max(rows + off(s));
                }
                s += 1;
            }
            if s > 248 || lbx > 0 || ladx > 0 || need > 18 || s0fail {
                tails.push(format!("[{s}, {lbx}, {ladx}, {need}, {}]", s0fail as u8));
            }
            h_slots[s.min(1023)] += 1;
            h_lb[lbx.clamp(0, 299) as usize] += 1;
            h_lad[ladx.clamp(0, 299) as usize] += 1;
            h_rows[need.clamp(0, 299) as usize] += 1;
            slot0_rows_fail += s0fail as u64;
        }
    }
    let js = |h: &[u64]| -> String {
        (0..h.len()).filter(|&i| h[i] > 0).map(|i| format!("\"{i}\": {}", h[i])).collect::<Vec<_>>().join(", ")
    };
    eprintln!("GF_REQ {{\"walks\": {walks}, \"seed_x\": {seed_x}, \"kmin\": {km}, \"slot0_rows_fail\": {slot0_rows_fail}, \"slots\": {{{}}}, \"lb_excess\": {{{}}}, \"lad_excess\": {{{}}}, \"krows_need\": {{{}}}}}",
              js(&h_slots), js(&h_lb), js(&h_lad), js(&h_rows));
    // per-walk tails [slots, lb_excess, lad_excess, krows_need, slot0_fail] of every walk with slots > 248, any window
    // excess, krows_need > 18 or a slot-0 row failure (the union of failures for any setting is computed from these)
    if let Ok(path) = std::env::var("GF_REQ_OUT") {
        std::fs::write(&path, format!("{{\"walks\": {walks}, \"seed_x\": {seed_x}, \"kmin\": {km}, \"tails\": [{}]}}\n", tails.join(", "))).unwrap();
    }
}
