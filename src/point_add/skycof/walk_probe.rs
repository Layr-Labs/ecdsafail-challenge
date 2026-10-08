//! Research probe (`SKYCOF_RESEARCH=1 SKYCOF_PROBE=walk`): the forward walk and the walk back alone,
//! simulated on random `d`. Reports the parked `s` against `-+2^R / d`, garbage and phase after the
//! forward walk, and `d` / garbage / phase after the walk back.
use super::walk;
use crate::circuit::{Op, OperationType as K, QubitId as Q, NO_BIT};
use crate::point_add::builder::Builder;
use crate::point_add::skycof_mm::model::U512;
use crate::point_add::N;
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};
use sha3::Shake256;
use std::collections::HashSet;

/// Expected Toffoli weight used by the trusted scorer: a Toffoli under `d`
/// nested classical conditions contributes `2^-d`.
fn expected_t(ops: &[Op]) -> f64 {
    let mut depth = 0i32;
    let mut total = 0.0;
    for op in ops {
        match op.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth -= 1,
            K::CCX | K::CCZ => {
                let d = depth + i32::from(op.c_condition != NO_BIT);
                total += 0.5f64.powi(d);
            }
            _ => {}
        }
    }
    assert_eq!(depth, 0, "walk probe left an unbalanced condition stack");
    total
}

fn rng_next(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn set(sim: &mut Simulator<sha3::Shake256Reader>, r: &[Q], v: U512, shot: usize) {
    for (i, &q) in r.iter().enumerate() {
        let w = sim.qubit_mut(q);
        if v.bit(i) {
            *w |= 1u64 << shot;
        } else {
            *w &= !(1u64 << shot);
        }
    }
}

fn get(sim: &Simulator<sha3::Shake256Reader>, r: &[Q], shot: usize) -> U512 {
    let mut v = U512::ZERO;
    for (i, &q) in r.iter().enumerate() {
        if (sim.qubit(q) >> shot) & 1 == 1 {
            v.set_bit(i, true);
        }
    }
    v
}

/// Research specification values use signed integers embedded in a 512-bit
/// two's-complement word. Cut-200 rails/coefficient products fit this width.
fn get_signed(sim: &Simulator<sha3::Shake256Reader>, r: &[Q], shot: usize) -> U512 {
    let v = get(sim, r, shot);
    if v.bit(r.len() - 1) {
        v | (U512::MAX << r.len())
    } else {
        v
    }
}

fn canonical_prefix_spec(d: U512, p: U512, cut: usize) -> [U512; 4] {
    let (mut x, mut y, mut a, mut b) = (d + p, d, U512::from(1), U512::MAX);
    for _ in 0..cut {
        if x.bit(0) {
            std::mem::swap(&mut x, &mut y);
            std::mem::swap(&mut a, &mut b);
        }
        let half: U512 = (x >> 1usize)
            | if x.bit(511) {
                U512::from(1) << 511usize
            } else {
                U512::ZERO
            };
        if half.bit(511) == y.bit(511) {
            y = y.wrapping_sub(half);
            a = (a << 1usize).wrapping_add(b);
        } else {
            y = y.wrapping_add(half);
            a = (a << 1usize).wrapping_sub(b);
        }
        x = half;
    }
    [x, y, a, b]
}

// Research-only exact cut200 seam. Kept here so it can consume the real
// ActiveWalk owners without changing production dispatch.
fn seam_fredkin(c: &mut Builder, g: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(g, a, b);
    c.cx(b, a);
}

fn seam_dirty_mcx(c: &mut Builder, controls: &[Q], target: Q, dirty: &[Q]) {
    match controls.len() {
        0 => c.x(target),
        1 => c.cx(controls[0], target),
        2 => c.ccx(controls[0], controls[1], target),
        m => {
            let d = &dirty[..m - 2];
            for bottom in [true, false] {
                if bottom {
                    c.ccx(controls[0], controls[1], d[0]);
                }
                for i in 1..d.len() {
                    c.ccx(d[i - 1], controls[i + 1], d[i]);
                }
                c.ccx(*d.last().unwrap(), *controls.last().unwrap(), target);
                for i in (1..d.len()).rev() {
                    c.ccx(d[i - 1], controls[i + 1], d[i]);
                }
                if bottom {
                    c.ccx(controls[0], controls[1], d[0]);
                }
            }
        }
    }
}

fn seam_overflow(c: &mut Builder, groups: &[(&[Q], Q)], flag: Q, dirty: &[Q]) {
    let mut controls = Vec::new();
    c.x(flag);
    for &(bits, sign) in groups {
        for &q in bits {
            c.cx(sign, q);
            c.x(q);
            controls.push(q);
        }
    }
    seam_dirty_mcx(c, &controls, flag, dirty);
    for &(bits, sign) in groups.iter().rev() {
        for &q in bits.iter().rev() {
            c.x(q);
            c.cx(sign, q);
        }
    }
}

fn cut200_gauge(c: &mut Builder, st: &mut walk::ActiveWalk, dirty: &[Q], inverse: bool) {
    let typ = st.typ.expect("cut200 gauge typ");
    if !inverse {
        while st.cof.s.len() < 168 {
            st.cof.s.push(c.alloc_qubit());
        }
        while st.cof.r.len() < 168 {
            st.cof.r.push(c.alloc_qubit());
        }
        c.x_all(&st.cof.s);
        super::adder::add(c, None, &st.cof.r, &st.cof.s, None, Some(999));
        c.x_all(&st.cof.s);
        c.x(typ);
        for (&a, &b) in st.cof.s.iter().zip(&st.cof.r) {
            seam_fredkin(c, typ, a, b);
        }
        c.x(typ);
        for (flag, word) in [
            (*st.rails.r1.last().unwrap(), &st.cof.s),
            (*st.rails.r2.last().unwrap(), &st.cof.r),
        ] {
            c.cx_all(flag, word);
            crate::point_add::lowroom::cinc_dirty(c, flag, word, &dirty[..word.len() + 1]);
        }
    } else {
        for (flag, word) in [
            (*st.rails.r2.last().unwrap(), &st.cof.r),
            (*st.rails.r1.last().unwrap(), &st.cof.s),
        ] {
            c.cx_all(flag, word);
            crate::point_add::lowroom::cinc_dirty(c, flag, word, &dirty[..word.len() + 1]);
        }
        c.x(typ);
        for (&a, &b) in st.cof.s.iter().zip(&st.cof.r).rev() {
            seam_fredkin(c, typ, a, b);
        }
        c.x(typ);
        super::adder::add(c, None, &st.cof.r, &st.cof.s, None, Some(999));
        for _ in 0..2 {
            c.free(st.cof.s.pop().unwrap());
            c.free(st.cof.r.pop().unwrap());
        }
    }
}

fn cut200_pack(c: &mut Builder, st: &mut walk::ActiveWalk, dirty: &[Q], inverse: bool) {
    let (x, y, a, b) = (&st.rails.r1, &st.rails.r2, &st.cof.s, &st.cof.r);
    let signs = (
        *x.last().unwrap(),
        *y.last().unwrap(),
        *a.last().unwrap(),
        *b.last().unwrap(),
    );
    let header = [a[0], b[0], x[138], y[138], a[166], b[166]];
    let (low, high) = (a[0], b[0]);
    if !inverse {
        c.x(low);
        c.x(high);
        seam_overflow(
            c,
            &[(&a[153..167], signs.2), (&b[153..167], signs.3)],
            low,
            dirty,
        );
        seam_overflow(
            c,
            &[(&x[130..138], signs.0), (&y[130..138], signs.1)],
            high,
            dirty,
        );
        c.cx(signs.0, x[138]);
        c.cx(signs.1, y[138]);
        c.cx(signs.2, a[166]);
        c.cx(signs.3, b[166]);
        c.cx(high, header[3]);
        c.cx(header[3], high);
        c.x(high);
        c.cx(low, high);
        c.cx(low, header[2]);
        c.cx(low, header[4]);
        c.x(header[5]);
        c.cx(low, header[5]);
        for (rail, coef, rs, cs) in [(x, a, signs.0, signs.2), (y, b, signs.1, signs.3)] {
            for p in 117..130 {
                let d = coef[282 - p];
                c.ccx(low, rs, rail[p]);
                c.ccx(low, d, rail[p]);
                c.cx(cs, d);
                c.ccx(low, cs, d);
                c.ccx(low, rail[p], d);
            }
            c.x(header[3]);
            for p in 130..138 {
                let d = coef[282 - p];
                c.ccx(header[3], rs, rail[p]);
                c.ccx(header[3], d, rail[p]);
                c.cx(cs, d);
                c.ccx(header[3], cs, d);
                c.ccx(header[3], rail[p], d);
            }
            c.x(header[3]);
        }
        let newh = c.alloc_qubits(5);
        st.h.wires
            .extend(a[145..166].iter().chain(&b[145..166]).copied());
        st.h.wires.extend(newh);
    } else {
        let newh = st.h.wires.split_off(155);
        st.h.wires.truncate(113);
        c.free_vec(&newh);
        for (rail, coef, rs, cs) in [(y, b, signs.1, signs.3), (x, a, signs.0, signs.2)] {
            c.x(header[3]);
            for p in (130..138).rev() {
                let d = coef[282 - p];
                c.ccx(header[3], rail[p], d);
                c.ccx(header[3], cs, d);
                c.cx(cs, d);
                c.ccx(header[3], d, rail[p]);
                c.ccx(header[3], rs, rail[p]);
            }
            c.x(header[3]);
            for p in (117..130).rev() {
                let d = coef[282 - p];
                c.ccx(low, rail[p], d);
                c.ccx(low, cs, d);
                c.cx(cs, d);
                c.ccx(low, d, rail[p]);
                c.ccx(low, rs, rail[p]);
            }
        }
        c.cx(low, header[5]);
        c.x(header[5]);
        c.cx(low, header[4]);
        c.cx(low, header[2]);
        c.cx(low, high);
        c.x(high);
        c.cx(header[3], high);
        c.cx(high, header[3]);
        c.cx(signs.3, b[166]);
        c.cx(signs.2, a[166]);
        c.cx(signs.1, y[138]);
        c.cx(signs.0, x[138]);
        seam_overflow(
            c,
            &[(&x[130..138], signs.0), (&y[130..138], signs.1)],
            high,
            dirty,
        );
        seam_overflow(
            c,
            &[(&a[153..167], signs.2), (&b[153..167], signs.3)],
            low,
            dirty,
        );
        c.x(high);
        c.x(low);
    }
}

fn kaliski_values_at(mut u: U512, p: U512, cut: usize) -> (U512, U512) {
    let mut v = p;
    for _ in 0..cut {
        if u.is_zero() {
            break;
        }
        if !u.bit(0) {
            u >>= 1usize;
        } else if u >= v {
            u = (u - v) >> 1usize;
        } else {
            (u, v) = ((v - u) >> 1usize, u);
        }
    }
    (u, v)
}

// ─── classical walk model (rails drive the letters, as in tick.rs) ─────────────────────────────

fn negu(x: U512) -> bool {
    x.bit(511)
}
fn sar1(x: U512) -> U512 {
    let y = x >> 1usize;
    if negu(x) {
        y | (U512::from(1u64) << 511usize)
    } else {
        y
    }
}
fn bitsu(x: U512) -> usize {
    512 - x.leading_zeros()
}
fn swu(x: U512) -> usize {
    if negu(x) {
        bitsu(!x) + 1
    } else {
        bitsu(x) + 1
    }
}

/// Classical walk of `d` against the envelope and the walk's assumptions. Returns the list of violations
/// (empty = the circuit walk is exact for this `d`).
pub fn classify(d: U512, p: U512) -> Vec<String> {
    use super::decoder::model::decide;
    let pp = super::pointadd::params();
    let env = super::pointadd::envelope();
    let r = pp.walk.r;
    let clamp = walk::CLAMP;
    let (mut r1, mut r2, mut s, mut rr, mut typ) = (d + p, d, U512::ZERO, U512::from(1u64), false);
    let mut out = Vec::new();
    let mut pushes = 0usize;
    let mut hbits: Vec<bool> = Vec::new();
    let mut park: Option<usize> = None;
    let topj = (U512::from(1u64) << clamp) - (U512::from(1u64) << (clamp - pp.walk.park_j));
    for t in 0..r {
        let w = env.widths(t);
        let pre = swu(r1).max(swu(r2));
        if pre > w.wsw {
            out.push(format!("t{t}:rail_swap {pre}>{}", w.wsw));
        }
        let c = r1.bit(0);
        let (mut a, mut b) = (r1, r2);
        if c {
            std::mem::swap(&mut a, &mut b);
        }
        let h = sar1(a);
        let agree = negu(h) == negu(b);
        let b2 = if agree {
            b.wrapping_sub(h)
        } else {
            b.wrapping_add(h)
        };
        let ad = swu(h).max(swu(b)).max(swu(b2));
        if ad > w.wad {
            out.push(format!("t{t}:rail_add {ad}>{}", w.wad));
        }
        let post_r1 = swu(h);
        if post_r1 > w.post_r1 {
            out.push(format!("t{t}:post_r1 {post_r1}>{}", w.post_r1));
        }
        let post_r2 = swu(b2);
        if post_r2 > w.post_r2 {
            out.push(format!("t{t}:post_r2 {post_r2}>{}", w.post_r2));
        }
        let isc = negu(b2) != negu(b);
        typ ^= c;
        if isc {
            std::mem::swap(&mut s, &mut rr);
        }
        if !typ {
            rr += s;
        }
        let sop = s;
        s <<= 1usize;
        if isc != (s.bit(1) && !typ) {
            out.push(format!("t{t}:isc_erase"));
        }
        let cofn = bitsu(rr).max(bitsu(sop) + 1);
        if cofn > w.ecof && !(w.ecof == clamp && cofn == clamp + 1 && bitsu(rr) <= clamp) {
            out.push(format!("t{t}:cof {cofn}>{}", w.ecof));
        }
        let parked_now = rr == p;
        if parked_now && park.is_none() {
            park = Some(t);
        }
        if bitsu(s) > clamp {
            if park.is_none() {
                out.push(format!("t{t}:fold_before_park"));
            }
            s -= p;
            if bitsu(s) > clamp {
                out.push(format!("t{t}:fold_overflow"));
            }
        }
        r1 = h;
        r2 = b2;
        // park test (top park_j bits of r) on clamp ticks; below the clamp the walk must not park
        if w.ecof == clamp {
            let z = rr & topj == topj;
            if z != parked_now {
                out.push(format!("t{t}:parktest z={z} parked={parked_now}"));
            }
        } else if parked_now {
            out.push(format!("t{t}:park_below_clamp"));
        }
        // Decoder history has the public width even on the park/post-park
        // branch; only non-parked ambiguous letters shift into it.
        if t >= 1 {
            hbits.resize(env.h[t], false);
        }
        // decoder push (t >= 1, not parked)
        if t >= 1 && !parked_now {
            let sl = s.as_limbs();
            let rl = rr.as_limbs();
            let (_, amb) = decide(sl, rl, env.cof[t], pp.walk.w_dec, true);
            if amb {
                pushes += 1;
                let letter_a = typ;
                if hbits.is_empty() {
                    if letter_a {
                        out.push(format!("t{t}:Hbit dropped=1 cap=0"));
                    }
                } else {
                    if *hbits.last().unwrap() {
                        out.push(format!("t{t}:Hbit dropped=1 cap={}", hbits.len()));
                    }
                    for i in (1..hbits.len()).rev() {
                        hbits[i] = hbits[i - 1];
                    }
                    hbits[0] = letter_a;
                }
            }
            if pushes > env.h[t] && super::pointadd::knob_flag("SKYCOF_CLASSIFY_COUNT_H") {
                out.push(format!("t{t}:Hcount {pushes}>{}", env.h[t]));
            }
            // letter consistency: decoder certain-A must be A, C iff bit1(s)
            let letter_a = typ;
            if !amb && !s.bit(1) && !letter_a {
                out.push(format!("t{t}:decoder_certainA_wrong"));
            }
        }
    }
    if !(r1.is_zero() && r2 == U512::from(1u64)) {
        out.push(format!("rails_not_parked park={park:?}"));
    }
    match park {
        None => out.push("no_park".into()),
        Some(k) => {
            if r - 1 - k > (1 << pp.walk.odo_bits) - 1 {
                out.push(format!("odo_overflow park={k}"));
            }
        }
    }
    if out.len() > 6 {
        out.truncate(6);
        out.push("...".into());
    }
    out
}

pub fn run_classify() {
    let p = U512::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    if let Some(v) = super::pointadd::knob("SKYCOF_PROBE_D") {
        for h in v.split(',').filter(|s| !s.is_empty()) {
            let mut d = U512::ZERO;
            for ch in h.trim().trim_start_matches("0x").chars() {
                d = (d << 4) | U512::from(ch.to_digit(16).unwrap() as u64);
            }
            eprintln!("CLASSIFY d={h} -> {:?}", classify(d, p));
        }
    }
    let n: usize = super::pointadd::knob("SKYCOF_PROBE_N")
        .map(|v| v.parse().unwrap())
        .unwrap_or(0);
    if n > 0 {
        let mut seed: u64 = super::pointadd::knob("SKYCOF_PROBE_SEED")
            .map(|v| v.parse().unwrap())
            .unwrap_or(0xC1A55);
        let mut cats: std::collections::BTreeMap<String, usize> = Default::default();
        let mut bad = 0usize;
        for _ in 0..n {
            let mut v = U512::ZERO;
            for i in 0..4 {
                v |= U512::from(rng_next(&mut seed)) << (64 * i);
            }
            let d = v.reduce_mod(p);
            if d.is_zero() {
                continue;
            }
            let o = classify(d, p);
            if !o.is_empty() {
                bad += 1;
                let k = o[0]
                    .split_once(':')
                    .map(|(_, b)| b.split(' ').next().unwrap().to_string())
                    .unwrap_or(o[0].clone());
                *cats.entry(k).or_default() += 1;
            }
        }
        eprintln!("CLASSIFY random walks={n} bad={bad} rate={:.2e} per-corpus(18048 walks)={:.2} first-violation: {cats:?}", bad as f64 / n as f64, bad as f64 / n as f64 * 18048.0);
    }
}

/// `SKYCOF_PROBE=walktrace SKYCOF_PROBE_D=...`: compare every reverse tick state with the forward state.
pub fn run_trace() {
    let pp = super::pointadd::params();
    let env = super::pointadd::envelope();
    let p = U512::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    walk::SNAPS.with(|s| *s.borrow_mut() = Some(Vec::new()));
    let mut b = Builder::new();
    let d = b.alloc_qubits(N);
    let _pass = b.alloc_qubits(N);
    let pk = walk::forward(&mut b, &pp.walk, env, &d);
    let _ = walk::backward(&mut b, &pp.walk, env, pk);
    let tail = b.take_ops();
    let snaps = walk::SNAPS.with(|s| s.borrow_mut().take().unwrap());
    if super::pointadd::knob_flag("SKYCOF_PROBE_SNAP_COSTS") {
        for (tag, ops, regs) in &snaps {
            let widths: Vec<usize> = regs.iter().map(Vec::len).collect();
            eprintln!(
                "WALK_SNAP_COST tag={tag} expected_T={:.3} native_T={} ops={} widths={widths:?}",
                expected_t(ops),
                ops.iter()
                    .filter(|op| matches!(op.kind, K::CCX | K::CCZ))
                    .count(),
                ops.len(),
            );
        }
        eprintln!(
            "WALK_SNAP_COST tag=tail expected_T={:.3} native_T={} ops={}",
            expected_t(&tail),
            tail.iter()
                .filter(|op| matches!(op.kind, K::CCX | K::CCZ))
                .count(),
            tail.len(),
        );
    }
    let (nq, nb) = b.i13_dims();
    let given: Vec<U512> = super::pointadd::knob("SKYCOF_PROBE_D")
        .unwrap()
        .split(',')
        .filter(|s| !s.is_empty())
        .map(|h| {
            let mut d = U512::ZERO;
            for ch in h.trim().trim_start_matches("0x").chars() {
                d = (d << 4) | U512::from(ch.to_digit(16).unwrap() as u64);
            }
            d
        })
        .collect();
    let mut rd = {
        let mut h = Shake256::default();
        h.update(b"skycof-walk-trace");
        h.finalize_xof()
    };
    let mut sim = Simulator::new(nq, nb + 1, &mut rd);
    sim.clear_for_shot();
    for (j, &dv) in given.iter().enumerate() {
        set(&mut sim, &d, dv.reduce_mod(p), j);
    }
    let mut fwd: std::collections::HashMap<String, Vec<Vec<U512>>> = Default::default();
    let mut first_bad: Vec<Option<String>> = vec![None; given.len()];
    for (tag, ops, regs) in &snaps {
        sim.apply_iter(ops.iter());
        let vals: Vec<Vec<U512>> = (0..given.len())
            .map(|j| regs.iter().map(|r| get(&sim, r, j)).collect())
            .collect();
        if let Some(t) = tag.strip_prefix('F') {
            fwd.insert(t.to_string(), vals);
        } else if let Some(t) = tag.strip_prefix('B') {
            let f = &fwd[t];
            for j in 0..given.len() {
                if first_bad[j].is_some() {
                    continue;
                }
                let names = ["r1", "r2", "s", "r", "H", "odo", "typ"];
                let bad: Vec<String> = (0..7)
                    .filter(|&k| {
                        f[j][k] != vals[j][k]
                            || (k != 4
                                && regs[k].len()
                                    != snaps.iter().find(|x| x.0 == format!("F{t}")).unwrap().2[k]
                                        .len())
                    })
                    .map(|k| format!("{}(f={:#x} b={:#x})", names[k], f[j][k], vals[j][k]))
                    .collect();
                if !bad.is_empty() {
                    first_bad[j] = Some(format!("tick {t}: {}", bad.join(" ")));
                }
            }
        }
    }
    sim.apply_iter(tail.iter());
    for (j, dv) in given.iter().enumerate() {
        eprintln!(
            "WALKTRACE d={dv:#x} first reverse mismatch: {}",
            first_bad[j].clone().unwrap_or("none".into())
        );
    }
}

pub fn run() {
    let pp = super::pointadd::params();
    let env = super::pointadd::envelope();
    let p = U512::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    let batches: usize = super::pointadd::knob("SKYCOF_PROBE_BATCHES")
        .map(|v| v.parse().unwrap())
        .unwrap_or(4);
    let mut b = Builder::new();
    let d = b.alloc_qubits(N);
    let pass = b.alloc_qubits(
        super::pointadd::knob("SKYCOF_PROBE_PASS")
            .map(|v| v.parse().unwrap())
            .unwrap_or(N),
    );
    let cut: usize = super::pointadd::knob("SKYCOF_PROBE_CUT")
        .map(|v| v.parse().unwrap())
        .unwrap_or(0);
    if cut > 0 && super::pointadd::knob_flag("SKYCOF_PROBE_PREFIX_ONLY") {
        let mut st = walk::forward_to(&mut b, &pp.walk, env, &d, cut);
        let widths = [
            st.rails.r1.len(),
            st.rails.r2.len(),
            st.cof.s.len(),
            st.cof.r.len(),
            st.h.wires.len(),
            st.odo.len(),
            usize::from(st.typ.is_some()),
        ];
        let fwd_end = b.op_count();
        let mut seam_cost = None;
        let mut gauge_spec = None;
        if cut == 200 && super::pointadd::knob_flag("SKYCOF_PROBE_CUT200_ADAPTER") {
            let t0 = b.report_totals().map_or(0.0, |x| x.1);
            cut200_gauge(&mut b, &mut st, &pass, false);
            let t1 = b.report_totals().map_or(t0, |x| x.1);
            if super::pointadd::knob_flag("SKYCOF_PROBE_CUT200_GAUGE_SPEC") {
                gauge_spec = Some((
                    b.op_count(),
                    [
                        st.rails.r1.clone(),
                        st.rails.r2.clone(),
                        st.cof.s.clone(),
                        st.cof.r.clone(),
                    ],
                ));
            }
            cut200_pack(&mut b, &mut st, &pass, false);
            let t2 = b.report_totals().map_or(t1, |x| x.1);
            cut200_pack(&mut b, &mut st, &pass, true);
            let t3 = b.report_totals().map_or(t2, |x| x.1);
            cut200_gauge(&mut b, &mut st, &pass, true);
            let t4 = b.report_totals().map_or(t3, |x| x.1);
            seam_cost = Some((t1 - t0, t2 - t1, t3 - t2, t4 - t3, b.peak_total()));
        }
        let restored = walk::backward_from_active(&mut b, &pp.walk, env, st);
        let ops = b.take_ops();
        let (nq, nb) = b.i13_dims();
        let mut rd = {
            let mut h = Shake256::default();
            h.update(b"skycof-prefix-roundtrip");
            h.finalize_xof()
        };
        let mut sim = Simulator::new(nq, nb + 1, &mut rd);
        let mut seed = 0x5052_4546_4958_u64 ^ cut as u64;
        let batches: usize = super::pointadd::knob("SKYCOF_PROBE_PREFIX_BATCHES")
            .map(|v| v.parse().unwrap())
            .unwrap_or(4);
        let keep: HashSet<u64> = restored.iter().chain(&pass).map(|q| q.0).collect();
        let mut failures = 0usize;
        let mut gauge_value_failures = 0usize;
        let mut gauge_invariant_failures = 0usize;
        let mut gauge_phase_failures = 0usize;
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut ds = Vec::with_capacity(64);
            let mut ps = Vec::with_capacity(64);
            for shot in 0..64 {
                let mut dv = U512::ZERO;
                let mut pv = U512::ZERO;
                for limb in 0..4 {
                    dv |= U512::from(rng_next(&mut seed)) << (64 * limb);
                    pv |= U512::from(rng_next(&mut seed)) << (64 * limb);
                }
                dv = dv.reduce_mod(p);
                set(&mut sim, &d, dv, shot);
                set(&mut sim, &pass, pv, shot);
                ds.push(dv);
                ps.push(pv);
            }
            if let Some((end, regs)) = &gauge_spec {
                sim.apply_iter(ops[..*end].iter());
                for shot in 0..64 {
                    let actual = regs.each_ref().map(|r| get_signed(&sim, r, shot));
                    let expected = canonical_prefix_spec(ds[shot], p, cut);
                    gauge_value_failures += usize::from(actual != expected);
                    gauge_invariant_failures += usize::from(
                        actual[0]
                            .wrapping_mul(actual[2])
                            .wrapping_add(actual[1].wrapping_mul(actual[3]))
                            != p,
                    );
                    gauge_phase_failures += ((sim.phase >> shot) & 1) as usize;
                }
                sim.apply_iter(ops[*end..].iter());
            } else {
                sim.apply_iter(ops.iter());
            }
            let mut garbage = 0u64;
            for id in 0..nq {
                if !keep.contains(&(id as u64)) {
                    garbage |= sim.qubits[id];
                }
            }
            for shot in 0..64 {
                failures += usize::from(
                    get(&sim, &restored, shot) != ds[shot]
                        || get(&sim, &pass, shot) != ps[shot]
                        || (garbage >> shot) & 1 != 0
                        || (sim.phase >> shot) & 1 != 0,
                );
            }
        }
        eprintln!(
            "WALKPROBE prefix_only cut={cut} peak={} live={} widths={widths:?} ops={} expected_T_fwd={:.3} expected_T_rev={:.3} expected_T_pair={:.3} shots={} failures={failures}",
            b.peak_total(), b.active_qubits(), ops.len(), expected_t(&ops[..fwd_end]),
            expected_t(&ops[fwd_end..]), expected_t(&ops), batches * 64
        );
        if let Some((gf, af, ai, gi, peak)) = seam_cost {
            eprintln!("CUT200_ADAPTER gauge_fwd={gf:.3} adapter_fwd={af:.3} adapter_inv={ai:.3} gauge_inv={gi:.3} pair={:.3} peak={peak}",gf+af+ai+gi);
        }
        if gauge_spec.is_some() {
            eprintln!("CUT200_GAUGE_SPEC shots={} value_failures={gauge_value_failures} invariant_failures={gauge_invariant_failures} phase_failures={gauge_phase_failures}", batches * 64);
            assert_eq!(
                (
                    gauge_value_failures,
                    gauge_invariant_failures,
                    gauge_phase_failures
                ),
                (0, 0, 0),
                "actual native prefix gauge does not match the canonical signed GCD ABI"
            );
        }
        return;
    }
    let mut cut_diag = None;
    let mut positive_diag: Option<(usize, Vec<Q>, Vec<Q>)> = None;
    let pk = if cut == 0 {
        walk::forward(&mut b, &pp.walk, env, &d)
    } else {
        let mut st = walk::forward_to(&mut b, &pp.walk, env, &d, cut);
        let widths = [
            st.rails.r1.len(),
            st.rails.r2.len(),
            st.cof.s.len(),
            st.cof.r.len(),
            st.h.wires.len(),
            st.odo.len(),
            usize::from(st.typ.is_some()),
        ];
        cut_diag = Some((
            b.op_count(),
            b.active_qubits(),
            b.peak_total(),
            st.live_width(),
            widths,
        ));
        if super::pointadd::knob_flag("SKYCOF_PROBE_POSITIVE_SEAM") {
            let typ = st.typ.expect("positive seam needs a completed prefix tick");
            let (frame, peak_f) =
                b.r3_peak(|b| super::packed_seam::to_positive(b, &mut st.rails, typ, &pass, 999));
            positive_diag = Some((b.op_count(), st.rails.r1.clone(), st.rails.r2.clone()));
            let mut bucket_peak = 0;
            let mut bucket_live = 0;
            if super::pointadd::knob_flag("SKYCOF_PROBE_BUCKET_SEAM") {
                assert_eq!(cut, 160, "first bucket geometry is for cut 160");
                let ((a, d, live), p0) = b.r3_peak(|b| {
                    let a = super::packed_seam::bucket_pack(b, &st.rails.r1, &st.cof.s);
                    let d = super::packed_seam::bucket_pack(b, &st.rails.r2, &st.cof.r);
                    (a, d, b.active_qubits())
                });
                bucket_peak = p0;
                bucket_live = live;
                let (_, p1) = b.r3_peak(|b| {
                    super::packed_seam::bucket_unpack(b, &st.rails.r2, &st.cof.r, d);
                    super::packed_seam::bucket_unpack(b, &st.rails.r1, &st.cof.s, a);
                });
                bucket_peak = bucket_peak.max(p1);
                assert!(bucket_peak <= 999, "bucket seam peak {bucket_peak}");
            }
            let (_, peak_i) = b.r3_peak(|b| {
                super::packed_seam::from_positive(b, &mut st.rails, typ, &pass, 999, frame)
            });
            eprintln!("WALKPROBE positive_seam cut={cut} peak_fwd={peak_f} bucket_peak={bucket_peak} bucket_live={bucket_live} peak_inv={peak_i} live_after={} ops={}", b.active_qubits(), b.op_count());
        }
        walk::forward_from(&mut b, &pp.walk, env, st)
    };
    let ops_f = b.take_ops();
    let s = pk.s.clone();
    let hw = pk.h.wires.clone();
    let odo = pk.odo.clone();
    let live_f = b.active_qubits();
    let d2 = walk::backward(&mut b, &pp.walk, env, pk);
    let ops_b = b.take_ops();
    let (nq, nb) = b.i13_dims();
    let passenger_ids: HashSet<u64> = pass.iter().map(|q| q.0).collect();
    assert!(
        ops_f.iter().chain(&ops_b).all(|op| {
            !passenger_ids.contains(&op.q_target.0)
                && !passenger_ids.contains(&op.q_control1.0)
                && !passenger_ids.contains(&op.q_control2.0)
        }),
        "GCD walk accesses a supposedly untouched passenger owner"
    );
    eprintln!(
        "WALKPROBE spectator_identity Q={} quantum_operand_references=0",
        pass.len()
    );
    let tf = expected_t(&ops_f);
    let tb = expected_t(&ops_b);
    eprintln!("WALKPROBE built: ops_f={} ops_b={} live_after_fwd={} peak={} nq={nq} expected_T_fwd={tf:.3} expected_T_back={tb:.3} expected_T_pair={:.3}", ops_f.len(), ops_b.len(), live_f, b.peak_total(), tf + tb);
    if let Some((op, live, peak, gcd_live, widths)) = cut_diag {
        eprintln!("WALKPROBE cut={cut} op={op} active_with_passenger={live} peak_to_cut={peak} gcd_live={gcd_live} widths=r1/r2/s/r/H/odo/typ:{widths:?} expected_T_prefix={:.3}", expected_t(&ops_f[..op]));
    }
    let keep_f: HashSet<u64> = s
        .iter()
        .chain(&hw)
        .chain(&odo)
        .chain(&pass)
        .map(|q| q.0)
        .collect();
    let keep_b: HashSet<u64> = d2.iter().chain(&pass).map(|q| q.0).collect();
    let r2 = U512::from(2u64).pow_mod(U512::from(pp.walk.r as u64), p);
    let mut seed = 0x5eed_u64;
    let (mut plus, mut minus, mut other, mut gf, mut phf, mut bad_b, mut gb, mut phb) =
        (0, 0, 0, 0, 0, 0, 0, 0);
    let mut rd = {
        let mut h = Shake256::default();
        h.update(b"skycof-walk-probe");
        h.finalize_xof()
    };
    let mut sim = Simulator::new(nq, nb + 1, &mut rd);
    let given: Vec<U512> = super::pointadd::knob("SKYCOF_PROBE_D")
        .map(|v| {
            v.split(',')
                .filter(|s| !s.is_empty())
                .map(|h| {
                    let mut d = U512::ZERO;
                    for ch in h.trim().trim_start_matches("0x").chars() {
                        d = (d << 4) | U512::from(ch.to_digit(16).unwrap() as u64);
                    }
                    d
                })
                .collect()
        })
        .unwrap_or_default();
    let mut conf = [0usize; 4];
    for bt in 0..batches {
        sim.clear_for_shot();
        let mut fbad = [false; 64];
        let mut ds = Vec::new();
        for j in 0..64 {
            let mut v = U512::ZERO;
            for i in 0..4 {
                v |= U512::from(rng_next(&mut seed)) << (64 * i);
            }
            let v = if bt == 0 && j < given.len() {
                given[j]
            } else {
                v.reduce_mod(p)
            };
            set(&mut sim, &d, v, j);
            ds.push(v);
        }
        if let Some((mid, ref ureg, ref vreg)) = positive_diag {
            sim.apply_iter(ops_f[..mid].iter());
            for (j, &dv) in ds.iter().enumerate() {
                let (u, v) = kaliski_values_at(dv, p, cut);
                assert_eq!(get(&sim, ureg, j), u, "positive seam u mismatch shot {j}");
                assert_eq!(get(&sim, vreg, j), v, "positive seam v mismatch shot {j}");
            }
            sim.apply_iter(ops_f[mid..].iter());
        } else {
            sim.apply_iter(ops_f.iter());
        }
        let mut g = 0u64;
        for id in 0..nq {
            if !keep_f.contains(&(id as u64)) {
                g |= sim.qubits[id];
            }
        }
        for (j, &dv) in ds.iter().enumerate() {
            let sv = get(&sim, &s, j).reduce_mod(p);
            let want = r2.mul_mod(dv.inv_mod(p).unwrap(), p);
            let negw = (p - want).reduce_mod(p);
            let ododv = get(&sim, &odo, j);
            let tag = if sv == want {
                plus += 1;
                "+"
            } else if sv == negw {
                minus += 1;
                "-"
            } else {
                other += 1;
                "?"
            };
            fbad[j] = tag != "-" || (g >> j) & 1 == 1 || (sim.phase >> j) & 1 == 1;
            if (g >> j) & 1 == 1 {
                gf += 1;
            }
            if (sim.phase >> j) & 1 == 1 {
                phf += 1;
            }
            if j < 8 {
                eprintln!(
                    "WALKPROBE shot sign={tag} odo={ododv} garbage={} phase={}",
                    (g >> j) & 1,
                    (sim.phase >> j) & 1
                );
            }
        }
        sim.apply_iter(ops_b.iter());
        let mut g = 0u64;
        for id in 0..nq {
            if !keep_b.contains(&(id as u64)) {
                g |= sim.qubits[id];
            }
        }
        for (j, &dv) in ds.iter().enumerate() {
            let bad = get(&sim, &d2, j) != dv || (g >> j) & 1 == 1 || (sim.phase >> j) & 1 == 1;
            if get(&sim, &d2, j) != dv {
                bad_b += 1;
            }
            if (g >> j) & 1 == 1 {
                gb += 1;
            }
            if (sim.phase >> j) & 1 == 1 {
                phb += 1;
            }
            if bad && (bt == 0 && j < given.len() || bad_b + gb + phb < 20) {
                eprintln!(
                    "WALKPROBE back-fail d={dv:#x} d_ok={} garbage={} phase={}",
                    get(&sim, &d2, j) == dv,
                    (g >> j) & 1,
                    (sim.phase >> j) & 1
                );
            }
            let actual = bad || fbad[j];
            let pred = classify(dv, p);
            conf[(actual as usize) * 2 + (!pred.is_empty()) as usize] += 1;
            if actual != !pred.is_empty() {
                eprintln!(
                    "WALKPROBE model-mismatch d={dv:#x} actual_bad={actual} predicted={pred:?}"
                );
            }
        }
    }
    eprintln!("WALKPROBE shots={} s=+2^R/d:{plus} s=-2^R/d:{minus} other:{other} fwd_garbage:{gf} fwd_phase:{phf} | back d_wrong:{bad_b} garbage:{gb} phase:{phb}", batches * 64);
    eprintln!(
        "WALKPROBE model vs circuit: ok/ok={} ok/pred-bad={} bad/pred-ok={} bad/bad={}",
        conf[0], conf[1], conf[2], conf[3]
    );
}
