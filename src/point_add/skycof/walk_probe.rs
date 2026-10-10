//! Research probe (`SKYCOF_RESEARCH=1 SKYCOF_PROBE=walk`): the forward walk and the walk back alone,
//! simulated on random `d`. Reports the parked `s` against `-+2^R / d`, garbage and phase after the
//! forward walk, and `d` / garbage / phase after the walk back.
use super::walk;
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::skycof_mm::model::U512;
use crate::point_add::N;
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};
use sha3::Shake256;
use std::collections::HashSet;

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

// ─── classical walk model (rails drive the letters, as in tick.rs) ─────────────────────────────

fn negu(x: U512) -> bool {
    x.bit(511)
}
fn sar1(x: U512) -> U512 {
    let y = x >> 1usize;
    if negu(x) { y | (U512::from(1u64) << 511usize) } else { y }
}
fn bitsu(x: U512) -> usize {
    512 - x.leading_zeros()
}
fn swu(x: U512) -> usize {
    if negu(x) { bitsu(!x) + 1 } else { bitsu(x) + 1 }
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
    let mut park: Option<usize> = None;
    let topj = (U512::from(1u64) << clamp) - (U512::from(1u64) << (clamp - pp.walk.park_j));
    for t in 0..r {
        let w = env.widths(t);
        let pre = swu(r1).max(swu(r2));
        if pre > w.wsw { out.push(format!("t{t}:rail_swap {pre}>{}", w.wsw)); }
        let c = r1.bit(0);
        let (mut a, mut b) = (r1, r2);
        if c { std::mem::swap(&mut a, &mut b); }
        let h = sar1(a);
        let agree = negu(h) == negu(b);
        let b2 = if agree { b.wrapping_sub(h) } else { b.wrapping_add(h) };
        let ad = swu(h).max(swu(b)).max(swu(b2));
        if ad > w.wad { out.push(format!("t{t}:rail_add {ad}>{}", w.wad)); }
        let isc = negu(b2) != negu(b);
        typ ^= c;
        if isc { std::mem::swap(&mut s, &mut rr); }
        if !typ { rr += s; }
        let sop = s;
        s <<= 1usize;
        if isc != (s.bit(1) && !typ) { out.push(format!("t{t}:isc_erase")); }
        let cofn = bitsu(rr).max(bitsu(sop) + 1);
        if cofn > w.ecof && !(w.ecof == clamp && cofn == clamp + 1 && bitsu(rr) <= clamp) {
            out.push(format!("t{t}:cof {cofn}>{}", w.ecof));
        }
        let parked_now = rr == p;
        if parked_now && park.is_none() { park = Some(t); }
        if bitsu(s) > clamp {
            if park.is_none() { out.push(format!("t{t}:fold_before_park")); }
            s -= p;
            if bitsu(s) > clamp { out.push(format!("t{t}:fold_overflow")); }
        }
        r1 = h;
        r2 = b2;
        // park test (top park_j bits of r) on clamp ticks; below the clamp the walk must not park
        if w.ecof == clamp {
            let z = rr & topj == topj;
            if z != parked_now { out.push(format!("t{t}:parktest z={z} parked={parked_now}")); }
        } else if parked_now {
            out.push(format!("t{t}:park_below_clamp"));
        }
        // decoder push (t >= 1, not parked)
        if t >= 1 && !parked_now {
            let sl = s.as_limbs();
            let rl = rr.as_limbs();
            let (_, amb) = decide(sl, rl, env.cof[t], pp.walk.w_dec, true);
            if amb { pushes += 1; }
            if pushes > env.h[t] { out.push(format!("t{t}:H {pushes}>{}", env.h[t])); }
            // letter consistency: decoder certain-A must be A, C iff bit1(s)
            let letter_a = typ;
            if !amb && !s.bit(1) && !letter_a { out.push(format!("t{t}:decoder_certainA_wrong")); }
        }
    }
    if !(r1.is_zero() && r2 == U512::from(1u64)) {
        out.push(format!("rails_not_parked park={park:?}"));
    }
    match park {
        None => out.push("no_park".into()),
        Some(k) => {
            if r - 1 - k > (1 << pp.walk.odo_bits) - 1 { out.push(format!("odo_overflow park={k}")); }
        }
    }
    if out.len() > 6 { out.truncate(6); out.push("...".into()); }
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
    let n: usize = super::pointadd::knob("SKYCOF_PROBE_N").map(|v| v.parse().unwrap()).unwrap_or(0);
    if n > 0 {
        let mut seed: u64 = super::pointadd::knob("SKYCOF_PROBE_SEED").map(|v| v.parse().unwrap()).unwrap_or(0xC1A55);
        let mut cats: std::collections::BTreeMap<String, usize> = Default::default();
        let mut bad = 0usize;
        for _ in 0..n {
            let mut v = U512::ZERO;
            for i in 0..4 {
                v |= U512::from(rng_next(&mut seed)) << (64 * i);
            }
            let d = v.reduce_mod(p);
            if d.is_zero() { continue; }
            let o = classify(d, p);
            if !o.is_empty() {
                bad += 1;
                let k = o[0].split_once(':').map(|(_, b)| b.split(' ').next().unwrap().to_string()).unwrap_or(o[0].clone());
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
    let (nq, nb) = b.i13_dims();
    let given: Vec<U512> = super::pointadd::knob("SKYCOF_PROBE_D").unwrap().split(',').filter(|s| !s.is_empty()).map(|h| {
        let mut d = U512::ZERO;
        for ch in h.trim().trim_start_matches("0x").chars() {
            d = (d << 4) | U512::from(ch.to_digit(16).unwrap() as u64);
        }
        d
    }).collect();
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
        let vals: Vec<Vec<U512>> = (0..given.len()).map(|j| regs.iter().map(|r| get(&sim, r, j)).collect()).collect();
        if let Some(t) = tag.strip_prefix('F') {
            fwd.insert(t.to_string(), vals);
        } else if let Some(t) = tag.strip_prefix('B') {
            let f = &fwd[t];
            for j in 0..given.len() {
                if first_bad[j].is_some() { continue; }
                let names = ["r1", "r2", "s", "r", "H", "odo", "typ"];
                let bad: Vec<String> = (0..7).filter(|&k| f[j][k] != vals[j][k] || (k != 4 && regs[k].len() != snaps.iter().find(|x| x.0 == format!("F{t}")).unwrap().2[k].len()))
                    .map(|k| format!("{}(f={:#x} b={:#x})", names[k], f[j][k], vals[j][k])).collect();
                if !bad.is_empty() {
                    first_bad[j] = Some(format!("tick {t}: {}", bad.join(" ")));
                }
            }
        }
    }
    sim.apply_iter(tail.iter());
    for (j, dv) in given.iter().enumerate() {
        eprintln!("WALKTRACE d={dv:#x} first reverse mismatch: {}", first_bad[j].clone().unwrap_or("none".into()));
    }
}

pub fn run() {
    let pp = super::pointadd::params();
    let env = super::pointadd::envelope();
    let p = U512::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    let batches: usize = super::pointadd::knob("SKYCOF_PROBE_BATCHES").map(|v| v.parse().unwrap()).unwrap_or(4);
    let mut b = Builder::new();
    let d = b.alloc_qubits(N);
    let pass = b.alloc_qubits(super::pointadd::knob("SKYCOF_PROBE_PASS").map(|v| v.parse().unwrap()).unwrap_or(N));
    let pk = walk::forward(&mut b, &pp.walk, env, &d);
    let ops_f = b.take_ops();
    let s = pk.s.clone();
    let hw = pk.h.wires.clone();
    let odo = pk.odo.clone();
    let live_f = b.active_qubits();
    let d2 = walk::backward(&mut b, &pp.walk, env, pk);
    let ops_b = b.take_ops();
    let (nq, nb) = b.i13_dims();
    eprintln!("WALKPROBE built: ops_f={} ops_b={} live_after_fwd={} peak={} nq={nq}", ops_f.len(), ops_b.len(), live_f, b.peak_total());
    let keep_f: HashSet<u64> = s.iter().chain(&hw).chain(&odo).chain(&pass).map(|q| q.0).collect();
    let keep_b: HashSet<u64> = d2.iter().chain(&pass).map(|q| q.0).collect();
    let r2 = U512::from(2u64).pow_mod(U512::from(pp.walk.r as u64), p);
    let mut seed = 0x5eed_u64;
    let (mut plus, mut minus, mut other, mut gf, mut phf, mut bad_b, mut gb, mut phb) = (0, 0, 0, 0, 0, 0, 0, 0);
    let mut rd = {
        let mut h = Shake256::default();
        h.update(b"skycof-walk-probe");
        h.finalize_xof()
    };
    let mut sim = Simulator::new(nq, nb + 1, &mut rd);
    let given: Vec<U512> = super::pointadd::knob("SKYCOF_PROBE_D")
        .map(|v| {
            v.split(',').filter(|s| !s.is_empty()).map(|h| {
                let mut d = U512::ZERO;
                for ch in h.trim().trim_start_matches("0x").chars() {
                    d = (d << 4) | U512::from(ch.to_digit(16).unwrap() as u64);
                }
                d
            }).collect()
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
            let v = if bt == 0 && j < given.len() { given[j] } else { v.reduce_mod(p) };
            set(&mut sim, &d, v, j);
            ds.push(v);
        }
        sim.apply_iter(ops_f.iter());
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
            let tag = if sv == want { plus += 1; "+" } else if sv == negw { minus += 1; "-" } else { other += 1; "?" };
            fbad[j] = tag != "-" || (g >> j) & 1 == 1 || (sim.phase >> j) & 1 == 1;
            if (g >> j) & 1 == 1 { gf += 1; }
            if (sim.phase >> j) & 1 == 1 { phf += 1; }
            if j < 8 {
                eprintln!("WALKPROBE shot sign={tag} odo={ododv} garbage={} phase={}", (g >> j) & 1, (sim.phase >> j) & 1);
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
            if get(&sim, &d2, j) != dv { bad_b += 1; }
            if (g >> j) & 1 == 1 { gb += 1; }
            if (sim.phase >> j) & 1 == 1 { phb += 1; }
            if bad && (bt == 0 && j < given.len() || bad_b + gb + phb < 20) {
                eprintln!("WALKPROBE back-fail d={dv:#x} d_ok={} garbage={} phase={}", get(&sim, &d2, j) == dv, (g >> j) & 1, (sim.phase >> j) & 1);
            }
            let actual = bad || fbad[j];
            let pred = classify(dv, p);
            conf[(actual as usize) * 2 + (!pred.is_empty()) as usize] += 1;
            if actual != !pred.is_empty() {
                eprintln!("WALKPROBE model-mismatch d={dv:#x} actual_bad={actual} predicted={pred:?}");
            }
        }
    }
    eprintln!("WALKPROBE shots={} s=+2^R/d:{plus} s=-2^R/d:{minus} other:{other} fwd_garbage:{gf} fwd_phase:{phf} | back d_wrong:{bad_b} garbage:{gb} phase:{phb}", batches * 64);
    eprintln!("WALKPROBE model vs circuit: ok/ok={} ok/pred-bad={} bad/pred-ok={} bad/bad={}", conf[0], conf[1], conf[2], conf[3]);
}
