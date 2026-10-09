//! Research probe (`SKYCOF_RESEARCH=1 SKYCOF_PROBE=replay`): the evaluator's shot inputs for an `ops.bin`
//! (`SKYCOF_REPLAY_OPS`, default `ops.bin`) and shot indices (`SKYCOF_REPLAY_SHOTS=i,j,...`): the two walk
//! inputs `d = x - ox` and `D' = ox - x3` of each shot, with the classical failure prediction of the ring walk.
use super::wfull::classify;
use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
use alloy_primitives::U256;
use ruint::Uint;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use std::io::Read;

type U = Uint<512, 8>;

fn secp() -> WeierstrassEllipticCurve {
    let h = |s: &str| U256::from_str_radix(s, 16).unwrap();
    WeierstrassEllipticCurve {
        modulus: h("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U256::from(0),
        b: U256::from(7),
        gx: h("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: h("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: h("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    }
}

fn to_u(x: U256) -> U {
    U::from_limbs_slice(x.as_limbs())
}

pub fn run() {
    let k = |n: &str| crate::point_add::skycof::pointadd::knob(n);
    let path = k("SKYCOF_REPLAY_OPS").unwrap_or_else(|| "ops.bin".into());
    let shots: Vec<usize> = k("SKYCOF_REPLAY_SHOTS").unwrap_or_default().split(',').filter(|s| !s.is_empty()).map(|s| s.trim().parse().unwrap()).collect();
    let mut f = std::fs::File::open(&path).expect("open ops.bin");
    let mut hdr = [0u8; 16];
    f.read_exact(&mut hdr).unwrap();
    assert_eq!(&hdr[..8], b"QECCOPSZ");
    let n = u64::from_le_bytes(hdr[8..].try_into().unwrap()) as usize;
    let mut dec = zstd::stream::read::Decoder::new(std::io::BufReader::new(f)).unwrap();
    dec.window_log_max(27).unwrap();
    let mut hasher = sha3::Shake256::default();
    hasher.update(b"quantum_ecc-fiat-shamir-v2");
    hasher.update(&(n as u64).to_le_bytes());
    let mut rec = [0u8; 56];
    for _ in 0..n {
        dec.read_exact(&mut rec).unwrap();
        let kind = u32::from_le_bytes(rec[0..4].try_into().unwrap()) as u8;
        hasher.update(&[kind]);
        for off in [8usize, 16, 24, 32, 40, 48] {
            hasher.update(&rec[off..off + 8]);
        }
    }
    let mut xof = hasher.finalize_xof();
    let curve = secp();
    let p = to_u(curve.modulus);
    let env = super::pointadd::envelope().clone();
    let mut idx = 0usize;
    let mut walk_inputs: Vec<U> = Vec::new();
    let mut pa_inputs: Vec<(U256, U256, U256, U256, usize)> = Vec::new();
    for _ in 0..9024 {
        let mut rb = [[0u8; 32]; 2];
        XofReader::read(&mut xof, &mut rb[0]);
        XofReader::read(&mut xof, &mut rb[1]);
        let k1 = U256::from_le_bytes(rb[0]);
        let k2 = U256::from_le_bytes(rb[1]);
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) {
            continue;
        }
        if shots.contains(&idx) {
            let e = curve.add(t.0, t.1, o.0, o.1);
            let (x, ox, x3) = (to_u(t.0), to_u(o.0), to_u(e.0));
            let d = x.add_mod(p - ox, p);
            let dp = ox.add_mod(p - x3, p);
            eprintln!("REPLAY shot {idx}: d={d:#x} -> {:?}", classify(d, &env));
            eprintln!("REPLAY shot {idx}: D'={dp:#x} -> {:?}", classify(dp, &env));
            walk_inputs.push(d);
            walk_inputs.push(dp);
            pa_inputs.push((t.0, t.1, o.0, o.1, idx));
            if k("SKYCOF_REPLAY_SQ").is_some_and(|v| v == "1") {
                // square inputs of this shot: x = d, y = lam = (y - oy) / (x - ox), ox
                let pp = curve.modulus;
                let dd = crate::weierstrass_elliptic_curve::sub_mod(t.0, o.0, pp);
                let dy = crate::weierstrass_elliptic_curve::sub_mod(t.1, o.1, pp);
                let inv = dd.inv_mod(pp).unwrap();
                let lam = dy.mul_mod(inv, pp);
                let (ph, garb) = square_on(dd, lam, o.0, 8);
                eprintln!("REPLAY square on shot {idx}: lanes 512 phase {ph} garbage {garb}");
            }
        }
        idx += 1;
    }
    eprintln!("REPLAY shots generated {idx}");
    if k("SKYCOF_REPLAY_PA").is_some_and(|v| v == "1") && !pa_inputs.is_empty() {
        pa_sections(&pa_inputs, k("SKYCOF_REPLAY_BATCHES").map(|v| v.parse().unwrap()).unwrap_or(4));
    }
    // gate-level walks of the replayed inputs, each repeated over many measurement streams
    let reps: usize = k("SKYCOF_REPLAY_REPS").map(|v| v.parse().unwrap()).unwrap_or(0);
    if reps > 0 && !walk_inputs.is_empty() {
        let bt = super::wtest::build(&env, 256);
        let mut ds = Vec::new();
        for _ in 0..reps {
            ds.extend(walk_inputs.iter().copied());
        }
        for seed in 0..4u64 {
            let bad = super::wtest::simulate(&bt, &env, p, &ds, 1000 + seed);
            eprintln!("REPLAY walk sim seed {seed}: {} lanes, {} bad {:?}", ds.len(), bad.len(), bad.iter().take(4).collect::<Vec<_>>());
        }
    }
}

/// Whole point addition (pre-simplifier, in-process build) on the replayed inputs, every lane of a batch the same
/// input with its own measurement stream; reports the phase of each lane at every section boundary (it must be 0
/// outside the two measured-debt spans) and the final correctness / garbage / phase.
fn pa_sections(inputs: &[(U256, U256, U256, U256, usize)], batches: usize) {
    use crate::sim::Simulator;
    use sha3::Shake256;
    super::pointadd::MARKS.with(|m| *m.borrow_mut() = Some(Vec::new()));
    let (ops, x, y, ox, oy, nq, nb) = super::pointadd::build_point_add_regs();
    let marks = super::pointadd::MARKS.with(|m| m.borrow_mut().take().unwrap());
    eprintln!("REPLAY pa built: {} ops, {} marks", ops.len(), marks.len());
    let curve = secp();
    let debt = ["sc_div_hmr", "sc_div_back", "sc_mul_hmr", "sc_mul_fwd", "sc_mul_mm5"];
    for &(tx, ty, ox_v, oy_v, idx) in inputs {
        let e = curve.add(tx, ty, ox_v, oy_v);
        let mut per_section: std::collections::BTreeMap<&str, u32> = Default::default();
        let mut final_bad = 0u32;
        let mut final_phase = 0u32;
        for bt in 0..batches {
            let mut rd = {
                let mut h = Shake256::default();
                sha3::digest::Update::update(&mut h, format!("pa-replay-{idx}-{bt}").as_bytes());
                h.finalize_xof()
            };
            let mut sim = Simulator::new(nq, nb + 1, &mut rd);
            sim.clear_for_shot();
            for lane in 0..64 {
                for i in 0..256 {
                    if tx.bit(i) { *sim.qubit_mut(x[i]) |= 1 << lane; }
                    if ty.bit(i) { *sim.qubit_mut(y[i]) |= 1 << lane; }
                    if ox_v.bit(i) { *sim.bit_mut(ox[i]) |= 1 << lane; }
                    if oy_v.bit(i) { *sim.bit_mut(oy[i]) |= 1 << lane; }
                }
            }
            let mut prev = 0usize;
            let mut names: Vec<(&str, usize)> = marks.clone();
            names.push(("end_of_ops", ops.len()));
            // section i spans [mark_i, mark_{i+1}); check the phase at the start of each section
            for w in names.windows(2) {
                let (nm, at) = w[0];
                sim.apply_iter(ops[prev..at].iter());
                prev = at;
                let _ = nm;
                // phase after everything before section `nm`: name the section that just ended
                let ended = names.iter().rev().find(|(_, a)| *a < at).map(|x| x.0).unwrap_or("start");
                if !debt.contains(&ended) && sim.phase != 0 {
                    *per_section.entry(ended).or_default() += sim.phase.count_ones();
                }
            }
            sim.apply_iter(ops[prev..].iter());
            let mut wrong = 0u64;
            for lane in 0..64 {
                let mut gx = U256::ZERO;
                let mut gy = U256::ZERO;
                for i in 0..256 {
                    if (sim.qubit(x[i]) >> lane) & 1 == 1 { gx.set_bit(i, true); }
                    if (sim.qubit(y[i]) >> lane) & 1 == 1 { gy.set_bit(i, true); }
                }
                if gx != e.0 || gy != e.1 { wrong |= 1 << lane; }
            }
            final_bad += wrong.count_ones();
            final_phase += sim.phase.count_ones();
        }
        eprintln!("REPLAY pa shot {idx}: lanes {} wrong {final_bad} final-phase {final_phase}; nonzero phase at section ends {:?}", 64 * batches, per_section);
    }
}

/// The square section alone (`x += 3 ox; x -= y^2`, as in the point addition) on given `(x, y, ox)`, 64 lanes each
/// with its own measurement stream: counts wrong / garbage / phase lanes.
pub fn square_on(xv: U256, yv: U256, oxv: U256, batches: usize) -> (u32, u32) {
    use crate::point_add::builder::Builder;
    use crate::point_add::classical::coord_add3x;
    use crate::point_add::square::sub_square;
    use crate::sim::Simulator;
    use sha3::Shake256;
    let circ = &mut Builder::new();
    let x = circ.alloc_qubits(256);
    let y = circ.alloc_qubits(256);
    let ox = circ.alloc_bits(256);
    coord_add3x(circ, &x, &ox);
    sub_square(circ, &x, &y);
    let ops = circ.take_ops();
    let (nq, nb) = circ.i13_dims();
    let (mut ph, mut garb) = (0u32, 0u32);
    let keep: std::collections::HashSet<u64> = x.iter().chain(&y).map(|q| q.0).collect();
    for bt in 0..batches {
        let mut rd = {
            let mut h = Shake256::default();
            sha3::digest::Update::update(&mut h, format!("sq-replay-{bt}").as_bytes());
            h.finalize_xof()
        };
        let mut sim = Simulator::new(nq, nb + 1, &mut rd);
        sim.clear_for_shot();
        for lane in 0..64 {
            for i in 0..256 {
                if xv.bit(i) { *sim.qubit_mut(x[i]) |= 1 << lane; }
                if yv.bit(i) { *sim.qubit_mut(y[i]) |= 1 << lane; }
                if oxv.bit(i) { *sim.bit_mut(ox[i]) |= 1 << lane; }
            }
        }
        sim.apply_iter(ops.iter());
        let mut g = 0u64;
        for id in 0..nq {
            if !keep.contains(&(id as u64)) { g |= sim.qubits[id]; }
        }
        ph += sim.phase.count_ones();
        garb += g.count_ones();
    }
    (ph, garb)
}
