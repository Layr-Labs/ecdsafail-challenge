//! Research probe (`SKYCOF_RESEARCH=1 SKYCOF_PROBE=pa`): the SKY-COF point addition built in segments and
//! simulated segment by segment on given inputs (`SKYCOF_PROBE_SHOTS=tx,ty,ox,oy;...` hex, padded with random
//! field elements to `SKYCOF_PROBE_BATCHES` x 64 shots). After each segment the live registers are compared
//! with the classical values; the first failing checkpoint of every shot is reported.
use super::pointadd::{self as pa, envelope, hmr_all, mulf_role as mulf, mulf_inv_role as mulf_inv, params, pay_debt, MmRole};
use super::walk;
use crate::circuit::{BitId, Op, QubitId as Q};
use crate::point_add::builder::Builder;
use crate::point_add::classical::{coord_add3x, coord_rsub, coord_sub};
use crate::point_add::skycof_mm::model::U512;
use crate::point_add::square::sub_square;
use crate::point_add::N;
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

#[derive(Clone, Copy)]
enum V {
    D,
    Dy,
    S,
    Lam,
    Dp,
    Tmp,
    S2,
    Yf,
    Xf,
}

struct Seg {
    name: &'static str,
    ops: Vec<Op>,
    checks: Vec<(V, Vec<Q>, bool)>, // (value, wires, exact-canonical required)
    // Intentional X-basis measurement phase, before the matching pay_debt.
    debt: Option<(V, Vec<BitId>)>,
}

fn parse_hex(s: &str) -> U512 {
    let s = s.trim().trim_start_matches("0x");
    let mut v = U512::ZERO;
    for ch in s.chars() {
        v = (v << 4) | U512::from(ch.to_digit(16).expect("hex") as u64);
    }
    v
}

pub fn run() {
    let p = U512::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    let pp = params();
    let env = envelope();
    let r = pp.walk.r;
    let c = &mut Builder::new();
    let x: Vec<Q> = c.alloc_qubits(N);
    let y: Vec<Q> = c.alloc_qubits(N);
    let ox: Vec<BitId> = c.alloc_bits(N);
    let oy: Vec<BitId> = c.alloc_bits(N);
    let mut segs: Vec<Seg> = Vec::new();
    macro_rules! seg {
        ($name:expr, $checks:expr) => {{
            seg!($name, $checks, None);
        }};
        ($name:expr, $checks:expr, $debt:expr) => {{
            let ops = c.take_ops();
            segs.push(Seg {
                name: $name,
                ops,
                checks: $checks,
                debt: $debt,
            });
        }};
    }
    coord_sub(c, &x, &ox);
    coord_sub(c, &y, &oy);
    seg!(
        "coord",
        vec![(V::D, x.clone(), true), (V::Dy, y.clone(), true)]
    );
    let pk = walk::forward(c, &pp.walk, env, &x);
    seg!(
        "div_fwd",
        vec![(V::S, pk.s.clone(), false), (V::Dy, y.clone(), true)]
    );
    let lam = mulf(c, &y, &pk.s, r, true, MmRole::SlopeValue);
    seg!(
        "mm1",
        vec![(V::Lam, lam.clone(), true), (V::S, pk.s.clone(), false), (V::Dy, y.clone(), true)]
    );
    let m = hmr_all(c, &y);
    let d = walk::backward(c, &pp.walk, env, pk);
    seg!(
        "div_back",
        vec![(V::D, d.clone(), true), (V::Lam, lam.clone(), true)],
        Some((V::Dy, m.clone()))
    );
    let t = mulf(c, &lam, &d, 0, false, MmRole::NumeratorDebt);
    seg!("div_debt_product", vec![(V::Dy, t.clone(), true)], Some((V::Dy, m.clone())));
    pay_debt(c, &t, &m);
    mulf_inv(c, &lam, &d, 0, false, t, MmRole::NumeratorDebt);
    c.free_bit_vec(&m);
    seg!(
        "div_debt",
        vec![(V::D, d.clone(), true), (V::Lam, lam.clone(), true)]
    );
    coord_add3x(c, &d, &ox);
    sub_square(c, &d, &lam);
    let dp = d;
    seg!(
        "square",
        vec![(V::Dp, dp.clone(), true), (V::Lam, lam.clone(), true)]
    );
    let tmp = mulf(c, &lam, &dp, 0, false, MmRole::ValueProduct);
    seg!("mm4", vec![(V::Tmp, tmp.clone(), true), (V::Lam, lam.clone(), true), (V::Dp, dp.clone(), true)]);
    let m = hmr_all(c, &lam);
    let pk = walk::forward(c, &pp.walk, env, &dp);
    seg!(
        "mul_fwd",
        vec![(V::S2, pk.s.clone(), false), (V::Tmp, tmp.clone(), true)],
        Some((V::Lam, m.clone()))
    );
    let lam2 = mulf(c, &tmp, &pk.s, r, true, MmRole::SlopeDebt);
    seg!("mm5_product", vec![(V::Lam, lam2.clone(), true)], Some((V::Lam, m.clone())));
    pay_debt(c, &lam2, &m);
    mulf_inv(c, &tmp, &pk.s, r, true, lam2, MmRole::SlopeDebt);
    c.free_bit_vec(&m);
    seg!(
        "mm5",
        vec![(V::S2, pk.s.clone(), false), (V::Tmp, tmp.clone(), true)]
    );
    let dp = walk::backward(c, &pp.walk, env, pk);
    seg!(
        "mul_back",
        vec![(V::Dp, dp.clone(), true), (V::Tmp, tmp.clone(), true)]
    );
    coord_sub(c, &tmp, &oy);
    coord_rsub(c, &dp, &ox);
    seg!(
        "final",
        vec![(V::Yf, tmp.clone(), true), (V::Xf, dp.clone(), true)]
    );
    let (nq, nb) = c.i13_dims();
    eprintln!(
        "PAPROBE built nq={nq} peak={} segs={}",
        c.peak_total(),
        segs.len()
    );

    // shots
    let batches: usize = pa::knob("SKYCOF_PROBE_BATCHES")
        .map(|v| v.parse().unwrap())
        .unwrap_or(1);
    let mut inputs: Vec<[U512; 4]> = pa::knob("SKYCOF_PROBE_SHOTS")
        .map(|v| {
            v.split(';')
                .filter(|s| !s.trim().is_empty())
                .map(|s| {
                    let f: Vec<U512> = s.split(',').map(parse_hex).collect();
                    [f[0], f[1], f[2], f[3]]
                })
                .collect()
        })
        .unwrap_or_default();
    if let Some(path) = pa::knob("SKYCOF_PROBE_SHOTS_FILE") {
        let text = std::fs::read_to_string(path).expect("read frozen input file");
        inputs.extend(text.lines().filter(|s| !s.trim().is_empty()).map(|s| {
            let f: Vec<U512> = s.split(',').map(parse_hex).collect();
            assert_eq!(f.len(), 4, "frozen input needs tx,ty,ox,oy");
            [f[0], f[1], f[2], f[3]]
        }));
    }
    let given = inputs.len();
    let mut seed = 99u64;
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
    while inputs.len() < batches * 64 {
        inputs.push([rnd(), rnd(), rnd(), rnd()]);
    }
    let r2 = U512::from(2u64).pow_mod(U512::from(r as u64), p);
    let neg = |v: U512| (p - v).reduce_mod(p);
    let expect = |inp: &[U512; 4]| -> [U512; 9] {
        let [tx, ty, oxv, oyv] = *inp;
        let d = tx.add_mod(neg(oxv), p);
        let dy = ty.add_mod(neg(oyv), p);
        let di = d.inv_mod(p).unwrap();
        let s = neg(r2.mul_mod(di, p));
        let lam = dy.mul_mod(di, p);
        let dp = tx
            .add_mod(oxv.mul_mod(U512::from(2u64), p), p)
            .add_mod(neg(lam.mul_mod(lam, p)), p);
        let tmp = lam.mul_mod(dp, p);
        let s2 = neg(r2.mul_mod(dp.inv_mod(p).unwrap(), p));
        let yf = tmp.add_mod(neg(oyv), p);
        let xf = oxv.add_mod(neg(dp), p);
        [d, dy, s, lam, dp, tmp, s2, yf, xf]
    };
    let mut rd = {
        let mut h = sha3::Shake256::default();
        h.update(b"skycof-pa-probe");
        h.finalize_xof()
    };
    let mut sim = Simulator::new(nq, nb + 1, &mut rd);
    let mut first_fail: std::collections::BTreeMap<String, usize> = Default::default();
    let mut checkpoint_fail: std::collections::BTreeMap<String, usize> = Default::default();
    let mut final_phase_fail = 0usize;
    for bt in 0..inputs.len().div_ceil(64) {
        sim.clear_for_shot();
        let lo = bt * 64;
        let hi = (lo + 64).min(inputs.len());
        for (j, inp) in inputs[lo..hi].iter().enumerate() {
            for i in 0..N {
                if inp[0].bit(i) {
                    *sim.qubit_mut(x[i]) |= 1 << j;
                }
                if inp[1].bit(i) {
                    *sim.qubit_mut(y[i]) |= 1 << j;
                }
                if inp[2].bit(i) {
                    *sim.bit_mut(ox[i]) |= 1 << j;
                }
                if inp[3].bit(i) {
                    *sim.bit_mut(oy[i]) |= 1 << j;
                }
            }
        }
        let exps: Vec<[U512; 9]> = inputs[lo..hi].iter().map(expect).collect();
        let mut failed = vec![false; hi - lo];
        for sg in &segs {
            sim.apply_iter(sg.ops.iter());
            let mut expected_phase = 0u64;
            if let Some((value, outcomes)) = &sg.debt {
                for j in 0..hi - lo {
                    let measured_value = exps[j][*value as usize];
                    for (i, &b) in outcomes.iter().enumerate() {
                        if measured_value.bit(i) {
                            expected_phase ^= sim.bit(b) & (1u64 << j);
                        }
                    }
                }
            }
            let residual_phase = sim.phase ^ expected_phase;
            for j in 0..hi - lo {
                let mut why = Vec::new();
                for (v, wires, exact) in &sg.checks {
                    let mut got = U512::ZERO;
                    for (i, &q) in wires.iter().enumerate() {
                        if (sim.qubit(q) >> j) & 1 == 1 {
                            got.set_bit(i, true);
                        }
                    }
                    let want = exps[j][*v as usize];
                    if got.reduce_mod(p) != want {
                        why.push(format!("{}:value got={got:#x} want={want:#x}", *v as usize));
                    } else if *exact && got != want {
                        why.push(format!("{}:noncanon", *v as usize));
                    }
                }
                if (residual_phase >> j) & 1 == 1 {
                    why.push("phase".into());
                    if sg.name == "final" { final_phase_fail += 1; }
                }
                if !why.is_empty() {
                    *checkpoint_fail.entry(sg.name.to_string()).or_default() += 1;
                    let i = lo + j;
                    if i < given || !failed[j] {
                        eprintln!(
                            "PAPROBE shot {i}{} seg {} -> {}",
                            if i < given { "(given)" } else { "" },
                            sg.name,
                            why.join(",")
                        );
                    }
                    if !failed[j] {
                        *first_fail.entry(sg.name.to_string()).or_default() += 1;
                    }
                    failed[j] = true;
                }
            }
        }
    }
    eprintln!(
        "PAPROBE shots={} first-fail by segment: {:?}",
        inputs.len(),
        first_fail
    );
    eprintln!("PAPROBE checkpoint-fail={checkpoint_fail:?} final-phase-fail={final_phase_fail}");
}
