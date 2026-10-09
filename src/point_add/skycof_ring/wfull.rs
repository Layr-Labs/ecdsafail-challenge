//! Full-width (secp256k1) ring-walk check: `SKYCOF_RING_WALKTEST=full`.
//! Builds the forward walk and the walk back with a 256-wire passenger at the source envelope and cap
//! (`SKYCOF_RING_CAP`, default the point-add cap), reports peak and expected Toffoli per direction, then
//! simulates `SKYCOF_RING_BATCHES` x 64 random `d` and compares every lane with the classical prediction
//! of [`classify`] (empty = the circuit must be exact on that `d`).
use super::rwalk::WEnv;
use super::selftest::expected_ccx;
use super::wtest::{self, true_walk};
use ruint::Uint;

type U = Uint<512, 8>;

fn bits(x: U) -> usize {
    512 - x.leading_zeros()
}

/// Classical prediction of the failure modes of the circuit walk on `d` (empty = exact).
pub fn classify(d: U, env: &WEnv) -> Vec<String> {
    let n = env.n;
    let p = U::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    let (recs, _, _, park, fold_ok) = true_walk(d, p, n, env.r, env.fold_w);
    let mut out = Vec::new();
    match park {
        None => out.push("unparked at R".to_string()),
        Some(k) => {
            if k < env.tp {
                out.push(format!("park {k} before TP"));
            }
            if env.r - k > (1usize << env.odo_bits) - 1 {
                out.push("odometer overflow".into());
            }
        }
    }
    if !fold_ok {
        out.push("fold".into());
    }
    let inr = |x: usize, r: &super::ring::Rng| x >= r.lo && x <= r.hi;
    for (t, rc) in recs.iter().enumerate() {
        if let Some(e) = rc.entry {
            match &env.z[t] {
                None => out.push(format!("t{t}: no ring window")),
                Some(z) => {
                    let zs = [z.ka, z.ua, z.vb, z.kap, z.uap, z.vbp];
                    for f in 0..6 {
                        if !inr(e[f], &zs[f]) {
                            out.push(format!("t{t}: ring window f{f} {} not in {:?}", e[f], zs[f]));
                        }
                    }
                }
            }
        }
        if t >= 1 {
            if let Some(q) = rc.post {
                match &env.dz[t] {
                    None => out.push(format!("t{t}: no decoder window")),
                    Some(z) => {
                        if !inr(q[0], &z.ka) {
                            out.push(format!("t{t}: decoder ka {}", q[0]));
                        }
                        if !inr(q[1], &z.vb) {
                            out.push(format!("t{t}: decoder vb {}", q[1]));
                        }
                        if !inr(q[2], &z.rb) {
                            out.push(format!("t{t}: decoder rb {}", q[2]));
                        }
                    }
                }
            }
        }
        if out.len() > 4 {
            break;
        }
    }
    // park-test false positives and history
    {
        let mut st = (d, p, U::ZERO, U::from(1u64));
        for t in 0..env.r {
            let (u, v, s, r) = st;
            if u.is_zero() {
                break;
            }
            st = if !u.bit(0) {
                (u >> 1usize, v, s << 1usize, r)
            } else if u >= v {
                ((u - v) >> 1usize, v, s << 1usize, r + s)
            } else {
                ((v - u) >> 1usize, u, r << 1usize, r + s)
            };
            if t >= env.tp && !st.0.is_zero() && st.1 == U::from(1u64) {
                let all = (n - 1 - env.park_j..n - 1).all(|j| st.3.bit(j) == env.p[j]);
                if all {
                    out.push(format!("t{t}: park test false positive"));
                }
            }
        }
    }
    let (hs, sound) = wtest::pushes(d, p, n, env);
    if !sound {
        out.push("decoder unsound".into());
    }
    for t in 0..env.r {
        if hs[t] as usize > env.h[t] {
            out.push(format!("t{t}: history {} > {}", hs[t], env.h[t]));
            break;
        }
    }
    let _ = bits;
    out
}

fn rng_next(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

pub fn run() {
    let env = super::pointadd::envelope().clone();
    let p = U::from_limbs_slice(&crate::point_add::SECP256K1_P.into_limbs());
    let t0 = std::time::Instant::now();
    super::rwalk::ACCT.with(|x| *x.borrow_mut() = Some(Vec::new()));
    let bt = wtest::build(&env, 256);
    let acct = bt.acct_f.clone().unwrap();
    let (tf, tb) = (expected_ccx(&bt.ops_f), expected_ccx(&bt.ops_b));
    {
        // forward components (push is nested inside decoder: reported separately and subtracted)
        let mut by: std::collections::BTreeMap<&str, f64> = Default::default();
        for &(nm, a, b) in &acct {
            if b <= bt.ops_f.len() {
                *by.entry(nm).or_default() += expected_ccx(&bt.ops_f[a..b]);
            }
        }
        for k in ["push", "d_capture", "d_rb"] {
            if let Some(p) = by.get(k).copied() {
                *by.get_mut("decoder").unwrap() -= p;
            }
        }
        let tot: f64 = by.values().sum();
        let parts: Vec<String> = by.iter().map(|(k, v)| format!("\"{k}\":{v:.0}")).collect();
        println!("{{\"kind\":\"skycof-ring-walk-fwd-parts\",{},\"sum\":{tot:.0}}}", parts.join(","));
    }
    println!("{{\"kind\":\"skycof-ring-walk-full\",\"cap\":{:?},\"peak\":{},\"ops_f\":{},\"ops_b\":{},\"exp_toffoli_fwd\":{tf:.1},\"exp_toffoli_back\":{tb:.1},\"build_secs\":{:.1}}}",
             env.cap, bt.peak, bt.ops_f.len(), bt.ops_b.len(), t0.elapsed().as_secs_f64());
    let batches: usize = std::env::var("SKYCOF_RING_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    if batches == 0 {
        return;
    }
    let mut seed: u64 = std::env::var("SKYCOF_RING_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0x5eed);
    let mut ds = Vec::new();
    while ds.len() < 64 * batches {
        let mut v = U::ZERO;
        for i in 0..4 {
            v |= U::from(rng_next(&mut seed)) << (64 * i);
        }
        let v = v.reduce_mod(p);
        if !v.is_zero() {
            ds.push(v);
        }
    }
    let bad = wtest::simulate(&bt, &env, p, &ds, 77);
    let mut conf = [0usize; 4];
    let badset: std::collections::HashMap<usize, String> = bad.into_iter().collect();
    for (i, &d) in ds.iter().enumerate() {
        let pred = classify(d, &env);
        let act = badset.get(&i);
        conf[(act.is_some() as usize) * 2 + (!pred.is_empty()) as usize] += 1;
        if act.is_some() != !pred.is_empty() {
            eprintln!("WALKFULL mismatch d={d:#x} actual={act:?} predicted={pred:?}");
        } else if let Some(a) = act {
            eprintln!("WALKFULL predicted failure d={d:#x} actual={a} predicted={pred:?}");
        }
    }
    println!("{{\"kind\":\"skycof-ring-walk-sim\",\"walks\":{},\"ok_ok\":{},\"ok_predbad\":{},\"bad_predok\":{},\"bad_bad\":{},\"secs\":{:.1}}}",
             ds.len(), conf[0], conf[1], conf[2], conf[3], t0.elapsed().as_secs_f64());
}
