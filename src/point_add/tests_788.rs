//! Lane FHD-788 designer (integer model only, no gates): census of the (phase, slot parity, h, depth, boundary|mid)
//! states the froghop-double walks visit, to size and price a 7-lane joint (h, depth) code.
//! Env: SC_SHOTS (walks, default 200000), SC_SEED, SC_OUT (output prefix, default /tmp/c788).
//! Writes `<SC_OUT>_states.tsv` (state -> distinct walks visiting it) and `<SC_OUT>_rare.txt` (per walk with a state
//! of 2h + pk + d >= 17 in DV / CO: the walk's distinct rare states), plus `<SC_OUT>_maxs.tsv` (per-walk max pi + d).
//! Mid-slot convention as `t789_tails`: (phase_pre, h_pre, depth_post) after `fwd` (depth moves at S4 / S6 before pi
//! moves at S9).

use super::refmodel_double::{self as rmd, Ph, N};
use super::tests_double::Rng;
use std::io::Write;

fn walk(rng: &mut Rng, pp: &N) -> rmd::St {
    let mut x = rng.below(256) % *pp;
    if x == N::ZERO {
        x = N::from(1u64);
    }
    rmd::St::new(x)
}

fn phi(p: Ph) -> usize {
    match p {
        Ph::Al => 0,
        Ph::Dv => 1,
        Ph::Co => 2,
        Ph::Rt => 3,
        Ph::Dn => 4,
    }
}

const NH: usize = 32;
const ND: usize = 64;
fn key(ph: usize, pk: usize, h: usize, d: usize, t: usize) -> usize {
    ((((ph * 2 + pk) * NH + h.min(NH - 1)) * ND + d.min(ND - 1)) * 2) + t
}

#[test]
fn c788_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78801);
    let out = std::env::var("SC_OUT").unwrap_or_else(|_| "/tmp/c788".into());
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let nk = 5 * 2 * NH * ND * 2;
    let mut cnt = vec![0u64; nk];
    let mut last = vec![u32::MAX; nk];
    let mut rare = std::io::BufWriter::new(std::fs::File::create(format!("{out}_rare.txt")).unwrap());
    let mut hmax: std::collections::BTreeMap<i32, u64> = Default::default();
    let mut unfinished = 0u64;
    for w in 0..shots {
        let wid = w as u32;
        let mut m = walk(&mut rng, &pp);
        let mut rs: Vec<usize> = vec![];
        let mut maxs = 0i32;
        for sigma in 0..lay.s {
            let pk = (sigma % 2 == 0) as usize;
            debug_assert!(m.ph == Ph::Dn || (m.pi as usize) % 2 == pk);
            let ph = phi(m.ph);
            let h = (m.pi >> 1) as usize;
            let d = m.stk.len();
            let mut rec = |ph: usize, h: usize, d: usize, t: usize, rs: &mut Vec<usize>, maxs: &mut i32| {
                let k = key(ph, pk, h, d, t);
                if last[k] != wid {
                    last[k] = wid;
                    cnt[k] += 1;
                    if (ph == 1 || ph == 2) && 2 * h + pk + d >= 17 {
                        rs.push(k);
                    }
                }
                if ph == 1 || ph == 2 {
                    *maxs = (*maxs).max((2 * h + pk + d) as i32);
                }
            };
            rec(ph, h, d, 0, &mut rs, &mut maxs);
            m.fwd(sigma);
            rec(ph, h, m.stk.len(), 1, &mut rs, &mut maxs);
        }
        if m.ph != Ph::Dn {
            unfinished += 1;
        }
        *hmax.entry(maxs).or_insert(0) += 1;
        if !rs.is_empty() {
            let v: Vec<String> = rs.iter().map(|k| k.to_string()).collect();
            writeln!(rare, "{}", v.join(" ")).unwrap();
        }
    }
    let mut f = std::fs::File::create(format!("{out}_states.tsv")).unwrap();
    writeln!(f, "# shots {shots} seed {seed}\nph\tpk\th\td\tt\twalks").unwrap();
    for ph in 0..5 {
        for pk in 0..2 {
            for h in 0..NH {
                for d in 0..ND {
                    for t in 0..2 {
                        let c = cnt[key(ph, pk, h, d, t)];
                        if c > 0 {
                            writeln!(f, "{ph}\t{pk}\t{h}\t{d}\t{t}\t{c}").unwrap();
                        }
                    }
                }
            }
        }
    }
    let mut f = std::fs::File::create(format!("{out}_maxs.tsv")).unwrap();
    writeln!(f, "# shots {shots} seed {seed} unfinished {unfinished}\nmaxs\twalks").unwrap();
    for (k, v) in &hmax {
        writeln!(f, "{k}\t{v}").unwrap();
    }
    eprintln!("C788 census seed {seed}: {shots} walks, unfinished {unfinished}, out {out}_*");
}
