//! Lane FHD-LEFT censuses (integer model only, no gates):
//! 1. envelope: per class and slot parity, the reachable (h = pi >> 1, depth) pairs at slot start, max pi, max
//!    depth, max pi + depth;
//! 2. occupancy: lanes each register needs at slot start under the masked-ladder conventions, to price W = 257.
//! FHD_SHOTS (default 20000) shots, FHD_SEED.

use super::refmodel_double::{self as rmd, Ph, N};
use super::tests_double::Rng;
use std::collections::BTreeMap;

fn cls(p: Ph) -> usize {
    match p { Ph::Al => 0, Ph::Dv => 1, Ph::Co => 2, Ph::Rt => 3, Ph::Dn => 4 }
}
const CN: [&str; 5] = ["AL", "DV", "CO", "RT", "DN"];

#[test]
fn fhd_census() {
    let shots: usize = std::env::var("FHD_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(20000);
    let seed: u64 = std::env::var("FHD_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(9191);
    let slots = super::layout_double().s;
    let mut rng = Rng::new(seed);
    let pp = rmd::p();
    // pairs[parity][class] -> (h, depth) -> count
    let mut pairs: Vec<Vec<BTreeMap<(i32, usize), u64>>> = vec![vec![BTreeMap::new(); 5]; 2];
    let mut maxpi = [0i32; 5];
    let mut maxdep = [0usize; 5];
    let mut maxsum = [0i32; 5];
    // occupancy: D need, V need (V frame) histograms by class (value = lanes needed)
    let mut dneed: Vec<BTreeMap<u32, u64>> = vec![BTreeMap::new(); 5];
    let mut vneed: Vec<BTreeMap<u32, u64>> = vec![BTreeMap::new(); 5];
    let mut shots_d257 = 0u64;
    let mut shots_v257 = 0u64;
    let mut unfinished = 0u64;
    let mut kmax_hist: BTreeMap<i32, u64> = BTreeMap::new();
    let lay = super::layout_double();
    // per slot: min / max of the stored offset (b - 1 - base) over non-DONE shots
    let mut omin = vec![i64::MAX; slots];
    let mut omax = vec![i64::MIN; slots];
    for _ in 0..shots {
        let mut x = rng.below(256) % pp;
        if x == N::ZERO { x = N::from(1u64); }
        let mut m = rmd::St::new(x);
        let mut hit_d = false;
        let mut hit_v = false;
        let mut shot_k = 0i32;
        for sigma in 0..slots {
            let c = cls(m.ph);
            let par = sigma % 2; // pi parity class: pi odd at even slots
            let h = m.pi >> 1;
            let dep = m.stk.len();
            *pairs[par][c].entry((h, dep)).or_insert(0) += 1;
            maxpi[c] = maxpi[c].max(m.pi);
            maxdep[c] = maxdep[c].max(dep);
            maxsum[c] = maxsum[c].max(m.pi + dep as i32);
            if c == 1 || c == 2 { shot_k = shot_k.max(m.pi + dep as i32); }
            let blr = m.r.bit_len() as u32;
            let blcd = m.cd.bit_len() as u32;
            let blrv = m.rv.bit_len() as u32;
            let blcv = m.cv.bit_len() as u32;
            let b = m.b;
            let pi = m.pi.max(0) as u32;
            // D: value region top (exclusive) + cofactor
            let dtop = match m.ph {
                Ph::Al => b + 1,
                Ph::Dv => b + pi + 1,
                _ => blr,
            };
            let dn = dtop + blcd;
            // V (own frame): value / stack region top (exclusive) + cofactor
            let vtop = match m.ph {
                Ph::Al => (b + 1).saturating_sub(pi).max(blrv),
                Ph::Dv | Ph::Co => b + (dep as u32).max(1),
                _ => blrv,
            };
            let vn = vtop + blcv;
            if m.ph != Ph::Dn {
                let o = m.b as i64 - 1 - lay.base[sigma] as i64;
                omin[sigma] = omin[sigma].min(o);
                omax[sigma] = omax[sigma].max(o);
                *dneed[c].entry(dn).or_insert(0) += 1;
                *vneed[c].entry(vn).or_insert(0) += 1;
                if dn > 257 { hit_d = true; }
                if vn > 257 { hit_v = true; }
            }
            m.fwd(sigma);
        }
        if m.ph != Ph::Dn { unfinished += 1; }
        *kmax_hist.entry(shot_k).or_insert(0) += 1;
        if hit_d { shots_d257 += 1; }
        if hit_v { shots_v257 += 1; }
    }
    eprintln!("FHD census: {shots} shots, seed {seed}, {slots} slots, unfinished {unfinished}");
    for c in 0..5 {
        eprintln!("  {}: max pi {} max depth {} max pi+depth {}", CN[c], maxpi[c], maxdep[c], maxsum[c]);
    }
    eprintln!("  per-shot max (pi + depth) over DV/CO slots: {:?}", kmax_hist);
    for par in 0..2 {
        let mut all: BTreeMap<(i32, usize), u64> = BTreeMap::new();
        for c in 0..5 {
            for (k, v) in &pairs[par][c] { *all.entry(*k).or_insert(0) += v; }
            eprintln!("  slot parity {par} ({}): {} pairs (h, depth) for {}", if par == 0 { "pi odd" } else { "pi even" }, pairs[par][c].len(), CN[c]);
        }
        eprintln!("  slot parity {par}: {} distinct (h, depth) pairs over all classes", all.len());
        let mut maxd_by_h: BTreeMap<i32, usize> = BTreeMap::new();
        for (h, d) in all.keys() { let e = maxd_by_h.entry(*h).or_insert(0); *e = (*e).max(*d); }
        eprintln!("  slot parity {par}: max depth by h {:?}", maxd_by_h);
    }
    for c in 0..4 {
        let dmax = dneed[c].keys().last().copied().unwrap_or(0);
        let vmax = vneed[c].keys().last().copied().unwrap_or(0);
        let d258: u64 = dneed[c].range(258..).map(|(_, v)| v).sum();
        let v258: u64 = vneed[c].range(258..).map(|(_, v)| v).sum();
        let dtot: u64 = dneed[c].values().sum();
        eprintln!("  occupancy {}: D need max {dmax} (shot-slots > 257: {d258} of {dtot}); V need max {vmax} (> 257: {v258})", CN[c]);
        eprintln!("     D need tail {:?}", dneed[c].range(250..).collect::<Vec<_>>());
        eprintln!("     V need tail {:?}", vneed[c].range(250..).collect::<Vec<_>>());
    }
    let mut spread: BTreeMap<i64, usize> = BTreeMap::new();
    let mut worst = (0usize, 0i64, 0i64);
    for sg in 0..slots {
        if omax[sg] >= omin[sg] {
            let w = omax[sg] - omin[sg] + 1;
            *spread.entry(w).or_insert(0) += 1;
            if w > worst.2 - worst.1 + 1 || worst.2 < worst.1 { worst = (sg, omin[sg], omax[sg]); }
            if omin[sg] < 0 || omax[sg] >= 64 { eprintln!("  offset out of [0,64) at slot {sg}: [{}, {}]", omin[sg], omax[sg]); }
        }
    }
    eprintln!("  offset spread (max - min + 1) histogram over slots: {:?}; widest slot {} [{}, {}]", spread, worst.0, worst.1, worst.2);
    eprintln!("  shots with any D need > 257: {shots_d257}; any V need > 257: {shots_v257}");
}
