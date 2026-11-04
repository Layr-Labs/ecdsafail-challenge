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

/// TJ-lane census (integer model only): per-walk max of the stored boundary offset u = (b - 1) - base(sigma) over all
/// slots, to price BB = 5 (u < 32) against BB = 6 (u < 64). Env: SC_SHOTS, SC_SEED.
#[test]
fn tj_bq_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78801);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let mut hist = vec![0u64; 300];
    let mut neg = 0u64;
    let mut slot_ge32 = vec![0u64; lay.s];
    let mut per_slot_max = vec![0i64; lay.s];
    for _ in 0..shots {
        let mut m = walk(&mut rng, &pp);
        let mut mx = i64::MIN;
        for sigma in 0..lay.s {
            let u = m.b as i64 - 1 - lay.base[sigma] as i64;
            if u < 0 { neg += 1; }
            if u >= 32 { slot_ge32[sigma] += 1; }
            if u > per_slot_max[sigma] { per_slot_max[sigma] = u; }
            mx = mx.max(u);
            m.fwd(sigma);
        }
        hist[(mx.max(0) as usize).min(299)] += 1;
    }
    let mut out = String::new();
    let mut cum = 0u64;
    for (u, c) in hist.iter().enumerate().rev() {
        cum += c;
        if *c > 0 && u >= 24 { out.push_str(&format!("maxu={u} walks={c} walks_with_max>=u={cum}\n")); }
    }
    let n32: u64 = hist[32..].iter().sum();
    let n40: u64 = hist[40..].iter().sum();
    let n48: u64 = hist[48..].iter().sum();
    let n64: u64 = hist[64..].iter().sum();
    out.push_str(&format!("walks {shots}: maxu>=32 {n32} ({:.4}%), >=40 {n40}, >=48 {n48}, >=64 {n64}, negative-u events {neg}\n",
        100.0 * n32 as f64 / shots as f64));
    let first32 = slot_ge32.iter().position(|&c| c > 0);
    let last32 = slot_ge32.iter().rposition(|&c| c > 0);
    out.push_str(&format!("slots with any u>=32: first {first32:?} last {last32:?}; per-slot max u (every 40th slot): "));
    for s in (0..lay.s).step_by(40) { out.push_str(&format!("{}:{} ", s, per_slot_max[s])); }
    out.push(0x0a as char);
    std::fs::write("/tmp/tj-lane/bq_census.txt", &out).unwrap();
    eprintln!("{out}");
}


/// TJ-lane census (integer model only): the lanes the packed D and V registers need per slot, raw (value + cofactor
/// + stack bits) and with the PLAN-T parity lane, to price WD = 257. Env: SC_SHOTS, SC_SEED.
#[test]
fn tj_width_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78801);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let bl = |x: &N| x.bit_len() as i64;
    let mut h: Vec<Vec<u64>> = vec![vec![0u64; 400]; 4];
    let mut vslack_at_d258 = vec![0u64; 40];
    let mut d258_phase = [0u64; 5];
    let mut d258_first_slot = vec![0u64; lay.s];
    for _ in 0..shots {
        let mut m = walk(&mut rng, &pp);
        let mut mx = [0i64; 4];
        let mut flagged = false;
        for sigma in 0..lay.s {
            let b = m.b as i64;
            let pi = m.pi as i64;
            let dep = m.stk.len() as i64;
            let draw = bl(&m.r) + bl(&m.cd);
            let vraw = bl(&m.rv).max(b + dep) + bl(&m.cv);
            let (dpar, vpar) = match m.ph {
                Ph::Al | Ph::Dn => (draw, vraw.max(b + 1 + bl(&m.cv))),
                Ph::Dv => (draw, vraw.max(b + (pi + dep).max(1) + 1 + bl(&m.cv))),
                Ph::Co => (draw.max(b + (pi + dep - 1).max(1) + bl(&m.cd)), vraw),
                Ph::Rt => (draw.max(b + 1 + bl(&m.cd)), vraw),
            };
            for (k, v) in [draw, dpar, vraw, vpar].iter().enumerate() { mx[k] = mx[k].max(*v); }
            if dpar >= 258 {
                let sl = (258 - vraw).clamp(0, 39) as usize;
                vslack_at_d258[sl] += 1;
                d258_phase[match m.ph { Ph::Al => 0, Ph::Dv => 1, Ph::Co => 2, Ph::Rt => 3, Ph::Dn => 4 }] += 1;
                if !flagged { d258_first_slot[sigma] += 1; flagged = true; }
            }
            m.fwd(sigma);
        }
        for k in 0..4 { h[k][mx[k].clamp(0, 399) as usize] += 1; }
    }
    let mut out = String::new();
    for (k, name) in ["D raw", "D with parity", "V raw", "V with parity"].iter().enumerate() {
        let mut cum = 0u64;
        let mut parts = vec![];
        for n in (254..262).rev() { cum += h[k][n]; parts.push(format!(">={n}:{cum}")); }
        out.push_str(&format!("{name}: {} (walks {shots}; walks with max > 261: {})\n", parts.join(" "), h[k][262..].iter().sum::<u64>()));
    }
    out.push_str(&format!("slot-events with D+parity >= 258 by phase [AL,DV,CO,RT,DN]: {:?}\n", d258_phase));
    out.push_str("V raw slack (258 - Vraw) at those events: ");
    for (s, c) in vslack_at_d258.iter().enumerate() { if *c > 0 { out.push_str(&format!("{s}:{c} ")); } }
    out.push_str("\nfirst slot of a D+parity>=258 event (walk count by slot, nonzero only, first 15): ");
    let mut n = 0;
    for (s, c) in d258_first_slot.iter().enumerate() { if *c > 0 && n < 15 { out.push_str(&format!("{s}:{c} ")); n += 1; } }
    out.push_str("\n");
    std::fs::write("/tmp/tj-lane/width_census.txt", &out).unwrap();
    eprintln!("{out}");
}

/// TJ-lane census (integer model only): at every CO / RT slot boundary, is the V-frame lane the parity uses in DV
/// (b + max(pi + dep, 1)) and the AL lane (b) free of rv, stack bits and cv? And how many free V-frame lanes exist.
#[test]
fn tj_par_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78801);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let bl = |x: &N| x.bit_len() as i64;
    let w = super::froghop_double::WD as i64;
    let mut ev = [0u64; 2]; // CO, RT boundary events
    let mut dvlane_free = [0u64; 2];
    let mut blane_free = [0u64; 2];
    let mut lane_bdep_free = [0u64; 2]; // lane b + dep (first lane above the stack)
    let mut min_free = [i64::MAX; 2];
    let mut walks_bad_dv = 0u64;
    let mut walks_bad_bdep = 0u64;
    for _ in 0..shots {
        let mut m = walk(&mut rng, &pp);
        let (mut bad_dv, mut bad_bdep) = (false, false);
        for sigma in 0..lay.s {
            let k = match m.ph { Ph::Co => 0, Ph::Rt => 1, _ => 9 };
            if k < 2 {
                let b = m.b as i64;
                let pi = m.pi as i64;
                let dep = m.stk.len() as i64;
                let lo = bl(&m.rv).max(b + dep); // first lane above rv and the stack bits
                let hi = w - bl(&m.cv); // cv's LSB lane
                let free = |l: i64| l >= lo && l < hi;
                ev[k] += 1;
                min_free[k] = min_free[k].min(hi - lo);
                let ldv = b + (pi + dep).max(1);
                if free(ldv) { dvlane_free[k] += 1; } else { bad_dv = true; }
                if free(b) { blane_free[k] += 1; }
                if free(b + dep) { lane_bdep_free[k] += 1; } else { bad_bdep = true; }
            }
            m.fwd(sigma);
        }
        if bad_dv { walks_bad_dv += 1; }
        if bad_bdep { walks_bad_bdep += 1; }
    }
    let out = format!("CO/RT boundary events {:?}; DV-lane (b+max(pi+dep,1)) free {:?}; lane b free {:?}; lane b+dep free {:?}; min free V lanes {:?}; walks with DV-lane not free {}; walks with b+dep not free {} (walks {})\n",
        ev, dvlane_free, blane_free, lane_bdep_free, min_free, walks_bad_dv, walks_bad_bdep, shots);
    std::fs::write("/tmp/tj-lane/par_census.txt", &out).unwrap();
    eprintln!("{out}");
}

/// TJ-lane census: at CO boundaries where D is tight (bl(r)+bl(cd) = 257, so the parity cannot stay in D at 257
/// lanes), which V-frame lane is free: b+dep, b, the DV lane; and are D-tight and V-tight CO events disjoint.
#[test]
fn tj_joint_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78801);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let bl = |x: &N| x.bit_len() as i64;
    let w = super::froghop_double::WD as i64;
    let (mut co, mut dtight, mut vtight, mut both) = (0u64, 0u64, 0u64, 0u64);
    let (mut bdep_free_dt, mut b_free_dt, mut dv_free_dt) = (0u64, 0u64, 0u64);
    let mut walks_both = 0u64;
    for _ in 0..shots {
        let mut m = walk(&mut rng, &pp);
        let mut wb = false;
        for sigma in 0..lay.s {
            if m.ph == Ph::Co {
                let b = m.b as i64; let pi = m.pi as i64; let dep = m.stk.len() as i64;
                let lo = bl(&m.rv).max(b + dep); let hi = w - bl(&m.cv);
                let free = |l: i64| l >= lo && l < hi;
                let dt = bl(&m.r) + bl(&m.cd) >= 257; let vt = hi - lo <= 0;
                co += 1; if dt { dtight += 1; } if vt { vtight += 1; } if dt && vt { both += 1; wb = true; }
                if dt { if free(b + dep) { bdep_free_dt += 1; } if free(b) { b_free_dt += 1; } if free(b + (pi + dep).max(1)) { dv_free_dt += 1; } }
            }
            m.fwd(sigma);
        }
        if wb { walks_both += 1; }
    }
    let out = format!("CO events {co}: D-tight {dtight}, V-tight {vtight}, both {both} (walks with both {walks_both}); at D-tight events: lane b+dep free {bdep_free_dt}, lane b free {b_free_dt}, DV lane free {dv_free_dt} (walks {shots})\n");
    std::fs::write("/tmp/tj-lane/joint_census.txt", &out).unwrap();
    eprintln!("{out}");
}

/// ds-tj787 census (integer model only): at every RT0 event (slot start, ph == Rt, pi == 0, so sigma odd) measure
/// whether the 64-window [base+1, base+64] of the Astra routing is fully inside (a) V's free gap and (b) D's free
/// gap, i.e. whether the conjugated 257-bank swap is value-exact on the reachable model states.
/// Conditions (window base B = base+1, top lane B+63 = base+64):
///   V side: shift region [b+1, base+64] must be zero lanes: b >= bl(rv) and base+64 < 258-bl(cv)
///   D side: shift region [b, base+64] must be zero lanes: b >= bl(r) and base+64 < 257-bl(cd)
///   plus the window must fit the registers: base <= 192 (D top lane 256), base <= 193 (V top lane 257).
#[test]
fn ds_rt0_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78701);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let bl = |x: &N| x.bit_len() as i64;
    let mut events = 0u64;
    let mut v_bottom_ok = 0u64; // b >= bl(rv)
    let mut d_bottom_ok = 0u64; // b >= bl(r)
    let mut v_top_ok = 0u64; // base+64 < 258-bl(cv)  <=> bl(cv) <= 193-base
    let mut d_top_ok = 0u64; // base+64 < 257-bl(cd)  <=> bl(cd) <= 192-base
    let mut d_fit = 0u64; // base <= 192
    let mut v_fit = 0u64; // base <= 193
    let mut all_ok = 0u64;
    let mut walks_all = 0u64;
    let mut max_cv_excess = 0i64;
    let mut max_cd_excess = 0i64;
    let mut first_bad: Option<(usize, usize, i64, i64, i64, i64, i64)> = None;
    for w in 0..shots {
        let mut m = walk(&mut rng, &pp);
        if super::tests_789::max_q_bits(&m.rv) >= super::froghop_double::QBAD {
            continue; // off-model shot
        }
        let mut wall_ok = true;
        for sigma in 0..lay.s {
            if m.ph == Ph::Rt && m.pi == 0 {
                let b = m.b as i64;
                let base = lay.base[sigma] as i64;
                events += 1;
                let blr = bl(&m.r);
                let blrv = bl(&m.rv);
                let blcd = bl(&m.cd);
                let blcv = bl(&m.cv);
                let u = b - 1 - base;
                let h = (base + 64).min(257);
                // Exactness conditions for the packed 257/258 swap at RT0 (parity preserved at V[b]):
                //  address window: u in [0, 63], b <= H (clipped window), b >= 1, b <= 256
                //  V side: lane b not an rv bit (b >= bl(rv));  D side: lane b above r (b >= bl(r))
                //          and the inserted hole lane must not collide with cd (b + bl(cd) <= 257)
                let vb = b >= blrv;
                let db = b >= blr;
                let vtop = blcv <= 257 - h; // the tree region [b+1, H] free of cv is NOT required: the route is a
                                            // permutation for any values; the only V requirement is b >= bl(rv).
                let dt = b + blcd <= 257;
                let win = u >= 0 && u < 64 && b >= 1 && b <= 256 && b <= h;
                let ok = vb && db && dt && win && vtop;
                v_bottom_ok += vb as u64;
                d_bottom_ok += db as u64;
                v_top_ok += vtop as u64;
                d_top_ok += dt as u64;
                d_fit += (base <= 192) as u64;
                v_fit += (base <= 193) as u64;
                all_ok += ok as u64;
                max_cv_excess = max_cv_excess.max(blcv - (257 - h));
                max_cd_excess = max_cd_excess.max(blcd - (257 - b));
                if !ok {
                    wall_ok = false;
                    if first_bad.is_none() {
                        first_bad = Some((w, sigma, b, base, blr, blrv, blcd));
                    }
                }
            }
            m.fwd(sigma);
        }
        walks_all += wall_ok as u64;
    }
    let out = format!(
        "RT0 events {events}: V-bottom(b>=bl(rv)) {v_bottom_ok}, D-bottom(b>=bl(r)) {d_bottom_ok}, \
         V-top(bl(cv)<=193-base) {v_top_ok}, D-top(bl(cd)<=192-base) {d_top_ok}, D-fit(base<=192) {d_fit}, \
         V-fit(base<=193) {v_fit}, ALL {all_ok}; walks with every rt0 OK {walks_all} (shots {shots}); \
         max cv excess {max_cv_excess}, max cd excess {max_cd_excess}; first bad {first_bad:?}\n"
    );
    std::fs::write("/tmp/ds-tj787/rt0_census.txt", &out).unwrap();
    eprintln!("{out}");
}

/// ds-tj787 787-design census (integer model only). Validates the existing sched windows against the model and
/// computes the per-slot windows the redesigned M2/M3/RT0 scans need, plus the freeness conditions for exactness.
///
/// Audiences at slot boundary states:
///   RT0 (S5 swap): ph == Rt && pi == 0.  u = b-1-base, H = min(base+64, 257).
///     V exact: b >= bl(rv) && bl(cv) <= 257 - H;  D exact: b >= bl(r) && bl(cd) <= 257 - b;  u in [0, 63], b <= 256.
///   M2 (S4 DV0->CO): ph == Dv && pi == 0, k = dep. New D target b, new V source b + max(dep,1).
///     D target free (257-wide D): bl(r) <= b && bl(cd) <= 256 - b. Old target b+max(dep,1)-1 should sit in [lc, p2hi].
///   M3 (S7 CO->RT): ph == Co && stk.len() == 1. New D source b; new V target physical (b + pi) mod 258
///     (the shot's CO pi; S9 relabels by -1, so the RT frame lane is V-frame b). Free at the M3 instant (stack
///     already popped, so depth 0): V-frame b free: b >= bl(rv) && bl(cv) <= 257 - b; D source free: same as M2.
///     Old source b+pi-1 should sit in [lc, p2hi]; old target b in [lob, hib) with lob=(lc+1).saturating_sub(pihi),
///     hib=(p2hi+1).min(w), pihi=jw.min(lv).
///   Probe / erase (S3, turning AL shots: ph == Al && r < rv<<pi): probe lane b+pi in [pb0, pb1), erase lane
///     b+pi-1 in [pe0, pe1).
///   S2 ladder: DV shots, active top lane b+pi (the lane-257 cell is dormant because r >= rv<<pi on every DV shot;
///     must be <= 257 on model).
#[test]
fn ds_787_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78701);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let bl = |x: &N| x.bit_len() as i64;
    let w = super::froghop_double::WD as i64;
    let s = lay.s;
    let mut rt0_events = 0u64;
    let mut rt0_bad = 0u64;
    let mut rt0_min_u = vec![i64::MAX; s];
    let mut rt0_max_u = vec![i64::MIN; s];
    let mut m2_min_b = vec![i64::MAX; s];
    let mut m2_max_b = vec![i64::MIN; s];
    let mut m2_min_v = vec![i64::MAX; s];
    let mut m2_max_v = vec![i64::MIN; s];
    let mut m2_bad_d = 0u64;
    let mut m2_bad_oldwin = 0u64;
    let mut m3_min_b = vec![i64::MAX; s];
    let mut m3_max_b = vec![i64::MIN; s];
    let mut m3_min_v = vec![i64::MAX; s];
    let mut m3_max_v = vec![i64::MIN; s];
    let mut m3_bad_v = 0u64;
    let mut m3_bad_d = 0u64;
    let mut m3_bad_oldsrc = 0u64;
    let mut m3_bad_oldtgt = 0u64;
    let mut probe_bad = 0u64;
    let mut erase_bad = 0u64;
    let mut s2_bad = 0u64;
    let mut m2_first_bad: Option<(usize, i64, i64, i64, i64, u8, u8)> = None;
    for _ in 0..shots {
        let mut m = walk(&mut rng, &pp);
        if super::tests_789::max_q_bits(&m.rv) >= super::froghop_double::QBAD {
            continue; // off-model shot
        }
        for sigma in 0..s {
            let b = m.b as i64;
            let pi = m.pi as i64;
            let dep = m.stk.len() as i64;
            let base = lay.base[sigma] as i64;
            let row = &lay.rows[sigma];
            let (lc, p2hi, pb0, pb1, pe0, pe1) = (row[3] as i64, row[4] as i64, row[5] as i64, row[6] as i64, row[7] as i64, row[8] as i64);
            match m.ph {
                Ph::Rt if pi == 0 => {
                    let u = b - 1 - base;
                    let h = (base + 64).min(257);
                    rt0_events += 1;
                    rt0_min_u[sigma] = rt0_min_u[sigma].min(u);
                    rt0_max_u[sigma] = rt0_max_u[sigma].max(u);
                    let ok = u >= 0 && u < 64 && b >= 1 && b <= 256 && b <= h
                        && b >= bl(&m.rv)
                        && b >= bl(&m.r) && b + bl(&m.cd) <= 257;
                    if !ok {
                        rt0_bad += 1;
                    }
                }
                Ph::Dv if pi == 0 => {
                    let k = dep.max(1);
                    let tgt = b + k - 1;
                    let vsrc = b + k;
                    if dep <= 1 {
                        // k<=1: the new three-way move. r_co = r after the final pop (r - rv if r >= rv).
                        let r_co = if m.r >= m.rv { &m.r - &m.rv } else { m.r.clone() };
                        let r_top = r_co.bit((b - 1) as usize) as u8;
                        let cd_top = m.cd.bit((256 - b) as usize) as u8;
                        let (r1, c1) = (r_top == 1, cd_top == 1);
                        let bad = if r1 {
                            // parity -> D[b]
                            bl(&r_co) > b || cd_top == 1
                        } else if c1 {
                            // parity -> D[b-1]
                            bl(&r_co) > b - 1 || m.cd.bit((257 - b) as usize)
                        } else {
                            // parity stays at V-frame b (rides the frame through CO): free at every CO slot.
                            // Track the cv growth through the CO span.
                            let mut mm = rmd::St { r: r_co.clone(), cd: m.cd.clone(), rv: m.rv.clone(),
                                                  cv: m.cv.clone(), pi: m.pi, ph: Ph::Dv, stk: m.stk.clone(),
                                                  b: m.b, cnt: m.cnt, par: m.par, refl: m.refl };
                            let mut bad = b < bl(&mm.rv);
                            mm.fwd(sigma);
                            let mut guard = 0usize;
                            while mm.ph == Ph::Co && guard < 64 {
                                if b + bl(&mm.cv) > 257 {
                                    bad = true;
                                }
                                mm.fwd(sigma + 1 + guard);
                                guard += 1;
                            }
                            if mm.ph != Ph::Rt {
                                bad = true;
                            }
                            bad
                        };
                        if bad {
                            m2_bad_d += 1;
                            if m2_first_bad.is_none() {
                                m2_first_bad = Some((sigma, b, dep, bl(&r_co), bl(&m.cd), r_top, cd_top));
                            }
                        }
                        m2_min_b[sigma] = m2_min_b[sigma].min(b - 1);
                        m2_max_b[sigma] = m2_max_b[sigma].max(b - 1);
                    } else {
                        // k>=2: today's lane D[b+k-1] (validated free in ds_co_host_census)
                        m2_min_v[sigma] = m2_min_v[sigma].min(vsrc);
                        m2_max_v[sigma] = m2_max_v[sigma].max(vsrc);
                    }
                    if tgt < lc || tgt > p2hi {
                        m2_bad_oldwin += 1;
                    }
                }
                Ph::Co if dep == 1 => {
                    let vphy = (b + pi).rem_euclid(258);
                    m3_min_b[sigma] = m3_min_b[sigma].min(b);
                    m3_max_b[sigma] = m3_max_b[sigma].max(b);
                    let lo = m3_min_v[sigma];
                    let hi = m3_max_v[sigma];
                    if lo == i64::MAX {
                        m3_min_v[sigma] = vphy;
                        m3_max_v[sigma] = vphy;
                    } else if lo > hi {
                        // current range is wrapped
                        let (nlo, nhi) = if vphy < lo { (vphy, hi) } else if vphy > hi { (lo, vphy) } else { (lo, hi) };
                        m3_min_v[sigma] = nlo;
                        m3_max_v[sigma] = nhi;
                    } else if vphy < lo || vphy > hi {
                        // extension may wrap: keep the range of smaller span
                        let span1 = if vphy < lo { hi - vphy } else { vphy - lo };
                        let span2 = if vphy < lo { 258 + lo - vphy + hi } else { 258 + vphy - hi + lo };
                        if span1 <= span2 {
                            m3_min_v[sigma] = m3_min_v[sigma].min(vphy);
                            m3_max_v[sigma] = m3_max_v[sigma].max(vphy);
                        } else {
                            let (nlo, nhi) = if vphy < lo { (vphy, hi) } else { (lo, vphy) };
                            m3_min_v[sigma] = nlo;
                            m3_max_v[sigma] = nhi;
                        }
                    }
                    if b < bl(&m.rv) || bl(&m.cv) > 257 - b {
                        m3_bad_v += 1;
                    }
                    if bl(&m.r) > b || bl(&m.cd) > 256 - b {
                        m3_bad_d += 1;
                    }
                    let pihi = (row[1] as i64).min(row[0] as i64);
                    let lob = (lc + 1 - pihi).max(0);
                    let hib = (p2hi + 1).min(w);
                    if b + pi - 1 < lc || b + pi - 1 > p2hi {
                        m3_bad_oldsrc += 1;
                    }
                    if b < lob || b >= hib {
                        m3_bad_oldtgt += 1;
                    }
                }
                Ph::Al => {
                    if m.r < (m.rv << pi) {
                        if b + pi < pb0 || b + pi >= pb1 {
                            probe_bad += 1;
                        }
                        if b + pi - 1 < pe0 || b + pi - 1 >= pe1 {
                            erase_bad += 1;
                        }
                    }
                }
                Ph::Dv => {
                    if b + pi > 257 {
                        s2_bad += 1;
                    }
                }
                _ => {}
            }
            m.fwd(sigma);
        }
    }
    let mut out = String::new();
    out.push_str(&format!("rt0 events {rt0_events}, bad {rt0_bad}\n"));
    out.push_str(&format!("m2 D-target-free bad {m2_bad_d}, old-window bad {m2_bad_oldwin}\n"));
    out.push_str(&format!("m2 first bad (sigma,b,k,blrco,blcd,r_top,cd_top) {m2_first_bad:?}\n"));
    out.push_str(&format!("m3 V-free bad {m3_bad_v}, D-free bad {m3_bad_d}, old-src bad {m3_bad_oldsrc}, old-tgt bad {m3_bad_oldtgt}\n"));
    out.push_str(&format!("probe bad {probe_bad}, erase bad {erase_bad}, s2 top>257 {s2_bad}\n"));
    out.push_str("sigma\tm2d0\tm2d1\tm2v0\tm2v1\tm3d0\tm3d1\tm3v0\tm3v1\trt0u0\trt0u1\n");
    for sigma in 0..s {
        let d = |x: i64| if x == i64::MAX { String::from("-") } else { x.to_string() };
        let dm = |x: i64| if x == i64::MIN { String::from("-") } else { x.to_string() };
        out.push_str(&format!("{sigma}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            d(m2_min_b[sigma]), d(m2_max_b[sigma]), d(m2_min_v[sigma]), d(m2_max_v[sigma]),
            d(m3_min_b[sigma]), d(m3_max_b[sigma]), d(m3_min_v[sigma]), d(m3_max_v[sigma]),
            d(rt0_min_u[sigma]), dm(rt0_max_u[sigma])));
    }
    let wraps = (0..s).filter(|&sig| m3_min_v[sig] != i64::MAX && m3_min_v[sig] > m3_max_v[sig]).count();
    out.push_str(&format!("m3 wrapped slots {wraps}\n"));
    std::fs::write("/tmp/ds-tj787/census787.txt", &out).unwrap();
    eprintln!("{out}");
}

/// ds-tj787 CO hosting census: find a single bq-expressible lane that is free for EVERY CO shot, so the parity can
/// live there through the whole CO phase (D is 257 lanes, V is 258).
///
/// At a CO boundary event the CO-phase constants are fixed (r, cd never change during CO; rv is fixed too; cv only
/// grows). D's lanes (257-wide): r at [0, bl(r)), cd at [256-bl(cd)+1, 256], free gap [bl(r), 256-bl(cd)]. V frame:
/// rv at [0, bl(rv)), stack bits at [b+1, b+dep] (the top bit b+dep is LIVE at the boundary), cv at [258-bl(cv),
/// 258), free gap [max(bl(rv), b+dep+1), 258-bl(cv)).
/// Candidates (all bq/pi/dep expressible):
///   D: Lcur = b+max(k,1)-1 (k = pi+dep-1, the current CO lane), Lcur-1
///   V frame: b+dep+1, b+max(pi+dep,1)+1
/// The parity must also survive the phase until M3 (no other writes to the gap lanes) and be movable to V-frame b
/// at M3 (a per-shot addressed move, so no extra constraint).
#[test]
fn ds_co_host_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78702);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let bl = |x: &N| x.bit_len() as i64;
    let mut events = 0u64;
    let mut d_cur = 0u64;
    let mut d_cur1 = 0u64;
    let mut v_bdep1 = 0u64;
    let mut v_dv1 = 0u64;
    let mut d_gap_events = 0u64; // events where D has any free lane (gap nonempty)
    let mut v_has_gap = 0u64;
    let mut min_d_gap = i64::MAX;
    let mut min_v_gap = i64::MAX;
    let mut d_cur_fail_v_fail = 0u64; // events where Lcur unfree AND b+dep+1 unfree
    let mut d_cur_fail_v1_fail = 0u64; // events where Lcur unfree AND dv+1 unfree
    let mut d_cur_fail_d_cur1_fail = 0u64;
    let mut k0_d0 = 0u64; // k=0, delta=0
    let mut k0_d1 = 0u64; // k=0, delta=1
    let mut k0_d0_lcur_ok = 0u64;
    let mut k0_d1_lcur_ok = 0u64;
    let mut kge1 = 0u64;
    let mut kge1_lcur1_ok = 0u64;
    let mut kge1_lcur1_fail = 0u64;
    let mut kge2_lcur_fail = 0u64; // k>=2 events where Lcur (today's lane) is cd-blocked or out of range
    let mut kge2 = 0u64;
    let mut lcur_over = 0u64; // Lcur > 256 (lane does not exist in a 257-wide D)
    let mut first_kge1_bad: Option<(usize, i64, i64, i64, i64, u8, u8)> = None;
    let mut first_k0d1: Option<(usize, i64, i64, i64, i64, i64)> = None;
    let mut first_bad: Option<(usize, i64, i64, i64, i64, i64, i64, i64)> = None;
    for _ in 0..shots {
        let mut m = walk(&mut rng, &pp);
        if super::tests_789::max_q_bits(&m.rv) >= super::froghop_double::QBAD {
            continue; // off-model shot
        }
        for sigma in 0..lay.s {
            if m.ph == Ph::Co {
                let b = m.b as i64;
                let pi = m.pi as i64;
                let dep = m.stk.len() as i64;
                let k = pi + dep - 1;
                events += 1;
                let d_gap = 256 - bl(&m.cd) - b + 1; // lanes [b, 256-bl(cd)] inclusive
                min_d_gap = min_d_gap.min(d_gap);
                if d_gap >= 1 {
                    d_gap_events += 1;
                }
                let lo = bl(&m.rv).max(b + dep + 1);
                let v_gap = 258 - bl(&m.cv) - lo;
                min_v_gap = min_v_gap.min(v_gap);
                if v_gap >= 1 {
                    v_has_gap += 1;
                }
                // In the 257-wide D, lane l holds cd bit (256-l). The parity is XORed onto the lane by the
                // oracle, so the lane is a valid host iff it is above r and its cd bit is 0.
                let dfree = |l: i64| l >= bl(&m.r) && l <= 256 && (l < 257 - bl(&m.cd) || !m.cd.bit((256 - l) as usize));
                let vfree = |l: i64| l >= lo && l < 258 - bl(&m.cv);
                let lcur = b + k.max(1) - 1;
                let lcur_free = dfree(lcur);
                if k == 0 {
                    // delta = bl(r) - bl(rv): r in [rv, 2rv) so delta in {0, 1}
                    let delta = bl(&m.r) - bl(&m.rv);
                    if delta == 1 && first_k0d1.is_none() {
                        first_k0d1 = Some((sigma, b, pi, dep, bl(&m.r), bl(&m.rv)));
                    }
                    if delta == 0 {
                        k0_d0 += 1;
                        if lcur_free {
                            k0_d0_lcur_ok += 1;
                        }
                    } else {
                        k0_d1 += 1;
                        if lcur_free {
                            k0_d1_lcur_ok += 1;
                        }
                    }
                } else {
                    kge1 += 1;
                    if k >= 2 {
                        kge2 += 1;
                        if !(lcur <= 256 && (lcur < 257 - bl(&m.cd) || !m.cd.bit((256 - lcur) as usize))) {
                            kge2_lcur_fail += 1;
                        }
                    }
                    if lcur >= 1 && dfree(lcur - 1) {
                        kge1_lcur1_ok += 1;
                    } else {
                        kge1_lcur1_fail += 1;
                        if first_kge1_bad.is_none() {
                            first_kge1_bad = Some((sigma, b, k, bl(&m.r), bl(&m.cd),
                                                  m.cd.bit((256 - (lcur - 1)) as usize) as u8,
                                                  m.cd.bit((256 - lcur) as usize) as u8));
                        }
                    }
                }
                if lcur > 256 {
                    lcur_over += 1;
                }
                if lcur_free {
                    d_cur += 1;
                }
                if lcur >= 1 && dfree(lcur - 1) {
                    d_cur1 += 1;
                }
                let c3 = b + dep + 1;
                if c3 <= 257 && vfree(c3) {
                    v_bdep1 += 1;
                }
                let ldv1 = b + (pi + dep).max(1) + 1;
                if ldv1 <= 257 && vfree(ldv1) {
                    v_dv1 += 1;
                }
                let c3_free = c3 <= 257 && vfree(c3);
                let ldv1_free = ldv1 <= 257 && vfree(ldv1);
                if !lcur_free && !c3_free {
                    d_cur_fail_v_fail += 1;
                    if first_bad.is_none() {
                        first_bad = Some((sigma, b, pi, dep, bl(&m.r), bl(&m.cd), bl(&m.rv), bl(&m.cv)));
                    }
                }
                if !lcur_free && !ldv1_free {
                    d_cur_fail_v1_fail += 1;
                }
                if !lcur_free && !(lcur >= 1 && dfree(lcur - 1)) {
                    d_cur_fail_d_cur1_fail += 1;
                }
            }
            m.fwd(sigma);
        }
    }
    let out = format!(
        "CO events {events} (shots {shots})\n\
         D gap exists {d_gap_events}, V gap exists {v_has_gap}, min D gap {min_d_gap}, min V gap {min_v_gap}\n\
         candidates free: D Lcur {d_cur}, D Lcur-1 {d_cur1}, V b+dep+1 {v_bdep1}, V dv+1 {v_dv1}\n\
         failures: Lcur&(b+dep+1) {d_cur_fail_v_fail}, Lcur&(dv+1) {d_cur_fail_v1_fail}, Lcur&(Lcur-1) {d_cur_fail_d_cur1_fail}\n\
         k=0 delta=0 {k0_d0} (Lcur ok {k0_d0_lcur_ok}), k=0 delta=1 {k0_d1} (Lcur ok {k0_d1_lcur_ok}), k>=1 {kge1} (Lcur-1 ok {kge1_lcur1_ok}, fail {kge1_lcur1_fail})\n\
         k>=2 {kge2} (Lcur cd-blocked {kge2_lcur_fail}), Lcur>256 events {lcur_over}\n\
         first Lcur&(b+dep+1) bad {first_bad:?}\n\
         first k>=1 Lcur-1 bad (sigma,b,k,blr,blcd,cdbit@Lcur-1,cdbit@Lcur) {first_kge1_bad:?}\n\
         first k=0 delta=1 (sigma,b,pi,dep,blr,blrv) {first_k0d1:?}\n"
    );
    std::fs::write("/tmp/ds-tj787/co_host_census.txt", &out).unwrap();
    eprintln!("{out}");
}

/// ds-tj787 packed-layout ladder census: the parent's S2 ladder relies on the no-borrow invariant
/// rvbit(l-pi) & cdbit(257-l) = 0 at every masked cell above bl(r); the packed 257-D shifts cd down by one, so the
/// ladder's reads see cdbit(256-l). The packed layout is value-exact iff rvbit(l-pi) & cdbit(256-l) = 0 holds at
/// every masked cell of every on-model DV shot (the only changed factor is the cd bit index).
#[test]
fn ds_ladder_invariant_census() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78703);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let mut bad_parent = 0u64;
    let mut bad_packed = 0u64;
    let mut bad_remap = 0u64;
    let mut events = 0u64;
    for _ in 0..shots {
        let mut m = walk(&mut rng, &pp);
        if super::tests_789::max_q_bits(&m.rv) >= super::froghop_double::QBAD {
            continue;
        }
        for sigma in 0..lay.s {
            if m.ph == Ph::Dv {
                let b = m.b as i64;
                let pi = m.pi as i64;
                let row = &lay.rows[sigma];
                let p1lo = row[2] as i64;
                let lv = row[0] as i64;
                for l in p1lo..lv {
                    if l >= pi && l <= b + pi {
                        // masked cell l; above-r iff l >= bl(r)
                        if l >= m.r.bit_len() as i64 {
                            events += 1;
                            let rv = (m.rv >> (l as u32 - pi as u32)).bit(0);
                            if rv && m.cd.bit((257 - l) as usize) {
                                bad_parent += 1;
                            }
                            if rv && m.cd.bit((256 - l) as usize) {
                                bad_packed += 1;
                            }
                            if rv && m.cd.bit((257 - l) as usize) {
                                bad_remap += 1;
                            }
                        }
                    }
                }
            }
            m.fwd(sigma);
        }
    }
    let out = format!("masked above-r cells {events}: parent invariant bad {bad_parent}, packed invariant bad {bad_packed}, remap (cd bit 257-l) bad {bad_remap} (shots {shots})\n");
    std::fs::write("/tmp/ds-tj787/ladder_invariant.txt", &out).unwrap();
    eprintln!("{out}");
}
