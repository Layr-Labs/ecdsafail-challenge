//! Cross-chunk carry-phase research, public ecdsa.fail resource competition.
use super::Builder;
use crate::circuit::QubitId;
thread_local! {static LAST_NATIVE:std::cell::RefCell<(Vec<usize>,Vec<String>)>=const{std::cell::RefCell::new((Vec::new(),Vec::new()))};}

/// Exact phase [u < v + seed], restoring operands. Native measured bottom,
/// coherent operand MAJ top; no unaccounted clean comparison ladder.
pub(crate) fn phase(
    c: &mut Builder,
    u: &[QubitId],
    v: &[QubitId],
    seed: Option<QubitId>,
    room: usize,
) {
    let n = u.len();
    assert_eq!(n, v.len());
    assert!(n >= 2 && room >= 1);
    if seed == Some(v[0]) {
        assert!(n >= 3);
        return phase(c, &u[1..], &v[1..], seed, room);
    }
    if n - 1 <= room {
        return super::compare::cmp_lt_phase(c, u, v, seed);
    }
    let cut = room;
    let alias = seed.is_some_and(|p| v[1..].contains(&p));
    let cs = c.alloc_qubits(cut);
    c.x_all(u);
    for i in 0..cut {
        c.cx(u[i], v[i]);
        let prev = if i == 0 {
            seed.map(|p| {
                c.cx(u[i], p);
                p
            })
            .unwrap_or(u[i])
        } else {
            c.cx(u[i], u[i - 1]);
            u[i - 1]
        };
        c.ccx(prev, v[i], cs[i]);
        if i == 0 && alias {
            c.cx(u[i], seed.unwrap());
        }
        c.cx(cs[i], u[i]);
    }
    for i in cut..n - 1 {
        c.cx(u[i], v[i]);
        c.cx(u[i], u[i - 1]);
        c.ccx(u[i - 1], v[i], u[i]);
    }
    c.cz(u[n - 1], v[n - 1]);
    c.cz(u[n - 1], u[n - 2]);
    c.cz(v[n - 1], u[n - 2]);
    for i in (cut..n - 1).rev() {
        c.ccx(u[i - 1], v[i], u[i]);
        c.cx(u[i], u[i - 1]);
        c.cx(u[i], v[i]);
    }
    for i in (0..cut).rev() {
        c.cx(cs[i], u[i]);
        let m = c.alloc_bit();
        c.hmr(cs[i], m);
        if i == 0 {
            if alias {
                c.cx(u[i], seed.unwrap());
            }
            c.cz_if(seed.unwrap_or(u[i]), v[i], m);
            if let Some(p) = seed {
                c.cx(u[i], p);
            }
        } else {
            c.cz_if(u[i - 1], v[i], m);
            c.cx(u[i], u[i - 1]);
        }
        c.cx(u[i], v[i]);
        c.free_bit(m);
    }
    c.free_vec(&cs);
    c.x_all(u);
}

/// Boundary h uses original a[0..h] and finished b[0..h]. The next chunk is
/// already complete; its out carry is the sole retained additional qubit.
pub(crate) fn add(
    c: &mut Builder,
    a: &[QubitId],
    b: &[QubitId],
    sizes: &[usize],
    room: usize,
    window: usize,
    seeded: bool,
    events: &mut Vec<String>,
) -> QubitId {
    assert_eq!(a.len(), b.len());
    assert_eq!(sizes.iter().sum::<usize>(), a.len());
    let base = c.active_qubits();
    let mut at = 0;
    let mut prev = None;
    for &w in sizes {
        let out = c.alloc_qubit();
        let available = room - usize::from(prev.is_some()) - 1;
        let bridge = (w - 1).saturating_sub(available);
        let op = c.op_count();
        let t = c.report_totals().unwrap().1;
        if bridge == 0 {
            super::modular::ripple_add(c, &a[at..at + w], &b[at..at + w], prev, Some(out));
        } else {
            super::bridge::raw_add(c, &a[at..at + w], &b[at..at + w], prev, Some(out), bridge);
        }
        events.push(format!(
            "{{\"kind\":\"chunk\",\"lo\":{at},\"hi\":{},\"bridge\":{bridge},\"op\":{op},\"T\":{}}}",
            at + w,
            c.report_totals().unwrap().1 - t
        ));
        if let Some(q) = prev {
            let m = c.alloc_bit();
            c.hmr(q, m);
            c.release_clean(q);
            let hi = at;
            let width = window.min(hi);
            let lo = hi - width;
            let seed = if seeded && lo > 0 {
                Some(a[lo - 1])
            } else {
                None
            };
            let op = c.op_count();
            let t = c.report_totals().unwrap().1;
            c.push_condition(m);
            phase(c, &b[lo..hi], &a[lo..hi], seed, room - 1);
            c.pop_condition();
            c.free_bit(m);
            events.push(format!(
                "{{\"kind\":\"repair\",\"lo\":{lo},\"hi\":{hi},\"seed\":{},\"op\":{op},\"T\":{}}}",
                seed.map_or(-1, |x| x.0 as i64),
                c.report_totals().unwrap().1 - t
            ));
        }
        prev = Some(out);
        at += w;
    }
    assert_eq!(c.active_qubits(), base + 1);
    prev.unwrap()
}
fn ids(v: &[QubitId]) -> String {
    format!(
        "[{}]",
        v.iter()
            .map(|q| q.0.to_string())
            .collect::<Vec<_>>()
            .join(",")
    )
}
/// Production hook: invoked only when native has already selected its exact
/// width-composition fallback. A wider/extra seeded policy is supplied by the
/// actual pingpong cell; this function does not invent policy overrides.
pub(crate) fn try_native(
    c: &mut Builder,
    a: &[QubitId],
    b: &[QubitId],
    room: usize,
    round: usize,
    multiply: bool,
    control: &super::width_composition::Plan,
    spec: impl Fn(usize) -> (usize, Option<usize>),
) -> Option<QubitId> {
    if std::env::var("HEO_CROSS_CHUNK").as_deref() != Ok("1") || room < 3 || !control.slow {
        return None;
    }
    let n = a.len();
    let specs: Vec<_> = (0..n)
        .map(|h| if h < 2 { (0, None) } else { spec(h) })
        .collect();
    let mut dp = vec![usize::MAX; n + 1];
    let mut prev = vec![0; n + 1];
    dp[0] = 0;
    for h in 0..n {
        if dp[h] == usize::MAX {
            continue;
        }
        for w in 2..=n - h {
            let p = super::width_composition::plan(w, room - usize::from(h > 0)).unwrap();
            let cw = specs[h].0;
            let repair = if h == 0 {
                0
            } else {
                cw - 1 + (cw - 1).saturating_sub(room - 1)
            };
            let cost = dp[h] + 2 * w + p.extra2 + repair;
            if cost < dp[h + w] {
                dp[h + w] = cost;
                prev[h + w] = h;
            }
        }
    }
    let old = 2 * n + control.extra2;
    if dp[n] >= old {
        return None;
    }
    let mut sizes = Vec::new();
    let mut h = n;
    while h > 0 {
        sizes.push(h - prev[h]);
        h = prev[h];
    }
    sizes.reverse();
    let base = c.active_qubits();
    let t = c.report_totals().map_or(0., |x| x.1);
    let mut at = 0;
    let mut carry = None;
    let mut repairs = Vec::new();
    let mut events = Vec::new();
    for &w in &sizes {
        let p = super::width_composition::plan(w, room - usize::from(carry.is_some())).unwrap();
        let out =
            super::width_composition::add_with_carry(c, &a[at..at + w], &b[at..at + w], carry, &p);
        events.push(format!(
            "{{\"kind\":\"block\",\"lo\":{at},\"hi\":{},\"sizes\":{:?},\"slow\":{}}}",
            at + w,
            p.sizes,
            p.slow
        ));
        if let Some(q) = carry {
            let (width, predictor) = specs[at];
            let lo = at - width;
            let seed = predictor.map(|j| a[j]);
            let m = c.alloc_bit();
            c.hmr(q, m);
            c.release_clean(q);
            c.record_replay_site('B', round, at, width);
            c.push_condition(m);
            phase(c, &b[lo..at], &a[lo..at], seed, room - 1);
            c.pop_condition();
            c.free_bit(m);
            repairs.push(format!(
                "[{}, {}, {}]",
                at,
                width,
                predictor.map_or(-1, |x| x as isize)
            ));
            events.push(format!(
                "{{\"kind\":\"repair\",\"lo\":{lo},\"hi\":{at},\"seed\":{}}}",
                seed.map_or(-1, |q| q.0 as isize)
            ));
        }
        carry = Some(out);
        at += w;
    }
    assert_eq!(c.active_qubits(), base + 1);
    let actual = c.report_totals().map_or(0., |x| x.1) - t;
    if c.report_totals().is_some() {
        assert_eq!(actual, dp[n] as f64 / 2.);
    }
    eprintln!("CROSS_DEPLOY {{\"round\":{round},\"multiply\":{multiply},\"room\":{room},\"control_T\":{},\"new_T\":{},\"blocks\":{:?},\"repairs\":[{}]}}",old as f64/2.,dp[n]as f64/2.,sizes,repairs.join(","));
    LAST_NATIVE.with(|s| *s.borrow_mut() = (sizes, events));
    carry
}
fn repair2(h: usize, room: usize, window: usize) -> usize {
    let w = h.min(window);
    w - 1 + (w - 1).saturating_sub(room - 1)
}
pub(crate) fn block_plan(n: usize, room: usize, window: usize) -> Vec<usize> {
    let mut dp = vec![usize::MAX; n + 1];
    let mut prev = vec![0; n + 1];
    dp[0] = 0;
    for h in 0..n {
        if dp[h] == usize::MAX {
            continue;
        }
        for w in 2..=n - h {
            let p = super::width_composition::plan(w, room - usize::from(h > 0)).unwrap();
            let t = dp[h] + 2 * w + p.extra2 + if h == 0 { 0 } else { repair2(h, room, window) };
            if t < dp[h + w] {
                dp[h + w] = t;
                prev[h + w] = h;
            }
        }
    }
    let mut out = Vec::new();
    let mut h = n;
    while h > 0 {
        out.push(h - prev[h]);
        h = prev[h];
    }
    out.reverse();
    out
}
/// Distinct schedule: an exact native retained-flag block, with a global
/// cross-prefix repair only when the block's incoming carry is released.
pub(crate) fn blocked(
    c: &mut Builder,
    a: &[QubitId],
    b: &[QubitId],
    sizes: &[usize],
    room: usize,
    window: usize,
    seeded: bool,
    events: &mut Vec<String>,
) -> QubitId {
    let base = c.active_qubits();
    let mut at = 0;
    let mut prev = None;
    for &w in sizes {
        let p = super::width_composition::plan(w, room - usize::from(prev.is_some())).unwrap();
        let op = c.op_count();
        let t = c.report_totals().unwrap().1;
        let out =
            super::width_composition::add_with_carry(c, &a[at..at + w], &b[at..at + w], prev, &p);
        events.push(format!("{{\"kind\":\"block\",\"lo\":{at},\"hi\":{},\"sizes\":{:?},\"slow\":{},\"op\":{op},\"T\":{}}}",at+w,p.sizes,p.slow,c.report_totals().unwrap().1-t));
        if let Some(q) = prev {
            let m = c.alloc_bit();
            c.hmr(q, m);
            c.release_clean(q);
            let hi = at;
            let width = window.min(hi);
            let lo = hi - width;
            let seed = if seeded && lo > 0 {
                Some(a[lo - 1])
            } else {
                None
            };
            let op = c.op_count();
            let t = c.report_totals().unwrap().1;
            c.push_condition(m);
            phase(c, &b[lo..hi], &a[lo..hi], seed, room - 1);
            c.pop_condition();
            c.free_bit(m);
            events.push(format!(
                "{{\"kind\":\"repair\",\"lo\":{lo},\"hi\":{hi},\"seed\":{},\"op\":{op},\"T\":{}}}",
                seed.map_or(-1, |x| x.0 as i64),
                c.report_totals().unwrap().1 - t
            ));
        }
        prev = Some(out);
        at += w;
    }
    assert_eq!(c.active_qubits(), base + 1);
    prev.unwrap()
}
pub fn run() {
    let path = std::env::var("CROSS_SCHEDULES").unwrap();
    let outdir = std::env::var("CROSS_OUTPUT").unwrap();
    std::fs::create_dir_all(&outdir).unwrap();
    for line in std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .filter(|x| !x.is_empty() && !x.starts_with('#'))
    {
        let f: Vec<_> = line.split_whitespace().collect();
        let tag = f[0];
        let n: usize = f[1].parse().unwrap();
        let room: usize = f[2].parse().unwrap();
        let win: usize = f[3].parse().unwrap();
        let seed: bool = f[4] == "1";
        let sizes: Vec<usize> = f[5..].iter().map(|s| s.parse().unwrap()).collect();
        let mut c = Builder::new();
        let a = c.alloc_qubits(n);
        let b = c.alloc_qubits(n);
        let start = c.op_count();
        let mut events = Vec::new();
        let mut sizes = if tag.contains("blockedopt") {
            block_plan(n, room, win)
        } else if tag.contains("control") {
            super::width_composition::plan(n, room).unwrap().sizes
        } else {
            sizes
        };
        let out = if tag.contains("nativehook") {
            let out = super::pingpong::heo_hooks::with_cmp_shift((2, 2), || {
                super::pingpong::heo_hooks::chunked_add(&mut c, &a, &b, 651, false)
            });
            let (s, e) = LAST_NATIVE.with(|x| x.borrow().clone());
            sizes = s;
            events = e;
            out
        } else if tag.contains("control") {
            let p = super::width_composition::plan(n, room).unwrap();
            super::width_composition::add(&mut c, &a, &b, &p)
        } else if tag.contains("blocked") {
            blocked(&mut c, &a, &b, &sizes, room, win, seed, &mut events)
        } else {
            add(&mut c, &a, &b, &sizes, room, win, seed, &mut events)
        };
        let t = c.report_totals().unwrap().1;
        let peak = c.peak_total();
        assert!(peak as usize <= 2 * n + room);
        let (nq, nb) = c.i13_dims();
        let ops = c.take_ops();
        let opjson = ops
            .iter()
            .map(|x| {
                format!(
                    "[{},{},{},{},{},{},{}]",
                    x.kind as u8,
                    x.q_control2.0,
                    x.q_control1.0,
                    x.q_target.0,
                    x.c_target.0,
                    x.c_condition.0,
                    x.r_target.0
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let artifact = format!("{tag}.json");
        let metadata=format!("\"tag\":\"{tag}\",\"n\":{n},\"room\":{room},\"window\":{win},\"seeded\":{seed},\"T\":{t},\"Q\":{peak},\"sizes\":{:?},\"events\":[{}]",sizes,events.join(","));
        std::fs::write(format!("{outdir}/{artifact}"),format!("{{{metadata},\"nq\":{nq},\"nb\":{nb},\"input_start\":{start},\"input_registers\":[{},{}],\"output_registers\":[{},{},{}],\"ops\":[{opjson}]}}",ids(&a),ids(&b),ids(&a),ids(&b),ids(&[out]))).unwrap();
        println!(
            "{{{metadata},\"artifact\":\"gates/{artifact}\",\"ops\":{}}}",
            ops.len()
        );
    }
}
