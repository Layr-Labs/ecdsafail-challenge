//! LEAPFROG GCD walk (research build, flag-gated by `LEAPFROG=1`).
//!
//! Rails R[0], R[1] are odd integers (two's complement, LSB first). Seed: R[0] = d (or d + p when d is even,
//! taking over the denominator's wires), R[1] = p. Tick t updates the TARGET R[t % 2] from the SOURCE
//! R[1 - t % 2] (roles alternate on a fixed schedule: no data-dependent payload route):
//!   * three forced ping-pong steps  T <- (T + s_i B) / 2,  s_i = +1 iff T[1] == B[1]  (keeps T odd; Clifford),
//!   * a fourth step with the deep/flat choice: the two candidates (T +- B) are even and exactly one is
//!     == 0 mod 4 ("deep"); v0 takes the deep one when v2(deep) <= 4 (admissible), else the flat one,
//!   * the extra trailing zeros e = v2(T) in [0,3] are stripped by a 2-stage barrel (k1 = e & 1, k2 = e >> 1).
//! Letter per tick: (s0, s1, s2, s3, k1, k2), six raw qubits on the tape.
//! Payload P[i] = lambda * R[i] (mod p): the same four add-halve steps (the head's replay cells) and a
//! controlled modular 2^-e. Division seed P = (y, 0); at park R = (+-1, +-1) and P = (+-lambda, +-lambda).
//! Reference model and envelope: scratchpad walksim/lf_ref.py, lf_env.py.
use super::builder::Builder;
use super::const_arith::{add_const, cadd_const_trunc, csub_const_trunc, sub_const};
use super::heo::gidney_add;
use super::modular::{f, go_fs, mod_addsub};
use super::pingpong::heo_hooks as cells;
use super::N;
use crate::circuit::{QubitId, NO_BIT};
use std::sync::OnceLock;

pub fn enabled() -> bool {
    std::env::var("LEAPFROG").is_ok_and(|v| v == "1")
}

/// Submission recipe, installed by `build()` on top of the Skywalk recipe (which still configures the shared
/// replay cells, coordinate ops and square): Leapfrog m = 2, sign2 + W1-window choice, fast rails, seed-half, walk
/// cap 1265;
/// the square's B fold stays plain (NATIVE_SFUSE_B=1) and the Skywalk back seam is off (both fuse into its walk).
pub(crate) fn install_recipe() {
    for (k, v) in [
        ("LEAPFROG", "1"),
        ("LEAPFROG_M", "2"),
        ("LF_FAST", "1"),
        ("LF_SEED", "half"),
        // W1-window choice rule (one 24-bit top-window compare at e = 1, equal signs): R 143 -> 140, tape -15
        ("LF_W1", "1"),
        // ... narrowed to an 18-bit window read 4 bits lower (leapfrog_data/anch_w1_k18a4.txt, see `w1_anchor`)
        ("LF_W1K", "18"),
        // joint-optimised width envelope, 139 ticks
        ("LF_PEEL", "1"),
        // rails held at their already-implied widths through the payload ops
        ("LF_TRIM", "1"),
        // last add-halve cell + payload barrel as one merged Montgomery-style op on the ticks where it fits
        ("LF_MERGED", "1"),
        // ... also on the late ticks (split fold where room is short)
        ("LF_MERGED_LATE", "1"),
        // merged-op fold windows: standard 56 bits; late 58, capped by the standard window
        ("LF_MERGED_WIN", "56"),
        ("LF_MERGED_LATE_WIN", "58"),
        // ticks 0..75 of the payload-fused traversals split into a rails-only pass (one payload register live: no
        // room-split rail adds) and a payload-only pass over the taped letters (-5.9k T)
        ("LF_REORDER", "74"),
        // plain seeded compares on would-be tie ticks; source-rail sign wire read by the rail adds; seed/unseed fused
        // with the coordinate seams
        ("LF_TIE_SEED", "1"),
        ("LF_SIGNWIRE", "1"),
        ("LF_SEAMS", "1"),
        // peak cap, co-tuned with LF_REORDER
        ("HEO_PIN_PP_WALK_MAX_QUBITS", "1241"),
        ("NATIVE_SFUSE_B", "1"),
        // payload cells: fold window floored at 55 bits (Skywalk's late-round profile narrows it to 49),
        // chunk-boundary / flag compares not widened (0 / 0 bits)
        ("LF_CELL_FOLD_MIN", "54"),
        ("LF_CMP_SHIFT", "0,0"),
        // tie-safe cell mode off (LF_TIE_FROM past the last tick): Leapfrog rail steps never cancel to zero, so the
        // cells see no structural ties
        ("LF_TIE_FROM", "999"),
        // walk room squeeze (see `early()`): odd rails held without their constant bit-0 wire (+2 walk wires, given
        // to the cells), split adders with the minimal low part
        ("LF_EARLY", "1"),
        ("LF_LOWREL_PAD", "0"),
    ] {
        std::env::set_var(k, v);
    }
    if FORCE_MERGED.load(std::sync::atomic::Ordering::Relaxed) {
        std::env::set_var("LF_MERGED", "1");
        for (k, v) in FORCE_EXTRA.lock().unwrap().iter() {
            std::env::set_var(k, v);
        }
    }
    std::env::remove_var("BACK_SEAM_FUSE");
}

/// Test hook: makes [`install_recipe`] (which runs after `build()` clears the process environment) also set
/// LF_MERGED=1, so one test process can build the env-free op stream with and without the merged op.
pub(crate) static FORCE_MERGED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// Test hook: extra recipe entries applied with [`FORCE_MERGED`] (paired A/B of recipe knobs, `LF_PAIRED_EXTRA`).
pub(crate) static FORCE_EXTRA: std::sync::Mutex<Vec<(String, String)>> = std::sync::Mutex::new(Vec::new());

/// `LEAPFROG_RULE=v0`: the plain 2-adic choice (deepest admissible); default sign2 (see [`choice_xor`]).
fn rule_v0() -> bool {
    std::env::var("LEAPFROG_RULE").is_ok_and(|v| v == "v0")
}

/// `LEAPFROG_RULE=pp`: plain ping-pong for comparison (one forced add-halve per tick, no choice, no barrel).
fn pp_mode() -> bool {
    std::env::var("LEAPFROG_RULE").is_ok_and(|v| v == "pp")
}

/// `LEAPFROG_M`: forced ping-pong steps per tick before the choice step (default 3; 1 in ping-pong mode).
fn forced() -> usize {
    if pp_mode() {
        return 1;
    }
    std::env::var("LEAPFROG_M").ok().and_then(|v| v.parse().ok()).unwrap_or(3)
}

// ---- profiler (LF_PROF2=1): expected Toffoli per component and per tick ----
thread_local! {
    static PROF: std::cell::RefCell<std::collections::BTreeMap<String, (f64, usize)>> = Default::default();
}
fn prof_on() -> bool {
    std::env::var("LF_PROF2").is_ok_and(|v| v == "1")
}
fn pmark(c: &Builder) -> f64 {
    c.expected_total()
}
fn pacc(c: &Builder, name: &str, t0: f64) {
    if prof_on() {
        let d = c.expected_total() - t0;
        PROF.with(|p| {
            let mut p = p.borrow_mut();
            let e = p.entry(name.to_string()).or_insert((0.0, 0));
            e.0 += d;
            e.1 += 1;
        });
    }
}
pub(crate) fn prof_dump() {
    if prof_on() {
        PROF.with(|p| {
            for (k, (v, n)) in p.borrow().iter() {
                eprintln!("LFPROF\t{k}\t{v:.1}\t{n}");
            }
        });
    }
}

/// `LEAPFROG_BARREL=old`: the two nested shift stages (halve + quarter) instead of [`cmod_barrel`].
fn old_barrel() -> bool {
    std::env::var("LEAPFROG_BARREL").is_ok_and(|v| v == "old")
}

fn envelope() -> &'static Vec<usize> {
    static ENV: OnceLock<Vec<usize>> = OnceLock::new();
    ENV.get_or_init(|| {
        if let Some(st) = steps_override() {
            return st.iter().map(|r| r[0]).collect();
        }
        if pp_mode() {
            return include_str!("leapfrog_data/env_pp.txt")
                .lines()
                .map(str::trim)
                .filter(|l| !l.is_empty() && !l.starts_with('#'))
                .map(|l| l.parse().expect("envelope width"))
                .collect();
        }
        match (rule_v0(), forced()) {
            (true, 3) => include_str!("leapfrog_data/env_v0.txt"),
            (false, 3) => include_str!("leapfrog_data/env_sign2.txt"),
            (false, 2) if seed_half() && lf_w1() && lf_peel() => include_str!("leapfrog_data/env_w1_peel139.txt"),
            (false, 2) if seed_half() && lf_w1() && w1_k() == 20 => include_str!("leapfrog_data/env_sign2_m2_w1k20.txt"),
            (false, 2) if seed_half() && lf_w1() => include_str!("leapfrog_data/env_sign2_m2_w1.txt"),
            (false, 2) if seed_half() => include_str!("leapfrog_data/env_sign2_m2_half.txt"),
            (false, 2) => include_str!("leapfrog_data/env_sign2_m2.txt"),
            cfg => panic!("no Leapfrog envelope for (v0, m) = {cfg:?}"),
        }
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(|l| l.parse().expect("envelope width"))
            .collect()
    })
}

fn fredkin(c: &mut Builder, ctrl: QubitId, a: QubitId, b: QubitId) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

/// Two's-complement resize: grow by sign extension, trim a top wire that must be a sign copy.
fn resize(c: &mut Builder, reg: &mut Vec<QubitId>, w: usize) {
    while reg.len() < w {
        let q = c.alloc_qubit();
        c.cx(*reg.last().unwrap(), q);
        reg.push(q);
    }
    while reg.len() > w {
        let top = reg.pop().unwrap();
        c.cx(*reg.last().unwrap(), top);
        c.free(top);
    }
}

/// `dst += (-1)^sign * src` on equal widths (sign = 1 subtracts): complement sandwich + carry-in.
fn signed_add(c: &mut Builder, sign: QubitId, src: &[QubitId], dst: &[QubitId]) {
    c.cx_all(sign, src);
    gidney_add(c, src, dst, Some(sign));
    c.cx_all(sign, src);
}

/// `out ^= carry_out(a + b + cin)`: Gidney carries, measurement-uncomputed; a and b restored. With `out = None`
/// it applies the phase (-1)^(NOT carry_out) instead (for MBU erasure of a kept carry, under a condition).
fn carry_out_xor(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: QubitId, out: Option<QubitId>) {
    let n = a.len();
    // Phase-only form: the top carry is never built. carry[n] = c ^ (a ^ c)(b ^ c) with c = carry[n - 1], so
    // (-1)^(NOT carry[n]) is one CZ on the two operand wires (while they hold a ^ c, b ^ c) times (-1)^(NOT c).
    let m = if out.is_none() && n >= 1 { n - 1 } else { n };
    let mut carry = vec![cin];
    for i in 0..m {
        let ci = carry[i];
        c.cx(ci, a[i]);
        c.cx(ci, b[i]);
        let t = and_new(c, a[i], b[i]);
        c.cx(ci, t);
        carry.push(t);
    }
    match out {
        Some(out) => c.cx(carry[n], out),
        None => {
            let ci = carry[m];
            if m < n {
                c.cx(ci, a[m]);
                c.cx(ci, b[m]);
                c.cz(a[m], b[m]);
                c.cx(ci, a[m]);
                c.cx(ci, b[m]);
            }
            c.x(ci);
            c.z_if(ci, NO_BIT);
            c.x(ci);
        }
    }
    for i in (0..m).rev() {
        let (ci, t) = (carry[i], carry[i + 1]);
        c.cx(ci, t);
        and_erase(c, t, a[i], b[i]);
        c.cx(ci, a[i]);
        c.cx(ci, b[i]);
    }
}

/// Rail `dst += (-1)^sign * src` whose carry ladder respects the walk cap: when the full ladder would not fit,
/// the low `delta` bits go first with their carry-out kept on one wire, the high part takes it as carry-in, and
/// the kept carry is erased exactly as [dst_low < src'_low + sign] (src' = sign-complemented source): +delta
/// Toffoli. `LF_RAIL_SPLIT=0` disables.
fn rail_signed_add(c: &mut Builder, sign: QubitId, src: &[QubitId], dst: &[QubitId]) {
    let n = dst.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let off = std::env::var("LF_RAIL_SPLIT").is_ok_and(|v| v == "0");
    if off || n <= 3 || n - 1 <= room {
        signed_add(c, sign, src, dst);
        return;
    }
    let delta = n + 1 - room;
    if delta + 2 > room || delta + 1 >= n {
        signed_add(c, sign, src, dst);
        return;
    }
    c.cx_all(sign, src);
    let (za, cq) = (c.alloc_qubit(), c.alloc_qubit());
    let mut al = src[..delta].to_vec();
    al.push(za);
    let mut bl = dst[..delta].to_vec();
    bl.push(cq);
    gidney_add(c, &al, &bl, Some(sign));
    c.free(za);
    gidney_add(c, &src[delta..], &dst[delta..], Some(cq));
    // cq = NOT carry_out(dst_low + NOT src'_low + NOT sign)
    c.x_all(&src[..delta]);
    c.x(sign);
    carry_out_xor(c, &src[..delta], &dst[..delta], sign, Some(cq));
    c.x(sign);
    c.x_all(&src[..delta]);
    c.x(cq);
    c.free(cq);
    c.cx_all(sign, src);
}

/// [`gidney_add`] with the top carry XORed straight into the top sum wire (one CCX, nothing to erase): the same
/// n - 1 Toffoli on n - 2 carry wires instead of n - 1.
fn gidney_add_lean(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>) {
    let n = a.len();
    assert!(n >= 1 && b.len() == n);
    if n < 2 {
        return gidney_add(c, a, b, cin);
    }
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    carry[0] = cin;
    for i in 0..n - 1 {
        if let Some(ci) = carry[i] {
            c.cx(ci, a[i]);
            c.cx(ci, b[i]);
        }
        if i + 2 == n {
            c.ccx(a[i], b[i], b[n - 1]);
            if let Some(ci) = carry[i] {
                c.cx(ci, b[n - 1]);
            }
        } else {
            let t = and_new(c, a[i], b[i]);
            if let Some(ci) = carry[i] {
                c.cx(ci, t);
            }
            carry[i + 1] = Some(t);
        }
    }
    c.cx(a[n - 1], b[n - 1]);
    for i in (0..n - 1).rev() {
        if let Some(next) = carry[i + 1] {
            if let Some(ci) = carry[i] {
                c.cx(ci, next);
            }
            and_erase(c, next, a[i], b[i]);
        }
        c.cx(a[i], b[i]);
        if let Some(ci) = carry[i] {
            c.cx(ci, a[i]);
            c.cx(ci, b[i]);
        }
    }
}

/// `b += a + cin` (Gidney) whose carry ladder respects the walk cap, as [`rail_signed_add`]'s split but for any
/// carry-in (None = 0). The kept carry is [b_low_new < a_low + cin] = NOT carry_out(b_low_new + NOT a_low +
/// NOT cin), erased with an exact compare.
fn capped_add(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>) {
    let n = b.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let off = std::env::var("LF_RAIL_SPLIT").is_ok_and(|v| v == "0");
    // the lean ladder holds n - 2 carries (its top carry goes straight into the top sum wire)
    if off || n <= 3 || n - 2 <= room {
        gidney_add_lean(c, a, b, cin);
        return;
    }
    let delta = n - room - split_tight() as usize;
    if std::env::var_os("LF_SPLIT_TRACE").is_some() {
        eprintln!("LF_SPLIT n={n} room={room} delta={delta}");
    }
    if delta + 3 > room || delta + 1 >= n {
        gidney_add_lean(c, a, b, cin);
        return;
    }
    let (za, cq) = (c.alloc_qubit(), c.alloc_qubit());
    let mut al = a[..delta].to_vec();
    al.push(za);
    let mut bl = b[..delta].to_vec();
    bl.push(cq);
    gidney_add_lean(c, &al, &bl, cin);
    c.free(za);
    gidney_add_lean(c, &a[delta..], &b[delta..], Some(cq));
    c.x_all(&a[..delta]);
    let ncin = match cin {
        Some(q) => {
            c.x(q);
            q
        }
        None => {
            let o = c.alloc_qubit();
            c.x(o);
            o
        }
    };
    let q0 = pmark(c);
    if split_mbu() {
        // cq = NOT carry_out(...): measure it away and fix the phase only on shots whose outcome is 1
        let m = c.alloc_bit();
        c.hmr(cq, m);
        c.release_clean(cq);
        c.push_condition(m);
        carry_out_xor(c, &a[..delta], &b[..delta], ncin, None);
        c.pop_condition();
        c.free_bit(m);
    } else {
        carry_out_xor(c, &a[..delta], &b[..delta], ncin, Some(cq));
        c.x(cq);
        c.free(cq);
    }
    pacc(c, "split.rail_erase", q0);
    match cin {
        Some(q) => c.x(q),
        None => {
            c.x(ncin);
            c.free(ncin);
        }
    }
    c.x_all(&a[..delta]);
}

/// `LF_SEED=half`: rails (R0, R1) = (d | d - p, (R0 +- p)/2) (both odd), payload (y, y/2) (rails red-team seed e).
fn seed_half() -> bool {
    std::env::var("LF_SEED").is_ok_and(|v| v == "half")
}

/// `LF_EARLY=1`: the walk room squeeze, i.e. [`lowrel`] + [`split_tight`] (each also has its own flag, which
/// overrides LF_EARLY: `LF_LOWREL=0` / `LF_SPLIT_TIGHT=0`).
fn early() -> bool {
    std::env::var("LF_EARLY").is_ok_and(|v| v == "1")
}

/// `LF_SPLIT_TIGHT=1` (or LF_EARLY): split adders keep the minimal low part. Rails ([`capped_add`], [`rail_add`]):
/// the high part holds n - delta - 1 carries + the kept carry, so delta = n - room (was n + 1 - room). Fold ladders
/// ([`lpa_capped`]): the low chunk is n - room (its kept carry's erase compares only it; was room - 4, i.e. the
/// erase compared ~room bits), and a ladder of n bits fits when n - 1 <= room.
fn split_tight() -> bool {
    std::env::var("LF_SPLIT_TIGHT").map_or(early(), |v| v == "1")
}

/// `LF_SPLIT_MBU=0` disables the MBU-halved erasure of split-adder kept carries.
fn split_mbu() -> bool {
    !std::env::var("LF_SPLIT_MBU").is_ok_and(|v| v == "0")
}

/// `LF_FAST=1` (m = 2, sign2): the rail package of the rails red-team (scratch rails_ops/rails.py): adds that skip
/// the known low carries, the choice and barrel letters from linear forms (5 Toffoli), MBU letter erasure on the
/// reverse tick, a 3-Toffoli sign fill, and per-step widths (leapfrog_data/env_sign2_m2_steps.txt).
fn lf_fast() -> bool {
    std::env::var("LF_FAST").is_ok_and(|v| v == "1") && !pp_mode() && !rule_v0() && forced() == 2
}

/// Experiment hook: per-step widths read at run time from `LF_STEPS_FILE` (unset in the submission build).
fn steps_override() -> Option<Vec<[usize; 5]>> {
    let path = std::env::var("LF_STEPS_FILE").ok()?;
    Some(parse_steps(&std::fs::read_to_string(path).expect("LF_STEPS_FILE")))
}

fn parse_steps(s: &str) -> Vec<[usize; 5]> {
    s.lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| {
            let v: Vec<usize> = l.split_whitespace().map(|x| x.parse().unwrap()).collect();
            [v[0], v[1], v[2], v[3], v[4]]
        })
        .collect()
}

/// Per-step widths (W, n0, n1, n2, nb) of the fast path.
fn steps() -> &'static Vec<[usize; 5]> {
    static S: OnceLock<Vec<[usize; 5]>> = OnceLock::new();
    S.get_or_init(|| {
        if let Some(st) = steps_override() {
            return st;
        }
        if seed_half() && lf_w1() && lf_peel() {
            include_str!("leapfrog_data/env_w1_peel139_steps.txt")
        } else if seed_half() && lf_w1() && w1_k() == 20 {
            include_str!("leapfrog_data/env_sign2_m2_w1k20_steps.txt")
        } else if seed_half() && lf_w1() {
            include_str!("leapfrog_data/env_sign2_m2_w1_steps.txt")
        } else if seed_half() {
            include_str!("leapfrog_data/env_sign2_m2_half_steps.txt")
        } else {
            include_str!("leapfrog_data/env_sign2_m2_steps.txt")
        }
            .lines()
            .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
            .map(|l| {
                let v: Vec<usize> = l.split_whitespace().map(|x| x.parse().unwrap()).collect();
                [v[0], v[1], v[2], v[3], v[4]]
            })
            .collect()
    })
}

/// Forced step `t <- (t + (-1)^sign b)/2`, sign = t1 ^ b1: bit 0 sums to 0 (carry 1), bit 1 sums to 1 with carry
/// t1, so the ripple covers bits [2, n) with carry-in t1. Drops t's low wire.
/// `LF_SIGNWIRE=1`: in the payload legs the source rail stays at min(W(t), W(t+1)) bits through the rail adds (the
/// width it is truncated to at the tick's end anyway); the adds read its sign wire for the missing top positions.
fn lf_signwire() -> bool {
    std::env::var("LF_SIGNWIRE").is_ok_and(|v| v == "1")
}

/// Rail `b += a + cin` with `a` possibly shorter than `b` (two's complement: positions past `a` read `a`'s sign wire,
/// shared by every such position of the parity ladder); same split policy under the walk cap as the full-width add.
fn rail_add(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>) {
    if a.len() >= b.len() {
        return capped_add(c, a, b, cin);
    }
    let sg = *a.last().unwrap();
    let add: Vec<Vec<QubitId>> = (0..b.len()).map(|i| vec![if i < a.len() { a[i] } else { sg }]).collect();
    // capped_add's split: the low `delta` bits first with their carry kept, the rest takes it as carry-in, the kept
    // carry erased (MBU) as NOT carry_out(b_low_new + NOT a_low + NOT cin)
    let n = b.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let off = std::env::var("LF_RAIL_SPLIT").is_ok_and(|v| v == "0");
    // the parity ladder holds n - 2 carries (its top carry goes straight into the top sum wire)
    if off || n <= 3 || n - 2 <= room {
        return ladder_parity_add(c, b, &add, cin);
    }
    let delta = n - room - split_tight() as usize;
    if delta + 3 > room || delta + 1 >= n || delta >= a.len() {
        return ladder_parity_add(c, b, &add, cin);
    }
    let cq = c.alloc_qubit();
    let mut lo = b[..delta].to_vec();
    lo.push(cq);
    let mut lo_add = add[..delta].to_vec();
    lo_add.push(vec![]);
    ladder_parity_add(c, &lo, &lo_add, cin);
    ladder_parity_add(c, &b[delta..], &add[delta..], Some(cq));
    let ncin = match cin {
        Some(q) => {
            c.x(q);
            q
        }
        None => {
            let o = c.alloc_qubit();
            c.x(o);
            o
        }
    };
    let q0 = pmark(c);
    let m = c.alloc_bit();
    c.hmr(cq, m);
    c.release_clean(cq);
    c.push_condition(m);
    carry_out_parity_xor(c, &b[..delta], &add[..delta], true, ncin, None);
    c.pop_condition();
    c.free_bit(m);
    pacc(c, "split.rail_erase", q0);
    match cin {
        Some(q) => c.x(q),
        None => {
            c.x(ncin);
            c.free(ncin);
        }
    }
}

fn fast_add_halve_forced(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    c.cx_all(sign, b);
    rail_add(c, &b[2..], &t[2..], Some(t[1]));
    c.x(t[0]);
    c.cx(b[1], t[1]);
    c.x(t[1]);
    c.cx_all(sign, b);
    let low = t.remove(0);
    c.free(low);
}
fn fast_double_sub_forced(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    t.insert(0, c.alloc_qubit());
    c.cx_all(sign, b);
    c.x(t[1]);
    c.cx(b[1], t[1]);
    c.x(t[0]);
    c.x_all(&t[2..]);
    rail_add(c, &b[2..], &t[2..], Some(t[1]));
    c.x_all(&t[2..]);
    c.cx_all(sign, b);
}
/// Choice step, any sign: bit 0 sums to 0 (carry 1), bits [1, n) get t + b' + 1 = NOT(NOT t + NOT b').
fn fast_add_halve_choice(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    c.cx_all(sign, b);
    c.x_all(&b[1..]);
    c.x_all(&t[1..]);
    rail_add(c, &b[1..], &t[1..], None);
    c.x_all(&t[1..]);
    c.x_all(&b[1..]);
    c.x(t[0]);
    c.cx_all(sign, b);
    let low = t.remove(0);
    c.free(low);
}
fn fast_double_sub_choice(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    t.insert(0, c.alloc_qubit());
    c.cx_all(sign, b);
    c.x(t[0]);
    c.x_all(&b[1..]);
    rail_add(c, &b[1..], &t[1..], None);
    c.x_all(&b[1..]);
    c.cx_all(sign, b);
}

/// `LF_LOWREL=1` (or LF_EARLY; fast path): rails are held WITHOUT their bit-0 wire wherever they are odd (both rails
/// at every tick boundary, through the forced steps, the payload ops and the choice add; the target holds it again
/// only from the choice add to the rail barrel). An odd rail's bit 0 is the constant 1, so the wire is released
/// (X + free) and re-materialised (alloc + X) only around the ops that read it: +2 wires of walk room almost
/// everywhere. Rail vectors then hold bit j + 1 at index j.
fn lowrel() -> bool {
    std::env::var("LF_LOWREL").map_or(early(), |v| v == "1") && lf_fast()
}
/// `LF_LOWREL_PAD=1`: the payload ops keep their pre-LOWREL live count (an idle placeholder wire per released bit-0
/// wire), so every cell picks the same route as without LF_LOWREL (its extra room would let a few more cells take
/// the finite-cut retained prebias); only the rail ops get the room.
/// `LF_LOWREL_PAD=2`: pad only the cells (add_halve / double_add, where the prebias routes are chosen); the merged
/// ops and payload barrels keep the extra room.
fn lr_pad_mode() -> u8 {
    std::env::var("LF_LOWREL_PAD").ok().and_then(|v| v.parse().ok()).unwrap_or(if early() { 2 } else { 0 })
}
fn lr_pad_on() -> bool {
    lr_pad_mode() == 1
}
fn lr_pad(c: &mut Builder, n: usize) -> Vec<QubitId> {
    if lr_pad_on() { c.alloc_qubits(n) } else { Vec::new() }
}
/// Cell pad outside any [`lr_pad`] block (modes 1 and 2).
fn lr_pad_c(c: &mut Builder, n: usize) -> Vec<QubitId> {
    if lr_pad_mode() >= 1 { c.alloc_qubits(n) } else { Vec::new() }
}
/// Cell pad inside an [`lr_pad`] block (mode 2 only).
fn lr_pad_c2(c: &mut Builder, n: usize) -> Vec<QubitId> {
    if lr_pad_mode() == 2 { c.alloc_qubits(n) } else { Vec::new() }
}
fn lr_unpad(c: &mut Builder, pads: Vec<QubitId>) {
    for q in pads {
        c.release_clean(q);
    }
}

/// Release an odd rail's bit-0 wire (it holds 1).
fn lr_drop(c: &mut Builder, r: &mut Vec<QubitId>) {
    let q = r.remove(0);
    c.x(q);
    c.free(q);
}
/// Re-materialise an odd rail's bit-0 wire.
fn lr_restore(c: &mut Builder, r: &mut Vec<QubitId>) {
    let q = c.alloc_qubit();
    c.x(q);
    r.insert(0, q);
}
/// [`fast_add_halve_forced`] on bit-0-less rails; the halved target's bit 0 (1) is not held either.
fn fast_add_halve_forced_lr(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    c.cx_all(sign, b);
    // bit 1 of the sum: t1 ^ b1 ^ sign = 0 (the halved rail's bit 0 is 1: released). sign = t1 ^ b1, so the
    // complemented source's bit 1 already equals t1, the carry into bit 2: t's bit-1 wire is cleared and released
    // BEFORE the ladder, which takes its carry-in from the source wire (one more free wire during the add).
    c.cx(b[0], t[0]);
    let low = t.remove(0);
    c.free(low);
    rail_add(c, &b[1..], t, Some(b[0]));
    c.cx_all(sign, b);
}
/// Inverse of [`fast_add_halve_forced_lr`].
fn fast_double_sub_forced_lr(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    // mirror of the forward step: the ladder's carry-in is the complemented source's bit 1; t's bit-1 wire (the
    // same value) is made only after the ladder
    c.cx_all(sign, b);
    c.x_all(t);
    rail_add(c, &b[1..], t, Some(b[0]));
    c.x_all(t);
    let u = c.alloc_qubit();
    c.cx(b[0], u);
    c.cx_all(sign, b);
    t.insert(0, u);
}
/// [`fast_add_halve_choice`] on bit-0-less rails: the halved (even) target comes out holding its bit 0.
fn fast_add_halve_choice_lr(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &[QubitId]) {
    c.cx_all(sign, b);
    c.x_all(b);
    c.x_all(t);
    rail_add(c, b, t, None);
    c.x_all(t);
    c.x_all(b);
    c.cx_all(sign, b);
}
/// Inverse of [`fast_add_halve_choice_lr`]: even target holding bit 0 in, bit-0-less odd target out.
fn fast_double_sub_choice_lr(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &[QubitId]) {
    c.cx_all(sign, b);
    c.x_all(b);
    rail_add(c, b, t, None);
    c.x_all(b);
    c.cx_all(sign, b);
}

/// Put the choice's linear forms on t's wires: t1 <- dq = t1^b1, t_i <- z_i = t_i^b_i^dq (i = 2,3,4; the deep
/// candidate's bits: -b mod 32 is ~b with bit 0 set, and the carries into bits 2..4 are 1 wherever they are read),
/// t_top <- eq = t_top^b_top^dq (signs equal). Self-inverse up to order: [`zlin_off`].
fn zlin_on(c: &mut Builder, t: &[QubitId], b: &[QubitId]) {
    let top = t.len() - 1;
    c.cx(b[1], t[1]);
    for i in 2..5 {
        c.cx(b[i], t[i]);
        c.cx(t[1], t[i]);
    }
    c.cx(b[top.min(b.len() - 1)], t[top]); // a shorter b (LF_SIGNWIRE): its sign wire
    c.cx(t[1], t[top]);
}
fn zlin_off(c: &mut Builder, t: &[QubitId], b: &[QubitId]) {
    let top = t.len() - 1;
    c.cx(t[1], t[top]);
    c.cx(b[top.min(b.len() - 1)], t[top]);
    for i in 2..5 {
        c.cx(t[1], t[i]);
        c.cx(b[i], t[i]);
    }
    c.cx(b[1], t[1]);
}

/// `LF_W1=1` (fast path, seed half): rule W1-window (rails tail research, scratch letters/tail, w1/): at e = 1 with
/// equal signs, take deep iff |x| > 4|B| in a K-bit window at the tick's fixed anchor (only informative for the slow
/// walks whose rails are still near the envelope top), else sign2.
fn lf_w1() -> bool {
    std::env::var("LF_W1").is_ok_and(|v| v == "1")
}
/// Joint-optimised W1 envelope (`LF_PEEL=1`): survivor maxima after sacrificing the failure budget shot by shot,
/// R = 139 (scratchpad peel fit; same fresh-seed failure as the uniform-quantile envelope).
fn lf_peel() -> bool {
    std::env::var("LF_PEEL").is_ok_and(|v| v == "1")
}

/// Rail trims around the payload ops (`LF_TRIM=1`, see [`fwd_tick_fast`] / [`rev_tick_fast`]).
fn lf_trim() -> bool {
    std::env::var("LF_TRIM").is_ok_and(|v| v == "1")
}

/// W1 window size K (`LF_W1K`, default 24).
fn w1_k() -> usize {
    static K: OnceLock<usize> = OnceLock::new();
    *K.get_or_init(|| std::env::var("LF_W1K").ok().and_then(|v| v.parse().ok()).unwrap_or(24))
}
fn w1_anchor(t: usize) -> usize {
    static A: OnceLock<Vec<usize>> = OnceLock::new();
    let a = A.get_or_init(|| {
        // K = 18 reads its window 4 bits lower: every anchor - 4, floored at 3
        let table = if w1_k() == 18 {
            include_str!("leapfrog_data/anch_w1_k18a4.txt")
        } else {
            include_str!("leapfrog_data/anch_w1.txt")
        };
        table.split(',').filter_map(|v| v.trim().parse().ok()).collect()
    });
    a[t.min(a.len() - 1)]
}

/// Comparator operand bit: constant or a wire (with an inversion flag).
#[derive(Clone, Copy)]
enum Lit {
    Zero,
    One,
    W(QubitId, bool),
}
/// One AND of the comparator's carry chain, for measurement-based erasure: t = AND(a ^ ia, b ^ ib) (^ c when the
/// Gidney form XORed the incoming carry wire c into a, b and t).
struct AndRec {
    t: QubitId,
    a: QubitId,
    ia: bool,
    b: QubitId,
    ib: bool,
    c: Option<QubitId>,
}
fn lit_and(c: &mut Builder, recs: &mut Vec<AndRec>, (a, ia): (QubitId, bool), (b, ib): (QubitId, bool), cw: Option<QubitId>) -> QubitId {
    if let Some(cw) = cw {
        c.cx(cw, a);
        c.cx(cw, b);
    }
    if ia { c.x(a); }
    if ib { c.x(b); }
    let t = and_new(c, a, b);
    if ib { c.x(b); }
    if ia { c.x(a); }
    if let Some(cw) = cw {
        c.cx(cw, t);
        c.cx(cw, b);
        c.cx(cw, a);
    }
    recs.push(AndRec { t, a, ia, b, ib, c: cw });
    t
}
fn erase_recs(c: &mut Builder, recs: Vec<AndRec>) {
    for r in recs.into_iter().rev() {
        if let Some(cw) = r.c {
            c.cx(cw, r.a);
            c.cx(cw, r.b);
            c.cx(cw, r.t);
        }
        if r.ia { c.x(r.a); }
        if r.ib { c.x(r.b); }
        and_erase(c, r.t, r.a, r.b);
        if r.ib { c.x(r.b); }
        if r.ia { c.x(r.a); }
        if let Some(cw) = r.c {
            c.cx(cw, r.b);
            c.cx(cw, r.a);
        }
    }
}
/// MAJ of three literals (carry of a full adder), folding constants; returns the carry literal.
fn lit_maj(c: &mut Builder, recs: &mut Vec<AndRec>, x: Lit, y: Lit, cin: Lit) -> Lit {
    use Lit::*;
    let and2 = |c: &mut Builder, recs: &mut Vec<AndRec>, p: Lit, q: Lit| -> Lit {
        match (p, q) {
            (Zero, _) | (_, Zero) => Zero,
            (One, o) | (o, One) => o,
            (W(a, ia), W(b, ib)) => W(lit_and(c, recs, (a, ia), (b, ib), None), false),
        }
    };
    let neg = |l: Lit| match l {
        Zero => One,
        One => Zero,
        W(q, i) => W(q, !i),
    };
    let or2 = |c: &mut Builder, recs: &mut Vec<AndRec>, p: Lit, q: Lit| -> Lit { neg(and2(c, recs, neg(p), neg(q))) };
    match (x, y, cin) {
        (Zero, o, k) | (o, Zero, k) | (o, k, Zero) => and2(c, recs, o, k),
        (One, o, k) | (o, One, k) | (o, k, One) => or2(c, recs, o, k),
        (W(a, ia), W(b, ib), W(cw, ic)) => {
            // MAJ = AND(x ^ c, y ^ c) ^ c (Gidney); the wires a, b carry raw values, so fold c's inversion in
            let t = lit_and(c, recs, (a, ia ^ ic), (b, ib ^ ic), Some(cw));
            W(t, ic)
        }
    }
}
/// The W1 window bits of `r` (width >= 6) at tick t: positions [h, h + K + 2), h = max(anchor - K, 0); a position
/// at or above the sign wire is the constant 0 (sign extension XOR sign). Returns the wires (Some) or constants.
fn w1_window(r: &[QubitId], t: usize) -> Vec<Option<QubitId>> {
    let h = w1_anchor(t).saturating_sub(w1_k());
    (h..h + w1_k() + 2).map(|p| (p + 1 < r.len()).then(|| r[p])).collect()
}
/// Conjugate the window wires with their register's sign (ones' complement magnitude); self-inverse.
fn w1_conj(c: &mut Builder, r: &[QubitId], win: &[Option<QubitId>]) {
    let sg = *r.last().unwrap();
    for q in win.iter().flatten() {
        c.cx(sg, *q);
    }
}
/// Carry chain of a + NOT(4b) (window magnitudes of x and B): its carry-out is [a > 4b]. Returns the result literal
/// and the AND records (window conjugation must be ON while building and while erasing).
fn w1_chain(c: &mut Builder, wa: &[Option<QubitId>], wb: &[Option<QubitId>]) -> (Lit, Vec<AndRec>) {
    let l = wa.len();
    let mut recs = Vec::new();
    let mut carry = Lit::Zero;
    for j in 0..l + 2 {
        let x = match wa.get(j).copied().flatten() {
            Some(q) => Lit::W(q, false),
            None => Lit::Zero,
        };
        let y = if j < 2 {
            Lit::One
        } else {
            match wb.get(j - 2).copied().flatten() {
                Some(q) => Lit::W(q, true),
                None => Lit::One,
            }
        };
        carry = lit_maj(c, &mut recs, x, y, carry);
    }
    (carry, recs)
}

/// sign2 choice into `out` and the barrel letters into k1, k2 (all xor into zero wires), 5 Toffoli:
/// out = dq ^ 1 ^ [z2=z3=z4=0] ^ (z2 & eq); Dsel = out ^ dq (deep taken); k2 = Dsel & !z2; k1 = Dsel ^ (k2 & z3).
fn fast_choice(c: &mut Builder, t: &[QubitId], b: &[QubitId], out: QubitId, k1: QubitId, k2: QubitId, tick: usize) {
    let top = t.len() - 1;
    let w1 = lf_w1().then(|| {
        let (wa, wb) = (w1_window(t, tick), w1_window(b, tick));
        w1_conj(c, t, &wa);
        w1_conj(c, b, &wb);
        let (w, recs) = w1_chain(c, &wa, &wb);
        w1_conj(c, b, &wb);
        w1_conj(c, t, &wa);
        (w, recs, wa, wb)
    });
    zlin_on(c, t, b);
    for i in 2..5 {
        c.x(t[i]);
    }
    let a1 = and_new(c, t[2], t[3]);
    let a2 = and_new(c, a1, t[4]);
    for i in 2..5 {
        c.x(t[i]);
    }
    let g = and_new(c, t[2], t[top]);
    c.cx(t[1], out);
    c.x(out);
    c.cx(a2, out);
    // W1: at e = 1 with equal signs the window can still accept deep: reject only if NOT [|x| > 4|B|]
    match w1.as_ref().map(|v| v.0) {
        None | Some(Lit::Zero) => c.cx(g, out),
        Some(Lit::One) => {}
        Some(Lit::W(wq, inv)) => {
            let mut r2 = Vec::new();
            let g2 = lit_and(c, &mut r2, (g, false), (wq, !inv), None);
            c.cx(g2, out);
            erase_recs(c, r2);
        }
    }
    and_erase(c, g, t[2], t[top]);
    for i in 2..5 {
        c.x(t[i]);
    }
    // barrel letters as XORs of wires at hand (t2 holds !z2), no Toffoli: k2 = Dsel & !z2 = !z2 ^ a2 (Dsel =
    // 1 ^ a2 ^ g.., g lies inside z2 and a2 inside !z2); k2 & z3 = !z2 & z3 = !z2 ^ a1, so k1 = Dsel ^ !z2 ^ a1
    c.cx(t[2], k2);
    c.cx(a2, k2);
    c.cx(t[2], k1);
    c.cx(a1, k1);
    and_erase(c, a2, a1, t[4]);
    and_erase(c, a1, t[2], t[3]);
    // Dsel on out's wire
    c.cx(t[1], out);
    for i in 2..5 {
        c.x(t[i]);
    }
    c.cx(out, k1);
    c.cx(t[1], out);
    zlin_off(c, t, b);
    if let Some((_, recs, wa, wb)) = w1 {
        w1_conj(c, t, &wa);
        w1_conj(c, b, &wb);
        erase_recs(c, recs);
        w1_conj(c, b, &wb);
        w1_conj(c, t, &wa);
    }
}

/// Conditional (classical bit `m`) phase flip on a & b & d: one AND, fired only when m is set.
fn ccz_if(c: &mut Builder, a: QubitId, b: QubitId, d: QubitId, m: crate::circuit::BitId) {
    c.push_condition(m);
    let q = and_new(c, a, b);
    c.cz(q, d);
    and_erase(c, q, a, b);
    c.pop_condition();
}

/// MBU erase of the choice letter on the reverse tick ((t, b) back at the pre-choice state).
fn fast_choice_erase(c: &mut Builder, t: &[QubitId], b: &[QubitId], out: QubitId, tick: usize) {
    let top = t.len() - 1;
    let m = c.alloc_bit();
    c.hmr(out, m);
    c.release_clean(out);
    // W1: the window compare is only needed for the phase fix, i.e. on shots whose outcome m is 1
    let w1 = lf_w1().then(|| {
        let (wa, wb) = (w1_window(t, tick), w1_window(b, tick));
        c.push_condition(m);
        w1_conj(c, t, &wa);
        w1_conj(c, b, &wb);
        let (w, recs) = w1_chain(c, &wa, &wb);
        w1_conj(c, b, &wb);
        w1_conj(c, t, &wa);
        c.pop_condition();
        (w, recs, wa, wb)
    });
    zlin_on(c, t, b);
    c.x(t[1]);
    c.z_if(t[1], m); // dq ^ 1
    c.x(t[1]);
    for i in 2..5 {
        c.x(t[i]);
    }
    ccz_if(c, t[2], t[3], t[4], m); // !z2 & !z3 & !z4
    for i in 2..5 {
        c.x(t[i]);
    }
    match w1.as_ref().map(|v| v.0) {
        None | Some(Lit::Zero) => c.cz_if(t[2], t[top], m), // z2 & eq
        Some(Lit::One) => {}
        Some(Lit::W(wq, inv)) => {
            // phase of z2 & eq & !w, on shots with m = 1
            c.push_condition(m);
            let q = and_new(c, t[2], t[top]);
            if !inv { c.x(wq); }
            c.cz(q, wq);
            if !inv { c.x(wq); }
            and_erase(c, q, t[2], t[top]);
            c.pop_condition();
        }
    }
    zlin_off(c, t, b);
    if let Some((_, recs, wa, wb)) = w1 {
        c.push_condition(m);
        w1_conj(c, t, &wa);
        w1_conj(c, b, &wb);
        erase_recs(c, recs);
        w1_conj(c, b, &wb);
        w1_conj(c, t, &wa);
        c.pop_condition();
    }
    c.free_bit(m);
}

/// MBU erase of the barrel letters on the reverse tick, from x3 (the target before the barrel):
/// k2 = !t0 & !t1, k1 = !t0 ^ (!t0 & !t1 & t2).
fn fast_k_erase(c: &mut Builder, t: &[QubitId], k1: QubitId, k2: QubitId) {
    c.x(t[0]);
    c.x(t[1]);
    // k1 first, while k2 is still live: k1 = !t0 ^ (k2 & t2), so its phase fix is Z + CZ (no Toffoli)
    let m1 = c.alloc_bit();
    c.hmr(k1, m1);
    c.release_clean(k1);
    c.z_if(t[0], m1);
    c.cz_if(k2, t[2], m1);
    c.free_bit(m1);
    let m2 = c.alloc_bit();
    c.hmr(k2, m2);
    c.release_clean(k2);
    c.cz_if(t[0], t[1], m2);
    c.free_bit(m2);
    c.x(t[1]);
    c.x(t[0]);
}

/// Rail barrel with the sign fill absorbed into re-based reflections (barrel research, scratch barrel_mc/
/// rail_lin_explicit.py): h1 = k1 & S, h2 = k2 & S; rho_0 (k2, minus the pair (1, w-1), done by h2), rho_-2
/// (k1 ^ k2), rho_-3 (k1, minus the no-op pair (w-2, w-1)); 1.5w - 2 Toffoli (even w). Same promise: the e low
/// wires are 0. `LF_RAILLIN=0` keeps [`fast_rail_barrel`]'s sign-fill form.
///
/// `drop0` (forward only; the caller holds an odd result without its bit-0 wire, LF_LOWREL): wire 0 ends as the
/// constant 1, so the last Fredkin that writes it, rho_-3's pair (0, w-3) under k1, needs no Toffoli. When k1 = 1 the
/// partner wire holds the rail's lowest set bit (1) and takes t0; when k1 = 0, t0 already holds that 1. Either way
/// t[w-3] <- t0 ^ t[w-3] ^ 1, and t0 is left holding 1 ^ (k1 & !t[w-3]): it is measured away (phase fix
/// CZ(k1, !t[w-3])) and released here. Returns true when wire 0 was released (the caller only forgets it).
fn lin_rail_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool, drop0: bool) -> bool {
    let w = t.len();
    let drop0 = drop0 && !inverse && w >= 4 && !std::env::var("LF_BARREL_DROP0").is_ok_and(|v| v == "0");
    let mut dropped = false;
    let s = t[w - 1];
    let h1 = and_new(c, k1, s);
    let h2 = and_new(c, k2, s);
    #[derive(Clone, Copy)]
    enum Op {
        Cx(QubitId, usize),
        F(u8, usize, usize),
    }
    let refl = |x: isize| -> Vec<(usize, usize)> {
        (0..w)
            .filter_map(|i| {
                let j = (x - i as isize).rem_euclid(w as isize) as usize;
                (i < j).then_some((i, j))
            })
            .collect()
    };
    let mut ops = vec![Op::Cx(h1, 0), Op::Cx(h2, 1), Op::Cx(h2, w - 1)];
    ops.extend(refl(0).into_iter().filter(|&p| p != (1, w - 1)).map(|(a, b)| Op::F(2, a, b)));
    ops.extend(refl(w as isize - 2).into_iter().map(|(a, b)| Op::F(3, a, b)));
    ops.extend(refl(w as isize - 3).into_iter().filter(|&p| p != (w - 2, w - 1)).map(|(a, b)| Op::F(1, a, b)));
    ops.extend([Op::Cx(h2, w - 2), Op::Cx(h2, w - 1)]);
    if inverse {
        ops.reverse();
    }
    let mut k12 = false; // k2 currently holds k1 ^ k2
    for op in ops {
        match op {
            Op::Cx(h, i) => c.cx(h, t[i]),
            Op::F(kind, a, b) => {
                let want = kind == 3;
                if want != k12 {
                    c.cx(k1, k2);
                    k12 = want;
                }
                let ctrl = if kind == 1 { k1 } else { k2 };
                if drop0 && kind == 1 && (a, b) == (0, w - 3) {
                    c.cx(t[0], t[b]);
                    c.x(t[b]);
                    c.x(t[0]); // now k1 & !t[b]
                    let m = c.alloc_bit();
                    c.hmr(t[0], m);
                    c.x(t[b]);
                    c.cz_if(k1, t[b], m);
                    c.x(t[b]);
                    c.free_bit(m);
                    c.release_clean(t[0]);
                    dropped = true;
                } else {
                    fredkin(c, ctrl, t[a], t[b]);
                }
            }
        }
    }
    if k12 {
        c.cx(k1, k2);
    }
    and_erase(c, h1, k1, t[w - 1]);
    and_erase(c, h2, k2, t[w - 1]);
    dropped
}

/// Rail barrel with the 3-Toffoli sign fill (h = k2 & sg -> t1, t0; h2 = k1 & h -> t2, t0; k1 & sg -> t0).
fn fast_rail_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool, drop0: bool) -> bool {
    if !std::env::var("LF_RAILLIN").is_ok_and(|v| v == "0") {
        return lin_rail_barrel(c, k1, k2, t, inverse, drop0);
    }
    let sg = *t.last().unwrap();
    if inverse {
        rot4(c, k1, k2, t, true);
    }
    let h = and_new(c, k2, sg);
    c.cx(h, t[1]);
    c.cx(h, t[0]);
    let h2 = and_new(c, k1, h);
    c.cx(h2, t[2]);
    c.cx(h2, t[0]);
    c.ccx(k1, sg, t[0]);
    and_erase(c, h2, k1, h);
    and_erase(c, h, k2, sg);
    if !inverse {
        rot4(c, k1, k2, t, false);
    }
    false
}

/// `t <- (t + (-1)^sign * b) / 2` on rails (exact: the sum is even). Widths: t and b at w on entry and exit.
fn rail_add_halve(c: &mut Builder, sign: QubitId, b: &mut Vec<QubitId>, t: &mut Vec<QubitId>) {
    let w = t.len();
    resize(c, t, w + 1);
    resize(c, b, w + 1);
    rail_signed_add(c, sign, b, t);
    resize(c, b, w);
    let low = t.remove(0);
    c.free(low);
}

/// Inverse of [`rail_add_halve`]: `t <- 2 t - (-1)^sign * b`.
fn rail_double_sub(c: &mut Builder, sign: QubitId, b: &mut Vec<QubitId>, t: &mut Vec<QubitId>) {
    let w = t.len();
    let low = c.alloc_qubit();
    t.insert(0, low);
    resize(c, b, w + 1);
    c.x(sign);
    rail_signed_add(c, sign, b, t);
    c.x(sign);
    resize(c, b, w);
    resize(c, t, w);
}

/// [`pp_sign_into`] from the two bit-1 wires.
fn pp_sign_into1(c: &mut Builder, t1: QubitId, b1: QubitId, q: QubitId) {
    c.cx(t1, q);
    c.cx(b1, q);
}

/// Forced ping-pong sign for the next step: 1 (subtract) iff t[1] != b[1].
fn pp_sign_into(c: &mut Builder, t: &[QubitId], b: &[QubitId], q: QubitId) {
    c.cx(t[1], q);
    c.cx(b[1], q);
}

/// AND into a fresh qubit; and its measurement-based uncompute.
#[track_caller]
fn and_new(c: &mut Builder, a: QubitId, b: QubitId) -> QubitId {
    let q = c.alloc_qubit();
    c.ccx(a, b, q);
    q
}
fn and_erase(c: &mut Builder, q: QubitId, a: QubitId, b: QubitId) {
    let m = c.alloc_bit();
    c.hmr(q, m);
    c.cz_if(a, b, m);
    c.free_bit(m);
    c.release_clean(q);
}

/// sign2 fourth-step choice into `out` (xor). dq = t[1] ^ b[1] (1 -> t + b is the deep candidate; the deep
/// sign bit is !dq). The deep candidate D (sc = D mod 32) is taken iff it is admissible (D mod 32 != 0, i.e.
/// e = v2(D) - 1 <= 3) and NOT (e == 1 and sign(t) == sign(+-b)): an e = 1 deep step that adds equal-signed
/// magnitudes grows the rail. a2 = [D == 0 mod 32] and g = [e == 1 and equal signs] are exclusive (g needs
/// sc[2] = 1), so deep = 1 ^ a2 ^ g and out ^= dq ^ deep. Needs t, b at width >= 6 (callers sign-extend).
fn choice_xor(c: &mut Builder, t: &[QubitId], b: &[QubitId], out: QubitId) {
    let (tt, bt) = (*t.last().unwrap(), *b.last().unwrap());
    let dq = c.alloc_qubit();
    c.cx(t[1], dq);
    c.cx(b[1], dq);
    let sc = c.alloc_qubits(5);
    c.cx_pairs(&t[..5], &sc);
    let bl = c.alloc_qubits(5);
    c.cx_pairs(&b[..5], &bl);
    // sc = (t + (-1)^{!dq} b) mod 32
    c.x(dq);
    signed_add(c, dq, &bl, &sc);
    c.x(dq);
    // a2 = (sc2 == sc3 == sc4 == 0)
    for &q in &sc[2..5] {
        c.x(q);
    }
    let a1 = and_new(c, sc[2], sc[3]);
    let a2 = and_new(c, a1, sc[4]);
    c.cx(dq, out);
    c.cx(a2, out);
    c.x(out);
    and_erase(c, a2, a1, sc[4]);
    and_erase(c, a1, sc[2], sc[3]);
    for &q in &sc[2..5] {
        c.x(q);
    }
    if !rule_v0() {
        // equal signs: !(t_top ^ b_top ^ !dq) = t_top ^ b_top ^ dq, held on dq's wire
        c.cx(tt, dq);
        c.cx(bt, dq);
        let g = and_new(c, dq, sc[2]);
        c.cx(g, out);
        and_erase(c, g, dq, sc[2]);
        c.cx(bt, dq);
        c.cx(tt, dq);
    }
    // undo sc: sc -= (-1)^{!dq} b  ==  sc += (-1)^{dq} b
    signed_add(c, dq, &bl, &sc);
    c.cx_pairs(&b[..5], &bl);
    c.free_vec(&bl);
    c.cx_pairs(&t[..5], &sc);
    c.free_vec(&sc);
    c.cx(t[1], dq);
    c.cx(b[1], dq);
    c.free(dq);
}

/// Barrel bits of a target with e = v2(t) <= 3 (xor into k1, k2):
/// k2 = (e >= 2) = !t0 & !t1 ; k1 = (e in {1,3}) = !t0 & (t1 | !t2) = !t0 & !(!t1 & t2).
fn barrel_bits_xor(c: &mut Builder, t: &[QubitId], k1: QubitId, k2: QubitId) {
    c.x(t[0]);
    c.x(t[1]);
    c.ccx(t[0], t[1], k2);
    let u = and_new(c, t[1], t[2]);
    c.x(u);
    c.ccx(t[0], u, k1);
    c.x(u);
    and_erase(c, u, t[1], t[2]);
    c.x(t[1]);
    c.x(t[0]);
}

/// Fredkin pairs of the 4-way cyclic rotation out[i] = in[(i + e) mod n], e = k1 + 2 k2, as three controlled
/// reflections rho_x: i -> x - i (two reflections compose to a rotation): rho_1 on e in {1,3} (ctrl k1),
/// rho_0 on e in {1,2} (ctrl k1 ^ k2, held on k2), rho_-2 on e in {2,3} (ctrl k2). 1.5n - 2 Fredkins instead
/// of the 2n - 3 of two nested shift stages (red-team construction, scratch redteam_rot/rotnet.py).
fn refl4_pairs(n: usize) -> [Vec<(usize, usize)>; 3] {
    let refl = |x: isize| -> Vec<(usize, usize)> {
        (0..n)
            .filter_map(|i| {
                let j = (x - i as isize).rem_euclid(n as isize) as usize;
                (i < j).then_some((i, j))
            })
            .collect()
    };
    [refl(1), refl(0), refl(-2)]
}

/// The 4-way rotation of `t` by e = k1 + 2 k2 (inverse: by -e).
fn rot4(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool) {
    let [r1, r0, rm2] = refl4_pairs(t.len());
    let stages: [(&Vec<(usize, usize)>, u8); 3] = [(&r1, 1), (&r0, 2), (&rm2, 3)];
    let order: Vec<usize> = if inverse { vec![2, 1, 0] } else { vec![0, 1, 2] };
    for s in order {
        let (pairs, kind) = stages[s];
        let ctrl = if kind == 1 { k1 } else { k2 };
        if kind == 2 {
            c.cx(k1, k2);
        }
        for &(a, b) in pairs {
            fredkin(c, ctrl, t[a], t[b]);
        }
        if kind == 2 {
            c.cx(k1, k2);
        }
    }
}

/// Rail barrel: arithmetic shift right by e = k1 + 2 k2 (the e low wires are 0): the sign goes into the e low
/// wires, then one cyclic 4-way rotation carries them to the top. 1.5w + 2 Toffoli (inverse: shift left).
fn rail_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool) {
    let sg = *t.last().unwrap();
    if inverse {
        rot4(c, k1, k2, t, true);
    }
    let a = and_new(c, k1, k2);
    c.cx(k1, a);
    c.cx(k2, a); // a = [e >= 1]
    c.ccx(a, sg, t[0]);
    c.cx(k2, a);
    c.cx(k1, a); // a = [e == 3]
    c.ccx(k2, sg, t[1]);
    c.ccx(a, sg, t[2]);
    and_erase(c, a, k1, k2);
    if !inverse {
        rot4(c, k1, k2, t, false);
    }
}

/// Bits [lo, hi) of m * (f - 1) for m in [0, 8) as XORs of the monomials m0, m1, m2, m0m1, m0m2, m1m2, m0m1m2
/// (algebraic normal form; index = monomial bit mask).
fn fold_anf(lo: usize, hi: usize) -> Vec<Vec<usize>> {
    let fm1: u128 = (1u128 << 32) + 976;
    (lo..hi)
        .map(|b| {
            (1..8usize)
                .filter(|&mask| {
                    let mut coef = 0u128;
                    for sub in 0..8usize {
                        if sub & !mask == 0 {
                            let mv = (0..3).filter(|u| sub >> u & 1 == 1).map(|u| 1u128 << u).sum::<u128>();
                            coef ^= (mv * fm1) >> b & 1;
                        }
                    }
                    coef == 1
                })
                .collect()
        })
        .collect()
}

/// Put (parity of `list`) ^ comp ^ carry on one wire for an AND control; returns the wire. With an empty
/// list the carry wire itself is used (X'd when comp). [`v_off`] undoes it.
fn v_on(c: &mut Builder, list: &[QubitId], comp: bool, ci: Option<QubitId>) -> QubitId {
    let h = match list.split_first() {
        Some((&h, rest)) => {
            for &q in rest {
                c.cx(q, h);
            }
            if let Some(ci) = ci {
                c.cx(ci, h);
            }
            h
        }
        None => ci.expect("live carry"),
    };
    if comp {
        c.x(h);
    }
    h
}
fn v_off(c: &mut Builder, list: &[QubitId], comp: bool, ci: Option<QubitId>) {
    match list.split_first() {
        Some((&h, rest)) => {
            if comp {
                c.x(h);
            }
            if let Some(ci) = ci {
                c.cx(ci, h);
            }
            for &q in rest {
                c.cx(q, h);
            }
        }
        None => {
            if comp {
                c.x(ci.unwrap());
            }
        }
    }
}

/// Gidney ripple `acc += addend + cin (mod 2^len)` where addend bit i is the parity of the wires `add[i]`
/// (possibly none). Carries that are provably 0 are skipped; carries are measurement-uncomputed.
fn ladder_parity_add(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>], cin: Option<QubitId>) {
    let n = acc.len();
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    carry[0] = cin;
    for i in 0..n - 1 {
        let ci = carry[i];
        if ci.is_none() && add[i].is_empty() {
            continue;
        }
        if let Some(ci) = ci {
            c.cx(ci, acc[i]);
        }
        let v = v_on(c, &add[i], false, ci);
        if i + 2 == n {
            // the carry into the top position is used once, for that position's sum bit: XOR it straight into
            // the top wire (one CCX, nothing to erase) instead of holding it on a carry wire
            c.ccx(acc[i], v, acc[n - 1]);
            v_off(c, &add[i], false, ci);
            if let Some(ci) = ci {
                c.cx(ci, acc[n - 1]);
                c.cx(ci, acc[i]);
            }
            continue;
        }
        let t = and_new(c, acc[i], v);
        v_off(c, &add[i], false, ci);
        if let Some(ci) = ci {
            c.cx(ci, t);
            c.cx(ci, acc[i]);
        }
        carry[i + 1] = Some(t);
    }
    for i in (0..n).rev() {
        let ci = carry[i];
        if i + 1 < n {
            if let Some(next) = carry[i + 1] {
                if let Some(ci) = ci {
                    c.cx(ci, next);
                    c.cx(ci, acc[i]);
                }
                let v = v_on(c, &add[i], false, ci);
                and_erase(c, next, acc[i], v);
                v_off(c, &add[i], false, ci);
                if let Some(ci) = ci {
                    c.cx(ci, acc[i]);
                }
            }
        }
        for &q in &add[i] {
            c.cx(q, acc[i]);
        }
        if let Some(ci) = ci {
            c.cx(ci, acc[i]);
        }
    }
}

/// `out ^= carry_out(acc + addend + cin)` (addend bits: parity of `add[i]`, complemented when `comp`);
/// acc unchanged; Gidney carries, measurement-uncomputed.
fn carry_out_parity_xor(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>], comp: bool, cin: QubitId, out: Option<QubitId>) {
    let n = acc.len();
    // Phase-only form: the top carry is never built (see `carry_out_xor`): one CZ on the two AND inputs of the
    // top position and the phase (-1)^(NOT carry[n - 1]).
    let m = if out.is_none() && n >= 1 { n - 1 } else { n };
    let mut carry = vec![cin];
    for i in 0..m {
        let ci = carry[i];
        c.cx(ci, acc[i]);
        let v = v_on(c, &add[i], comp, Some(ci));
        let t = and_new(c, acc[i], v);
        v_off(c, &add[i], comp, Some(ci));
        c.cx(ci, t);
        c.cx(ci, acc[i]);
        carry.push(t);
    }
    match out {
        Some(out) => c.cx(carry[n], out),
        None => {
            let ci = carry[m];
            if m < n {
                c.cx(ci, acc[m]);
                let v = v_on(c, &add[m], comp, Some(ci));
                c.cz(acc[m], v);
                v_off(c, &add[m], comp, Some(ci));
                c.cx(ci, acc[m]);
            }
            c.x(ci);
            c.z_if(ci, NO_BIT);
            c.x(ci);
        }
    }
    for i in (0..m).rev() {
        let (ci, t) = (carry[i], carry[i + 1]);
        c.cx(ci, t);
        c.cx(ci, acc[i]);
        let v = v_on(c, &add[i], comp, Some(ci));
        and_erase(c, t, acc[i], v);
        v_off(c, &add[i], comp, Some(ci));
        c.cx(ci, acc[i]);
    }
}

/// [`ladder_parity_add`] under the walk cap, split recursively: when the ladder does not fit, the low chunk (sized to
/// the room) goes first with its carry-out kept, the rest (recursively) takes it as carry-in, and each kept carry is
/// erased exactly as NOT carry_out(acc_low_new + NOT addend_low + NOT cin) (MBU-halved unless LF_SPLIT_MBU=0).
fn ladder_parity_add_capped(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>]) {
    lpa_capped(c, acc, add, None);
}
fn lpa_capped(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>], cin: Option<QubitId>) {
    let n = acc.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let off = std::env::var("LF_RAIL_SPLIT").is_ok_and(|v| v == "0");
    // the parity ladder holds n - 2 carries (its top carry goes straight into the top sum wire)
    if off || n <= room + 1 + split_tight() as usize {
        ladder_parity_add(c, acc, add, cin);
        return;
    }
    // tight: the minimal low chunk when it fits beside its kept carry; otherwise the room-sized low chunk (recursive)
    let tight = split_tight() && n - room + 2 <= room;
    let l = if tight { n - room - 1 } else { room.saturating_sub(4) };
    if (!tight && l < 4) || l + 1 >= n {
        ladder_parity_add(c, acc, add, cin);
        return;
    }
    let cq = c.alloc_qubit();
    let mut lo = acc[..l].to_vec();
    lo.push(cq);
    let mut lo_add = add[..l].to_vec();
    lo_add.push(vec![]);
    ladder_parity_add(c, &lo, &lo_add, cin);
    lpa_capped(c, &acc[l..], &add[l..], Some(cq));
    let ncin = match cin {
        Some(q) => {
            c.x(q);
            q
        }
        None => {
            let o = c.alloc_qubit();
            c.x(o);
            o
        }
    };
    let q0 = pmark(c);
    if split_mbu() {
        let m = c.alloc_bit();
        c.hmr(cq, m);
        c.release_clean(cq);
        c.push_condition(m);
        carry_out_parity_xor(c, &acc[..l], &add[..l], true, ncin, None);
        c.pop_condition();
        c.free_bit(m);
    } else {
        carry_out_parity_xor(c, &acc[..l], &add[..l], true, ncin, Some(cq));
        c.x(cq);
        c.free(cq);
    }
    pacc(c, "split.fold_erase", q0);
    match cin {
        Some(q) => c.x(q),
        None => {
            c.x(ncin);
            c.free(ncin);
        }
    }
}

/// Controlled modular scaling of a payload by 2^-e (inverse: 2^e), e = k1 + 2 k2 in [0, 3]. With p == -1 and
/// f == 1 (mod 8): m = P mod 2^e gives P 2^-e = rotr_e(P - m (f - 1)) (mod p); f - 1 = 2^32 + 61 * 16 leaves
/// m in bits 0..2, and the rotation carries it to the top. One fold ladder over bits [4, 4 + fs) whose addend
/// bits are monomials of m, then the 4-way reflection rotation.
fn cmod_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, p: &[QubitId], inverse: bool) {
    let extra: usize = std::env::var("LF_FOLD_EXTRA").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let (lo, hi) = (4, (4 + go_fs("GO_FG_P") + extra).min(N));
    let t = and_new(c, k1, k2);
    if inverse {
        rot4(c, k1, k2, p, true);
    }
    c.cx(k1, t);
    c.cx(k2, t);
    let m0 = and_new(c, t, p[0]); // [e >= 1] & p0
    c.cx(k2, t);
    c.cx(k1, t);
    let m1 = and_new(c, k2, p[1]);
    let m2 = and_new(c, t, p[2]);
    let m01 = and_new(c, m0, m1);
    let m02 = and_new(c, m0, m2);
    let m12 = and_new(c, m1, m2);
    let m012 = and_new(c, m01, m2);
    let mono = [m0, m0, m1, m01, m2, m02, m12, m012]; // index = monomial mask (0 unused)
    let add: Vec<Vec<QubitId>> = fold_anf(lo, hi).into_iter().map(|ms| ms.into_iter().map(|k| mono[k]).collect()).collect();
    let acc = &p[lo..hi];
    if inverse {
        ladder_parity_add_capped(c, acc, &add);
    } else {
        c.x_all(acc);
        ladder_parity_add_capped(c, acc, &add);
        c.x_all(acc);
    }
    and_erase(c, m012, m01, m2);
    and_erase(c, m12, m1, m2);
    and_erase(c, m02, m0, m2);
    and_erase(c, m01, m0, m1);
    and_erase(c, m2, t, p[2]);
    and_erase(c, m1, k2, p[1]);
    c.cx(k1, t);
    c.cx(k2, t);
    and_erase(c, m0, t, p[0]);
    c.cx(k2, t);
    c.cx(k1, t);
    if !inverse {
        rot4(c, k1, k2, p, false);
    }
    and_erase(c, t, k1, k2);
}

// ---- LF_MERGED: last add-halve cell + payload barrel as one Montgomery step (scratch paycell/merged.py) ----
//
// Forward:  T <- (T + (-1)^sg S) 2^-k,  k = 1 + e, e = k1 + 2 k2.  In the sg-complemented frame the production
// chunked adder leaves A (256 bits) and its overflow ov; V = A + ov f == T +- S (mod p).  With p == -1 and
// f == 1 (mod 16), mu = V mod 2^k = (A + ov) mod 2^k and Y = rotr_k(V - mu (f - 1)): one fold ladder over bits
// [0, MW) adds ov (bit 0) and (f - 1)(u - 15) (bits 4..), u = n + 15, n = ov -+ mu in [-15, 16] (5 bits); the
// addend bits are ANF monomials of u.  mu's bits are read off the ladder's own low sum bits (hook after bit 3).
// The overflow is erased exactly from the top ripple's carry frame when the fold fits beside that ripple (exact
// route, [`merged_split`], as the retained-prebias cell does) and otherwise with the production cell's flag
// compare; the rotation by 1 is free (swaps), the rotation by e is the 4-way reflection network.  Reverse: the
// exact inverse map T <- 2^k T - (-1)^sg S (mu = the rotated-in low bits, gated copies erased from the result's
// low bits, S_low and ov).  Used for ticks t < LF_MERGED_MAX (default LF_TIE_FROM: no tie-safe mode) whose
// fold phase fits under the walk cap ([`merged_fits`]); other ticks keep the cell + [`cmod_barrel`].

/// `LF_MERGED=1`: use the merged op on ticks where it fits ([`merged_fits`]).
fn lf_merged() -> bool {
    std::env::var("LF_MERGED").is_ok_and(|v| v == "1")
}
/// Merged fold window (bits [0, MW) of the payload); the constant is < 2^37, so 24 bits of escape margin.
fn merged_win() -> usize {
    static W: OnceLock<usize> = OnceLock::new();
    *W.get_or_init(|| std::env::var("LF_MERGED_WIN").ok().and_then(|v| v.parse().ok()).unwrap_or(61))
}
const M_OFF: i128 = 15;

/// Linear form over wires (XOR of the wires, XOR a constant).
#[derive(Clone, Debug, Default)]
struct Lin {
    w: Vec<QubitId>,
    one: bool,
}
impl Lin {
    fn of(qs: &[QubitId]) -> Lin {
        let mut l = Lin::default();
        for &q in qs {
            l = l.x(&Lin { w: vec![q], one: false });
        }
        l
    }
    fn k(b: bool) -> Lin {
        Lin { w: vec![], one: b }
    }
    fn x(&self, o: &Lin) -> Lin {
        let mut w = self.w.clone();
        for &q in &o.w {
            if let Some(p) = w.iter().position(|&r| r == q) {
                w.remove(p);
            } else {
                w.push(q);
            }
        }
        Lin { w, one: self.one ^ o.one }
    }
}
fn lin_on(c: &mut Builder, l: &Lin, h: QubitId) {
    for &q in &l.w {
        if q != h {
            c.cx(q, h);
        }
    }
    if l.one {
        c.x(h);
    }
}
fn lin_off(c: &mut Builder, l: &Lin, h: QubitId) {
    if l.one {
        c.x(h);
    }
    for &q in l.w.iter().rev() {
        if q != h {
            c.cx(q, h);
        }
    }
}
/// Host two forms on wires (each parity on one of its own wires) so that the second hosting reads no wire the
/// first one changed: the first form is hosted on a wire the second does not contain. Returns
/// (first_is_a, host_a, host_b).
fn lin_hosts(a: &Lin, b: &Lin) -> (bool, QubitId, QubitId) {
    assert!(!a.w.is_empty() && !b.w.is_empty(), "AND of a constant form");
    if let Some(&ha) = a.w.iter().find(|q| !b.w.contains(q)) {
        (true, ha, b.w[0])
    } else {
        let &hb = b.w.iter().find(|q| !a.w.contains(q)).expect("AND of two equal forms");
        (false, a.w[0], hb)
    }
}
fn lin_pair_on(c: &mut Builder, a: &Lin, b: &Lin) -> (QubitId, QubitId) {
    let (af, ha, hb) = lin_hosts(a, b);
    if af {
        lin_on(c, a, ha);
        lin_on(c, b, hb);
    } else {
        lin_on(c, b, hb);
        lin_on(c, a, ha);
    }
    (ha, hb)
}
fn lin_pair_off(c: &mut Builder, a: &Lin, b: &Lin) {
    let (af, ha, hb) = lin_hosts(a, b);
    if af {
        lin_off(c, b, hb);
        lin_off(c, a, ha);
    } else {
        lin_off(c, a, ha);
        lin_off(c, b, hb);
    }
}
/// AND of two linear forms into a fresh wire (one Toffoli).
fn lin_and(c: &mut Builder, a: &Lin, b: &Lin) -> QubitId {
    let q = c.alloc_qubit();
    let (ha, hb) = lin_pair_on(c, a, b);
    c.ccx(ha, hb, q);
    lin_pair_off(c, a, b);
    q
}
/// Measurement-based erasure of a wire holding AND(a, b) (zero Toffoli).
fn lin_and_erase(c: &mut Builder, q: QubitId, a: &Lin, b: &Lin) {
    let m = c.alloc_bit();
    c.hmr(q, m);
    let (ha, hb) = lin_pair_on(c, a, b);
    c.cz_if(ha, hb, m);
    lin_pair_off(c, a, b);
    c.free_bit(m);
    c.release_clean(q);
}
fn lin_xor_into(c: &mut Builder, l: &Lin, t: QubitId) {
    for &q in &l.w {
        assert_ne!(q, t);
        c.cx(q, t);
    }
    if l.one {
        c.x(t);
    }
}

/// AND records of the merged op's helper wires, erased in reverse order.
type Recs = Vec<(QubitId, Lin, Lin)>;
fn m_and(c: &mut Builder, recs: &mut Recs, a: Lin, b: Lin) -> Lin {
    let q = lin_and(c, &a, &b);
    recs.push((q, a, b));
    Lin::of(&[q])
}
fn m_erase(c: &mut Builder, recs: &mut Recs, from: usize) {
    while recs.len() > from {
        let (q, a, b) = recs.pop().unwrap();
        lin_and_erase(c, q, &a, &b);
    }
}

/// ANF of the merged addend: bit b of (f - 1)(u - 15) mod 2^MW over the 5 bits of u, as monomial masks
/// (0 = the constant 1); and the AND construction order (m, a, b) of the nonlinear monomials (m = a | b).
fn merged_tables() -> &'static (Vec<Vec<usize>>, Vec<(usize, usize, usize)>) {
    static T: OnceLock<(Vec<Vec<usize>>, Vec<(usize, usize, usize)>)> = OnceLock::new();
    T.get_or_init(|| {
        let mw = merged_win();
        let g16: i128 = (1i128 << 32) + 976;
        let modw: i128 = 1i128 << mw;
        let vals: Vec<i128> = (0..32i128).map(|u| (g16 * (u - M_OFF)).rem_euclid(modw)).collect();
        let table: Vec<Vec<usize>> = (0..mw)
            .map(|b| {
                let mut a: Vec<u8> = vals.iter().map(|v| (v >> b & 1) as u8).collect();
                for i in 0..5 {
                    for x in 0..32 {
                        if x >> i & 1 == 1 {
                            a[x] ^= a[x ^ (1 << i)];
                        }
                    }
                }
                (0..32).filter(|&x| a[x] == 1).collect()
            })
            .collect();
        assert!(table[..4].iter().all(|r| r.is_empty()), "(f - 1) * n has 4 zero low bits");
        let mut need: Vec<usize> = table.iter().flatten().copied().filter(|m| m.count_ones() >= 2).collect();
        need.sort_by_key(|&m| (m.count_ones(), m));
        need.dedup();
        let mut avail: Vec<usize> = vec![1, 2, 4, 8, 16];
        let mut plan = Vec::new();
        for m in need {
            let mut pick = None;
            'o: for &a in &avail {
                for &b in &avail {
                    if a | b == m && a != m && b != m {
                        pick = Some((a, b));
                        break 'o;
                    }
                }
            }
            let (a, b) = pick.expect("monomial plan needs an intermediate");
            plan.push((m, a, b));
            avail.push(m);
            avail.sort();
        }
        (table, plan)
    })
}

/// u = x + ov + 15*sg, exactly, with four temporary ANDs.
/// Rewrite as (x + ov - sg) + 16*sg: a conditional four-bit increment/decrement.
/// The caller erases these helpers through the existing reverse-order MBU records.
fn m_u_build(c: &mut Builder, recs: &mut Recs, x: &[Lin; 4], ov: &Lin, sg: &Lin) -> [Lin; 5] {
    let mut carry = ov.x(sg);
    let mut u = Vec::with_capacity(5);
    for bit in x {
        u.push(bit.x(&carry));
        carry = m_and(c, recs, bit.x(sg), carry);
    }
    u.push(sg.x(&carry));
    u.try_into().unwrap()
}

/// Bits [0, MW) of (f - 1)(u - 15) mod 2^MW from the 5 bits of u with 10 ANDs (the ANF monomial route takes 19; 10
/// is the rank bound: the 16 distinct output bits span 10 dimensions beyond the affine functions of u). Written
/// over any XOR/AND algebra `T`, so the same code emits the wire forms and checks itself on truth tables.
/// With n = u - 15 in [-15, 16] and (f - 1) = 2^32 + 16 * 61:
///   * bits 4..14 = 61 n mod 2^10 = (64 u + (109 - 3u)) mod 2^10, and 109 - 3u = 3 v + 16 with v = NOT u = 31 - u,
///     in [16, 109]: bits 4..10 are the low 6 bits of 3v + 16 (ripple v + 2v, carries c2 = v0 v1 = 1 ^ u0 ^ u1 ^ u0u1
///     and three MAJ; the + 16 is free), and bits 10..14 are (u + !u4) mod 16 (bit 6 of 109 - 3u is [u <= 15]);
///   * bits 14..32 = s = [n < 0] = !u4 & !(u0 u1 u2 u3) (sign extension of 61 n);
///   * bits 32.. = n - s: (u + !s) mod 16, then 1 ^ u4 ^ u0u1u2u3, then s. The carries of u + !s are
///     !s & p = p ^ (!u4 & p) ^ s ^ !u4 for a prefix product p of u0..u2: XORs of ANDs already made.
fn addend10<T: Clone>(u: &[T; 5], one: &T, zero: &T, mw: usize, x: &dyn Fn(&T, &T) -> T, and: &mut dyn FnMut(T, T) -> T) -> Vec<T> {
    let p1 = and(u[0].clone(), u[1].clone());
    let p2 = and(p1.clone(), u[2].clone());
    let m15 = and(p2.clone(), u[3].clone());
    let nu4 = x(&u[4], one);
    let s = x(&nu4, &and(nu4.clone(), m15.clone()));
    let d1 = and(nu4.clone(), u[0].clone());
    let d2 = and(nu4.clone(), p1.clone());
    let d3 = and(nu4.clone(), p2.clone());
    let v: Vec<T> = u.iter().map(|l| x(l, one)).collect();
    let c2 = x(&x(&x(one, &u[0]), &u[1]), &p1);
    let c3 = x(&and(x(&v[2], &c2), x(&v[1], &c2)), &c2);
    let c4 = x(&and(x(&v[3], &c3), x(&v[2], &c3)), &c3);
    let c5 = x(&and(x(&v[4], &c4), x(&v[3], &c4)), &c4);
    // 3v + 16, bits 0..6
    let b4 = x(&x(&v[4], &v[3]), &c4);
    let low = [v[0].clone(), x(&v[1], &v[0]), x(&x(&v[2], &v[1]), &c2), x(&x(&v[3], &v[2]), &c3), x(&b4, one), x(&x(&v[4], &c5), &b4)];
    let sn = x(&s, &nu4); // !u4 & u0u1u2u3
    let e = [x(&s, one), x(&x(&u[0], &d1), &sn), x(&x(&p1, &d2), &sn), x(&x(&p2, &d3), &sn)];
    let dd = [nu4.clone(), d1, d2, d3];
    (0..mw)
        .map(|b| match b {
            0..=3 => zero.clone(),
            4..=9 => low[b - 4].clone(),
            10..=13 => x(&u[b - 10], &dd[b - 10]),
            14..=31 => s.clone(),
            32..=35 => x(&u[b - 32], &e[b - 32]),
            36 => x(&x(&u[4], one), &m15),
            _ => s.clone(),
        })
        .collect()
}

/// `LF_ADDEND=anf` keeps the ANF monomial route of [`m_addend`] (19 ANDs); default: [`addend10`].
fn lf_addend10() -> bool {
    static A: OnceLock<bool> = OnceLock::new();
    *A.get_or_init(|| {
        if std::env::var("LF_ADDEND").is_ok_and(|v| v == "anf") {
            return false;
        }
        // self-check on truth tables over the 32 values of u (bit i of a table = the value at u = i)
        let mw = merged_win();
        let ut: [u32; 5] = std::array::from_fn(|i| (0..32u32).filter(|v| v >> i & 1 == 1).map(|v| 1u32 << v).sum());
        let mut n_and = 0usize;
        let got = addend10(&ut, &u32::MAX, &0u32, mw, &|a, b| a ^ b, &mut |a, b| {
            n_and += 1;
            a & b
        });
        let g16: i128 = (1i128 << 32) + 976;
        for b in 0..mw {
            let want: u32 = (0..32i128).filter(|&v| (g16 * (v - M_OFF)).rem_euclid(1i128 << mw) >> b & 1 == 1).map(|v| 1u32 << v).sum();
            assert_eq!(got[b], want, "addend10 bit {b}");
        }
        assert_eq!(n_and, 10);
        true
    })
}

/// The nonlinear monomials of u (ANDs into `recs`) and the addend forms of bits [0, MW): bit 0 = ov, 1..3 = 0.
fn m_addend(c: &mut Builder, recs: &mut Recs, u: &[Lin; 5], ov: &Lin) -> Vec<Lin> {
    if lf_addend10() {
        let mut add = addend10(u, &Lin::k(true), &Lin::k(false), merged_win(), &|a: &Lin, b: &Lin| a.x(b), &mut |a: Lin, b: Lin| m_and(c, recs, a, b));
        add[0] = ov.clone();
        return add;
    }
    let (table, plan) = merged_tables();
    let mut mono: Vec<Option<Lin>> = vec![None; 32];
    for i in 0..5 {
        mono[1 << i] = Some(u[i].clone());
    }
    for &(m, a, b) in plan {
        let q = m_and(c, recs, mono[a].clone().unwrap(), mono[b].clone().unwrap());
        mono[m] = Some(q);
    }
    table
        .iter()
        .enumerate()
        .map(|(b, row)| {
            if b == 0 {
                return ov.clone();
            }
            row.iter().fold(Lin::k(false), |acc, &m| if m == 0 { acc.x(&Lin::k(true)) } else { acc.x(mono[m].as_ref().unwrap()) })
        })
        .collect()
}

/// Gidney carry out of bit i: AND(acc_i ^ c_i, add_i ^ c_i) ^ c_i (and its MBU erase).
fn m_carry(c: &mut Builder, acc: QubitId, add: &Lin, ci: QubitId) -> QubitId {
    let (a, b) = (Lin::of(&[acc, ci]), add.x(&Lin::of(&[ci])));
    let t = lin_and(c, &a, &b);
    c.cx(ci, t);
    t
}
fn m_carry_erase(c: &mut Builder, t: QubitId, acc: QubitId, add: &Lin, ci: QubitId) {
    let (a, b) = (Lin::of(&[acc, ci]), add.x(&Lin::of(&[ci])));
    c.cx(ci, t);
    lin_and_erase(c, t, &a, &b);
}

/// The merged fold ladder acc[0..MW) += ov + addend(u) (mod 2^MW). `hook` runs once the carries into bits 1..4 are
/// live (sum bits 0..3 = acc_j ^ c_j, acc_0 ^ ov) and returns the addend forms of bits [4, MW); the ANDs it
/// records are erased at the mirror point of the backward pass (before bits 3..0 are written).
fn m_fold(c: &mut Builder, acc: &[QubitId], ov: QubitId, recs: &mut Recs, plan: &[usize],
          hook: impl FnOnce(&mut Builder, &mut Recs, [QubitId; 4]) -> Vec<Lin>) {
    let mw = acc.len();
    assert_eq!(plan.iter().sum::<usize>(), mw - 4, "fold plan covers bits [4, MW)");
    let mut car: Vec<QubitId> = Vec::with_capacity(5);
    car.push(ov); // car[0] stands for the bit-0 addend (no carry-in)
    let c1 = and_new(c, acc[0], ov);
    car.push(c1);
    for i in 1..4 {
        let t = and_new(c, acc[i], car[i]);
        car.push(t);
    }
    let base = recs.len();
    let add = hook(c, recs, [car[1], car[2], car[3], car[4]]);
    // upper ladder [4, MW) in chunks: a non-final chunk keeps its carry-out (the next chunk's carry-in) and is
    // written back at once; kept carries are erased exactly at the end (MBU + [acc < add + cin] phase compare)
    let mut kept: Vec<(usize, usize, QubitId, QubitId)> = Vec::new();
    let (mut lo, mut cin) = (4usize, car[4]);
    for (j, &w) in plan.iter().enumerate() {
        let hi = lo + w;
        let last = j + 1 == plan.len();
        // lean final chunk: the carry into its top bit is used once, so it goes straight into that bit's wire (one
        // CCX, nothing to erase) and the chunk holds w - 2 carries ([`m_fold_plan`] gives it the extra bit)
        let direct = last && w >= 2 && m_fold_lean();
        let mut cc = vec![cin]; // cc[k] = carry into bit lo + k
        for i in lo..(if last { hi - 1 - direct as usize } else { hi }) {
            let t = m_carry(c, acc[i], &add[i], cc[i - lo]);
            cc.push(t);
        }
        if direct {
            let (i, ci) = (hi - 2, cc[w - 2]);
            let (a, b) = (Lin::of(&[acc[i], ci]), add[i].x(&Lin::of(&[ci])));
            let (ha, hb) = lin_pair_on(c, &a, &b);
            c.ccx(ha, hb, acc[hi - 1]);
            lin_pair_off(c, &a, &b);
            c.cx(ci, acc[hi - 1]);
        }
        if lf_merged_trace() && (last || plan.len() > 1) {
            eprintln!("LF_MERGED_FOLD chunk={j} [{lo},{hi}) active={} cap={}", c.active_qubits(), cells::cap());
        }
        assert!(c.active_qubits() as usize <= cells::cap() || std::env::var_os("LF_MERGED_NOCAPCHECK").is_some(),
            "merged fold over the walk cap: {} > {}", c.active_qubits(), cells::cap());
        for i in (lo..hi).rev() {
            lin_xor_into(c, &add[i], acc[i]);
            if direct && i == hi - 1 {
                continue; // its carry is already in the wire
            }
            c.cx(cc[i - lo], acc[i]);
            if i > lo {
                m_carry_erase(c, cc[i - lo], acc[i - 1], &add[i - 1], cc[i - lo - 1]);
            }
        }
        if !last {
            let out = cc[w];
            kept.push((lo, hi, cin, out));
            cin = out;
        }
        lo = hi;
    }
    for (lo, hi, cin, out) in kept.into_iter().rev() {
        let m = c.alloc_bit();
        c.hmr(out, m);
        c.release_clean(out);
        c.push_condition(m);
        lin_lt_phase(c, &acc[lo..hi], &add[lo..hi], cin);
        c.pop_condition();
        c.free_bit(m);
    }
    and_erase(c, car[4], acc[3], car[3]);
    m_erase(c, recs, base);
    for i in (1..4).rev() {
        c.cx(car[i], acc[i]);
        and_erase(c, car[i], acc[i - 1], car[i - 1]);
    }
    c.cx(ov, acc[0]);
}

/// CZ between two linear forms (a constant side degenerates to Z or nothing).
fn lin_cz(c: &mut Builder, a: &Lin, b: &Lin) {
    match (a.w.is_empty(), b.w.is_empty()) {
        (true, true) => {
            if a.one && b.one {
                // global phase -1: unobservable inside a classically conditioned block only if unconditional;
                // never produced by the callers (cin and acc forms are never constant)
                panic!("lin_cz of two constants");
            }
        }
        (true, false) | (false, true) => {
            let (k, l) = if a.w.is_empty() { (a, b) } else { (b, a) };
            if k.one {
                let h = l.w[0];
                lin_on(c, l, h);
                c.z_if(h, NO_BIT);
                lin_off(c, l, h);
            }
        }
        (false, false) => {
            let (ha, hb) = lin_pair_on(c, a, b);
            c.cz(ha, hb);
            lin_pair_off(c, a, b);
        }
    }
}

/// Phase (-1)^[a < add + cin] on the current condition (a: w wires, add: w forms, cin: a wire): the carry-out of
/// NOT a + add + cin, Gidney carries measurement-uncomputed, the top carry as three CZs; w - 1 ANDs.
fn lin_lt_phase(c: &mut Builder, a: &[QubitId], add: &[Lin], cin: QubitId) {
    let w = a.len();
    c.x_all(a);
    let mut d = vec![cin];
    for i in 0..w - 1 {
        let t = m_carry(c, a[i], &add[i], d[i]);
        d.push(t);
    }
    let (x, y, z) = (Lin::of(&[a[w - 1]]), add[w - 1].clone(), Lin::of(&[d[w - 1]]));
    lin_cz(c, &x, &y);
    lin_cz(c, &y, &z);
    lin_cz(c, &z, &x);
    for i in (1..w).rev() {
        m_carry_erase(c, d[i], a[i - 1], &add[i - 1], d[i - 1]);
    }
    c.x_all(a);
}

/// Chunk plan of the merged fold's upper ladder (bits [4, MW), n = MW - 4) for `budget` live wires above the fold's
/// fixed part: one chunk when n - 1 carries fit; else the fewest chunks with the final chunk as wide as it can be (a
/// non-final chunk j holds j kept carries + w_j; the final one K-1 kept + w_K - 1). Expected cost of the split:
/// sum over non-final chunks of (w_j - 1) / 2 Toffoli.
fn merged_plan(n: usize, budget: usize) -> Option<Vec<usize>> {
    if budget + 1 >= n {
        return Some(vec![n]);
    }
    for k in 2..=n {
        let wk = (budget + 2).checked_sub(k)?;
        if wk == 0 {
            return None;
        }
        let caps: Vec<usize> = (0..k - 1).map(|j| budget.saturating_sub(j)).collect();
        if caps.contains(&0) {
            return None;
        }
        let rest = n.checked_sub(wk)?;
        if caps.iter().sum::<usize>() < rest {
            continue;
        }
        let mut sizes = Vec::with_capacity(k);
        let mut left = rest;
        if rest < k - 1 {
            return None;
        }
        for &cap in &caps {
            // every non-final chunk at least 1 wide; fill from the bottom
            let take = cap.min(left - (k - 2 - sizes.len()));
            sizes.push(take);
            left -= take;
        }
        if left > 0 || sizes.contains(&0) {
            continue;
        }
        sizes.push(wk);
        return Some(sizes);
    }
    None
}

fn lf_merged_trace() -> bool {
    std::env::var("LF_MERGED_TRACE").is_ok_and(|v| v == "1")
}

/// Rotation of a 256-bit register by one place (free: swaps). down: out[i] = in[i + 1].
fn rot1(c: &mut Builder, p: &[QubitId], down: bool) {
    let n = p.len();
    if down {
        for i in 0..n - 1 {
            c.swap(p[i], p[i + 1]);
        }
    } else {
        for i in (0..n - 1).rev() {
            c.swap(p[i], p[i + 1]);
        }
    }
}

/// Merged fold of the forward op (register in the sg-complemented frame, holding A; `ov` the adder's overflow).
fn m_fold_fwd(c: &mut Builder, acc: &[QubitId], ov: QubitId, sg: QubitId, k1: QubitId, k2: QubitId) {
    let (lsg, lov) = (Lin::of(&[sg]), Lin::of(&[ov]));
    let plan = m_fold_plan(c, M_FIXED_FWD, acc.len());
    m_fold(c, acc, ov, &mut Vec::new(), &plan, |c, recs, car| {
        // low sum bits nu_j = acc_j ^ c_j; mu_j = nu_j ^ sg masked by [k > j]
        let nu = [Lin::of(&[acc[0], ov]), Lin::of(&[acc[1], car[0]]), Lin::of(&[acc[2], car[1]]), Lin::of(&[acc[3], car[2]])];
        let tt = m_and(c, recs, Lin::of(&[k1]), Lin::of(&[k2]));
        let gates = [Lin::of(&[k1, k2]).x(&tt), Lin::of(&[k2]), tt.clone()];
        let mut x = vec![nu[0].x(&Lin::k(true))];
        for j in 1..4 {
            let q = m_and(c, recs, gates[j - 1].clone(), nu[j].x(&lsg));
            x.push(q.x(&lsg).x(&Lin::k(true)));
        }
        let x: [Lin; 4] = x.try_into().unwrap();
        let u = m_u_build(c, recs, &x, &lov, &lsg);
        m_addend(c, recs, &u, &lov)
    });
}

/// Fold extra (live wires beyond the adder's overflow) of the merged ops: MW - 1 carries plus 18 (forward: k-gate,
/// gated mu bits, u, monomials) or 14 (reverse: u, monomials; its 5 mu copies are live before the add).
fn m_fold_need(rev: bool) -> usize {
    merged_win() - 1 + if rev { if lf_merged_rev2() { 3 + 4 + 14 } else { 14 } } else { 18 }
}

/// Exact-flag split (`LF_MERGED_EXACT`, default 1): the lowest split s such that the top ripple [s, N) (N - s - 1
/// carries + the split carry + the overflow) and the fold fit under the cap during the consumer, with the split
/// compare (and seed) above the fold window. None when infeasible.
fn merged_split(c: &Builder, proxy: usize, multiply: bool, rev: bool) -> Option<usize> {
    if std::env::var("LF_MERGED_EXACT").is_ok_and(|v| v == "0") {
        return None;
    }
    let room = cells::cap().checked_sub(c.active_qubits() as usize)?;
    let mw = merged_win();
    let lo = (N + 1 + m_fold_need(rev)).saturating_sub(room);
    let mut s = lo.max(mw + 30);
    while s < N - 2 && s < mw + cells::split_compare_width(proxy, multiply, s) + 1 {
        s += 1;
    }
    let min_top: usize = std::env::var("LF_MERGED_EXACT_MINTOP").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    (s + min_top <= N).then_some(s)
}

/// Forward merged op: `tgt <- (tgt + (-1)^sg src) 2^-(1 + e) (mod p)`, e = k1 + 2 k2 (the replay cell `add_halve`
/// followed by [`cmod_barrel`]). `proxy` keys the production chunked adder and the flag / split compares. With a
/// split (exact route) the fold runs inside the top ripple and the overflow is erased exactly from its frame;
/// otherwise the overflow is erased with the cell's flag compare.
fn merged_fwd(c: &mut Builder, sg: QubitId, src: &[QubitId], tgt: &[QubitId], k1: QubitId, k2: QubitId, proxy: usize, split: Option<usize>,
              mw: usize) {
    c.cx_all(sg, tgt);
    match split {
        Some(sp) => cells::add_consume_exact(c, src, tgt, proxy, false, sp, |c, ov| m_fold_fwd(c, &tgt[..mw], ov, sg, k1, k2)),
        None => {
            let ov = cells::chunked_add(c, src, tgt, proxy, false);
            m_fold_fwd(c, &tgt[..mw], ov, sg, k1, k2);
            let k = cells::flag_erase(c, ov, tgt, src, mw, proxy, false);
            c.release_clean(ov);
            if lf_merged_trace() {
                eprintln!("LF_MERGED_FLAG fwd proxy={proxy} k={k}");
            }
        }
    }
    c.cx_all(sg, tgt);
    rot1(c, tgt, true);
    rot4(c, k1, k2, tgt, false);
}

/// Reverse merged op (exact inverse map): `tgt <- 2^(1 + e) tgt - (-1)^sg src (mod p)` (the inverse
/// [`cmod_barrel`] followed by the replay cell `double_add` with the sign flipped). `exact`: try the exact route
/// ([`merged_split`], judged once the 5 mu copies are live); the mu copies are erased inside the fold consumer.
fn merged_rev(c: &mut Builder, sg: QubitId, src: &[QubitId], tgt: &[QubitId], k1: QubitId, k2: QubitId, proxy: usize, exact: bool,
              mw: usize) {
    if lf_merged_rev2() {
        return merged_rev2(c, sg, src, tgt, k1, k2, proxy, exact, mw);
    }
    rot4(c, k1, k2, tgt, true);
    rot1(c, tgt, false);
    // copies of the rotated-in low bits (mu), gated by [k > j]
    let mut gl_recs: Recs = Vec::new();
    let g0 = c.alloc_qubit();
    c.cx(tgt[0], g0);
    let tt = m_and(c, &mut gl_recs, Lin::of(&[k1]), Lin::of(&[k2]));
    let gates = [Lin::of(&[k1, k2]).x(&tt), Lin::of(&[k2]), tt.clone()];
    let mut gl = vec![Lin::of(&[g0])];
    for j in 1..4 {
        let q = m_and(c, &mut gl_recs, gates[j - 1].clone(), Lin::of(&[tgt[j]]));
        gl.push(q);
    }
    // the cell's complemented frame: reg ^ sg ^ 1
    c.x_all(tgt);
    c.cx_all(sg, tgt);
    let split = if exact { merged_split(c, proxy, true, true) } else { None };
    if lf_merged_trace() {
        eprintln!("LF_MERGED_SPLIT rev proxy={proxy} split={split:?} active={}", c.active_qubits());
    }
    // fold, then erase the mu copies (R = the rotated-in low bits, recovered from the folded register, S_low, ov)
    let core = |c: &mut Builder, ov: QubitId, mut gl_recs: Recs| {
        let (lsg, lov) = (Lin::of(&[sg]), Lin::of(&[ov]));
        let plan = m_fold_plan(c, M_FIXED_REV, mw);
        let mut recs: Recs = Vec::new();
        let x: [Lin; 4] = std::array::from_fn(|j| gl[j].x(&lsg).x(&Lin::k(true)));
        let u = m_u_build(c, &mut recs, &x, &lov, &lsg);
        let add = m_addend(c, &mut recs, &u, &lov);
        m_fold(c, &tgt[..mw], ov, &mut Vec::new(), &plan, |_, _, _| add.clone());
        m_erase(c, &mut recs, 0);
        // in the frame: R = ((frame ^ 1) + S_low + ov) ^ sg (mod 16)
        let mut rr: Recs = Vec::new();
        let s_: Vec<Lin> = (0..4).map(|j| Lin::of(&[src[j]])).collect();
        let rg: Vec<Lin> = (0..4).map(|j| Lin::of(&[tgt[j]]).x(&Lin::k(true))).collect();
        let mut sum = vec![rg[0].x(&s_[0]).x(&lov)];
        let mut cc = lov.clone();
        for j in 0..3 {
            let q = m_and(c, &mut rr, rg[j].x(&cc), s_[j].x(&cc));
            cc = q.x(&cc);
            sum.push(rg[j + 1].x(&s_[j + 1]).x(&cc));
        }
        let r: Vec<Lin> = sum.iter().map(|l| l.x(&lsg)).collect();
        lin_xor_into(c, &r[0], g0);
        c.release_clean(g0);
        // gated copies AND(gate_j, R_j), then tt (recorded order: tt, q1, q2, q3)
        let qs: Vec<(QubitId, Lin, Lin)> = gl_recs.drain(1..).collect();
        for (j, (q, gate, _)) in qs.into_iter().enumerate().rev() {
            lin_and_erase(c, q, &gate, &r[j + 1]);
        }
        m_erase(c, &mut gl_recs, 0);
        m_erase(c, &mut rr, 0);
    };
    match split {
        Some(sp) => cells::add_consume_exact(c, src, tgt, proxy, true, sp, |c, ov| core(c, ov, gl_recs)),
        None => {
            let ov = cells::chunked_add(c, src, tgt, proxy, true);
            core(c, ov, gl_recs);
            let k = cells::flag_erase(c, ov, tgt, src, mw, proxy, true);
            c.release_clean(ov);
            if lf_merged_trace() {
                eprintln!("LF_MERGED_FLAG rev proxy={proxy} k={k}");
            }
        }
    }
    c.cx_all(sg, tgt);
    c.x_all(tgt);
}

/// `LF_MERGED_REV2` (default: on with LF_MERGED_LATE): the reverse merged op without mu copies. After the chunked
/// add the register's low bits are L = (F + S_low) mod 16, F the cell frame of W = rotl_k(Y); W_low = (L - S_low) ^ sg ^ 1
/// costs 3 borrow ANDs (the copies' 3-AND recovery is dropped), and every helper is built and erased inside the fold
/// while L is unwritten: nothing extra is live across the chunked add (fewer chunk compares), +2 wires in the fold.
fn lf_merged_rev2() -> bool {
    std::env::var("LF_MERGED_REV2").map_or(lf_merged_late(), |v| v == "1")
}

/// [`merged_rev`] with [`lf_merged_rev2`].
fn merged_rev2(c: &mut Builder, sg: QubitId, src: &[QubitId], tgt: &[QubitId], k1: QubitId, k2: QubitId, proxy: usize, exact: bool,
               mw: usize) {
    rot4(c, k1, k2, tgt, true);
    rot1(c, tgt, false);
    // the cell's complemented frame: reg ^ sg ^ 1
    c.x_all(tgt);
    c.cx_all(sg, tgt);
    let split = if exact { merged_split(c, proxy, true, true) } else { None };
    if lf_merged_trace() {
        eprintln!("LF_MERGED_SPLIT rev2 proxy={proxy} split={split:?} active={}", c.active_qubits());
    }
    let core = |c: &mut Builder, ov: QubitId| {
        let (lsg, lov, one) = (Lin::of(&[sg]), Lin::of(&[ov]), Lin::k(true));
        let plan = m_fold_plan(c, M_FIXED_REV2, mw);
        m_fold(c, &tgt[..mw], ov, &mut Vec::new(), &plan, |c, recs, _car| {
            // W_low = (L - S_low) ^ sg ^ 1, borrows beta_{j+1} = MAJ(NOT L_j, S_j, beta_j)
            let l: Vec<Lin> = (0..4).map(|j| Lin::of(&[tgt[j]])).collect();
            let sl: Vec<Lin> = (0..4).map(|j| Lin::of(&[src[j]])).collect();
            let mut beta = vec![Lin::k(false), m_and(c, recs, l[0].x(&one), sl[0].clone())];
            for j in 1..3 {
                let b = beta[j].clone();
                let q = m_and(c, recs, l[j].x(&one).x(&b), sl[j].x(&b));
                beta.push(q.x(&b));
            }
            let w: Vec<Lin> = (0..4).map(|j| l[j].x(&sl[j]).x(&beta[j]).x(&lsg).x(&one)).collect();
            let tt = m_and(c, recs, Lin::of(&[k1]), Lin::of(&[k2]));
            let gates = [Lin::of(&[k1, k2]).x(&tt), Lin::of(&[k2]), tt.clone()];
            let mut gl = vec![w[0].clone()];
            for j in 1..4 {
                gl.push(m_and(c, recs, gates[j - 1].clone(), w[j].clone()));
            }
            let x: [Lin; 4] = std::array::from_fn(|j| gl[j].x(&lsg).x(&one));
            let u = m_u_build(c, recs, &x, &lov, &lsg);
            m_addend(c, recs, &u, &lov)
        });
    };
    match split {
        Some(sp) => cells::add_consume_exact(c, src, tgt, proxy, true, sp, core),
        None => {
            let ov = cells::chunked_add(c, src, tgt, proxy, true);
            core(c, ov);
            let k = cells::flag_erase(c, ov, tgt, src, mw, proxy, true);
            c.release_clean(ov);
            if lf_merged_trace() {
                eprintln!("LF_MERGED_FLAG rev2 proxy={proxy} k={k}");
            }
        }
    }
    c.cx_all(sg, tgt);
    c.x_all(tgt);
}

/// Live wires of the merged fold beyond the op's starting count, excluding the upper ladder's carries: the fold's
/// own carries into bits 1..4 and its helper ANDs (forward: k-gate, gated mu bits, u, monomials = 18), measured
/// from the fold's start (overflow live); the reverse's u + monomials (14) with its 5 mu copies counted at the op.
const M_FIXED_FWD: usize = 4 + 18;
const M_FIXED_REV: usize = 4 + 14;
/// [`merged_rev2`]: carries into bits 1..4, 3 borrows, k-gate + 3 gated mu bits, u, monomials.
const M_FIXED_REV2: usize = 4 + 3 + 4 + 14;

/// Wires counted in M_FIXED_* that the fold no longer holds. [`m_u_build`] (8 ANDs to 4) and [`addend10`] freed
/// 4 + 9 wires; M_FIXED_* and [`m_fold_need`] no longer count any of them, so the fit and split rules
/// ([`merged_fits`], [`merged_split`], [`m_fold_need`]) and the fold's own chunk plan all see the same live
/// count and nothing is left over. The cap assert inside [`m_fold`] guards the count.
fn m_fold_slack() -> usize {
    0
}

/// `LF_FOLD_LEAN=0` keeps the merged fold's final chunk with a carry wire for its top bit.
fn m_fold_lean() -> bool {
    !std::env::var("LF_FOLD_LEAN").is_ok_and(|v| v == "0")
}

/// The fold's chunk plan at the current live count (`fixed`: the fold's non-ladder wires still to be allocated).
fn m_fold_plan(c: &Builder, fixed: usize, mw: usize) -> Vec<usize> {
    let budget = cells::cap().saturating_sub(c.active_qubits() as usize + fixed - m_fold_slack());
    // lean final chunk ([`m_fold`]): it holds one carry fewer, so plan one bit less and give that bit to the final
    // chunk. The fit rule ([`merged_fits`]) keeps the plain plan, so the same ticks run the merged op.
    let lean = if m_fold_lean() && mw >= 7 { merged_plan(mw - 5, budget) } else { None };
    let plan = match lean {
        Some(mut p) => {
            *p.last_mut().unwrap() += 1;
            p
        }
        None => merged_plan(mw - 4, budget).expect("merged fold plan (checked by merged_fits)"),
    };
    if lf_merged_trace() && plan.len() > 1 {
        eprintln!("LF_MERGED_PLAN budget={budget} plan={plan:?} x2={}", plan_x2(&plan));
    }
    plan
}

/// Twice the expected extra Toffoli of a chunk plan (the kept carries' exact compares fire on half the shots).
fn plan_x2(plan: &[usize]) -> usize {
    plan[..plan.len() - 1].iter().map(|w| w - 1).sum()
}

/// `LF_MERGED_LATE=1`: also run the merged op where its fold must be split (late ticks) and on tie-safe ticks (with the
/// tie predicate, as the cells), when the split's extra2 is at most LF_MERGED_LATE_MAXX2 (default 60).
fn lf_merged_late() -> bool {
    std::env::var("LF_MERGED_LATE").is_ok_and(|v| v == "1")
}

/// Merged op on tick t: LF_MERGED=1, before the tie-safe ticks (LF_MERGED_MAX, default LF_TIE_FROM) and when the
/// flag route's fold phase (ov + [`m_fold_need`], + the 5 mu copies on the reverse) fits under the walk cap at
/// `active` (live count at the op).
fn merged_fits(active: usize, t: usize, rev: bool) -> Option<usize> {
    static MAX: OnceLock<usize> = OnceLock::new();
    let max = *MAX.get_or_init(|| {
        std::env::var("LF_MERGED_MAX").ok().and_then(|v| v.parse().ok())
            .unwrap_or_else(|| std::env::var("LF_TIE_FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
    });
    if lf_merged_trace() {
        eprintln!("LF_MERGED_ROOM t={t} rev={rev} active={active} room={}", cells::cap().saturating_sub(active));
    }
    let late = lf_merged_late();
    if !lf_merged() || (t >= max && !late) {
        return None;
    }
    // forward: overflow + fold fixed part; reverse: 5 mu copies + overflow + fold fixed part; then the ladder budget
    let fixed = 1 + if rev { if lf_merged_rev2() { M_FIXED_REV2 } else { 5 + M_FIXED_REV } } else { M_FIXED_FWD };
    let budget = cells::cap().checked_sub(active + fixed)?;
    let mw = merged_win();
    // the standard op: a single-chunk fold before the tie-safe ticks
    if t < max && merged_plan(mw - 4, budget).is_some_and(|p| p.len() == 1) {
        return Some(mw);
    }
    if !late {
        return None;
    }
    // late op: the fold window LF_MERGED_LATE_WIN (default MW), split to the room; taken when the split's expected
    // extra (x2 / 2) is at most LF_MERGED_LATE_GAIN_FWD / _REV (defaults 1000: always) plus the production barrel's
    // own split extra at this room (its fold ladder [4, 4 + fs) beside 8 helpers, lpa_capped)
    let lw: usize = std::env::var("LF_MERGED_LATE_WIN").ok().and_then(|v| v.parse().ok()).unwrap_or(mw).min(mw);
    let plan = merged_plan(lw - 4, budget)?;
    let gain: usize = std::env::var(if rev { "LF_MERGED_LATE_GAIN_REV" } else { "LF_MERGED_LATE_GAIN_FWD" })
        .ok().and_then(|v| v.parse().ok()).unwrap_or(1000);
    let room = cells::cap().saturating_sub(active);
    let fs = go_fs("GO_FG_P");
    let bar_split = if split_tight() {
        (fs + 8).saturating_sub(room) / 2
    } else if fs + 8 > room {
        room.saturating_sub(8 + 4) / 2
    } else {
        0
    };
    let ok = plan_x2(&plan) / 2 <= gain + bar_split;
    if lf_merged_trace() {
        eprintln!("LF_MERGED_FIT t={t} rev={rev} active={active} win={lw} plan={plan:?} x2={} bar_split={bar_split} cap={} ok={ok}",
            plan_x2(&plan), cells::cap());
    }
    ok.then_some(lw)
}

/// Controlled arithmetic shift right by one of a register whose low wire is 0 when `ctrl`.
fn crot_down_fix(c: &mut Builder, ctrl: QubitId, t: &[QubitId]) {
    let w = t.len();
    for i in 0..w - 1 {
        fredkin(c, ctrl, t[i], t[i + 1]);
    }
    c.ccx(ctrl, t[w - 2], t[w - 1]);
}
fn crot_up_fix(c: &mut Builder, ctrl: QubitId, t: &[QubitId]) {
    let w = t.len();
    c.ccx(ctrl, t[w - 2], t[w - 1]);
    for i in (0..w - 1).rev() {
        fredkin(c, ctrl, t[i], t[i + 1]);
    }
}

/// Controlled arithmetic shift right by two of a register whose two low wires are 0 when `ctrl`.
fn crot2_down_fix(c: &mut Builder, ctrl: QubitId, t: &[QubitId]) {
    let w = t.len();
    for i in 0..w - 2 {
        fredkin(c, ctrl, t[i], t[i + 2]);
    }
    c.ccx(ctrl, t[w - 3], t[w - 2]);
    c.ccx(ctrl, t[w - 3], t[w - 1]);
}
fn crot2_up_fix(c: &mut Builder, ctrl: QubitId, t: &[QubitId]) {
    let w = t.len();
    c.ccx(ctrl, t[w - 3], t[w - 1]);
    c.ccx(ctrl, t[w - 3], t[w - 2]);
    for i in (0..w - 2).rev() {
        fredkin(c, ctrl, t[i], t[i + 2]);
    }
}

/// Controlled modular quartering: `p <- ctrl ? p/4 : p (mod p)`. With p == 3 (mod 4), m = p mod 4 makes
/// p + m*P == 0 (mod 4); P = 2^256 - f, so subtract m*f in the fold window, rotate by two and put m on top.
fn cmod_quarter(c: &mut Builder, ctrl: QubitId, p: &[QubitId]) {
    let fs = go_fs("GO_FG_P");
    let m0 = and_new(c, ctrl, p[0]);
    let m1 = and_new(c, ctrl, p[1]);
    csub_const_trunc(c, &p[..fs], f(), m0);
    csub_const_trunc(c, &p[1..1 + fs], f(), m1);
    for i in 0..N - 2 {
        fredkin(c, ctrl, p[i], p[i + 2]);
    }
    c.cx(m0, p[N - 2]);
    c.cx(m1, p[N - 1]);
    c.ccx(ctrl, p[N - 1], m1);
    c.ccx(ctrl, p[N - 2], m0);
    c.release_clean(m1);
    c.release_clean(m0);
}
/// Inverse of [`cmod_quarter`]: `p <- ctrl ? 4p : p (mod p)`.
fn cmod_quadruple(c: &mut Builder, ctrl: QubitId, p: &[QubitId]) {
    let fs = go_fs("GO_FG_P");
    let (m0, m1) = (c.alloc_qubit(), c.alloc_qubit());
    c.ccx(ctrl, p[N - 2], m0);
    c.ccx(ctrl, p[N - 1], m1);
    c.cx(m1, p[N - 1]);
    c.cx(m0, p[N - 2]);
    for i in (0..N - 2).rev() {
        fredkin(c, ctrl, p[i], p[i + 2]);
    }
    cadd_const_trunc(c, &p[1..1 + fs], f(), m1, false);
    cadd_const_trunc(c, &p[..fs], f(), m0, false);
    and_erase(c, m1, ctrl, p[1]);
    and_erase(c, m0, ctrl, p[0]);
}

/// Controlled modular halving of a 256-bit payload: `p <- ctrl ? p/2 : p (mod p)`.
fn cmod_halve(c: &mut Builder, ctrl: QubitId, p: &[QubitId]) {
    let par = and_new(c, ctrl, p[0]);
    csub_const_trunc(c, &p[..go_fs("GO_FG_P")], f(), par);
    for i in 0..N - 1 {
        fredkin(c, ctrl, p[i], p[i + 1]);
    }
    c.cx(par, p[N - 1]);
    c.ccx(ctrl, p[N - 1], par);
    c.release_clean(par);
}
/// Inverse of [`cmod_halve`]: `p <- ctrl ? 2p : p (mod p)`.
fn cmod_double(c: &mut Builder, ctrl: QubitId, p: &[QubitId]) {
    let par = c.alloc_qubit();
    c.ccx(ctrl, p[N - 1], par);
    c.cx(par, p[N - 1]);
    for i in (0..N - 1).rev() {
        fredkin(c, ctrl, p[i], p[i + 1]);
    }
    cadd_const_trunc(c, &p[..go_fs("GO_FG_P")], f(), par, false);
    and_erase(c, par, ctrl, p[0]);
}

pub struct Walk {
    pub r: [Vec<QubitId>; 2],
    tape: Vec<Vec<QubitId>>,
}

fn seed(c: &mut Builder, d: &[QubitId]) -> [Vec<QubitId>; 2] {
    let r = seed_full(c, d);
    lr_walk_drop(c, r)
}
/// LF_LOWREL: the seeded rails (both odd) without their bit-0 wires.
fn lr_walk_drop(c: &mut Builder, r: [Vec<QubitId>; 2]) -> [Vec<QubitId>; 2] {
    let mut r = r;
    if lowrel() {
        lr_drop(c, &mut r[0]);
        lr_drop(c, &mut r[1]);
    }
    r
}
/// LF_LOWREL: the walked-back rails with their bit-0 wires, for the unseed.
fn lr_walk_restore(c: &mut Builder, r: [Vec<QubitId>; 2]) -> [Vec<QubitId>; 2] {
    let mut r = r;
    if lowrel() {
        lr_restore(c, &mut r[1]);
        lr_restore(c, &mut r[0]);
    }
    r
}
fn seed_full(c: &mut Builder, d: &[QubitId]) -> [Vec<QubitId>; 2] {
    if seed_half() {
        return seed_half_rails(c, d);
    }
    let w0 = envelope()[0].max(N + 5);
    // R0 = d + p * [d even], on d's own wires (+ extension); [d even] ends as R0[N] (exact unless d + p < 2^256).
    let mut r0 = d.to_vec();
    r0.extend(c.alloc_qubits(w0 - N));
    let ev = c.alloc_qubit();
    c.cx(r0[0], ev);
    c.x(ev);
    c.cx(ev, r0[N]); // + 2^256
    csub_const_trunc(c, &r0[..go_fs("GO_FG_P")], f(), ev); // - f
    c.cx(r0[N], ev);
    c.free(ev);
    // R1 = 3 R0 + 2p (odd, coprime to R0; payload lambda*R1 == 3y: never zero, never +-P0 early on)
    let r1 = c.alloc_qubits(w0);
    c.cx_pairs(&r0, &r1);
    gidney_add(c, &r0[..w0 - 1], &r1[1..], None); // + 2 R0
    add_const(c, &r1[N + 1..], alloy_primitives::U256::from(1u8)); // + 2^257
    let one = c.alloc_qubit();
    c.x(one);
    csub_const_trunc(c, &r1[1..1 + go_fs("GO_FG_P")], f(), one); // - 2f
    c.x(one);
    c.free(one);
    [r0, r1]
}

fn unseed(c: &mut Builder, r: [Vec<QubitId>; 2], d: &[QubitId]) {
    let r = lr_walk_restore(c, r);
    if seed_half() {
        let r0 = unseed_half_rails(c, r);
        return restore_onto(c, r0, d);
    }
    let [mut r0, mut r1] = r;
    let w0 = envelope()[0].max(N + 5);
    resize(c, &mut r0, w0);
    resize(c, &mut r1, w0);
    let one = c.alloc_qubit();
    c.x(one);
    cadd_const_trunc(c, &r1[1..1 + go_fs("GO_FG_P")], f(), one, false);
    c.x(one);
    c.free(one);
    sub_const(c, &r1[N + 1..], alloy_primitives::U256::from(1u8));
    c.x_all(&r1[1..]);
    gidney_add(c, &r0[..w0 - 1], &r1[1..], None); // R1 - 2 R0 == NOT(NOT R1 + 2 R0)
    c.x_all(&r1[1..]);
    c.cx_pairs(&r0, &r1);
    c.free_vec(&r1);
    let ev = c.alloc_qubit();
    c.cx(r0[N], ev);
    cadd_const_trunc(c, &r0[..go_fs("GO_FG_P")], f(), ev, false);
    c.cx(ev, r0[N]);
    c.x(ev);
    c.cx(r0[0], ev);
    c.free(ev);
    restore_onto(c, r0, d);
}

/// Move d's bits (the low N wires of `cur`) back onto d's own wires (SWAPs are Clifford); free the extension.
fn restore_onto(c: &mut Builder, cur: Vec<QubitId>, d: &[QubitId]) {
    let mut cur = cur;
    for i in 0..N {
        let want = d[i];
        if cur[i] == want {
            continue;
        }
        if let Some(j) = cur.iter().position(|&q| q == want) {
            c.swap(cur[i], cur[j]);
            cur.swap(i, j);
        } else {
            c.reacquire(want);
            c.swap(cur[i], want);
            c.free(cur[i]);
            cur[i] = want;
        }
    }
    c.free_vec(&cur[N..]);
}

/// Seed e: R0 = d (d odd) or d - p (d even, negative), on d's wires + extension; R1 = (R0 + s p)/2 with s = +1 iff
/// R0 == 3 (mod 4), so both rails are odd. Constant folds only (no 3 R0 add): R0 - p + [R0 == 3 mod 4] 2p, halved.
fn seed_half_rails(c: &mut Builder, d: &[QubitId]) -> [Vec<QubitId>; 2] {
    let w0 = envelope()[0].max(N + 4);
    let fs = go_fs("GO_FG_P");
    let mut r0 = d.to_vec();
    r0.extend(c.alloc_qubits(w0 - N));
    let ev = c.alloc_qubit();
    c.cx(r0[0], ev);
    c.x(ev); // [d even]
    cadd_const_trunc(c, &r0[..fs], f(), ev, false); // + f
    for i in N..w0 {
        c.cx(ev, r0[i]); // - 2^256: d + f - 2^256 < 0, all high bits set
    }
    c.cx(r0[w0 - 1], ev); // ev == sign
    c.free(ev);
    let r1 = seed_r1(c, &r0);
    [r0, r1]
}

/// R1 = (R0 + s p)/2, s = +1 iff R0 == 3 (mod 4), from R0 at width w0.
fn seed_r1(c: &mut Builder, r0: &[QubitId]) -> Vec<QubitId> {
    let w0 = r0.len();
    let fs = go_fs("GO_FG_P");
    let one_u = alloy_primitives::U256::from(1u8);
    let mut r1 = c.alloc_qubits(w0);
    c.cx_pairs(&r0, &r1);
    if lf_seams() {
        // R0 - p + [R0 == 3 mod 4] 2p = R0 + (sg ? +p : -p): low window +f / -f selected by sg (one ladder)
        let sg = c.alloc_qubit();
        c.cx(r0[1], sg);
        let m = (alloy_primitives::U256::from(1u8) << (fs + 1)) - alloy_primitives::U256::from(1u8);
        add_sel_const(c, &r1[..fs + 1], f() & m, (alloy_primitives::U256::ZERO.wrapping_sub(f())) & m, sg);
        sub_const(c, &r1[N..], one_u);
        cadd_const_trunc(c, &r1[N + 1..], one_u, sg, false);
        c.cx(r0[1], sg);
        c.free(sg);
    } else {
    let one = c.alloc_qubit();
    c.x(one);
    cadd_const_trunc(c, &r1[..fs], f(), one, false); // - p = - 2^256 + f
    c.x(one);
    c.free(one);
    sub_const(c, &r1[N..], one_u);
    let sg = c.alloc_qubit();
    c.cx(r0[1], sg); // [R0 == 3 mod 4]: + 2p
    csub_const_trunc(c, &r1[1..1 + fs], f(), sg);
    cadd_const_trunc(c, &r1[N + 1..], one_u, sg, false);
    c.cx(r0[1], sg);
    c.free(sg);
    }
    let low = r1.remove(0);
    c.free(low);
    resize(c, &mut r1, w0);
    r1
}

/// `LF_SEAMS=1`: seam fusions around the walks (R1's two seed folds as one selected fold; coordinate ops fused
/// into the divide's seed / unseed and the multiply's unseed).
fn lf_seams() -> bool {
    std::env::var("LF_SEAMS").is_ok_and(|v| v == "1")
}

/// `acc += sel ? k1 : k0 (mod 2^len)`: one Gidney ladder whose addend bit i is the parity k0_i ^ sel (k0_i ^ k1_i)
/// (a constant-1 wire for the fixed bits).
fn add_sel_const(c: &mut Builder, acc: &[QubitId], k0: alloy_primitives::U256, k1: alloy_primitives::U256, sel: QubitId) {
    let one = c.alloc_qubit();
    c.x(one);
    let add: Vec<Vec<QubitId>> = (0..acc.len())
        .map(|i| {
            let mut v = Vec::new();
            if k0.bit(i) { v.push(one); }
            if k0.bit(i) != k1.bit(i) { v.push(sel); }
            v
        })
        .collect();
    ladder_parity_add(c, acc, &add, None);
    c.x(one);
    c.free(one);
}

/// Exact inverse of [`seed_half_rails`]; returns R0's wires holding d (+ zero extension).
fn unseed_half_rails(c: &mut Builder, r: [Vec<QubitId>; 2]) -> Vec<QubitId> {
    let r0 = unseed_r1(c, r);
    let w0 = r0.len();
    let fs = go_fs("GO_FG_P");
    let ev = c.alloc_qubit();
    c.cx(r0[w0 - 1], ev);
    for i in N..w0 {
        c.cx(ev, r0[i]);
    }
    csub_const_trunc(c, &r0[..fs], f(), ev);
    c.x(ev);
    c.cx(r0[0], ev);
    c.free(ev);
    r0
}

/// Inverse of [`seed_r1`]: clears R1, returns R0 at width w0.
fn unseed_r1(c: &mut Builder, r: [Vec<QubitId>; 2]) -> Vec<QubitId> {
    let [mut r0, mut r1] = r;
    let w0 = envelope()[0].max(N + 4);
    let fs = go_fs("GO_FG_P");
    let one_u = alloy_primitives::U256::from(1u8);
    resize(c, &mut r0, w0);
    resize(c, &mut r1, w0 - 1);
    r1.insert(0, c.alloc_qubit());
    if lf_seams() {
        let sg = c.alloc_qubit();
        c.cx(r0[1], sg);
        csub_const_trunc(c, &r1[N + 1..], one_u, sg);
        add_const(c, &r1[N..], one_u);
        let m = (alloy_primitives::U256::from(1u8) << (fs + 1)) - alloy_primitives::U256::from(1u8);
        add_sel_const(c, &r1[..fs + 1], (alloy_primitives::U256::ZERO.wrapping_sub(f())) & m, f() & m, sg);
        c.cx(r0[1], sg);
        c.free(sg);
    } else {
    let sg = c.alloc_qubit();
    c.cx(r0[1], sg);
    csub_const_trunc(c, &r1[N + 1..], one_u, sg);
    cadd_const_trunc(c, &r1[1..1 + fs], f(), sg, false);
    c.cx(r0[1], sg);
    c.free(sg);
    add_const(c, &r1[N..], one_u);
    let one = c.alloc_qubit();
    c.x(one);
    csub_const_trunc(c, &r1[..fs], f(), one);
    c.x(one);
    c.free(one);
    }
    c.cx_pairs(&r0, &r1);
    c.free_vec(&r1);
    r0
}

/// Fold window of the seam ops: the wider of the seed's and the coordinate shell's (no new truncation site).
fn seam_fs() -> usize {
    go_fs("GO_FG_P").max(go_fs("GO_FG_M"))
}

/// `mask` of the low `n` bits.
fn low_mask(n: usize) -> alloy_primitives::U256 {
    (alloy_primitives::U256::from(1u8) << n) - alloy_primitives::U256::from(1u8)
}

/// Front seam (`LF_SEAMS`): R0 of seed e straight from x2 and the classical ox, without forming d = x2 - ox mod p.
/// D = x2 - ox lands as (x mod 2^256, ov = [D < 0]); R0 = D - p (D >= 0 even), D + p (D < 0 even), D (odd) is
/// exactly the seed's d or d - p. One selected +-f fold replaces coord_sub's +f fold and the seed's; ov (the choice
/// of representative) is erased as coord_sub erases its borrow, by a top-window phase compare.
fn seed_r0_seam(c: &mut Builder, x: &[QubitId], ox: &[crate::circuit::BitId]) -> Vec<QubitId> {
    let w0 = envelope()[0].max(N + 4);
    let fs = seam_fs();
    c.x_all(x);
    let ov = c.alloc_qubit();
    super::modular::r5_ripple_add_cbits(c, ox, x, ov); // ~x + ox: carry = [ox > x]
    c.x_all(x); // x = D mod 2^256
    let e = c.alloc_qubit();
    c.cx(x[0], e);
    c.x(e); // [D even]
    c.x(ov);
    let g = and_new(c, e, ov); // D >= 0 even: - p
    c.x(ov);
    let mut r0 = x.to_vec();
    let ext = c.alloc_qubits(w0 - N);
    c.cx(ov, ext[0]);
    c.cx(e, ext[0]); // sign(R0) = ov ^ [D even]
    for &q in &ext[1..] {
        c.cx(ext[0], q);
    }
    r0.extend(ext.iter().copied());
    // low window += f g - f (e ^ g): addend bit i = (f_i ^ nf_i) g ^ nf_i e
    let nf = alloy_primitives::U256::ZERO.wrapping_sub(f()) & low_mask(fs);
    let add: Vec<Vec<QubitId>> = (0..fs)
        .map(|i| {
            let mut v = Vec::new();
            if f().bit(i) != nf.bit(i) { v.push(g); }
            if nf.bit(i) { v.push(e); }
            v
        })
        .collect();
    ladder_parity_add(c, &r0[..fs], &add, None);
    c.x(ov);
    and_erase(c, g, e, ov);
    c.x(ov);
    c.cx(ext[0], e);
    c.cx(ov, e); // [D even] = sign ^ ov
    c.free(e);
    // ov = [x2 < ox] = carry out of R0_low + ox (+ f when R0 >= 0): [~R0_top < ox_top] on the top window
    let k = super::modular::erase_compare();
    c.x_all(&r0[N - k..N]);
    let tv = c.alloc_qubits(k);
    for i in 0..k {
        c.x_if_bit(tv[i], ox[N - k + i]);
    }
    super::compare::erase_with_compare(c, ov, &r0[N - k..N], &tv, None);
    for i in 0..k {
        c.x_if_bit(tv[i], ox[N - k + i]);
    }
    c.free_vec(&tv);
    c.x_all(&r0[N - k..N]);
    c.free(ov);
    r0
}

/// Back seam (`LF_SEAMS`): from R (odd, |R| < p, two's complement on `r` = low N wires + sign copies) to
/// x = (R + C) mod p on the low N wires (returned; the sign wires are freed), without forming d = R + p [R < 0].
/// The register gets `add` (= C, or C + 1 over a complemented R for the reverse subtraction); `cb` = C. With
/// L = (R_low + C) mod 2^256 and ov its carry, x = L + (ov - sign) f exactly; then sign = 1 ^ x0 ^ C0 ^ ov and
/// ov = [x < C] (erased by a top-window phase compare, as the coordinate shell erases its overflow).
fn seam_add_reduce(c: &mut Builder, r: Vec<QubitId>, add: &[crate::circuit::BitId], cb: &[crate::circuit::BitId]) -> Vec<QubitId> {
    let w = r.len();
    let fs = seam_fs();
    let sgn = r[w - 1];
    for &q in &r[N..w - 1] {
        c.cx(sgn, q);
        c.free(q);
    }
    let low = r[..N].to_vec();
    let ov = c.alloc_qubit();
    super::modular::r5_ripple_add_cbits(c, add, &low, ov);
    c.x(sgn);
    let plus = and_new(c, ov, sgn); // ov & !sign: + f
    c.x(sgn);
    // + f plus - f minus with minus = ov ^ sign ^ plus: addend bit i = (f_i ^ nf_i) plus ^ nf_i (ov ^ sign)
    let nf = alloy_primitives::U256::ZERO.wrapping_sub(f()) & low_mask(fs);
    let lists: Vec<Vec<QubitId>> = (0..fs)
        .map(|i| {
            let mut v = Vec::new();
            if f().bit(i) != nf.bit(i) { v.push(plus); }
            if nf.bit(i) { v.push(ov); v.push(sgn); }
            v
        })
        .collect();
    ladder_parity_add(c, &low[..fs], &lists, None);
    c.x(sgn);
    and_erase(c, plus, ov, sgn);
    c.x(sgn);
    c.cx(low[0], sgn);
    c.cx(ov, sgn);
    c.x(sgn);
    c.x_if_bit(sgn, cb[0]);
    c.free(sgn);
    let k = super::modular::erase_compare();
    let tv = c.alloc_qubits(k);
    for i in 0..k {
        c.x_if_bit(tv[i], cb[N - k + i]);
    }
    super::compare::erase_with_compare(c, ov, &low[N - k..], &tv, None);
    for i in 0..k {
        c.x_if_bit(tv[i], cb[N - k + i]);
    }
    c.free_vec(&tv);
    c.free(ov);
    low
}

/// Tie-safe payload cell: the head's seeded compares need, on exact ties, pred = sign ^ [P_T == -P_S];
/// post-park P = lambda * (+-1, +-1), so the negation flag is the xor of the rails' sign bits. Only ticks in
/// tie-safe mode (see [`tie_from`]) get the predicate wire.
/// `LF_TIE_SEED=1` (pingpong `tie_borrow`): tie mode keeps the routes bypassed but the compares use their own seeded
/// predictors, so the predictor wire is never read: [`tie_pred`] marks tie mode with the cell's sign wire instead of
/// allocating one (one more wire of room for the late cells).
fn tie_seed() -> bool {
    static T: OnceLock<bool> = OnceLock::new();
    *T.get_or_init(|| std::env::var("LF_TIE_SEED").is_ok_and(|v| v == "1"))
}
fn tie_pred(c: &mut Builder, t: usize, s: QubitId, tsign: QubitId, ssign: QubitId) -> Option<QubitId> {
    if t < tie_from() {
        return None;
    }
    if tie_seed() {
        return Some(s);
    }
    let q = c.alloc_qubit();
    c.cx(s, q);
    c.cx(tsign, q);
    c.cx(ssign, q);
    Some(q)
}
fn tie_unpred(c: &mut Builder, q: Option<QubitId>, s: QubitId, tsign: QubitId, ssign: QubitId) {
    let Some(q) = q else { return };
    if tie_seed() {
        return;
    }
    c.cx(s, q);
    c.cx(tsign, q);
    c.cx(ssign, q);
    c.free(q);
}

/// Compare-width shifts (chunk-boundary dB, overflow-flag dF) applied to every Leapfrog payload cell
/// (`LF_CMP_SHIFT=dB,dF`; each +1 halves that compare's miss rate for about one Toffoli per cell).
fn cmp_shift() -> (isize, isize) {
    static S: OnceLock<(isize, isize)> = OnceLock::new();
    *S.get_or_init(|| {
        let v = std::env::var("LF_CMP_SHIFT").unwrap_or_else(|_| "0,0".into());
        let (a, b) = v.split_once(',').expect("LF_CMP_SHIFT=dB,dF");
        (a.trim().parse().unwrap(), b.trim().parse().unwrap())
    })
}

/// Payload ties (P_T = +-P_S) need R_T = +-R_S, i.e. a parked walk (the rails stay coprime); the earliest park in
/// 640k walks is tick 108. Before tick LF_TIE_FROM (default 0 = always) the cells run without the tie-safe mode,
/// which re-enables the replay cell's prebias / width-composition routes.
fn tie_from() -> usize {
    static F: OnceLock<usize> = OnceLock::new();
    *F.get_or_init(|| std::env::var("LF_TIE_FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
}

/// [`cmp_shift`] applied from tick LF_CMP_FROM on (default 0 = every tick).
fn cmp_shift_at(t: usize) -> (isize, isize) {
    static F: OnceLock<usize> = OnceLock::new();
    let from = *F.get_or_init(|| std::env::var("LF_CMP_FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(0));
    if t >= from { cmp_shift() } else { (0, 0) }
}

fn proxy_fold(w: usize, multiply: bool) -> (usize, usize) {
    let w = std::env::var("LF_PROXY_MIN").ok().and_then(|v| v.parse::<usize>().ok()).map_or(w, |m| w.max(m));
    let proxy = cells::proxy_round(w);
    let extra: usize = std::env::var("LF_CELL_FOLD_EXTRA").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let floor: usize = std::env::var("LF_CELL_FOLD_MIN").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    (((cells::fold_window(proxy, multiply) + extra).max(floor)).min(N - 8), proxy)
}

/// Forward tick t; when `pay` is given, the division payload is updated alongside.
fn fwd_tick(c: &mut Builder, wk: &mut Walk, t: usize, mut pay: Option<&mut [Vec<QubitId>; 2]>) {
    if lf_fast() {
        return fwd_tick_fast(c, wk, t, pay);
    }
    let env = envelope();
    let w = env[t];
    if pay.is_some() && std::env::var_os("LF_PROFILE").is_some() {
        eprintln!("LF_PROF t={t} w={w} active={} peak_so_far={}", c.active_qubits(), c.peak_total());
    }
    let (ti, si) = (t % 2, 1 - t % 2);
    let [r_a, r_b] = &mut wk.r;
    let (tr, br) = if ti == 0 { (r_a, r_b) } else { (r_b, r_a) };
    resize(c, tr, w);
    resize(c, br, w);
    let (fold, proxy) = proxy_fold(w, false);
    let m = forced();
    let mut letter = vec![QubitId(0); if pp_mode() { 1 } else { m + 3 }];
    for i in 0..m {
        let s = c.alloc_qubit();
        pp_sign_into(c, tr, br, s);
        rail_add_halve(c, s, br, tr);
        if let Some(p) = pay.as_deref_mut() {
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            let pr = tie_pred(c, usize::MAX, s, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::add_halve(c, s, &ps, &pt, fold, proxy)));
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
        }
        letter[i] = s;
    }
    if pp_mode() {
        wk.tape.push(letter);
        let wn = env.get(t + 1).copied().unwrap_or(w);
        resize(c, tr, wn);
        resize(c, br, wn);
        return;
    }
    let s3 = c.alloc_qubit();
    let wq = w.max(6);
    resize(c, tr, wq);
    resize(c, br, wq);
    choice_xor(c, tr, br, s3);
    resize(c, tr, w);
    resize(c, br, w);
    rail_add_halve(c, s3, br, tr);
    if let Some(p) = pay.as_deref_mut() {
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        let pr = tie_pred(c, usize::MAX, s3, *tr.last().unwrap(), *br.last().unwrap());
        cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::add_halve(c, s3, &ps, &pt, fold, proxy)));
        tie_unpred(c, pr, s3, *tr.last().unwrap(), *br.last().unwrap());
    }
    letter[m] = s3;
    let (k1, k2) = (c.alloc_qubit(), c.alloc_qubit());
    barrel_bits_xor(c, tr, k1, k2);
    if old_barrel() {
        crot_down_fix(c, k1, tr);
        crot2_down_fix(c, k2, tr);
    } else {
        rail_barrel(c, k1, k2, tr, false);
    }
    if let Some(p) = pay.as_deref_mut().filter(|_| std::env::var("LF_NOBAR").is_err()) {
        if old_barrel() {
            cmod_halve(c, k1, &p[ti]);
            cmod_quarter(c, k2, &p[ti]);
        } else {
            cmod_barrel(c, k1, k2, &p[ti], false);
        }
    }
    letter[m + 1] = k1;
    letter[m + 2] = k2;
    wk.tape.push(letter);
    let wn = env.get(t + 1).copied().unwrap_or(w);
    resize(c, tr, wn);
    resize(c, br, wn);
}

/// [`fwd_tick`] on the fast rail path (`LF_FAST=1`); same letters and payload cells.
fn fwd_tick_fast(c: &mut Builder, wk: &mut Walk, t: usize, mut pay: Option<&mut [Vec<QubitId>; 2]>) {
    let st = steps();
    let [w, n0, n1, n2, nb] = st[t];
    if pay.is_some() && std::env::var_os("LF_PROFILE").is_some() {
        eprintln!("LF_PROF t={t} w={w} active={} peak_so_far={}", c.active_qubits(), c.peak_total());
    }
    let (ti, si) = (t % 2, 1 - t % 2);
    let [r_a, r_b] = &mut wk.r;
    let (tr, br) = if ti == 0 { (r_a, r_b) } else { (r_b, r_a) };
    let (fold, proxy) = proxy_fold(w, false);
    let fk = if pay.is_some() { "F" } else { "R" };
    let tick0 = pmark(c);
    let mut letter = Vec::with_capacity(5);
    // LF_TRIM: during payload ops hold the rails at the widths this tick truncates them to anyway (target: the
    // next step's width; source: min(W(t), W(t+1))), so the cells get the freed wires as scratch.
    let wn = st.get(t + 1).map(|r| r[0]).unwrap_or(w);
    let trim = lf_trim() && pay.is_some();
    let sw = lf_signwire() && pay.is_some();
    let bw = |n: usize| if sw { n.min(w).min(wn) } else { n };
    // LF_LOWREL: o = 1 while the rails are held without their bit-0 wire (the widths below are full widths)
    let lr = lowrel();
    let o = lr as usize;
    for (nk, nnext) in [(n0, n1), (n1, n2)] {
        resize(c, tr, nk - o);
        resize(c, br, bw(nk) - o);
        let s = c.alloc_qubit();
        pp_sign_into1(c, tr[1 - o], br[1 - o], s);
        let q0 = pmark(c);
        if lr {
            fast_add_halve_forced_lr(c, s, br, tr);
        } else {
            fast_add_halve_forced(c, s, br, tr);
        }
        pacc(c, &format!("fwd{fk}.rail_forced"), q0);
        let q0 = pmark(c);
        if let Some(p) = pay.as_deref_mut() {
            if trim {
                let (wt, wb) = (tr.len() + o, br.len() + o);
                resize(c, tr, wt.min(nnext) - o);
                resize(c, br, wb.min(w).min(wn) - o);
            }
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            let pads = lr_pad_c(c, 2 * o);
            let pr = tie_pred(c, t, s, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s, &ps, &pt, fold, proxy)));
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
            lr_unpad(c, pads);
        }
        pacc(c, &format!("fwd{fk}.pay_cell"), q0);
        letter.push(s);
    }
    resize(c, tr, n2 - o);
    resize(c, br, bw(n2) - o);
    let (s3, k1, k2) = (c.alloc_qubit(), c.alloc_qubit(), c.alloc_qubit());
    let q0 = pmark(c);
    if lr {
        lr_restore(c, tr);
        lr_restore(c, br);
    }
    fast_choice(c, tr, br, s3, k1, k2, t);
    if lr {
        lr_drop(c, br);
        lr_drop(c, tr);
    }
    pacc(c, &format!("fwd{fk}.choice"), q0);
    let q0 = pmark(c);
    if lr {
        fast_add_halve_choice_lr(c, s3, br, tr);
    } else {
        fast_add_halve_choice(c, s3, br, tr);
    }
    pacc(c, &format!("fwd{fk}.rail_choice"), q0);
    if trim {
        let wb = br.len() + o;
        resize(c, br, wb.min(w).min(wn) - o);
    }
    // LF_MERGED: the third cell and the payload barrel become one merged op, run after the rail barrel (they act on
    // disjoint registers); the fit is judged at the live count there (tr at width nb; LF_LOWREL: its bit 0 released).
    let at_barrel = (c.active_qubits() as usize + nb).checked_sub(tr.len() + o).unwrap() + if lr_pad_on() { 2 * o } else { 0 };
    // on tie-safe ticks the merged op runs with the cells' tie predicate (one more live wire)
    let merged = if pay.is_some() { merged_fits(at_barrel + usize::from(t >= tie_from() && !tie_seed()), t, false) } else { None };
    let qc3 = pmark(c);
    let q0 = pmark(c);
    if let Some(p) = pay.as_deref_mut().filter(|_| merged.is_none()) {
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        let pads = lr_pad_c(c, o);
        let pr = tie_pred(c, t, s3, *tr.last().unwrap(), *br.last().unwrap());
        cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s3, &ps, &pt, fold, proxy)));
        tie_unpred(c, pr, s3, *tr.last().unwrap(), *br.last().unwrap());
        lr_unpad(c, pads);
        pacc(c, &format!("c3cell.fwd.t{t:03}"), q0);
    }
    pacc(c, &format!("fwd{fk}.pay_cell"), q0);
    resize(c, tr, nb);
    let q0 = pmark(c);
    if fast_rail_barrel(c, k1, k2, tr, false, lr) {
        tr.remove(0); // released inside the barrel
    } else if lr {
        lr_drop(c, tr);
    }
    pacc(c, &format!("fwd{fk}.rail_barrel"), q0);
    let q0 = pmark(c);
    let pads = if pay.is_some() { lr_pad(c, 2 * o) } else { Vec::new() };
    if let Some(p) = pay.as_deref_mut() {
        if let Some(mw) = merged {
            assert_eq!(c.active_qubits() as usize, at_barrel);
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            let pr = tie_pred(c, t, s3, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || {
                cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, false, || {
                    let split = if pr.is_none() { merged_split(c, proxy, false, false) } else { None };
                    if lf_merged_trace() {
                        eprintln!("LF_MERGED_SPLIT fwd t={t} proxy={proxy} split={split:?} active={}", c.active_qubits());
                    }
                    merged_fwd(c, s3, &ps, &pt, k1, k2, proxy, split, mw)
                }))
            });
            tie_unpred(c, pr, s3, *tr.last().unwrap(), *br.last().unwrap());
            pacc(c, &format!("fwd{fk}.pay_merged"), q0);
        } else {
            cmod_barrel(c, k1, k2, &p[ti], false);
            pacc(c, &format!("c3bar.fwd.t{t:03}"), q0);
        }
    }
    lr_unpad(c, pads);
    pacc(c, &format!("fwd{fk}.pay_barrel"), q0);
    if pay.is_some() {
        pacc(c, &format!("c3b.fwd.t{t:03}"), qc3);
    }
    pacc(c, &format!("tick.fwd{fk}.t{:03}", t / 10 * 10), tick0);
    letter.extend([s3, k1, k2]);
    wk.tape.push(letter);
    resize(c, tr, wn - o);
    resize(c, br, wn - o);
}

/// Exact inverse of [`fwd_tick_fast`].
fn rev_tick_fast(c: &mut Builder, wk: &mut Walk, t: usize, mut pay: Option<&mut [Vec<QubitId>; 2]>) {
    let st = steps();
    let [w, n0, n1, n2, nb] = st[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let letter = wk.tape.pop().expect("tape underflow");
    let (s0, s1, s3, k1, k2) = (letter[0], letter[1], letter[2], letter[3], letter[4]);
    let [r_a, r_b] = &mut wk.r;
    let (tr, br) = if ti == 0 { (r_a, r_b) } else { (r_b, r_a) };
    // LF_TRIM: the forward tick left the target within min(nb, W(t+1)) bits and the source within
    // min(W(t), W(t+1)); keep them there through the payload ops instead of widening to W(t) first.
    let wn = st.get(t + 1).map(|r| r[0]).unwrap_or(w);
    let sw = lf_signwire() && pay.is_some();
    let bw = |n: usize| if sw { n.min(w).min(wn) } else { n };
    let lr = lowrel();
    let o = lr as usize;
    if lf_trim() && pay.is_some() {
        resize(c, tr, nb.min(wn) - o);
        resize(c, br, w.min(wn) - o);
    } else {
        resize(c, tr, w - o);
        resize(c, br, w - o);
    }
    let (fold, proxy) = proxy_fold(w, true);
    let fk = if pay.is_some() { "F" } else { "R" };
    let tick0 = pmark(c);
    let pads = if pay.is_some() { lr_pad(c, 2 * o) } else { Vec::new() };
    if let Some(p) = pay.as_deref_mut() {
        let q0 = pmark(c);
        let merged = merged_fits(c.active_qubits() as usize + usize::from(t >= tie_from() && !tie_seed()), t, true);
        if let Some(mw) = merged {
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            // the reverse runs the cell's frame with the sign flipped (as double_add with s^1): predicate of NOT s3
            let pr = (t >= tie_from()).then(|| {
                c.x(s3);
                let pr = tie_pred(c, t, s3, *tr.last().unwrap(), *br.last().unwrap());
                c.x(s3);
                pr
            }).flatten();
            cells::with_tie(pr, || {
                cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, true, || merged_rev(c, s3, &ps, &pt, k1, k2, proxy, pr.is_none(), mw)))
            });
            if pr.is_some() {
                c.x(s3);
                tie_unpred(c, pr, s3, *tr.last().unwrap(), *br.last().unwrap());
                c.x(s3);
            }
            pacc(c, "revF.pay_merged", q0);
            pacc(c, &format!("c3b.rev.t{t:03}"), q0);
        } else {
            cmod_barrel(c, k1, k2, &p[ti], true);
            pacc(c, &format!("c3bar.rev.t{t:03}"), q0);
        }
        pacc(c, "revF.pay_barrel", q0);
        let qc3 = q0;
        let q0 = pmark(c);
        for s in [s3, s1, s0] {
            if merged.is_some() && s == s3 {
                continue;
            }
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            c.x(s);
            let cp = lr_pad_c2(c, 2 * o);
            let pr = tie_pred(c, t, s, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || cells::double_add(c, s, &ps, &pt, fold, proxy)));
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
            lr_unpad(c, cp);
            c.x(s);
            if s == s3 {
                pacc(c, &format!("c3b.rev.t{t:03}"), qc3);
            }
        }

        pacc(c, "revF.pay_cell", q0);
    }
    lr_unpad(c, pads);
    resize(c, tr, nb - o);
    resize(c, br, bw(n2) - o);
    let q0 = pmark(c);
    if lr {
        lr_restore(c, tr);
    }
    fast_rail_barrel(c, k1, k2, tr, true, false);
    pacc(c, &format!("rev{fk}.rail_barrel"), q0);
    resize(c, tr, n2 - 1);
    let q0 = pmark(c);
    fast_k_erase(c, tr, k1, k2);
    pacc(c, &format!("rev{fk}.k_erase"), q0);
    let q0 = pmark(c);
    if lr {
        fast_double_sub_choice_lr(c, s3, br, tr);
    } else {
        fast_double_sub_choice(c, s3, br, tr);
    }
    pacc(c, &format!("rev{fk}.rail_choice"), q0);
    let q0 = pmark(c);
    if lr {
        lr_restore(c, tr);
        lr_restore(c, br);
    }
    fast_choice_erase(c, tr, br, s3, t);
    if lr {
        lr_drop(c, br);
        lr_drop(c, tr);
    }
    pacc(c, &format!("rev{fk}.choice_erase"), q0);
    for (s, nk) in [(s1, n1), (s0, n0)] {
        resize(c, tr, nk - 1 - o);
        resize(c, br, bw(nk) - o);
        let q0 = pmark(c);
        if lr {
            fast_double_sub_forced_lr(c, s, br, tr);
        } else {
            fast_double_sub_forced(c, s, br, tr);
        }
        pacc(c, &format!("rev{fk}.rail_forced"), q0);
        pp_sign_into1(c, tr[1 - o], br[1 - o], s);
        c.free(s);
    }
    pacc(c, &format!("tick.rev{fk}.t{:03}", t / 10 * 10), tick0);
    resize(c, tr, w - o);
    resize(c, br, w - o);
}

/// Exact inverse of [`fwd_tick`]; with `pay`, applies the multiply-direction payload cells first.
fn rev_tick(c: &mut Builder, wk: &mut Walk, t: usize, mut pay: Option<&mut [Vec<QubitId>; 2]>) {
    if lf_fast() {
        return rev_tick_fast(c, wk, t, pay);
    }
    let env = envelope();
    let w = env[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let letter = wk.tape.pop().expect("tape underflow");
    let [r_a, r_b] = &mut wk.r;
    let (tr, br) = if ti == 0 { (r_a, r_b) } else { (r_b, r_a) };
    resize(c, tr, w);
    resize(c, br, w);
    let m = forced();
    let (fold, proxy) = proxy_fold(w, true);
    if pp_mode() {
        let s = letter[0];
        if let Some(p) = pay.as_deref_mut() {
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            c.x(s);
            let pr = tie_pred(c, usize::MAX, s, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::double_add(c, s, &ps, &pt, fold, proxy)));
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
            c.x(s);
        }
        rail_double_sub(c, s, br, tr);
        pp_sign_into(c, tr, br, s);
        c.free(s);
        return;
    }
    let (k1, k2) = (letter[m + 1], letter[m + 2]);
    if let Some(p) = pay.as_deref_mut() {
        if old_barrel() {
            cmod_quadruple(c, k2, &p[ti]);
            cmod_double(c, k1, &p[ti]);
        } else {
            cmod_barrel(c, k1, k2, &p[ti], true);
        }
        for i in (0..=m).rev() {
            let s = letter[i];
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            c.x(s);
            let pr = tie_pred(c, usize::MAX, s, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::double_add(c, s, &ps, &pt, fold, proxy)));
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
            c.x(s);
        }
    }
    if old_barrel() {
        crot2_up_fix(c, k2, tr);
        crot_up_fix(c, k1, tr);
    } else {
        rail_barrel(c, k1, k2, tr, true);
    }
    barrel_bits_xor(c, tr, k1, k2);
    c.free(k1);
    c.free(k2);
    rail_double_sub(c, letter[m], br, tr);
    let wq = w.max(6);
    resize(c, tr, wq);
    resize(c, br, wq);
    choice_xor(c, tr, br, letter[m]);
    resize(c, tr, w);
    resize(c, br, w);
    c.free(letter[m]);
    for i in (0..m).rev() {
        let s = letter[i];
        rail_double_sub(c, s, br, tr);
        pp_sign_into(c, tr, br, s);
        c.free(s);
    }
}

fn rounds() -> usize {
    envelope().len()
}

/// LF_REORDER=T: the payload-fused traversals leave their first T ticks to a rails-only pass plus a payload-only
/// pass (letters read back from the tape). The rail adds then run with one payload register live (no room splits)
/// and the cells run beside the rails parked at tick T. 0 = off. T must stay below the tie-safe ticks.
fn lf_reorder(multiply: bool) -> usize {
    let key = if multiply { "LF_REORDER_MUL" } else { "LF_REORDER_DIV" };
    let r = std::env::var(key).or_else(|_| std::env::var("LF_REORDER")).ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    assert!(r == 0 || r <= tie_from(), "LF_REORDER must not reach the tie-safe ticks");
    r.min(rounds())
}

/// Payload half of [`fwd_tick_fast`] on a tick below the tie-safe ticks, its letter already on the tape.
fn pay_fwd_tick(c: &mut Builder, t: usize, letter: &[QubitId], p: &mut [Vec<QubitId>; 2]) {
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (fold, proxy) = proxy_fold(w, false);
    let (s0, s1, s3, k1, k2) = (letter[0], letter[1], letter[2], letter[3], letter[4]);
    for s in [s0, s1] {
        let q0 = pmark(c);
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        let cp = lr_pad_c2(c, 2 * lowrel() as usize);
        cells::with_tie(None, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s, &ps, &pt, fold, proxy)));
        lr_unpad(c, cp);
        pacc(c, "fwdP.pay_cell", q0);
    }
    let q0 = pmark(c);
    let (pt, ps) = (p[ti].clone(), p[si].clone());
    if let Some(mw) = merged_fits(c.active_qubits() as usize, t, false) {
        cells::with_tie(None, || {
            cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, false, || {
                let split = merged_split(c, proxy, false, false);
                merged_fwd(c, s3, &ps, &pt, k1, k2, proxy, split, mw)
            }))
        });
        pacc(c, "fwdP.pay_merged", q0);
    } else {
        let cp = lr_pad_c2(c, 2 * lowrel() as usize);
        cells::with_tie(None, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s3, &ps, &pt, fold, proxy)));
        lr_unpad(c, cp);
        cmod_barrel(c, k1, k2, &p[ti], false);
        pacc(c, "fwdP.pay_cell_barrel", q0);
    }
}

/// Payload half of [`rev_tick_fast`] on a tick below the tie-safe ticks (the tape is read, not popped).
fn pay_rev_tick(c: &mut Builder, t: usize, letter: &[QubitId], p: &mut [Vec<QubitId>; 2]) {
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (fold, proxy) = proxy_fold(w, true);
    let (s0, s1, s3, k1, k2) = (letter[0], letter[1], letter[2], letter[3], letter[4]);
    let q0 = pmark(c);
    let merged = merged_fits(c.active_qubits() as usize, t, true);
    if let Some(mw) = merged {
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        cells::with_tie(None, || {
            cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, true, || merged_rev(c, s3, &ps, &pt, k1, k2, proxy, true, mw)))
        });
        pacc(c, "revP.pay_merged", q0);
    } else {
        cmod_barrel(c, k1, k2, &p[ti], true);
        pacc(c, "revP.pay_barrel", q0);
    }
    for s in [s3, s1, s0] {
        if merged.is_some() && s == s3 {
            continue;
        }
        let q0 = pmark(c);
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        c.x(s);
        let cp = lr_pad_c2(c, 2 * lowrel() as usize);
        cells::with_tie(None, || cells::with_cmp_shift(cmp_shift_at(t), || cells::double_add(c, s, &ps, &pt, fold, proxy)));
        lr_unpad(c, cp);
        c.x(s);
        pacc(c, "revP.pay_cell", q0);
    }
}

/// `y <- y / x (mod p)`, x restored. Division payload fused into the forward walk; rails-only walkback.
pub fn divide(c: &mut Builder, y: &[QubitId], x: &[QubitId]) {
    divide_dbg(c, y, x, false);
}
/// `LF_SEAMS=1`: fuse the coordinate ops into the walks' seeds (see [`seed_r0_seam`], [`seam_add_reduce`]).
pub fn seams() -> bool {
    lf_seams() && seed_half()
}

/// [`divide`] with the coordinate shell fused in (`LF_SEAMS`): x <- x2 - ox enters the seed, and the unseed leaves
/// x = x2 - ox + 3 ox + (square offset) mod p, i.e. the state after coord_x_sub, divide and coord_add3x.
pub fn divide_seamed(c: &mut Builder, y: &[QubitId], x: &[QubitId], ox: &[crate::circuit::BitId]) {
    let c3 = super::classical::add3x_operand(c, ox);
    SEAM_OPS.with(|s| *s.borrow_mut() = Some((ox.to_vec(), c3.clone())));
    divide_dbg(c, y, x, false);
    SEAM_OPS.with(|s| *s.borrow_mut() = None);
    super::classical::release_operand(c, &c3);
}

/// [`multiply`] with coord_rsub_final fused into the unseed (`LF_SEAMS`): leaves x = ox - u mod p.
pub fn multiply_seamed(c: &mut Builder, y: &[QubitId], x: &[QubitId], ox: &[crate::circuit::BitId]) {
    let p1 = super::classical::plus1_operand(c, ox);
    SEAM_MUL.with(|s| *s.borrow_mut() = Some((ox.to_vec(), p1.clone())));
    multiply(c, y, x);
    SEAM_MUL.with(|s| *s.borrow_mut() = None);
    super::classical::release_operand(c, &p1);
}

thread_local! {
    /// Divide seam operands (ox, 3 ox + offset mod p) while [`divide_seamed`] runs.
    static SEAM_OPS: std::cell::RefCell<Option<(Vec<crate::circuit::BitId>, Vec<crate::circuit::BitId>)>> = const { std::cell::RefCell::new(None) };
    /// Multiply seam operands (ox, ox + 1) while [`multiply_seamed`] runs.
    static SEAM_MUL: std::cell::RefCell<Option<(Vec<crate::circuit::BitId>, Vec<crate::circuit::BitId>)>> = const { std::cell::RefCell::new(None) };
}


pub(crate) fn divide_dbg(c: &mut Builder, y: &[QubitId], x: &[QubitId], keep_p1: bool) -> Vec<QubitId> {
    let q0 = pmark(c);
    let r = match SEAM_OPS.with(|s| s.borrow().clone()) {
        Some((ox, _)) => {
            let r0 = seed_r0_seam(c, x, &ox);
            let r1 = seed_r1(c, &r0);
            lr_walk_drop(c, [r0, r1])
        }
        None => seed(c, x),
    };
    pacc(c, "div.seed", q0);
    let mut wk = Walk { r, tape: Vec::new() };
    let ahead = lf_reorder(false);
    for t in 0..ahead {
        fwd_tick(c, &mut wk, t, None);
    }
    let q0 = pmark(c);
    let p1 = c.alloc_qubits(N);
    c.cx_pairs(y, &p1);
    if seed_half() {
        cells::mod_halve(c, &p1); // P1 = y/2
    } else {
        cells::mod_double(c, &p1);
        mod_addsub(c, false, y, &p1); // P1 = 3y
    }
    let mut pay = [y.to_vec(), p1];
    pacc(c, "div.p1_setup", q0);
    for t in 0..ahead {
        let letter = wk.tape[t].clone();
        let pads = lr_pad(c, 2 * lowrel() as usize);
        pay_fwd_tick(c, t, &letter, &mut pay);
        lr_unpad(c, pads);
    }
    for t in ahead..rounds() {
        fwd_tick(c, &mut wk, t, Some(&mut pay));
    }
    let q0 = pmark(c);
    // endpoint: rails (+-1, +-1); P = (s0 lam, s1 lam)
    let (s0, s1) = (*wk.r[0].last().unwrap(), *wk.r[1].last().unwrap());
    let x01 = c.alloc_qubit();
    c.cx(s0, x01);
    c.cx(s1, x01);
    cells::cond_negate(c, x01, &pay[1]);
    c.cx_pairs(&pay[0], &pay[1]);
    c.cx(s0, x01);
    c.cx(s1, x01);
    c.free(x01);
    let p1 = std::mem::take(&mut pay[1]);
    if !keep_p1 {
        c.free_vec(&p1);
    }
    cells::cond_negate(c, s0, &pay[0]);
    pacc(c, "div.endpoint", q0);
    for t in (0..rounds()).rev() {
        rev_tick(c, &mut wk, t, None);
    }
    let q0 = pmark(c);
    match SEAM_OPS.with(|s| s.borrow().clone()) {
        Some((_, c3)) => {
            let rr = lr_walk_restore(c, wk.r);
            let r0 = unseed_r1(c, rr);
            let low = seam_add_reduce(c, r0, &c3, &c3);
            restore_onto(c, low, x);
        }
        None => unseed(c, wk.r, x),
    }
    pacc(c, "div.unseed", q0);
    p1
}

/// `y <- y * x (mod p)`, x restored. Rails-only forward, payload fused into the walkback.
pub fn multiply(c: &mut Builder, y: &[QubitId], x: &[QubitId]) {
    let q0 = pmark(c);
    let r = seed(c, x);
    pacc(c, "mul.seed", q0);
    let mut wk = Walk { r, tape: Vec::new() };
    for t in 0..rounds() {
        fwd_tick(c, &mut wk, t, None);
    }
    let (s0, s1) = (*wk.r[0].last().unwrap(), *wk.r[1].last().unwrap());
    let q0 = pmark(c);
    let mut pay = [y.to_vec(), c.alloc_qubits(N)];
    cells::cond_negate(c, s0, &pay[0]);
    c.cx_pairs(&pay[0], &pay[1]);
    let x01 = c.alloc_qubit();
    c.cx(s0, x01);
    c.cx(s1, x01);
    cells::cond_negate(c, x01, &pay[1]);
    c.cx(s0, x01);
    c.cx(s1, x01);
    c.free(x01);
    pacc(c, "mul.endpoint", q0);
    let ahead = lf_reorder(true);
    for t in (ahead..rounds()).rev() {
        rev_tick(c, &mut wk, t, Some(&mut pay));
    }
    for t in (0..ahead).rev() {
        let letter = wk.tape[t].clone();
        let pads = lr_pad(c, 2 * lowrel() as usize);
        pay_rev_tick(c, t, &letter, &mut pay);
        lr_unpad(c, pads);
    }
    let q0 = pmark(c);
    let p1 = std::mem::take(&mut pay[1]);
    if seed_half() {
        cells::mod_double(c, &p1); // P0
    } else {
        mod_addsub(c, true, &pay[0], &p1); // 2 P0
        cells::mod_halve(c, &p1); // P0
    }
    c.cx_pairs(&pay[0], &p1);
    c.free_vec(&p1);
    for t in (0..ahead).rev() {
        rev_tick(c, &mut wk, t, None);
    }
    match SEAM_MUL.with(|s| s.borrow().clone()) {
        Some((ox, p1c)) => {
            // ox - R = (-R) + ox: complement R (= -R - 1) and add ox + 1
            let rr = lr_walk_restore(c, wk.r);
            let r0 = unseed_r1(c, rr);
            c.x_all(&r0);
            let low = seam_add_reduce(c, r0, &p1c, &ox);
            restore_onto(c, low, x);
        }
        None => unseed(c, wk.r, x),
    }
    pacc(c, "mul.p1_unseed", q0);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{analyze_ops, QubitOrBit};
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::digest::{ExtendableOutput, Update};

    fn modp() -> U256 {
        super::super::SECP256K1_P
    }
    fn mulmod(a: U256, b: U256) -> U256 {
        a.mul_mod(b, modp())
    }
    fn inv(a: U256) -> U256 {
        a.pow_mod(modp() - U256::from(2u8), modp())
    }

    pub(super) fn run_pub(kind: &str, batches: usize) { run(kind, batches) }
    fn run(kind: &str, batches: usize) {
        super::super::install_skywalk_submission_recipe();
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let mut c = Builder::new();
        let x = c.alloc_qubits(N);
        let y = c.alloc_qubits(N);
        let mut extra: Option<Vec<QubitId>> = None;
        let mut extra2: Option<QubitId> = None;
        match kind {
            "div" => divide(&mut c, &y, &x),
            "mul" => multiply(&mut c, &y, &x),
            "rails" | "rails1" => {
                let r = seed(&mut c, &x);
                let mut wk = Walk { r, tape: Vec::new() };
                let n = if kind == "rails1" { 1 } else { rounds() };
                for t in 0..n { fwd_tick(&mut c, &mut wk, t, None); }
                for t in (0..n).rev() { rev_tick(&mut c, &mut wk, t, None); }
                unseed(&mut c, wk.r, &x);
            }
            "seed" => { let r = seed(&mut c, &x); unseed(&mut c, r, &x); }
            "fwdrails" | "fwdpay" | "fwdpaynobar" => {
                let r = seed(&mut c, &x);
                let mut wk = Walk { r, tape: Vec::new() };
                let p1 = c.alloc_qubits(N);
                c.cx_pairs(&y, &p1);
                let mut pay = [y.to_vec(), p1];
                let n = std::env::var("LF_N").ok().and_then(|v| v.parse().ok()).unwrap_or(rounds());
                if kind == "fwdpaynobar" { std::env::set_var("LF_NOBAR", "1"); }
                for t in 0..n { fwd_tick(&mut c, &mut wk, t, if kind == "fwdrails" { None } else { Some(&mut pay) }); }
                std::env::remove_var("LF_NOBAR");
            }
            k if k.starts_with("fr") => {
                // fused forward n ticks, then exact inverse (multiply-direction payload) n ticks: identity
                let n: usize = k[2..].parse().unwrap();
                let r = seed(&mut c, &x);
                let mut wk = Walk { r, tape: Vec::new() };
                let p1 = c.alloc_qubits(N);
                c.cx_pairs(&y, &p1);
                let mut pay = [y.to_vec(), p1];
                for t in 0..n { fwd_tick(&mut c, &mut wk, t, Some(&mut pay)); }
                for t in (0..n).rev() { rev_tick(&mut c, &mut wk, t, Some(&mut pay)); }
                let p1 = std::mem::take(&mut pay[1]);
                c.cx_pairs(&y, &p1);
                c.free_vec(&p1);
                unseed(&mut c, wk.r, &x);
            }
            "cell" => {
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let cw = std::env::var("LF_CELLW").ok().and_then(|v| v.parse().ok()).unwrap_or(200);
                let (fold, proxy) = proxy_fold(cw, false);
                eprintln!("cellw={cw} proxy={proxy} fold={fold}");
                cells::add_halve(&mut c, sg, &x, &y, fold, proxy);
                extra2 = Some(sg);
            }
            "chalve" => { cmod_halve(&mut c, x[0], &y); }
            "cquarter" => { cmod_quarter(&mut c, x[0], &y); }
            "cbarrel" => { cmod_barrel(&mut c, x[0], x[1], &y, false); }
            "cbpair" => { cmod_barrel(&mut c, x[0], x[1], &y, false); cmod_barrel(&mut c, x[0], x[1], &y, true); }
            "rbarrel" => {
                // rail: odd value v * 2^e in a 262-bit register, e = x mod 4; check arithmetic shift right
                let w = 262; let t = c.alloc_qubits(w);
                c.cx_pairs(&y, &t[..N]);
                for q in &t[N..] { c.cx(y[N - 1], *q); }
                rail_barrel(&mut c, x[0], x[1], &t, false);
                rail_barrel(&mut c, x[0], x[1], &t, true);
                for q in &t[N..] { c.cx(y[N - 1], *q); }
                c.cx_pairs(&y, &t[..N]);
                c.free_vec(&t);
            }
            "cqpair" => { cmod_quarter(&mut c, x[0], &y); cmod_quadruple(&mut c, x[0], &y); }
            "celltie" | "celltie261" => {
                let src = c.alloc_qubits(N); c.cx_pairs(&y, &src);
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let (fold, proxy) = proxy_fold(if kind == "celltie" { 200 } else { 261 }, false);
                cells::add_halve(&mut c, sg, &src, &y, fold, proxy);
                c.x(sg);
                cells::double_add(&mut c, sg, &src, &y, fold, proxy);
                c.x(sg);
                c.cx(x[1], sg); c.free(sg);
                c.cx_pairs(&y, &src); c.free_vec(&src);
            }
            "tiesafe" | "tiesafe_neg" => {
                let src = c.alloc_qubits(N); c.cx_pairs(&y, &src);
                if kind == "tiesafe_neg" { let one = c.alloc_qubit(); c.x(one); cells::cond_negate(&mut c, one, &src); c.x(one); c.free(one); }
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let pr = c.alloc_qubit(); c.cx(sg, pr); if kind == "tiesafe_neg" { c.x(pr); }
                let (fold, proxy) = proxy_fold(30, false);
                cells::with_tie(Some(pr), || cells::with_cmp_shift(cmp_shift(), || cells::add_halve(&mut c, sg, &src, &y, fold, proxy)));
                c.x(sg); c.x(pr);
                cells::with_tie(Some(pr), || cells::with_cmp_shift(cmp_shift(), || cells::double_add(&mut c, sg, &src, &y, fold, proxy)));
                c.x(sg); c.x(pr);
                if kind == "tiesafe_neg" { c.x(pr); } c.cx(sg, pr); c.free(pr);
                c.cx(x[1], sg); c.free(sg);
                if kind == "tiesafe_neg" { let one = c.alloc_qubit(); c.x(one); cells::cond_negate(&mut c, one, &src); c.x(one); c.free(one); }
                c.cx_pairs(&y, &src); c.free_vec(&src);
            }
            "cell261" => {
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let (fold, proxy) = proxy_fold(261, false);
                cells::add_halve(&mut c, sg, &x, &y, fold, proxy);
                c.x(sg);
                cells::double_add(&mut c, sg, &x, &y, fold, proxy);
                c.x(sg);
                extra2 = Some(sg);
            }
            "chpair" => { cmod_halve(&mut c, x[0], &y); cmod_double(&mut c, x[0], &y); }
            "cellpair" | "cellpair_m" => {
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let mm = kind == "cellpair_m";
                let (fold, proxy) = proxy_fold(200, false);
                cells::add_halve(&mut c, sg, &x, &y, fold, proxy);
                let (fold2, proxy2) = proxy_fold(200, true);
                let (fold2, proxy2) = if mm { (fold2, proxy2) } else { (fold, proxy) };
                c.x(sg);
                cells::double_add(&mut c, sg, &x, &y, fold2, proxy2);
                c.x(sg);
                extra2 = Some(sg);
            }
            "dbl" => {
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let (fold, proxy) = proxy_fold(200, true);
                cells::double_add(&mut c, sg, &x, &y, fold, proxy);
                extra2 = Some(sg);
            }
            "negate" => { cells::cond_negate(&mut c, x[0], &y); }
            "divp1" => { let p1 = divide_dbg(&mut c, &y, &x, true); extra = Some(p1); }
            _ => panic!(),
        }
        if let Some(sg) = extra2 { c.cx(x[1], sg); c.free(sg); }
        c.declare_qubit_register(&x);
        c.declare_qubit_register(&y);
        if let Some(e) = &extra { c.declare_qubit_register(e); }
        let peak = c.peak_total();
        prof_dump();
        let ops = c.take_ops();
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"leapfrog-test");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rnd = || {
            let mut v = U256::ZERO;
            for i in 0..4 {
                seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
                v |= U256::from(seed) << (64 * i);
            }
            v % modp()
        };
        let (mut bad, mut phase_bad, mut anc_bad, mut shots) = (0, 0, 0, 0);
        let mut phase_shots = 0usize;
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut ins = Vec::new();
            for shot in 0..64 {
                let (xv, yv) = (rnd().max(U256::from(1u8)), rnd());
                sim.set_register(&regs[0], xv, shot);
                sim.set_register(&regs[1], yv, shot);
                ins.push((xv, yv));
            }
            sim.apply_iter(ops.iter());
            if regs.len() > 2 {
                let mut nz = 0;
                let mut ex = None;
                for (shot, &(xv, yv)) in ins.iter().enumerate() {
                    let v = sim.get_register(&regs[2], shot);
                    if v != U256::ZERO { nz += 1; if ex.is_none() { ex = Some((v, mulmod(yv, inv(xv)))); } }
                }
                eprintln!("P1 nonzero in {nz}/64 shots; example (P1, lambda) = {:?}", ex);
            }
            for (shot, &(xv, yv)) in ins.iter().enumerate() {
                let gx = sim.get_register(&regs[0], shot);
                let gy = sim.get_register(&regs[1], shot);
                let want = match kind {
                    "div" | "divp1" => mulmod(yv, inv(xv)),
                    "mul" => mulmod(yv, xv),
                    "cell" => { let h = inv(U256::from(2u8)); let s = if xv.bit(1) { modp() - xv } else { xv }; mulmod(yv.add_mod(s, modp()), h) }
                    "chalve" => if xv.bit(0) { mulmod(yv, inv(U256::from(2u8))) } else { yv },
                    "cquarter" => if xv.bit(0) { mulmod(yv, inv(U256::from(4u8))) } else { yv },
                    "cbarrel" => { let e = (xv.bit(0) as u32) + 2 * (xv.bit(1) as u32); mulmod(yv, inv(U256::from(1u64 << e))) }
                    "cbpair" | "rbarrel" => yv,
                    "cqpair" => yv,
                    "chpair" | "cellpair" | "cellpair_m" | "celltie" | "celltie261" | "cell261" | "tiesafe" | "tiesafe_neg" => yv,
                    "dbl" => { let s = if xv.bit(1) { modp() - xv } else { xv }; yv.add_mod(yv, modp()).add_mod(s, modp()) }
                    "negate" => if xv.bit(0) { (modp() - yv) % modp() } else { yv },
                    _ => yv };
                if gx != xv || gy != want {
                    bad += 1;
                    eprintln!("WRONG kind={kind} x={xv:#x} y={yv:#x} got_x_ok={} got_y={gy:#x} want={want:#x}", gx == xv);
                }
            }
            if sim.phase != 0 {
                phase_bad += 1;
                phase_shots += sim.phase.count_ones() as usize;
                for (shot, &(xv, yv)) in ins.iter().enumerate() {
                    if (sim.phase >> shot) & 1 == 1 {
                        eprintln!("PHASEBAD kind={kind} x={xv:#x} y={yv:#x}");
                    }
                }
            }
            for reg in &regs {
                for qb in reg {
                    if let QubitOrBit::Qubit(q) = *qb {
                        *sim.qubit_mut(q) = 0;
                    }
                }
            }
            if (0..nq).any(|q| sim.qubit(crate::circuit::QubitId(q)) != 0) {
                anc_bad += 1;
            }
            shots += 64;
        }
        let avg_t = sim.stats.toffoli_gates as f64 / shots as f64;
        eprintln!("LEAPFROG {kind}: shots={shots} wrong={bad} phase_bad_batches={phase_bad} phase_bad_shots={phase_shots} ancilla_bad_batches={anc_bad} \
                   avgT={avg_t:.0} peak={peak} qubits={nq} rounds={}", rounds());
        assert_eq!(bad, 0, "wrong results");
        assert_eq!(anc_bad, 0, "ancilla garbage");
    }

    /// Full point addition with LEAPFROG on, simulated like eval_circuit (random k*G points).
    #[test]
    fn leapfrog_point_add() {
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        if std::env::var_os("LF_USE_RECIPE").is_some() { install_recipe(); }
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        if let Ok(ov) = std::env::var("LF_OVR") {
            for kv in ov.split(';').filter(|k| !k.is_empty()) { let (k, v) = kv.split_once('=').unwrap(); std::env::set_var(k, v); }
        }
        if let Ok(list) = std::env::var("LF_UNSET") {
            for k in list.split(',').filter(|k| !k.is_empty()) { std::env::remove_var(k); }
        }
        let ops = super::super::build_point_add();
        prof_dump();
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let hx = |h: &str| U256::from_str_radix(h, 16).unwrap();
        let curve = crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
            modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
            a: U256::from(0u8), b: U256::from(7u8),
            gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
            order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        };
        let mut h = sha3::Shake256::default();
        h.update(b"leapfrog-pa");
        // LF_PA_MEASSEED: a different measurement-outcome stream (same inputs), to separate phase-prone shots from luck
        if let Ok(ms) = std::env::var("LF_PA_MEASSEED") { h.update(ms.as_bytes()); }
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        // LF_SIMSEED: a different input stream
        let simseed: u64 = std::env::var("LF_SIMSEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
        let mut seed = 0x1234_5678_9abc_def1u64 ^ simseed.wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let mut rnd = || { let mut v = U256::ZERO; for i in 0..4 { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; v |= U256::from(seed) << (64 * i); } v };
        let (mut bad, mut phase_shots, mut anc, mut shots) = (0, 0usize, 0, 0);
        let (mut xbad, mut ybad, mut yneg) = (0, 0, 0);
        let batches = std::env::var("LF_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut exp = Vec::new();
            let mut pts = Vec::new();
            let pain: Option<Vec<U256>> = std::env::var("LF_PAIN").ok().map(|v| v.split(',').map(|h| U256::from_str_radix(h.trim().trim_start_matches("0x"), 16).unwrap()).collect());
            for shot in 0..64 {
                let (t, o) = if let Some(pv) = &pain { ((pv[0], pv[1]), (pv[2], pv[3])) } else {
                    (curve.mul(curve.gx, curve.gy, rnd()), curve.mul(curve.gx, curve.gy, rnd())) };
                pts.push((t.0, t.1, o.0, o.1));
                sim.set_register(&regs[0], t.0, shot);
                sim.set_register(&regs[1], t.1, shot);
                sim.set_register(&regs[2], o.0, shot);
                sim.set_register(&regs[3], o.1, shot);
                exp.push(curve.add(t.0, t.1, o.0, o.1));
            }
            sim.apply_iter(ops.iter());
            for (shot, e) in exp.iter().enumerate() {
                let (gx, gy) = (sim.get_register(&regs[0], shot), sim.get_register(&regs[1], shot));
                let ph = (sim.phase >> shot) & 1 == 1;
                if gx != e.0 || gy != e.1 || ph {
                    let (t0, o0) = (pts[shot].0, pts[shot].2);
                    let dx = t0.add_mod(modp() - o0, modp());
                    let xp = o0.add_mod(modp() - e.0, modp());
                    eprintln!("PAFAIL dx={dx:#x} xp={xp:#x} wrong={} phase={}", gx != e.0 || gy != e.1, ph);
                    if std::env::var_os("LF_PAFULL").is_some() { eprintln!("PAINPUT batch={} shot={shot} x2={:#x} y2={:#x} ox={:#x} oy={:#x}", shots / 64, pts[shot].0, pts[shot].1, pts[shot].2, pts[shot].3); }
                }
                if gx != e.0 || gy != e.1 { bad += 1; }
                if gx != e.0 { xbad += 1; }
                if gy != e.1 { ybad += 1; if gy == (modp() - e.1) % modp() { yneg += 1; } }
            }
            phase_shots += sim.phase.count_ones() as usize;
            for reg in &regs { for qb in reg { if let QubitOrBit::Qubit(q) = *qb { *sim.qubit_mut(q) = 0; } } }
            if (0..nq).any(|q| sim.qubit(crate::circuit::QubitId(q)) != 0) { anc += 1; }
            shots += 64;
        }
        let avg_t = sim.stats.toffoli_gates as f64 / shots as f64;
        eprintln!("LEAPFROG point_add: xbad={xbad} ybad={ybad} (y negated: {yneg})");
        eprintln!("LEAPFROG point_add: shots={shots} wrong={bad} phase_bad_shots={phase_shots} ancilla_bad_batches={anc} \
                   avgT={avg_t:.0} qubits={nq} score={:.0}", avg_t * nq as f64);
    }

    /// Single payload cell on parked pairs (LF_UT=1): P_S = lam b, P_T = lam t (t, b = +-1), the walk's sign
    /// (T + (-1)^s B = 2T), at tick LF_UT_T, direction LF_UT_DIR (fwd add_halve / rev double_add), with the live count
    /// padded to the real tick's (512 + 5t + 2W + 3, or LF_UT_ACTIVE). LF_UT_TIE=1 runs the tie-safe mode.
    /// LF_UT_MODE=rand: random P_T, P_S, s (control). Reports value and phase failures.
    #[test]
    fn leapfrog_tie_unit() {
        if std::env::var_os("LF_UT").is_none() { return; }
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        install_recipe();
        if let Ok(ov) = std::env::var("LF_OVR") { for kv in ov.split(';').filter(|k| !k.is_empty()) { let (k, v) = kv.split_once('=').unwrap(); std::env::set_var(k, v); } }
        let t: usize = std::env::var("LF_UT_T").ok().and_then(|v| v.parse().ok()).unwrap_or(120);
        let rev = std::env::var("LF_UT_DIR").is_ok_and(|v| v == "rev");
        let tie = std::env::var("LF_UT_TIE").is_ok_and(|v| v == "1");
        let rand = std::env::var("LF_UT_MODE").is_ok_and(|v| v == "rand");
        let w = steps()[t][0];
        let active: usize = std::env::var("LF_UT_ACTIVE").ok().and_then(|v| v.parse().ok()).unwrap_or(512 + 5 * t + 2 * w + 3);
        let mut c = Builder::new();
        let pt = c.alloc_qubits(N);
        let ps = c.alloc_qubits(N);
        let s = c.alloc_qubit();
        let tsg = c.alloc_qubit();
        let ssg = c.alloc_qubit();
        let pad = c.alloc_qubits(active.saturating_sub(c.active_qubits() as usize));
        let (fold, proxy) = proxy_fold(w, rev);
        if rev { c.x(s); }
        let pr = tie.then(|| { let q = c.alloc_qubit(); c.cx(s, q); c.cx(tsg, q); c.cx(ssg, q); q });
        cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || if rev {
            cells::double_add(&mut c, s, &ps, &pt, fold, proxy)
        } else {
            cells::add_halve(&mut c, s, &ps, &pt, fold, proxy)
        }));
        if let Some(q) = pr { c.cx(s, q); c.cx(tsg, q); c.cx(ssg, q); c.free(q); }
        if rev { c.x(s); }
        c.free_vec(&pad);
        c.declare_qubit_register(&pt);
        c.declare_qubit_register(&ps);
        c.declare_qubit_register(&[s]);
        c.declare_qubit_register(&[tsg]);
        c.declare_qubit_register(&[ssg]);
        let ops = c.take_ops();
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let p = modp();
        let mut h = sha3::Shake256::default();
        h.update(b"leapfrog-tie-unit");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        let mut seed = 0x2545_f491_4f6c_dd1du64 ^ (t as u64) << 32;
        let mut rnd = || { let mut v = U256::ZERO; for i in 0..4 { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; v |= U256::from(seed) << (64 * i); } v };
        let batches: usize = std::env::var("LF_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(16);
        let (mut bad, mut phb, mut shots) = (0usize, 0usize, 0usize);
        let half = (p + U256::from(1u8)) >> 1; // 1/2 mod p
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut exp = Vec::new();
            for shot in 0..64 {
                let lam = rnd().reduce_mod(p);
                let r = rnd();
                let (tneg, bneg) = (r.bit(0), r.bit(1));
                let fixed = std::env::var("LF_UT_LAM").ok().map(|l| {
                    let lam = U256::from_str_radix(l.trim_start_matches("0x"), 16).unwrap();
                    let m = |k: &str| { let v: i64 = std::env::var(k).unwrap().parse().unwrap();
                        let a = lam.mul_mod(U256::from(v.unsigned_abs()), p); if v < 0 { (p - a) % p } else { a } };
                    (m("LF_UT_PT"), m("LF_UT_PS"), std::env::var("LF_UT_SUB").is_ok_and(|v| v == "1"))
                });
                let (vt, vs, sub) = if let Some(f) = fixed { f } else if rand {
                    (rnd().reduce_mod(p), lam, r.bit(2))
                } else {
                    (if tneg { (p - lam) % p } else { lam }, if bneg { (p - lam) % p } else { lam }, tneg != bneg)
                };
                let sv = if sub { (p - vs) % p } else { vs };
                let want = if rev { vt.add_mod(vt, p).add_mod(p - sv, p) } else { vt.add_mod(sv, p).mul_mod(half, p) };
                sim.set_register(&regs[0], vt, shot);
                sim.set_register(&regs[1], vs, shot);
                sim.set_register(&regs[2], U256::from(sub as u8), shot);
                sim.set_register(&regs[3], U256::from(tneg as u8), shot);
                sim.set_register(&regs[4], U256::from(bneg as u8), shot);
                exp.push(want);
            }
            sim.apply_iter(ops.iter());
            for (shot, e) in exp.iter().enumerate() {
                let got = sim.get_register(&regs[0], shot);
                if got != *e { bad += 1; }
                if (sim.phase >> shot) & 1 == 1 { phb += 1; }
            }
            shots += 64;
        }
        eprintln!("TIEUNIT t={t} rev={rev} tie={tie} rand={rand} active={active} proxy={proxy} fold={fold} shots={shots} wrong={bad} phase_bad={phb}");
    }

    /// Bisect harness: fixed input (LF_X, LF_Y) in every shot; the multiply's fused walk-back stops after tick
    /// LF_N (inclusive) and the payload pair is printed for shot 0 (no cleanup; compare with y * R(n) mod p).
    #[test]
    fn leapfrog_trace() {
        let Ok(xs) = std::env::var("LF_X") else { return };
        super::super::install_skywalk_submission_recipe();
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let xv = U256::from_str_radix(xs.trim_start_matches("0x"), 16).unwrap();
        let yv = U256::from_str_radix(std::env::var("LF_Y").unwrap().trim_start_matches("0x"), 16).unwrap();
        let n: usize = std::env::var("LF_N").unwrap().parse().unwrap();
        let mut c = Builder::new();
        let x = c.alloc_qubits(N);
        let y = c.alloc_qubits(N);
        let r = seed(&mut c, &x);
        let mut wk = Walk { r, tape: Vec::new() };
        for t in 0..rounds() { fwd_tick(&mut c, &mut wk, t, None); }
        let (s0, s1) = (*wk.r[0].last().unwrap(), *wk.r[1].last().unwrap());
        let mut pay = [y.to_vec(), c.alloc_qubits(N)];
        cells::cond_negate(&mut c, s0, &pay[0]);
        c.cx_pairs(&pay[0], &pay[1]);
        let x01 = c.alloc_qubit();
        c.cx(s0, x01); c.cx(s1, x01);
        cells::cond_negate(&mut c, x01, &pay[1]);
        c.cx(s0, x01); c.cx(s1, x01);
        c.free(x01);
        for t in (n..rounds()).rev() { rev_tick(&mut c, &mut wk, t, Some(&mut pay)); }
        c.declare_qubit_register(&x);
        c.declare_qubit_register(&y);
        c.declare_qubit_register(&pay[1]);
        let ops = c.take_ops();
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"leapfrog-trace");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        sim.clear_for_shot();
        for shot in 0..64 { sim.set_register(&regs[0], xv, shot); sim.set_register(&regs[1], yv, shot); }
        sim.apply_iter(ops.iter());
        eprintln!("TRACE n={n} P0={:#x} P1={:#x} phase={:#x}", sim.get_register(&regs[1], 0), sim.get_register(&regs[2], 0), sim.phase);
    }

    /// Official-semantics failure count over several nonces: the env-free `build()` op stream, re-nonced with
    /// `apply_tail_nonce`, then eval_circuit's exact Fiat-Shamir shot derivation and 64-shot batch simulation.
    /// LF_NONCE0 (start), LF_NONCES (count). Prints distinct failing shots per nonce.
    #[test]
    fn leapfrog_official_lambda() {
        let Ok(n_nonces) = std::env::var("LF_NONCES") else { return };
        let n_nonces: u64 = n_nonces.parse().unwrap();
        let nonce0: u64 = std::env::var("LF_NONCE0").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let base = super::super::build();
        let hx = |h: &str| U256::from_str_radix(h, 16).unwrap();
        let curve = crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
            modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
            a: U256::from(0u8), b: U256::from(7u8),
            gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
            order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        };
        let mut tot = 0usize;
        for k in 0..n_nonces {
            let nonce = nonce0 + k;
            let ops = super::super::apply_tail_nonce(base.clone(), nonce);
            let (nq, nb, _, regs) = analyze_ops(ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"quantum_ecc-fiat-shamir-v2");
            h.update(&(ops.len() as u64).to_le_bytes());
            for op in &ops {
                h.update(&[op.kind as u8]);
                h.update(&op.q_control2.0.to_le_bytes());
                h.update(&op.q_control1.0.to_le_bytes());
                h.update(&op.q_target.0.to_le_bytes());
                h.update(&op.c_target.0.to_le_bytes());
                h.update(&op.c_condition.0.to_le_bytes());
                h.update(&op.r_target.0.to_le_bytes());
            }
            let mut xof = h.finalize_xof();
            let (mut tg, mut of, mut ex) = (Vec::new(), Vec::new(), Vec::new());
            for _ in 0..9024 {
                let mut rb = [[0u8; 32]; 2];
                sha3::digest::XofReader::read(&mut xof, &mut rb[0]);
                sha3::digest::XofReader::read(&mut xof, &mut rb[1]);
                let (k1, k2) = (U256::from_le_bytes(rb[0]), U256::from_le_bytes(rb[1]));
                let t = curve.mul(curve.gx, curve.gy, k1);
                let o = curve.mul(curve.gx, curve.gy, k2);
                if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) { continue; }
                ex.push(curve.add(t.0, t.1, o.0, o.1));
                tg.push(t);
                of.push(o);
            }
            let n = tg.len();
            let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
            let (mut fails, mut wrong, mut phase) = (0usize, 0usize, 0usize);
            for b in 0..(n + 63) / 64 {
                let bs = 64.min(n - b * 64);
                let mask: u64 = if bs == 64 { u64::MAX } else { (1u64 << bs) - 1 };
                sim.clear_for_shot();
                for s in 0..bs {
                    let i = b * 64 + s;
                    sim.set_register(&regs[0], tg[i].0, s);
                    sim.set_register(&regs[1], tg[i].1, s);
                    sim.set_register(&regs[2], of[i].0, s);
                    sim.set_register(&regs[3], of[i].1, s);
                }
                sim.apply_iter(ops.iter());
                let ph = sim.phase & mask;
                for s in 0..bs {
                    let i = b * 64 + s;
                    let bad = sim.get_register(&regs[0], s) != ex[i].0 || sim.get_register(&regs[1], s) != ex[i].1;
                    if bad { wrong += 1; }
                    if (ph >> s) & 1 == 1 { phase += 1; }
                    if bad || (ph >> s) & 1 == 1 { fails += 1; }
                }
            }
            tot += fails;
            eprintln!("OFFICIAL nonce={nonce} shots={n} failing={fails} (wrong {wrong}, phase {phase})");
        }
        eprintln!("OFFICIAL mean failing shots per draw = {:.2} over {n_nonces} nonces", tot as f64 / n_nonces as f64);
    }

    fn mprim_win() -> usize {
        std::env::var("LF_MPRIM_WIN").ok().and_then(|v| v.parse().ok()).unwrap_or(merged_win())
    }

    /// LF_MERGED primitives: kinds (LF_MPRIM_KINDS, default all) mfwd / mrev / mpair (merged forward, reverse,
    /// forward-then-reverse) and cfwd / crev (production cell + barrel equivalents, for cost). Inputs: x = S, y = T,
    /// c = (sg, k1, k2); residues mixed uniform / low / high / special values / T = +-S. LF_MPRIM_PAD idle qubits
    /// shrink the cap room (multi-chunk adder layouts); LF_CELLW picks the proxy width.
    #[test]
    fn leapfrog_merged_prims() {
        let Ok(kinds) = std::env::var("LF_MPRIM_KINDS") else { return };
        super::super::install_skywalk_submission_recipe();
        install_recipe();
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let batches: usize = std::env::var("LF_MPRIM_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(16);
        let pad: usize = std::env::var("LF_MPRIM_PAD").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
        let cw: usize = std::env::var("LF_CELLW").ok().and_then(|v| v.parse().ok()).unwrap_or(200);
        let mut tot_bad = 0;
        for kind in kinds.split(',') {
            let mut c = Builder::new();
            let x = c.alloc_qubits(N);
            let y = c.alloc_qubits(N);
            let ctl = c.alloc_qubits(4);
            let padq = c.alloc_qubits(pad);
            let (sg, k1, k2, neg) = (ctl[0], ctl[1], ctl[2], ctl[3]);
            // tie kinds (mt*/ct*): inputs y = +-x, the cells' tie predicate sign ^ [P_T == -P_S] on a live wire
            let tie = kind.starts_with("mt") || kind.starts_with("ct");
            let base_kind = if tie { format!("{}{}", &kind[..1], &kind[2..]) } else { kind.to_string() };
            let mulw = base_kind == "mrev" || base_kind == "crev";
            let (fold, proxy) = proxy_fold(cw, mulw);
            let pred = |c: &mut Builder, flip: bool| -> Option<QubitId> {
                tie.then(|| { let q = c.alloc_qubit(); c.cx(sg, q); c.cx(neg, q); if flip { c.x(q); } q })
            };
            let unpred = |c: &mut Builder, q: Option<QubitId>, flip: bool| {
                if let Some(q) = q { if flip { c.x(q); } c.cx(neg, q); c.cx(sg, q); c.free(q); }
            };
            let fwd = |c: &mut Builder| {
                let pr = pred(c, false);
                cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::with_bridge(proxy, false, || {
                    let split = if pr.is_none() { merged_split(c, proxy, false, false) } else { None };
                    eprintln!("MPRIM split fwd {split:?}");
                    merged_fwd(c, sg, &x, &y, k1, k2, proxy, split, mprim_win())
                })));
                unpred(c, pr, false);
            };
            let rev = |c: &mut Builder| {
                let pr = pred(c, true);
                cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::with_bridge(proxy, true, || merged_rev(c, sg, &x, &y, k1, k2, proxy, pr.is_none(), mprim_win()))));
                unpred(c, pr, true);
            };
            let a0 = c.active_qubits();
            match base_kind.as_str() {
                "mfwd" => fwd(&mut c),
                "mrev" => rev(&mut c),
                "mpair" => { fwd(&mut c); rev(&mut c); }
                "cfwd" => {
                    let pr = pred(&mut c, false);
                    cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::add_halve(&mut c, sg, &x, &y, fold, proxy)));
                    unpred(&mut c, pr, false);
                    cmod_barrel(&mut c, k1, k2, &y, false);
                }
                "crev" => {
                    cmod_barrel(&mut c, k1, k2, &y, true);
                    c.x(sg);
                    let pr = pred(&mut c, false);
                    cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::double_add(&mut c, sg, &x, &y, fold, proxy)));
                    unpred(&mut c, pr, false);
                    c.x(sg);
                }
                _ => panic!("kind {kind}"),
            }
            assert_eq!(c.active_qubits(), a0, "{kind}: live count changed");
            let extra_peak = c.peak_total() - a0;
            c.free_vec(&padq);
            c.declare_qubit_register(&x);
            c.declare_qubit_register(&y);
            c.declare_qubit_register(&ctl);
            let ops = c.take_ops();
            let (nq, nb, _, regs) = analyze_ops(ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"leapfrog-merged");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
            let mut seed = 0x5851_f42d_4c95_7f2du64;
            let mut r64 = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
            let p = modp();
            let fv = U256::from((1u64 << 32) + 977);
            let specials = [U256::ZERO, U256::from(1u8), fv - U256::from(1u8), fv, fv + U256::from(1u8), p - U256::from(1u8),
                            p - fv, (p - U256::from(1u8)) >> 1, (p + U256::from(1u8)) >> 1, U256::from(2u8), p - U256::from(2u8)];
            let (mut bad, mut phase_bad, mut anc_bad, mut shots) = (0usize, 0usize, 0usize, 0usize);
            for b in 0..batches {
                sim.clear_for_shot();
                let mut ins = Vec::new();
                for shot in 0..64 {
                    let mut pick = |mode: u64, r64: &mut dyn FnMut() -> u64| -> U256 {
                        match mode {
                            0..=5 => { let mut v = U256::ZERO; for i in 0..4 { v |= U256::from(r64()) << (64 * i); } v % p }
                            6 => U256::from(r64() >> 24),
                            7 => p - U256::from(1u8) - U256::from(r64() >> 24),
                            _ => specials[(r64() % specials.len() as u64) as usize],
                        }
                    };
                    let uni = std::env::var("LF_MPRIM_MODE").is_ok_and(|v| v == "uniform");
                    let mx = if uni { 0 } else { r64() % 9 };
                    let xv = pick(mx, &mut r64);
                    let my = if uni { 0 } else { r64() % 11 };
                    let yv = match my { 9 => xv, 10 => (p - xv) % p, m => pick(m, &mut r64) };
                    let cv = r64() & 7;
                    // tie kinds: y = x or y = -x, neg bit = [y == -x]
                    let (yv, cv) = if tie { if r64() & 1 == 1 { ((p - xv) % p, cv | 8) } else { (xv, cv) } } else { (yv, cv) };
                    // first batch: x, y special values (mixed mode only)
                    let (xv, yv) = if !tie && !uni && b == 0 && shot < 32 { (specials[shot % specials.len()], specials[(shot * 7 + 3) % specials.len()]) } else { (xv, yv) };
                    sim.set_register(&regs[0], xv, shot);
                    sim.set_register(&regs[1], yv, shot);
                    sim.set_register(&regs[2], U256::from(cv), shot);
                    ins.push((xv, yv, cv));
                }
                sim.apply_iter(ops.iter());
                for (shot, &(xv, yv, cv)) in ins.iter().enumerate() {
                    let (sgv, e) = (cv & 1 == 1, ((cv >> 1) & 1) + 2 * ((cv >> 2) & 1));
                    let k = 1 + e as usize;
                    let sx = if sgv { (p - xv) % p } else { xv };
                    let want = match base_kind.as_str() {
                        "mfwd" | "cfwd" => mulmod(yv.add_mod(sx, p), inv(U256::from(1u64 << k))),
                        "mrev" | "crev" => mulmod(yv, U256::from(1u64 << k)).add_mod((p - sx) % p, p),
                        _ => yv,
                    };
                    let (gx, gy, gc) = (sim.get_register(&regs[0], shot), sim.get_register(&regs[1], shot), sim.get_register(&regs[2], shot));
                    if gx != xv || gy != want || gc != U256::from(cv) {
                        bad += 1;
                        if bad <= 8 { eprintln!("MPRIM WRONG {kind} x={xv:#x} y={yv:#x} sg={sgv} e={e} got={gy:#x} want={want:#x} x_ok={} c_ok={}", gx == xv, gc == U256::from(cv)); }
                    }
                    if (sim.phase >> shot) & 1 == 1 {
                        phase_bad += 1;
                        if phase_bad <= 8 { eprintln!("MPRIM PHASE {kind} x={xv:#x} y={yv:#x} sg={sgv} e={e}"); }
                    }
                    if std::env::var_os("LF_MPRIM_DUMP").is_some() && (gy != want || (sim.phase >> shot) & 1 == 1) {
                        eprintln!("MSHOT {kind} {b} {shot} wrong={} phase={} x={xv:#x} y={yv:#x} sg={sgv} e={e}", gy != want, (sim.phase >> shot) & 1);
                    }
                }
                for reg in &regs { for qb in reg { if let QubitOrBit::Qubit(q) = *qb { *sim.qubit_mut(q) = 0; } } }
                if (0..nq).any(|q| sim.qubit(crate::circuit::QubitId(q)) != 0) { anc_bad += 1; }
                shots += 64;
            }
            let avg_t = sim.stats.toffoli_gates as f64 / shots as f64;
            eprintln!("MPRIM {kind}: cellw={cw} proxy={proxy} fold={fold} pad={pad} shots={shots} wrong={bad} phase_bad={phase_bad} anc_bad_batches={anc_bad} avgT={avg_t:.2} extra_peak={extra_peak}");
            tot_bad += bad + phase_bad + anc_bad;
        }
        assert_eq!(tot_bad, 0, "merged primitive failures");
    }

    /// Paired official-semantics comparison: the env-free `build()` op stream without (A) and with (B) LF_MERGED
    /// (via [`FORCE_MERGED`]), each re-nonced with `apply_tail_nonce`; the 9024 shots are derived from A's
    /// Fiat-Shamir hash and run through both streams. LF_PAIRED_NONCES (count), LF_NONCE0 (start).
    #[test]
    fn leapfrog_official_paired() {
        let Ok(n_nonces) = std::env::var("LF_PAIRED_NONCES") else { return };
        let n_nonces: u64 = n_nonces.parse().unwrap();
        let nonce0: u64 = std::env::var("LF_NONCE0").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        // LF_PAIRED_EXTRA="K=V,K=V": B = the recipe plus these entries (default: plus LF_MERGED=1)
        *FORCE_EXTRA.lock().unwrap() = std::env::var("LF_PAIRED_EXTRA").unwrap_or_default().split(',').filter(|e| !e.is_empty())
            .map(|e| { let (k, v) = e.split_once('=').expect("K=V"); (k.to_string(), v.to_string()) }).collect();
        FORCE_MERGED.store(false, std::sync::atomic::Ordering::Relaxed);
        let base_a = super::super::build();
        FORCE_MERGED.store(true, std::sync::atomic::Ordering::Relaxed);
        let base_b = super::super::build();
        FORCE_MERGED.store(false, std::sync::atomic::Ordering::Relaxed);
        let hx = |h: &str| U256::from_str_radix(h, 16).unwrap();
        let curve = crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
            modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
            a: U256::from(0u8), b: U256::from(7u8),
            gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
            order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        };
        let fs = |ops: &[crate::circuit::Op]| {
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
        };
        let (mut ta, mut tb, mut tw_both, mut tw_a, mut tw_b, mut tp_a, mut tp_b) = (0usize, 0usize, 0, 0, 0, 0, 0);
        let (mut tofa, mut tofb, mut nshots) = (0u64, 0u64, 0usize);
        for k in 0..n_nonces {
            let nonce = nonce0 + k;
            let ops_a = super::super::apply_tail_nonce(base_a.clone(), nonce);
            let ops_b = super::super::apply_tail_nonce(base_b.clone(), nonce);
            let mut xof = fs(&ops_a);
            let (mut tg, mut of, mut ex) = (Vec::new(), Vec::new(), Vec::new());
            for _ in 0..9024 {
                let mut rb = [[0u8; 32]; 2];
                sha3::digest::XofReader::read(&mut xof, &mut rb[0]);
                sha3::digest::XofReader::read(&mut xof, &mut rb[1]);
                let (k1, k2) = (U256::from_le_bytes(rb[0]), U256::from_le_bytes(rb[1]));
                let t = curve.mul(curve.gx, curve.gy, k1);
                let o = curve.mul(curve.gx, curve.gy, k2);
                if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) { continue; }
                ex.push(curve.add(t.0, t.1, o.0, o.1));
                tg.push(t);
                of.push(o);
            }
            let n = tg.len();
            let mut run = |ops: &[crate::circuit::Op], xof_tag: &[u8]| -> (Vec<bool>, Vec<bool>, u64) {
                let (nq, nb, _, regs) = analyze_ops(ops.iter());
                let mut h = sha3::Shake256::default();
                h.update(xof_tag);
                h.update(&nonce.to_le_bytes());
                let mut mx = h.finalize_xof();
                let mut sim = Simulator::new(nq as usize, nb as usize, &mut mx);
                let (mut wrong, mut phase) = (vec![false; n], vec![false; n]);
                for b in 0..(n + 63) / 64 {
                    let bs = 64.min(n - b * 64);
                    sim.clear_for_shot();
                    for s in 0..bs {
                        let i = b * 64 + s;
                        sim.set_register(&regs[0], tg[i].0, s);
                        sim.set_register(&regs[1], tg[i].1, s);
                        sim.set_register(&regs[2], of[i].0, s);
                        sim.set_register(&regs[3], of[i].1, s);
                    }
                    sim.apply_iter(ops.iter());
                    for s in 0..bs {
                        let i = b * 64 + s;
                        wrong[i] = sim.get_register(&regs[0], s) != ex[i].0 || sim.get_register(&regs[1], s) != ex[i].1;
                        phase[i] = (sim.phase >> s) & 1 == 1;
                    }
                }
                (wrong, phase, sim.stats.toffoli_gates)
            };
            let (wa, pa, xa) = run(&ops_a, b"paired-meas");
            let (wb, pb, xb) = run(&ops_b, b"paired-meas");
            let fa = (0..n).filter(|&i| wa[i] || pa[i]).count();
            let fb = (0..n).filter(|&i| wb[i] || pb[i]).count();
            let wboth = (0..n).filter(|&i| wa[i] && wb[i]).count();
            let wonly_a = (0..n).filter(|&i| wa[i] && !wb[i]).count();
            let wonly_b = (0..n).filter(|&i| !wa[i] && wb[i]).count();
            let (pa_n, pb_n) = (pa.iter().filter(|&&x| x).count(), pb.iter().filter(|&&x| x).count());
            eprintln!("PAIRED nonce={nonce} shots={n} failing A={fa} B={fb} | wrong both={wboth} onlyA={wonly_a} onlyB={wonly_b} | phase A={pa_n} B={pb_n} | avgT A={:.1} B={:.1}",
                xa as f64 / n as f64, xb as f64 / n as f64);
            for i in 0..n {
                if wb[i] && !wa[i] { eprintln!("PAIRED_ONLYB_WRONG nonce={nonce} i={i}"); }
            }
            ta += fa; tb += fb; tw_both += wboth; tw_a += wonly_a; tw_b += wonly_b; tp_a += pa_n; tp_b += pb_n;
            tofa += xa; tofb += xb; nshots += n;
        }
        eprintln!("PAIRED total over {n_nonces} nonces: failing A={ta} B={tb} (mean {:.2} / {:.2}) | wrong both={tw_both} onlyA={tw_a} onlyB={tw_b} | phase A={tp_a} B={tp_b} | avgT A={:.1} B={:.1}",
            ta as f64 / n_nonces as f64, tb as f64 / n_nonces as f64, tofa as f64 / nshots as f64, tofb as f64 / nshots as f64);
    }

    #[test]
    fn leapfrog_divide() {
        run("div", std::env::var("LF_DIV_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(16));
    }

    #[test]
    fn leapfrog_prims() {
        for k in ["tiesafe", "tiesafe_neg"] { std::panic::catch_unwind(|| run(k, 2)).ok(); }
    }

    #[test]
    fn leapfrog_bisect() {
        for n in [1usize, 2, 3, 4, 8, 16, 32, 64, 100, 133] {
            let k = format!("fr{n}");
            let k: &'static str = Box::leak(k.into_boxed_str());
            std::panic::catch_unwind(|| run(k, 2)).ok();
        }
    }

    #[test]
    fn leapfrog_divp1() {
        run("divp1", 1);
    }

    #[test]
    fn leapfrog_parts() {
        run("seed", 2);
        run("rails1", 2);
        run("rails", 2);
    }

    #[test]
    fn leapfrog_multiply() {
        run("mul", std::env::var("LF_DIV_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(4));
    }
}
#[cfg(test)]
mod prof {
    #[test]
    fn leapfrog_prim_costs() {
        for k in std::env::var("LF_KINDS").unwrap().split(',').map(|k| &*Box::leak(k.to_string().into_boxed_str())) {
            std::panic::catch_unwind(|| super::tests::run_pub(k, 2)).ok();
        }
    }
}
