//! B3b: the CARRY schedule of HEO(S,u), ported from B1's verified Python emitter
//! (`round2-build/B1/b1_emit.py` + `b1heo.py` + `b1g3.py`) onto the head's tree.
//!
//! Selected with `HEO_WALK=1 HEO_SCHEDULE=carry`. Research-only: nothing here runs
//! in the default build. Seed: the BASE rail seed `(d + p, d)` (B3b finding F-B3b-1:
//! the `pmd` seed breaks the C10 trit property, see `B3b/trit_seeds.py`).
//!
//! DIV leg (`y <- y / x`): G3 rail seed (tick 0 direct) | fused forward t < r2d:
//! rail tick (servo split, I-H deferral) -> pack -> cell t (cell 0 skipped; G1b at
//! t = 1) -> route | rails-only forward | terminal loan | trailing batch of cells
//! (C10 groups unpacked/repacked, LIFO) | endpoint `Del ^= Sig` | unloan | P2
//! unsplit reverse applying the I-H phases | G3 unseed.
//!
//! MUL leg (`y <- y * x`): G3 seed | P4 rails-only forward | loan | `Del = Sig` |
//! trailing batch of inverse cells R-1..r2m | unloan | rails-only reverse |
//! fused walkback r2m-1..r1m (split repairs: exact or windowed) | head batch of
//! inverse cells r1m-1..1 (G1b inverse at t = 1) | `Del` freed | rails-only
//! reverse r1m-1..0 | G3 unseed.
//!
//! Cells: the head's replay cells (every I77 lever) at the proxy round of the rail
//! width. Degenerate zone t < `HEO_ZONE` (B1 F1/F2, B2 section 3): division cells
//! run tie-safe (sign-seeded compares, B3a Fix A); multiply cells run B1's
//! `double_add_nc` (every degenerate inverse returns the representative p).
use super::super::builder::Builder;
use super::super::compare::erase_with_compare;
use super::super::const_arith::{add_const, cadd_const_trunc, sub_const};
use super::super::modular::f;
use super::super::pingpong::{fold_step, unwind_fold_step};
use super::super::{N, SECP256K1_P};
use super::{config, fredkin, h7, resize, restore_layout, truthy, HeoConfig, Rails};
use crate::circuit::{BitId, QubitId};
use alloy_primitives::U256;
use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Configuration Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SplitMode {
    /// Boundary carries HMR'd as soon as consumed; the phase is repaired by the
    /// mirror pass's unsplit ripple (I-H).
    Defer,
    /// Boundaries kept, erased top-down by exact whole-chunk compares.
    Exact,
    /// Windowed repair (L-SPLIT): exact on a leading chunk <= K, else top-K window.
    Approx,
    /// Unsplit, applying deferred phases (the mirror pass).
    Apply,
}

pub struct CarryCfg {
    pub r2d: usize,
    pub r2m: usize,
    pub r1m: usize,
    pub split_mul: SplitMode,
    pub split_k: usize,
    pub zone: usize,
    pub g3: bool,
    pub g1b: bool,
    pub lifo: bool,
    /// Seed the multiply-zone nc cell's compares like the head (CMP_SEED_MUL).
    pub nc_seed: bool,
    /// Split mode of the forward rail ticks (default Defer = I-H).
    pub fwd_split: SplitMode,
    /// Park R2[0] between ticks: at every tick boundary exactly one rail is odd,
    /// so R2[0] = NOT R1[0] (F-B3b lever L-PAR, Clifford only).
    pub park_parity: bool,
    /// B4: H0 start frame `(h, h - p)` instead of G3 (`HEO_CARRY_SEED=h0`). Tick-0 pseudo-letter
    /// `(o_{-1}, 0)` with `o_{-1} = NOT h[255]`; payload `(0, (-1)^{o_{-1}} N)` with cell 1 in
    /// closed form; the walk parks at `(0, +-1)` so the loan keeps R2's sign (B4 FB4-1).
    pub h0: bool,
    /// B4: FD fused start `((d - b p)/2, d - (1-b) p + X)` (`HEO_CARRY_SEED=fd`). Tick-0 pseudo-letter
    /// `(o_0, s_0)` with `o_0 = NOT(X_sign XOR X[254])`, `s_0 = Y_sign AND NOT o_0`; 6 payload classes; the
    /// multiply leg carries X's sign (the parity b) on one extra wire (B4 FB4-2, route i).
    pub fd: bool,
    /// RB-1: L-T0 on the DIVISION leg (FD only, `HEO_LT0=1`): letter 0 leaves the codec. o_0 is held on one raw
    /// wire from the seed to the unseed, s_0 is never computed (the div payload seed reads the rails), and the
    /// div tape codes letters 1..R-1 with its groups offset by one letter. The multiply leg is unchanged
    /// (it needs the 6-valued class at its head batch's end, INTEGRATE I-2).
    pub lt0: bool,
    /// RB-1 (`HEO_BW=inv`, FD only): drop the FB4-2 b wire from the multiply leg's forward, trailing batch and
    /// fused walkback. FINDING FB-RB1-1: in the orientation frame the sign of the LARGER-magnitude rail,
    /// a = (o_t ? sign R2 : sign R1), is invariant over the whole walk, and a = (o_0 ? Y_sign : X_sign) at the
    /// post-seed state, so b = X_sign = a ^ o_0. The head batch recomputes a from the rails' sign wires and
    /// o_{r1m-1} (1 Toffoli) at its first step and XORs o_0 in at its last; the wire is then b as before.
    pub bw_inv: bool,
    /// RB-1 (`HEO_LT0_MUL=1`, needs `HEO_BW=inv`): L-T0 on the MULTIPLY leg too. The class (X_sign, Y_sign, o_0)
    /// is rebuilt at the head batch from the frame invariant: a = larger-rail sign (constant) and the smaller-rail
    /// sign b_0 = b_{r1m-1} ^ f_1 ^ .. ^ f_{r1m-1} (the f bits are XORed in while each letter is raw in the head
    /// batch); (X_sign, Y_sign) = swap^{o_0}(a, b_0). Both wires ride rails-rev2 (not binding) and are cleared by
    /// CX from the post-seed rail signs. o_0 is a raw wire; s_0 is never computed.
    pub lt0_mul: bool,
    /// RB-1 (`HEO_LOAN_BOTH=1`): FINDING FB-RB1-3. The walk FIRST parks at (+-1, 0) (o = 0) and reaches (0, +-1)
    /// one tick later; the terminal loan assumed (0, +-1), so every walk whose first park is exactly at tick R
    /// failed (9 of 48 x-bad probe lanes on front07; the walk model counted them as parked). The loan now swaps
    /// the (narrow) rails on NOT o_{R-1} first, and the unloan swaps them back: both park states are accepted.
    pub loan_both: bool,
    /// INTEGRATE-R3 (`HEO_RAIL_MAX=257`, FD or H0 only): R4C-1. FD/H0 post-seed rails satisfy |X|, |Y| < p and the
    /// reducing add never grows a magnitude, so every rail value fits 257 bits two's complement; envelope widths
    /// above that are dead wires (ticks 1-13, the Q1175-1177 binders). Only the RAIL widths are clamped (`wpost`,
    /// the forward / reverse tick widths); the cells keep their proxy (`cell_proxy_w`). Default: no clamp.
    pub rail_max: usize,
    /// INTEGRATE-R3 (`HEO_PROXY_ENVELOPE=path`): fix for FB-RB1-4. The cells pick their band tables through
    /// `h7::proxy_round(esw[t])`; with this knob they read esw[t] from the given fixed envelope instead of the row's,
    /// so envelope sells / clamps no longer move the cells' windows. Default: the row's own esw.
    pub proxy_esw: Option<Vec<usize>>,
    /// B6 (`HEO_DB_SKIP=1`, D-B): skip the div batch's terminal route (t = R-1). On every passing shot the
    /// payload pair is the duplicate (q, q) there (the endpoint's `cx_pairs` + free proves it), so the swap is
    /// the identity: -256 CCX, lambda-exact. Default off.
    pub db_skip: bool,
    /// B6 (`HEO_LR1=1`, D-D L-R1): after each forward tick (t < R-1) and before each mul fused walkback cell,
    /// trim R1 to min(wpost(t), rw(esw[t]) - 1). R1 = X >> 1 is a sign extension of an (esw-1)-bit value by
    /// construction, so the trim (CX + free of a sign copy) is exact on every shot; Clifford only. Default off.
    pub lr1: bool,
    /// B6 (`HEO_DB_SKIP2=1`, lambda-priced, D-B section 4): also skip the div batch route at t = R-2. It is the identity
    /// on every passing walk except those that park exactly at tick R with s_{R-2} = 1. Default off.
    pub db_skip2: bool,
    /// B6 (`HEO_MB_SKIP2=1`, lambda-priced): skip the mul batch route at t = R-2 (the mirror of `db_skip2`; the route at
    /// t = R-1 acts on the fresh copy and is already removed by the product simplifier). Default off.
    pub mb_skip2: bool,
    /// B6 (`HEO_CELL_WINDOWS=tsv`, R5-A): per-(leg, t) shifts (dB, dF, dX) of the cells' chunk-boundary compare,
    /// flag compare and fold window. dX adds to fw; dB/dF shift only the compare widths (thread-local in
    /// pingpong.rs), never `chunk_layout`. Default: none (byte-identical).
    pub cell_windows: Option<std::collections::HashMap<(bool, usize), (isize, isize, isize)>>,
    /// B7 (`HEO_DIV_LIFO_N=n`, Effort 8b V-P6): the div batch leaves its last n+1 groups raw (the walkback unpacks
    /// them first). Default 0 = the base LIFO (last group only).
    pub div_lifo_n: usize,
    /// B7 (`HEO_MULB_LIFO_N=n`, V-P7): the mul batch does not repack groups gid(r2m)..gid(r2m)+n-1. Default 0.
    pub mulb_lifo_n: usize,
    /// B7 (`HEO_HEAD_LIFO_N=n`, V-P5 n=1 / V-P8 n=2): the mul head batch does not repack groups 0..n-1, and with
    /// n >= 1 skips the gtop repack (railsrev2 unpacks it at once). Default 0.
    pub head_lifo_n: usize,
    /// B7 (`HEO_DIV_PARTIAL=1`, V-P9): the div batch unpacks only what letter t needs (`ensure_raw`). Default off.
    pub div_partial: bool,
    /// B7 (`HEO_MULB_PARTIAL=1`, V-P9): the mul batch likewise. Default off. (The head-batch partial is the 8b trap.)
    pub mulb_partial: bool,
    /// B7 (`HEO_DIV_EARLY_P3=1`, Effort 7 LAZY_BATCH div part): pack3 a div-batch group right after its 3rd letter's
    /// route, so its last two cells run with one more free wire. Same gates. Default off.
    pub div_early_p3: bool,
    /// B7 (`HEO_O0_DEC=1`, Effort 7 O0, needs L-T0): div forward tick 1 erases the raw o_0 wire (o_0 = o_1 ^ c_1,
    /// c_1 = r2[1]^r2[2]^e2[0]^e2[1]^kp ^ r2[1]e2[0] from the FD relation; HMR + CZ repair, 0 T); the walkback's
    /// tick 1 rebuilds it (1 CCX). Default off.
    pub o0_dec: bool,
    /// B7 (`HEO_O0M=1`, Effort 7 O0-M, needs L-T0 on the mul leg): the same forward erase on the mul leg; the head-batch
    /// end rebuilds o_0 = NOT A AND NOT(Del[1] ^ Sig[0]) (1 CCX) before the class inverse. railsrev2 stays standard.
    pub o0m: bool,
    /// B7 (`HEO_RAIL_BRIDGE=x`, Effort 10 S-C): per-tick min rule for rail splits. 0 = off.
    pub rail_bridge: f64,
    /// B7 (`HEO_RAIL_BRIDGE_EXACT=1`): the rule also covers Exact-mode splits.
    pub rail_bridge_exact: bool,
}

/// B6: parse an R5-A window table: lines `leg t esw proxy pw pi dB dF dX` (leg = div | mul; '#' comments).
fn parse_cell_windows(text: &str) -> std::collections::HashMap<(bool, usize), (isize, isize, isize)> {
    let mut m = std::collections::HashMap::new();
    for line in text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let f: Vec<&str> = line.split_whitespace().collect();
        assert!(f.len() >= 9, "HEO_CELL_WINDOWS: bad line {line:?}");
        let mul = match f[0] { "div" => false, "mul" => true, o => panic!("HEO_CELL_WINDOWS leg {o:?}") };
        let t: usize = f[1].parse().expect("HEO_CELL_WINDOWS t");
        let p = |i: usize| f[i].parse::<isize>().unwrap_or_else(|_| panic!("HEO_CELL_WINDOWS field {i} in {line:?}"));
        assert!(m.insert((mul, t), (p(6), p(7), p(8))).is_none(), "HEO_CELL_WINDOWS duplicate {line:?}");
    }
    m
}

/// B6: the (dB, dF, dX) shift of cell (leg, t) under `HEO_CELL_WINDOWS` ((0, 0, 0) when absent).
fn cell_shift(mul: bool, t: usize) -> (isize, isize, isize) {
    carry_cfg().cell_windows.as_ref().and_then(|m| m.get(&(mul, t)).copied()).unwrap_or((0, 0, 0))
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|s| s.trim().parse().ok()).unwrap_or(default)
}
fn env_bool(name: &str, default: bool) -> bool {
    match std::env::var(name) {
        Ok(v) => !matches!(v.trim().to_ascii_lowercase().as_str(), "" | "0" | "false" | "no" | "off"),
        Err(_) => default,
    }
}

pub fn carry_cfg() -> &'static CarryCfg {
    static CFG: OnceLock<CarryCfg> = OnceLock::new();
    CFG.get_or_init(|| {
        let split_mul = match std::env::var("HEO_SPLIT_MUL").unwrap_or_else(|_| "approx".into()).as_str() {
            "approx" => SplitMode::Approx,
            "exact" => SplitMode::Exact,
            other => panic!("HEO_SPLIT_MUL {other:?}: approx | exact"),
        };
        let c = CarryCfg {
            r2d: env_usize("HEO_R2D", 365),
            r2m: env_usize("HEO_R2M", 360),
            r1m: env_usize("HEO_R1M", 190),
            split_mul,
            split_k: env_usize("HEO_SPLIT_K", 24),
            zone: env_usize("HEO_ZONE", 22),
            g3: env_bool("HEO_G3", true),
            g1b: env_bool("HEO_G1B", true),
            lifo: env_bool("HEO_LIFO", true),
            nc_seed: env_bool("HEO_NC_SEED", true),
            fwd_split: match std::env::var("HEO_FWD_SPLIT").unwrap_or_else(|_| "defer".into()).as_str() {
                "defer" => SplitMode::Defer,
                "exact" => SplitMode::Exact,
                "approx" => SplitMode::Approx,
                other => panic!("HEO_FWD_SPLIT {other:?}"),
            },
            park_parity: env_bool("HEO_PARK_PARITY", true),
            h0: match std::env::var("HEO_CARRY_SEED").unwrap_or_else(|_| "g3".into()).as_str() {
                "g3" | "fd" => false,
                "h0" => true,
                other => panic!("HEO_CARRY_SEED {other:?}: g3 | h0 | fd"),
            },
            fd: std::env::var("HEO_CARRY_SEED").is_ok_and(|v| v == "fd"),
            lt0: std::env::var("HEO_CARRY_SEED").is_ok_and(|v| v == "fd") && env_bool("HEO_LT0", false),
            bw_inv: std::env::var("HEO_CARRY_SEED").is_ok_and(|v| v == "fd")
                && std::env::var("HEO_BW").is_ok_and(|v| v == "inv"),
            lt0_mul: std::env::var("HEO_CARRY_SEED").is_ok_and(|v| v == "fd")
                && std::env::var("HEO_BW").is_ok_and(|v| v == "inv") && env_bool("HEO_LT0_MUL", false),
            loan_both: env_bool("HEO_LOAN_BOTH", false),
            rail_max: env_usize("HEO_RAIL_MAX", usize::MAX),
            proxy_esw: std::env::var("HEO_PROXY_ENVELOPE").ok().filter(|p| !p.trim().is_empty()).map(|p| {
                let text = include_str!("skywalk_data/env_front07_R396_clamp.txt").to_owned();
                super::parse_envelope(&text).0
            }),
            db_skip: env_bool("HEO_DB_SKIP", false),
            lr1: env_bool("HEO_LR1", false),
            db_skip2: env_bool("HEO_DB_SKIP2", false),
            mb_skip2: env_bool("HEO_MB_SKIP2", false),
            cell_windows: std::env::var("HEO_CELL_WINDOWS").ok().filter(|p| !p.trim().is_empty()).map(|p| {
                let text = include_str!("skywalk_data/windows_full_safe_mulB64.tsv").to_owned();
                parse_cell_windows(&text)
            }),
            div_lifo_n: env_usize("HEO_DIV_LIFO_N", 0),
            mulb_lifo_n: env_usize("HEO_MULB_LIFO_N", 0),
            head_lifo_n: env_usize("HEO_HEAD_LIFO_N", 0),
            div_partial: env_bool("HEO_DIV_PARTIAL", false),
            mulb_partial: env_bool("HEO_MULB_PARTIAL", false),
            div_early_p3: env_bool("HEO_DIV_EARLY_P3", false),
            o0_dec: env_bool("HEO_O0_DEC", false),
            o0m: env_bool("HEO_O0M", false),
            rail_bridge: std::env::var("HEO_RAIL_BRIDGE").ok().and_then(|s| s.trim().parse::<f64>().ok()).unwrap_or(0.0),
            rail_bridge_exact: env_bool("HEO_RAIL_BRIDGE_EXACT", false),
        };
        if c.div_lifo_n + c.mulb_lifo_n + c.head_lifo_n > 0 || c.div_partial || c.mulb_partial || c.div_early_p3
            || c.o0_dec || c.o0m || c.rail_bridge > 0.0 {
            eprintln!("HEO_CARRY_B7 div_lifo_n={} mulb_lifo_n={} head_lifo_n={} div_partial={} mulb_partial={} div_early_p3={} \
                       o0_dec={} o0m={} rail_bridge={} rail_bridge_exact={}", c.div_lifo_n, c.mulb_lifo_n, c.head_lifo_n,
                c.div_partial, c.mulb_partial, c.div_early_p3, c.o0_dec, c.o0m, c.rail_bridge, c.rail_bridge_exact);
        }
        assert!(!c.o0_dec || c.lt0, "HEO_O0_DEC needs HEO_CARRY_SEED=fd HEO_LT0=1");
        assert!(!c.o0m || c.lt0_mul, "HEO_O0M needs HEO_CARRY_SEED=fd HEO_BW=inv HEO_LT0_MUL=1");
        if c.db_skip || c.lr1 || c.cell_windows.is_some() || c.db_skip2 || c.mb_skip2 {
            eprintln!("HEO_CARRY_B6 db_skip={} db_skip2={} mb_skip2={} lr1={} cell_windows={}", c.db_skip, c.db_skip2, c.mb_skip2, c.lr1,
                c.cell_windows.as_ref().map_or("none".to_string(), |m| format!("{} rows", m.len())));
        }
        assert!(c.rail_max == usize::MAX || ((c.fd || c.h0) && c.rail_max > N),
            "HEO_RAIL_MAX needs HEO_CARRY_SEED=fd|h0 and a width >= N+1 (R4C-1)");
        if c.rail_max != usize::MAX || c.proxy_esw.is_some() {
            eprintln!("HEO_CARRY_R3 rail_max={} proxy={}", c.rail_max,
                std::env::var("HEO_PROXY_ENVELOPE").unwrap_or_else(|_| "row".into()));
        }
        eprintln!("HEO_CARRY r2d={} r2m={} r1m={} split_mul={:?} K={} zone={} g3={} g1b={} lifo={} h0={} fd={}{}",
            c.r2d, c.r2m, c.r1m, c.split_mul, c.split_k, c.zone, c.g3, c.g1b, c.lifo, c.h0, c.fd,
            format!("{}{}{}{}", if c.lt0 { " lt0=div" } else { "" }, if c.bw_inv { " bw=inv" } else { "" },
                    if c.lt0_mul { " lt0=mul" } else { "" }, if c.loan_both { " loan=both" } else { "" }));
        c
    })
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Ledger (observes the op stream only) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

#[derive(Default)]
pub struct Ledger {
    /// component -> (native, expected)
    pub comp: BTreeMap<&'static str, (usize, f64)>,
    /// (peak, label, t)
    pub binders: Vec<(u32, &'static str, usize)>,
    pub splits: BTreeMap<&'static str, usize>,
    pub mirror_over: usize,
    pub mirror_over_max: usize,
    pub infeasible: usize,
}

pub static LEDGER: Mutex<Option<Ledger>> = Mutex::new(None);

/// `(op index at the END of a booked step, label, t)` under `HEO_TICK_TRACE` (probe attribution).
pub static CHECKPOINTS: Mutex<Vec<(usize, &'static str, usize)>> = Mutex::new(Vec::new());
fn tracing() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| truthy("HEO_TICK_TRACE"))
}

fn ledger<R>(f: impl FnOnce(&mut Ledger) -> R) -> R {
    let mut g = LEDGER.lock().unwrap();
    f(g.get_or_insert_with(Ledger::default))
}

/// Run `body`, booking its Toffoli under `comp` and its window peak under `(label, t)`.
thread_local! {
    /// Open `book` frames: (children native, children expected, children max peak).
    static BOOK_STACK: std::cell::RefCell<Vec<(usize, f64, u32)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Run `body`, booking its OWN Toffoli (nested books excluded) under `comp` and its
/// window peak (nested included) under `(label, t)`.
fn book<R>(c: &mut Builder, comp: &'static str, label: &'static str, t: usize, body: impl FnOnce(&mut Builder) -> R) -> R {
    let before = c.report_totals();
    let skywalk_before = (c.op_count(), c.active_qubits(), c.phase_name());
    let p0 = c.take_win_peak();
    BOOK_STACK.with(|s| {
        let mut s = s.borrow_mut();
        if let Some(top) = s.last_mut() {
            top.2 = top.2.max(p0);
        }
        s.push((0, 0.0, 0));
    });
    let out = body(c);
    if tracing() {
        CHECKPOINTS.lock().unwrap().push((c.op_count(), label, t));
    }
    let p1 = c.take_win_peak();
    let (cn, ce, cp) = BOOK_STACK.with(|s| s.borrow_mut().pop().unwrap());
    let peak = p1.max(cp);
    let after = c.report_totals();
    let (dn, de) = match (before, after) {
        (Some(b), Some(a)) => (a.0 - b.0, a.1 - b.1),
        _ => (0, 0.0),
    };
    if env_bool("SKYWALK_SITE_TRACE", false) {
        eprintln!("SKYWALK_SITE\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.1}\t{}\t{:.1}",
            skywalk_before.2, comp, label, t, skywalk_before.0, c.op_count(),
            skywalk_before.1, c.active_qubits(), peak,
            h7::cap().saturating_sub(skywalk_before.1 as usize),
            h7::cap().saturating_sub(c.active_qubits() as usize), dn, de, dn - cn, de - ce);
    }
    ledger(|l| {
        let e = l.comp.entry(comp).or_insert((0, 0.0));
        e.0 += dn - cn;
        e.1 += de - ce;
        l.binders.push((peak, label, t));
    });
    BOOK_STACK.with(|s| {
        if let Some(top) = s.borrow_mut().last_mut() {
            top.0 += dn;
            top.1 += de;
            top.2 = top.2.max(peak);
        }
    });
    out
}

pub fn print_ledger() {
    let mut g = LEDGER.lock().unwrap();
    let Some(l) = g.as_mut() else { return };
    let (mut tn, mut te) = (0usize, 0.0f64);
    for (k, (n, e)) in &l.comp {
        eprintln!("HEO_LEDGER {k:<22} native={n:>8} expected={e:>11.1}");
        tn += n;
        te += e;
    }
    eprintln!("HEO_LEDGER {:<22} native={tn:>8} expected={te:>11.1}", "TOTAL(heo)");
    l.binders.sort_by(|a, b| b.0.cmp(&a.0));
    for (p, label, t) in l.binders.iter().take(12) {
        eprintln!("HEO_BINDER peak={p} {label} t={t}");
    }
    for (k, v) in &l.splits {
        eprintln!("HEO_SPLITS {k} {v}");
    }
    eprintln!("HEO_MIRROR over={} max_over={} infeasible={}", l.mirror_over, l.mirror_over_max, l.infeasible);
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Exact ripple with deferred phases (B1 b1arith.ripple_add) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

fn carry_step(c: &mut Builder, a: QubitId, b: QubitId, prev: Option<QubitId>, carry: QubitId) {
    if let Some(p) = prev {
        c.cx(p, a);
        c.cx(p, b);
    }
    let reused=REVERSE_LOW.with(|r| {let mut v=r.borrow_mut();if v.as_ref().is_some_and(|&(aa,bb,p,q)| (a,b,prev,carry)==(aa,bb,Some(p),q)){v.take();true}else{false}});
    if !reused {c.ccx(a, b, carry);} else {eprintln!("REVERSE_CARRY_REUSE carry={} a={} b={}",carry.0,a.0,b.0);}
    if let Some(p) = prev { c.cx(p, carry); }
}

// v025 A-2 (two-tick shared product, ported from c1-001/two-tick-001): the tick's first
// carry `u = (h0 XOR p1) AND (x2[0] XOR p1)` (undressed) is retained instead of HMR-erased when
// the next tick can turn it into the codec's first nonlinear predicate. The unwind keeps the
// original erasure and phase schedule everywhere else.
thread_local! {
    static SHARED_LOW: std::cell::RefCell<Option<(QubitId, QubitId, QubitId, Option<QubitId>)>> = const { std::cell::RefCell::new(None) };
}
fn shared_low_start(a: QubitId, b: QubitId, p: QubitId) {
    SHARED_LOW.with(|x| { assert!(x.borrow().is_none()); *x.borrow_mut() = Some((a, b, p, None)); });
}
fn shared_low_finish() -> QubitId {
    SHARED_LOW.with(|x| x.borrow_mut().take().unwrap().3.expect("shared low carry: first carry not encountered"))
}

fn unwind_carry_step(c: &mut Builder, a: QubitId, b: QubitId, prev: Option<QubitId>, carry: QubitId) {
    let keep = SHARED_LOW.with(|x| {
        let mut v = x.borrow_mut();
        if let Some((aa, bb, pp, out)) = v.as_mut() {
            if a == *aa && b == *bb && prev == Some(*pp) { assert!(out.is_none()); *out = Some(carry); return true; }
        }
        false
    });
    if keep {
        let p = prev.unwrap(); c.cx(p, carry); c.cx(p, a); c.cx(a, b); return;
    }
    if let Some(p) = prev {
        c.cx(p, carry);
    }
    let m = c.alloc_bit();
    c.hmr(carry, m);
    c.cz_if(a, b, m);
    c.free_bit(m);
    c.free(carry);
    if let Some(p) = prev {
        c.cx(p, a);
    }
    c.cx(a, b);
}

fn terminal_step(c: &mut Builder, a: &[QubitId], b: &[QubitId], prev: Option<QubitId>) {
    let n = b.len();
    let i = n - 2;
    if let Some(p) = prev {
        c.cx(p, a[i]);
        c.cx(p, b[i]);
    }
    c.ccx(a[i], b[i], b[n - 1]);
    if let Some(p) = prev {
        c.cx(p, b[n - 1]);
    }
    // K3b rail source-top loan: the addend's top wire may be ALIASED to a[n-2] (its value
    // copy; the real top wire is lent out). Read the top bit from a[n-2] once it is restored.
    let alias = a[n - 1] == a[i];
    if !alias {
        c.cx(a[n - 1], b[n - 1]);
    }
    if let Some(p) = prev {
        c.cx(p, a[i]);
    }
    if alias {
        c.cx(a[i], b[n - 1]);
    }
    c.cx(a[i], b[i]);
}

/// `b += a + cin`. Vented to `cout` when given (`w - 1` owned carries), else wrapped
/// (`w - 2` owned). `deferred` holds `(i, m)`: `Z^m` on the carry out of bit `i`
/// while it still holds the arithmetic carry (I-H mirror repair).
fn rail_ripple(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>, cout: Option<QubitId>,
               deferred: &mut Vec<(usize, BitId)>) {
    let w = b.len();
    assert!(w >= 1 && a.len() == w);
    let vented = cout.is_some();
    let owned = if vented { w - 1 } else { w.saturating_sub(2) };
    let mut carries = c.alloc_qubits(owned);
    if let Some(o) = cout {
        carries.push(o);
    }
    let prev = |i: usize, cs: &[QubitId]| if i == 0 { cin } else { Some(cs[i - 1]) };
    for i in 0..carries.len() {
        carry_step(c, a[i], b[i], prev(i, &carries), carries[i]);
    }
    if vented || w == 1 {
        let top = w - 1;
        if let Some(p) = prev(top, &carries) {
            c.cx(p, if vented { a[top] } else { b[top] });
        }
        c.cx(a[top], b[top]);
    } else {
        terminal_step(c, a, b, prev(w - 2, &carries));
    }
    for i in (0..owned).rev() {
        if let Some(pos) = deferred.iter().position(|&(k, _)| k == i) {
            let (_, m) = deferred.remove(pos);
            c.z_if(carries[i], m);
            c.free_bit(m);
        }
        unwind_carry_step(c, a[i], b[i], prev(i, &carries), carries[i]);
    }
}

/// B1 `split_sizes`: chunk widths for a wrapped `w`-bit add under `room` free wires
/// (the carry-in is already live). `Ok(None)` = no split needed; `Err` = infeasible.
fn split_sizes(w: usize, room: usize, exact: bool) -> Result<Option<Vec<usize>>, ()> {
    if w <= room + 2 {
        return Ok(None);
    }
    for k in 1..64usize {
        let caps: Vec<isize> = if exact {
            let mut v: Vec<isize> = (0..k).map(|j| room as isize - j as isize).collect();
            v.push(room as isize - k as isize + 2);
            v
        } else {
            let mut v = vec![room as isize];
            v.extend(std::iter::repeat_n(room as isize - 1, k - 1));
            v.push(room as isize + 1);
            v
        };
        if *caps.iter().min().unwrap() < 2 {
            return Err(());
        }
        let sum: isize = caps.iter().sum();
        if sum >= w as isize {
            let mut sizes: Vec<usize> = caps.iter().map(|&x| x as usize).collect();
            let mut excess = sum as usize - w;
            for s in sizes.iter_mut().take(k) {
                let cut = excess.min(*s - 2);
                *s -= cut;
                excess -= cut;
            }
            assert_eq!(excess, 0);
            return Ok(Some(sizes));
        }
    }
    Err(())
}

/// K3b (`K3B_RAIL_LOAN=1`): the head's I76 SOURCE-TOP loan, re-wired into HEO's rail add. When the addend's top
/// wire is an exact value copy of the wire below (`top_copy`), clear it by CX, lend it to the pool (the split
/// planner sees one more wire of room), read the top bit from `a[w-2]` in the terminal step, and restore the
/// copy after the add. Clifford only; exact on every shot.
#[allow(clippy::too_many_arguments)]
fn rail_add(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: QubitId, mode: SplitMode,
            tick_def: &mut Vec<(usize, BitId)>, label: &'static str, top_copy: bool) {
    static ON: OnceLock<bool> = OnceLock::new();
    let on = *ON.get_or_init(|| env_bool("K3B_RAIL_LOAN", false));
    let w = b.len();
    if !(on && top_copy && w >= 3) {
        return rail_add_inner(c, a, b, cin, mode, tick_def, label);
    }
    let (q, s) = (a[w - 1], a[w - 2]);
    c.cx(s, q);
    c.release_clean(q);
    let mut al = a.to_vec();
    al[w - 1] = s;
    rail_add_inner(c, &al, b, cin, mode, tick_def, label);
    c.reacquire(q);
    c.cx(s, q);
}

/// Servoed rail add `b += a + cin` (wrapped). See [`SplitMode`].
fn rail_add_inner(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: QubitId, mode: SplitMode,
            tick_def: &mut Vec<(usize, BitId)>, label: &'static str) {
    let w = b.len();
    let room = h7::cap().saturating_sub(c.active_qubits() as usize);
    if env_bool("K3B_RAIL_TRACE", false) {
        eprintln!("K3B_RAIL {label} w={w} room={room} mode={mode:?} def={}", tick_def.len());
    }
    if !tick_def.is_empty() || mode == SplitMode::Apply {
        if w > room + 2 {
            ledger(|l| {
                l.mirror_over += 1;
                l.mirror_over_max = l.mirror_over_max.max(w - 2 - room);
            });
        }
        rail_ripple(c, a, b, Some(cin), None, tick_def);
        assert!(tick_def.is_empty(), "deferred phase did not name an owned carry");
        return;
    }
    let sizes = match split_sizes(w, room, mode == SplitMode::Exact) {
        Ok(None) => {
            rail_ripple(c, a, b, Some(cin), None, &mut Vec::new());
            return;
        }
        Err(()) => {
            ledger(|l| l.infeasible += 1);
            rail_ripple(c, a, b, Some(cin), None, &mut Vec::new());
            return;
        }
        Ok(Some(s)) => s,
    };
    let kb = carry_cfg().rail_bridge;
    if kb > 0.0 && (mode == SplitMode::Approx || (mode == SplitMode::Exact && carry_cfg().rail_bridge_exact)) {
        // B7 S-C rule: the exact hybrid costs `excess` extra CCX (one UMA per in-place stage); the split costs one
        // coin-gated boundary erase per chunk boundary ((n - 1) / 2 expected T for an n-bit compare).
        let excess = w - 2 - room;
        let kw = carry_cfg().split_k;
        let cost: f64 = sizes[..sizes.len() - 1].iter().enumerate().map(|(j, &s)| {
            let n = if mode == SplitMode::Approx && !(j == 0 && s <= kw) { kw.min(s) } else { s };
            (n as f64 - 1.0) / 2.0
        }).sum();
        if (excess as f64) < kb * cost {
            ledger(|l| {
                *l.splits.entry("B7 bridged ticks").or_insert(0) += 1;
                *l.splits.entry("B7 bridged stages").or_insert(0) += excess;
            });
            super::super::bridge::raw_add(c, a, b, Some(cin), None, excess);
            return;
        }
    }
    ledger(|l| *l.splits.entry(label).or_insert(0) += sizes.len() - 1);
    let mut bounds = Vec::with_capacity(sizes.len());
    let mut lo = 0;
    for &s in &sizes {
        bounds.push((lo, lo + s));
        lo += s;
    }
    let k_win = carry_cfg().split_k;
    let mut carry_in = Some(cin);
    let mut kept_defer: Option<(QubitId, usize)> = None;
    let mut kept: Vec<(QubitId, usize, usize, Option<QubitId>)> = Vec::new();
    for (j, &(lo, hi)) in bounds.iter().enumerate() {
        let last = j + 1 == bounds.len();
        let out = if last { None } else { Some(c.alloc_qubit()) };
        rail_ripple(c, &a[lo..hi], &b[lo..hi], carry_in, out, &mut Vec::new());
        match mode {
            SplitMode::Defer => {
                if let Some((bw, bhi)) = kept_defer.take() {
                    let m = c.alloc_bit();
                    c.hmr(bw, m);
                    c.free(bw);
                    tick_def.push((bhi - 1, m));
                }
                if let Some(o) = out {
                    kept_defer = Some((o, hi));
                }
            }
            SplitMode::Approx => {
                if let Some((bw, plo, phi, pcin)) = kept.pop() {
                    if plo == 0 && phi - plo <= k_win {
                        erase_with_compare(c, bw, &b[plo..phi], &a[plo..phi], pcin);
                    } else {
                        let k = k_win.min(phi - plo);
                        erase_with_compare(c, bw, &b[phi - k..phi], &a[phi - k..phi], None);
                    }
                    c.free(bw);
                }
                if let Some(o) = out {
                    kept.push((o, lo, hi, carry_in));
                }
            }
            SplitMode::Exact => {
                if let Some(o) = out {
                    kept.push((o, lo, hi, carry_in));
                }
            }
            SplitMode::Apply => unreachable!(),
        }
        carry_in = out;
    }
    if mode == SplitMode::Exact {
        for &(bw, lo, hi, cin_j) in kept.iter().rev() {
            erase_with_compare(c, bw, &b[lo..hi], &a[lo..hi], cin_j);
            c.free(bw);
        }
    }
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Rail ticks (B1 b1heo fwd_tick / rev_tick) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

#[allow(clippy::too_many_arguments)]
fn fwd_tick_c(c: &mut Builder, rails: &mut Rails, typ_prev: Option<QubitId>, wsw: usize, wad: usize,
              mode: SplitMode, def: &mut Vec<(usize, BitId)>, label: &'static str, o0_erase: bool) -> (QubitId, QubitId) {
    resize(c, &mut rails.r1, wsw);
    resize(c, &mut rails.r2, wsw);
    let ctl = rails.r1[0];
    for i in 1..wsw {
        fredkin(c, ctl, rails.r1[i], rails.r2[i]);
    }
    c.cx(ctl, rails.r2[0]);
    let mut e2 = rails.r1[1..].to_vec();
    let mut typ_prev = typ_prev;
    if o0_erase {
        // B7 O0 (Effort 7): typ_prev is L-T0's raw o_0 wire. Move the cx(o_0, ctl) up (ctl = o_1), then
        // o0 ^= ctl gives c_1, which the FD relation fixes from 3 low bits of the pre-add registers:
        // c_1 = r2[1]^r2[2]^e2[0]^e2[1]^kp ^ (r2[1] AND e2[0]). The linear part is XORed out and the AND is
        // measured out (HMR + CZ repair): 0 Toffoli, exact on every FD input.
        let o0 = typ_prev.take().expect("O0 erase needs the o_0 wire");
        assert!(wsw >= 4 && rails.r2.len() >= 3 && e2.len() >= 2);
        c.cx(o0, ctl);
        c.cx(ctl, o0);
        c.cx(rails.r2[1], o0);
        c.cx(rails.r2[2], o0);
        c.cx(e2[0], o0);
        c.cx(e2[1], o0);
        if o0_kp() {
            c.x(o0);
        }
        let m = c.alloc_bit();
        c.hmr(o0, m);
        c.cz_if(rails.r2[1], e2[0], m);
        c.free_bit(m);
        c.free(o0);
    }
    resize(c, &mut e2, wad);
    resize(c, &mut rails.r2, wad);
    let tau = c.alloc_qubit();
    c.cx(e2[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.x(tau);
    c.cx_all(tau, &e2);
    let r2 = rails.r2.clone();
    rail_add(c, &e2, &r2, tau, mode, def, label, wad >= wsw);
    c.cx_all(tau, &e2);
    c.x(tau);
    c.cx(e2[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    rails.r1 = e2;
    (ctl, tau)
}

/// Inverse of [`fwd_tick_c`]; rails enter at `wad`, leave at `w_before`.
#[allow(clippy::too_many_arguments)]
fn rev_tick_c(c: &mut Builder, rails: &mut Rails, typ: QubitId, s: QubitId, typ_prev: Option<QubitId>, wsw: usize,
              w_before: usize, mode: SplitMode, def: &mut Vec<(usize, BitId)>, label: &'static str,
              o0_rebuild: bool, top_copy: bool) -> Option<QubitId> {
    let wad = rails.r1.len();
    assert_eq!(rails.r2.len(), wad);
    let tau = s;
    c.cx(rails.r1[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.x(tau);
    c.cx_all(tau, &rails.r1);
    c.x_all(&rails.r2);
    let (r1, r2) = (rails.r1.clone(), rails.r2.clone());
    rail_add(c, &r1, &r2, tau, mode, def, label, top_copy);
    c.x_all(&rails.r2);
    c.cx_all(tau, &rails.r1);
    c.x(tau);
    c.cx(rails.r1[wad - 1], tau);
    c.cx(rails.r2[wad - 1], tau);
    c.free(tau);
    let ctl = typ;
    let mut rebuilt = None;
    if o0_rebuild {
        // B7 O0 (Effort 7): rebuild o_0 from (r1 = h, r2 = R2 before the add): g = c_1 (1 CCX), then o_0 = o_1 ^ c_1
        // and ctl = o_1 ^ o_0 = c_1, exactly what cx(o_0, ctl) would have left.
        assert!(typ_prev.is_none());
        let o0 = c.alloc_qubit();
        c.ccx(rails.r2[1], rails.r1[0], o0);
        c.cx(rails.r2[1], o0);
        c.cx(rails.r2[2], o0);
        c.cx(rails.r1[0], o0);
        c.cx(rails.r1[1], o0);
        if o0_kp() {
            c.x(o0);
        }
        c.cx(ctl, o0);
        c.cx(o0, ctl);
        rebuilt = Some(o0);
    }
    if let Some(tp) = typ_prev {
        c.cx(tp, ctl);
    }
    resize(c, &mut rails.r1, wsw - 1);
    resize(c, &mut rails.r2, wsw);
    rails.r1.insert(0, ctl);
    c.cx(ctl, rails.r2[0]);
    for i in 1..wsw {
        fredkin(c, ctl, rails.r1[i], rails.r2[i]);
    }
    resize(c, &mut rails.r1, w_before);
    resize(c, &mut rails.r2, w_before);
    rebuilt
}

/// B7 O0: the constant term of the c_1 decode, kp = [p mod 8 in {3, 5}] (0 for secp256k1, p = 7 mod 8).
fn o0_kp() -> bool {
    let r = SECP256K1_P.as_limbs()[0] & 7;
    r == 3 || r == 5
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Select-constant ripple (B1 b1arith.cselect_const_add) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

fn bits_of(v: U256, w: usize) -> Vec<bool> {
    (0..w).map(|i| i < 256 && v.bit(i)).collect()
}
/// Two's complement of `v` over `w` bits (w may exceed 256).
fn neg_bits(v: U256, w: usize) -> Vec<bool> {
    let b = bits_of(v, w);
    let mut out = vec![false; w];
    let mut carry = true;
    for i in 0..w {
        let inv = !b[i];
        out[i] = inv ^ carry;
        carry &= inv;
    }
    out
}

/// Phase `(-1)^m` (a classically conditioned global phase) via any wire `q`.
fn neg_if(c: &mut Builder, q: QubitId, m: BitId) {
    c.x(q);
    c.z_if(q, m);
    c.x(q);
    c.z_if(q, m);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Zero,
    One,
    Ctl,
    NCtl,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum How {
    Copy,
    AndC,
    AndNc,
    AndP,
    OrP,
    Maj,
}

/// `acc += (ctrl ? k1 : k0) mod 2^len(acc)`, exact, one Toffoli per live carry.
fn cselect_const_add(c: &mut Builder, acc: &[QubitId], k0: &[bool], k1: &[bool], ctrl: QubitId) {
    let w = acc.len();
    let kind: Vec<Kind> = (0..w).map(|i| match (k0[i], k1[i]) {
        (false, false) => Kind::Zero,
        (true, true) => Kind::One,
        (false, true) => Kind::Ctl,
        (true, false) => Kind::NCtl,
    }).collect();
    let mut car: Vec<Option<QubitId>> = vec![None; w + 1];
    let mut how: Vec<Option<How>> = vec![None; w + 1];
    let maj_fwd = |c: &mut Builder, i: usize, prev: QubitId, q: QubitId, kind: &[Kind]| {
        let neg = kind[i] == Kind::NCtl;
        if neg { c.x(ctrl); }
        c.cx(prev, acc[i]);
        c.cx(prev, ctrl);
        c.ccx(acc[i], ctrl, q);
        c.cx(prev, ctrl);
        c.cx(prev, acc[i]);
        if neg { c.x(ctrl); }
        c.cx(prev, q);
    };
    let maj_undo = |c: &mut Builder, i: usize, prev: QubitId, m: BitId, kind: &[Kind]| {
        let neg = kind[i] == Kind::NCtl;
        if neg { c.x(ctrl); }
        c.cx(prev, acc[i]);
        c.cx(prev, ctrl);
        c.cz_if(acc[i], ctrl, m);
        c.cx(prev, ctrl);
        c.cx(prev, acc[i]);
        if neg { c.x(ctrl); }
        c.z_if(prev, m);
    };
    for i in 0..w.saturating_sub(1) {
        let k = kind[i];
        match car[i] {
            None => {
                if k == Kind::Zero { continue; }
                let q = c.alloc_qubit();
                match k {
                    Kind::One => { c.cx(acc[i], q); how[i + 1] = Some(How::Copy); }
                    Kind::Ctl => { c.ccx(acc[i], ctrl, q); how[i + 1] = Some(How::AndC); }
                    _ => { c.x(ctrl); c.ccx(acc[i], ctrl, q); c.x(ctrl); how[i + 1] = Some(How::AndNc); }
                }
                car[i + 1] = Some(q);
            }
            Some(prev) => {
                let q = c.alloc_qubit();
                match k {
                    Kind::Zero => { c.ccx(acc[i], prev, q); how[i + 1] = Some(How::AndP); }
                    Kind::One => {
                        c.x(acc[i]); c.x(prev); c.ccx(acc[i], prev, q); c.x(q); c.x(acc[i]); c.x(prev);
                        how[i + 1] = Some(How::OrP);
                    }
                    _ => { maj_fwd(c, i, prev, q, &kind); how[i + 1] = Some(How::Maj); }
                }
                car[i + 1] = Some(q);
            }
        }
    }
    for i in (0..w).rev() {
        if i + 1 < w {
            if let Some(q) = car[i + 1] {
                let prev = car[i];
                match how[i + 1].unwrap() {
                    How::Copy => c.cx(acc[i], q),
                    h => {
                        let m = c.alloc_bit();
                        c.hmr(q, m);
                        match h {
                            How::AndC => c.cz_if(acc[i], ctrl, m),
                            How::AndNc => { c.x(ctrl); c.cz_if(acc[i], ctrl, m); c.x(ctrl); }
                            How::AndP => c.cz_if(acc[i], prev.unwrap(), m),
                            How::OrP => {
                                neg_if(c, acc[i], m);
                                let p = prev.unwrap();
                                c.x(acc[i]); c.x(p); c.cz_if(acc[i], p, m); c.x(acc[i]); c.x(p);
                            }
                            How::Maj => maj_undo(c, i, prev.unwrap(), m, &kind),
                            How::Copy => unreachable!(),
                        }
                        c.free_bit(m);
                    }
                }
                c.free(q);
            }
        }
        match kind[i] {
            Kind::One => c.x(acc[i]),
            Kind::Ctl => c.cx(ctrl, acc[i]),
            Kind::NCtl => { c.cx(ctrl, acc[i]); c.x(acc[i]); }
            Kind::Zero => {}
        }
        if let Some(p) = car[i] {
            c.cx(p, acc[i]);
        }
    }
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ G3: tick 0 of the rails seeded directly (B1 b1g3) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

fn fw_slice() -> usize {
    super::super::modular::f_slice()
}

/// Rotate a register list down by one (relabel only, no ops).
fn rot_down(v: &[QubitId]) -> Vec<QubitId> {
    let mut o = v[1..].to_vec();
    o.push(v[0]);
    o
}
fn rot_up(v: &[QubitId]) -> Vec<QubitId> {
    let mut o = vec![v[v.len() - 1]];
    o.extend_from_slice(&v[..v.len() - 1]);
    o
}

/// From `x = d`: `R1 = h = (d + b p)/2`, `R2 = h + p` (b = 0) or `h - p` (b = 1),
/// tape trit 0 = `(typ = ~b, s = b)`. `x`'s wires become `R1`'s low 256 bits.
fn g3_seed(c: &mut Builder, x: &[QubitId], wout: usize) -> (Rails, QubitId, QubitId) {
    let fw = fw_slice();
    let b = c.alloc_qubit();
    c.cx(x[0], b);
    c.cx(b, x[0]);
    let half = f() >> 1;
    let kneg = U256::ZERO.wrapping_sub(half); // -(f>>1) mod 2^256; the slice keeps fw-1 bits
    cadd_const_trunc(c, &x[1..fw], kneg, b, false);
    let xr = rot_down(x);
    c.cx(b, xr[N - 1]);
    c.cx(xr[N - 1], b);
    c.free(b);
    let mut r1 = xr.clone();
    r1.extend(c.alloc_qubits(wout - N));
    let typ0 = c.alloc_qubit();
    let s0 = c.alloc_qubit();
    c.cx(r1[N - 1], s0);
    c.cx(r1[N - 1], typ0);
    c.x(typ0);
    let r2 = c.alloc_qubits(wout);
    for i in 0..N {
        c.cx(r1[i], r2[i]);
    }
    cselect_const_add(c, &r2, &bits_of(SECP256K1_P, wout), &neg_bits(SECP256K1_P, wout), r1[N - 1]);
    (Rails { r1, r2 }, typ0, s0)
}

/// Inverse of [`g3_seed`]; returns the 256 wires now holding `d` (in order).
fn g3_unseed(c: &mut Builder, rails: Rails, typ0: QubitId, s0: QubitId) -> Vec<QubitId> {
    let Rails { r1, r2 } = rails;
    let w = r2.len();
    assert_eq!(r1.len(), w);
    cselect_const_add(c, &r2, &neg_bits(SECP256K1_P, w), &bits_of(SECP256K1_P, w), r1[N - 1]);
    for i in 0..N {
        c.cx(r1[i], r2[i]);
    }
    c.free_vec(&r2);
    c.x(typ0);
    c.cx(r1[N - 1], typ0);
    c.cx(r1[N - 1], s0);
    c.free(typ0);
    c.free(s0);
    c.free_vec(&r1[N..]);
    let x = r1[..N].to_vec();
    let b = c.alloc_qubit();
    c.cx(x[N - 1], b);
    c.cx(b, x[N - 1]);
    let xu = rot_up(&x);
    let fw = fw_slice();
    cadd_const_trunc(c, &xu[1..fw], f() >> 1, b, false);
    c.cx(b, xu[0]);
    c.cx(xu[0], b);
    c.free(b);
    xu
}

/// Base seed without G3: `(R1, R2) = (d + p, d)` at `w0`.
fn seed_base(c: &mut Builder, x: &[QubitId], w0: usize) -> Rails {
    let r1 = c.alloc_qubits(w0);
    c.cx_pairs(&x[..N], &r1[..N]);
    cselect_const_add(c, &r1, &bits_of(SECP256K1_P, w0), &bits_of(SECP256K1_P, w0), x[0]);
    let mut r2 = x.to_vec();
    r2.extend(c.alloc_qubits(w0 - N));
    Rails { r1, r2 }
}
fn unseed_base(c: &mut Builder, rails: Rails) -> Vec<QubitId> {
    let Rails { r1, r2 } = rails;
    let w = r1.len();
    cselect_const_add(c, &r1, &neg_bits(SECP256K1_P, w), &neg_bits(SECP256K1_P, w), r2[0]);
    c.cx_pairs(&r2[..N], &r1[..N]);
    c.free_vec(&r1);
    c.free_vec(&r2[N..]);
    r2[..N].to_vec()
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ B4: H0 start frame (h, h - p) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

/// `R1 = h = d/2 mod p` (G3's truncated mod-halve), `R2 = h - p` for EVERY d: low 256 bits `h + F`
/// (h + F < 2^256, one truncated constant ladder over the fold window), bits >= 256 set to 1.
/// Tick-0 pseudo-letter `(typ0, s0) = (o_{-1}, 0)` with `o_{-1} = [h < p/2] = NOT h[255]`
/// (exact but for a 2^-225 sliver). `x`'s wires become `R1`'s low 256 bits.
fn h0_seed(c: &mut Builder, x: &[QubitId], wout: usize) -> (Rails, QubitId, QubitId) {
    let fw = fw_slice();
    let b = c.alloc_qubit();
    c.cx(x[0], b);
    c.cx(b, x[0]);
    let half = f() >> 1;
    let kneg = U256::ZERO.wrapping_sub(half);
    cadd_const_trunc(c, &x[1..fw], kneg, b, false);
    let xr = rot_down(x);
    c.cx(b, xr[N - 1]);
    c.cx(xr[N - 1], b);
    c.free(b);
    let mut r1 = xr.clone();
    r1.extend(c.alloc_qubits(wout - N));
    let r2 = c.alloc_qubits(wout);
    for i in 0..N {
        c.cx(r1[i], r2[i]);
    }
    add_const(c, &r2[..fw], f());
    for &q in &r2[N..] {
        c.x(q);
    }
    let typ0 = c.alloc_qubit();
    c.cx(r1[N - 1], typ0);
    c.x(typ0);
    let s0 = c.alloc_qubit();
    (Rails { r1, r2 }, typ0, s0)
}

/// Inverse of [`h0_seed`]; returns the 256 wires now holding `d` (in order).
fn h0_unseed(c: &mut Builder, rails: Rails, typ0: QubitId, s0: QubitId) -> Vec<QubitId> {
    let Rails { r1, r2 } = rails;
    let w = r2.len();
    assert_eq!(r1.len(), w);
    let fw = fw_slice();
    c.free(s0);
    c.x(typ0);
    c.cx(r1[N - 1], typ0);
    c.free(typ0);
    for &q in &r2[N..] {
        c.x(q);
    }
    sub_const(c, &r2[..fw], f());
    for i in 0..N {
        c.cx(r1[i], r2[i]);
    }
    c.free_vec(&r2);
    c.free_vec(&r1[N..]);
    let x = r1[..N].to_vec();
    let b = c.alloc_qubit();
    c.cx(x[N - 1], b);
    c.cx(b, x[N - 1]);
    let xu = rot_up(&x);
    cadd_const_trunc(c, &xu[1..fw], f() >> 1, b, false);
    c.cx(b, xu[0]);
    c.cx(xu[0], b);
    c.free(b);
    xu
}

/// H0 payload seed fused with cell 1 (division). On entry `Sig = N`; allocates `Del`.
/// Leaves `Del = (-1)^{o_{-1}} N`, `Sig = (-1)^{1 + o_{-1} + o_1} N/2` (verified on scalar walks,
/// `B4/h0_scalar.py`), i.e. the state after cell 1 and before route 1.
fn h0_payload_div(c: &mut Builder, sig: &[QubitId], om1: QubitId, o1: QubitId) -> Vec<QubitId> {
    let del = c.alloc_qubits(N);
    c.cx_pairs(sig, &del);
    h7::mod_halve(c, sig);
    h7::cond_negate(c, om1, &del);
    c.cx(om1, o1);
    c.x(o1);
    h7::cond_negate(c, o1, sig);
    c.x(o1);
    c.cx(om1, o1);
    del
}

/// Inverse of [`h0_payload_div`] at the end of the multiply head batch: from
/// `(Sig, Del) = ((-1)^{1+o_{-1}+o_1} M/2, (-1)^{o_{-1}} M)` to `Sig = M`, `Del = 0`.
fn h0_payload_mul_inv(c: &mut Builder, sig: &[QubitId], del: &[QubitId], om1: QubitId, o1: QubitId) {
    c.cx(om1, o1);
    c.x(o1);
    h7::cond_negate(c, o1, sig);
    c.x(o1);
    c.cx(om1, o1);
    h7::cond_negate(c, om1, del);
    h7::mod_double(c, sig);
    c.cx_pairs(sig, del);
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ B4: FD fused start ((d - b p)/2, 3X + (2b - 1) p) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

/// Rails: `X = (d>>1) + b (F+1)/2` with sign bits `b` (= `(d - b p)/2`), `Y = d - (1-b) p + X`
/// (walk-search CHECK c11 fused seed). Pseudo-letter `(o_0, s_0)`: `o_0 = [|X| < |Y|] = NOT(X_sign ^ X[254])`
/// (exact but for a 2^-220 sliver), `s_0 = Y_sign & NOT o_0` (a legal trit; lets the multiply leg decode the
/// payload class). `x`'s wires become `X`'s low 256 bits.
pub(crate) fn fd_seed(c: &mut Builder, x: &[QubitId], wout: usize, with_s0: bool) -> (Rails, QubitId, Option<QubitId>) {
    assert!(wout >= N + 1, "FD rails need a sign bit above 256");
    if let Some((r1,y))=super::super::native_sfuse_b::take_native(c,x,wout){
        let typ0=c.alloc_qubit();c.cx(r1[wout-1],typ0);c.cx(r1[N-2],typ0);c.x(typ0);
        let s=if with_s0{let q=c.alloc_qubit();c.x(typ0);c.ccx(y[wout-1],typ0,q);c.x(typ0);Some(q)}else{None};
        return(Rails{r1,r2:y},typ0,s);
    }
    if super::super::fd_coordinate::enabled(){if let Some((r1,y))=super::super::fd_coordinate::native_seed(c,x,wout){
        let typ0=c.alloc_qubit();c.cx(r1[wout-1],typ0);c.cx(r1[N-2],typ0);c.x(typ0);
        let s=if with_s0{let q=c.alloc_qubit();c.x(typ0);c.ccx(y[wout-1],typ0,q);c.x(typ0);Some(q)}else{None};
        return(Rails{r1,r2:y},typ0,s);
    }}
    fd_seed_at(c, x, wout, with_s0, N, f(), fw_slice())
}

/// [`fd_seed`] at width `n`, fold constant `f` (`p = 2^n - f`) and ladder window `fw`: the production
/// body, parametrised so the back-seam certificate runs it at n = 4 / 6.
pub(crate) fn fd_seed_at(c: &mut Builder, x: &[QubitId], wout: usize, with_s0: bool, n: usize, f: U256, fw: usize) -> (Rails, QubitId, Option<QubitId>) {
    assert!(wout >= n + 1, "FD rails need a sign bit above the register");
    assert_eq!(x.len(), n);
    let b = c.alloc_qubit();
    c.cx(x[0], b);
    let y = c.alloc_qubits(wout);
    for i in 0..n {
        c.cx(x[i], y[i]);
    }
    c.x(b);
    cadd_const_trunc(c, &y[..fw], f, b, false);
    for &q in &y[n..] {
        c.cx(b, q);
    }
    c.x(b);
    c.cx(b, x[0]);
    let half_up = (f + U256::from(1u64)) >> 1;
    cadd_const_trunc(c, &x[1..fw], half_up, b, false);
    let xr = rot_down(x);
    c.cx(b, xr[n - 1]);
    let mut r1 = xr.clone();
    let ext = c.alloc_qubits(wout - n);
    for &q in &ext {
        c.cx(b, q);
    }
    r1.extend(ext);
    c.cx(xr[n - 1], b);
    c.free(b);
    super::gidney_add(c, &r1, &y, None);
    let typ0 = c.alloc_qubit();
    c.cx(r1[wout - 1], typ0);
    c.cx(r1[n - 2], typ0);
    c.x(typ0);
    if !with_s0 {
        return (Rails { r1, r2: y }, typ0, None);
    }
    let s0 = c.alloc_qubit();
    c.x(typ0);
    c.ccx(y[wout - 1], typ0, s0);
    c.x(typ0);
    (Rails { r1, r2: y }, typ0, Some(s0))
}

/// Inverse of [`fd_seed`]; returns the 256 wires now holding `d` (in order). With the back seam fused
/// for `leg` (`BACK_SEAM_FUSE`), the wires hold `d + b (F+1)` on the low window instead and the
/// coordinate op that follows completes the correction (see `back_seam`).
fn fd_unseed(c: &mut Builder, rails: Rails, typ0: QubitId, s0: Option<QubitId>, leg: super::super::back_seam::Leg) -> Vec<QubitId> {
    fd_unseed_at(c, rails, typ0, s0, N, f(), fw_slice(), super::super::back_seam::fused(leg))
}

/// [`fd_unseed`] at width `n`, fold constant `f` and ladder window `fw`; `fused` = the back seam.
pub(crate) fn fd_unseed_at(c: &mut Builder, rails: Rails, typ0: QubitId, s0: Option<QubitId>, n: usize, f: U256, fw: usize, fused: bool) -> Vec<QubitId> {
    let Rails { r1, r2: y } = rails;
    let wout = y.len();
    assert_eq!(r1.len(), wout);
    if let Some(s0) = s0 {
        c.x(typ0);
        c.ccx(y[wout - 1], typ0, s0);
        c.x(typ0);
        c.free(s0);
    }
    c.x(typ0);
    c.cx(r1[n - 2], typ0);
    c.cx(r1[wout - 1], typ0);
    c.free(typ0);
    c.x_all(&y);
    super::gidney_add(c, &r1, &y, None);
    c.x_all(&y);
    let b = c.alloc_qubit();
    let xr = r1[..n].to_vec();
    c.cx(xr[n - 1], b);
    for &q in &r1[n..] {
        c.cx(b, q);
    }
    c.free_vec(&r1[n..]);
    c.cx(b, xr[n - 1]);
    let x = rot_up(&xr);
    let half_up = (f + U256::from(1u64)) >> 1;
    if !fused {
        cadd_const_trunc(c, &x[1..fw], U256::ZERO.wrapping_sub(half_up), b, false);
    }
    c.cx(b, x[0]);
    c.x(b);
    for &q in &y[n..] {
        c.cx(b, q);
    }
    if fused {
        // I-2 back seam: `y += b ? (F+1) : -F` as one selected ladder; `y` then equals the
        // uncorrected `x` (= d + b (F+1) on the window) and the XOR below still clears it.
        c.x(b);
        super::super::back_seam::selected_ladder(c, &y[..fw], b, U256::ZERO.wrapping_sub(f), f + U256::from(1u64));
        super::super::back_seam::note_fused_unseed();
    } else {
        cadd_const_trunc(c, &y[..fw], U256::ZERO.wrapping_sub(f), b, false);
        c.x(b);
    }
    for i in 0..n {
        c.cx(x[i], y[i]);
    }
    c.free_vec(&y);
    c.cx(x[0], b);
    c.free(b);
    x
}

/// FD payload seed (division), rails at the post-seed state. On entry `Sig = N`; allocates `Del`.
/// Classes (`B4/fd_scalar.py`, CHECK c11): from (N, 2N), swap iff A = NOT(xs ^ ys), negate Sig iff ys,
/// negate Del iff NOT(ys ^ o_0).
fn fd_payload_div(c: &mut Builder, sig: &[QubitId], xs: QubitId, ys: QubitId, o0: QubitId) -> Vec<QubitId> {
    let del = c.alloc_qubits(N);
    c.cx_pairs(sig, &del);
    h7::mod_double(c, &del);
    c.cx(xs, ys);
    c.x(ys);
    route(c, ys, sig, &del);
    c.x(ys);
    c.cx(xs, ys);
    h7::cond_negate(c, ys, sig);
    c.cx(o0, ys);
    c.x(ys);
    h7::cond_negate(c, ys, &del);
    c.x(ys);
    c.cx(o0, ys);
    del
}

/// RB-1: exact inverse of [`fd_payload_div`] given the class wires (X_sign, Y_sign, o_0); clears `del` to 0.
fn fd_payload_div_inv(c: &mut Builder, sig: &[QubitId], del: &[QubitId], xs: QubitId, ys: QubitId, o0: QubitId) {
    c.cx(o0, ys);
    c.x(ys);
    c.fold_trace("fd-neg-del", |c| h7::cond_negate(c, ys, del));
    c.x(ys);
    c.cx(o0, ys);
    c.fold_trace("fd-neg-sig", |c| h7::cond_negate(c, ys, sig));
    c.cx(xs, ys);
    c.x(ys);
    route(c, ys, sig, del);
    c.x(ys);
    c.cx(xs, ys);
    c.fold_trace("fd-halve-del", |c| h7::mod_halve(c, del));
    c.cx_pairs(sig, del);
}

/// Inverse of [`fd_payload_div`] at the end of the multiply head batch; the class is decoded from the tape
/// pseudo-letter `(o_0, s_0)` and the carried sign wire `bw` = X_sign: `ys = o_0 ? NOT bw : s_0`.
fn fd_payload_mul_inv(c: &mut Builder, sig: &[QubitId], del: &[QubitId], o0: QubitId, s0: QubitId, bw: QubitId) {
    // s_0 = 0 whenever o_0 = 1, so ys = s_0 ^ (o_0 & NOT bw): one Toffoli each way.
    let ys = c.alloc_qubit();
    let dec = |c: &mut Builder| {
        c.x(bw);
        c.ccx(o0, bw, ys);
        c.x(bw);
    };
    c.cx(s0, ys);
    dec(c);
    c.cx(o0, ys);
    c.x(ys);
    h7::cond_negate(c, ys, del);
    c.x(ys);
    c.cx(o0, ys);
    h7::cond_negate(c, ys, sig);
    c.cx(bw, ys);
    c.x(ys);
    route(c, ys, sig, del);
    c.x(ys);
    c.cx(bw, ys);
    h7::mod_halve(c, del);
    c.cx_pairs(sig, del);
    dec(c);
    c.cx(s0, ys);
    c.free(ys);
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ G1b: payload ticks 0-1 in closed form (B1 b1g3) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

/// On entry `Sig = N` (cell 0 skipped). Allocates `Del`; leaves `(h, 0)` if s0 = 0,
/// `(+h, N)` if s0 = 1 and tick 1 is E, `(-h, N)` if A (h = N/2 mod p).
fn g1b_forward(c: &mut Builder, sig: &[QubitId], s0: QubitId, typ1: QubitId) -> Vec<QubitId> {
    let del = c.alloc_qubits(N);
    for i in 0..N {
        c.ccx(s0, sig[i], del[i]);
    }
    h7::mod_halve(c, sig);
    c.x(typ1);
    let a = c.alloc_qubit();
    c.ccx(s0, typ1, a);
    c.x(typ1);
    h7::cond_negate(c, a, sig);
    let m = c.alloc_bit();
    c.hmr(a, m);
    c.x(typ1);
    c.cz_if(s0, typ1, m);
    c.x(typ1);
    c.free_bit(m);
    c.free(a);
    del
}

/// Mirror of [`g1b_forward`]: on exit `Sig = y d`, and `Del = 0` on every lane (for
/// s0 = 0 it held the degenerate representative p, cleared under ~s0).
fn g1b_inverse(c: &mut Builder, sig: &[QubitId], del: &[QubitId], s0: QubitId, typ1: QubitId) {
    c.x(typ1);
    let a = c.alloc_qubit();
    c.ccx(s0, typ1, a);
    c.x(typ1);
    h7::cond_negate(c, a, sig);
    let m = c.alloc_bit();
    c.hmr(a, m);
    c.x(typ1);
    c.cz_if(s0, typ1, m);
    c.x(typ1);
    c.free_bit(m);
    c.free(a);
    h7::mod_double(c, sig);
    for i in 0..N {
        c.ccx(s0, sig[i], del[i]);
    }
    c.x(s0);
    for i in 0..N {
        if SECP256K1_P.bit(i) {
            c.cx(s0, del[i]);
        }
    }
    c.x(s0);
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Multiply-zone cell: B1 double_add_nc on the head's adder Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

fn block_selectors(u: U256, width: usize, m1f: QubitId, p2f: QubitId, e: QubitId) -> Vec<Vec<QubitId>> {
    let nu = h7::twos_complement_bits(u, width);
    (0..width).map(|i| {
        let pu = i < 256 && u.bit(i);
        let p2u = i >= 1 && i - 1 < 256 && u.bit(i - 1);
        let mut out = Vec::new();
        if pu ^ nu[i] { out.push(m1f); }
        if p2u { out.push(p2f); }
        if pu { out.push(e); }
        out
    }).collect()
}

fn fold_generic_single(c: &mut Builder, acc: &[QubitId], sel: &[Vec<QubitId>], first_carry: QubitId) {
    let width = acc.len();
    assert!(width >= 3);
    for &q in &sel[0] {
        c.cx(q, acc[0]);
    }
    let carries = c.alloc_qubits(width - 3);
    let prev = |off: usize| if off == 0 { first_carry } else { carries[off - 1] };
    for off in 0..carries.len() {
        fold_step(c, acc[off + 1], prev(off), carries[off], &sel[off + 1], false);
    }
    let i = width - 2;
    fold_step(c, acc[i], prev(carries.len()), acc[width - 1], &sel[i], true);
    for &q in &sel[width - 1] {
        c.cx(q, acc[width - 1]);
    }
    for off in (0..carries.len()).rev() {
        unwind_fold_step(c, acc[off + 1], prev(off), carries[off], &sel[off + 1]);
    }
    c.free_vec(&carries);
}

fn fold_generic(c: &mut Builder, acc: &[QubitId], m1f: QubitId, p2f: QubitId, e: QubitId, first_carry: QubitId) {
    let fw = acc.len();
    if c.active_qubits() as usize + fw - 3 <= h7::cap() {
        let sel = block_selectors(f(), fw, m1f, p2f, e);
        fold_generic_single(c, acc, &sel, first_carry);
        return;
    }
    let sb = h7::FOLD_SPLIT_BIT;
    let f_low = f() & ((U256::from(1) << sb) - U256::from(1));
    fold_generic_single(c, &acc[..sb], &block_selectors(f_low, sb, m1f, p2f, e), first_carry);
    let boundary = c.alloc_qubit();
    c.ccx(acc[sb], e, boundary);
    fold_generic_single(c, &acc[sb..], &block_selectors(U256::from(1), fw - sb, m1f, p2f, e), boundary);
    c.cx(e, acc[sb]);
    h7::and_uncompute(c, boundary, acc[sb], e);
    c.cx(e, acc[sb]);
}

/// `target <- 2 target + (-1)^sign source (mod p)`; degenerate inverses (output 0)
/// always land on the representative p (B1 `double_add_nc`).
fn double_add_nc(c: &mut Builder, sign: QubitId, source: &[QubitId], target: &[QubitId], fw: usize, proxy: usize) {
    let od = h7::start_doubling(c, target);
    c.cx_all(sign, source);
    let o = h7::chunked_add(c, source, target, proxy, true);
    c.cx(sign, o);
    c.cx(sign, od);
    let rr = h7::and_clean(c, o, od);
    c.cx(sign, o);
    c.cx(sign, od);
    c.x(sign);
    let p2f = h7::and_clean(c, rr, sign);
    c.x(sign);
    c.cx(p2f, rr); // rr wire = m1f
    c.cx(od, o);
    c.cx(sign, o); // o wire = e
    c.cx(sign, target[0]);
    c.cx(sign, o);
    let fc = h7::and_clean(c, target[0], o);
    c.cx(sign, fc);
    c.cx(sign, target[0]);
    c.cx(sign, o);
    c.cx(sign, target[0]);
    fold_generic(c, &target[..fw], rr, p2f, o, fc);
    c.cx(o, target[0]);
    c.cx(sign, target[0]);
    c.cx(sign, fc);
    c.cx(sign, target[0]);
    c.cx(sign, o);
    h7::and_uncompute(c, fc, target[0], o);
    c.cx(sign, target[0]);
    c.cx(sign, o);
    c.cx(sign, target[0]);
    c.cx(o, target[0]);
    c.cx(sign, o);
    c.cx(od, o);
    c.cx(p2f, rr);
    c.x(sign);
    h7::and_uncompute(c, p2f, rr, sign);
    c.x(sign);
    c.cx(sign, o);
    c.cx(sign, od);
    h7::and_uncompute(c, rr, o, od);
    c.cx(sign, o);
    c.cx(sign, od);
    c.cx(target[0], od);
    c.cx(source[0], od);
    c.cx(o, od);
    c.free(od);
    let (mut k, seeded) = h7::mul_flag_spec(proxy, fw);
    let borrow = if seeded {
        Some(source[N - k - 1])
    } else if carry_cfg().nc_seed {
        k -= 1;
        Some(source[N - k - 1])
    } else {
        None
    };
    erase_with_compare(c, o, &target[N - k..], &source[N - k..], borrow);
    c.free(o);
    c.cx_all(sign, source);
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Cells + routing Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

fn route(c: &mut Builder, s: QubitId, sig: &[QubitId], del: &[QubitId]) {
    for i in 0..N {
        h7::cswap(c, s, sig[i], del[i]);
    }
}

/// The esw[t] the cells key their proxy round on: the row's own, or the pinned `HEO_PROXY_ENVELOPE` (INTEGRATE-R3).
fn cell_proxy_w(cfg: &HeoConfig, t: usize) -> usize {
    match &carry_cfg().proxy_esw {
        Some(v) => *v.get(t).unwrap_or_else(|| panic!("HEO_PROXY_ENVELOPE has {} ticks, needs tick {t}", v.len())),
        None => cfg.esw[t],
    }
}

/// K2 (`K2_CELL_LOAN`): R1 at a cell is E/2 = r1[1..esw] sign-extended, so when its length reaches esw its top wire
/// is an exact copy of the wire below on every shot. 1 = the head's replay sign-copy loan; 2 = raw loan. It is the
/// same wire HEO_LR1 frees, so it is inert while HEO_LR1=1 (R1 is then already esw-1 long at every cell).
fn k2_cell_loan(c: &mut Builder, r1: &[QubitId], esw_t: usize, body: impl FnOnce(&mut Builder)) {
    static MODE: OnceLock<usize> = OnceLock::new();
    let mode = *MODE.get_or_init(|| env_usize("K2_CELL_LOAN", 0));
    let n = r1.len();
    if mode == 0 || n < 3 || n < esw_t {
        body(c);
        return;
    }
    let (q, s) = (r1[n - 1], r1[n - 2]);
    if mode == 1 {
        h7::with_copy_loans(c, &[(q, s)], body);
    } else {
        c.cx(s, q);
        c.release_clean(q);
        body(c);
        c.reacquire(q);
        c.cx(s, q);
    }
}

/// K3b per-cell oracle harness. `K3B_CELL_PINS_ALL="N=V;N=V"` pins every payload cell; `K3B_CELL_OVR=path` holds
/// lines `idx N=V N=V ...` for single cells (cell index = order of cell calls in the build); `K3B_CELL_TRACE=1`
/// prints `K3B_CELL idx dir t proxy live room cost nB lB nF lF` (cost = expected T of the cell, from the phase report).
fn k3b_cell<R>(c: &mut Builder, dir: &str, t: usize, proxy: usize, body: impl FnOnce(&mut Builder) -> R) -> R {
    use std::collections::HashMap;
    use std::sync::atomic::{AtomicUsize, Ordering};
    static IDX: AtomicUsize = AtomicUsize::new(0);
    static ALL: OnceLock<Vec<(String, String)>> = OnceLock::new();
    static OVR: OnceLock<HashMap<usize, Vec<(String, String)>>> = OnceLock::new();
    static TRACE: OnceLock<bool> = OnceLock::new();
    let kv = |s: &str| -> Vec<(String, String)> {
        s.split([';', ' ']).filter(|x| !x.trim().is_empty()).map(|x| {
            let (k, v) = x.split_once('=').expect("N=V");
            (k.trim().to_string(), v.trim().to_string())
        }).collect()
    };
    let all = ALL.get_or_init(|| std::env::var("K3B_CELL_PINS_ALL").map(|s| kv(&s)).unwrap_or_default());
    let ovr = OVR.get_or_init(|| std::env::var("K3B_CELL_OVR").ok().map(|p| {
        include_str!("skywalk_data/ovr_v025_lamneutral.txt").to_owned().lines().filter(|l| !l.trim().is_empty() && !l.starts_with('#')).map(|l| {
            let (i, rest) = l.trim().split_once(char::is_whitespace).unwrap_or((l.trim(), ""));
            (i.parse::<usize>().unwrap(), kv(rest))
        }).collect()
    }).unwrap_or_default());
    let idx = IDX.fetch_add(1, Ordering::Relaxed);
    let mut pins: HashMap<String, String> = all.iter().cloned().collect();
    if let Some(v) = ovr.get(&idx) {
        pins.extend(v.iter().cloned());
    }
    let set = !pins.is_empty();
    if set {
        super::CELL_PINS.with(|m| *m.borrow_mut() = Some(pins));
    }
    let live = c.active_qubits();
    let room = h7::cap().saturating_sub(live as usize);
    let before = c.report_totals();
    let s0 = c.k3b_sites;
    let out = body(c);
    let after = c.report_totals();
    let s1 = c.k3b_sites;
    if set {
        super::CELL_PINS.with(|m| *m.borrow_mut() = None);
    }
    if *TRACE.get_or_init(|| env_bool("K3B_CELL_TRACE", false)) {
        let cost = match (before, after) { (Some(b), Some(a)) => a.1 - b.1, _ => f64::NAN };
        eprintln!("K3B_CELL {idx} {dir} {t} {proxy} {live} {room} {cost:.1} {} {:.3e} {} {:.3e}", s1.0 - s0.0,
            s1.1 - s0.1, s1.2 - s0.2, s1.3 - s0.3);
    }
    out
}

/// Division cell t: `Sig <- (Sig - (-1)^g Del)/2`.
fn cell_div(c: &mut Builder, cfg: &HeoConfig, t: usize, typ: QubitId, sig: &[QubitId], del: &[QubitId]) {
    let proxy = h7::proxy_round(cell_proxy_w(cfg, t));
    let (db, df, dx) = cell_shift(false, t);
    let fw = h7::fold_window(proxy, false).checked_add_signed(dx).expect("HEO_CELL_WINDOWS: fold window positive");

    if truthy("HEO_CELL_TRACE") {
        eprintln!("HEO_CELL div t={t} esw={} proxy={proxy} fw={fw} live={} room={}", cfg.esw[t], c.active_qubits(),
            h7::cap().saturating_sub(c.active_qubits() as usize));
    }
    k3b_cell(c, "div", t, proxy, |c| {
        if std::env::var_os("TERMINAL_PAIR").is_some() && t+1==cfg.rounds() {
            let fw=std::env::var("TERMINAL_FW").ok().map(|x|x.parse().unwrap()).unwrap_or(50);
            eprintln!("TERMINAL_SITE {} {} {} {}","div",t,c.active_qubits(),fw);
            super::super::pingpong::terminal_pair(c,typ,sig,del,fw,true);return;
        }

        c.x(typ);
        let tie = (t < carry_cfg().zone).then_some(typ);
        h7::with_cmp_shift((db, df), || h7::with_tie(tie, || h7::add_halve(c, typ, del, sig, fw, proxy)));
        c.x(typ);
    });
}

/// Multiply cell t: `Sig <- 2 Sig + (-1)^g Del`.
fn cell_mul(c: &mut Builder, cfg: &HeoConfig, t: usize, typ: QubitId, sig: &[QubitId], del: &[QubitId]) {
    let proxy = h7::proxy_round(cell_proxy_w(cfg, t));
    let (db, df, dx) = cell_shift(true, t);
    let fw = h7::fold_window(proxy, true).checked_add_signed(dx).expect("HEO_CELL_WINDOWS: fold window positive");

    if truthy("HEO_CELL_TRACE") {
        eprintln!("HEO_CELL mul t={t} esw={} proxy={proxy} fw={fw} live={} room={}", cfg.esw[t], c.active_qubits(),
            h7::cap().saturating_sub(c.active_qubits() as usize));
    }
    k3b_cell(c, "mul", t, proxy, |c| {
        if std::env::var_os("TERMINAL_PAIR").is_some() && t+1==cfg.rounds() {
            let fw=std::env::var("TERMINAL_FW").ok().map(|x|x.parse().unwrap()).unwrap_or(50);
            eprintln!("TERMINAL_SITE {} {} {} {}","mul",t,c.active_qubits(),fw);
            super::super::pingpong::terminal_pair(c,typ,sig,del,fw,false);return;
        }

        h7::with_cmp_shift((db, df), || {
            if t < carry_cfg().zone {
                double_add_nc(c, typ, del, sig, fw, proxy);
            } else {
                h7::double_add(c, typ, del, sig, fw, proxy);
            }
        });
    });
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ C10 record codec (B1 b1heo) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

#[path = "codec_probe.rs"]
pub mod codec_probe;
#[path = "codec_synth.rs"]
mod codec_synth;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum GState {
    Raw,
    P3,
    P5,
}

#[derive(Clone)]
struct Group {
    state: GState,
    synth: bool,
    a2: QubitId,
    a1: QubitId,
    a0: QubitId,
    h3: QubitId,
    l3: QubitId,
    b2: QubitId,
    b1: QubitId,
    b0: QubitId,
    m_g: Option<BitId>,
}

struct Tape {
    /// v025 A-2: per group, the shared product `h2 * typ3` waiting for that group's pack3.
    shared: Vec<Option<QubitId>>,
    raw: Vec<Option<(QubitId, QubitId)>>,
    groups: Vec<Option<Group>>,
    /// RB-1 L-T0: the codec starts at letter `off` (group g = letters 5g+off..5g+off+4); letters below `off`
    /// are held outside the tape.
    off: usize,
}

/// A packed record from a different group is idle for the entire field cell.
/// Its arbitrary quantum value and any deferred codec phase remain untouched.
fn dirty_cell(c:&mut Builder,tape:&Tape,t:usize,body:impl FnOnce(&mut Builder)){
    let current=t.checked_sub(tape.off).map(|x|x/5);
    let loan=tape.groups.iter().enumerate().find_map(|(g,p)|{
        if Some(g)==current{return None;}p.as_ref().map(|p|(g,p.a1))
    });
    if std::env::var("DIRTY_BOUNDARY_MODE").is_ok(){
        eprintln!("DIRTY_POOL\t{}\t{}\t{}\t{}",t,c.op_count(),loan.map_or(usize::MAX,|x|x.0),loan.map_or(u64::MAX,|x|x.1.0));
    }
    super::super::dirty_boundary_probe::with_tape(c,loan.map(|x|x.1),body);
}

fn to_hl(c: &mut Builder, (typ, s): (QubitId, QubitId)) -> (QubitId, QubitId) {
    c.cx(s, typ);
    c.x(typ);
    (s, typ)
}
fn from_hl(c: &mut Builder, h: QubitId, l: QubitId) -> (QubitId, QubitId) {
    c.x(l);
    c.cx(h, l);
    (l, h)
}
fn pair_pack(c: &mut Builder, h1: QubitId, l1: QubitId, h2: QubitId, l2: QubitId) {
    let anc = c.alloc_qubit();
    c.cx(h1, h2);
    c.ccx(h1, h2, anc);
    fredkin(c, anc, l1, l2);
    c.cx(anc, l2);
    c.cx(anc, h1);
    let m = c.alloc_bit();
    c.hmr(anc, m);
    c.cz_if(h2, l2, m);
    c.free_bit(m);
    c.free(anc);
}
fn pair_unpack(c: &mut Builder, h1: QubitId, l1: QubitId, h2: QubitId, l2: QubitId) {
    let anc = c.alloc_qubit();
    c.ccx(h2, l2, anc);
    c.cx(anc, h1);
    c.cx(anc, l2);
    fredkin(c, anc, l1, l2);
    let m = c.alloc_bit();
    c.hmr(anc, m);
    c.cz_if(h1, h2, m);
    c.free_bit(m);
    c.free(anc);
    c.cx(h1, h2);
}

impl Tape {
    fn new(r: usize) -> Self {
        Self::with_offset(r, 0)
    }
    fn with_offset(r: usize, off: usize) -> Self {
        Tape { shared: vec![None; (r - off).div_ceil(5)], raw: vec![None; r], groups: vec![None; (r - off).div_ceil(5)], off }
    }
    /// Group of letter `u` (u >= off).
    fn gid(&self, u: usize) -> usize {
        (u - self.off) / 5
    }
    fn get(&self, t: usize) -> (QubitId, QubitId) {
        self.raw[t].unwrap_or_else(|| panic!("tape trit {t} not raw"))
    }
    fn pack3(&mut self, c: &mut Builder, g: usize) {
        let t0 = 5 * g + self.off;
        let (h1, l1) = to_hl(c, self.raw[t0].take().unwrap());
        let (h2, l2) = to_hl(c, self.raw[t0 + 1].take().unwrap());
        let (h3, l3) = to_hl(c, self.raw[t0 + 2].take().unwrap());
        if truthy("HEO_CODEC_SYNTH") {
            let [a2,a1,a0,h3,l3]=codec_synth::pack_compatible_shared(c,[h1,l1,h2,l2,h3,l3],self.shared[g].take());
            self.groups[g]=Some(Group{state:GState::P3,synth:true,a2,a1,a0,h3,l3,b2:a2,b1:a2,b0:a2,m_g:None});
            return;
        }
        assert!(self.shared[g].is_none(), "shared product needs the synthesized codec");
        pair_pack(c, h1, l1, h2, l2);
        let (fwire, a2, a1, a0) = (h1, l1, h2, l2);
        fredkin(c, fwire, a1, h3);
        fredkin(c, fwire, a0, l3);
        c.cx(fwire, h3);
        c.cx(fwire, l3);
        let m = c.alloc_bit();
        c.hmr(fwire, m);
        c.cz_if(h3, l3, m);
        c.free_bit(m);
        c.free(fwire);
        self.groups[g] = Some(Group { state: GState::P3, synth: false, a2, a1, a0, h3, l3, b2: a2, b1: a2, b0: a2, m_g: None });
    }
    fn pack5(&mut self, c: &mut Builder, g: usize) {
        let t0 = 5 * g + self.off;
        let (h4, l4) = to_hl(c, self.raw[t0 + 3].take().unwrap());
        let (h5, l5) = to_hl(c, self.raw[t0 + 4].take().unwrap());
        let mut grp = self.groups[g].take().unwrap();
        assert_eq!(grp.state, GState::P3);
        pair_pack(c, h4, l4, h5, l5);
        let (gw, b2, b1, b0) = (h4, l4, h5, l5);
        for (x, y) in [(grp.a2, b2), (grp.h3, b1), (grp.l3, b0)] {
            fredkin(c, gw, x, y);
        }
        for x in [grp.a2, grp.h3, grp.l3] {
            c.cx(gw, x);
        }
        let m = c.alloc_bit();
        c.hmr(gw, m);
        c.free(gw);
        if truthy("HEO_CODEC_NODEFER") {
            // diagnostic: apply the pack CCZ now (2 extra Toffoli) so no phase is left in flight
            let anc = c.alloc_qubit();
            c.ccx(grp.a2, grp.h3, anc);
            c.cz_if(anc, grp.l3, m);
            c.ccx(grp.a2, grp.h3, anc);
            c.free(anc);
            c.free_bit(m);
        } else {
            grp.m_g = Some(m); // the pack CCZ, deferred to the next unpack5
        }
        grp.b2 = b2;
        grp.b1 = b1;
        grp.b0 = b0;
        grp.state = GState::P5;
        self.groups[g] = Some(grp);
    }
    fn unpack5(&mut self, c: &mut Builder, g: usize) {
        let t0 = 5 * g + self.off;
        let mut grp = self.groups[g].take().unwrap();
        assert_eq!(grp.state, GState::P5);
        let gw = c.alloc_qubit();
        let an2 = c.alloc_qubit();
        c.ccx(grp.a2, grp.h3, an2);
        c.ccx(an2, grp.l3, gw);
        if let Some(m) = grp.m_g.take() {
            c.z_if(gw, m);
            c.free_bit(m);
        }
        let m = c.alloc_bit();
        c.hmr(an2, m);
        c.cz_if(grp.a2, grp.h3, m);
        c.free_bit(m);
        c.free(an2);
        for x in [grp.a2, grp.h3, grp.l3] {
            c.cx(gw, x);
        }
        for (x, y) in [(grp.a2, grp.b2), (grp.h3, grp.b1), (grp.l3, grp.b0)] {
            fredkin(c, gw, x, y);
        }
        let (h4, l4, h5, l5) = (gw, grp.b2, grp.b1, grp.b0);
        pair_unpack(c, h4, l4, h5, l5);
        self.raw[t0 + 3] = Some(from_hl(c, h4, l4));
        self.raw[t0 + 4] = Some(from_hl(c, h5, l5));
        grp.state = GState::P3;
        self.groups[g] = Some(grp);
    }
    fn unpack3(&mut self, c: &mut Builder, g: usize) {
        let t0 = 5 * g + self.off;
        let grp = self.groups[g].take().unwrap();
        assert_eq!(grp.state, GState::P3);
        if grp.synth {
            let ([h1,l1,h2,l2,h3,l3],q)=codec_synth::unpack_compatible_retained(c,[grp.a2,grp.a1,grp.a0,grp.h3,grp.l3],REVERSE_CODEC_CAPTURE.with(|v|v.get()));
            assert!(self.shared[g].is_none());self.shared[g]=q;
            if q.is_some(){eprintln!("REVERSE_CODEC_CAPTURE group={g} t0={t0}");}
            self.raw[t0]=Some(from_hl(c,h1,l1));
            self.raw[t0+1]=Some(from_hl(c,h2,l2));
            self.raw[t0+2]=Some(from_hl(c,h3,l3));
            return;
        }
        let fwire = c.alloc_qubit();
        c.ccx(grp.h3, grp.l3, fwire);
        c.cx(fwire, grp.h3);
        c.cx(fwire, grp.l3);
        fredkin(c, fwire, grp.a1, grp.h3);
        fredkin(c, fwire, grp.a0, grp.l3);
        pair_unpack(c, fwire, grp.a2, grp.a1, grp.a0);
        self.raw[t0] = Some(from_hl(c, fwire, grp.a2));
        self.raw[t0 + 1] = Some(from_hl(c, grp.a1, grp.a0));
        self.raw[t0 + 2] = Some(from_hl(c, grp.h3, grp.l3));
    }
    fn state(&self, g: usize) -> GState {
        self.groups[g].as_ref().map_or(GState::Raw, |x| x.state)
    }
    fn ensure_raw(&mut self, c: &mut Builder, u: usize) {
        if u < self.off {
            return;
        }
        let g = self.gid(u);
        if self.state(g) == GState::P5 {
            self.unpack5(c, g);
        }
        if self.raw[u].is_none() && self.state(g) == GState::P3 {
            self.unpack3(c, g);
        }
    }
    fn ensure_group_raw(&mut self, c: &mut Builder, g: usize, r: usize) {
        for u in 5 * g + self.off..(5 * g + self.off + 5).min(r) {
            self.ensure_raw(c, u);
        }
    }
    /// Pack after tick t (B1 `pack_due`).
    fn pack_due(&mut self, c: &mut Builder, t: usize, r: usize, skip_last_group: bool) {
        if t < self.off {
            return;
        }
        let u = t - self.off;
        let g = u / 5;
        if u % 5 == 3 && !(skip_last_group && t + 2 >= r && 5 * g + self.off + 4 >= r) {
            self.pack3(c, g);
        }
        if u % 5 == 0 && u > 0 && self.state(g - 1) == GState::P3 {
            self.pack5(c, g - 1);
        }
    }
    /// B1 `repack`.
    fn repack(&mut self, c: &mut Builder, g: usize, r: usize) {
        let t0 = 5 * g + self.off;
        if t0 + 2 < r && self.state(g) == GState::Raw && self.raw[t0].is_some() {
            self.pack3(c, g);
        }
        if t0 + 4 < r && self.state(g) == GState::P3 && self.raw[t0 + 3].is_some() && self.raw[t0 + 4].is_some() {
            self.pack5(c, g);
        }
    }
    fn all_consumed(&self) -> bool {
        self.shared.iter().all(Option::is_none) && self.raw.iter().all(Option::is_none) && self.groups.iter().all(|g| g.is_none() || g.as_ref().unwrap().state == GState::Raw)
    }
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Terminal loan (B1): at park the rails are exactly (0, 1) Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

fn loan(c: &mut Builder, rails: Rails) -> (QubitId, (usize, usize)) {
    if carry_cfg().h0 || carry_cfg().fd {
        return loan_signed(c, rails);
    }
    let Rails { r1, r2 } = rails;
    c.cx(r1[0], r2[0]);
    c.x(r2[0]);
    let widths = (r1.len(), r2.len());
    c.free_vec(&r1[1..]);
    c.free_vec(&r2);
    (r1[0], widths)
}

/// B4: park state `(0, s)` with `s = +-1` (H0/FD starts). R2 = +1 is `0..01`, R2 = -1 is all ones: keep
/// R2's sign wire, clear bits 1..w-2 from it and bit 0 by X. Clifford only; still one loaned wire.
fn loan_signed(c: &mut Builder, rails: Rails) -> (QubitId, (usize, usize)) {
    let Rails { r1, r2 } = rails;
    let w2 = r2.len();
    let sgn = r2[w2 - 1];
    for &q in &r2[1..w2 - 1] {
        c.cx(sgn, q);
    }
    c.x(r2[0]);
    let widths = (r1.len(), w2);
    c.free_vec(&r1);
    c.free_vec(&r2[..w2 - 1]);
    (sgn, widths)
}

fn unloan_signed(c: &mut Builder, sgn: QubitId, widths: (usize, usize)) -> Rails {
    let r1 = c.alloc_qubits(widths.0);
    let mut r2 = c.alloc_qubits(widths.1 - 1);
    r2.push(sgn);
    c.x(r2[0]);
    for &q in &r2[1..widths.1 - 1] {
        c.cx(sgn, q);
    }
    Rails { r1, r2 }
}

fn unloan(c: &mut Builder, o: QubitId, widths: (usize, usize)) -> Rails {
    if carry_cfg().h0 || carry_cfg().fd {
        return unloan_signed(c, o, widths);
    }
    let mut r1 = vec![o];
    r1.extend(c.alloc_qubits(widths.0 - 1));
    let r2 = c.alloc_qubits(widths.1);
    c.x(r2[0]);
    c.cx(r1[0], r2[0]);
    Rails { r1, r2 }
}

/// RB-1 FB-RB1-3: swap the rails iff NOT o (o = o_{R-1}; o = 0 means the (+-1, 0) first-park state). Self-inverse.
fn park_orient(c: &mut Builder, rails: &Rails, o: QubitId) {
    assert_eq!(rails.r1.len(), rails.r2.len(), "park_orient: rails at one width");
    c.x(o);
    for i in 0..rails.r1.len() {
        fredkin(c, o, rails.r1[i], rails.r2[i]);
    }
    c.x(o);
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ L-PAR: park R2[0] = NOT R1[0] while the rails are idle Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

fn park_par(c: &mut Builder, k: &CarryCfg, rails: &mut Rails) {
    if k.park_parity {
        let q = rails.r2.remove(0);
        c.cx(rails.r1[0], q);
        c.x(q);
        c.free(q);
    }
}
fn unpark_par(c: &mut Builder, k: &CarryCfg, rails: &mut Rails) {
    if k.park_parity {
        let q = c.alloc_qubit();
        c.x(q);
        c.cx(rails.r1[0], q);
        rails.r2.insert(0, q);
    }
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ The two legs Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬

/// R4C-1: a RAIL width clamped at `HEO_RAIL_MAX` (identity by default; INTEGRATE-R3).
fn rw(w: usize) -> usize {
    w.min(carry_cfg().rail_max)
}
fn wpost(cfg: &HeoConfig, t: usize) -> usize {
    rw(if t + 1 < cfg.rounds() { cfg.ead[t].min(cfg.esw[t + 1]) } else { cfg.ead[t] })
}
/// B6 L-R1: R1's width after forward tick t (t >= 1): the halved rail needs at most rw(esw[t]) - 1 wires.
fn lr1_width(cfg: &HeoConfig, t: usize) -> usize {
    wpost(cfg, t).min(rw(cfg.esw[t]) - 1)
}
fn wbefore(cfg: &HeoConfig, t: usize) -> usize {
    if t == 0 { cfg.esw[0].max(N + 2) } else { wpost(cfg, t - 1) }
}

// Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬ Effort 11 FAMILY A (`HEO_FAMA=1`): C1 MAG-SLOT + S5 VENT-MBU + S1 half-empty Fredkin Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬Ã¢â€â‚¬
//
// Design and gate-level verification: 11-terms-in-place/work/R2-family1/ROUND2.md (a0_verify.py, both legs, exhaustive
// small p + 500k 256-bit walks per leg). Each rail tick converts HEO's PARKED boundary rails (L-PAR on) to the C1 frame by
// CNOTs only (C = R1[0]; X1[i] = R1[i]^s1; X2[0] = !R1[0]^s2; X2[i] = R2[i]^s2; the sign wires become the bit-0 wires),
// runs the magnitude tick, and converts back, so every other gadget (seeds, loan, head batch, cells, codec, L-R1) is
// untouched. Forward tick = HEO's CCX; reverse tick = HEO's - 1 (the vented borrow is the tape letter s, MBU-erased) -
// n_half (slot-1 structural-zero bits are Fredkins with a known-0 input: an AND forward, an MBU in reverse).

fn fama_on() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        let on = env_bool("HEO_FAMA", false);
        if on {
            eprintln!("HEO_FAMA on (C1 + S5 VENT-MBU + S1 half-empty Fredkin)");
        }
        on
    })
}

fn park_mbu_on() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        let on = env_bool("HEO_PARK_MBU", false);
        if on {
            eprintln!("HEO_PARK_MBU on (loan orient: CX + MBU; unloan orient: 1 CCX)");
        }
        on
    })
}

struct AState {
    c: QubitId,
    x1: Vec<QubitId>,
    x2: Vec<QubitId>,
}

/// Parked HEO rails -> family A (0 T).
fn a_from_heo(c: &mut Builder, rails: Rails) -> AState {
    let Rails { r1, r2 } = rails;
    let (n1, n2) = (r1.len(), r2.len());
    assert!(n1 >= 2 && n2 >= 1);
    let (s1w, s2w) = (r1[n1 - 1], r2[n2 - 1]);
    for &q in &r1[1..n1 - 1] {
        c.cx(s1w, q);
    }
    for &q in &r2[..n2 - 1] {
        c.cx(s2w, q);
    }
    let cw = r1[0];
    c.cx(cw, s1w);
    c.cx(cw, s2w);
    c.x(s2w);
    let mut x1 = vec![s1w];
    x1.extend_from_slice(&r1[1..n1 - 1]);
    let mut x2 = vec![s2w];
    x2.extend_from_slice(&r2[..n2 - 1]);
    AState { c: cw, x1, x2 }
}

/// Family A -> parked HEO rails, R1 at `w1` wires, R2 at `w2` (parked: w2 - 1 wires); 0 T. Registers are zero-extended.
fn a_to_heo(c: &mut Builder, st: AState, w1: usize, w2: usize) -> Rails {
    let AState { c: cw, mut x1, mut x2 } = st;
    while x1.len() < w1 - 1 {
        x1.push(c.alloc_qubit());
    }
    while x2.len() < w2 - 1 {
        x2.push(c.alloc_qubit());
    }
    assert!(x1.len() == w1 - 1 && x2.len() == w2 - 1, "a_to_heo: family A register wider than the HEO target");
    let (s1w, s2w) = (x1[0], x2[0]);
    c.cx(cw, s1w);
    c.x(s2w);
    c.cx(cw, s2w);
    for &q in &x1[1..] {
        c.cx(s1w, q);
    }
    for &q in &x2[1..] {
        c.cx(s2w, q);
    }
    let mut r1 = vec![cw];
    r1.extend_from_slice(&x1[1..]);
    r1.push(s1w);
    let mut r2 = x2[1..].to_vec();
    r2.push(s2w);
    Rails { r1, r2 }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ATop {
    Vent,
    Erase,
    Sum,
}

fn a_mbu(c: &mut Builder, q: QubitId, x: QubitId, y: QubitId) {
    let m = c.alloc_bit();
    c.hmr(q, m);
    c.cz_if(x, y, m);
    c.free_bit(m);
    c.free(q);
}

/// Family A ripple `b += a + cin` over w = b.len() bits, w - 1 owned carries. The top carry is vented into the fresh
/// wire `cout` (Vent) or is the content of `cout` and is MBU-erased (Erase: S5). `a` may be one bit short: its top
/// source bit is then the constant 1 (C1-SS, no pad wire).
fn a_ripple(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>, cout: QubitId, top: ATop,
            deferred: &mut Vec<(usize, BitId)>, top_release: bool) {
    let w = b.len();
    let short = a.len() + 1 == w;
    assert!(w >= 1 && (a.len() == w || short));
    let carries = if REVERSE_LOW.with(|v|v.borrow().is_some()) {reverse_carries(c,w-1,a[0],b[0],cin)}else{c.alloc_qubits(w-1)};
    let prev = |i: usize, cs: &[QubitId]| if i == 0 { cin } else { Some(cs[i - 1]) };
    for i in 0..w - 1 {
        carry_step(c, a[i], b[i], prev(i, &carries), carries[i]);
    }
    let t = w - 1;
    let p = prev(t, &carries);
    if !short {
        if let Some(p) = p {
            c.cx(p, a[t]);
            c.cx(p, b[t]);
        }
        match top {
            ATop::Sum => {},
            ATop::Vent => {
                if top_release {
                    // Existing released folded top: sum_top = !carry_out.
                    c.x(cout); c.cx(a[t], cout); c.cx(b[t], cout);
                } else { c.ccx(a[t], b[t], cout); }
                if let Some(p) = p { c.cx(p, cout); }
            }
            ATop::Erase => {
                if let Some(p) = p {
                    c.cx(p, cout);
                }
                if top_release { c.cx(b[t], cout); c.free(cout); }
                else { a_mbu(c, cout, a[t], b[t]); }
            }
        }
        if let Some(p) = p {
            c.cx(p, a[t]);
        }
        c.cx(a[t], b[t]);
    } else {
        match p {
            Some(p) => {
                c.cx(p, b[t]);
                match top {
                    ATop::Sum => {},
                    ATop::Vent => {
                        if top_release { c.cx(b[t], cout); }
                        else { c.x(p); c.ccx(p, b[t], cout); c.x(p); c.cx(p, cout); }
                    }
                    ATop::Erase => {
                        c.cx(p, cout);
                        if top_release { c.cx(b[t], cout); c.free(cout); }
                        else { c.x(p); a_mbu(c, cout, p, b[t]); c.x(p); }
                    }
                }
            }
            None => {
                if top != ATop::Sum { c.cx(b[t], cout); }
                if top == ATop::Erase {
                    c.free(cout);
                }
            }
        }
        c.x(b[t]);
    }
    for i in (0..w - 1).rev() {
        if let Some(pos) = deferred.iter().position(|&(k, _)| k == i) {
            let (_, m) = deferred.remove(pos);
            c.z_if(carries[i], m);
            c.free_bit(m);
        }
        unwind_carry_step(c, a[i], b[i], prev(i, &carries), carries[i]);
    }
}

/// `split_sizes` for family A's add shape (w - 1 owned carries; the last chunk's top carry lives in `cout`, already
/// counted live): the last cap is one lower than the wrapped planner's, and no split is needed while w - 1 <= room.
fn split_sizes_a(w: usize, room: usize, exact: bool) -> Result<Option<Vec<usize>>, ()> {
    if w <= room + 1 {
        return Ok(None);
    }
    for k in 1..64usize {
        let caps: Vec<isize> = if exact {
            let mut v: Vec<isize> = (0..k).map(|j| room as isize - j as isize).collect();
            v.push(room as isize - k as isize + 1);
            v
        } else {
            let mut v = vec![room as isize];
            v.extend(std::iter::repeat_n(room as isize - 1, k - 1));
            v.push(room as isize);
            v
        };
        if *caps.iter().min().unwrap() < 2 {
            return Err(());
        }
        let sum: isize = caps.iter().sum();
        if sum >= w as isize {
            let mut sizes: Vec<usize> = caps.iter().map(|&x| x as usize).collect();
            let mut excess = sum as usize - w;
            for s in sizes.iter_mut().take(k) {
                let cut = excess.min(*s - 2);
                *s -= cut;
                excess -= cut;
            }
            assert_eq!(excess, 0);
            return Ok(Some(sizes));
        }
    }
    Err(())
}

/// Servoed family A add (see [`rail_add_inner`]; same split modes, same boundary erasures).
#[allow(clippy::too_many_arguments)]
fn fama_add(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: QubitId, cout: QubitId, top: ATop, mode: SplitMode,
            tick_def: &mut Vec<(usize, BitId)>, label: &'static str, top_release: bool) {
    let w = b.len();
    let room = h7::cap().saturating_sub(c.active_qubits() as usize);
    if env_bool("K3B_RAIL_TRACE", false) {
        eprintln!("K3B_RAIL {label} w={w} room={room} mode={mode:?} def={} fama={top:?}", tick_def.len());
    }
    if !tick_def.is_empty() || mode == SplitMode::Apply {
        if w > room + 1 {
            ledger(|l| {
                l.mirror_over += 1;
                l.mirror_over_max = l.mirror_over_max.max(w - 1 - room);
            });
        }
        a_ripple(c, a, b, Some(cin), cout, top, tick_def, top_release);
        assert!(tick_def.is_empty(), "deferred phase did not name an owned carry");
        return;
    }
    let sizes = match split_sizes_a(w, room, mode == SplitMode::Exact) {
        Ok(None) => {
            a_ripple(c, a, b, Some(cin), cout, top, &mut Vec::new(), top_release);
            return;
        }
        Err(()) => {
            ledger(|l| l.infeasible += 1);
            a_ripple(c, a, b, Some(cin), cout, top, &mut Vec::new(), top_release);
            return;
        }
        Ok(Some(s)) => s,
    };
    ledger(|l| *l.splits.entry(label).or_insert(0) += sizes.len() - 1);
    let mut bounds = Vec::with_capacity(sizes.len());
    let mut lo = 0;
    for &s in &sizes {
        bounds.push((lo, lo + s));
        lo += s;
    }
    let k_win = carry_cfg().split_k;
    let mut carry_in = Some(cin);
    let mut kept_defer: Option<(QubitId, usize)> = None;
    let mut kept: Vec<(QubitId, usize, usize, Option<QubitId>)> = Vec::new();
    for (j, &(lo, hi)) in bounds.iter().enumerate() {
        let last = j + 1 == bounds.len();
        let out = if last { None } else { Some(c.alloc_qubit()) };
        if last {
            a_ripple(c, &a[lo..a.len().min(hi)], &b[lo..hi], carry_in, cout, top, &mut Vec::new(), top_release);
        } else {
            rail_ripple(c, &a[lo..hi], &b[lo..hi], carry_in, out, &mut Vec::new());
        }
        match mode {
            SplitMode::Defer => {
                if let Some((bw, bhi)) = kept_defer.take() {
                    let m = c.alloc_bit();
                    c.hmr(bw, m);
                    c.free(bw);
                    tick_def.push((bhi - 1, m));
                }
                if let Some(o) = out {
                    kept_defer = Some((o, hi));
                }
            }
            SplitMode::Approx => {
                if let Some((bw, plo, phi, pcin)) = kept.pop() {
                    if plo == 0 && phi - plo <= k_win {
                        erase_with_compare(c, bw, &b[plo..phi], &a[plo..phi], pcin);
                    } else {
                        let k = k_win.min(phi - plo);
                        erase_with_compare(c, bw, &b[phi - k..phi], &a[phi - k..phi], None);
                    }
                    c.free(bw);
                }
                if let Some(o) = out {
                    kept.push((o, lo, hi, carry_in));
                }
            }
            SplitMode::Exact => {
                if let Some(o) = out {
                    kept.push((o, lo, hi, carry_in));
                }
            }
            SplitMode::Apply => unreachable!(),
        }
        carry_in = out;
    }
    if mode == SplitMode::Exact {
        for &(bw, lo, hi, cin_j) in kept.iter().rev() {
            erase_with_compare(c, bw, &b[lo..hi], &a[lo..hi], cin_j);
            c.free(bw);
        }
    }
}

/// Slot-1 magnitude bits entering tick t >= 1 (FD: |X| < p/2 < 2^255 makes the top one structurally 0 at t = 1).
fn fama_w1(cfg: &HeoConfig, t: usize) -> usize {
    let k = carry_cfg();
    if t == 1 && k.fd {
        return N - 1;
    }
    let tp = t - 1;
    let w = if k.lr1 && tp > 0 && tp + 1 < cfg.rounds() { lr1_width(cfg, tp) } else { wpost(cfg, tp) };
    w - 1
}


/// Literal exporter for public ecdsa.fail resource research, no real-world key target.
pub fn rail_top_probe() {
 let args:Vec<String>=std::env::args().collect();let w:usize=args[1].parse().unwrap();let room:usize=args[2].parse().unwrap();let short=args[3]=="1";let inverse=args[4]=="1";let fixed=args[5]=="1";let path=&args[6];
 let mut c=Builder::new();let a=c.alloc_qubits(w-usize::from(short));let b=c.alloc_qubits(w);let cin=c.alloc_qubit();let cout=c.alloc_qubit();let base=c.active_qubits();
 std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS",(base as usize+room).to_string());
 let start=c.op_count();let top=if inverse{ATop::Erase}else{ATop::Vent};
 if inverse { for &q in &b {c.x(q);} }
 fama_add(&mut c,&a,&b,cin,cout,top,SplitMode::Exact,&mut Vec::new(),"top_probe",fixed);
 if inverse { for &q in &b {c.x(q);} }
 let t=c.report_totals().unwrap().1;let peak=c.peak_total();let(nq,nb)=c.i13_dims();let ops=c.take_ops();let data=ops[start..].iter().map(|o|format!("[{},{},{},{},{},{}]",o.kind as u8,o.q_target.0,o.q_control1.0,o.q_control2.0,o.c_target.0,o.c_condition.0)).collect::<Vec<_>>().join(",");
 let ai=a.iter().map(|q|q.0).collect::<Vec<_>>();let bi=b.iter().map(|q|q.0).collect::<Vec<_>>();
 std::fs::write(path,format!("{{\"w\":{w},\"room\":{room},\"short\":{short},\"inverse\":{inverse},\"fixed\":{fixed},\"nq\":{nq},\"nb\":{nb},\"base\":{base},\"Q\":{peak},\"T\":{t},\"regs\":{{\"a\":{:?},\"b\":{:?},\"cin\":[{}],\"cout\":[{}]}},\"ops\":[{data}]}}",ai,bi,cin.0,cout.0)).unwrap();
 println!("{{\"artifact\":\"{path}\",\"w\":{w},\"room\":{room},\"short\":{short},\"inverse\":{inverse},\"fixed\":{fixed},\"Q\":{peak},\"base\":{base},\"T\":{t}}}");
}

pub fn rail_alias_probe() {
 let args:Vec<String>=std::env::args().collect();let w:usize=args[1].parse().unwrap();let room:usize=args[2].parse().unwrap();let short=args[3]=="1";let inverse=args[4]=="1";let fixed=args[5]=="1";let path=&args[6];
 let mut c=Builder::new();let a=c.alloc_qubits(w-usize::from(short));let b=c.alloc_qubits(w);let cin=c.alloc_qubit();let cout=b[w-1];let base=c.active_qubits();
 std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS",(base as usize+room).to_string());
 let start=c.op_count();let top=ATop::Sum;
 if inverse { for &q in &b {c.x(q);} }
 fama_add(&mut c,&a,&b,cin,cout,top,SplitMode::Exact,&mut Vec::new(),"top_probe",fixed);
 if inverse { for &q in &b {c.x(q);} }
 let t=c.report_totals().unwrap().1;let peak=c.peak_total();let(nq,nb)=c.i13_dims();let ops=c.take_ops();let data=ops[start..].iter().map(|o|format!("[{},{},{},{},{},{}]",o.kind as u8,o.q_target.0,o.q_control1.0,o.q_control2.0,o.c_target.0,o.c_condition.0)).collect::<Vec<_>>().join(",");
 let ai=a.iter().map(|q|q.0).collect::<Vec<_>>();let bi=b.iter().map(|q|q.0).collect::<Vec<_>>();
 std::fs::write(path,format!("{{\"w\":{w},\"room\":{room},\"short\":{short},\"inverse\":{inverse},\"fixed\":{fixed},\"nq\":{nq},\"nb\":{nb},\"base\":{base},\"Q\":{peak},\"T\":{t},\"alias\":true,\"regs\":{{\"a\":{:?},\"b\":{:?},\"cin\":[{}]}},\"ops\":[{data}]}}",ai,bi,cin.0)).unwrap();
 println!("{{\"artifact\":\"{path}\",\"w\":{w},\"room\":{room},\"short\":{short},\"inverse\":{inverse},\"fixed\":{fixed},\"Q\":{peak},\"base\":{base},\"T\":{t}}}");
}

/// Family A forward tick t >= 1 on parked HEO rails; returns the parked post-tick rails and the tape pair (typ_t, s_t).
#[allow(clippy::too_many_arguments)]
fn fama_fwd(c: &mut Builder, cfg: &HeoConfig, rails: Rails, typ_prev: Option<QubitId>, t: usize, o0_erase: bool,
            mode: SplitMode, def: &mut Vec<(usize, BitId)>, label: &'static str,
            mut mid: Option<&mut dyn FnMut(&mut Builder, QubitId)>,
            keep_low: bool, prior: Option<(QubitId, QubitId)>) -> (Rails, QubitId, QubitId, Option<QubitId>, Option<QubitId>) {
    // v025 I-3 (HEO_CELL_INSIDE): `mid` runs the payload cell after the parity route and the
    // previous-letter fix (typ = o_t is final) but BEFORE the add widens the rails and allocates
    // the tape sign wire s_t, so the cell sees fewer live wires than it does after the tick.
    // v025 A-2 (HEO_CARRY_CODEC): `keep_low` retains this tick's first carry (returned as the
    // fourth value); `prior = (u, s_prev)` consumes the previous tick's retained carry into the
    // codec's shared product (returned as the fifth value), replacing the bit-0 Fredkin.
    let k = carry_cfg();
    let r = cfg.rounds();
    let (msw, mad) = (rw(cfg.esw[t]) - 1, rw(cfg.ead[t]) - 1);
    let mut st = a_from_heo(c, rails);
    let w1 = fama_w1(cfg, t);
    while st.x1.len() > w1 {
        let q = st.x1.pop().unwrap();
        c.free(q);
    }
    let cw = st.c;
    let mpost = st.x2.len();
    assert!(st.x1.len() == w1 && w1 <= mpost && mpost <= msw, "fama_fwd t={t}: w1={} mpost={mpost} msw={msw}", st.x1.len());
    // v025 I-3b (HEO_CELL_INSIDE=2): defer the S1 half-empty ANDs (fresh z wires) until after the
    // mid-tick cell, so the cell also sees those wires free. Not at the O0-erase tick (t = 1).
    // Only defer S1 when its original source survives the normal pre-cell trim.
    // Then each deferred AND is one genuinely absent live helper at the hook;
    // crossing an ead shrink would instead keep the original source alive.
    let defer_s1 = mid.is_some() && !o0_erase && (env_usize("HEO_CELL_INSIDE", 0) >= 2
        || (env_bool("HEO_CELL_HELPER_S1", false) && label=="divfwd" && mpost <= mad
            && [5usize,7,8,260,272].contains(&t)
            // The mid callback packs old letters at u%5=0 or3. It may change
            // typ_prev's physical wire there, so it must not be reread afterward.
            && t>=usize::from(k.lt0) && ![0usize,3].contains(&((t-usize::from(k.lt0))%5))));
    if mid.is_some() && env_bool("HEO_CELL_HELPER_TRACE",false) {eprintln!("CELL_HELPER_FRAME tick={t} w1={w1} mpost={mpost} mad={mad} defer={defer_s1} saved={} entry={}", if defer_s1{mpost-w1}else{0},c.active_qubits());}
    // The existing pre-add zero-free requires (1-cw)*x2[mad] = 0.
    // On that same domain x2[mad] already equals cw*x2[mad], so transfer its
    // physical wire to slot 1. The ordinary independent inverse still restores
    // slot 2 via CX and pays the standard AND measurement phase correction.
    let output_alias = env_bool("HEO_S1_OUTPUT_ALIAS", false) && !defer_s1
        && w1 <= mad && mpost == mad + 1;
    if !defer_s1 {
        for j in w1..mpost {
            if output_alias && j == mad {
                let z = st.x2.pop().unwrap();
                st.x1.push(z);
                continue;
            }
            // S1: slot 1 is structurally 0 here, so the Fredkin is an AND into a fresh wire (MBU'd by the reverse)
            let z = c.alloc_qubit();
            c.ccx(cw, st.x2[j], z);
            c.cx(z, st.x2[j]);
            st.x1.push(z);
        }
    }
    let shared = prior.map(|(u, s_prev)| {
        // u = c * D_old; sigma_prev converts it to the current sign
        // difference, and magnitude bit0 routing contributes the extra c.
        let q = c.alloc_qubit(); c.ccx(cw, s_prev, q);
        c.cx(q, u); c.cx(cw, u);
        c.cx(u, st.x1[0]); c.cx(u, st.x2[0]);
        c.cx(st.x2[0], st.x1[0]); a_mbu(c, u, cw, st.x1[0]); c.cx(st.x2[0], st.x1[0]);
        q
    });
    for j in usize::from(shared.is_some())..w1 {
        if env_bool("HEO_FREDKIN_OUTPUT_ALIAS", false) && !defer_s1
            && w1 == mpost && mpost == mad + 1 && j == mad {
            // On the existing zero-output domain the surviving route is a XOR b.
            // The old first wire is (1-cw) times that survivor; erase it with its
            // literal HMR correction before the type and payload callback change.
            let old_first = st.x1[j];
            let survivor = st.x2.pop().unwrap();
            c.cx(old_first, survivor);
            c.x(cw); a_mbu(c, old_first, cw, survivor); c.x(cw);
            st.x1[j] = survivor;
        } else {
            fredkin(c, cw, st.x1[j], st.x2[j]);
        }
    }
    let AState { c: _, mut x1, mut x2 } = st;
    if o0_erase {
        // B7 O0, ported: linear part r2[1]^r2[2]^e2[0]^e2[1] == x2[1]^x2[2]^x1[1]^x1[2] (pends cancel); the AND's CZ
        // runs on r2[1] = x2[1]^!x2[0] and e2[0] = x1[1]^x1[0], conjugated in and out.
        let o0 = typ_prev.expect("O0 erase needs the o_0 wire");
        assert!(x1.len() >= 3 && x2.len() >= 3);
        c.cx(o0, cw);
        c.cx(cw, o0);
        c.cx(x2[1], o0);
        c.cx(x2[2], o0);
        c.cx(x1[1], o0);
        c.cx(x1[2], o0);
        if o0_kp() {
            c.x(o0);
        }
        c.cx(x2[0], x2[1]);
        c.x(x2[1]);
        c.cx(x1[0], x1[1]);
        a_mbu(c, o0, x2[1], x1[1]);
        c.cx(x1[0], x1[1]);
        c.x(x2[1]);
        c.cx(x2[0], x2[1]);
    } else if let Some(tp) = typ_prev {
        c.cx(tp, cw);
    }
    if defer_s1 {
        // The cell reads o_t (cw now); the S1 ANDs need the parity c = cw XOR typ_prev.
        if let Some(m) = mid.as_mut() {
            m(c, cw);
        }
        if let Some(tp) = typ_prev { c.cx(tp, cw); }
        for j in w1..mpost {
            let z = c.alloc_qubit();
            c.ccx(cw, x2[j], z);
            c.cx(z, x2[j]);
            x1.push(z);
        }
        if let Some(tp) = typ_prev { c.cx(tp, cw); }
    }
    let p1 = x1[0];
    let mut hs: Vec<QubitId> = x1[1..].to_vec();
    while hs.len() > mad {
        let q = hs.pop().unwrap();
        c.free(q);
    }
    while x2.len() > mad {
        let q = x2.pop().unwrap();
        c.free(q);
    }
    if !defer_s1 {
        if let Some(m) = mid.as_mut() {
            m(c, cw);
        }
    }
    while x2.len() < mad {
        x2.push(c.alloc_qubit());
    }
    let mut pads = 0;
    while hs.len() + 1 < mad {
        hs.push(c.alloc_qubit());
        pads += 1;
    }
    let top_alias = env_bool("HEO_RAIL_TOP_ALIAS", false) && mad > wpost(cfg, t) - 1;
    let cout = if top_alias { x2[mad-1] } else { c.alloc_qubit() };
    c.x_all(&hs);
    c.x(p1);
    let top_release = env_bool("HEO_RAIL_TOP_RELEASE", false) && mad > wpost(cfg, t) - 1;
    if top_release { eprintln!("RAIL_TOP_RELEASE {label} direction=forward tick={t} w={mad} wp={} short={}", wpost(cfg,t), hs.len()+1==x2.len()); }
    if keep_low { shared_low_start(hs[0], x2[0], p1); }
    fama_add(c, &hs, &x2, p1, cout, if top_alias {ATop::Sum} else {ATop::Vent}, mode, def, label, top_release);
    let retained = keep_low.then(shared_low_finish);
    c.x(p1);
    c.x_all(&hs);
    if !top_alias { c.x(cout); } // s_t = sum_top = NOT carry on released-top promise.
    for &q in &x2 { if q != cout { c.cx(cout, q); } }
    if let Some(&h0) = hs.first() {
        c.cx(h0, p1); // p1's wire becomes C_{t+1}
    }
    for _ in 0..pads {
        let q = hs.pop().unwrap();
        c.free(q);
    }
    let wp = wpost(cfg, t);
    let w1a = if k.lr1 && t > 0 && t + 1 < r { lr1_width(cfg, t) } else { wp };
    while hs.len() > w1a - 1 {
        let q = hs.pop().unwrap();
        c.free(q);
    }
    while x2.len() > wp - 1 {
        let q = x2.pop().unwrap();
        if !top_alias || q != cout { c.free(q); }
    }
    let rails = a_to_heo(c, AState { c: p1, x1: hs, x2 }, w1a, wp);
    (rails, cw, cout, retained, shared)
}

/// Family A reverse tick t >= 1: exact mirror of [`fama_fwd`]; consumes the tape pair. Returns parked rails at
/// wbefore(t) and the rebuilt o_0 wire (div O0 at t = 1).
#[allow(clippy::too_many_arguments)]
fn fama_rev(c: &mut Builder, cfg: &HeoConfig, rails: Rails, typ: QubitId, s: QubitId, typ_prev: Option<QubitId>, t: usize,
            o0_rebuild: bool, mode: SplitMode, def: &mut Vec<(usize, BitId)>, label: &'static str,
            mut mid: Option<&mut dyn FnMut(&mut Builder, QubitId)>, incoming:Option<QubitId>, codec:Option<(QubitId,QubitId)>) -> (Rails, Option<QubitId>, Option<QubitId>) {
    // v025 I-3 (HEO_CELL_INSIDE): `mid` runs the payload cell after the inverse add has consumed the
    // tape sign wire s and the pads are freed, but before the rails regrow and before typ is folded
    // into the parity wire (typ = o_t still holds the letter the cell reads).
    let (msw, mad) = (rw(cfg.esw[t]) - 1, rw(cfg.ead[t]) - 1);
    let w1 = fama_w1(cfg, t);
    let mpost = wpost(cfg, t - 1) - 1;
    assert!(w1 <= mpost && mpost <= msw, "fama_rev t={t}");
    let hs_fwd = (mpost - 1).min(mad);
    let pads = (mad - 1).saturating_sub(hs_fwd);
    let hs_len = hs_fwd + pads;
    let AState { c: p1, x1: mut hs, mut x2 } = a_from_heo(c, rails);
    while hs.len() > hs_len {
        let q = hs.pop().unwrap();
        c.free(q);
    }
    while hs.len() < hs_len {
        hs.push(c.alloc_qubit());
    }
    assert!(x2.len() <= mad, "fama_rev t={t}: slot 2 wider than the add");
    let top_alias = env_bool("HEO_RAIL_TOP_ALIAS", false) && mad > wpost(cfg, t) - 1;
    while x2.len() < mad - usize::from(top_alias) { x2.push(c.alloc_qubit()); }
    if top_alias { x2.push(s); }
    if let Some(&h0) = hs.first() {
        c.cx(h0, p1);
    }
    for &q in &x2 { if q != s { c.cx(s, q); } }
    if !top_alias { c.x(s); } // alias becomes carry upon target complement below.
    c.x_all(&hs);
    c.x(p1);
    c.x_all(&x2);
    let top_release = env_bool("HEO_RAIL_TOP_RELEASE", false) && mad > wpost(cfg, t) - 1;
    if top_release { eprintln!("RAIL_TOP_RELEASE {label} direction=reverse tick={t} w={mad} wp={} short={}", wpost(cfg,t), hs.len()+1==x2.len()); }
    if let Some(q)=incoming {assert!(mode==SplitMode::Apply && mid.is_none());REVERSE_LOW.with(|v|{assert!(v.borrow().is_none());*v.borrow_mut()=Some((hs[0],x2[0],p1,q));});}
    fama_add(c, &hs, &x2, p1, s, if top_alias {ATop::Sum} else {ATop::Erase}, mode, def, label, top_release); // S5: the tape letter is MBU-erased at the top
    assert!(REVERSE_LOW.with(|v|v.borrow().is_none()),"shared reverse carry was not consumed");
    c.x_all(&x2);
    c.x(p1);
    c.x_all(&hs);
    let mut rebuilt = None;
    if o0_rebuild {
        assert!(typ_prev.is_none() && hs.len() >= 2 && x2.len() >= 3);
        let o0 = c.alloc_qubit();
        c.cx(x2[0], x2[1]);
        c.x(x2[1]);
        c.cx(p1, hs[0]);
        c.ccx(x2[1], hs[0], o0);
        c.cx(p1, hs[0]);
        c.x(x2[1]);
        c.cx(x2[0], x2[1]);
        c.cx(x2[1], o0);
        c.cx(x2[2], o0);
        c.cx(hs[0], o0);
        c.cx(hs[1], o0);
        if o0_kp() {
            c.x(o0);
        }
        c.cx(typ, o0);
        c.cx(o0, typ);
        rebuilt = Some(o0);
    }
    for _ in 0..pads {
        let q = hs.pop().unwrap();
        c.free(q);
    }
    while x2.len() > mpost {
        let q = x2.pop().unwrap();
        c.free(q);
    }
    if let Some(m) = mid.as_mut() {
        m(c, typ);
    }
    while hs.len() < mpost - 1 {
        hs.push(c.alloc_qubit());
    }
    while x2.len() < mpost {
        x2.push(c.alloc_qubit());
    }
    if let Some(tp) = typ_prev {
        c.cx(tp, typ);
    }
    let cw = typ;
    let mut x1 = vec![p1];
    x1.extend(hs);
    let retained=codec.map(|(q,sign_prev)| {
        assert!(mid.is_none());let u=c.alloc_qubit();
        c.cx(x2[0],x1[0]);c.ccx(cw,x1[0],u);c.cx(x2[0],x1[0]);
        c.cx(u,x1[0]);c.cx(u,x2[0]);
        c.cx(q,u);c.cx(cw,u);
        // q=h2*typ3=cw*sign_prev, since typ_prev*sign_prev=0.
        a_mbu(c,q,cw,sign_prev);u
    });
    for j in usize::from(retained.is_some())..w1 {fredkin(c,cw,x1[j],x2[j]);}
    for j in (w1..mpost).rev() {
        c.cx(x1[j], x2[j]);
        a_mbu(c, x1[j], cw, x2[j]); // S1: the half bit is the persistent AND C & X2[j]
    }
    x1.truncate(w1);
    let wb = wbefore(cfg, t);
    (a_to_heo(c, AState { c: cw, x1, x2 }, wb, wb), rebuilt, retained)
}

/// HEO_PARK_MBU loan orient: at park the rails are (0, +-1) with o = 1 or (+-1, 0) with o = 0. r2 ^= r1 makes r2 = +-1,
/// and r1 == NOT o AND r2 bitwise is MBU-erased (0 T); clean wires are re-issued for loan_signed. Accepts exactly the
/// shots park_orient accepts.
fn park_mbu_loan(c: &mut Builder, rails: &mut Rails, o: QubitId) {
    assert_eq!(rails.r1.len(), rails.r2.len(), "park_mbu_loan: rails at one width");
    for i in 0..rails.r1.len() {
        c.cx(rails.r1[i], rails.r2[i]);
    }
    c.x(o);
    for i in 0..rails.r1.len() {
        let q = rails.r1[i];
        a_mbu(c, q, o, rails.r2[i]);
        rails.r1[i] = c.alloc_qubit();
    }
    c.x(o);
}

/// HEO_PARK_MBU unloan orient, after unloan_signed rebuilt (0, +-1): r1 = NOT o AND r2 (1 CCX + fan-out), r2 ^= r1.
fn park_mbu_unloan(c: &mut Builder, rails: &mut Rails, o: QubitId) {
    let w = rails.r1.len();
    assert!(w >= 2 && rails.r2.len() == w);
    c.x(o);
    c.cx(o, rails.r1[0]);
    c.ccx(o, rails.r2[w - 1], rails.r1[1]);
    for i in 2..w {
        c.cx(rails.r1[1], rails.r1[i]);
    }
    c.x(o);
    for i in 0..w {
        c.cx(rails.r1[i], rails.r2[i]);
    }
}

struct Walk {
    /// v025 A-2: the previous tick's retained first carry (multiply forward pass only).
    pending_low: Option<QubitId>,
    rails: Option<Rails>,
    tape: Tape,
    deferred: Vec<Vec<(usize, BitId)>>,
    /// B4 FD multiply leg: X's post-seed sign (the parity b), carried to the head batch's end.
    bwire: Option<QubitId>,
    /// RB-1 L-T0 (division leg): o_0 on one raw wire, outside the tape.
    o0: Option<QubitId>,
    /// This leg runs L-T0.
    lt0: bool,
    /// RB-1 L-T0 on the multiply leg: Y's post-seed sign, carried from the head batch to the unseed.
    ywire: Option<QubitId>,
    /// B7 O0 / O0-M: forward tick 1 erases the raw o_0 wire.
    o0_erase: bool,
    /// B7 O0 (division leg only): reverse tick 1 rebuilds o_0 (the mul leg re-creates it at the head-batch end).
    o0_rebuild: bool,
}

impl Walk {
    /// typ of letter `u` (the raw o_0 wire under L-T0 for u = 0).
    fn typ_of(&self, u: usize) -> QubitId {
        if u == 0 && self.lt0 { self.o0.unwrap() } else { self.tape.get(u).0 }
    }
}

fn forward_tick(c: &mut Builder, cfg: &HeoConfig, k: &CarryCfg, w: &mut Walk, x: &[QubitId], t: usize,
                label: &'static str, mid: Option<&mut dyn FnMut(&mut Builder, &mut Tape, QubitId)>) -> (QubitId, QubitId) {
    assert!(mid.is_none() || t > 0, "HEO_CELL_INSIDE: no mid-tick cell at the seed tick");
    let (typ, s) = if t == 0 && k.fd {
        let lt0 = w.lt0;
        let (mut rails, typ, s) = book(c, "seeds", "fd seed", 0, |c| fd_seed(c, x, wpost(cfg, 0), !lt0));
        park_par(c, k, &mut rails);
        w.rails = Some(rails);
        if lt0 {
            // L-T0: o_0 stays raw; no tape letter 0 (s is unused at t = 0 by the division leg).
            w.o0 = Some(typ);
            return (typ, typ);
        }
        (typ, s.unwrap())
    } else if t == 0 && k.h0 {
        let (mut rails, typ, s) = book(c, "seeds", "h0 seed", 0, |c| h0_seed(c, x, wpost(cfg, 0)));
        park_par(c, k, &mut rails);
        w.rails = Some(rails);
        (typ, s)
    } else if t == 0 && k.g3 {
        let (mut rails, typ, s) = book(c, "seeds", "g3 seed", 0, |c| g3_seed(c, x, wpost(cfg, 0)));
        park_par(c, k, &mut rails);
        w.rails = Some(rails);
        (typ, s)
    } else {
        if t == 0 {
            let mut rails = seed_base(c, x, wbefore(cfg, 0));
            park_par(c, k, &mut rails);
            w.rails = Some(rails);
        }
        let prev = if t > 0 { Some(w.typ_of(t - 1)) } else { None };
        let o0e = t == 1 && w.lt0 && w.o0_erase;
        if fama_on() && t > 0 {
            assert!(k.park_parity, "HEO_FAMA needs L-PAR (HEO_PARK_PARITY on)");
            let taken = w.rails.take().unwrap();
            let mut def = Vec::new();
            // v025 A-2: shared sign/carry/codec product, multiply forward pass only (rails-only pass,
            // room ~287: the retained carry wire crosses no field cell). Retain at letter u%5==1,
            // consume at u%5==2, erase at that group's pack3.
            let mul_leg = label == "mulfwd";
            let shared_on = mul_leg && env_bool("HEO_CARRY_CODEC", false) && truthy("HEO_CODEC_SYNTH");
            let u = t.checked_sub(w.tape.off);
            let keep_low = shared_on && u.is_some_and(|u| u % 5 == 1) && t + 2 < cfg.rounds();
            let pl = w.pending_low.take();
            let prior = pl.map(|q| (q, w.tape.get(t - 1).1));
            let (nr, typ, s, retained, shared) = {
                let tape = &mut w.tape;
                let mut adapter = mid.map(|m| move |c: &mut Builder, typ: QubitId| m(c, tape, typ));
                let hook: Option<&mut dyn FnMut(&mut Builder, QubitId)> = match adapter.as_mut() {
                    Some(f) => Some(f),
                    None => None,
                };
                fama_fwd(c, cfg, taken, prev, t, o0e, k.fwd_split, &mut def, label, hook, keep_low, prior)
            };
            w.pending_low = retained;
            if let Some(q) = shared {
                let g = w.tape.gid(t);
                assert!(w.tape.shared[g].is_none(), "shared product already pending for group {g}");
                w.tape.shared[g] = Some(q);
            }
            w.rails = Some(nr);
            if o0e {
                w.o0 = None;
            }
            w.deferred[t] = def;
            w.tape.raw[t] = Some((typ, s));
            return (typ, s);
        }
        let rails = w.rails.as_mut().unwrap();
        unpark_par(c, k, rails);
        let mut def = Vec::new();
        let pair = fwd_tick_c(c, rails, prev, rw(cfg.esw[t]), rw(cfg.ead[t]), k.fwd_split, &mut def, label, o0e);
        if let Some(m) = mid {
            // Non-FAMA rails: no mid-tick hook exists; run the cell after the tick as before.
            m(c, &mut w.tape, pair.0);
        }
        if o0e {
            w.o0 = None;
        }
        w.deferred[t] = def;
        resize(c, &mut rails.r1, wpost(cfg, t));
        resize(c, &mut rails.r2, wpost(cfg, t));
        if k.lr1 && t > 0 && t + 1 < cfg.rounds() {
            // B6 L-R1: R1 = X >> 1 fits rw(esw[t]) - 1 wires by construction (exact, Clifford only).
            resize(c, &mut rails.r1, lr1_width(cfg, t));
        }
        park_par(c, k, rails);
        pair
    };
    w.tape.raw[t] = Some((typ, s));
    (typ, s)
}

/// Reverse tick t (pops the trit). Returns the denominator wires at t == 0.
fn reverse_tick(c: &mut Builder, cfg: &HeoConfig, k: &CarryCfg, w: &mut Walk, t: usize, mode: SplitMode,
                label: &'static str, mid: Option<&mut dyn FnMut(&mut Builder, &Tape, QubitId)>) -> Option<Vec<QubitId>> {
    assert!(mid.is_none() || t > 0, "HEO_CELL_INSIDE: no mid-tick cell at the unseed tick");
    let share=label=="divrev" && env_bool("HEO_REVERSE_CARRY_CODEC",false) && truthy("HEO_CODEC_SYNTH");
    REVERSE_CODEC_CAPTURE.with(|v|v.set(share));
    book(c, "codec", "rev codec", t, |c| {
        w.tape.ensure_raw(c, t);
        if t > 0 {
            w.tape.ensure_raw(c, t - 1);
        }
    });
    REVERSE_CODEC_CAPTURE.with(|v|v.set(false));
    if t == 0 && w.lt0 {
        let typ = w.o0.take().unwrap();
        let mut rails = w.rails.take().unwrap();
        unpark_par(c, k, &mut rails);
        if let Some(bw) = w.bwire.take() {
            c.cx(*rails.r1.last().unwrap(), bw);
            c.free(bw);
        }
        if let Some(yw) = w.ywire.take() {
            c.cx(*rails.r2.last().unwrap(), yw);
            c.free(yw);
        }
        let leg = if label.starts_with("mul") { super::super::back_seam::Leg::Mul } else { super::super::back_seam::Leg::Div };
        return Some(book(c, "seeds", "fd unseed", 0, |c| fd_unseed(c, rails, typ, None, leg)));
    }
    let (typ, s) = w.tape.raw[t].take().unwrap();
    if t == 0 && k.h0 {
        let mut rails = w.rails.take().unwrap();
        unpark_par(c, k, &mut rails);
        return Some(book(c, "seeds", "h0 unseed", 0, |c| h0_unseed(c, rails, typ, s)));
    }
    if t == 0 && k.fd {
        let mut rails = w.rails.take().unwrap();
        unpark_par(c, k, &mut rails);
        if let Some(bw) = w.bwire.take() {
            c.cx(*rails.r1.last().unwrap(), bw);
            c.free(bw);
        }
        let leg = if label.starts_with("mul") { super::super::back_seam::Leg::Mul } else { super::super::back_seam::Leg::Div };
        return Some(book(c, "seeds", "fd unseed", 0, |c| fd_unseed(c, rails, typ, Some(s), leg)));
    }
    if t == 0 && k.g3 {
        let mut rails = w.rails.take().unwrap();
        unpark_par(c, k, &mut rails);
        return Some(book(c, "seeds", "g3 unseed", 0, |c| g3_unseed(c, rails, typ, s)));
    }
    let o0r = t == 1 && w.lt0 && w.o0_rebuild && w.o0.is_none();
    let tp = if t > 0 && !o0r { Some(w.typ_of(t - 1)) } else { None };
    if fama_on() && t > 0 {
        assert!(k.park_parity, "HEO_FAMA needs L-PAR (HEO_PARK_PARITY on)");
        let taken = w.rails.take().unwrap();
        let mut def = std::mem::take(&mut w.deferred[t]);
        let incoming=if share{w.pending_low.take()}else{None};
        let codec=if share && t>=w.tape.off && (t-w.tape.off)%5==2 {
            let g=w.tape.gid(t);w.tape.shared[g].take().map(|q|(q,w.tape.get(t-1).1))
        }else{None};
        let (nr, rebuilt, retained) = {
            let tape = &w.tape;
            let mut adapter = mid.map(|m| move |c: &mut Builder, typ: QubitId| m(c, tape, typ));
            let hook: Option<&mut dyn FnMut(&mut Builder, QubitId)> = match adapter.as_mut() {
                Some(f) => Some(f),
                None => None,
            };
            fama_rev(c, cfg, taken, typ, s, tp, t, o0r, mode, &mut def, label, hook, incoming, codec)
        };
        assert!(def.is_empty(), "fama_rev: deferred phases left over");
        assert!(w.pending_low.is_none());w.pending_low=retained;
        w.rails = Some(nr);
        if o0r {
            w.o0 = rebuilt;
        }
        return None;
    }
    if let Some(m) = mid {
        // Non-FAMA rails: no mid-tick hook exists; run the cell before the tick as before.
        m(c, &w.tape, typ);
    }
    let rails = w.rails.as_mut().unwrap();
    unpark_par(c, k, rails);
    resize(c, &mut rails.r1, rw(cfg.ead[t]));
    resize(c, &mut rails.r2, rw(cfg.ead[t]));
    let mut def = std::mem::take(&mut w.deferred[t]);
    // K3b: R1 = X >> 1 fits rw(esw[t]) - 1 bits, so its top wire is a sign copy when the add width reaches esw[t],
    // or when the regrow wpost(t) -> ead[t] above created it (L-R1's trim only lowers the start of that regrow).
    let top_copy = rw(cfg.ead[t]) >= rw(cfg.esw[t]) || rw(cfg.ead[t]) > wpost(cfg, t);
    let rebuilt = rev_tick_c(c, rails, typ, s, tp, rw(cfg.esw[t]), wbefore(cfg, t), mode, &mut def, label, o0r, top_copy);
    if o0r {
        w.o0 = rebuilt;
    }
    if t == 0 {
        let rails = w.rails.take().unwrap();
        return Some(unseed_base(c, rails));
    }
    park_par(c, k, rails);
    None
}

/// `numerator /= denominator (mod p)`.
pub fn divide(c: &mut Builder, numerator: &[QubitId], denominator: &[QubitId]) {
    let cfg = config();
    let k = carry_cfg();
    assert_eq!(cfg.seed, super::Seed::Base, "carry schedule: base seed only (F-B3b-1)");
    let r = cfg.rounds();
    let sig = numerator;
    let mut del: Option<Vec<QubitId>> = None;
    let off = usize::from(k.lt0);
    let mut w = Walk { pending_low: None, rails: None, tape: Tape::with_offset(r, off), deferred: vec![Vec::new(); r], bwire: None,
                       o0: None, lt0: k.lt0, ywire: None, o0_erase: k.o0_dec && k.lt0, o0_rebuild: k.o0_dec && k.lt0 };
    c.set_phase("heo_div_fwd");
    for t in 0..r {
        if env_bool("SKYWALK_CUT_MAP", false) && [200, 254].contains(&t) {
            let rails = w.rails.as_ref().unwrap();
            let r1: Vec<u64> = rails.r1.iter().map(|q| q.0).collect();
            let r2: Vec<u64> = rails.r2.iter().map(|q| q.0).collect();
            let sig_ids: Vec<u64> = sig.iter().map(|q| q.0).collect();
            let del_ids: Vec<u64> = del.as_ref().unwrap().iter().map(|q| q.0).collect();
            let prev = w.typ_of(t - 1).0;
            let extra: Vec<u64> = [w.bwire, w.o0, w.ywire].iter().filter_map(|q| q.map(|x| x.0)).collect();
            eprintln!("SKYWALK_CUT_MAP {{\"cut\":{},\"live\":{},\"op\":{},\"r1\":{:?},\"r2\":{:?},\"sig\":{:?},\"del\":{:?},\"previous_typ\":{},\"extra\":{:?},\"entry_common_width\":{},\"current_esw\":{},\"current_ead\":{},\"previous_lr1_width\":{},\"park_parity\":{},\"r2d\":{}}}", t, c.active_qubits(), c.op_count(), r1, r2, sig_ids, del_ids, prev, extra, wbefore(cfg, t), rw(cfg.esw[t]), rw(cfg.ead[t]), lr1_width(cfg,t-1), k.park_parity, k.r2d);
        }
        // v025 I-3: with HEO_CELL_INSIDE the ordinary fused cell (and the codec pack due at this
        // tick, which only needs letters < t) run inside the rail tick, before the add.
        let inside_cell = env_bool("HEO_CELL_INSIDE", false) && t > 0 && t < k.r2d
            && !(t == 1 && k.h0) && !(t == 1 && k.g1b && !k.fd);
        let (typ, s) = if inside_cell {
            let d: Vec<QubitId> = del.as_ref().unwrap().clone();
            let mut mid = |c: &mut Builder, tape: &mut Tape, typ: QubitId| {
                book(c, "codec", "div codec", t, |c| tape.pack_due(c, t, r, false));
                book(c, "cells", "div fused cell", t, |c| dirty_cell(c, tape, t, |c| cell_div(c, cfg, t, typ, sig, &d)));
            };
            book(c, "rails", "div fwd rail", t, |c| forward_tick(c, cfg, k, &mut w, denominator, t, "divfwd", Some(&mut mid)))
        } else {
            book(c, "rails", "div fwd rail", t, |c| forward_tick(c, cfg, k, &mut w, denominator, t, "divfwd", None))
        };
        if !inside_cell {
            book(c, "codec", "div codec", t, |c| w.tape.pack_due(c, t, r, false));
        }
        if t < k.r2d {
            if t == 0 && k.fd {
                let rails = w.rails.as_ref().unwrap();
                let (xs, ys) = (*rails.r1.last().unwrap(), *rails.r2.last().unwrap());
                del = Some(book(c, "g1b", "div fd payload", t, |c| fd_payload_div(c, sig, xs, ys, typ)));
            } else if t == 0 {
                assert!(k.g1b || k.h0, "carry schedule: G1b or H0 required (cell 0 skipped)");
            } else if t == 1 && k.h0 {
                let om1 = w.tape.get(0).0;
                del = Some(book(c, "g1b", "div h0 payload", t, |c| h0_payload_div(c, sig, om1, typ)));
            } else if t == 1 && k.g1b && !k.fd {
                let s0 = w.tape.get(0).1;
                del = Some(book(c, "g1b", "div g1b", t, |c| g1b_forward(c, sig, s0, typ)));
            } else if !inside_cell {
                let d = del.as_ref().unwrap();
                let r1 = w.rails.as_ref().unwrap().r1.clone();
                book(c, "cells", "div fused cell", t, |c| k2_cell_loan(c, &r1, rw(cfg.esw[t]), |c| dirty_cell(c, &w.tape, t, |c| cell_div(c, cfg, t, typ, sig, d))));
            }
            if t > 0 {
                let d = del.as_ref().unwrap();
                book(c, "routing", "div route", t, |c| route(c, s, sig, d));
            }
        }
    }
    c.set_phase("heo_div_batch");
    let mut rails = w.rails.take().unwrap();
    unpark_par(c, k, &mut rails);
    if k.loan_both {
        book(c, "codec", "div batch codec", r - 1, |c| w.tape.ensure_raw(c, r - 1));
        let ol = w.tape.get(r - 1).0;
        book(c, "seeds", "loan orient", r - 1, |c| if park_mbu_on() { park_mbu_loan(c, &mut rails, ol) } else { park_orient(c, &rails, ol) });
    }
    let (o, wid) = loan(c, rails);
    let last_g = w.tape.gid(r - 1);
    let d = del.take().unwrap();
    let mut early_g: Option<usize> = None;
    for t in k.r2d..r {
        let g = w.tape.gid(t);
        if k.div_partial || early_g == Some(g) {
            // B7 V-P9: unpack only what letter t needs (the first batch group keeps its P3 part packed); also every
            // letter of a group the LAZY_BATCH rule already packed early (a group unpack would undo the pack3)
            book(c, "codec", "div batch codec", t, |c| w.tape.ensure_raw(c, t));
        } else {
            book(c, "codec", "div batch codec", t, |c| w.tape.ensure_group_raw(c, g, r));
        }
        let (typ, s) = w.tape.get(t);
        book(c, "cells", "div batch cell", t, |c| dirty_cell(c, &w.tape, t, |c| cell_div(c, cfg, t, typ, sig, &d)));
        if !(k.db_skip && t + 1 == r) && !(k.db_skip2 && t + 2 == r) {
            book(c, "routing", "div batch route", t, |c| route(c, s, sig, &d));
        }
        // B7 V-P6: HEO_DIV_LIFO_N = n leaves the last n+1 groups raw (base n = 0: the last group)
        let lifo_keep = k.lifo && g + k.div_lifo_n >= last_g;
        if k.div_early_p3 && (t - off) % 5 == 2 && !lifo_keep {
            // B7 LAZY_BATCH (div): letters 0..2 of the group are consumed; pack them now (repack then does pack5 only)
            let t0 = 5 * g + off;
            if t0 + 2 < r && w.tape.state(g) == GState::Raw && (t0..t0 + 3).all(|u| w.tape.raw[u].is_some()) {
                book(c, "codec", "div batch codec", t, |c| w.tape.pack3(c, g));
                early_g = Some(g);
            }
        }
        if ((t - off) % 5 == 4 || t == r - 1) && !lifo_keep {
            book(c, "codec", "div batch codec", t, |c| w.tape.repack(c, g, r));
        }
    }
    c.set_phase("heo_div_endpoint");
    c.cx_pairs(sig, &d);
    c.free_vec(&d);
    let mut rails = unloan(c, o, wid);
    if k.loan_both {
        book(c, "codec", "div batch codec", r - 1, |c| w.tape.ensure_raw(c, r - 1));
        let ol = w.tape.get(r - 1).0;
        book(c, "seeds", "loan orient", r - 1, |c| if park_mbu_on() { park_mbu_unloan(c, &mut rails, ol) } else { park_orient(c, &rails, ol) });
    }
    park_par(c, k, &mut rails);
    w.rails = Some(rails);
    c.set_phase("heo_div_walkback");
    let mut x_out = None;
    for t in (0..r).rev() {
        let out = book(c, "rails", "div rev rail", t, |c| reverse_tick(c, cfg, k, &mut w, t, SplitMode::Apply, "divrev", None));
        if out.is_some() {
            x_out = out;
        }
    }
    assert!(w.tape.all_consumed(), "div tape not consumed");
    restore_layout(c, &x_out.unwrap(), denominator);
}

/// `numerator *= denominator (mod p)`.
pub fn multiply(c: &mut Builder, numerator: &[QubitId], denominator: &[QubitId]) {
    let cfg = super::config_mul();
    let k = carry_cfg();
    assert_eq!(cfg.seed, super::Seed::Base, "carry schedule: base seed only (F-B3b-1)");
    let r = cfg.rounds();
    let sig = numerator;
    let lt0m = k.lt0_mul;
    let off = usize::from(lt0m);
    let mut w = Walk { pending_low: None, rails: None, tape: Tape::with_offset(r, off), deferred: vec![Vec::new(); r], bwire: None, o0: None,
                       lt0: lt0m, ywire: None, o0_erase: k.o0m && lt0m, o0_rebuild: false };
    c.set_phase("heo_mul_fwd");
    for t in 0..r {
        book(c, "rails", "mul fwd rail", t, |c| forward_tick(c, cfg, k, &mut w, denominator, t, "mulfwd", None));
        if t == 0 && k.fd && !k.bw_inv {
            let bw = c.alloc_qubit();
            c.cx(*w.rails.as_ref().unwrap().r1.last().unwrap(), bw);
            w.bwire = Some(bw);
        }
        book(c, "codec", "mul codec", t, |c| w.tape.pack_due(c, t, r, k.lifo));
    }
    c.set_phase("heo_mul_batch");
    let mut rails = w.rails.take().unwrap();
    unpark_par(c, k, &mut rails);
    if k.loan_both {
        book(c, "codec", "mul batch codec", r - 1, |c| w.tape.ensure_raw(c, r - 1));
        let ol = w.tape.get(r - 1).0;
        book(c, "seeds", "loan orient", r - 1, |c| if park_mbu_on() { park_mbu_loan(c, &mut rails, ol) } else { park_orient(c, &rails, ol) });
    }
    let (o, wid) = loan(c, rails);
    let del = c.alloc_qubits(N);
    c.cx_pairs(sig, &del);
    for t in (k.r2m..r).rev() {
        let g = w.tape.gid(t);
        if k.mulb_partial {
            book(c, "codec", "mul batch codec", t, |c| w.tape.ensure_raw(c, t)); // B7 V-P9
        } else {
            book(c, "codec", "mul batch codec", t, |c| w.tape.ensure_group_raw(c, g, r));
        }
        let (typ, s) = w.tape.get(t);
        if !(k.mb_skip2 && t + 2 == r) {
            book(c, "routing", "mul batch route", t, |c| route(c, s, sig, &del));
        }
        book(c, "cells", "mul batch cell", t, |c| dirty_cell(c, &w.tape, t, |c| cell_mul(c, cfg, t, typ, sig, &del)));
        // B7 V-P7: railsrev reads the batch's last groups soon after; HEO_MULB_LIFO_N = n leaves n of them raw
        if (t - off) % 5 == 0 && g >= w.tape.gid(k.r2m) + k.mulb_lifo_n {
            book(c, "codec", "mul batch codec", t, |c| w.tape.repack(c, g, r));
        }
    }
    let mut rails = unloan(c, o, wid);
    if k.loan_both {
        book(c, "codec", "mul batch codec", r - 1, |c| w.tape.ensure_raw(c, r - 1));
        let ol = w.tape.get(r - 1).0;
        book(c, "seeds", "loan orient", r - 1, |c| if park_mbu_on() { park_mbu_unloan(c, &mut rails, ol) } else { park_orient(c, &rails, ol) });
    }
    park_par(c, k, &mut rails);
    w.rails = Some(rails);
    c.set_phase("heo_mul_railsrev");
    for t in (k.r2m..r).rev() {
        book(c, "rails", "mul rev rail", t, |c| reverse_tick(c, cfg, k, &mut w, t, SplitMode::Exact, "mulrev", None));
    }
    c.set_phase("heo_mul_fused");
    for t in (k.r1m..k.r2m).rev() {
        if k.lr1 && t > 0 {
            // B6 L-R1: the rails hold the post-tick-t state; the reverse tick's resize to ead[t] re-extends R1.
            let rails = w.rails.as_mut().unwrap();
            book(c, "rails", "mul fused lr1", t, |c| resize(c, &mut rails.r1, lr1_width(cfg, t)));
        }
        book(c, "codec", "mul fused codec", t, |c| w.tape.ensure_raw(c, t));
        let (typ, s) = w.tape.get(t);
        book(c, "routing", "mul fused route", t, |c| route(c, s, sig, &del));
        if env_bool("HEO_CELL_INSIDE", false) {
            // v025 I-3: the inverse cell runs inside the reverse tick, after the inverse add has
            // consumed the tape sign wire s and before the rails regrow.
            let mut mid = |c: &mut Builder, tape: &Tape, typ: QubitId| {
                book(c, "cells", "mul fused cell", t, |c| dirty_cell(c, tape, t, |c| cell_mul(c, cfg, t, typ, sig, &del)));
            };
            book(c, "rails", "mul fused rail", t, |c| reverse_tick(c, cfg, k, &mut w, t, k.split_mul, "mulfused", Some(&mut mid)));
        } else {
            let r1 = w.rails.as_ref().unwrap().r1.clone();
            book(c, "cells", "mul fused cell", t, |c| k2_cell_loan(c, &r1, rw(cfg.esw[t]), |c| dirty_cell(c, &w.tape, t, |c| cell_mul(c, cfg, t, typ, sig, &del))));
            book(c, "rails", "mul fused rail", t, |c| reverse_tick(c, cfg, k, &mut w, t, k.split_mul, "mulfused", None));
        }
    }
    if lt0m {
        // RB-1: single head batch with the class rebuilt from the frame invariant (see CarryCfg::lt0_mul).
        c.set_phase("heo_mul_headbatch");
        let (s1, s2) = {
            let rails = w.rails.as_ref().unwrap();
            (*rails.r1.last().unwrap(), *rails.r2.last().unwrap())
        };
        let mut yw: Option<QubitId> = None;
        for t in (1..k.r1m).rev() {
            let g = w.tape.gid(t);
            book(c, "codec", "mul head codec", t, |c| {
                if truthy("HEO_HEAD_PARTIAL") { w.tape.ensure_raw(c, t); }
                else { w.tape.ensure_group_raw(c, g, r); }
            });
            let (typ, s) = w.tape.get(t);
            if t + 1 == k.r1m {
                // b_T = smaller-rail sign = o ? sign R1 : sign R2 (1 Toffoli)
                let b = c.alloc_qubit();
                book(c, "g1b", "mul fd signs", t, |c| {
                    c.cx(s2, b);
                    c.cx(s2, s1);
                    c.ccx(typ, s1, b);
                    c.cx(s2, s1);
                });
                yw = Some(b);
            }
            c.cx(s, yw.unwrap()); // b_{t-1} = b_t ^ f_t
            book(c, "routing", "mul head route", t, |c| route(c, s, sig, &del));
            book(c, "cells", "mul head cell", t, |c| dirty_cell(c, &w.tape, t, |c| cell_mul(c, cfg, t, typ, sig, &del)));
            // B7 V-P5 / V-P8: groups 0..n-1 are the last ones railsrev2 reads; leave them raw
            if (t - off) % 5 == 0 && g >= k.head_lifo_n {
                book(c, "codec", "mul head codec", t, |c| w.tape.repack(c, g, r));
            }
        }
        // a = larger-rail sign = o_{r1m-1} ? sign R2 : sign R1, computed now so it is live for the payload only.
        let top = k.r1m - 1;
        let gtop = w.tape.gid(top);
        book(c, "codec", "mul head codec", top, |c| w.tape.ensure_raw(c, top));
        let o_top = w.tape.get(top).0;
        let a = c.alloc_qubit();
        book(c, "g1b", "mul fd signs", top, |c| {
            c.cx(s1, a);
            c.cx(s1, s2);
            c.ccx(o_top, s2, a);
            c.cx(s1, s2);
        });
        if k.head_lifo_n == 0 {
            // B7 V-P5 (n >= 1): railsrev2 starts at t = top and would unpack gtop again at once: keep it raw
            book(c, "codec", "mul head codec", top, |c| w.tape.repack(c, gtop, r));
        }
        let b = yw.unwrap();
        if w.o0.is_none() {
            // B7 O0-M (Effort 7 CHECK, AND form): the pair is the FD class state of (M, 2M); with A = NOT(a ^ b)
            // (a, b = larger / smaller rail signs, before the fredkin), o_0 = NOT A AND NOT(Del[1] ^ Sig[0])
            // for p = 3 mod 4. 1 CCX; every control restored.
            assert!(k.o0m && (SECP256K1_P.as_limbs()[0] & 3) == 3);
            let o0n = c.alloc_qubit();
            book(c, "g1b", "mul o0m rebuild", 0, |c| {
                c.cx(a, b);
                c.cx(del[1], sig[0]);
                c.x(sig[0]);
                c.ccx(b, sig[0], o0n);
                c.x(sig[0]);
                c.cx(del[1], sig[0]);
                c.cx(a, b);
            });
            w.o0 = Some(o0n);
        }
        let o0 = w.o0.unwrap();
        book(c, "g1b", "mul fd payload", 0, |c| {
            fredkin(c, o0, a, b); // (a, b) = (X_sign, Y_sign)
            if std::env::var_os("FOLD_FD_TRANSPORT").is_some(){super::super::dirty_boundary_probe::with_tape(c,Some(o0),|c| fd_payload_div_inv(c,sig,&del,a,b,o0));}else{fd_payload_div_inv(c, sig, &del, a, b, o0);}
        });
        c.free_vec(&del);
        w.bwire = Some(a);
        w.ywire = Some(b);
        c.set_phase("heo_mul_railsrev2");
        let mut x_out = None;
        for t in (0..k.r1m).rev() {
            let out = book(c, "rails", "mul rev2 rail", t, |c| reverse_tick(c, cfg, k, &mut w, t, SplitMode::Exact, "mulrev2", None));
            if out.is_some() {
                x_out = out;
            }
        }
        assert!(w.tape.all_consumed(), "mul tape not consumed");
        restore_layout(c, &x_out.unwrap(), denominator);
        if truthy("HEO_LEDGER_PRINT") {
            print_ledger();
        }
        return;
    }
    // B4: optional STAGED head batch (B2 a2_headbatch_stages): `HEO_HB_STAGES=b1,b2,..` (descending multiples
    // of 5 below r1m). Each stage runs its cells at the current rail state, then the rails-only reverse down to the
    // stage boundary (consuming those letters) before the next stage. Empty = the single head batch.
    let mut bounds: Vec<usize> = std::env::var("HEO_HB_STAGES").ok().map(|v| {
        v.split(',').map(str::trim).filter(|x| !x.is_empty()).map(|x| x.parse::<usize>().expect("HEO_HB_STAGES")).collect()
    }).unwrap_or_default();
    bounds.push(0);
    let mut cur = k.r1m;
    let mut x_out = None;
    for &b in &bounds {
        assert!(b < cur && b % 5 == 0, "HEO_HB_STAGES must descend below r1m in multiples of 5");
        c.set_phase("heo_mul_headbatch");
        for t in (b..cur).rev() {
            let g = t / 5;
            book(c, "codec", "mul head codec", t, |c| {
                if truthy("HEO_HEAD_PARTIAL") { w.tape.ensure_raw(c, t); }
                else { w.tape.ensure_group_raw(c, g, r); }
            });
            let (typ, s) = w.tape.get(t);
            if k.fd && k.bw_inv && t + 1 == k.r1m {
                // FB-RB1-1: a = o_{r1m-1} ? sign R2 : sign R1 (the larger rail's sign, invariant) -> the b wire.
                let rails = w.rails.as_ref().unwrap();
                let (s1, s2) = (*rails.r1.last().unwrap(), *rails.r2.last().unwrap());
                let bw = c.alloc_qubit();
                book(c, "g1b", "mul fd bw", t, |c| {
                    c.cx(s1, bw);
                    c.cx(s1, s2);
                    c.ccx(typ, s2, bw);
                    c.cx(s1, s2);
                });
                w.bwire = Some(bw);
            }
            if t > 0 {
                book(c, "routing", "mul head route", t, |c| route(c, s, sig, &del));
            }
            if t == 1 && k.h0 {
                let om1 = w.tape.get(0).0;
                book(c, "g1b", "mul h0 payload", t, |c| h0_payload_mul_inv(c, sig, &del, om1, typ));
            } else if t == 1 && !k.fd {
                let s0 = w.tape.get(0).1;
                book(c, "g1b", "mul g1b", t, |c| g1b_inverse(c, sig, &del, s0, typ));
            } else if t >= 1 {
                book(c, "cells", "mul head cell", t, |c| dirty_cell(c, &w.tape, t, |c| cell_mul(c, cfg, t, typ, sig, &del)));
            } else if k.fd {
                let bw = w.bwire.unwrap();
                if k.bw_inv {
                    c.cx(typ, bw); // b = a ^ o_0
                }
                book(c, "g1b", "mul fd payload", t, |c| fd_payload_mul_inv(c, sig, &del, typ, s, bw));
            }
            if t % 5 == 0 {
                book(c, "codec", "mul head codec", t, |c| w.tape.repack(c, g, r));
            }
        }
        if b == 0 {
            c.free_vec(&del);
        }
        c.set_phase("heo_mul_railsrev2");
        for t in (b..cur).rev() {
            let out = book(c, "rails", "mul rev2 rail", t, |c| reverse_tick(c, cfg, k, &mut w, t, SplitMode::Exact, "mulrev2", None));
            if out.is_some() {
                x_out = out;
            }
        }
        cur = b;
    }
    assert!(w.tape.all_consumed(), "mul tape not consumed");
    restore_layout(c, &x_out.unwrap(), denominator);
    if truthy("HEO_LEDGER_PRINT") {
        print_ledger();
    }
}

thread_local! {
 static REVERSE_CODEC_CAPTURE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
 static REVERSE_LOW: std::cell::RefCell<Option<(QubitId,QubitId,QubitId,QubitId)>> = const { std::cell::RefCell::new(None) };
}
fn reverse_carries(c:&mut Builder,n:usize,a:QubitId,b:QubitId,prev:Option<QubitId>)->Vec<QubitId>{
 let q=REVERSE_LOW.with(|r|r.borrow().as_ref().map(|&(aa,bb,p,q)|{assert_eq!((a,b,prev),(aa,bb,Some(p)));q}));
 if let Some(q)=q {assert!(n>0);let mut out=vec![q];out.extend(c.alloc_qubits(n-1));out}else{c.alloc_qubits(n)}
}


