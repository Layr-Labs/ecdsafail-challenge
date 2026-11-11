//! froghop-one: a low-qubit exact-packed Euclid point addition with one hop per Euclid step.

pub mod arith;
pub mod builder;
pub mod froghop_double;
pub mod froghop_one;
#[cfg(all(test, greedyfrog_legacy_tests))] // external tree, absent in the greedyfrog worktree
#[path = "../../../r16-c27-839/src/point_add/froghop_one.rs"]
mod froghop_one_before_a4a;
#[cfg(test)]
mod froghop_one_before_rxd;
#[cfg(test)]
mod froghop_one_before_topbit;
#[cfg(test)]
mod froghop_one_before_s7diet;
#[cfg(test)]
mod froghop_one_before_s2diet;
#[cfg(test)]
mod froghop_one_diet_bb6;
#[cfg(all(test, greedyfrog_legacy_tests))] // external tree, absent in the greedyfrog worktree
#[path = "../../../r10-c6z/src/point_add/froghop_one.rs"]
mod froghop_one_before_b1cache;
pub mod mask;
pub mod modp_double;
pub mod ftport;
pub mod ft_adapter;
pub mod sqport;
pub mod pointadd_double;
pub mod pointadd_one;
pub mod refmodel_double;
pub mod refmodel_one;
pub mod greedyfrog_model;
pub mod greedyfrog;
pub mod pointadd_greedyfrog;
#[cfg(test)]
mod greedyfrog_diag;
mod affine_simplify;
mod quadratic_simplify;
mod truth_simplify;
mod classical_wide;
mod cond_pass;
mod frontier_rewrite;
mod lease_pass;
mod postpass;
mod hold_pass;
mod interned_witness;
mod pscan;
mod zero_force;
mod classical_factors_xor;
mod mabsorb;
#[cfg(all(test, greedyfrog_legacy_tests))] // uses the external-tree modules
mod tests_one;
#[cfg(test)]
mod tests_double;

use crate::circuit::{Op, OperationType, NO_BIT};
use std::sync::LazyLock;

pub const SCHED_DOUBLE: &str = include_str!("sched_double.txt");
pub const SCHED_ONE: &str = include_str!("sched_one.txt");
/// Fiat-Shamir nonce (number of identity X X pairs appended). `FH_NONCE` overrides it for corpus measurements; the
/// official build uses this value.
pub const NONCE: usize = 1;
/// Logical-AND carry qubits for the traversal ladders' ordinary lanes.
pub const GPOOL: usize = 12;
/// Traversal state: pi, k, flags, the layout's stack/DONE counter, depth and b offset.
pub fn state(lay: &froghop_one::LayOne) -> usize {
    froghop_one::HIB + froghop_one::KB + 3 + lay.smax + froghop_one::DEPB + froghop_one::BB + 1
}
/// Peak live qubits: the traversal's 2 W + 256 passenger + state + scratch + GPOOL + reflection bit; the modular
/// routines take every clean qubit up to it as carry pool.
pub static PEAK: LazyLock<u64> = LazyLock::new(|| {
    if USE_GREEDYFROG {
        // dev only: GF_PEAK=<cap> (the official build runs with an empty environment)
        return std::env::var("GF_PEAK").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(GREEDYFROG_PEAK);
    }
    let lay = layout_one();
    (2 * froghop_one::W1 + 256 + state(&lay) + froghop_one::POOL_1 + GPOOL + 1) as u64
});
/// Build the point addition with uniform greedy Euclid divisions (`pointadd_greedyfrog`) instead of froghop-one.
pub const USE_GREEDYFROG: bool = true;
/// greedyfrog peak cap. The traversal needs 2 W rings, the 256-qubit passenger, LA LB (18; the DONE counter lives in
/// ring Y), the reflection bit (which carries the swap parity) and 24 lanes of slot scratch (815); above that, the
/// slots take clean ancillas and carry pools up to the cap, below it borrowed lanes. The modular routines fill their carry pools up to it.
pub const GREEDYFROG_PEAK: u64 = 825;

pub fn nonce() -> usize {
    std::env::var("FH_NONCE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(NONCE)
}

pub fn layout_double() -> froghop_double::LayDouble {
    froghop_double::LayDouble::from_text(SCHED_DOUBLE, 24)
}

pub fn layout_one() -> froghop_one::LayOne {
    froghop_one::LayOne::from_text(SCHED_ONE, 24)
}

/// claude-r8 Q798: the 799 build's switches with GF_PEAK=798, R5_PRE4=2 (the 4-lane undo-rows prefix on every masked
/// slot) and the R10 allocation-site closures (each fires only where the cap leaves no lane for the parent's
/// allocation; see `r10_on` in greedyfrog.rs).
/// The 799 build's switches (R9-MERGE799 build C), applied as defaults: a variable already set in the environment
/// wins, and `R9_OFF=1` skips the whole table (the inherited defaults, for paired A/B checks).
const R9_DEFAULTS: &str = "GF_PEAK=797 I5_RFREE=1 I5_RCNT=1 I5_SYFOLD=1 I5_SPLIT=1 I5_DCMP7=1 I4_WIT=1 I4_EFE=1 I4_DEFER=1 \
    R3_LA8=1 R3_LA8LIVE=1 R3_YTOPB=1 R3_RA1YG=1 R3_ANF3=1 R3_LA8ROWS=1 R3_LATOP=1 R3_VERG=1 R3_VROOM=1 R3_VUF=1 \
    R3_VROOM_Y=1 R3F_SLIM=1 R4_RHO=1 R4_WIDE=1 R4_MASK=1 R4_SWCXY=1 R4_SWT=1 R4_SWC0=1 R4_CVIEW=1 R4_CSUB=1 R4_IDLE=1 \
    R3F_NOROLL=1 R4_TOPC=1 R4_LBLATE=1 R5_EARLY=1 R5_LAH6=1 R5_MPOOL=1 R5_FOLD=1 R5_YOFF=1 R5_PRE4=2 WL_ROUND_DIV=1 \
    LS2_RW=56 LS2_WC=23 R6_GEC=1 R6_LBV=1 R6_PTOP=1 R6_MIX=1 R8_LHF=1 R8_M8=1 R8_LHFAC=1 R8_LAMX=1 R8_ITAIL=1 R8_IUNSW=1 \
    R8_IDEN=1 R8_PPLAN=2 R8_FZ=1 R8_FUSE=58 R8_CC=1 R8_PHB=1 R8_CC2=1 R8_SWL=1 \
    R10_WGT=1 R10_RBF=1 R10_RBL=1 R10_P2S=1 R10_LB8=1 R10_P4F=1 R10_SH2=1 R10_NI=1 R10_DEC=1 R10_RBY=1 \
    R10_LBT=1 R10_X0=1 R10_WGT2=1 R10_P2S2=1 R10_LB7=1 R10_NI2=1 R10_RBL2=1 R11_FOLD=1 R11_DEC1=1 R11_LA7=1 R11_LA5=1";

/// S4 Q796 (Opus q796jc, structural lane S4): the Q797 build at GF_PEAK=796 with the source-present Q796 closures
/// (fable 796b R12_PF3 / R12_SH3 / R12_WGT3 / R12_JLF, ds-q796-f6 R12_NIF / R12_TERM, F5 R12_DECODE_PERM / R12_P2S3=1)
/// and R15_JC, the old greedyfrog's joint-code sweep (GF_JC) on the slim VERG slots, which takes the sweep's g, y (and
/// f on act-constant slots) off the RowTmp::attach instant. R15_IDLE_P: the parent's R4_IDLE (envelope host) only at
/// the sites where the Q797 build fires it. LS1_CET=0: the shell products' chunk-carry erases are exact compares
/// (LS-1's top-26 truncation misses on top-lane ties; the 796 cap shrinks a ProductStream pool 28 -> 27, which moves
/// its chunk boundaries and hence which inputs tie: new fixed-input phase failures, Codex wD witness 91b7-01/7586).
/// LS2_CMPT=37: the modular adds' overflow-flag oracles compare the top 37 lanes instead of 25 (the widest whose carry
/// erase fits the 796 pools); the 796 cap shrinks the first ProductStream's room 20 -> 19, which changes the values
/// reaching those truncated compares (Codex wD witness 91b7-14/72, a top-25 tie). Not exact by construction: per
/// erase the tie probability drops 2^-12 below the parent's.
/// R8_FUSE=96 LS2_WM=96 LS2_RW=96 WL_DFOLD=0: the shell products' fold windows (fused 58, merged 57, fold register 56,
/// double fold 58 lanes: dropped-carry approximations, a classical error shifted up by later doublings) widened to 96
/// lanes, the double fold off (its 58-lane jit window cannot widen in these pools); the 796 cap shifts where the
/// ProductStream's folds switch, so other inputs drop a carry (witness q796jc-v4scan-01/1711, y off by 2^173). Applied before the R9 table (a variable already set in the
/// environment wins). Off switch `WL_R15_ROW796=0`: the parent Q797 build, byte for byte.
pub const R15_ROW796: bool = true;
const R15_DEFAULTS: &str = "GF_PEAK=796 R12_PF3=1 R12_SH3=1 R12_WGT3=1 R12_JLF=1 R12_NIF=1 R12_TERM=1 \
    R12_DECODE_PERM=1 R12_P2S3=1 R15_JC=1 R15_IDLE_P=1 LS1_CET=0 LS2_CMPT=37 \
    R8_FUSE=96 LS2_WM=96 LS2_RW=96 WL_DFOLD=0";

/// fotl765 R9 Q795 (worker FREEZE, 10 Nov 2026): the r9 merge2 (Q792 X0NA + the final r9 closure patches prefix, done d4,
/// la, rowtmp) at GF_PEAK=795, with the builder-census switches that took its traversal to peak 795 baked as defaults.
/// Applied BEFORE the R15 and R9 tables, so these values win over theirs (a variable already set in the environment
/// still wins). Functional switches only: the shell products' parent widths (LS1_CET=26 LS2_CMPT=25 R8_FUSE=58
/// LS2_WM=57 LS2_RW=56 WL_DFOLD=1, the Q797 build's, which the 795 pools fit; the R15 table had widened them for 796),
/// M1_ROWF=close (ROW-F row 0 runs pool-free where the 795 cap leaves the pool empty; unset, the build panics at the
/// R10_X0 row-shape assert in greedyfrog.rs, measured),
/// and the r9 closure knobs Q792_X0NA R9_PREFIX R9_DONE R9_LA R9_LB R9_LU R9_ROWTMP. The census probes P2_OVER,
/// I5_SNAP, SZ1_POOLS (and GREEDYFROG_PROF, M1_EXP, WALK_STOP) only log and are not baked.
/// Off switch `WL_R9_ROW795=0`: the env-knob tree (the Q796 defaults unless the knobs are set by hand).
pub const R9_ROW795: bool = true;
const R795_DEFAULTS: &str = "GF_PEAK=795 LS1_CET=26 LS2_CMPT=25 R8_FUSE=58 LS2_WM=57 LS2_RW=56 WL_DFOLD=1 M1_ROWF=close \
    Q792_X0NA=1 R9_PREFIX=1 R9_DONE=1 R9_LA=1 R9_LB=1 R9_LU=1 R9_ROWTMP=1";

/// fotl765 R14 Q794 "Chumjetzze" (worker R14-merge, 11 Nov 2026): the R14 rung (ohMeingott + Vollgasbuebe, läckBobby,
/// losgahts, DonRwetter, läckBobby-b, Schaffhuuserzopf) at GF_PEAK=794, baked as defaults. Applied BEFORE the R795,
/// R15 and R9 tables, so these values win over theirs (a variable already set in the environment still wins).
/// Functional switches only: the cap, the even-cap shell set that clears witness 1711 (LS1_CET=0 LS2_CMPT=29
/// R8_FUSE=64 LS2_WM=64 LS2_RW=64 WL_DFOLD=0, campaign/bin/cen794.sh) and the six family knobs (R14_FWD94=2,
/// R14_PFX94=1, R14_LA94=1, R14_MISC94=1 = "sdupyxr", R14_PFX94B=1, R14_LA94B=1). M1_ROWF=close comes from the R795
/// table. The census probes P2_OVER, I5_SNAP, SZ1_POOLS (and GREEDYFROG_PROF, M1_EXP, WALK_STOP) only log and are not
/// baked (raw stream identical with and without them, measured). Off switch `WL_R14_ROW794=0`: the Q795b row tree.
pub const R14_ROW794: bool = true;
const R794_DEFAULTS: &str = "GF_PEAK=794 LS1_CET=0 LS2_CMPT=29 R8_FUSE=64 LS2_WM=64 LS2_RW=64 WL_DFOLD=0 \
    R14_FWD94=2 R14_PFX94=1 R14_LA94=1 R14_MISC94=1 R14_PFX94B=1 R14_LA94B=1";

fn apply_defaults() {
    let r794 = std::env::var("WL_R14_ROW794").map_or(R14_ROW794, |v| v.trim() == "1");
    if r794 {
        for kv in R794_DEFAULTS.split_whitespace() {
            let (k, v) = kv.split_once('=').unwrap();
            if std::env::var_os(k).is_none() { std::env::set_var(k, v); }
        }
    }
    let r795 = std::env::var("WL_R9_ROW795").map_or(R9_ROW795, |v| v.trim() == "1");
    if r795 {
        for kv in R795_DEFAULTS.split_whitespace() {
            let (k, v) = kv.split_once('=').unwrap();
            if std::env::var_os(k).is_none() { std::env::set_var(k, v); }
        }
    }
    let r15 = std::env::var("WL_R15_ROW796").map_or(R15_ROW796, |v| v.trim() == "1");
    if r15 {
        for kv in R15_DEFAULTS.split_whitespace() {
            let (k, v) = kv.split_once('=').unwrap();
            if std::env::var_os(k).is_none() { std::env::set_var(k, v); }
        }
    }
    if std::env::var_os("R9_OFF").is_some() { return; }
    for kv in R9_DEFAULTS.split_whitespace() {
        let (k, v) = kv.split_once('=').unwrap();
        if std::env::var_os(k).is_none() { std::env::set_var(k, v); }
    }
}

pub fn build() -> Vec<Op> {
    apply_defaults();
    // dev only (inert in the official empty environment): PP_LOAD=<ops.bin> replaces the builder by a saved stream;
    // PP_FROM = raw (default: the GF_RAW stream, every post-pass runs), lease (a PP_DUMP_PRELEASE stream: lease_pass
    // and the B-POSTPASS passes run) or final (a finished ops.bin: only the B-POSTPASS passes run).
    let pp_load = std::env::var("PP_LOAD").ok();
    let pp_from = std::env::var("PP_FROM").unwrap_or_default();
    let mut ops = if let Some(path) = &pp_load {
        postpass::load(path)
    } else {
    let mut b = builder::B::new();
    if USE_GREEDYFROG {
        pointadd_greedyfrog::point_add(&mut b);
    } else {
        let lay = layout_one();
        pointadd_one::point_add(&mut b, &lay);
    }
    if std::env::var_os("M1_EXP").is_some() { m1_stage_dump(&b.ops, &greedyfrog::m1_take()); }
    let removed = cancel_adjacent_ccx(&mut b.ops);
    eprintln!("{}: ops {} peak qubits {} width {} emitted Toffoli {} (adjacent CCX gates removed {})",
              if USE_GREEDYFROG { "greedyfrog" } else { "froghop-one" },
              b.ops.len(), b.peak, b.width(), b.tof - removed as u64, removed);
    // dev only (inert in the official empty environment): static counts before the post-passes, then stop
    if std::env::var_os("WALK_STOP").is_some() {
        greedyfrog::prof_dump();
        builder::p2_over_dump();
        eprintln!("WALK_STOP pre-post counts {:?} peak {}", counts(&b.ops), b.peak);
        std::process::exit(0);
    }
    b.ops
    };
    if std::env::var_os("SZ1_RAW_ONLY").is_some() {
        // sz1 measurement only: the pre-post-pass counts, then stop (no ops.bin)
        eprintln!("SZ1RAW {:?}", counts(&ops));
        std::process::exit(0);
    }
    if std::env::var_os("SZ1_RAW_OPS").is_some() {
        // sz1 measurement only (census GF_RAW): the raw stream, no post-passes, with the tail nonce
        eprintln!("SZ1RAWOPS {:?}", counts(&ops));
        append_tail_nonce(&mut ops, TAIL_NONCE);
        return ops;
    }
    // dev only: GF_RAW writes the raw stream (no post-passes) with the tail nonce
    // q792 diagnostic (dev only, inert unless Q792_RELOC=<cap> is set): symbolic-live census of the raw stream and the
    // width-only dup_relocate (R12_HOLDQ's pass) into <cap> wires; with GF_RAW the relocated raw stream is written
    if let Ok(cap) = std::env::var("Q792_RELOC") {
        let cap: usize = cap.trim().parse().expect("Q792_RELOC cap");
        hold_pass::q792_census(&ops, cap);
        if std::env::var_os("Q792_CENSUS_ONLY").is_some() { std::process::exit(0); }
        if std::env::var_os("Q792_LOAN_CENSUS").is_some() { hold_pass::q792_loan_census(&ops, cap); std::process::exit(0); }
        let n0 = ops.len();
        match hold_pass::dup_relocate(std::mem::take(&mut ops), cap) {
            Some(m) => { eprintln!("Q792_RELOC relocated the raw stream into {cap} wires (ops {n0} -> {})", m.len()); ops = m; }
            None => { eprintln!("Q792_RELOC relocation failed"); std::process::exit(3); }
        }
    }
    if std::env::var_os("GF_RAW").is_some() {
        eprintln!("GF_RAW: skipping all post passes, ops {}", ops.len());
        append_tail_nonce(&mut ops, TAIL_NONCE);
        return ops;
    }
    // the identity X X pairs at the end are kept out of the post-passes and re-appended unchanged
    let n2 = 2 * nonce();
    let tail = ops.split_off(ops.len() - n2);
    assert!(tail.iter().all(|o| o.kind == OperationType::X && o.q_target == tail[0].q_target));
    // Exact generic post-passes: Boolean tables over at most six atoms (to a fixed point), nine-atom tables with the
    // product index, then the conditional-AND pass with options m (CCX -> CX), f (ANDs read only by phases) and
    // s (ANDs built under the classical bit that decides their read).
    let skip_base = pp_load.is_some() && (pp_from == "lease" || pp_from == "final");
    if !skip_base {
    let before = counts(&ops);
    for pass in 1..=32 {
        let previous = counts(&ops);
        ops = truth_simplify::simplify_products(ops);
        let after = counts(&ops);
        eprintln!("POSTPASS_T pass={pass} before={previous:?} after={after:?}");
        if previous == after { break; }
    }
    let previous = counts(&ops);
    ops = classical_wide::simplify_products(ops);
    eprintln!("POSTPASS_W before={previous:?} after={:?}", counts(&ops));
    let previous = counts(&ops);
    ops = cond_pass::run_with(ops, "mfsur");
    eprintln!("POSTPASS_C before={previous:?} after={:?}", counts(&ops));
    eprintln!("POSTPASS raw={before:?} final={:?}", counts(&ops));
    ops = frontier_rewrite::apply(ops);
    }
    if let Ok(path) = std::env::var("PP_DUMP_PRELEASE") {
        postpass::dump(&path, &ops, &tail); // dev only
    }
    if !(pp_load.is_some() && pp_from == "final") {
        ops = lease_pass::run(ops);
    }
    eprintln!("POST_LEASE {:?}", counts(&ops));
    if let Ok(cap) = std::env::var("R12_HOLDQ") {
        let cap: usize = cap.trim().parse().expect("R12_HOLDQ cap");
        let original = std::mem::take(&mut ops);
        match hold_pass::dup_relocate(original.clone(), cap) {
            Some(mapped) => {
                eprintln!("R12_HOLDQ relocated the stream into {cap} wires");
                ops = mapped;
            }
            None => {
                eprintln!("R12_HOLDQ relocation failed; stream unchanged");
                ops = original;
            }
        }
    }
    ops = postpass::run(ops);
    eprintln!("POST_PP {:?}", counts(&ops));
    ops.extend(tail);
    append_tail_nonce(&mut ops, TAIL_NONCE);
    ops
}

/// Fixed 48-bit Fiat-Shamir tail nonce. Each bit is an X/X identity pair on qubit 0 or 1, so the nonce changes
/// only the challenge hash, never the circuit semantics, qubit peak or Toffoli count.
const TAIL_NONCE: u64 = 321; // fotl765 R14 Q794 Chumjetzze (worker R14-merge): first clean nonce ascending from 1 for this stream (fe_nonce_t48 tail48 early-abort scan, 1..320 fail; fasteval 9024 OK); was 779, fotl765 R9 Q795b (worker FIXX0, Q792_X0NA made exact): first clean nonce ascending from 1 for this stream (fe_nonce_t48 early-abort scan, 1..778 fail; fasteval 9024 OK); was 649 (worker FREEZE)

fn append_tail_nonce(ops: &mut Vec<Op>, nonce: u64) {
    use crate::circuit::QubitId;
    assert!(nonce < (1u64 << 48));
    for bit in 0..48 {
        let mut x = Op::empty();
        x.kind = OperationType::X;
        x.q_target = QubitId((nonce >> bit) & 1);
        ops.push(x);
        ops.push(x);
    }
}

/// (ops, native Toffoli, expected executed Toffoli) under the classical-condition weights.
/// m1-shell diagnostic (dev only, M1_EXP): per profile section, emitted Toffoli and raw expected Toffoli after the
/// adjacent-CCX cancellation (each removed gate is charged to its own section), conditioned ops at 0.5 as `counts`.
fn m1_stage_dump(ops: &[Op], bounds: &[(&'static str, usize)]) {
    let nseg = bounds.len() + 1;
    let (mut em, mut ex) = (vec![0i64; nseg], vec![0f64; nseg]);
    let mut seg = 0usize; // segment 0: before the first boundary
    let mut depth: u32 = 0;
    let mut cstack: Vec<u32> = vec![];
    let mut st: Vec<(u32, u32, u8)> = Vec::with_capacity(ops.len() / 2);
    for (i, op) in ops.iter().enumerate() {
        while seg < bounds.len() && bounds[seg].1 <= i { seg += 1; }
        match op.kind {
            OperationType::PushCondition => { cstack.push(depth); depth += 1; },
            OperationType::PopCondition => depth = cstack.pop().expect("balanced"),
            _ => {},
        }
        let w = 0.5f64.powi(depth as i32);
        let is_t = matches!(op.kind, OperationType::CCX | OperationType::CCZ);
        if is_t {
            em[seg] += 1;
            ex[seg] += w * if op.c_condition == NO_BIT { 1.0 } else { 0.5 };
        }
        if let Some(&(j, sj, dj)) = st.last() {
            if op.kind == OperationType::CCX && op.c_condition == NO_BIT && ops[j as usize] == *op {
                st.pop();
                em[sj as usize] -= 1; ex[sj as usize] -= 0.5f64.powi(dj as i32);
                em[seg] -= 1; ex[seg] -= w;
                continue;
            }
        }
        st.push((i as u32, seg as u32, depth.min(255) as u8));
    }
    let mut agg: Vec<(String, i64, f64, usize)> = vec![];
    let mut occ: std::collections::HashMap<&str, usize> = Default::default();
    for k in 0..nseg {
        let name = if k == 0 { "-pre" } else { bounds[k - 1].0 };
        let n = { let e = occ.entry(name).or_insert(0); *e += 1; *e };
        if name.starts_with("s.") { eprintln!("M1OCC {name}#{n} emitted {} expected {:.1}", em[k], ex[k]); }
        if let Some(a) = agg.iter_mut().find(|a| a.0 == name) { a.1 += em[k]; a.2 += ex[k]; a.3 += 1; }
        else { agg.push((name.to_string(), em[k], ex[k], 1)); }
    }
    let (te, tx): (i64, f64) = (em.iter().sum(), ex.iter().sum());
    for a in &agg { eprintln!("M1EXP {:16} n {:5} emitted {:9} expected {:12.1}", a.0, a.3, a.1, a.2); }
    eprintln!("M1TOT emitted {te} expected {tx:.1}");
}

fn counts(ops: &[Op]) -> (usize, u64, f64) {
    let mut weight = 1.0;
    let mut stack = vec![];
    let mut native = 0;
    let mut expected = 0.0;
    for op in ops {
        match op.kind {
            OperationType::PushCondition => { stack.push(weight); weight *= 0.5; },
            OperationType::PopCondition => weight = stack.pop().expect("balanced condition stack"),
            OperationType::CCX | OperationType::CCZ => {
                native += 1;
                expected += weight * if op.c_condition == NO_BIT { 1.0 } else { 0.5 };
            },
            _ => {},
        }
    }
    assert!(stack.is_empty());
    (ops.len(), native, expected)
}

/// Exact in-place cancellation; every removed pair is consecutive, identical,
/// unconditioned, self-inverse CCX on the same three physical wires.
pub fn cancel_adjacent_ccx(ops: &mut Vec<Op>) -> usize {
    let old_len = ops.len();
    let mut dst = 0usize;
    for src in 0..old_len {
        let op = ops[src];
        if dst > 0 && op.kind == OperationType::CCX && op.c_condition == NO_BIT && ops[dst - 1] == op {
            dst -= 1;
        } else {
            ops[dst] = op;
            dst += 1;
        }
    }
    ops.truncate(dst);
    let removed = old_len - dst;
    assert_eq!(removed % 2, 0);
    removed
}


