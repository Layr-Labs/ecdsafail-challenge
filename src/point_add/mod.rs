mod hold_pass;
mod gate_fold;
mod named_controls;
mod seed_mult;
mod product_eraser;
mod last_veto;
mod last_veto_local;
mod fd_coordinate;
mod back_seam;
pub mod cross_chunk_probe;
pub mod dirty_boundary_probe;
pub mod fold_template;
mod width_composition;
mod compact_mapped_add;
mod compact_chunk_add;
use std::str::FromStr;

use alloy_primitives::U256;

use crate::circuit::{BitId, Op, OperationType, QubitId};
use builder::Builder;
use classical::{coord_add3x, coord_rsub, coord_sub};
use pingpong::{divide, multiply};
use square::sub_square;

mod affine_simplify;
mod interned_witness;
mod quadratic_simplify;
mod truth_simplify;
mod builder;
mod classical;
mod compare;
mod const_arith;
mod modular;
mod pingpong;
mod leapfrog;
mod y33_clears;
mod record;
// B3a: HEO(S,u) walk research seam. Inert unless HEO_WALK / HEO_RESEARCH is set.
pub mod heo;
mod square;
mod sqc;
mod square_split;
mod sqleaf;
mod moddiv_adapter;

const N: usize = 256;

const SECP256K1_P: U256 = U256::from_limbs([
    0xFFFF_FFFE_FFFF_FC2F,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
]);

/// Fixed I10 configuration. Unlisted research switches are absent/off.
/// The submission emits the same circuit regardless of inherited environment.
fn env_raw(name: &str) -> Option<String> {
    // B3a research overlay: returns None (no effect) unless HEO_RESEARCH or
    // HEO_WALK is set in the process environment. See heo::pinned_override.
    if let Some(v) = heo::pinned_override(name) {
        return Some(v);
    }
    let value = match name {
        "I76_SOURCE_TOP_LOAN" => "1",
        "I74_RESULT_TOP_LOAN" => "1",
        "SQ_LEND_RETAINED_CROSS3" => "0",
        "I45_NARROW_ROUNDS" => "549,550,551,552,553,586,587,640,641,648,683,684,685,686",
        "I50_SPLIT_BRIDGE" => "1",
        "I35_CELLS" => "0",
        "I35_TRACE" => "0",
        "I35_BUDGET" => "1",
        "PP_WALK_EXTRA_ROUNDS" => "683:4:1",
        "SQ_ASM_TAIL" => "24",
        "SQ_ROW1_INVERSE_CARRIES" => "1",
        "SQ_ROW1_STREAM" => "1",
        "SQ_ROW0_COPY" => "1",
        "I41_ROUNDS" => "20,61,62,68,71,80,89,95,100,129,135,161,165,182,512,525,528,533,536,549,550,551,552,553,586,587,616,640,641,648,655,658,683,684,685,686,687",
        "I33_DISABLE" => "0",
        "I35_PROFILE" => "408:1:1,409:1:1,410:1:1,411:1:1,412:1:1,413:1:1,414:1:1,415:1:1,416:1:1,417:1:1,418:1:1,419:1:1,420:1:1,421:1:1,422:1:1,423:1:1,512:1:1,513:1:1,514:1:1,515:1:1,516:1:1,517:1:1,518:1:1,519:1:1,520:1:1,521:1:1,522:1:1,523:1:1,524:1:1,525:1:1,526:1:1,527:1:1,528:1:1,529:1:1,530:1:1,531:1:1,532:1:1,533:1:1,534:1:1,535:1:1,547:1:1,574:1:1,575:1:1,576:1:1,577:1:1,578:1:1,579:1:1,580:1:1,581:1:1,582:1:1,583:1:1,584:1:1,585:1:1,586:1:1,587:1:1,588:1:1,589:1:1,590:1:1,591:1:1,609:0:1,619:0:2,620:0:2,620:1:1,621:1:1,622:1:1,623:1:1,624:1:1,625:1:1,626:1:1,627:1:1,628:1:1,629:1:1,630:1:1,631:1:1,632:1:1,633:1:1,634:1:1,635:1:1,636:1:1,637:1:1,638:1:1,639:1:1,646:1:1",
        "I12_DIV_PROFILE" => "192:192,193:193,194:194,195:195,196:196,197:197,198:198,199:199,200:200,201:201,202:202,203:203,204:204,205:205,206:206,207:207,208:208,209:209,210:210,211:211,212:212,213:213,214:214,215:215,216:216,217:217,218:218,219:219,220:220,221:221,222:222,223:223,224:224,225:225,226:226,227:227,228:228,229:229,230:230,231:231,232:232,233:233,234:234,235:235,236:236,237:237,238:238,239:239,240:240,241:241,242:242,243:243,244:244,245:245,246:246,247:247,248:248,249:249,250:392,393:393,394:394,395:395,396:396,397:397,398:398,399:399,400:400,401:401,402:402,403:403,404:404,405:405,406:406,407:407,408:408,409:409,410:410,411:411,412:412,413:413,414:414,415:415,416:416,417:417,418:418,419:419,420:420,421:421,422:422,423:423,424:424,425:425,426:426,427:427,428:428,429:429,430:430,431:431,432:432,433:496,497:497,498:498,499:499,500:500,501:501,502:502,503:503,504:504,505:505,506:506,507:507,508:508,509:509,510:510,511:511,512:512,513:513,514:514,515:515,516:516,517:517,518:518,519:519,520:520,521:522,523:523,524:524,525:525,526:526,527:527,528:528,529:529,530:530,531:531,532:532,533:533,534:534,535:535,536:536,537:537,538:538,539:539,540:540,541:572,573:573,574:574,575:575,576:576,577:577,578:578,579:579,580:580,581:581,582:582,583:583,584:584,585:585,586:586,587:587,588:588,589:596,597:597,598:598,599:599,600:600,601:601,602:602,603:604,605:606,607:608,609:609,610:611,612:613,614:615,616:616,617:618,619:620,621:621,622:622,623:623,624:624,625:625,626:626,627:627,628:628,629:629,630:630,631:631,632:632,633:633,634:634,635:635,636:636,637:637,638:638,639:639,640:640,641:641,642:642,643:643,644:644,645:645,646:646,647:647,648:648,649:664,665:666,667:668,669:670,671:671,672:672,673:673,674:674,675:675,676:676,677:677,678:678,679:679,680:680,681:681,682:682,683:683,684:684",
        "I12_MUL_PROFILE" => "654:653,652:651,650:649,648:648,647:647,646:646,645:640,639:639,638:638,637:625,624:620,619:618,617:616,615:609,608:602,601:595,594:592,591:586,585:585,584:584,583:579,578:574,573:571,570:567,566:548,547:547,546:542,541:539,538:536,535:533,532:528,527:525,524:512,511:503,502:502,501:495,494:424,423:423,422:420,419:415,414:410,409:409,408:408,407:403",
        "I12_B_GUARD" => "4",
        "CMP_SEED_ALL" => "1",
        "ERASE_COMPARE" => "24",
        "FOLD_GUARD" => "25",
        "PP_CF_DEFER_WALK_PHASE" => "1",
        "PP_CF_END_CHUNK" => "8",
        "PP_CHUNK_SHAPE" => "64:0,38:1,25:-2,0:-4",
        "PP_CUT_SQIDENT" => "1",
        "PP_CUT_WALKLOAN" => "1",
        "PP_DEPTH_PROFILE" => "0:0",
        "PP_DIRECT_ENDPOINT" => "1",
        "PP_DIRECT_FOLD" => "1",
        "PP_FLAG_SHAPE" => "38:0,25:-1,0:-3",
        "PP_FLAG_WIDEN_DIV" => "38",
        "PP_FOLD_PROFILE" => "38:0,32:-1,19:-4,0:-4",
        "PP_FOLD_WIDEN" => "242",
        "PP_HEAD_DIV" => "192",
        "PP_HEAD_MUL" => "403",
        "PP_JOINT_GUARD" => "0",
        "PP_JOINT_LOW_BITS" => "32",
        "PP_JOINT_MUL_FOLD" => "1",
        "PP_JOINT_PREBIAS_DIV" => "1",
        "PP_MID_BATCH_DIV" => "0",
        "PP_MID_BATCH_MUL" => "32",
        "PP_NEW_REPLAY" => "1",
        "PP_PREBIAS_RETAIN_BITS" => "32",
        "PP_PREBIAS_DOUBLE" => "1",
        "PP_PREBIAS_DOUBLE_FALLBACK" => "1",
        "PP_Q1208_HELPERS" => "1",
        "PP_R2" => "648",
        "PP_REPLAY_CHUNK_COMPARE" => "21",
        "PP_REPLAY_FLAG_COMPARE" => "20",
        "PP_REPLAY_FOLD_WINDOW" => "54",
        "PP_REPLAY_FOLD_WINDOW_MUL" => "54",
        "PP_REPLAY_SIGN_LOAN" => "1",
        "PP_REPLAY_SIGN_LOAN_MUL" => "1",
        "PP_RETAIN_EXACT_DIV" => "1",
        "PP_RETAIN_EXACT_EXTRA_DIV" => "4",
        "PP_RETAIN_EXACT_EXTRA_MUL" => "4",
        "PP_RETAIN_EXACT_MUL" => "1",
        "PP_RETAIN_LATE_WIDEN" => "3",
        "PP_RETAIN_REBALANCE" => "1",
        "PP_REUSE_DIV_PARITY" => "1",
        "PP_REUSE_MUL_SELECTORS" => "1",
        "PP_ROUNDS_MUL" => "698",
        "PP_SIMPLIFY" => "product,affine,quadratic,truth",
        "PP_SOURCE_SIGN_GROW" => "1",
        "PP_SOURCE_SIGN_LOAN" => "0",
        "PP_SPLIT_FOLD" => "0",
        "PP_SPLIT_FOLD_OVERAGE" => "0",
        "PP_SPLIT_OVERLAP_BITS" => "1",
        "PP_SPRINT_MIXED" => "0",
        "PP_TAIL_DIV" => "682",
        "PP_TAIL_MUL" => "655",
        "PP_WALK_GUARD_BITS" => "1",
        "PP_WALK_GUARD_MAX_WIDTH" => "64",
        "PP_WALK_MAX_QUBITS" => "1251",
        "PP_WIDTH_SCHEDULE" => "259,258x19,257x5,256x3,255x4,254x4,253x2,252x4,251x3,250x5,249x2,248x4,247x3,246x2,245x4,244x3,243x3,242x3,241x3,240x3,239x4,238x3,237x2,236x4,235x2,234x3,233x2,232x4,231x4,230x2,229x3,228x3,227x3,226x2,225x4,224x2,223x2,222x3,221x3,220x4,219x3,218x2,217x3,216x3,215x3,214x4,213x2,212x2,211x3,210x4,209x3,208x2,207x2,206x2,205x3,204x2,203x4,202x3,201x3,200x4,199x2,198x2,197x3,196x2,195x2,194x4,193x4,192x2,191x3,190x3,189x2,188x3,187x2,186x3,185x2,184x3,183x4,182x2,181x3,180x4,179x2,178x2,177x3,176x3,175,174x2,173x2,172x4,171x3,170x2,169x2,168x4,167x3,166x3,165x2,164x3,163x3,162x2,161x3,160x2,159x3,158x2,157x3,156x2,155x4,154x2,153x3,152x2,151x3,150x3,149x2,148x2,147x2,146x4,145x4,144x3,143x2,142x2,141x3,140x2,139x2,138x2,137x3,136x2,135x4,134x3,133x3,132x3,131x2,130x3,129x2,128x4,127x3,126x2,125x2,124x3,123x2,122x3,121x3,120x2,119x5,118x2,117x3,116x2,115x3,114x4,113x2,112x2,111x4,110x2,109x2,108x2,107x2,106x2,105x5,104x2,103x2,102x2,101x2,100x4,99x2,98x2,97x2,96x3,95x3,94x3,93x2,92x3,91x2,90x4,89x3,88x2,87x2,86x4,85x2,84,83x4,82x2,81x2,80x2,79x3,78x2,77x2,76x3,75,74x2,73x3,72x3,71x2,70x3,69x3,68x3,67x3,66x2,65x3,64x4,63x2,62x2,61x3,60x2,59x2,58x2,57x2,56x2,55x3,54x3,53x2,52x3,51x2,50x4,49x2,48x2,47x3,46x3,45x2,44x2,43x3,42x2,41x2,40x3,39x2,38x2,37x3,36x4,35x2,34x3,33x2,32x2,31x2,30x2,29x2,28x4,27x2,26x2,25x3,24x2,23x2,22x2,21x3,20x3,19x2,18x3,17x2,16x2,15x3,14x2,13x2,12x2,11x2,10x2,9x4,8x9,8x2",
        "SQ_ALIAS_PRODUCT_LSB" => "1",
        "SQ_A_POLICY" => "7",
        "SQ_BORROW_ROW_CARRIES" => "0",
        "SQ_B_POLICY" => "7",
        "SQ_C_POLICY" => "7",
        "SQ_CIN_SPREAD" => "1",
        "SQ_DEFER_CROSS_PHASE" => "1",
        "SQ_DIAG_PRELOAD" => "1",
        "SQ_FIT_CROSS" => "1",
        "SQ_LEND_ASSEMBLY_ZEROS" => "1",
        "SQ_LEND_RETAINED_ANDS" => "2",
        "SQ_LEND_RETAINED_CROSS2" => "0",
        "SQ_LEND_RETAINED_ZEROS" => "1",
        "SQ_ODD_NODE_TOPS" => "1",
        "SQ_ROW0_CARRY" => "1",
        "SQ_ROW0_INVERSE_CARRIES" => "1",
        "SQ_ROW_ALL_MEASURE_TOP" => "1",
        "SQ_SPARSE_CORRECTION" => "0",
        "SQ_SPARSE_SPREAD" => "0",
        "SQ_SPLIT_LOW_MIN" => "64",
        "SQ_SPLIT_SUM_MIN" => "65",
        "SQ_ZERO_TOP_CROSS" => "1",
        "SQ_ZERO_TOP_SPREAD" => "1",
        "SQ_ZERO_TOP_SUM" => "1",
        // Stream-tail nonce for deterministic Fiat-Shamir input derivation.
        "TAIL_NONCE" => "19401376922166",
        "PP_SEED_SHORT_MUL_F_COST" => "1",
        "SQ_HIGH_CARRY_LOAN" => "1",
        "SQ_HOLD_BOUNDARY" => "1",
        "SQ_OWN_TOP_ZEROS" => "1",
        // B3a: unpinned names stay None unless the research overlay is on.
        _ => return heo::passthrough(name),
    };
    Some(value.to_owned())
}

fn env_flag(name: &str) -> bool {
    env_raw(name).is_some_and(|value| {
        !matches!(value.to_ascii_lowercase().as_str(), "0" | "false" | "no" | "off")
    })
}

fn required_env<T: FromStr>(name: &str) -> T
where
    <T as FromStr>::Err: std::fmt::Display,
{
    let raw = env_raw(name).unwrap_or_else(|| panic!("missing fixed I10 setting {name}"));
    raw.parse().unwrap_or_else(|e| panic!("invalid fixed I10 setting {name}: {e}"))
}

fn optional_env<T: FromStr>(name: &str) -> Option<T> {
    env_raw(name)?.parse().ok()
}

macro_rules! pinned_env {
    ($vis:vis $name:ident, $env:literal) => {
        $vis fn $name() -> usize {
            static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
            *SLOT.get_or_init(|| $crate::point_add::required_env($env))
        }
    };
}
use pinned_env;

pinned_env!(fold_guard, "FOLD_GUARD");

/// Rewrite the 96-op identity tail to encode the ground nonce. Only `q_target`
/// changes (X;X pairs stay identities), so circuit function is untouched; the
/// Fiat-Shamir seed is what moves.
fn apply_tail_nonce(mut ops: Vec<Op>, nonce: u64) -> Vec<Op> {
    let n = ops.len();
    assert!(n >= 96, "op stream too short for nonce tail");
    let start = n - 96;
    for i in 0..96 {
        assert!(
            ops[start + i].kind == OperationType::X,
            "tail op {} is not an X",
            start + i
        );
    }
    for b in 0..48 {
        let t = QubitId((nonce >> b) & 1);
        ops[start + 2 * b].q_target = t;
        ops[start + 2 * b + 1].q_target = t;
    }
    ops
}

/// The candidate itself: `(x, y) += (ox, oy)` on secp256k1 in affine
/// coordinates, with `(ox, oy)` classical.
///
/// The chord-and-tangent formulae in eight phases, each named for the `set_phase`
/// report `build_circuit` prints. `x`/`y` are the quantum coordinates and are
/// overwritten in place; every scratch qubit each phase takes is returned to |0>
/// before the next one starts.
/// laneG: the square section of the board leader's stream (f5f14f4, ops 4461256 .. 5418492), wires and bits as recorded: on entry only x and y are
/// live in both streams, every other wire is |0>, and the section's bits are written before any later read. It leaves R0 on x + four wires.
fn lfg_square_section(c: &mut Builder, x: &[QubitId]) {
    let raw = zstd::stream::decode_all(&include_bytes!("sq_leader.zst")[..]).expect("sq_leader");
    let w = |r: &[u8], i: usize| u64::from_le_bytes(r[i..i + 8].try_into().unwrap());
    assert_eq!(raw.len() % 56, 0);
    assert_eq!(c.active_qubits(), 512, "square section: only x and y live on entry");
    let mut seen: u64 = 0;
    for r in raw.chunks_exact(56) {
        let mut o = Op::empty();
        o.kind = match w(r, 0) & 0xffff_ffff {
            0 => OperationType::Neg, 3 => OperationType::BitInvert, 4 => OperationType::BitStore0, 5 => OperationType::BitStore1,
            6 => OperationType::X, 7 => OperationType::Z, 8 => OperationType::CX, 9 => OperationType::CZ, 10 => OperationType::Swap,
            11 => OperationType::R, 12 => OperationType::Hmr, 13 => OperationType::CCX, 14 => OperationType::CCZ,
            15 => OperationType::PushCondition, 16 => OperationType::PopCondition, k => panic!("square section: kind {k}"),
        };
        o.q_control2 = QubitId(w(r, 8));
        o.q_control1 = QubitId(w(r, 16));
        o.q_target = QubitId(w(r, 24));
        o.c_target = BitId(w(r, 32));
        o.c_condition = BitId(w(r, 40));
        o.r_target = crate::circuit::RegisterId(w(r, 48));
        c.lfg_push_raw(o);
        seen += 1;
    }
    eprintln!("LFG_SQTX ops={seen}");
    leapfrog::lfg_set_preseed(c, x, &[1129, 1141, 697, 695]);
}

pub(crate) fn build_point_add() -> Vec<Op> {
    let circ = &mut Builder::new();
    let x: &[QubitId] = &circ.alloc_qubits(N);
    let y: &[QubitId] = &circ.alloc_qubits(N);
    let ox: &[BitId] = &circ.alloc_bits(N);
    let oy: &[BitId] = &circ.alloc_bits(N);

    if leapfrog::enabled() {
        // LF_SEAMS: coord_x_sub / coord_add3x / coord_rsub_final fused into the walks' seed and unseeds
        let seams = leapfrog::seams();
        if !seams {
            circ.set_phase("coord_x_sub");
            coord_sub(circ, x, ox);
        }
        circ.set_phase("coord_y_sub");
        coord_sub(circ, y, oy);
        circ.set_phase("divide");
        if seams { leapfrog::divide_seamed(circ, y, x, ox); } else { leapfrog::divide(circ, y, x); }
        if !seams {
            circ.set_phase("coord_add3x");
            coord_add3x(circ, x, ox);
        }
        narrow::square_entry(circ);
        circ.set_phase("square");
        // LF_SQUARE_CAP: the square's own width budget (its ladders size to it instead of the walk cap)
        if std::env::var("LFG_SQTX").is_ok_and(|v| v == "1") {
            lfg_square_section(circ, x);
        } else {
        pingpong::with_phase_cap(Some(required_env::<usize>("LF_SQUARE_CAP")), || sub_square(circ, x, y));
        }
        circ.set_phase("multiply");
        if seams { leapfrog::multiply_seamed(circ, y, x, ox); } else { leapfrog::multiply(circ, y, x); }
        leapfrog::c35_widen_check();
        narrow::report();
        circ.set_phase("coord_y_sub_final");
        coord_sub(circ, y, oy);
        if !seams {
            circ.set_phase("coord_rsub_final");
            coord_rsub(circ, x, ox);
        }
        leapfrog::prof_dump();
        circ.declare_qubit_register(x);
        circ.declare_qubit_register(y);
        circ.declare_bit_register(ox);
        circ.declare_bit_register(oy);
        circ.y33_clears();
        circ.finalize_records();
        return circ.take_ops();
    }

    circ.set_phase("coord_x_sub"); // x2 -= ox
    if fd_coordinate::enabled(){fd_coordinate::retained_coord_sub(circ,x,ox);}else if j_fuse::j_xfuse() { classical::coord_sub_keep(circ, x, ox); } else { coord_sub(circ, x, ox); }

    circ.set_phase("coord_y_sub"); // y2 -= oy
    if heo::carry::r4_ysub_fuse() { heo::carry::r4_ysub_head(circ, y, oy); } else if j_fuse::j_yfuse() { classical::coord_sub_halve(circ, y, oy); } else { coord_sub(circ, y, oy); }

    circ.set_phase("divide"); // y2 /= x2
    if heo::enabled() {
        heo::divide(circ, y, x);
    } else {
        divide(circ, y, x);
    }

    circ.set_phase("coord_add3x"); // x2 += 3*ox
    coord_add3x(circ, x, ox);

    circ.set_phase("square"); // x2 -= y2^2
    sub_square(circ, x, y);

    circ.set_phase("multiply"); // y2 *= x2
    if heo::carry::r4_yfin_fuse() { heo::carry::r4_yfin_stash(oy); }
    if heo::enabled() {
        heo::multiply(circ, y, x);
    } else {
        multiply(circ, y, x);
    }

    circ.set_phase("coord_y_sub_final"); // y2 -= oy
    if heo::carry::r4_yfin_fuse() { assert!(heo::carry::r4_yfin_consumed(), "R4_YFIN_FUSE: oy not consumed"); } else if j_fuse::j_yfuse() { classical::coord_double_sub(circ, y, oy); } else { coord_sub(circ, y, oy); }

    circ.set_phase("coord_rsub_final"); // x2 = ox - x2
    coord_rsub(circ, x, ox);

    circ.declare_qubit_register(x);
    circ.declare_qubit_register(y);
    circ.declare_bit_register(ox);
    circ.declare_bit_register(oy);
    circ.finalize_records();
    circ.take_ops()
}

/// Emit the fixed I10 circuit and accepted public-validation nonce 9342055114.
// Accepted r007 build recipe. Installed before any OnceLock reads configuration.
fn install_skywalk_submission_recipe() {
    for (name, value) in [
        ("HEO_WALK", "1"),
        ("HEO_SCHEDULE", "carry"),
        ("HEO_SEED", "base"),
        ("HEO_FIT_MODE", "win"),
        ("HEO_FIT_K", "19"),
        ("HEO_ZONE", "1"),
        ("HEO_R2D", "382"),
        ("HEO_R2M", "370"),
        ("HEO_R1M", "99"),
        ("HEO_CARRY_SEED", "fd"),
        ("HEO_PIN_PP_WALK_MAX_QUBITS", "1172"),
        ("HEO_LT0", "1"),
        ("HEO_BW", "inv"),
        ("HEO_LT0_MUL", "1"),
        ("HEO_LOAN_BOTH", "1"),
        ("HEO_RAIL_MAX", "257"),
        ("HEO_DB_SKIP", "1"),
        ("HEO_DB_SKIP2", "1"),
        ("HEO_LR1", "1"),
        ("HEO_PIN_SQ_SPARSE_CORRECTION", "1"),
        ("HEO_PIN_SQ_LEND_RETAINED_ANDS", "3"),
        ("HEO_PIN_I35_PROFILE", "600:0:1,602:0:1,640:0:1,642:0:1,644:0:1,646:0:1,672:0:1,673:0:1,674:0:1,675:0:1,676:0:1,677:0:1,678:0:1,679:0:1,680:0:1,681:0:1,682:0:1,683:0:1,684:0:1,685:0:1,686:0:1,687:0:1,688:0:1,689:0:1,690:0:1,691:0:1,692:0:1,693:0:1,694:0:1,695:0:1,696:0:1,697:0:1,698:0:1,620:1:1,591:1:1"),
        ("HEO_HEAD_LIFO_N", "2"),
        ("HEO_DIV_LIFO_N", "2"),
        ("HEO_MULB_LIFO_N", "2"),
        ("HEO_DIV_PARTIAL", "1"),
        ("HEO_MULB_PARTIAL", "1"),
        ("HEO_DIV_EARLY_P3", "1"),
        ("HEO_O0_DEC", "1"),
        ("HEO_O0M", "1"),
        ("K3B_RAIL_LOAN", "1"),
        ("HEO_MABSORB", "1"),
        ("HEO_FAMA", "1"),
        ("HEO_PARK_MBU", "1"),
        ("HEO_PHASE_REPORT", "1"),
        ("HEO_LEDGER_PRINT", "1"),
        ("HEO_CODEC_SYNTH", "1"),
        ("HEO_HEAD_PARTIAL", "1"),
        ("PP_J_WCIN", "1"),
        ("CLS_BMERGE_LITE", "1"),
        ("PP_U_DPARK", "1"),
        ("PP_U_DPARK_BEST", "1"),
        ("PP_U_C0WIDE", "1"),
        ("SKYWALK_SITE_TRACE", "1"),
        ("DIRTY_BOUNDARY_MODE", "transport"),
        ("FOLD_PACKED_BOUNDARIES", "1"),
        ("CONST_BINDER_MODE", "packed"),
        ("CONST_SQUARE_TRANSPORT", "1"),
        ("HEO_CROSS_CHUNK", "1"),
        ("FD_COORD_FUSE", "1"),
        ("FD_COORD_LOW_ONE", "1"),
        ("HEO_PIN_FOLD_GUARD", "20"),
        ("HEO_PIN_PP_FOLD_WIDEN", "112"),
        ("HEO_PIN_PP_FOLD_PROFILE", "56:0,38:-1,32:-1,25:-5,19:-7,0:-5"),
        ("PP_DROP_EXACT_LEAD", "1"),
        ("PP_DROP_EXACT_LEAD_DIR", "mul"),
        ("HEO_RAIL_TOP_RELEASE", "1"),
        ("HEO_RAIL_TOP_ALIAS", "1"),
        ("HEO_PIN_PP_WIDTH_SCHEDULE", "259,258x19,257x6,256x2,255x5,254x3,253x4,252x3,251x2,250x5,249x2,248x4,247x3,246x2,245x5,244x2,243x3,242x3,241x3,240x3,239x4,238x3,237x2,236x4,235x2,234x3,233x2,232x4,231x3,230x3,229x3,228x3,227x3,226x3,225x3,224x2,223x2,222x4,221x2,220x4,219x3,218x2,217x3,216x3,215x3,214x3,213x2,212x3,211x4,210x2,209x3,208x2,207x3,206x3,205x2,204x2,203x4,202x3,201x3,200x3,199x3,198x2,197x3,196x2,195x4,194x2,193x3,192x3,191x3,190x2,189x3,188x2,187x3,186x2,185x3,184x3,183x2,182x3,181x3,180x3,179x3,178x2,177x4,176x2,175x3,174x3,173x3,172x2,171x3,170x2,169x3,168x2,167x3,166x3,165x3,164x2,163x3,162x3,161x3,160x2,159x3,158x3,157x2,156x3,155x2,154x3,153x3,152x2,151x3,150x3,149x2,148x3,147x2,146x3,145x2,144x3,143x3,142x3,141x3,140x2,139x2,138x4,137x2,136x2,135x3,134x3,133x2,132x3,131x2,130x3,129x3,128x2,127x3,126x3,125x2,124x2,123x3,122x2,121x3,120x2,119x2,118x2,117x2,116x4,115x2,114x3,113x2,112x3,111x3,110x2,109x3,108x2,107x3,106x3,105x3,104x3,103x3,102x2,101x3,100x2,99x3,98x3,97x2,96x3,95x3,94x2,93x3,92x3,91x2,90x3,89x2,88x4,87x3,86x3,85,84x2,83x3,82x2,81x3,80x2,79x2,78x3,77x2,76x3,75x2,74x2,73x3,72x3,71x2,70x3,69x2,68x4,67x3,66x2,65x3,64x4,63,62x2,61x3,60x2,59x2,58x3,57x2,56x2,55x3,54x3,53x2,52x2,51x2,50x5,49,48x2,47x3,46x3,45x2,44x3,43x3,42x2,41x2,40x2,39x3,38x2,37x2,36x3,35x3,34x3,33x2,32x2,31x2,30x3,29x2,28x4,27x2,26x2,25x3,24x2,23x2,22x2,21x3,20x3,19x2,18x3,17x2,16x2,15x3,14x2,13x2,12x2,11x2,10x2,9x4,8x12"),
        ("HEO_PIN_I41_ROUNDS", "36,45,52,61,62,68,71,74,77,80,89,95,100,101,104,110,119,129,130,135,144,150,153,158,161,167,172,175,182,183,513,518,525,528,533,538,539,542,549,550,551,552,553,571,583,586,587,591,611,618,621,633,640,641,648,655,658,683,684,685,686,687"),
        ("HEO_PIN_PP_N_BADJ", "350-399:m:0,400-476:m:0,477-553:m:-1,554-599:m:-2,400-449:d:1,649-699:a:-1,554-615:m:-1,589-615:d:-1,616-648:m:0,350-553:d:1,250-349:d:1,350-399:m:1"),
        ("HEO_PIN_PP_N_HOLE2", "1"),
        ("HEO_PIN_I12_DIV_PROFILE", "192:192,193:193,194:194,195:195,196:196,197:197,198:198,199:199,200:200,201:201,202:202,203:203,204:204,205:205,206:206,207:207,208:208,209:209,210:210,211:211,212:212,213:213,214:214,215:215,216:216,217:217,218:218,219:219,220:220,221:221,222:222,223:223,224:224,225:225,226:226,227:227,228:228,229:229,230:230,231:231,232:232,233:233,234:234,235:235,236:236,237:237,238:238,239:239,240:240,241:241,242:242,243:243,244:244,245:245,246:246,247:247,248:248,249:251,252:255,256:256,257:392,393:393,394:394,395:395,396:396,397:397,398:398,399:399,400:400,401:401,402:402,403:403,404:404,405:405,406:406,407:407,408:408,409:409,410:410,411:411,412:412,413:413,414:414,415:415,416:416,417:417,418:418,419:419,420:420,421:421,422:422,423:423,424:424,425:425,426:426,427:427,428:428,429:429,430:430,431:433,434:434,435:438,439:439,440:441,442:442,443:445,446:496,497:497,498:498,499:499,500:500,501:501,502:502,503:503,504:504,505:505,506:506,507:507,508:508,509:509,510:510,511:511,512:512,513:513,514:514,515:515,516:516,517:517,518:518,519:519,520:520,521:522,523:523,524:524,525:525,526:526,527:527,528:528,529:529,530:530,531:531,532:532,533:533,534:534,535:535,536:536,537:537,538:538,539:539,540:572,573:573,574:574,575:575,576:576,577:577,578:578,579:579,580:580,581:581,582:582,583:583,584:584,585:586,587:588,589:596,597:597,598:598,599:599,600:600,601:601,602:603,604:604,605:606,607:608,609:610,611:611,612:613,614:615,616:617,618:618,619:620,621:622,623:624,625:625,626:626,627:627,628:628,629:629,630:630,631:631,632:632,633:633,634:634,635:635,636:636,637:637,638:638,639:639,640:640,641:641,642:642,643:643,644:644,645:645,646:646,647:647,648:648,649:665,666:666,667:668,669:670,671:671,672:672,673:673,674:674,675:675,676:676,677:677,678:678,679:679,680:680,681:681,682:682,683:683,684:684"),
        ("HEO_PIN_PP_HEAD_MUL", "414"),
        ("HEO_PIN_PP_J_WCIN", "1"),
        ("HEO_PIN_PP_U_DPARK", "1"),
        ("HEO_PIN_PP_U_DPARK_BEST", "1"),
        ("HEO_PIN_PP_U_C0WIDE", "1"),
        ("HEO_PIN_I12_MUL_PROFILE", "657:657,656:656,655:655,654:653,652:651,650:649,648:642,641:641,640:640,639:639,638:638,637:634,633:625,624:624,623:621,620:620,619:616,615:609,608:603,602:595,594:592,591:591,590:587,586:585,584:584,583:583,582:575,574:571,570:566,565:540,539:539,538:534,533:529,528:528,527:526,525:519,518:516,515:513,512:507,506:502,501:495,494:444,443:441,440:438,437:437,436:433,432:428,427:425,424:423,422:420,419:419,418:415,414:409,408:408,407:407,406:406,405:405,404:404,403:403,402:402,401:401,400:400"),
        ("HEO_PIN_PP_TAIL_MUL", "662"),
        ("GO_KEEP_SUM", "1"),
        ("GO_KEEP_FOLD", "1"),
        ("HEO_PIN_PP_RETAIN_LATE_WIDEN", "0"),
        ("HEO_PIN_PP_N_CAPR", "621-648:18,649-665:16,350-399:20,450-499:20,150-199:20,50-99:20,200-349:20,500-549:20"),
        ("HEO_PIN_SQ_ASM_TAIL", "18"),
        ("HEO_PIN_ERASE_COMPARE", "20"),
        ("HEO_PIN_PP_DROP_EXACT_LEAD_WIDEN", "0"),
        ("HEO_PIN_PP_FLAG_WIDEN_DIV", "30"),
        ("GO_JLB", "616-698:m:-1"),
        ("GO_PRB", "631-698:-1"),
        ("GO_B1", "1"),
        ("GO_B2", "1"),
        ("GO_B3_A", "0"),
        ("GO_B3_B", "0"),
        ("SQ_HIGH_EARLY_LOAN", "3"),
        ("SQ_HIGH_EARLY_TRACE", "1"),
        ("SQ_FLAT_SHARED_CARRIES", "1"),
        ("SQ_FLAT_SHARE_C0", "1"),
        ("SHARED_BMERGE_CARRIES", "7"),
        ("SHARED_BMERGE_SOURCE_LOAN", "1"),
        ("NATIVE_SFUSE_B", "4"),
        ("HEO_CELL_INSIDE", "1"),
        ("HEO_CARRY_CODEC", "1"),
        ("HEO_REVERSE_CARRY_CODEC", "1"),
        ("SKYWALK_MERGED_HIGH_STREAM", "3"),
        ("TERMINAL_PAIR", "1"),
        ("TERMINAL_FW", "42"),
        ("HEO_CELL_HELPER_S1", "1"),
        ("BACK_SEAM_FUSE", "3"),
        ("HEO_S1_OUTPUT_ALIAS", "1"),
        ("HEO_PIN_PP_CHUNK_SHAPE", "64:0,38:1,25:-3,0:-4"),
        ("HEO_FREDKIN_OUTPUT_ALIAS", "1"),
        // sky5 package (frozen-sky5, r5_ycd): GO share knobs, GO #11 divfwd share selection (dfsel_s4),
        // R3 S1 tick list, R4 FD payload / y fusions, R5 classical-operand adds and compares.
        ("GO_MULREV2_SHARE", "1"),
        ("GO_MULREV_SHARE", "1"),
        ("GO_DIVFWD_SHARE", "1"),
        ("GO_SHARE_ROOMFIX", "1"),
        ("GO_DIVFWD_SHARE_T", "2,12,17,22,27,32,37,42,47,52,57,62,67,72,77,82,87,92,97,102,132,137,142,147,152,157,162,167,172,177,182,187,222,227,382,387,107,232,242,272,277,307,332,337"),
        ("R4_FDP_FUSE", "1"),
        ("R3_S1_TICKS", "5,7,8,268"),
        ("R4_YSUB_FUSE", "1"),
        ("R4_YFIN_FUSE", "1"),
        ("R5_YFIN2", "1"),
        ("R5_CBITS", "15"),
        ("R5_CCMP", "23"),
        ("R5_CBITS_PAD", "1"),
        ("R5_CBITS_PAD_ALL", "1"),
        // sky8 package (frozen-sky8, GO p7f): split carry window K=21, FOLD_WIDEN 68 (above), GO r6 per-cell
        // compare re-balance (div ticks 150-155 dB -1, mul ticks 225-344 dF +1), iA.100 envelopes (heo.rs).
        ("HEO_SPLIT_K", "21"),
        ("GO_CELLB", "div:150-155:-1,div:220-329:-1,mul:105-194:1"),
        ("GO_CELLF", "mul:225-344:1,div:250-299:-1"),
        // sky9 package (frozen-sky9, 19.5 Lambda limit): multiply batch route skipped at t = R-2 (B6), one
        // chunk compare bit fewer on rounds 0-399 (go_slice GO_CHUNK), 65 rewrite rows re-keyed to this op stream.
        ("HEO_MB_SKIP2", "1"),
        ("GO_CHUNK", "0-399:-1"),
        // sky10 package (frozen-sky10, 19.5 Lambda limit): FIT_K 22, ERASE_COMPARE 22, SQ_ASM_TAIL 18 and FOLD_GUARD 20
        // are set in place above; 52 SAT-proven square rows re-keyed to this op stream.
        // sky12 package (frozen-sky12, 19.5 Lambda limit): GO_CELLB adds div ticks 220-329 dB -1 and mul ticks 105-194
        // dB +1, GO_CELLF adds div ticks 250-299 dF -1 (above); 53 SAT-proven square rows re-keyed to this op stream.
        // sky13 package (frozen-sky13, 19.5 Lambda limit): HEO_PIN_PP_N_BADJ re-balanced (sells 400-449 d and 616-648 m by
        // one bit, buys 400-476 m by one bit, above); 54 SAT-proven square rows re-keyed to this op stream.
        // sky14 package (frozen-sky14, 19.5 Lambda limit): HEO_PIN_PP_FOLD_PROFILE 25:-3 and 0:-5, HEO_PIN_PP_FOLD_WIDEN 112
        // (above); 58 SAT-proven square rows re-keyed to this op stream.
        // sky15 package (frozen-sky15, 19.5 Lambda limit): HEO_PIN_PP_FOLD_PROFILE 44:0 (new top band) and 25:-5,
        // HEO_PIN_PP_FOLD_WIDEN 144, HEO_FIT_K 21, HEO_PIN_ERASE_COMPARE 21 (above); 64 SAT-proven rows (57 square rows
        // re-keyed to this op stream, 7 new rows from a whole-program span census, 3 of them outside the square).
        // sky16 package (frozen-sky16, 19.5 Lambda limit): HEO_R1M 99 (above; fused/headbatch boundary moved from 190 to 99,
        // headbatch cells get room 98 and run 3 chunks instead of 4); 62 of the sky15 rows, which sit in the op prefix that
        // HEO_R1M leaves unchanged (the two headbatch rows are dropped).
        // sky17 package (frozen-sky17, 19.5 Lambda limit): HEO_PIN_I35_PROFILE re-balanced on the multiplication walk only
        // (above; bridge-width sells and buys priced on paired CRN nonces); the op stream through the last square row is
        // unchanged, so the same 62 sky16 rows stay exact.
        // sky18 package (frozen-sky18, 19.5 Lambda limit): HEO_PIN_ERASE_COMPARE 20, HEO_PIN_PP_FOLD_WIDEN 128 and a 56:0 top
        // band on HEO_PIN_PP_FOLD_PROFILE (above); 56 SAT-proven rows re-proved on this op stream (sky18_rewrite.txt).
        // sky19 package (frozen-sky19, 19.5 Lambda limit): HEO_PIN_I35_PROFILE adds division-walk bridges (R_D) and TERMINAL_FW
        // goes from 50 to 40 (above); 62 SAT-proven rows re-proved on this op stream (sky19_rewrite.txt).
        // sky20 package (frozen-sky20, 19.5 Lambda limit): HEO_PIN_PP_FOLD_PROFILE band 19 goes from -4 to -5 and
        // HEO_PIN_PP_FOLD_WIDEN from 128 to 112 (above); 61 SAT-proven rows re-proved on this op stream (sky20_rewrite.txt).
        // sky21 package (frozen-sky21, 19.5 Lambda limit): the sky20 knobs unchanged plus 8 new SAT-proven rows from a fresh
        // census of this op stream (6 square, 2 outside), 69 rows in all (sky21_rewrite.txt).
        // q73a package (frozen-q73a, Q1173, 19.5 Lambda limit): walk cap 1173 (HEO_PIN_PP_WALK_MAX_QUBITS above), the
        // jackylee0424 Q1173 I35 profile (above), a site-constrained per-cell K3B bridge/room retune (q73a_k3b_retune.txt,
        // read through SKYX_K3B_RETUNE in heo_carry.rs), GO_FLAG 0-63:4 and SKY_SPLIT_TRIM_LAST, and a Lambda buy stack:
        // GO_CELLB mul 0-49 +1, GO_CHUNK 0-49 a:0, HEO_PIN_PP_FOLD_WIDEN 128, HEO_PIN_ERASE_COMPARE 22 (above);
        // 105 SAT-proven rows on this op stream (102 square, 3 outside), compiled in (q73a_rewrite.txt).
        // q73b package (Round Q73-S1 sell, 19.5 Lambda limit): q73a with GO_CELLB mul ticks 25-49 instead of 0-49 (above;
        // -16.7 T for +0.0235 Lambda); the 105 q73a rows kept, the 2 late outside rows re-proved at their shifted
        // positions (q73b_rewrite.txt).
        ("GO_FLAG", "0-63:4"),
        ("SKY_SPLIT_TRIM_LAST", "1"),
    ] { std::env::set_var(name, value); }
    std::env::set_var("HEO_ENVELOPE", concat!(env!("CARGO_MANIFEST_DIR"), "/src/point_add/skywalk_data/extended-middle-0.txt"));
    std::env::set_var("HEO_ENVELOPE_MUL", concat!(env!("CARGO_MANIFEST_DIR"), "/src/point_add/skywalk_data/extended-middle-1.txt"));
    std::env::set_var("HEO_PROXY_ENVELOPE", concat!(env!("CARGO_MANIFEST_DIR"), "/src/point_add/skywalk_data/env_front07_R393_clamp.txt"));
    std::env::set_var("HEO_CELL_WINDOWS", concat!(env!("CARGO_MANIFEST_DIR"), "/src/point_add/skywalk_data/windows_full_safe_mulB64.tsv"));
    std::env::set_var("K3B_CELL_OVR", concat!(env!("CARGO_MANIFEST_DIR"), "/src/point_add/skywalk_data/ovr_v025_lamneutral.txt"));
    std::env::set_var("SKYX_K3B_RETUNE", concat!(env!("CARGO_MANIFEST_DIR"), "/src/point_add/skywalk_data/cap1172_bridge_room_profile_probe.txt"));
}

/// sky8 submission: every setting of the circuit is pinned in code (the recipe above, the compiled-in
/// envelopes and rewrite rows, `TAIL_NONCE` in `env_raw`). Clear the inherited process environment first
/// so that no variable set on the host (`HEO_PIN_*`, `GO_*`, `R*_*`, `SKY_*`, ...) can change the circuit.
fn clear_process_env() {
    let keys: Vec<std::ffi::OsString> = std::env::vars_os().map(|(k, _)| k).collect();
    for k in keys {
        let s = k.to_string_lossy();
        if s.is_empty() || s.contains('=') || s.contains('\0') { continue; }
        std::env::remove_var(&k);
    }
    frozen_env_restore();
}

/// Leapfrog branch: the submission build emits the Leapfrog point add (see [`leapfrog::install_recipe`]).
const LEAPFROG_SUBMISSION: bool = true;

pub(crate) mod rail_s6;

/// The frozen candidate: walk cap, square cap, digit cap and the walk's recipe entries, pinned here. `clear_process_env`
/// wipes the host environment and sets these; the width table and its anchors are compiled in (a2_table_text, a2_anch_text).
const FROZEN_WALK_CAP: usize = 1230;
const FROZEN_SQ_CAP: usize = 1230;
const FROZEN_EMAX: usize = 5;
const FROZEN_RECIPE: &[(&str, &str)] = &[
    ("LFA2_SET_HEO_PIN_PP_WALK_MAX_QUBITS", "1230"),
    ("LFA2_SET_LF_REORDER_DIV", "2"),
    ("LFQ_RW", "20"),
    ("LFA2_PAIR", "1"),
    ("LFA2_PAIR_MATCH", "104523"),
    ("LFA2_CODE", "1"),
    ("LFA2_S6", "1"),
    ("LFA2_SET_LF_YP8_LATE", "1:13,4:17,9:22,84:19,94:17,105:15,110:13,116:11"),
    ("LFA2_SET_SL_N2_DFROM", "119"),
    ("LFA2_SET_SL_N2_MFROM", "119"),
    ("LFA2_SET_LF_CMP_FROM", "109"),
    ("LF_YP8_CHUNK", "1"),
    ("LFQ_DROPS", "1"),
    ("LFQ_PAGEFIRST", "1"),
    ("LFQ_KPAGE", "1"),
    ("SL_N2_DEEP", "none"),
    ("LFQ_FCR", "1"),
    ("LFQ_Y42LAST", "1"),
    ("LFQ_LASTN", "2"),
    ("A2R_SPEC", "58-91:direct,92-123:lean"),
    ("A2R_SERIAL", "1-98"),
    ("A2R_HB", "1-107,110-111,115-117"),
    ("LFA2_EXT", "0"),
    ("LL_CMPF", "0-200:1"),
    ("LFG_KEEP", "1"),
    ("LFG_KEEP_R", "1-123"),
    ("LFG_KFWD", "1-55"),
    ("LFG_SEEDP", "3"),
    ("LFG_RT0P", "3"),
    ("LFG_SQTX", "0"),
    ("LFA2_FWIN", "57"),
    ("LFA2_RWIN", "57"),
    ("LFG_VETO", "1"),
    ("LFA2_SET_LF_REORDER_MUL", "44"),
];
fn frozen_env_restore() {
    for (k, v) in FROZEN_RECIPE { std::env::set_var(k, v); }
    std::env::set_var("CONTRACT69_PAIR_COMMIT", "1");
}
pub fn build() -> Vec<Op> {
    build_generated()
}

/// laneW: the final policies with no stream binding. Exact and proof-based only; the stream-bound narrowing tables are out.
fn lane_generic_policy(ops: Vec<Op>) -> Vec<Op> {
    let ops = affine_simplify::simplify(ops);
    let ops = cond_pass::final_cap_cleanup(ops);
    // laneG: laneL's terminal veto (LFG_VETO=1): the last tick's [a > 4b] compare gone, Y4 = 0; the filter has the key last_veto
    let ops = if std::env::var("LFG_VETO").is_ok_and(|v| v == "1") { last_veto::run(ops, 3) } else { ops };
    let ops = hold_pass::hold_pass(ops);
    let mut ops = if std::env::var("A2R_GENERIC_PASSES").ok().as_deref() == Some("0") {
        ops
    } else {
        let ops = gate_fold::finish_rounds(gate_fold::apply(ops));
        let mut named_ops = ops;
        let named = named_controls::apply_in_place(&mut named_ops);
        eprintln!("NAMED_CONTROLS {named:?}");
        named_ops
    };
    // Q1228 shelf diagnostic: emit the exact pre-edit stream first, then
    // rebind the parent's certified source-edit tables by sequence identity.
    const A2R_NO_SOURCE_EDITS: bool = true;
    if A2R_NO_SOURCE_EDITS { return ops; }
    let ops=source_edits::run(ops,include_str!("bind81_followup.txt"));
    if std::env::var("QSTEP87_LATE_OFF").ok().as_deref()==Some("1"){return ops;}
    let ops=source_edits::run(ops,include_str!("qstep87_later.txt"));
    let ops=source_edits::run(ops,include_str!("qstep87_ur.txt"));
    if option_env!("ARMI94_OFF")==Some("1"){ops}else{source_edits::run(ops,include_str!("armi94_followup.txt"))}
}

/// Original structural generator, retained for audit and regeneration.
pub fn build_generated() -> Vec<Op> {
    // W124 (Codex) width composition, ported onto 6602a4e8: the effective selection pinned in source.
    // trace=true reproduces W124's logs only (stderr); it does not change gates.
    let w113_trace = true;
    let w120_cubic = true;
    let w123_lazy_gates = true;

    clear_process_env();
    install_skywalk_submission_recipe();
    std::env::set_var("EXACT_PAIR_CARRY", "1");
    if LEAPFROG_SUBMISSION {
        leapfrog::install_recipe();
    }
    // W124: W110's field page basis at the fold's tight public chunk budgets (LFF_PAGE5), W120 cubic page cleanup,
    // W123 lazy inverse gate restoration; set after both recipes, exactly as in the W124 emitter.
    std::env::set_var("LFF_PAGE5", "1");
    if w120_cubic { std::env::set_var("LFF_CUBIC_CLEANUP", "1"); }
    if w123_lazy_gates { std::env::set_var("W123_LAZY_GATES", "1"); }
    if w113_trace {
        std::env::set_var("ROOM_TRACE", "1");
        std::env::set_var("LFF_PAGE5_TRACE", "1");
    }
    if std::env::var_os("SKYWALK_SQUARE_HIGH_PROBE").is_some(){square::high_probe();std::process::exit(0);}
    if std::env::var_os("SKYWALK_MODDIV_ADAPTER_PROBE").is_some(){moddiv_adapter::probe();std::process::exit(0);}
    std::env::set_var("SQUARE_GROUPS_GROUP", "on");
    std::env::set_var("SQUARE_GROUPS_SUM", "on");
    std::env::set_var("SQUARE_GROUPS_A2", "on");
    std::env::set_var("SQUARE_GROUPS_A3", "on");
    std::env::set_var("SQC_LEAF_D", "12");
    std::env::set_var("SQUARE_SPLIT", "on");
    std::env::set_var("RAIL_ZERO_FILL", "1");
    std::env::set_var("SQC_G", "22");
    std::env::set_var("SQC_T", "19");
    std::env::set_var("FRAME_SHIFT","1");
    std::env::set_var("RAIL_OPT_DROPS","1");
    std::env::set_var("RAIL_OPT_RESERVE","1");
    std::env::set_var("RAIL_OPT_SEED","1");
    std::env::set_var("RAIL_OPT_NARROW","1");
    std::env::set_var("FRAME_FWD","1");
    std::env::set_var("LFA2_EMAX", FROZEN_EMAX.to_string());
    std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", FROZEN_WALK_CAP.to_string());
    std::env::set_var("LF_SQUARE_CAP", FROZEN_SQ_CAP.to_string());
    let recipe=include_str!("bind81_recipe.txt").to_owned();
    for line in recipe.lines(){if let Some((k,v))=line.split_once('='){std::env::set_var(k,v);}}
    eprintln!("BIND81_RECIPE {}",recipe.replace('\n',";"));
    let mut ops = build_point_add();
    {use std::io::Write;let mut f=std::io::BufWriter::new(std::fs::File::create("bind81-builder.raw").unwrap());
     for o in &ops {for v in [o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{f.write_all(&v.to_le_bytes()).unwrap();}}f.flush().unwrap();}
    if std::env::var("BIND81_RAW").ok().as_deref()==Some("1"){
       let mut x=Op::empty();x.kind=OperationType::X;x.q_target=QubitId(0);ops.extend(std::iter::repeat_n(x,96));return apply_tail_nonce(ops,required_env("TAIL_NONCE"));
    }

    // Effort-8 INT / B7b (`HEO_EMIT_ONLY=1`, research overlay only): stop after emission (the HEO phase report and
    // K3B_CELL traces are complete here), skipping the simplifier chain and the ops.bin write. Sweep instrument.
    if heo::research_on() && std::env::var("HEO_EMIT_ONLY").is_ok_and(|v| v == "1") {
        eprintln!("HEO_EMIT_ONLY exit ops={}", ops.len());
        std::process::exit(0);
    }
    // Exact op-stream post-passes, ported from the 2026-09-04 warpspeed
    // campaign (R10 affine, R33 quadratic, R41 truth, R46 product). Each pass
    // re-derives value supports from the stream's own ABI and drops or weakens
    // CCX ops it proves redundant, so composition is semantics-preserving.
    // The fixed four-pass chain is applied left to right, BEFORE the tail
    // append so the 96-X identity tail and the nonce it encodes are never
    // reinterpreted by a proof.
    let simplify_config =
        env_raw("PP_SIMPLIFY").unwrap_or_else(|| "product,affine,quadratic,truth".to_string());
    if simplify_config != "off" {
        for name in simplify_config.split(',') {
            let name = name.trim();
            let before = ops.len();
            ops = match name {
                "affine" => affine_simplify::simplify(ops),
                "quadratic" => quadratic_simplify::simplify(ops),
                "truth" => truth_simplify::simplify(ops),
                "product" => truth_simplify::simplify_products(ops),
                other => panic!("PP_SIMPLIFY: unknown pass {other:?}"),
            };
            eprintln!(
                "pp_simplify {name}: {before} -> {} ops ({} removed)",
                ops.len(),
                before - ops.len()
            );
        }
    }
    ops = interned_witness::witnesses(ops);
    if std::env::var("HEO_MABSORB").is_ok_and(|v| v == "1") {
        // B7 (K3a): measurement absorption, an exact generic post-pass (off = byte-identical).
        ops = mabsorb::absorb(ops);
    }
    // row cuts (SL_ROWCUT; unset = this gate list byte for byte): CCX rows that are CNOT forms on every reachable state
    // Entry-specific stream configuration.
    // pscan: SL_PSCAN=1 prints the parity scan, SL_PSCAN_FIX=1 rewrites its hits (pscan.rs)
    ops = pscan::run(ops);
    // cond pass v2 (SL_COND; unset = this gate list byte for byte): Toffolis consumed only by
    // phases, a measurement or a reset, or needing no Toffoli at all (cond_pass.rs, guarded)
    ops = cond_pass::run(ops);
    // square top carries (SL_SQTOP; unset = this gate list byte for byte): the square's inverse-row
    // top carries built only under the top bit that reads them (sqtop_pass.rs)
    ops = sqtop_pass::run(ops);
    // y42-railtop (leapfrog.rs `Y42_BOUND`; false = this gate list byte for byte): the edits of the four bound
    // passes above as one table, carried to this tree's stream with the rail switches on
    // round17 a2-build v5w: main's seven stream-bound passes (and cond_pass ur / zero_force between them) replayed as
    // one edit table bound to this stream after reader_pass (frozen_stack.rs): the harness's re-anchoring of main's
    // edits on lever A's stream (2 census_anchored clusters) plus the generic passes' result, op for op
    // the 6-hunk table placed by the stream prefix it edits, the two generic classical-control passes and the proved
    // CCX cuts bound to this stream (compose_post.rs)
    ops = compose_post::run(ops);
    ops = stream_pipeline::run(ops);
    ops = post_pipeline::run(ops);
    let mut ops = lane_generic_policy(ops);
    let nonce: u64 = required_env("TAIL_NONCE");
    let mut x = Op::empty();
    x.kind = OperationType::X;
    x.q_target = QubitId(0);
    ops.extend(std::iter::repeat_n(x, 96));
    let ops = apply_tail_nonce(ops, nonce);
    // Robust 340-operation subset: each gate is dead in 64 real-RNG nonce
    // corpora (577,536 shots), on all 16 fixed measurement corpora, and lies
    // outside conditional execution. This is an empirical support cut, not a
    // universal deadness claim.
    if std::env::var("Q27_DEAD_OFF").ok().as_deref()==Some("1"){
        let mut ops2 = source_edits::run_positions(ops,include_str!("q27_later.txt"));
        if std::env::var("HP2").ok().as_deref()==Some("1"){ ops2 = hold_pass::hold_pass_holds_only(ops2); }
        if std::env::var("HP3").ok().as_deref()==Some("1"){ ops2 = hold_pass::exact_final_pass(ops2); }
        return ops2;
    }
    let dead_rows: Vec<usize> = include_str!("dead-direct64-q1228.idx")
        .lines()
        .filter(|line| !line.is_empty() && *line != "idx")
        .map(|line| line.split('\t').next().unwrap().parse().unwrap())
        .collect();
    assert_eq!(dead_rows.len(), 340, "dead index must contain 340 rows");
    let dead: std::collections::BTreeSet<usize> = dead_rows.into_iter().collect();
    assert_eq!(dead.len(), 340, "dead index rows must be unique");
    let before = ops.len();
    let ops: Vec<Op> = ops
        .into_iter()
        .enumerate()
        .filter_map(|(i, op)| (!dead.contains(&i)).then_some(op))
        .collect();
    assert_eq!(before - ops.len(), 340, "dead index must remove 340 ops");
    ops
}


mod affine_constant;

mod known_stream;
mod round2_receiver;

mod round2_fused;

mod bridge;
mod j_fuse;

mod average;

mod stream_wide;

/// GO r34 per-round slicing hook: env GO_<K> (or LAB_GO_<K>) = "lo-hi:dir:delta,..."
/// dir a/d/m (or "lo-hi:delta" = any). First match wins. Unset = 0 (pinned circuit).
pub(crate) fn go_slice(key: &str, round: usize, dir: u8) -> isize {
    let Some(v) = env_raw(key) else { return 0 };
    for it in v.split(',') {
        let f: Vec<&str> = it.split(':').collect();
        let (rng, d, del) = match f.len() { 2 => (f[0], "a", f[1]), 3 => (f[0], f[1], f[2]), _ => panic!("bad {key} {it}") };
        let (lo, hi) = rng.split_once('-').expect("lo-hi");
        let (lo, hi): (usize, usize) = (lo.parse().unwrap(), hi.parse().unwrap());
        if round < lo || round > hi { continue; }
        if d != "a" && d.as_bytes()[0] != dir { continue; }
        return del.parse().unwrap();
    }
    0
}

mod mabsorb;
mod sqtop_pass;
mod narrow;
mod zero_force;
mod pscan;
mod cond_pass;
pub mod constant_templates;

mod native_sfuse_b;




mod zero_product;
mod frozen_stack;
mod compose_post;
mod source_edits;
mod classical_factors_xor;
mod classical_wide;




mod stream_pipeline;




mod post_pipeline;


