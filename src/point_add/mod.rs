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
mod record;
mod square;

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
    let value = match name {
        "DUMP_REPLAY_SITES" => "1", // Read-only experiment map.
        "I76_SOURCE_TOP_LOAN" => "1",
        "I74_RESULT_TOP_LOAN" => "1",
        "SQ_LEND_RETAINED_CROSS3" => "0",
        "I45_NARROW_ROUNDS" => "549,550,551,552,553,586,587,640,641,648,683,684,685,686",
        "I50_SPLIT_BRIDGE" => "1",
        "I35_CELLS" => "0",
        "I35_TRACE" => "0",
        "I35_BUDGET" => "0",
        "PP_WALK_EXTRA_ROUNDS" => "683:4:1",
        "SQ_ASM_TAIL" => "24",
        "SQ_ROW1_INVERSE_CARRIES" => "1",
        "SQ_ROW1_STREAM" => "1",
        "SQ_ROW0_COPY" => "1",
        "I33_DISABLE" => "0",
        "I12_B_GUARD" => "4",
        "CMP_SEED_ALL" => "1",
        "ERASE_COMPARE" => "28",
        "FOLD_GUARD" => "21",
        "PP_CF_DEFER_WALK_PHASE" => "1",
        "PP_CF_END_CHUNK" => "8",
        "PP_CHUNK_SHAPE" => "64:0,38:1,25:-2,0:-4",
        "PP_CUT_SQIDENT" => "1",
        "PP_CUT_WALKLOAN" => "1",
        "PP_DEPTH_PROFILE" => "0:0",
        "PP_DIRECT_ENDPOINT" => "1",
        "PP_DIRECT_FOLD" => "1",
        "PP_FLAG_SHAPE" => "38:0,25:-1,0:-3",
        "PP_FLAG_WIDEN_DIV" => "696",
        "PP_HEAD_DIV" => "192",
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
        "PP_WALK_GUARD_BITS" => "1",
        "PP_WALK_GUARD_MAX_WIDTH" => "64",
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
        "SQ_LEND_RETAINED_ANDS" => "0",
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
        // Accepted public-validation nonce from the production grind.
        "TAIL_NONCE" => "91400000113896",
        "PP_SEED_SHORT_MUL_F_COST" => "1",
        "SQ_HIGH_CARRY_LOAN" => "1",
        "SQ_HOLD_BOUNDARY" => "1",
        "SQ_OWN_TOP_ZEROS" => "1",
        // ==================== pkgFdP + stk2 package pins (pr426-sub3) ====================
        // Every knob that differs from PR 426 lives in this block and nowhere else;
        // FOLD_WIDEN, RETAIN_LATE_WIDEN and WIDTH_SCHEDULE were removed from the
        // alphabetical list above so no arm shadows these. Spec (pr426-hunt/R/q5.txt):
        //   PP_RETAIN_LATE_WIDEN=1 PP_FOLD_WIDEN=0 PP_WIDTH_SCHEDULE=<PR 426>,8
        //   PP_DROP_EXACT_LEAD=1 PP_DROP_EXACT_LEAD_DIR=mul PP_F_PEAKCMP=24
        // The trailing ",8" adds one division round (699); PP_ROUNDS_MUL stays 698.
        // Protection buy: change ONE line here (e.g. "PP_FOLD_WIDEN" => "12"), or for
        // FOLD_GUARD move its line ("FOLD_GUARD" => "25", above) here with the new value.
        // The first matching arm wins, so a key must never appear twice. Then mirror
        // it in the grinder's Config::p426fdp (GRIND_WIDEN / GRIND_FOLD_GUARD defaults).
        "PP_RETAIN_LATE_WIDEN" => "1",
        "PP_FOLD_WIDEN" => "64",
        "PP_DROP_EXACT_LEAD" => "1",
        "PP_DROP_EXACT_LEAD_DIR" => "mul",
        "PP_F_PEAKCMP" => "24",
        // ---- stk2 (pr426-sub3): agent M's schedule-only levers on top of pkgFdP ----
        // Spec pr426-hunt/M/stk2.spec; reference build pr426-hunt/M/runs/stk2w
        // (ops md5 fed8ad7a5bd1fc23118c448286c2633d). PP_TAIL_MUL (was 655) and
        // I12_MUL_PROFILE were removed from the alphabetical list above so no arm
        // shadows these. Both only choose which late multiply walk rounds batch before
        // their replays; no round, width, fold window, guard or compare width changes.
        "PP_TAIL_MUL" => "657",
        // r6a_dpark re-pins I12_MUL_PROFILE in its own block below.
        // ================== end pkgFdP + stk2 package pins ==================
        // ==================== pkgN2 package pins (pr426-n2) ====================
        // pkgN2 = stk2 + agent N (PP_N_HOLE2, PP_N_BADJ) + N's schedule/qubit spec,
        // pr426-hunt/N/runs/pkgN2.spec; reference build pr426-hunt/N/runs/pkgN2
        // (ops md5 e17412f8fd54ee29ba011d8e46e1560e, 12,209,348 ops, Q1250).
        // Lambda gate: 16.30 +- 0.18 on 512 nonces (est + 2 SE <= 18, CIRCUIT_CONTRACT.md).
        // I41_ROUNDS, PP_WALK_MAX_QUBITS and PP_WIDTH_SCHEDULE were removed from the lists
        // above so no arm shadows these; the first matching arm wins, so a key must never
        // appear twice. PP_N_* keys are pinned here too.
        // Mirror any change in the grinder: grind-bundle/grind-p426d Config::p426n2.
        "PP_WALK_MAX_QUBITS" => "1249",
        "PP_N_HOLE2" => "1",
        // pkgJ1 (agent J): exact round-0/round-1 fold fusions, pr426-hunt/J/runs/pkgJ1.spec.
        "PP_J_XFUSE" => "1",
        "PP_J_YFUSE" => "1",
        "PP_J_AFUSE" => "1",
        "PP_J_RFUSE" => "1",
        "PP_J_SEED1" => "1",
        // r6a_dpark re-pins PP_WIDTH_SCHEDULE, I41_ROUNDS and PP_N_BADJ in its own block below.
        // ================== end pkgN2 package pins ==================
        // ==================== r6a_dpark package pins (pr426-r6) ====================
        // r6a_dpark = pkgJ1 + agent J (PP_J_SFUSE_B, PP_J_WCIN, PP_J_WCIN_B0LAST, PP_J_BMERGE)
        // + agent U (PP_U_DPARK, PP_U_DPARK_BEST, PP_U_C0WIDE) + U's re-derived schedules.
        // Spec pr426-hunt/U/r6a_dpark.spec; reference build pr426-hunt/U/runs/r6adp
        // (ops md5 f3ff6eff86829b2db538a99482579791 at reference TAIL_NONCE 26225815260, 12,194,112 ops, Q1250).
        // Agent U CRN runs: gate Lambda 16.336 +- 0.253 (256 nonces from 793401000), holdout
        // 16.590 +- 0.255 (256 from 793501000); pooled 16.463 +- 0.179, mean T 889,202.1
        // (est + 2 SE <= 18 is required before grind or submit, CIRCUIT_CONTRACT.md).
        // PP_WIDTH_SCHEDULE, I41_ROUNDS, PP_N_BADJ (pkgN2 block), I12_MUL_PROFILE (stk2 block),
        // I12_DIV_PROFILE, I35_PROFILE, PP_HEAD_MUL and PP_FOLD_PROFILE (alphabetical list) were
        // removed above so no arm shadows these; the first matching arm wins, so a key must never
        // appear twice. Every other pkgJ1 pin is unchanged. Mirror any change in the grinder.
        "PP_WIDTH_SCHEDULE" => "259,258x19,257x6,256x2,255x5,254x3,253x4,252x3,251x2,250x5,249x2,248x4,247x3,246x2,245x5,244x2,243x3,242x3,241x3,240x3,239x4,238x3,237x2,236x4,235x2,234x3,233x2,232x4,231x4,230x2,229x3,228x4,227x2,226x3,225x3,224x2,223x2,222x4,221x2,220x4,219x3,218x2,217x4,216x2,215x3,214x3,213x2,212x3,211x4,210x2,209x3,208x2,207x3,206x3,205x2,204x2,203x4,202x3,201x3,200x4,199x2,198x3,197x2,196x3,195x3,194x2,193x3,192x3,191x3,190x2,189x3,188x2,187x3,186x2,185x3,184x3,183x2,182x3,181x3,180x3,179x3,178x2,177x4,176x2,175x3,174x3,173x3,172x2,171x3,170x3,169x2,168x3,167x3,166x2,165x3,164x2,163x3,162x3,161x3,160x2,159x3,158x3,157x2,156x3,155x2,154x3,153x3,152x2,151x3,150x3,149x2,148x3,147x2,146x3,145x2,144x3,143x3,142x3,141x3,140x2,139x3,138x3,137x2,136x3,135x2,134x3,133x2,132x3,131x2,130x3,129x3,128x3,127x2,126x3,125x2,124x2,123x3,122x2,121x3,120x2,119x2,118x3,117,116x4,115x2,114x3,113x2,112x3,111x3,110x2,109x3,108x2,107x3,106x3,105x3,104x3,103x3,102x2,101x3,100x2,99x3,98x3,97x2,96x3,95x3,94x2,93x3,92x3,91x2,90x3,89x2,88x5,87x2,86x4,84x2,83x3,82x2,81x3,80x2,79x2,78x3,77x2,76x3,75x2,74x2,73x3,72x3,71x2,70x3,69x2,68x4,67x3,66x2,65x3,64x4,63x2,62x2,61x3,60x2,59x2,58x2,57x2,56x2,55x3,54x3,53x2,52x2,51x2,50x5,49,48x2,47x3,46x3,45x2,44x3,43x3,42x2,41x2,40x2,39x3,38x2,37x2,36x3,35x3,34x3,33x2,32x2,31x2,30x3,29x2,28x4,27x2,26x2,25x3,24x2,23x2,22x2,21x3,20x3,19x2,18x3,17x2,16x2,15x3,14x2,13x2,12x2,11x2,10x2,9x4,8x12",
        "I41_ROUNDS" => "36,45,52,61,62,68,71,74,77,80,89,95,100,101,104,110,119,129,130,135,144,150,153,158,161,167,172,175,182,183,513,518,525,528,533,538,539,542,549,550,551,552,553,571,583,586,587,591,611,618,621,633,640,641,648,655,658,683,684,685,686,687",
        "PP_N_BADJ" => "350-399:m:0,400-553:m:-1,554-599:m:-2,400-449:d:2,649-699:a:-1,554-615:m:-1,589-615:d:-1,616-648:m:1,350-553:d:1,250-349:d:1,350-399:m:1",
        "I12_MUL_PROFILE" => "657:657,656:656,655:655,654:653,652:651,650:649,648:641,640:640,639:639,638:638,637:633,632:624,623:621,620:620,619:616,615:609,608:603,602:592,591:591,590:586,585:585,584:584,583:583,582:574,573:571,570:566,565:538,537:533,532:528,527:525,524:518,517:516,515:513,512:507,506:502,501:495,494:440,439:438,437:437,436:432,431:427,426:424,423:423,422:420,419:419,418:414,413:409",
        "I12_DIV_PROFILE" => "192:192,193:193,194:194,195:195,196:196,197:197,198:198,199:199,200:200,201:201,202:202,203:203,204:204,205:205,206:206,207:207,208:208,209:209,210:210,211:211,212:212,213:213,214:214,215:215,216:216,217:217,218:218,219:219,220:220,221:221,222:222,223:223,224:224,225:225,226:226,227:227,228:228,229:229,230:230,231:231,232:232,233:233,234:234,235:235,236:236,237:237,238:238,239:239,240:240,241:241,242:242,243:243,244:244,245:245,246:246,247:247,248:248,249:250,251:255,256:392,393:393,394:394,395:395,396:396,397:397,398:398,399:399,400:400,401:401,402:402,403:403,404:404,405:405,406:406,407:407,408:408,409:409,410:410,411:411,412:412,413:413,414:414,415:415,416:416,417:417,418:418,419:419,420:420,421:421,422:422,423:423,424:424,425:425,426:426,427:427,428:428,429:429,430:430,431:433,434:434,435:438,439:439,440:441,442:442,443:444,445:496,497:497,498:498,499:499,500:500,501:501,502:502,503:503,504:504,505:505,506:506,507:507,508:508,509:509,510:510,511:511,512:512,513:513,514:514,515:515,516:516,517:517,518:518,519:519,520:520,521:522,523:523,524:524,525:525,526:526,527:527,528:528,529:529,530:530,531:531,532:532,533:533,534:534,535:535,536:536,537:537,538:538,539:572,573:573,574:574,575:575,576:576,577:577,578:578,579:579,580:580,581:581,582:582,583:583,584:584,585:585,586:588,589:596,597:597,598:598,599:599,600:600,601:601,602:602,603:604,605:606,607:608,609:610,611:611,612:613,614:615,616:617,618:618,619:620,621:622,623:624,625:625,626:626,627:627,628:628,629:629,630:630,631:631,632:632,633:633,634:634,635:635,636:636,637:637,638:638,639:639,640:640,641:641,642:642,643:643,644:644,645:645,646:646,647:647,648:648,649:664,665:666,667:668,669:670,671:671,672:672,673:673,674:674,675:675,676:676,677:677,678:678,679:679,680:680,681:681,682:682,683:683,684:684",
        // r6i (agent O2): I35_PROFILE re-derived per cell after DPARK (spec pr426-hunt/O2/runs/r6i.spec,
        // reference ops md5 ab7665628b337f4b25f696ff6874ba22 at TAIL_NONCE 26225815260). Bridges move to the
        // multiply tail so the drop-exact-lead layout ends in an 8-bit last chunk (no prefix compare).
        // Classical results bit-identical to r6a_dpark; paired dfailb -0.039 +- 0.069 over 512 nonces.
        "I35_PROFILE" => "600:0:1,602:0:1,640:0:1,642:0:1,644:0:1,646:0:1,672:0:1,673:0:1,674:0:1,675:0:1,676:0:1,677:0:1,678:0:1,679:0:1,680:0:1,681:0:1,682:0:1,683:0:1,684:0:1,685:0:1,686:0:1,687:0:1,688:0:1,689:0:1,690:0:1,691:0:1,692:0:1,693:0:1,694:0:1,695:0:1,696:0:1,697:0:1,698:0:1,620:1:1,591:1:1",
        "PP_HEAD_MUL" => "413",
        "PP_FOLD_PROFILE" => "38:0,32:0,19:-3,0:-4",
        // New exact constructions (agent J: square B-branch fusions; agent U: doubling-replay park).
        "PP_J_SFUSE_B" => "1",
        "PP_J_WCIN" => "1",
        "PP_J_WCIN_B0LAST" => "1",
        "PP_J_BMERGE" => "1",
        "PP_U_DPARK" => "1",
        "PP_U_DPARK_BEST" => "1",
        "PP_U_C0WIDE" => "1",
        // ================== end r6a_dpark package pins ==================
        _ => return None,
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
fn build_point_add() -> Vec<Op> {
    let circ = &mut Builder::new();
    let x: &[QubitId] = &circ.alloc_qubits(N);
    let y: &[QubitId] = &circ.alloc_qubits(N);
    let ox: &[BitId] = &circ.alloc_bits(N);
    let oy: &[BitId] = &circ.alloc_bits(N);

    circ.set_phase("coord_x_sub"); // x2 -= ox
    if j_fuse::j_xfuse() { classical::coord_sub_keep(circ, x, ox); } else { coord_sub(circ, x, ox); }

    circ.set_phase("coord_y_sub"); // y2 -= oy
    if j_fuse::j_yfuse() { classical::coord_sub_halve(circ, y, oy); } else { coord_sub(circ, y, oy); }

    circ.set_phase("divide"); // y2 /= x2
    divide(circ, y, x);

    circ.set_phase("coord_add3x"); // x2 += 3*ox
    coord_add3x(circ, x, ox);

    circ.set_phase("square"); // x2 -= y2^2
    sub_square(circ, x, y);

    circ.set_phase("multiply"); // y2 *= x2
    multiply(circ, y, x);

    circ.set_phase("coord_y_sub_final"); // y2 -= oy
    if j_fuse::j_yfuse() { classical::coord_double_sub(circ, y, oy); } else { coord_sub(circ, y, oy); }

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
pub fn build() -> Vec<Op> {
    let mut ops = build_point_add();
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
    // Isolated exact-cost screen after the existing witness rewrite.
    ops = truth_simplify::simplify_products(ops);
    let nonce: u64 = required_env("TAIL_NONCE");
    let mut x = Op::empty();
    x.kind = OperationType::X;
    x.q_target = QubitId(0);
    ops.extend(std::iter::repeat_n(x, 96));
    ops = apply_tail_nonce(ops, nonce);
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
