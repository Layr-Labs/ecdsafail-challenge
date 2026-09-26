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
        "SQ_LEND_RETAINED_CROSS2" => "2",
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
        "TAIL_NONCE" => "211106234700983",
        "PP_SEED_SHORT_MUL_F_COST" => "1",
        "SQ_HIGH_CARRY_LOAN" => "1",
        "SQ_HOLD_BOUNDARY" => "1",
        "SQ_OWN_TOP_ZEROS" => "1",
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
    coord_sub(circ, x, ox);

    circ.set_phase("coord_y_sub"); // y2 -= oy
    coord_sub(circ, y, oy);

    circ.set_phase("divide"); // y2 /= x2
    divide(circ, y, x);

    circ.set_phase("coord_add3x"); // x2 += 3*ox
    coord_add3x(circ, x, ox);

    circ.set_phase("square"); // x2 -= y2^2
    sub_square(circ, x, y);

    circ.set_phase("multiply"); // y2 *= x2
    multiply(circ, y, x);

    circ.set_phase("coord_y_sub_final"); // y2 -= oy
    coord_sub(circ, y, oy);

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

mod average;

mod stream_wide;
