//! Actual-gate differential test source; not executed by the author.
//! Compile/native require ROOT's resource slot and an explicit test filter.

use super::*;
use crate::circuit::Op;
use crate::point_add::builder::G;
use crate::point_add::tests_frogdrop::run;
use std::io::Write;

const WIDTH: usize = 699;
const APP_CAP: u64 = 100_000_000;

#[derive(Clone, Copy, Debug)]
struct Case { width: usize, lo: usize, hi: usize, shape: usize,
              pre: usize, temps: usize, extra: usize, negative: bool, leaf_dirty: bool }

fn lane(case: Case, value: usize) -> Option<usize> {
    let end = 1usize << case.width;
    if value >= end { return None; }
    match case.shape {
        0 => Some(32 + value),
        1 => if value % 3 == 1 { None } else { Some(32 + value) },
        2 => if value == 0 || value == end / 2 || value + 1 == end { Some(32 + value) } else { None },
        3 => Some(32 + end - 1 - value),
        4 => Some(32 + value / 2), // legal decoder alias: tree must fall back
        _ => unreachable!(),
    }
}

fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    for width in 1usize..=5 {
        for shape in 0..5 {
            for &(pre, temps, extra, negative) in &[
                (0, 0, 0, false), (2.min(width - 1), 1, 1, true),
                (width - 1, 2, 2, true), (width - 1, 0, 1, false),
            ] {
                out.push(Case { width, lo: 0, hi: (1 << width) - 1, shape, pre, temps, extra, negative, leaf_dirty: false });
            }
        }
    }
    for shape in [0, 1, 3, 4] {
        for &(pre, temps, extra, negative) in &[(0, 0, 2, true), (2, 1, 1, false), (7, 2, 2, true), (7, 0, 1, false)] {
            if shape == 1 && !(pre == 2 || temps == 2) { continue; }
            if shape >= 3 && !(pre == 0 || temps == 2) { continue; }
            out.push(Case { width: 8, lo: 0, hi: 255, shape, pre, temps, extra, negative, leaf_dirty: false });
        }
    }
    for &(width, lo, hi, shape) in &[(4, 0, 31, 0), (4, 5, 9, 1), (4, 0, 0, 0),
        (4, 3, 2, 0), (4, 16, 20, 0), (8, 27, 210, 0), (8, 200, 350, 1)] {
        out.push(Case { width, lo, hi, shape, pre: 2.min(width - 1), temps: 1, extra: 2, negative: true, leaf_dirty: false });
    }
    for &(width, shape, pre, temps, extra) in &[(4, 0, 2, 1, 2), (4, 1, 3, 2, 1),
        (8, 0, 7, 2, 2), (4, 3, 0, 1, 1), (3, 4, 1, 2, 2)] {
        out.push(Case { width, lo: 0, hi: (1 << width) - 1, shape, pre, temps, extra, negative: true, leaf_dirty: true });
    }
    // Extra pre cells are arbitrary spectators: Dec's original ABI consumes
    // only min(pre.len(), width-1), and the tree must use exactly that subset.
    out.push(Case { width: 4, lo: 0, hi: 15, shape: 0, pre: 8, temps: 1, extra: 2, negative: true, leaf_dirty: false });
    out.push(Case { width: 4, lo: 0, hi: 15, shape: 1, pre: 3, temps: 2, extra: 0, negative: true, leaf_dirty: false });
    out
}

fn recipes(case: Case) -> (Vec<G>, Vec<G>, Option<Vec<G>>) {
    let mut b = B::new();
    let q = b.alloc_n(WIDTH);
    let extra: Vec<_> = (0..case.extra).map(|i| (q[8 + i], case.negative && i == 0)).collect();
    let dirty: Vec<_> = if case.leaf_dirty {
        [q[32], q[33], q[40], q[45]].into_iter().chain(q[400..428].iter().copied()).collect()
    } else { q[400..432].to_vec() };
    let mapping = |v| lane(case, v).map(|i| q[i]);
    b.begin();
    read_lane_decoder(&mut b, &q[..case.width], case.lo, case.hi, &mapping, case.negative,
                      &extra, q[10], &q[12..12 + case.pre], &q[20..20 + case.temps], &dirty);
    let reference = b.end();
    b.begin();
    read_lane(&mut b, &q[..case.width], case.lo, case.hi, &mapping, case.negative,
              &extra, q[10], &q[12..12 + case.pre], &q[20..20 + case.temps], &dirty);
    let selected = b.end();
    let leaves: Vec<_> = (case.lo..=case.hi).take_while(|&v| v < (1 << case.width))
        .filter_map(|v| mapping(v).map(|wire| (v, wire))).collect();
    let forced = read_lane_tree::tree_record(&mut b, &q[..case.width], &leaves, case.negative,
        &extra, q[10], &q[12..12 + case.pre], &q[20..20 + case.temps], &dirty);
    if forced.is_none() { assert_eq!(selected, reference, "exact fallback: {case:?}"); }
    (reference, selected, forced)
}

fn emit(record: &[G], inverse: bool) -> (Vec<Op>, u64) {
    let mut b = B::new(); b.alloc_n(WIDTH); b.play(record, inverse);
    assert_eq!(b.peak, WIDTH as u64);
    assert!(b.ops.len() <= 65_536, "one local recipe gate cap");
    (b.ops, b.tof)
}

fn directions(record: &[G]) -> (Vec<Op>, Vec<Op>, Vec<Op>, Vec<Op>, u64, u64) {
    let (f, ft) = emit(record, false);
    let (i, it) = emit(record, true);
    let mut fi = f.clone(); fi.extend_from_slice(&i);
    let mut inverse_forward = i.clone(); inverse_forward.extend_from_slice(&f);
    (f, i, fi, inverse_forward, ft, it)
}

fn input(case: Case, pack: usize, pattern: usize) -> Vec<u64> {
    let mut words: Vec<_> = (0..WIDTH).map(|i| match pattern {
        0 => 0, 1 => u64::MAX,
        2 => if i & 1 == 0 { 0xaaaaaaaaaaaaaaaa } else { 0x5555555555555555 },
        _ => (i as u64).wrapping_add(0x9e3779b97f4a7c15).wrapping_mul(0xd1342543de82ef95).rotate_left((i % 64) as u32),
    }).collect();
    for word in &mut words[..case.width] { *word = 0; }
    for word in &mut words[8..8 + case.extra] { *word = 0; }
    words[10] = 0;
    for word in &mut words[12..12 + case.pre.min(case.width - 1)] { *word = 0; }
    let h = case.pre.min(case.width - 1);
    let used_temps = case.temps.min((case.width - h + 1 + case.extra).saturating_sub(2));
    for word in &mut words[20..20 + used_temps] { *word = 0; }
    let count = 1usize << (case.width + case.extra + 1);
    for shot in 0..64 {
        let code = (pack * 64 + shot) % count;
        for bit in 0..case.width { words[bit] |= (((code >> bit) & 1) as u64) << shot; }
        for bit in 0..case.extra { words[8 + bit] |= (((code >> (case.width + bit)) & 1) as u64) << shot; }
        words[10] |= (((code >> (case.width + case.extra)) & 1) as u64) << shot;
    }
    words
}

fn expected(case: Case, input: &[u64]) -> Vec<u64> {
    let mut out = input.to_vec();
    for shot in 0..64 {
        let value = (0..case.width).fold(0, |v, bit| v | ((((input[bit] >> shot) & 1) as usize) << bit));
        let enabled = (0..case.extra).all(|i| (((input[8 + i] >> shot) & 1) != 0) != (case.negative && i == 0));
        if enabled && case.lo <= value && value <= case.hi {
            if let Some(wire) = lane(case, value) {
                if (((input[wire] >> shot) & 1) != 0) != case.negative { out[10] ^= 1u64 << shot; }
            }
        }
    }
    out
}

fn check(ops: &[Op], input: &[u64], desired: &[u64], apps: &mut u64, label: &str, case: Case) {
    *apps = apps.checked_add(ops.len() as u64).unwrap();
    assert!(*apps <= APP_CAP);
    let actual = run(ops, WIDTH, &|q| q.copy_from_slice(input));
    assert_eq!(actual.phase, 0, "phase: {label} {case:?}");
    assert_eq!(actual.q, desired, "all699: {label} {case:?}");
}

// Alias rejection is a public port check, not a claim that aliased original
// controls/targets constitute a valid reversible query ABI.
fn structural_rejections() {
    let mut b = B::new(); let q = b.alloc_n(WIDTH);
    let leaves = [(0, q[32]), (1, q[33])];
    for (reg, ls, extra, target, pre, temps, dirty) in [
        (vec![q[0], q[0]], leaves.to_vec(), vec![], q[10], vec![], vec![], q[400..432].to_vec()),
        (q[..2].to_vec(), vec![(0, q[32]), (1, q[32])], vec![], q[10], vec![], vec![], q[400..432].to_vec()),
        (q[..2].to_vec(), leaves.to_vec(), vec![(q[32], false)], q[10], vec![], vec![], q[400..432].to_vec()),
        (q[..2].to_vec(), leaves.to_vec(), vec![], q[32], vec![], vec![], q[400..432].to_vec()),
        (q[..2].to_vec(), leaves.to_vec(), vec![], q[10], vec![q[32]], vec![], q[400..432].to_vec()),
        (q[..2].to_vec(), leaves.to_vec(), vec![], q[10], vec![], vec![q[32]], q[400..432].to_vec()),
        (q[..2].to_vec(), leaves.to_vec(), vec![], q[10], vec![], vec![], vec![q[32], q[400]]),
    ] {
        assert!(read_lane_tree::tree_record(&mut b, &reg, &ls, false, &extra, target, &pre, &temps, &dirty).is_none());
        let sentinel = vec![G::X(q[600])];
        assert_eq!(read_lane_tree::choose_record(&mut b, &reg, &ls, false, &extra, target,
            &pre, &temps, &dirty, sentinel.clone()), sentinel);
    }
}

#[test]
#[ignore]
fn actual699_payload_pruned_read_tree_differential_v1() {
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    println!("PAYLOAD_READ_TREE_READY pid={} Q=699 packed_app_cap=100000000", std::process::id());
    std::io::stdout().flush().unwrap();
    let mut command = String::new();
    std::io::stdin().read_line(&mut command).unwrap();
    assert_eq!(command, "RUN\n", "ROOT-authorized own-PID resource gate");
    structural_rejections();
    let cases = cases();
    assert_eq!(cases.len(), 124);
    // Exact actual-op preflight, one case resident. No simulated packed gate
    // application occurs before the complete app cap is established.
    let mut planned_apps = 0u64;
    for &case in &cases {
        let (reference, selected, forced) = recipes(case);
        let (rf, ri, _, _, _, _) = directions(&reference);
        let (nf, ni, fi, inverse_forward, _, _) = directions(&selected);
        let mut per_pack = rf.len() + ri.len() + nf.len() + ni.len() + fi.len() + inverse_forward.len();
        if let Some(tree) = forced {
            let (tf, ti, tfi, tif, _, _) = directions(&tree);
            per_pack += tf.len() + ti.len() + tfi.len() + tif.len();
        }
        let packs = (1usize << (case.width + case.extra + 1)).div_ceil(64);
        planned_apps += per_pack as u64 * packs as u64 * 4;
    }
    assert!(planned_apps <= APP_CAP, "exact app preflight: {planned_apps}");
    let path = std::env::var_os("PAYLOAD_READ_TREE_LEDGER_OUT").expect("fresh ledger required");
    let mut ledger = std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();
    writeln!(ledger, "width\tlo\thi\tshape\tpre\ttemps\textra\tnegative\tleaf_dirty\ttree_eligible\tselected_tree\told_F_T\tselected_F_T\told_I_T\tselected_I_T\ttree_F_T\ttree_I_T").unwrap();
    let mut apps = 0u64; let mut frames = 0u64; let mut selected_trees = 0u64; let mut saved = 0u64;
    for &case in &cases {
        let (reference, selected, forced) = recipes(case);
        let (rf, ri, _, _, rt, rit) = directions(&reference);
        let (nf, ni, fi, inverse_forward, nt, nit) = directions(&selected);
        assert!(nt <= rt && nit <= rit);
        assert_eq!(read_lane_tree::prices(&reference), Some((rt, rit)));
        assert_eq!(read_lane_tree::prices(&selected), Some((nt, nit)));
        saved += rt + rit - nt - nit;
        let changed = selected != reference;
        selected_trees += u64::from(changed);
        let td = forced.as_ref().map(|tree| directions(tree));
        if let (Some(tree), Some((_, _, _, _, ft, it))) = (&forced, &td) {
            assert_eq!(read_lane_tree::prices(tree), Some((*ft, *it)));
        }
        let tree_ft = td.as_ref().map(|t| t.4.to_string()).unwrap_or_else(|| "fallback".to_owned());
        let tree_it = td.as_ref().map(|t| t.5.to_string()).unwrap_or_else(|| "fallback".to_owned());
        writeln!(ledger, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{rt}\t{nt}\t{rit}\t{nit}\t{tree_ft}\t{tree_it}",
            case.width, case.lo, case.hi, case.shape, case.pre, case.temps, case.extra, case.negative, case.leaf_dirty, forced.is_some(), changed).unwrap();
        let packs = (1usize << (case.width + case.extra + 1)).div_ceil(64);
        for pattern in 0..4 {
            for pack in 0..packs {
                let input = input(case, pack, pattern); let desired = expected(case, &input);
                for (ops, want, label) in [(&rf, &desired, "decoder-F"), (&ri, &desired, "decoder-I"),
                    (&nf, &desired, "selected-F"), (&ni, &desired, "selected-I"),
                    (&fi, &input, "selected-literal-FI"), (&inverse_forward, &input, "selected-literal-IF")] {
                    check(ops, &input, want, &mut apps, label, case); frames += 64;
                }
                if let Some((tf, ti, tfi, tif, _, _)) = &td {
                    for (ops, want, label) in [(tf, &desired, "forced-tree-F"), (ti, &desired, "forced-tree-I"),
                        (tfi, &input, "forced-tree-literal-FI"), (tif, &input, "forced-tree-literal-IF")] {
                        check(ops, &input, want, &mut apps, label, case); frames += 64;
                    }
                }
            }
        }
    }
    assert_eq!(apps, planned_apps);
    ledger.flush().unwrap();
    println!("PAYLOAD_READ_TREE_NATIVE_PASS calls={} lane_frames={frames} packed_apps={apps} selected_trees={selected_trees} saved_local_T={saved} all699=true phase0=true target_arbitrary=true raw_codes_exhaustive=true source_and_dirty_arbitrary=true helpers_returned=true alias_fallback=true literal_FI_IF=true full_build=false", cases.len());
}
