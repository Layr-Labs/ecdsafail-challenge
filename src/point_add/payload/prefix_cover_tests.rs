//! Actual-gate differential test for the public interval prefix cover.
//! Prepared only; compilation and execution require ROOT resource coordination.

use super::*;
use crate::circuit::Op;
use crate::point_add::builder::G;
use crate::point_add::tests_frogdrop::run;
use std::io::Write;

const WIDTH: usize = 699;

fn old_goto(b: &mut B, mask: &Mask<'_>, old: Option<isize>, new: Option<isize>) {
    // Byte-derived original goto body, using the unchanged original toggle.
    let previous = old.map(|l| mask.set(l)).unwrap_or((1, 0));
    let next = new.map(|l| mask.set(l)).unwrap_or((1, 0));
    let inside = |r: (usize, usize), v: usize| r.0 <= r.1 && v >= r.0 && v <= r.1;
    for v in 0..=mask.amax {
        if inside(previous, v) != inside(next, v) { mask.toggle(b, v); }
    }
}

fn recipe(maximum: usize, below: bool, old: Option<isize>, new: Option<isize>,
          base_count: usize, negative: bool, temp_count: usize, improved: bool) -> Vec<G> {
    let mut b = B::new();
    let q = b.alloc_n(WIDTH);
    let base: Vec<_> = (0..base_count).map(|i| (q[4 + i], negative && i + 1 == base_count)).collect();
    let mut mask = Mask::new(&q[..4], maximum, below, base, q[6], &q[7..7 + temp_count], &q[9..41]);
    mask.cur = old;
    b.begin();
    if improved { mask.goto(&mut b, new); }
    else { old_goto(&mut b, &mask, old, new); }
    b.end()
}

fn emit(record: &[G], inverse: bool) -> (Vec<Op>, u64) {
    let mut b = B::new();
    b.alloc_n(WIDTH);
    b.play(record, inverse);
    assert_eq!(b.peak, WIDTH as u64);
    assert!(b.ops.len() < 8192);
    (b.ops, b.tof)
}

fn allowed(value: usize, maximum: usize, below: bool, limit: Option<isize>) -> bool {
    if value > maximum { return false; }
    match limit { None => false, Some(l) => if below { (value as isize) < l } else { (value as isize) >= l } }
}

fn state(pack: usize, base_count: usize, pattern: usize) -> Vec<u64> {
    let mut words: Vec<u64> = (0..WIDTH).map(|i| match pattern {
        0 => 0,
        1 => u64::MAX,
        2 => if i & 1 == 0 { 0xaaaaaaaaaaaaaaaa } else { 0x5555555555555555 },
        _ => (i as u64).wrapping_add(0x9e3779b97f4a7c15).wrapping_mul(0xd1342543de82ef95).rotate_left((i % 64) as u32),
    }).collect();
    for word in &mut words[..9] { *word = 0; }
    let cases = 16usize << (base_count + 1);
    for lane in 0..64 {
        let code = (pack * 64 + lane) % cases;
        let value = code & 15;
        for bit in 0..4 { words[bit] |= (((value >> bit) & 1) as u64) << lane; }
        for bit in 0..base_count { words[4 + bit] |= (((code >> (4 + bit)) & 1) as u64) << lane; }
        words[6] |= (((code >> (4 + base_count)) & 1) as u64) << lane;
    }
    // A control outside the selected one-control ABI is an arbitrary spectator.
    if base_count == 1 { words[5] = match pattern { 0 => 0, 1 => u64::MAX, 2 => 0xaaaaaaaaaaaaaaaa, _ => 0x123456789abcdef0 }; }
    words
}

fn expected(input: &[u64], maximum: usize, below: bool, old: Option<isize>, new: Option<isize>,
            base_count: usize, negative: bool) -> Vec<u64> {
    let mut out = input.to_vec();
    for lane in 0..64 {
        let value = (0..4).fold(0, |x, bit| x | ((((input[bit] >> lane) & 1) as usize) << bit));
        let base = (0..base_count).all(|i| {
            let value = ((input[4 + i] >> lane) & 1) != 0;
            value != (negative && i + 1 == base_count)
        });
        if base && allowed(value, maximum, below, old) != allowed(value, maximum, below, new) {
            out[6] ^= 1u64 << lane;
        }
    }
    out
}

fn check(ops: &[Op], input: &[u64], desired: &[u64], apps: &mut u64, label: &str) {
    let r = run(ops, WIDTH, &|q| q.copy_from_slice(input));
    *apps += ops.len() as u64;
    assert_eq!(r.phase, 0, "phase: {label}");
    assert_eq!(r.q, desired, "all699: {label}");
}

#[test]
#[ignore]
fn actual699_payload_mask_prefix_cover_differential_v1() {
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    let path = std::env::var_os("PAYLOAD_MASK_LEDGER_OUT").expect("fresh ledger path required");
    let mut ledger = std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();
    writeln!(ledger, "amax\tbelow\told\tnew\tbase\tnegative\ttemps\told_F_T\tnew_F_T\told_I_T\tnew_I_T\told_F_ops\tnew_F_ops").unwrap();
    let mut apps = 0u64;
    let mut calls = 0u64;
    let mut frames = 0u64;
    let mut saved = 0u64;
    for maximum in 0..16usize {
        let m = maximum as isize;
        let limits = [None, Some(-1), Some(0), Some(1), Some(7), Some(8), Some(m), Some(m + 1), Some(17)];
        let pairs: Vec<_> = limits.iter().copied().map(|v| (None, v))
            .chain(limits.iter().copied().map(|v| (v, None)))
            .chain([(Some(7), Some(8)), (Some(8), Some(7)), (Some(0), Some(17)), (Some(17), Some(0))]).collect();
        for below in [false, true] {
            for &(old, new) in &pairs {
                for &(base_count, negative, temp_count) in &[(1, false, 0), (1, false, 1), (1, true, 2), (2, true, 0), (2, true, 1), (2, true, 2)] {
                    let reference = recipe(maximum, below, old, new, base_count, negative, temp_count, false);
                    let changed = recipe(maximum, below, old, new, base_count, negative, temp_count, true);
                    let (rf, rt) = emit(&reference, false);
                    let (ri, rit) = emit(&reference, true);
                    let (nf, nt) = emit(&changed, false);
                    let (ni, nit) = emit(&changed, true);
                    let mut fi = nf.clone(); fi.extend_from_slice(&ni);
                    let mut inverse_forward = ni.clone(); inverse_forward.extend_from_slice(&nf);
                    assert!(nt <= rt && nit <= rit);
                    saved += rt + rit - nt - nit;
                    calls += 1;
                    writeln!(ledger, "{maximum}\t{below}\t{old:?}\t{new:?}\t{base_count}\t{negative}\t{temp_count}\t{rt}\t{nt}\t{rit}\t{nit}\t{}\t{}", rf.len(), nf.len()).unwrap();
                    let packs = (16usize << (base_count + 1)).div_ceil(64);
                    for pattern in 0..4 {
                        for pack in 0..packs {
                            let input = state(pack, base_count, pattern);
                            let desired = expected(&input, maximum, below, old, new, base_count, negative);
                            check(&rf, &input, &desired, &mut apps, "reference-F");
                            check(&nf, &input, &desired, &mut apps, "new-F");
                            check(&ri, &desired, &input, &mut apps, "reference-I");
                            check(&ni, &desired, &input, &mut apps, "new-I");
                            check(&fi, &input, &input, &mut apps, "literal-FI");
                            check(&inverse_forward, &input, &input, &mut apps, "literal-IF");
                            frames += 6 * 64;
                        }
                    }
                    assert!(apps <= 100_000_000);
                }
            }
        }
    }
    ledger.flush().unwrap();
    println!("PAYLOAD_PREFIX_MASK_NATIVE_PASS calls={calls} lane_frames={frames} packed_apps={apps} saved_local_T={saved} all699=true phase0=true controls_helpers_dirty_returned=true raw_size_codes=16 dirty_patterns=4 full_build=false");
}
