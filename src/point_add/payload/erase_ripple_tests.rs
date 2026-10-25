//! ROOT-only actual-gate differential test; no author execution.
use super::*;
use super::erase_ripple::{self, PrefixMask};
use crate::circuit::Op;
use crate::point_add::builder::G;
use crate::point_add::frogdrop_sched::N;
use crate::point_add::tests_frogdrop::run;
use std::io::Write;

const WIDTH: usize = 699;
const APP_CAP: u64 = 100_000_000;
#[derive(Clone, Copy, Debug)]
struct Case { len: usize, rb: usize, lo: usize, hi: usize, am: Option<usize>,
              shared_g: bool, data_dirty: bool, exhaustive: bool, temps: usize }

fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    for len in 1..=4 { out.push(Case { len, rb: 3, lo: 0, hi: 7, am: None,
        shared_g: false, data_dirty: true, exhaustive: true, temps: 2 }); }
    out.push(Case { len: 3, rb: 3, lo: 0, hi: 7, am: None,
        shared_g: false, data_dirty: false, exhaustive: true, temps: 0 });
    for &(len, lo, hi, am, shared_g) in &[
        (24, 1, 23, Some(1), false), (25, 0, 255, Some(15), true),
        (40, 2, 39, Some(1), true), (41, 0, 255, Some(15), false),
        (65, 1, 64, Some(3), true), (129, 1, 128, None, false),
        (256, 0, 255, Some(15), true), (256, 48, 255, Some(2), false),
    ] { out.push(Case { len, rb: 8, lo, hi, am, shared_g,
        data_dirty: true, exhaustive: false, temps: 2 }); }
    out
}

fn recipes(c: Case) -> (Vec<G>, Vec<G>, Vec<G>) {
    let mut b = B::new(); let q = b.alloc_n(WIDTH);
    let t = &q[32..32 + c.len]; let s = &q[300..300 + c.len];
    let pre = &q[16..16 + c.rb]; let temps = &q[24..24 + c.temps];
    let dirty: Vec<_> = q[600..WIDTH].iter().copied()
        .chain(if c.data_dirty { s[..c.len.min(10)].iter().copied() } else { s[..0].iter().copied() }).collect();
    let mask = c.am.map(|amax| PrefixMask { bits: &q[4..c.rb], amax,
        flag: if c.shared_g { q[16 + c.rb - 2] } else { q[12] } });
    let args = (&q[..c.rb], [(q[8], false), (q[9], true)]);
    let eligible = erase_ripple::geometry(t, s, q[11], q[10], args.0, &args.1, pre, temps, &dirty, mask);
    assert_eq!(eligible, c.temps != 0);
    let old = erase_ripple::reference_record(&mut b, t, s, q[11], q[10], args.0,
        c.lo, c.hi, &args.1, pre, temps, &dirty, mask);
    let forced = erase_ripple::fused_record(&mut b, t, s, q[11], q[10], args.0,
        c.lo, c.hi, &args.1, pre, temps, &dirty, mask).unwrap_or_else(|| old.clone());
    let selected = erase_ripple::choose_record(&mut b, t, s, q[11], q[10], args.0,
        c.lo, c.hi, &args.1, pre, temps, &dirty, mask);
    if !eligible { assert_eq!(selected, old, "unchanged original fallback"); }
    (old, selected, forced)
}

fn emit(rec: &[G], inverse: bool) -> (Vec<Op>, u64) {
    let mut b = B::new(); b.alloc_n(WIDTH); b.play(rec, inverse);
    assert_eq!(b.peak, WIDTH as u64); assert!(b.ops.len() <= 65_536);
    (b.ops, b.tof)
}
fn directions(rec: &[G]) -> (Vec<Op>, Vec<Op>, Vec<Op>, Vec<Op>, u64, u64) {
    let (f, ft) = emit(rec, false); let (i, it) = emit(rec, true);
    let mut fi = f.clone(); fi.extend_from_slice(&i);
    let mut inverse_forward = i.clone(); inverse_forward.extend_from_slice(&f);
    (f, i, fi, inverse_forward, ft, it)
}
fn patterns(i: usize, pattern: usize) -> u64 {
    match pattern {
        0 => 0, 1 => u64::MAX,
        2 => if i % 2 == 0 { 0xaaaaaaaaaaaaaaaa } else { 0x5555555555555555 },
        _ => (i as u64).wrapping_add(0x9e3779b97f4a7c15).wrapping_mul(0xd1342543de82ef95)
            .rotate_left((i % 64) as u32),
    }
}
fn input(c: Case, pack: usize, pattern: usize) -> Vec<u64> {
    let mut w: Vec<_> = (0..WIDTH).map(|i| patterns(i, pattern)).collect();
    for v in &mut w[..c.rb] { *v = 0; }
    w[8] = 0; w[9] = 0; w[10] = 0; w[11] = 0;
    for v in &mut w[16..16 + c.rb - 1] { *v = 0; }
    for v in &mut w[24..24 + c.temps] { *v = 0; }
    if c.am.is_some() && !c.shared_g { w[12] = 0; }
    if c.exhaustive {
        for v in &mut w[32..32 + c.len] { *v = 0; }
        for v in &mut w[300..300 + c.len] { *v = 0; }
    }
    for lane in 0..64 {
        let code = pack * 64 + lane;
        for bit in 0..c.rb { w[bit] |= (((code >> bit) & 1) as u64) << lane; }
        for bit in 0..3 { w[8 + bit] |= (((code >> (c.rb + bit)) & 1) as u64) << lane; }
        if c.exhaustive {
            for bit in 0..c.len {
                w[32 + bit] |= (((code >> (c.rb + 3 + bit)) & 1) as u64) << lane;
                w[300 + bit] |= (((code >> (c.rb + 3 + c.len + bit)) & 1) as u64) << lane;
            }
        }
    }
    w
}
fn word(w: &[u64], start: usize, len: usize, lane: usize) -> N {
    let mut n = N::ZERO;
    for bit in 0..len { if (w[start + bit] >> lane) & 1 != 0 { n |= N::from(1u64) << bit; } }
    n
}
fn put(w: &mut [u64], start: usize, len: usize, lane: usize, value: N) {
    for bit in 0..len {
        let mask = 1u64 << lane;
        if value.bit(bit) { w[start + bit] |= mask; } else { w[start + bit] &= !mask; }
    }
}
// Independent arithmetic desired action, including foreign raw source words.
// At the midpoint of a full MAJ sweep, source[v] = carry_(v+1)
// XOR original_source[v+1] (the last source cell has no following XOR).
fn predicate(c: Case, code: usize, target: N, source: N, act: bool, sign: bool) -> bool {
    if !act || sign || code < c.lo || code > c.hi || code >= c.len { return false; }
    let low = (N::from(1u64) << (code + 1)) - N::from(1u64);
    let carry = (((low - (target & low)) + (source & low)) >> (code + 1)).bit(0);
    let next = code + 1 < c.len && source.bit(code + 1);
    !(carry ^ next)
}
fn expected(c: Case, initial: &[u64], inverse: bool) -> Vec<u64> {
    let mut out = initial.to_vec();
    for lane in 0..64 {
        let code = (0..c.rb).fold(0usize, |v, bit| v | ((((initial[bit] >> lane) & 1) as usize) << bit));
        let act = (initial[8] >> lane) & 1 != 0;
        let sign = (initial[9] >> lane) & 1 != 0;
        let mut e = (initial[10] >> lane) & 1 != 0;
        let source = word(initial, 300, c.len, lane);
        let mut target = word(initial, 32, c.len, lane);
        let span = match c.am {
            None => c.len,
            Some(am) => if code >> 4 <= am { c.len.min(24 + 16 * (code >> 4)) } else { 0 },
        };
        if inverse { e ^= predicate(c, code, target, source, act, sign); }
        if e && span > 0 {
            let mask = (N::from(1u64) << span) - N::from(1u64);
            let low = if inverse { ((N::from(1u64) << span) + (target & mask) - (source & mask)) & mask }
                      else { ((target & mask) + (source & mask)) & mask };
            target = (target & !mask) | low;
        }
        if !inverse { e ^= predicate(c, code, target, source, act, sign); }
        put(&mut out, 32, c.len, lane, target);
        if e { out[10] |= 1u64 << lane; } else { out[10] &= !(1u64 << lane); }
    }
    out
}
fn check(ops: &[Op], initial: &[u64], desired: &[u64], apps: &mut u64, label: &str, c: Case) {
    *apps = apps.checked_add(ops.len() as u64).unwrap(); assert!(*apps <= APP_CAP);
    let actual = run(ops, WIDTH, &|q| q.copy_from_slice(initial));
    assert_eq!(actual.phase, 0, "phase {label} {c:?}");
    assert_eq!(actual.q, desired, "all699 {label} {c:?}");
}
fn packs(c: Case) -> usize { (1usize << (c.rb + 3 + if c.exhaustive { 2 * c.len } else { 0 })).div_ceil(64) }

#[test]
#[ignore]
fn actual699_payload_fused_add_compare_differential_v1() {
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    println!("PAYLOAD_ERASE_FUSION_READY pid={} Q=699 packed_app_cap=100000000", std::process::id());
    std::io::stdout().flush().unwrap();
    let mut command = String::new(); std::io::stdin().read_line(&mut command).unwrap(); assert_eq!(command, "RUN\n");
    let cases = cases(); assert_eq!(cases.len(), 13);
    let mut planned_apps = 0u64;
    for &c in &cases {
        let (old, new, forced) = recipes(c);
        let od = directions(&old); let nd = directions(&new); let fd = directions(&forced);
        let per = od.0.len() + od.1.len() + nd.0.len() + nd.1.len() + nd.2.len() + nd.3.len()
            + fd.0.len() + fd.1.len() + fd.2.len() + fd.3.len();
        planned_apps += per as u64 * packs(c) as u64 * if c.exhaustive { 4 } else { 1 };
    }
    assert!(planned_apps <= APP_CAP, "exact preflight before simulation: {planned_apps}");
    let path = std::env::var_os("PAYLOAD_ERASE_FUSION_LEDGER_OUT").expect("fresh ledger required");
    let mut ledger = std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
    writeln!(ledger, "len\trb\tlo\thi\tamax\tshared_g\told_F_T\tnew_F_T\told_I_T\tnew_I_T\tforced_F_T\tforced_I_T").unwrap();
    let mut apps = 0u64; let mut frames = 0u64; let mut saved = 0u64;
    for &c in &cases {
        let (old, new, forced) = recipes(c);
        let od = directions(&old); let nd = directions(&new); let fd = directions(&forced);
        assert!(nd.4 <= od.4 && nd.5 <= od.5);
        saved += od.4 + od.5 - nd.4 - nd.5;
        writeln!(ledger, "{}\t{}\t{}\t{}\t{:?}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", c.len, c.rb, c.lo, c.hi,
            c.am, c.shared_g, od.4, nd.4, od.5, nd.5, fd.4, fd.5).unwrap();
        for pack in 0..packs(c) {
            for pattern in 0..if c.exhaustive { 4 } else { 1 } {
                let initial = input(c, pack, if c.exhaustive { pattern } else { pack % 4 });
                let f = expected(c, &initial, false); let i = expected(c, &initial, true);
                for (ops, desired, label) in [(&od.0, &f, "old-F"), (&od.1, &i, "old-I"),
                    (&nd.0, &f, "selected-F"), (&nd.1, &i, "selected-I"),
                    (&nd.2, &initial, "selected-FI"), (&nd.3, &initial, "selected-IF"),
                    (&fd.0, &f, "forced-F"), (&fd.1, &i, "forced-I"),
                    (&fd.2, &initial, "forced-FI"), (&fd.3, &initial, "forced-IF")] {
                    check(ops, &initial, desired, &mut apps, label, c); frames += 64;
                }
            }
        }
    }
    assert_eq!(apps, planned_apps); ledger.flush().unwrap();
    println!("PAYLOAD_ERASE_FUSION_NATIVE_PASS calls={} lane_frames={frames} packed_apps={apps} saved_local_T={saved} all699=true phase0=true e_act_sign_arbitrary=true raw_codes_exhaustive=true source_target_dirty_arbitrary=true shared_g_returned=true helpers_returned=true literal_FI_IF=true full_build=false", cases.len());
}
