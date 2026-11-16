//! Argon-lever tests: values, phase, lanes returned, and a deliberate break that must be caught.
use super::builder::B;
use super::modp_frogdrop::fold_c_split;
use crate::circuit::QubitId;
use crate::point_add::fd2::tests_frogdrop::{run, Rng};

fn model(t: u128, on: bool) -> u128 {
    // t has 67 meaningful lanes (u128); mirrors fold_c_split's window arithmetic
    if !on { return t; }
    let mut v = t;
    let low = v & 1023; let sum = low + 977; let cr = sum >> 10;
    v = (v & !1023u128) | (sum & 1023);
    let m35 = (1u128 << 35) - 1;
    let hi = (v >> 10) & m35; v = (v & !(m35 << 10)) | (((hi + cr) & m35) << 10);
    let h2 = (v >> 32) & m35; v = (v & !(m35 << 32)) | (((h2 + 1) & m35) << 32);
    v
}

fn case(clean: bool, brk: bool) -> bool {
    let mut rng = Rng::new(if clean { 5 } else { 6 });
    let mut b = B::new();
    let t = b.alloc_n(70);
    let ctl = b.alloc();
    let dirty = b.alloc_n(60);
    let cl = if clean { Some(b.alloc()) } else { None };
    let dsl: Vec<QubitId> = dirty.clone();
    if brk { b.x(dsl[0]); }
    fold_c_split(&mut b, &t, ctl, &dsl, cl);
    if brk { b.x(dsl[0]); b.x(dsl[0]); }
    b.flush_dependency();
    let nq = b.width() as usize;
    // shots: random windows, with extra-heavy low bits and carry chains
    let mut vals: Vec<u128> = vec![];
    for s in 0..64 {
        let mut v = ((rng.next() as u128) | ((rng.next() as u128) << 64)) & ((1u128 << 67) - 1);
        if s % 4 == 1 { v |= (1u128 << 45) - 1; v &= !0x1ffu128; v |= 0x3ff & rng.next() as u128; }
        if s % 4 == 2 { v = (v & !1023) | (940 + (rng.next() % 80) as u128); }
        if s % 8 == 3 { v = (1u128 << 35) - 1 << 10 | 1023; }
        vals.push(v);
    }
    let cw = rng.next();
    let dw: Vec<u64> = (0..dsl.len()).map(|_| rng.next()).collect();
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| {
        for s in 0..64 { for i in 0..67 { if (vals[s] >> i) & 1 == 1 { w[t[i].0 as usize] |= 1 << s; } } }
        w[ctl.0 as usize] = cw;
        for (i, q) in dsl.iter().enumerate() { w[q.0 as usize] = dw[i]; }
    });
    let mut ok = sim.phase == 0;
    if let Some(c) = cl { ok &= sim.q[c.0 as usize] == 0; }
    ok &= sim.q[ctl.0 as usize] == cw;
    for (i, q) in dsl.iter().enumerate() { ok &= sim.q[q.0 as usize] == dw[i]; }
    for s in 0..64 {
        let mut g = 0u128;
        for i in 0..67 { if (sim.q[t[i].0 as usize] >> s) & 1 == 1 { g |= 1u128 << i; } }
        ok &= g == model(vals[s], (cw >> s) & 1 == 1);
        for i in 67..70 { ok &= (sim.q[t[i].0 as usize] >> s) & 1 == 0; }
    }
    eprintln!("fold_c_split clean={clean} brk={brk} tof={} ok={ok}", sim.tof);
    ok
}

#[test]
fn argon_fold_c_split_clean() { assert!(case(true, false)); }
#[test]
fn argon_fold_c_split_borrowed() { assert!(case(false, false)); }
#[test]
fn argon_fold_c_split_break_is_caught() { assert!(!case(false, true)); assert!(!case(true, true)); }
