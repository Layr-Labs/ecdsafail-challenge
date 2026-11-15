//! r3new: block-level tests of metalane's R3 items on this tree. Frame gate lists are evaluated classically, 64 random assignments per
//! lane word (every lane random before the list: dirty content), then EVERY lane is checked.
//!
//! Run: cargo test --release --bin build_circuit -- r3n_ --show-output
//!
//! r3n_b6_remap     B6: r3n_b6_swaps (D descending cswaps) against rotate_up by e - D for every D = 3..12 and class length e = D + 1..24: the
//!                  top-D lanes Q of the span carry weights 0..D-1 exactly as after the rotation (control 1), nothing moves (control 0), and
//!                  rev(list) restores every lane; the chosen list (r3n_b6_remap) passes the same checks. Toffoli counts printed (R3NTOF).
//! r3n_and2_lits    B4a: and2_lits against tgt ^= AND of the polarity-adjusted literals, all four polarity patterns, random dirty lanes, twice =
//!                  identity (the AND-marker form needs a clean target; outside the macro pass and2 is a plain Toffoli, which this tests)
//! r3n_b3_algebra   B3a / B3b: the flag algebra of fl_cls at a c4l slot over every (y1, y2) pattern: equal to the full class flags on the
//!                  states the invariant allows (every acting shot is of class 2 or 3), and the table of the states where it differs
//! No test exists for B2a (sandwich_x, needs the sandwich frame; the direct and held forms are the same Boolean function) or for B4b (not ported).

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

fn eval_gl(g: &[super::G], st: &mut [u64]) {
    for x in g {
        assert!(x.0 != super::MAC, "eval_gl: MAC macro in a unit-test list");
        if x.2 != super::NONE {
            let t = super::gl_loader::lane_of(x.2) as usize;
            st[t] ^= st[x.0 as usize] & st[x.1 as usize];
        } else if x.1 != super::NONE {
            st[x.1 as usize] ^= st[x.0 as usize];
        } else {
            st[x.0 as usize] = !st[x.0 as usize];
        }
    }
}
fn toffolis(g: &[super::G]) -> usize { g.iter().filter(|x| x.2 != super::NONE).count() }

#[test]
fn r3n_b6_remap() {
    let mut rng = Rng(0x3a3a_0001);
    let mut fails = 0u64;
    let mut checks = 0u64;
    for dd in 3..=12usize {
        let mut line = String::new();
        for eu in dd + 1..=24usize {
            let lanes: Vec<u32> = (0..eu as u32).collect();
            let d = eu as u32;
            let nl = eu + 1;
            let rot = super::rotate_up(d, &lanes, eu - dd);
            let swp = super::r3n_b6_swaps(d, &lanes, dd);
            let chosen = super::r3n_b6_remap(d, &lanes, dd);
            for (name, list) in [("swaps", &swp), ("chosen", &chosen)] {
                for rep in 0..4 {
                    let st0: Vec<u64> = (0..nl).map(|_| rng.next()).collect();
                    let mut sr = st0.clone();
                    eval_gl(&rot, &mut sr);
                    let mut sw = st0.clone();
                    eval_gl(list, &mut sw);
                    // control 1: Q = lanes[eu-dd..eu) must equal the rotation's Q (= old lanes[0..dd)); control 0 (bit-sliced): nothing moves
                    let mut ok = true;
                    for q in eu - dd..eu {
                        let want = (st0[q - (eu - dd)] & st0[d as usize]) | (st0[q] & !st0[d as usize]);
                        if sw[q] != want || sr[q] != want { ok = false; }
                    }
                    if sw[d as usize] != st0[d as usize] { ok = false; }
                    let mut back = sw.clone();
                    eval_gl(&super::rev(list), &mut back);
                    if back != st0 { ok = false; }
                    // under control 0 every lane is unchanged
                    for l in 0..eu { if (sw[l] ^ st0[l]) & !st0[d as usize] != 0 { ok = false; } }
                    checks += 1;
                    if !ok { fails += 1; if fails <= 5 { eprintln!("FAIL b6 D {dd} e {eu} {name} rep {rep}"); } }
                }
            }
            line += &format!(" e{eu}:{}/{}", toffolis(&rot) / 1, toffolis(&chosen));
        }
        eprintln!("R3NTOF b6 D {dd} (rotate_up cswap-Toffolis / chosen):{line}");
    }
    eprintln!("b6: {checks} checks, {fails} bad");
    assert_eq!(fails, 0);
}

#[test]
fn r3n_and2_lits() {
    let mut rng = Rng(0x3a3a_0002);
    let mut fails = 0u64;
    for pa in [false, true] {
        for pb in [false, true] {
            let l = [(0u32, pa), (1u32, pb)];
            let g = super::and2_lits(&l, 2);
            for _ in 0..64 {
                let st0: Vec<u64> = (0..6).map(|_| rng.next()).collect();
                let mut st = st0.clone();
                eval_gl(&g, &mut st);
                let lit = |q: usize, pos: bool| if pos { st0[q] } else { !st0[q] };
                let mut want = st0.clone();
                want[2] ^= lit(0, pa) & lit(1, pb);
                if st != want { fails += 1; }
                eval_gl(&g, &mut st);
                if st != st0 { fails += 1; }
            }
        }
    }
    eprintln!("R3NTOF and2_lits: {} Toffoli per half (a plain Toffoli outside the macro pass; AND compute + measured uncompute inside it)", toffolis(&super::and2_lits(&[(0, true), (1, true)], 2)));
    assert_eq!(fails, 0);
}

/// the class flags of a c4l slot as fl_cls builds them, per (cl, y1, y2): old = literal sets of classes 2 and 3, new = B3a / B3b forms
#[test]
fn r3n_b3_algebra() {
    let mut fails = 0u64;
    for big in [vec![2i32, 3], vec![2], vec![3]] {
        for cl in [false, true] {
            for y1 in [false, true] {
                for y2 in [false, true] {
                    // class e literals (fl_cls): cl, Y[1..e-2] zero, marker Y[e-1] one: class 2 = cl & y1; class 3 = cl & !y1 & y2
                    let old = |e: i32| match e { 2 => cl && y1, 3 => cl && !y1 && y2, _ => false };
                    // valid state: an acting shot (cl) is of a class in big (B3a invariant); a non-acting shot has any y
                    let valid = !cl || big.iter().any(|&e| old(e));
                    let b3b = |e: i32| match e { 2 => cl && y1, 3 => cl && !y1, _ => false };
                    let b3a_all = cl; // one flag over all of big
                    let want_all = big.iter().any(|&e| old(e));
                    let diff_a = b3a_all != want_all;
                    let diff_b = big.iter().all(|&b| b == 2 || b == 3) && (b3b(3) != old(3));
                    if valid && (diff_a || diff_b) { fails += 1; eprintln!("FAIL b3 big {big:?} cl {cl} y1 {y1} y2 {y2}"); }
                    if !valid { eprintln!("R3NTOF b3 big {big:?} cl {cl} y1 {y1} y2 {y2}: excluded by the invariant (differs: B3a {diff_a}, B3b {diff_b})"); }
                }
            }
        }
    }
    assert_eq!(fails, 0);
}
