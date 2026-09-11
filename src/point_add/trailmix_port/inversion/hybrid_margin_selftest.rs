//! Bounded exact-inequality tests and native coefficient-cell regression hook.
use super::*;

fn inequalities() {
    for (w, l, kf, ki, full) in [
        (83, 31, Some(139), Some(139), true),
        (85, 31, Some(137), Some(137), true),
        (95, 31, Some(127), Some(127), true),
        (97, 31, Some(125), Some(125), true),
        (105, 31, Some(117), Some(117), true),
        (109, 31, Some(113), Some(113), true),
        (116, 31, Some(106), Some(106), true),
        (128, 31, Some(94), Some(94), true),
        (137, 31, Some(85), Some(85), true),
        (105, 63, Some(85), Some(85), true),
        (189, 31, Some(32), Some(33), true),
        (190, 31, None, Some(31), false),
        (191, 31, None, None, false),
    ] {
        let b = numerical_bounds(w, l);
        assert_eq!(
            (b.forward_drop, b.inverse_drop, b.full_fused),
            (kf, ki, full)
        );
        let d = Wide::from(2) * ((Wide::from(1) << (l + 1)) + Wide::from(1)) * (Wide::from(1) << w);
        for (k, c) in [
            (b.forward_drop, Wide::from(2) * gap_minus_one()),
            (b.inverse_drop, gap_minus_one()),
        ] {
            if let Some(k) = k {
                assert!(modulus() > d * ((Wide::from(1) << k) + c));
                if k < 255 {
                    assert!(modulus() <= d * ((Wide::from(1) << (k + 1)) + c));
                }
            }
        }
    }
    let p = Wide::from(101);
    let d = Wide::from(1);
    // Strict boundary:101 ==1*(2^0+100) must be rejected.
    assert_eq!(largest_drop(p, d, Wide::from(100)), None);
    assert_eq!(largest_drop(Wide::from(102), d, Wide::from(100)), Some(0));
    assert!(!numerical_bounds(255, 31).full_fused);
}

fn borrowing_fallback() {
    let names = [
        "TRAILMIX_Q_TARGET",
        "LOWQ_ONE_A_ELIM",
        "LOWQ_CLZ_DIFF_CONST_FOLD",
        "LOWQ_BORROW_PASSENGER_CARRY",
    ];
    let saved: Vec<_> = names.iter().map(|&n| (n, std::env::var(n).ok())).collect();
    for n in &names[1..] {
        std::env::set_var(n, "1");
    }
    std::env::set_var(names[0], "684");
    assert!(super::super::lowq_one_a_elim_enabled());
    assert!(super::super::lowq_borrow_passenger_carry_enabled());
    std::env::set_var(names[0], "999");
    assert!(!super::super::lowq_one_a_elim_enabled());
    assert!(!super::super::lowq_clz_diff_const_fold_enabled());
    assert!(!super::super::lowq_borrow_passenger_carry_enabled());
    std::env::set_var(names[0], "684");
    std::env::set_var("LOWQ_CLZ_DIFF_CONST_FOLD", "0");
    assert!(!super::super::lowq_borrow_passenger_carry_enabled());
    for (n, v) in saved {
        if let Some(v) = v {
            std::env::set_var(n, v);
        } else {
            std::env::remove_var(n);
        }
    }
}

pub(crate) fn run() {
    inequalities();
    borrowing_fallback();
    assert!(
        named_support_enabled(),
        "native margin test requires HYBRID_MARGIN_SUPPORT=exact-positive-l31"
    );
    assert!(
        admitted_bounds().is_some(),
        "source configuration must satisfy explicit support guard"
    );
    report();
    super::super::cell_folds::parametric_margin_selftest();
    eprintln!("HYBRID_MARGIN_SELFTEST PASS exact_integer_bounds=true strict_inequalities=true independent_inverse_bound=true coherent_borrow_fallback=true; local_cell_fixtures_not_whole_profile_membership");
}

#[cfg(test)]
#[test]
fn hybrid_margin_exact_inequalities() {
    inequalities();
}
