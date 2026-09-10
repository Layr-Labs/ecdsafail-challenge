//! Full production-feature census without retaining the expanded operation vector.
//! Pins the final live-cache candidate; historical capacity experiments are receipts.
use super::*;

#[test]
#[ignore = "one authorized sequential full-source cache census"]
fn cache_extension_count() {
    let data = zstd::stream::decode_all(COMPRESSED_HIR).unwrap();
    let g = parse_graph(&data);
    shared_product::validate_phase_child(&g);
    comparator::validate_helper(&g);
    let qi: Vec<_> = (1..=512).collect();
    let ci: Vec<_> = (0..512).collect();
    let mut s = State::new(g.root_qubits, g.root_bits, &qi, &ci, false, 0);
    s.endpoint_enabled = true;
    s.carry_enabled = true;
    s.motif_enabled = true;
    s.motif_exclusions = motif::exclusions(&g);
    expand_node(&g, &mut s, g.root, 0, g.root_qubits, 0, g.root_bits);
    s.flush_raw();
    s.assert_accounting(g.summaries[g.root].output_ops, 0);
    assert!(s.capture.is_none() && s.comparator_capture.is_none());
    assert!(s.proof.balanced() && matches!(s.pending_hmr, PendingHmr::None));
    assert!(s.out.is_empty());
    assert_eq!(s.outer_toggles, 2);
    assert_eq!(g.root_qubits, 835);
    assert_eq!(g.root_bits, 1280);
    let static_t = s.output_hist[OperationType::CCX as usize]
        + s.output_hist[OperationType::CCZ as usize] - s.outer_lowered;
    let conditional_t = 512*s.predicate_blocks - s.carry_selected
        - s.endpoint_blocks - s.endpoint_outer;
    let expected_2t = 2*static_t - conditional_t;
    assert_eq!(s.proof.cache_cap(), 1_048_576);
    assert_eq!((g.root_qubits - 1, s.output_ops + 4*257 - 2, expected_2t),
        (834, 400_674_985, 126_413_754));
    assert_eq!((s.proof.evictions(), s.proof.collections()), (0, 284));
    assert_eq!((s.prefix_rewrites, s.shared_rewrites), (7421, 4_229_759));
    assert_eq!(s.trace, [0x6c051972fbdfd66c, 0xe6b40bffb3156b73]);
    let residual = s.residual_counts.iter().sum::<usize>();
    let skipped_residual = s.skipped_residual.iter().sum::<usize>();
    assert_eq!(s.final_private_hmr, s.proof.rewrites as usize + s.one_cleanups
        + residual + s.carry_selected - s.skipped_cleanups as usize
        - s.skipped_one - skipped_residual - s.comparator.skipped_private_hmr);
    assert_eq!(s.final_private_neg, s.one_cleanups + s.residual_counts[1]
        + s.carry_selected - s.skipped_one - s.skipped_residual[1]
        - s.comparator.skipped_private_neg);
    println!("CACHE_CENSUS cap={} qubits={} ops={} static_T={} conditional_T={} expected_2T={} expected_T={:.1} parent_expected_2T=126439508 gain_2T={}",
        s.proof.cache_cap(), g.root_qubits-1, s.output_ops+4*257-2,
        static_t, conditional_t, expected_2t, expected_2t as f64/2.0,
        126439508isize-expected_2t as isize);
    println!("DETAIL input={} output={} clean={} one={} residual={:?} support=[{},{},{}] prefix={} shared={} family24={:?} family36={:?} family63={:?} retention=[{},{},{}] comparator=[{},{},{}] private=[{},{}] trace={:016x}{:016x} fingerprint={}",
        s.input_ops, s.output_ops, s.proof.rewrites, s.one_cleanups, s.residual_counts,
        s.proof.support_dead, s.proof.support_x, s.proof.support_cx,
        s.prefix_rewrites, s.shared_rewrites, s.family24_counts,s.family36_counts,s.family63_counts,
        s.retention.selected,s.retention.proven,s.retention.fallback,
        s.comparator.eligible,s.comparator.selected,s.comparator.saving,
        s.final_private_hmr,s.final_private_neg,s.trace[0],s.trace[1],s.proof.diagnostic_fingerprint());
}
