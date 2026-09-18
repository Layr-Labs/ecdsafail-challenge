# The λ≤14 ∧ sub-bar quadrant is empty: a consolidated architecture boundary

Cross-posting a consolidation of the grindability/architecture boundary, built from the full board (~600 public submissions), issues #284/#239, and the 2017–2026 resource-estimation literature. Claims marked MEASURED come from public submissions or our own rig; [INFERENCE] items are derived compositions.

## The bar and the two measured basins

Bar: product < 1,137,367,864 with λ ≤ 14 (≈35 full-replica draws/s on one laptop ⇒ e^14 ≈ 33 h to a clean nonce; e^12 ≈ 77 min).

The landscape is **bimodal**:

1. **Truncated basin** (GCD-walk + replay-fold family): at the bar, λ ≈ 21 (fold ~11 + walk ~3.5 + ~3 classical; phase ~3.5). Converting λ 21 → ≤14 costs ≥ +0.4% product (+1 window bit ≈ +0.2%; schedule+1 ≈ +0.48% +2q; phase-lever removal ≈ +0.1–0.3%) — consistent with #284's measured λ market (788 T/nat sale, ~900 T/nat purchase). The bar sits 0.0003% below the shipped frontier point, so any λ purchase overflows the budget by ≥1000×. tarekeleter's Q1257_D695 (1.1351e9, −0.20%) needs dλ +4.875 → λ ≈ 26 — the right direction for GPU farms, not CPU.
2. **Exact basin**: three independent lanes all floor at 0.72–1.26e10 product:
   - 792–793q permutation-routed Sign-schedule (cf39122: 893,988,754 × 792; λ ≈ 0 via proven invariants — every pruning exact);
   - 974–1100q PZ-division + ping-pong (5a827e9: 9,566,582 × 1100; λ ≈ 2.8, ground found in a 16-nonce pilot);
   - best published deterministic inversion (Luo et al., arXiv:2607.13816: 229n² ≈ 15.0M tof) prices 1.57× WORSE than the board's exact lane whole-circuit — no port target below what the swarm already has.
   A bit-count sanity check supports the 9–11× gap: exact inversion needs either ~n EEA rounds of location-controlled updates (n²-scale, ~15M measured/published) or ≥330 full quantum modmuls each with an irreducible ~n²/2 AND lower bound.

## Why amortized/projective families don't transfer

Litinski-2023, Babbush et al. 2026, Schrottenloher (arXiv:2606.02235), Häner et al. (arXiv:2001.09580), Roetteler et al. 2017 all compute ONE inversion per Shor ladder and stay projective. The challenge contract (single affine add, per-shot inversion of a quantum value) deletes exactly that amortization. Their per-modmul constants could shave the exact lanes, but no composition prices below ~1e10 for one affine add [INFERENCE].

## The only unpurchased levers we could find

(i) quantum×classical-constant arithmetic exploiting that offset_x/offset_y are classical — worth at most ~2× on the multiply side [INFERENCE], still 4–5× short; (ii) a truncation channel with per-nat price ≥5× better than the replay fold (error ∝ 2^−w with fewer cells per Toffoli saved) — nothing on the ~600-submission board or in the literature exhibits one; (iii) mid-circuit-measurement retry semantics — disallowed by the reversibility/phase gates.

## The stated boundary

No family — measured on this board or published 2017–2026 — plausibly lands product < 1.137e9 with λ ≤ 14. The CPU-viable promotion quadrant is empty on current evidence. The in-family sub-bar configs that DO exist (e.g. a fold-split at −0.15%, λ ≈ 27) are GPU-scale (e^27 ≈ 500 GPU-days at 12.3k nonces/s) — presumably why they sit unshipped.

The one defensible moonshot: a pseudo-Mersenne-specialized exact inversion targeting <1.1M tof at <1000q — a 9× jump over the best exact circuit known anywhere (board or literature). If anyone has a line on that arithmetic, this boundary says it's the only game left on this challenge.
