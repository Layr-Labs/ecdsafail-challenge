//! Exact integer walk, not a quantum simulation or a nonce search.
use super::*;
use ruint::Uint;

// Five limbs allow the signed lift and sum without 256-bit overflow.
type Word = Uint<320, 5>;

fn lift(value: U256) -> Word {
    let limbs = value.as_limbs();
    Word::from_limbs([limbs[0], limbs[1], limbs[2], limbs[3], 0])
}

fn half(value: Word) -> Word {
    (value >> 1) | (value & (Word::from(1) << 319))
}

fn fits(value: Word, width: usize) -> bool {
    let upper = value >> (width - 1);
    upper == Word::ZERO || upper == Word::MAX >> (width - 1)
}

fn terminal(u: Word, v: Word) -> bool {
    (u == Word::from(1) || u == Word::MAX) && (v == Word::from(1) || v == Word::MAX)
}

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Outcome {
    convergence: bool,
    width: Option<usize>,
    arithmetic: Option<usize>,
    hitting: usize,
}

impl Outcome {
    fn fails(self) -> bool {
        self.convergence || self.width.is_some() || self.arithmetic.is_some()
    }
}

pub(super) fn model(denominator: U256, widths: &[usize], rounds: usize, exact_from: usize) -> Outcome {
    assert!(rounds > 0 && rounds <= widths.len());
    assert!(exact_from<=widths.len());
    let p = lift(super::super::SECP256K1_P);
    let mut u = p;
    let d = lift(denominator);
    let mut v = (d >> 1usize).wrapping_sub(p);
    if d.bit(1) {
        v = v.wrapping_add(p);
    }
    if d.bit(0) {
        v = v.wrapping_add((p + Word::from(1)) >> 1);
    }
    let mut outcome = Outcome::default();
    for r in 0..rounds {
        if r > 0 {
            let (source, target) = if r % 2 == 0 { (u, &mut v) } else { (v, &mut u) };
            let sum = if target.bit(1) ^ source.bit(1) {
                target.wrapping_sub(source)
            } else {
                target.wrapping_add(source)
            };
            *target = half(sum);
            // Ordinary rounds rotate a width-1 bit-1-and-up rail and copy its
            // sign. The pre-rotation half-sum must fit that signed rail too.
            // Lookup continuation has no native add/rotation rail truncation.
            let arithmetic_width=if r>=exact_from {widths[r]}else{widths[r]-1};
            if r >= 2 && !fits(*target, arithmetic_width) && outcome.arithmetic.is_none() {
                outcome.arithmetic = Some(r);
            }
        }
        let next_width = widths[(r + 1).min(rounds - 1)];
        if (!fits(u, next_width) || !fits(v, next_width)) && outcome.width.is_none() {
            outcome.width = Some(r);
        }
        if terminal(u, v) {
            outcome.hitting = r + 1;
            return outcome;
        }
    }
    outcome.convergence = true;
    outcome.hitting = rounds + 1; // right-censored, not an observed hitting time
    outcome
}

fn difference(a: U256, b: U256) -> U256 {
    if a >= b {
        a - b
    } else {
        super::super::SECP256K1_P - (b - a)
    }
}

#[derive(Default)]
struct Counts {
    convergence: [usize; 4],
    scheduled: [usize; 4],
    predicted: [usize; 4],
    width: [usize; 2],
    arithmetic: [usize; 2],
    convergence_width: [usize; 2],
    first_width: [std::collections::BTreeMap<usize, usize>; 2],
    first_arithmetic: [std::collections::BTreeMap<usize, usize>; 2],
}

impl Counts {
    fn record(&mut self, pair: [Outcome; 2]) {
        self.convergence
            [usize::from(pair[0].convergence) + 2 * usize::from(pair[1].convergence)] += 1;
        self.scheduled[usize::from(pair[0].convergence || pair[0].width.is_some())
            + 2 * usize::from(pair[1].convergence || pair[1].width.is_some())] += 1;
        self.predicted[usize::from(pair[0].fails()) + 2 * usize::from(pair[1].fails())] += 1;
        for (pass, outcome) in pair.into_iter().enumerate() {
            if let Some(r) = outcome.width {
                self.width[pass] += 1;
                self.convergence_width[pass] += usize::from(outcome.convergence);
                *self.first_width[pass].entry(r).or_default() += 1;
            }
            if let Some(r) = outcome.arithmetic {
                self.arithmetic[pass] += 1;
                *self.first_arithmetic[pass].entry(r).or_default() += 1;
            }
        }
    }

    fn print(&self, total: usize) {
        for (label, cells) in [
            ("CONV", self.convergence),
            ("CONV_OR_SCHEDULE_WIDTH", self.scheduled),
            ("WALK_PREDICTED", self.predicted),
        ] {
            assert_eq!(cells.iter().sum::<usize>(), total);
            println!(
                "{label}_TABLE neither={} divide_only={} multiply_only={} both={}",
                cells[0], cells[1], cells[2], cells[3]
            );
            print_rate(&format!("{label}_divide"), cells[1] + cells[3], total);
            print_rate(&format!("{label}_multiply"), cells[2] + cells[3], total);
            print_rate(&format!("{label}_both"), cells[3], total);
            print_rate(&format!("{label}_union"), total - cells[0], total);
            let a = (cells[1] + cells[3]) as f64 / total as f64;
            let b = (cells[2] + cells[3]) as f64 / total as f64;
            let denominator = (a * (1.0 - a) * b * (1.0 - b)).sqrt();
            println!(
                "{label}_CORRELATION phi={:.8} expected_both_if_independent={:.6} \
                (sparse overlap cannot establish independence)",
                (cells[3] as f64 / total as f64 - a * b) / denominator,
                a * b * total as f64
            );
        }
        for pass in 0..2 {
            let name = if pass == 0 { "divide" } else { "multiply" };
            print_rate(&format!("WIDTH_{name}"), self.width[pass], total);
            print_rate(
                &format!("ARITHMETIC_RAIL_{name}"),
                self.arithmetic[pass],
                total,
            );
            println!("CONV_AND_WIDTH {name}={}", self.convergence_width[pass]);
            for (kind, counts) in [
                ("WIDTH", &self.first_width[pass]),
                ("ARITHMETIC_RAIL", &self.first_arithmetic[pass]),
            ] {
                let mut ranked: Vec<_> = counts.iter().collect();
                ranked.sort_by_key(|&(round, count)| (std::cmp::Reverse(*count), *round));
                for (round, count) in ranked.into_iter().take(20) {
                    println!("FIRST_MISS {kind} {name} after_round={round} count={count}");
                }
            }
        }
    }
}

#[test]
#[ignore = "262144 fresh paired classical walks; no circuit build/simulation"]
fn paired_walk_sample() {
    let attempts = std::env::var("MEASURE_SHOTS")
        .map(|s| s.parse().expect("positive MEASURE_SHOTS"))
        .unwrap_or(262_144);
    assert!(attempts > 0);
    let seed = fresh_seed();
    let seed_hex: String = seed.iter().map(|b| format!("{b:02x}")).collect();
    println!(
        "PAIRED_WALK seed={seed_hex} attempts={attempts} op_stream_independent=true threads=1"
    );
    let mut xof = independent_xof(&seed);
    let start = Instant::now();
    let shots = sample_points(&mut xof, attempts);
    let point_seconds = start.elapsed().as_secs_f64();
    assert!(!shots.is_empty());
    let (widths, mul_rounds) = super::super::pingpong::measurement_walk_widths();
    let exact_from = super::super::pingpong::measurement_exact_tail_start().unwrap_or(widths.len());
    let denominators: Vec<_> = shots
        .iter()
        .map(|shot| {
            [
                difference(shot.target.0, shot.offset.0),
                difference(shot.offset.0, shot.expected.0),
            ]
        })
        .collect();
    let mut counts = Counts::default();
    let start = Instant::now();
    for pair in &denominators {
        counts.record([
            model(pair[0], &widths, widths.len(), exact_from),
            model(pair[1], &widths, mul_rounds, exact_from),
        ]);
    }
    let walk_seconds = start.elapsed().as_secs_f64();
    counts.print(shots.len());
    let per_set = SCORED_SHOTS as f64 / shots.len() as f64;
    let p_walk = 1.0 - counts.predicted[0] as f64 / shots.len() as f64;
    let expected_prefix = if p_walk == 0.0 {
        SCORED_SHOTS as f64
    } else {
        -((SCORED_SHOTS as f64) * (-p_walk).ln_1p()).exp_m1() / p_walk
    };
    println!(
        "WALK_TIMING accepted={} rejected={} point_seconds={point_seconds:.6} \
        paired_walk_seconds={walk_seconds:.6} walk_us_per_pair={:.6} \
        points_seconds_per_9024={:.6} walk_seconds_per_9024={:.6} \
        eager_seconds_per_9024={:.6} early_abort_expected_pairs={expected_prefix:.3} \
        ideal_streaming_seconds_per_candidate={:.6}",
        shots.len(),
        attempts - shots.len(),
        walk_seconds * 1e6 / shots.len() as f64,
        point_seconds * per_set,
        walk_seconds * per_set,
        (point_seconds + walk_seconds) * per_set,
        (point_seconds + walk_seconds) * expected_prefix / shots.len() as f64
    );
    println!("LIMIT: CONV/WIDTH are ideal-walk predictions, not observed circuit failures. \
        No full-circuit lambda, precision/recall, nonce hashing, replay, or grinder throughput measured.");
}

#[test]
fn documented_walk_witnesses_and_signed_bounds() {
    let widths = vec![259; 1300];
    for (d, expected) in [
        (U256::from(1), 512),
        (U256::from(3), 1135),
        (U256::from(1) << 255, 1239),
        (U256::from(2) * super::super::modular::f(), 1263),
    ] {
        let outcome = model(d, &widths, widths.len(), widths.len());
        assert_eq!(outcome.hitting, expected, "d={d}");
        assert!(!outcome.fails());
    }
    let zero = model(U256::ZERO, &widths, 698, widths.len());
    assert!(zero.convergence && zero.width.is_none());
    for width in [5, 9, 64, 65, 256, 259] {
        let limit = Word::from(1) << (width - 1);
        assert!(fits(limit - Word::from(1), width));
        assert!(!fits(limit, width));
        let negative = Word::ZERO.wrapping_sub(limit);
        assert!(fits(negative, width));
        assert!(!fits(negative.wrapping_sub(Word::from(1)), width));
    }
    assert_eq!(
        half(Word::ZERO.wrapping_sub(Word::from(3))),
        Word::ZERO.wrapping_sub(Word::from(2))
    );
    assert_eq!(
        difference(U256::ZERO, U256::from(1)),
        super::super::SECP256K1_P - U256::from(1)
    );
}

#[test]
fn labels_overlap_without_double_counting() {
    let mut counts = Counts::default();
    counts.record([
        Outcome {
            convergence: true,
            width: Some(4),
            ..Outcome::default()
        },
        Outcome::default(),
    ]);
    counts.record(
        [Outcome {
            convergence: true,
            ..Outcome::default()
        }; 2],
    );
    assert_eq!(counts.convergence, [0, 1, 0, 1]);
    assert_eq!(counts.predicted, [0, 1, 0, 1]);
    assert_eq!(counts.scheduled, [0, 1, 0, 1]);
    assert_eq!(counts.convergence_width, [1, 0]);
}

#[test]
fn signed_rail_bound_matches_emitted_single_round() {
    // Exhaustive tiny primitive test, not the full point-add circuit or the
    // Monte Carlo: verify the extra sign bit consumed by the actual rotation.
    for width in 5..=7 {
        let (ops, rails) = super::super::pingpong::measurement_single_step(width);
        let (qubits, bits, _, _) = analyze_ops(ops.iter());
        let regs: Vec<Vec<_>> = rails
            .iter()
            .map(|rail| rail.iter().copied().map(QubitOrBit::Qubit).collect())
            .collect();
        let limit = 1i64 << (width - 1);
        let cases: Vec<_> = (-limit + 1..limit)
            .step_by(2)
            .flat_map(|a| (-limit + 1..limit).step_by(2).map(move |b| (a, b)))
            .collect();
        let mut xof = independent_xof(&[0x51; 32]);
        let mut sim = Simulator::new(qubits as usize, bits as usize, &mut xof);
        for batch in cases.chunks(64) {
            sim.clear_for_shot();
            for (lane, &(a, b)) in batch.iter().enumerate() {
                sim.set_register(&regs[0], U256::from(((a >> 1) & (limit - 1)) as u64), lane);
                sim.set_register(&regs[1], U256::from(((b >> 1) & (limit - 1)) as u64), lane);
            }
            sim.apply_iter(ops.iter());
            for (lane, &(a, b)) in batch.iter().enumerate() {
                let expected = if ((a ^ b) & 2) == 0 {
                    (b + a) / 2
                } else {
                    (b - a) / 2
                };
                let out = sim.get_register(&regs[1], lane).to::<u64>() as i64;
                let signed = (out << (65 - width)) >> (65 - width);
                let got = 2 * signed + 1;
                let fits_rail = (-limit / 2..limit / 2).contains(&expected);
                assert_eq!(got == expected, fits_rail, "width={width} a={a} b={b}");
                assert_eq!(
                    sim.get_register(&regs[0], lane).to::<u64>(),
                    ((a >> 1) & (limit - 1)) as u64,
                    "source preserved"
                );
            }
        }
    }
}
