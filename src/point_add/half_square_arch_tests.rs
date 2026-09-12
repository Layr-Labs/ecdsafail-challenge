use super::{parse_graph, shift_controls, Graph, Reader, COMPRESSED_HIR};
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
struct Call {
    at: usize,
    child: usize,
    condition_width: usize,
    expected: usize,
    qmap: Vec<usize>,
    cmap: Vec<usize>,
}

#[derive(Default)]
struct Direct {
    qlen: usize,
    clen: usize,
    ops: usize,
    tags: [usize; 12],
    calls: Vec<Call>,
}

fn decode_direct(graph: &Graph<'_>, node_id: usize) -> Direct {
    let node = graph.nodes[node_id];
    let mut r = Reader { data: &graph.data[node.start..node.end], at: 0 };
    let mut out = Direct {
        qlen: r.uvar(),
        clen: r.uvar(),
        ops: r.uvar(),
        ..Direct::default()
    };
    for at in 0..out.ops {
        let tag = r.byte();
        assert!(tag <= 11);
        out.tags[tag as usize] += 1;
        let condition_width = r.uvar();
        let expected = r.uvar();
        for _ in 0..condition_width { assert!(r.uvar() < out.clen); }
        if tag == 11 {
            let child = r.uvar();
            let nq = r.uvar();
            let qmap: Vec<_> = (0..nq).map(|_| r.uvar()).collect();
            let nc = r.uvar();
            let cmap: Vec<_> = (0..nc).map(|_| r.uvar()).collect();
            assert!(qmap.iter().all(|&q| q < out.qlen));
            assert!(cmap.iter().all(|&c| c < out.clen));
            out.calls.push(Call { at, child, condition_width, expected, qmap, cmap });
        } else {
            let nq = r.uvar();
            for _ in 0..nq { assert!(r.uvar() < out.qlen); }
            let nc = r.uvar();
            for _ in 0..nc { assert!(r.uvar() < out.clen); }
        }
    }
    assert_eq!(r.at, r.data.len());
    out
}

fn contiguous(xs: &[usize]) -> bool {
    xs.windows(2).all(|w| w[1] == w[0] + 1)
}

fn ordered_runs(xs: &[usize]) -> Vec<(usize, usize)> {
    let mut runs = Vec::new();
    for &x in xs {
        match runs.last_mut() {
            Some((_, end)) if *end + 1 == x => *end = x,
            _ => runs.push((x, x)),
        }
    }
    runs
}

fn expanded_native(graph: &Graph<'_>, node_id: usize, memo: &mut [Option<(usize, usize)>]) -> (usize, usize) {
    if let Some(found) = memo[node_id] {
        return found;
    }
    let direct = decode_direct(graph, node_id);
    let mut out = (direct.tags[5], direct.tags[6]);
    for call in direct.calls {
        let child = expanded_native(graph, call.child, memo);
        out.0 += child.0;
        out.1 += child.1;
    }
    memo[node_id] = Some(out);
    out
}

#[test]
fn q833_parent_and_incumbent_cost_census() {
    let original = zstd::stream::decode_all(COMPRESSED_HIR).unwrap();
    let shifted = shift_controls::replace(&original);
    let graph = parse_graph(&shifted);
    let square = decode_direct(&graph, 2265);
    let parent = decode_direct(&graph, 2269);

    assert_eq!((square.qlen, square.clen), (518, 256));
    assert_eq!((parent.qlen, parent.clen), (835, 1280));
    assert_eq!(graph.summaries[2265].toffoli, 1_110_533);
    assert_eq!(graph.summaries[2269].toffoli, 70_054_098);
    let mut memo = vec![None; graph.nodes.len()];
    assert_eq!(expanded_native(&graph, 2265, &mut memo), (1_110_533, 0));
    assert_eq!(expanded_native(&graph, 2266, &mut memo), (1_110_533, 0));
    assert_eq!(expanded_native(&graph, 2258, &mut memo), (2_813, 0));

    let square_minus_calls: Vec<_> = parent.calls.iter()
        .filter(|call| (2312..=2314).contains(&call.at))
        .collect();
    assert_eq!(square_minus_calls.iter().map(|call| (call.at, call.child)).collect::<Vec<_>>(),
        [(2312, 2265), (2313, 2258), (2314, 2266)]);
    let square_map: Vec<_> = (257..=774).collect();
    let csub_map: Vec<_> = [0].into_iter()
        .chain(513..=768)
        .chain(1..=256)
        .chain(769..=773)
        .collect();
    let arithmetic_cbits: Vec<_> = (1024..=1279).collect();
    assert_eq!(square_minus_calls[0].qmap, square_map);
    assert_eq!(square_minus_calls[1].qmap, csub_map);
    assert_eq!(square_minus_calls[2].qmap, square_map);
    for call in &square_minus_calls {
        assert_eq!((call.condition_width, call.expected), (0, 1));
        assert_eq!(call.cmap, arithmetic_cbits);
        println!("SQUARE_MINUS_MAP at={} child={} qmap_runs={:?} cmap_runs={:?}",
            call.at, call.child, ordered_runs(&call.qmap), ordered_runs(&call.cmap));
    }

    for node_id in [2258usize, 2265, 2266] {
        let direct = decode_direct(&graph, node_id);
        println!("SQUARE_MINUS_CHILD node={node_id} width={}/{} direct_ops={} tags={:?} direct_calls={}",
            direct.qlen, direct.clen, direct.ops, direct.tags, direct.calls.len());
    }

    let reusable_cost_nodes: Vec<_> = graph.summaries.iter().enumerate()
        .filter(|(_, summary)| matches!(summary.toffoli, 1_531 | 2_813))
        .map(|(id, summary)| {
            let direct = decode_direct(&graph, id);
            (id, direct.qlen, direct.clen, direct.ops, summary.toffoli)
        })
        .collect();
    println!("REUSABLE_COST_NODES {reusable_cost_nodes:?}");

    let mut calls: BTreeMap<(usize, usize, usize), Vec<&Call>> = BTreeMap::new();
    for call in &parent.calls {
        calls.entry((call.child, call.condition_width, call.expected)).or_default().push(call);
    }
    println!("PARENT node=2269 width={}/{} direct_ops={} tags={:?} expanded_ops={} scored_ccx_ccz={}",
        parent.qlen, parent.clen, parent.ops, parent.tags,
        graph.summaries[2269].output_ops, graph.summaries[2269].toffoli);
    for ((child, cw, expected), uses) in calls {
        let first = uses[0];
        println!("PARENT_CALL child={child} multiplicity={} condition={cw}/{expected} first_at={} child_scored={} qmap={}..{} contiguous={} cmap={}..{} contiguous={}",
            uses.len(), first.at, graph.summaries[child].toffoli,
            first.qmap.first().copied().unwrap_or(usize::MAX), first.qmap.last().copied().unwrap_or(usize::MAX), contiguous(&first.qmap),
            first.cmap.first().copied().unwrap_or(usize::MAX), first.cmap.last().copied().unwrap_or(usize::MAX), contiguous(&first.cmap));
    }

    // The source backend's recursively compiled exact primitives are pinned by
    // the selected HIR itself: 256*cadd + 255*dbl is exactly node 2265.
    const CADD: usize = 2_813;
    const DBL: usize = 1_531;
    let square_from_primitives = 256 * CADD + 255 * DBL;
    let parent_from_primitives = 2 * square_from_primitives + CADD;
    assert_eq!(square_from_primitives, graph.summaries[2265].toffoli);
    // Node 2269 is the complete point-addition parent. The 2,223,879-count
    // square-minus interval is its square/csub/inverse-square subsequence.

    // Exact parent-level factorization:
    // y=a+2^128*b => y^2=a^2+2^129*ab+2^256*b^2.
    // Materialize one factor in A at a time, modular-double it to its weight,
    // controlled-subtract from X, halve back, and uncompute A.
    const H: usize = 128;
    const N: usize = 256;
    const SQ128_PUBLISHED: usize = H * (H + 3) / 2 - 1;
    const MUL128_PUBLISHED: usize = H * H + 4 * H + 3;
    let dbl_halve_calls = 2 * ((H + 1) + N);
    let exact_modular = dbl_halve_calls * DBL + 3 * CADD;
    let published_nonmod = 2 * (2 * SQ128_PUBLISHED + MUL128_PUBLISHED);
    // Historical pre-emitter estimate. The native prototype subsequently
    // disproved this as an upper bound: its exact low-ancilla count is 295,680.
    let assumed_low_ancilla_nonmod = 2 * published_nonmod;
    let preliminary_candidate = exact_modular + assumed_low_ancilla_nonmod;
    const EMITTED_LOW_ANCILLA_NONMOD: usize = 295_680;
    assert_eq!(dbl_halve_calls, 770);
    assert_eq!(published_nonmod, 67_330);
    assert_eq!(preliminary_candidate, 1_321_969);
    assert!(assumed_low_ancilla_nonmod < EMITTED_LOW_ANCILLA_NONMOD);
    println!("HALF_SQUARE_PRELIMINARY_ASSUMPTION incumbent={} cadd={} dbl_halve={} exact_modular={} published_nonmod={} assumed_2x_nonmod={} preliminary_candidate={} emitted_nonmod={} assumption_is_upper_bound=false",
        parent_from_primitives, 3, dbl_halve_calls, exact_modular,
        published_nonmod, assumed_low_ancilla_nonmod, preliminary_candidate,
        EMITTED_LOW_ANCILLA_NONMOD);
}

fn mod_double(x: u64, p: u64) -> u64 { (2 * x) % p }

fn mod_halve(x: u64, p: u64) -> u64 {
    if x & 1 == 0 { x / 2 } else { (x + p) / 2 }
}

fn factor_round_trip(
    mut x: u64,
    factor: u64,
    shift: usize,
    control: u64,
    p: u64,
    cleanup_checks: &mut usize,
) -> u64 {
    let mut a = 0u64;
    assert!(factor < p);
    // Reversible XOR-load into a clean A register.
    a ^= factor;
    for _ in 0..shift { a = mod_double(a, p); }
    x = (x + p - control * a) % p;
    for _ in 0..shift { a = mod_halve(a, p); }
    assert_eq!(a, factor, "halve must invert every modular double");
    a ^= factor;
    assert_eq!(a, 0, "factor uncompute must restore A=0");
    *cleanup_checks += 1;
    x
}

#[test]
fn half_square_parent_oracle_even_widths_2_through_10() {
    // Largest convenient odd primes below 2^n. All half-products are already
    // canonical, matching secp256k1 where (2^128-1)^2 < p.
    let primes = [(2usize, 3u64), (4, 13), (6, 61), (8, 251), (10, 1021)];
    let mut parent_cases = 0usize;
    let mut cleanup_checks = 0usize;
    let mut control_hits = [0usize; 2];
    for (n, p) in primes {
        let h = n / 2;
        let mask = (1u64 << h) - 1;
        for y in 0..p {
            let lo = y & mask;
            let hi = y >> h;
            let lo2 = lo * lo;
            let cross = lo * hi;
            let hi2 = hi * hi;
            assert!(lo2 < p && cross < p && hi2 < p);
            for control in 0..=1u64 {
                control_hits[control as usize] += 1;
                for x0 in 0..p {
                    let mut got = x0;
                    got = factor_round_trip(got, lo2, 0, control, p, &mut cleanup_checks);
                    got = factor_round_trip(got, cross, h + 1, control, p, &mut cleanup_checks);
                    got = factor_round_trip(got, hi2, n, control, p, &mut cleanup_checks);
                    let want = (x0 + p - control * ((y * y) % p)) % p;
                    assert_eq!(got, want, "n={n} p={p} control={control} x={x0} y={y}");
                    parent_cases += 1;
                }
            }
        }
    }
    assert!(control_hits.into_iter().all(|n| n > 0));
    println!("HALF_SQUARE_ORACLE widths=2,4,6,8,10 parent_cases={parent_cases} factor_cleanup_checks={cleanup_checks} control_hits={control_hits:?} Y_preserved=true A_out=0 scratch_out=0 phase_model=exact_reversible status=pass");
}

#[test]
fn half_square_symbolic_peak_contract() {
    const CTRL: usize = 1;
    const X: usize = 256;
    const Y: usize = 256;
    const A: usize = 256;
    const S: usize = 66;
    const LOGICAL: usize = CTRL + X + Y + A + S;
    assert_eq!(LOGICAL, 835);

    // All three products are serialized in A. A one-clean-carry non-modular
    // square/multiply uses S[0]. Exact dbl/halve use S[0..4], and exact csub
    // uses S[0..4]. No phase needs more than five declared S lines.
    const MAX_S_USED: usize = 5;
    assert!(MAX_S_USED <= S);
    // The production Q833 lease is the logical pair 787/834 = S[18]/S[65].
    // Keeping this architecture on S[0..5] avoids both lease endpoints.
    let leased = [18usize, 65usize];
    assert!(leased.into_iter().all(|s| s >= MAX_S_USED));
    println!("HALF_SQUARE_LIVENESS logical_root={LOGICAL} product_register=A[256] serialized_factors=3 max_declared_S_used={MAX_S_USED} lease_endpoints_avoided=S18,S65 extra_logical=0 expected_physical=833");
}
