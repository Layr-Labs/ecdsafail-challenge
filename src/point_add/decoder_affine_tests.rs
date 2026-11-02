//! Native-only decoder transition/lifecycle checks. Authored but UNRUN.
//! Uses the actual Dec and original Simulator; no point-add inputs or schedules.
use super::{mc_xor, Dec};
use crate::circuit::{OperationType, QubitId};
use crate::point_add::builder::B;
use crate::sim::Simulator;
use sha3::digest::XofReader;

const NB: usize = 3;
const PHASES: [u64; 2] = [0, 0xa569_36c3_96a5_c33c];
const INITIAL_BITS: [u64; NB] = [
    0x8123_4567_89ab_cdef, 0x9696_a5a5_5a5a_6969, 0x1234_5678_8765_4321,
];

struct Tape { words: Vec<u64>, used: usize }
impl XofReader for Tape {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8, "original Simulator draw width changed");
        let word = self.words[self.used];
        self.used += 1;
        out.copy_from_slice(&word.to_le_bytes());
    }
}

// Literal old goto_h; its comp helper is unchanged by the production patch.
// This comparison arm is not the expected-value oracle.
fn parent_move(dec: &mut Dec<'_>, b: &mut B, j: usize, levels: usize) {
    let n = dec.v.len();
    let keep = match dec.cur {
        None => 0,
        Some(c) => {
            let mut kp = 0;
            while kp < levels && ((c ^ j) >> (n - 2 - kp)) == 0 { kp += 1; }
            kp
        }
    };
    if let Some(c) = dec.cur {
        for i in (keep..levels).rev() { dec.comp(b, i, c, true); }
    }
    for i in keep..levels { dec.comp(b, i, j, false); }
    dec.cur = Some(j);
}

fn transition(b: &mut B, candidate: bool, n: usize, h: usize, old: usize, new: usize) {
    let v: Vec<_> = (0..n).map(|i| QubitId(i as u64)).collect();
    let pre: Vec<_> = (n..n+h).map(|i| QubitId(i as u64)).collect();
    let mut dec = Dec::new(&v, &pre);
    // The test's initial state explicitly satisfies every old-prefix equation.
    dec.cur = Some(old);
    if candidate { dec.goto_h(b, new, h); }
    else { parent_move(&mut dec, b, new, h); }
    assert_eq!(dec.cur, Some(new));
}

// mode0 forward; mode1 literal inverse; mode2 forward then literal inverse.
fn build_transition(candidate: bool, nested: bool, mode: usize,
                    n: usize, h: usize, old: usize, new: usize) -> B {
    let nq = n + h + 2;
    let mut b = B::new();
    b.alloc_n(nq);
    if nested { b.begin(); b.begin(); }
    if mode != 1 { transition(&mut b, candidate, n, h, old, new); }
    if mode != 0 {
        b.begin();
        transition(&mut b, candidate, n, h, old, new);
        let rec = b.end();
        b.play(&rec, true);
    }
    if nested {
        let inner = b.end(); b.play(&inner, false);
        let outer = b.end(); b.play(&outer, false);
    }
    assert_eq!(b.width(), nq as u64);
    assert_eq!(b.live, nq as u64);
    assert_eq!(b.peak, nq as u64);
    b
}

// Direct prefix equality, independent of the gate/keep logic.
fn transition_state(n: usize, h: usize, selector: usize) -> Vec<u64> {
    let mut q = vec![0u64; n+h+2];
    for lane in 0..64usize {
        let value = lane & ((1usize << n)-1);
        for i in 0..n { q[i] |= (((value >> i) & 1) as u64) << lane; }
        for i in 0..h {
            let shift = n-i-2;
            let matched = (value >> shift) == (selector >> shift);
            q[n+i] |= (matched as u64) << lane;
        }
        q[n+h] |= (((lane >> n) & 1) as u64) << lane;
        q[n+h+1] |= (((lane >> (n+1)) & 1) as u64) << lane;
    }
    q
}

fn check_run(b: &B, initial: &[u64], wanted: &[u64], words: Vec<u64>, phase: u64) {
    let mut wanted_bits = INITIAL_BITS.to_vec();
    if let Some(&last) = words.last() { wanted_bits[0] = last; }
    let draws = words.len();
    let mut tape = Tape { words, used: 0 };
    {
        let mut sim = Simulator::new(initial.len(), NB, &mut tape);
        sim.qubits.clone_from_slice(initial);
        sim.bits.clone_from_slice(&INITIAL_BITS);
        sim.phase = phase;
        // One complete original call: never reset its captured-mask stack midword.
        sim.apply_iter(b.ops.iter());
        assert_eq!(sim.qubits, wanted, "full quantum state");
        assert_eq!(sim.bits, wanted_bits, "scratch transcript and all classical spectators");
        assert_eq!(sim.phase, phase, "phase restored");
        assert_eq!(sim.stats.toffoli_gates, 64*b.tof, "literal executed CCX count");
    }
    assert_eq!(tape.used, draws, "all and only expected measurement draws");
}

#[test]
fn exhaustive_transition_values_outcomes_and_inverses() {
    let mut layouts = 0usize;
    let mut words_built = 0usize;
    let mut packs = 0usize;
    let mut distribution = [0usize; 4];
    for n in 2..=4usize {
        for h in 1..n {
            for old in 0..1usize<<n {
                for new in 0..1usize<<n {
                    // Count directly which prefix equalities have changed.
                    let changed = (0..h).filter(|&i|
                        (old >> (n-i-2)) != (new >> (n-i-2))).count();
                    distribution[changed] += 1;
                    layouts += 1;
                    for candidate in [false, true] {
                        let per_pass = if candidate { changed.saturating_sub(1) } else { changed };
                        for nested in [false, true] {
                            for mode in 0..3usize {
                                let b = build_transition(candidate, nested, mode, n, h, old, new);
                                let passes = if mode == 2 { 2 } else { 1 };
                                let draws = passes * per_pass;
                                assert_eq!(b.tof, draws as u64);
                                assert_eq!(b.ops.iter().filter(|o| o.kind == OperationType::Hmr).count(), draws);
                                assert_eq!(b.ops.iter().filter(|o| o.kind == OperationType::CZ).count(), draws);
                                assert!(b.ops.len() <= 66, "fixed small-word resource cap");
                                words_built += 1;
                                let initial_selector = if mode == 1 { new } else { old };
                                let final_selector = if mode == 0 { new } else { old };
                                let initial = transition_state(n, h, initial_selector);
                                let wanted = transition_state(n, h, final_selector);
                                for outcome in 0..1usize<<draws {
                                    let tape: Vec<_> = (0..draws).map(|i|
                                        if (outcome >> i) & 1 == 0 { 0 } else { u64::MAX }).collect();
                                    for phase in PHASES {
                                        check_run(&b, &initial, &wanted, tape.clone(), phase);
                                        packs += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(distribution, [140, 308, 272, 192]);
    assert_eq!(layouts, 912);
    assert_eq!(words_built, 10_944);
    assert_eq!(packs, 131_600);
    eprintln!("DECODER_AFFINE_TRANSITION layouts={layouts} words={words_built} packs={packs} basis_instances={} full_state_checks={} failures=0",
              packs*64, packs*5);
}

fn selectors(n: usize, style: usize) -> Vec<usize> {
    let mut list = vec![0, 1, 1, (1usize<<(n-2))-1, 1usize<<(n-2),
                        (1usize<<(n-1))-1, 1usize<<(n-1), (1usize<<n)-1];
    match style {
        0 => {},
        1 => list.reverse(),
        2 => { for j in &mut list { *j ^= *j >> 1; } },
        _ => unreachable!(),
    }
    list
}

// Layout: value[n], held[h], independent XOR query outputs[n+1], dirty[5].
// The last five wires are arbitrary; they are not extra clean decoder resources.
fn scan(b: &mut B, n: usize, h: usize, style: usize) {
    let v: Vec<_> = (0..n).map(|i| QubitId(i as u64)).collect();
    let pre: Vec<_> = (n..n+h).map(|i| QubitId(i as u64)).collect();
    let out0 = n+h;
    let dirty: Vec<_> = (out0+n+1..out0+n+6).map(|i| QubitId(i as u64)).collect();
    let mut dec = Dec::new(&v, &pre);
    for j in selectors(n, style) {
        let controls = if h == n-1 {
            vec![(dec.goto(b, j), false)]
        } else {
            dec.ctrls(b, j)
        };
        mc_xor(b, &controls, QubitId(out0 as u64), &[], &dirty);
        for i in 0..n {
            if (j >> i) & 1 != 0 {
                mc_xor(b, &controls, QubitId((out0+1+i) as u64), &[], &dirty);
            }
        }
    }
    dec.clear(b);
    dec.clear(b); // a cleared decoder must be safe to clear again
    assert_eq!(dec.cur, None);
}

fn build_scan(n: usize, h: usize, style: usize, mode: usize) -> B {
    let nq = 2*n+h+6;
    let mut b = B::new();
    b.alloc_n(nq);
    b.begin(); b.begin();
    if mode != 1 { scan(&mut b, n, h, style); }
    if mode != 0 {
        b.begin(); scan(&mut b, n, h, style); let word = b.end();
        b.play(&word, true);
    }
    let inner = b.end(); b.play(&inner, false);
    let outer = b.end(); b.play(&outer, false);
    assert_eq!(b.width(), nq as u64);
    assert_eq!(b.live, nq as u64);
    assert_eq!(b.peak, nq as u64);
    assert!(b.ops.len() <= 6000, "fixed wide-word resource cap");
    b
}

fn scan_states(n: usize, h: usize, style: usize, mode: usize, batch: usize) -> (Vec<u64>, Vec<u64>) {
    let nq = 2*n+h+6;
    let out0 = n+h;
    let mut initial = vec![0u64; nq];
    for lane in 0..64usize {
        let value = (64*batch+lane) & ((1usize<<n)-1);
        for i in 0..n { initial[i] |= (((value>>i)&1) as u64)<<lane; }
    }
    // Fixed mixed arbitrary output/dirty bit planes; all are checked for restoration.
    for i in out0..nq {
        initial[i] = 0x963c_a55a_f00f_6996u64.rotate_left(((7*i+3*batch)%64) as u32);
    }
    let mut wanted = initial.clone();
    if mode != 2 {
        for lane in 0..64usize {
            let value = (64*batch+lane) & ((1usize<<n)-1);
            for j in selectors(n, style) {
                if value == j {
                    wanted[out0] ^= 1u64<<lane;
                    for i in 0..n {
                        wanted[out0+1+i] ^= (((j>>i)&1) as u64)<<lane;
                    }
                }
            }
        }
    }
    (initial, wanted)
}

#[test]
fn actual_width_lifecycle_queries_and_dirty_restoration() {
    let mut words_built = 0usize;
    let mut packs = 0usize;
    for n in 5..=7usize {
        for h in 0..n {
            for style in 0..3usize {
                for mode in 0..3usize {
                    let b = build_scan(n, h, style, mode);
                    let draws = b.ops.iter().filter(|o| o.kind == OperationType::Hmr).count();
                    assert_eq!(b.ops.iter().filter(|o| o.kind == OperationType::CZ).count(), draws);
                    words_built += 1;
                    for batch in 0..((1usize<<n)+63)/64 {
                        let (initial, wanted) = scan_states(n, h, style, mode, batch);
                        for tape_style in 0..2usize {
                            let tape: Vec<_> = (0..draws).map(|i| {
                                let q = 0xa53c_69f0_96a5_c33cu64.rotate_left(((11*i+batch)%64) as u32);
                                if tape_style == 0 { q } else { !q }
                            }).collect();
                            for phase in PHASES {
                                check_run(&b, &initial, &wanted, tape.clone(), phase);
                                packs += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(words_built, 162);
    assert_eq!(packs, 900);
    eprintln!("DECODER_AFFINE_LIFECYCLE words={words_built} packs={packs} basis_instances={} full_state_checks={} failures=0",
              packs*64, packs*5);
}
