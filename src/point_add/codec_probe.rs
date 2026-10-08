//! Exact finite-support checks of the actual emitted codec operations.
//! HMR outcomes are independent formal variables, so zero final phase checks
//! every measurement branch, not a sampled set. Valid basis inputs together
//! with zero relative phases establish the promised-subspace quantum map.
use super::*;
use crate::circuit::{Op, OperationType as K, NO_BIT};

struct Read {
    at: usize,
    trit: usize,
    typ: QubitId,
    s: QubitId,
}

fn emit(
    n: usize,
    order: usize,
) -> (
    Vec<Op>,
    Vec<(usize, QubitId, QubitId)>,
    Vec<Read>,
    Vec<(QubitId, QubitId)>,
    usize,
    usize,
    u32,
) {
    let mut c = Builder::new();
    let mut tape = Tape::new(n);
    let mut input = Vec::new();
    let mut reads = Vec::new();
    for t in 0..n {
        let qs = c.alloc_qubits(2);
        let pair = (qs[0], qs[1]);
        input.push((c.op_count(), pair.0, pair.1));
        tape.raw[t] = Some(pair);
        if t == 2 {
            tape.pack3(&mut c, 0);
        }
        if t == 4 {
            tape.pack5(&mut c, 0);
        }
    }
    // Both complete traversal orders, with complete repack between reads.
    for pass in 0..2 {
        let mut sequence = (0..n).collect::<Vec<_>>();
        if (pass + order) % 2 == 1 {
            sequence.reverse();
        }
        for t in sequence {
            tape.ensure_raw(&mut c, t);
            let (typ, s) = tape.get(t);
            reads.push(Read {
                at: c.op_count(),
                trit: t,
                typ,
                s,
            });
        }
        tape.repack(&mut c, 0, n);
    }
    let mut output = vec![(QubitId(0), QubitId(0)); n];
    for t in (0..n).rev() {
        tape.ensure_raw(&mut c, t);
        if t > 0 {
            tape.ensure_raw(&mut c, t - 1);
        }
        output[t] = tape.raw[t].take().unwrap();
    }
    assert!(tape.all_consumed());
    let dims = c.i13_dims();
    let peak = c.peak_total();
    (c.take_ops(), input, reads, output, dims.0, dims.1, peak)
}

fn sim(op: &Op, q: &mut [bool], bits: &mut [u128], phase: &mut u128, measurements: &mut usize) {
    let t = op.q_target.0 as usize;
    let a = op.q_control1.0 as usize;
    let b = op.q_control2.0 as usize;
    let condition = if op.c_condition == NO_BIT {
        1
    } else {
        bits[op.c_condition.0 as usize]
    };
    match op.kind {
        K::X => {
            assert_eq!(condition, 1);
            q[t] ^= true;
        }
        K::CX => {
            assert_eq!(condition, 1);
            q[t] ^= q[a];
        }
        K::CCX => {
            assert_eq!(condition, 1);
            q[t] ^= q[a] & q[b];
        }
        K::Swap => {
            assert_eq!(condition, 1);
            q.swap(t, a);
        }
        K::Z => {
            if q[t] {
                *phase ^= condition;
            }
        }
        K::CZ => {
            if q[t] & q[a] {
                *phase ^= condition;
            }
        }
        K::CCZ => {
            if q[t] & q[a] & q[b] {
                *phase ^= condition;
            }
        }
        K::Hmr => {
            *measurements += 1;
            assert!(*measurements < 128);
            let m = 1u128 << *measurements;
            bits[op.c_target.0 as usize] = m;
            if q[t] {
                *phase ^= m;
            }
            q[t] = false;
        }
        K::R => {
            assert!(!q[t], "reset of nonzero scratch wire {}", t);
        }
        K::BitStore0 => bits[op.c_target.0 as usize] = 0,
        K::BitStore1 => bits[op.c_target.0 as usize] = 1,
        K::Register | K::AppendToRegister => {}
        _ => panic!("unsupported symbolic codec gate {:?}", op.kind),
    }
}

pub fn run() {
    for n in [3usize, 5] {
        for order in 0..2 {
            let (ops, input, reads, output, nq, nb, peak) = emit(n, order);
            let ccx = ops
                .iter()
                .filter(|op| matches!(op.kind, K::CCX | K::CCZ))
                .count();
            let hmr = ops.iter().filter(|op| op.kind == K::Hmr).count();
            for word in 0..3usize.pow(n as u32) {
                let mut original = Vec::new();
                let mut digits = word;
                let mut q = vec![false; nq];
                let mut bits = vec![0u128; nb];
                let mut phase = 0u128;
                let mut measurements = 0;
                for _ in &input {
                    let trit = digits % 3;
                    digits /= 3;
                    let h = trit == 2;
                    let l = trit == 1;
                    let value = (true ^ h ^ l, h);
                    original.push(value);
                }
                let mut read = 0;
                for pos in 0..=ops.len() {
                    for (i, (at, typ, s)) in input.iter().enumerate() {
                        if *at == pos {
                            assert!(!q[typ.0 as usize] && !q[s.0 as usize]);
                            q[typ.0 as usize] = original[i].0;
                            q[s.0 as usize] = original[i].1;
                        }
                    }
                    while read < reads.len() && reads[read].at == pos {
                        let r = &reads[read];
                        assert_eq!(
                            (q[r.typ.0 as usize], q[r.s.0 as usize]),
                            original[r.trit],
                            "read n={n} order={order} word={word} t={}",
                            r.trit
                        );
                        read += 1;
                    }
                    if pos < ops.len() {
                        sim(&ops[pos], &mut q, &mut bits, &mut phase, &mut measurements);
                    }
                }
                assert_eq!(read, reads.len());
                assert_eq!(phase, 0, "phase n={n} order={order} word={word}");
                for (i, (typ, s)) in output.iter().enumerate() {
                    assert_eq!((q[typ.0 as usize], q[s.0 as usize]), original[i]);
                    q[typ.0 as usize] = false;
                    q[s.0 as usize] = false;
                }
                assert!(q.iter().all(|v| !*v));
            }
            println!("{{\"kind\":\"actual-rust-codec-lifecycle\",\"trits\":{n},\"first_read_reverse\":{},\"valid_cases\":{},\"ccx\":{ccx},\"peak\":{peak},\"hmr\":{hmr},\"measurement_branches\":\"symbolically exhaustive\",\"value\":\"pass\",\"phase\":\"pass\",\"cleanup\":\"pass\"}}",order==1,3usize.pow(n as u32));
        }
    }
    run_synth();
}

fn run_synth() {
    for order in 0..2 {
        let mut c = Builder::new();
        let wires = c.alloc_qubits(6);
        let input: [QubitId; 6] = wires.try_into().unwrap();
        let mut raw = input;
        let mut reads = Vec::new();
        for pass in 0..3 {
            let packed = codec_synth::pack(&mut c, raw);
            raw = codec_synth::unpack(&mut c, packed);
            let mut sequence = (0..3).collect::<Vec<_>>();
            if (pass + order) % 2 == 1 {
                sequence.reverse();
            }
            for trit in sequence {
                reads.push((c.op_count(), trit, raw[2 * trit], raw[2 * trit + 1]));
            }
        }
        let (nq, nb) = c.i13_dims();
        let peak = c.peak_total();
        let ops = c.take_ops();
        for word in 0..27 {
            let mut q = vec![false; nq];
            let mut bits = vec![0; nb];
            let mut phase = 0;
            let mut measurements = 0;
            let mut digits = word;
            let mut original = Vec::new();
            for t in 0..3 {
                let v = digits % 3;
                digits /= 3;
                let pair = (v & 1 != 0, v & 2 != 0);
                original.push(pair);
                q[input[2 * t].0 as usize] = pair.0;
                q[input[2 * t + 1].0 as usize] = pair.1;
            }
            for pos in 0..=ops.len() {
                for &(at, t, h, l) in &reads {
                    if at == pos {
                        assert_eq!((q[h.0 as usize], q[l.0 as usize]), original[t]);
                    }
                }
                if pos < ops.len() {
                    sim(&ops[pos], &mut q, &mut bits, &mut phase, &mut measurements);
                }
            }
            assert_eq!(phase, 0, "synth phase word={word}");
            for t in 0..3 {
                assert_eq!(
                    (q[raw[2 * t].0 as usize], q[raw[2 * t + 1].0 as usize]),
                    original[t]
                );
                q[raw[2 * t].0 as usize] = false;
                q[raw[2 * t + 1].0 as usize] = false;
            }
            assert!(q.iter().all(|v| !*v));
        }
        let ccx = ops.iter().filter(|o| o.kind == K::CCX).count();
        let hmr = ops.iter().filter(|o| o.kind == K::Hmr).count();
        println!("{{\"kind\":\"synthesized-rust-codec-lifecycle\",\"trits\":3,\"first_read_reverse\":{},\"valid_cases\":27,\"ccx\":{ccx},\"peak\":{peak},\"hmr\":{hmr},\"measurement_branches\":\"symbolically exhaustive\",\"value\":\"pass\",\"phase\":\"pass\",\"cleanup\":\"pass\"}}",order==1);
    }
}
