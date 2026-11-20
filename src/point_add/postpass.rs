//! B-POSTPASS (Q825 program): exact generic op-stream passes run on the final stream after lease_pass, each behind a
//! const, plus dev-only stream I/O for iterating the pass chain on a saved stream (inert in the official empty
//! environment).
//!
//! Passes (names as in `PP_PASSES`):
//! - `fix`: the Boolean passes again on the post-lease stream (truth tables to a fixed point, nine-atom tables,
//!   cond_pass m/f/s/u/r), then the adjacent CCX canceller;
//! - `iw`: interned_witness (CCX -> CX from a live wire holding the exact product, affine + interned products);
//! - `zf`: zero_force (an X measurement of a wire that is the same constant on every shot is forced to outcome 0)
//!   followed by `dead`;
//! - `dead`: blocks and ops conditioned on a bit that holds 0 on every shot (last write an unconditional
//!   BIT_STORE0 at depth 0) are deleted (they never run);
//! - `cfx`: classical-value XOR factoring (CCX whose effective AND equals a classical bit times one control ->
//!   CX under the bit), both the seven- and nine-atom versions;
//! - `mab`: K3a measurement absorption;
//! - `adj`: cancel_adjacent_ccx.
use crate::circuit::{Op, OperationType as K, NO_BIT};

/// The passes of the official build, in order (empty: the stream after lease_pass is final).
/// MICRO-SHELL PP-FIX2: a second `fix,iw` round after the first converges further (-335 T on the M-017 stream).
pub const PASSES: &str = "zf,iw,cfx,fix,iw,fix,iw";

pub fn run(mut ops: Vec<Op>) -> Vec<Op> {
    // dev only: PP_PASSES overrides the official list (the official build runs with an empty environment)
    let list = std::env::var("PP_PASSES").unwrap_or_else(|_| PASSES.to_string());
    for name in list.split(',').map(str::trim).filter(|s| !s.is_empty()) {
        let before = super::counts(&ops);
        let t0 = std::time::Instant::now();
        ops = match name {
            "fix" => {
                for _ in 0..16 {
                    let previous = super::counts(&ops);
                    ops = super::truth_simplify::simplify_products(ops);
                    if super::counts(&ops) == previous { break; }
                }
                ops = super::classical_wide::simplify_products(ops);
                ops = super::cond_pass::run_with(ops, "mfsur");
                super::cancel_adjacent_ccx(&mut ops);
                ops
            }
            "truth" => {
                for _ in 0..16 {
                    let previous = super::counts(&ops);
                    ops = super::truth_simplify::simplify_products(ops);
                    if super::counts(&ops) == previous { break; }
                }
                ops
            }
            "wide" => super::classical_wide::simplify_products(ops),
            "cond" => super::cond_pass::run_with(ops, "mfsur"),
            "condmf" => super::cond_pass::run_with(ops, "mfs"),
            "iw" => super::interned_witness::witnesses(ops),
            "zf" => dead(super::zero_force::run(ops)),
            "dead" => dead(ops),
            "cfx" => {
                let ops = super::classical_factors_xor::simplify_classical(ops);
                super::classical_wide::simplify_classical(ops)
            }
            "mab" => super::mabsorb::absorb(ops),
            "adj" => {
                super::cancel_adjacent_ccx(&mut ops);
                ops
            }
            other => panic!("postpass: unknown pass {other}"),
        };
        eprintln!("POSTPASS_PP {name} before={before:?} after={:?} {:.1} s", super::counts(&ops),
                  t0.elapsed().as_secs_f64());
    }
    ops
}

/// Delete what never runs: a PUSH_CONDITION block (with everything nested in it) or an op whose per-op condition is
/// a bit known to be 0 on every shot. A bit is known 0 after an unconditional BIT_STORE0 at depth 0, until its next
/// write of any kind (a write inside a block or under a condition makes it unknown).
fn dead(ops: Vec<Op>) -> Vec<Op> {
    let nb = ops.iter().flat_map(|o| [o.c_target, o.c_condition]).filter(|b| *b != NO_BIT)
        .map(|b| b.0 as usize + 1).max().unwrap_or(0);
    let mut zero = vec![false; nb];
    let mut out = Vec::with_capacity(ops.len());
    let (mut depth, mut skip, mut removed, mut blocks) = (0usize, 0usize, 0usize, 0usize);
    for o in ops {
        if skip > 0 {
            match o.kind {
                K::PushCondition => skip += 1,
                K::PopCondition => skip -= 1,
                _ => {}
            }
            removed += 1;
            continue;
        }
        if o.kind == K::PushCondition && zero[o.c_condition.0 as usize] {
            skip = 1;
            blocks += 1;
            removed += 1;
            continue;
        }
        if o.c_condition != NO_BIT && zero[o.c_condition.0 as usize] && o.kind != K::PushCondition {
            removed += 1;
            continue;
        }
        match o.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth -= 1,
            K::Hmr | K::BitStore0 | K::BitStore1 | K::BitInvert => {
                let b = o.c_target.0 as usize;
                zero[b] = o.kind == K::BitStore0 && depth == 0 && o.c_condition == NO_BIT;
            }
            _ => {}
        }
        out.push(o);
    }
    eprintln!("POSTPASS_DEAD removed ops {removed} blocks {blocks}");
    out
}

/// dev only: read a build_circuit ops.bin (QECCOPSZ framing) and drop its 96-op tail nonce.
pub fn load(path: &str) -> Vec<Op> {
    use crate::circuit::{BitId, QubitId, RegisterId};
    use std::io::Read;
    let mut file = std::fs::File::open(path).expect("PP_LOAD: open");
    let mut header = [0u8; 16];
    file.read_exact(&mut header).unwrap();
    assert_eq!(&header[..8], b"QECCOPSZ");
    let n = u64::from_le_bytes(header[8..].try_into().unwrap()) as usize;
    let mut dec = zstd::stream::read::Decoder::new(std::io::BufReader::new(file)).unwrap();
    let mut ops = Vec::with_capacity(n);
    let mut rec = [0u8; 56];
    let rd = |r: &[u8], o: usize| u64::from_le_bytes(r[o..o + 8].try_into().unwrap());
    for _ in 0..n {
        dec.read_exact(&mut rec).unwrap();
        let kind_raw = u32::from_le_bytes(rec[0..4].try_into().unwrap());
        assert!(kind_raw <= 17);
        // OperationType discriminants are 0..=17 in declaration order
        let kind: K = unsafe { std::mem::transmute(kind_raw as u8) };
        ops.push(Op { kind, q_control2: QubitId(rd(&rec, 8)), q_control1: QubitId(rd(&rec, 16)),
                      q_target: QubitId(rd(&rec, 24)), c_target: BitId(rd(&rec, 32)),
                      c_condition: BitId(rd(&rec, 40)), r_target: RegisterId(rd(&rec, 48)) });
    }
    let m = ops.len() - 96;
    assert!(ops[m..].iter().all(|o| o.kind == K::X && o.q_target.0 <= 1));
    ops.truncate(m);
    eprintln!("PP_LOAD {path}: {} ops (tail nonce dropped)", ops.len());
    ops
}

/// dev only: write ops (plus a zero 96-op tail nonce) in build_circuit's framing.
pub fn dump(path: &str, ops: &[Op], tail: &[Op]) {
    use std::io::Write;
    let mut all: Vec<Op> = Vec::with_capacity(ops.len() + tail.len() + 96);
    all.extend_from_slice(ops);
    all.extend_from_slice(tail);
    super::append_tail_nonce(&mut all, 0);
    let mut w = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
    w.write_all(b"QECCOPSZ").unwrap();
    w.write_all(&(all.len() as u64).to_le_bytes()).unwrap();
    let mut enc = zstd::stream::write::Encoder::new(w, 3).unwrap();
    let mut rec = [0u8; 56];
    for op in &all {
        rec[0..4].copy_from_slice(&(op.kind as u32).to_le_bytes());
        rec[4..8].copy_from_slice(&[0u8; 4]);
        rec[8..16].copy_from_slice(&op.q_control2.0.to_le_bytes());
        rec[16..24].copy_from_slice(&op.q_control1.0.to_le_bytes());
        rec[24..32].copy_from_slice(&op.q_target.0.to_le_bytes());
        rec[32..40].copy_from_slice(&op.c_target.0.to_le_bytes());
        rec[40..48].copy_from_slice(&op.c_condition.0.to_le_bytes());
        rec[48..56].copy_from_slice(&op.r_target.0.to_le_bytes());
        enc.write_all(&rec).unwrap();
    }
    enc.finish().unwrap().flush().unwrap();
    eprintln!("PP_DUMP {path}: {} ops", all.len());
}
