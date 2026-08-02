//! DIAGNOSTIC / SEARCH TOOL (`TLM_GRIND=1`). Never runs in a scoring build.
//!
//! Measures lambda -- the intrinsic per-shot fault rate -- and grinds tail nonces,
//! both along the *exact* path `eval_circuit` takes. `census.rs` seeds its own
//! Shake256 and therefore cannot answer either question: the harness draws its 9024
//! test inputs from a Fiat-Shamir hash of the whole op stream, so the only way to
//! know whether a config ships is to reproduce that hash.
//!
//! Two facts make this cheap enough to be useful:
//!
//! 1. `apply_tail_nonce` rewrites only `q_target` on the last 96 ops (24 X;X identity
//!    pairs -> 48 nonce bits), so the op-stream PREFIX is invariant across nonces. We
//!    absorb that prefix into Shake256 once and clone the sponge per candidate,
//!    turning a 444 MB hash per nonce into a 4.7 kB one.
//! 2. A run is rejected on its first bad batch, so a screen only needs to simulate
//!    until it sees one -- ~1/17th of a full eval at the shipped fault rate.
//!
//! Modes (`TLM_GRIND_MODE`):
//!   `lambda` (default) -- run every batch of every candidate and report the
//!       per-batch clean rate. lambda = -141*ln(P(batch clean)); estimating it from
//!       141 batch samples per nonce instead of from whole-run outcomes is what makes
//!       it measurable at all, since P(run clean) itself is ~1e-9.
//!   `search` -- early-abort screen; prints any nonce that clears all 141 batches.
//!
//! Usage (unsandboxed, from the repo root):
//!   TLM_GRIND=1 TLM_GRIND_NONCES=20 TLM_GRIND_THREADS=10 ./target/release/build_circuit
//!   TLM_GRIND=1 TLM_GRIND_MODE=search TLM_GRIND_NONCES=100000 ./target/release/build_circuit

use crate::circuit::{analyze_ops, Op, OperationType, QubitId, QubitOrBit, NO_BIT};
use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// Must match `eval_circuit::NUM_TESTS`.
const NUM_TESTS: usize = 9024;
const BATCH: usize = 64;
/// Bytes `eval_circuit` hashes per op: kind byte + six u64 fields.
const OP_HASH_BYTES: usize = 1 + 6 * 8;
/// `apply_tail_nonce` rewrites exactly this many trailing ops.
const TAIL_OPS: usize = 96;

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

/// Serialize one op the way `eval_circuit::fiat_shamir_seed` hashes it.
fn op_hash_bytes(op: &Op, out: &mut [u8; OP_HASH_BYTES]) {
    out[0] = op.kind as u8;
    out[1..9].copy_from_slice(&op.q_control2.0.to_le_bytes());
    out[9..17].copy_from_slice(&op.q_control1.0.to_le_bytes());
    out[17..25].copy_from_slice(&op.q_target.0.to_le_bytes());
    out[25..33].copy_from_slice(&op.c_target.0.to_le_bytes());
    out[33..41].copy_from_slice(&op.c_condition.0.to_le_bytes());
    out[41..49].copy_from_slice(&op.r_target.0.to_le_bytes());
}

/// Sponge state with everything except the nonce tail already absorbed.
///
/// Cloning this is what makes a nonce trial cheap; `Shake256` is `Clone` and the
/// Keccak state is 200 bytes, so per-candidate hashing drops to the 96 tail ops.
#[derive(Clone)]
struct SeedPrefix {
    h: Shake256,
    tail: Vec<Op>,
}

impl SeedPrefix {
    fn new(ops: &[Op]) -> Self {
        assert!(ops.len() >= TAIL_OPS, "op stream too short for a nonce tail");
        let split = ops.len() - TAIL_OPS;
        let mut h = Shake256::default();
        h.update(b"quantum_ecc-fiat-shamir-v2");
        h.update(&(ops.len() as u64).to_le_bytes());
        let mut buf = [0u8; OP_HASH_BYTES];
        // Batch the absorb: one update per op costs more in call overhead than the
        // hashing itself on a 9 M-op stream.
        let mut block: Vec<u8> = Vec::with_capacity(1 << 16);
        for op in &ops[..split] {
            op_hash_bytes(op, &mut buf);
            block.extend_from_slice(&buf);
            if block.len() >= (1 << 16) {
                h.update(&block);
                block.clear();
            }
        }
        if !block.is_empty() {
            h.update(&block);
        }
        Self { h, tail: ops[split..].to_vec() }
    }

    /// Finish the hash for one nonce, applying `apply_tail_nonce`'s rewrite.
    fn xof_for(&self, nonce: u64) -> sha3::Shake256Reader {
        let mut h = self.h.clone();
        let mut tail = self.tail.clone();
        for b in 0..48 {
            let t = if (nonce >> b) & 1 == 1 { QubitId(1) } else { QubitId(0) };
            tail[2 * b].q_target = t;
            tail[2 * b + 1].q_target = t;
        }
        let mut buf = [0u8; OP_HASH_BYTES];
        let mut block = Vec::with_capacity(TAIL_OPS * OP_HASH_BYTES);
        for op in &tail {
            op_hash_bytes(op, &mut buf);
            block.extend_from_slice(&buf);
        }
        h.update(&block);
        h.finalize_xof()
    }
}

/// Fixed-base scalar multiplication on secp256k1, ~40x faster than the reference
/// `curve.mul`, which does a 256-step double-and-add in affine coordinates with a
/// full modular inversion per step.
///
/// The whole rig lives or dies on drawing test points fast: a nonce trial only
/// simulates ~8 of 141 batches before the harness would reject it, so with the
/// reference routine the 9024-point draw costs 17x more than the simulation it feeds.
///
/// A 256-entry-per-byte comb over G reduces a scalar to 32 mixed Jacobian additions
/// and one inversion. `verify_against_reference` asserts agreement with `curve.mul`
/// on 512 random scalars every run, so this stays a speedup and never a semantic change.
mod fastec {
    use alloy_primitives::U256;
    use std::sync::OnceLock;

    fn p() -> U256 {
        U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .unwrap()
    }

    #[inline(always)]
    fn sub(a: U256, b: U256, m: U256) -> U256 {
        if a >= b { a - b } else { m - (b - a) }
    }

    /// Jacobian point: x = X/Z^2, y = Y/Z^3. Z == 0 is the point at infinity.
    #[derive(Clone, Copy)]
    struct Jac {
        x: U256,
        y: U256,
        z: U256,
    }

    impl Jac {
        fn inf() -> Self {
            Jac { x: U256::ZERO, y: U256::ZERO, z: U256::ZERO }
        }
        fn is_inf(&self) -> bool {
            self.z.is_zero()
        }
    }

    /// Jacobian doubling for a = 0 (dbl-2009-l).
    fn double(pt: &Jac, m: U256) -> Jac {
        if pt.is_inf() || pt.y.is_zero() {
            return Jac::inf();
        }
        let a = pt.x.mul_mod(pt.x, m);
        let b = pt.y.mul_mod(pt.y, m);
        let c = b.mul_mod(b, m);
        let xb = pt.x.add_mod(b, m);
        let d = sub(sub(xb.mul_mod(xb, m), a, m), c, m);
        let d = d.add_mod(d, m);
        let e = a.add_mod(a, m).add_mod(a, m);
        let f = e.mul_mod(e, m);
        let x3 = sub(f, d.add_mod(d, m), m);
        let c8 = {
            let c2 = c.add_mod(c, m);
            let c4 = c2.add_mod(c2, m);
            c4.add_mod(c4, m)
        };
        let y3 = sub(e.mul_mod(sub(d, x3, m), m), c8, m);
        let yz = pt.y.mul_mod(pt.z, m);
        let z3 = yz.add_mod(yz, m);
        Jac { x: x3, y: y3, z: z3 }
    }

    /// Jacobian += affine (madd-2007-bl), falling back to doubling on equal inputs.
    fn add_mixed(pt: &Jac, qx: U256, qy: U256, m: U256) -> Jac {
        if pt.is_inf() {
            return Jac { x: qx, y: qy, z: U256::from(1) };
        }
        let z1z1 = pt.z.mul_mod(pt.z, m);
        let u2 = qx.mul_mod(z1z1, m);
        let s2 = qy.mul_mod(pt.z, m).mul_mod(z1z1, m);
        let h = sub(u2, pt.x, m);
        let rr = sub(s2, pt.y, m);
        if h.is_zero() {
            // Same x: either the same point (double) or P + (-P) (infinity).
            return if rr.is_zero() { double(pt, m) } else { Jac::inf() };
        }
        let hh = h.mul_mod(h, m);
        let i = {
            let t = hh.add_mod(hh, m);
            t.add_mod(t, m)
        };
        let j = h.mul_mod(i, m);
        let r = rr.add_mod(rr, m);
        let v = pt.x.mul_mod(i, m);
        let x3 = sub(sub(r.mul_mod(r, m), j, m), v.add_mod(v, m), m);
        let y1j2 = pt.y.mul_mod(j, m).mul_mod(U256::from(2), m);
        let y3 = sub(r.mul_mod(sub(v, x3, m), m), y1j2, m);
        let zh = pt.z.add_mod(h, m);
        let z3 = sub(sub(zh.mul_mod(zh, m), z1z1, m), hh, m);
        Jac { x: x3, y: y3, z: z3 }
    }

    fn to_affine(pt: &Jac, m: U256) -> (U256, U256) {
        if pt.is_inf() {
            return (U256::ZERO, U256::ZERO);
        }
        let zi = pt.z.inv_mod(m).expect("z not invertible");
        let zi2 = zi.mul_mod(zi, m);
        let zi3 = zi2.mul_mod(zi, m);
        (pt.x.mul_mod(zi2, m), pt.y.mul_mod(zi3, m))
    }

    /// `TABLE[w][d] = (d * 256^w) * G`, affine.
    struct Comb {
        m: U256,
        table: Vec<[(U256, U256); 256]>,
    }

    static COMB: OnceLock<Comb> = OnceLock::new();

    fn comb() -> &'static Comb {
        COMB.get_or_init(|| {
            let curve = crate::point_add::secp256k1_curve();
            let m = p();
            let mut table = Vec::with_capacity(32);
            let mut base = Jac { x: curve.gx, y: curve.gy, z: U256::from(1) };
            for _ in 0..32 {
                let mut row = [(U256::ZERO, U256::ZERO); 256];
                let mut acc = Jac::inf();
                for d in 1..256 {
                    acc = add_mixed(&acc, to_affine(&base, m).0, to_affine(&base, m).1, m);
                    row[d] = to_affine(&acc, m);
                }
                table.push(row);
                for _ in 0..8 {
                    base = double(&base, m);
                }
            }
            Comb { m, table }
        })
    }

    /// k * G, matching `WeierstrassEllipticCurve::mul(gx, gy, k)` exactly.
    pub fn mul_g(k: U256) -> (U256, U256) {
        let c = comb();
        let bytes: [u8; 32] = k.to_le_bytes();
        let mut acc = Jac::inf();
        for (w, &b) in bytes.iter().enumerate() {
            if b != 0 {
                let (qx, qy) = c.table[w][b as usize];
                acc = add_mixed(&acc, qx, qy, c.m);
            }
        }
        to_affine(&acc, c.m)
    }

    /// Prove the fast path against the reference on random scalars.
    pub fn verify_against_reference(n: usize) {
        use sha3::{
            digest::{ExtendableOutput, Update, XofReader},
            Shake256,
        };
        let curve = crate::point_add::secp256k1_curve();
        let mut h = Shake256::default();
        h.update(b"grind-fastec-selftest");
        let mut xof = h.finalize_xof();
        for i in 0..n {
            let mut rb = [0u8; 32];
            xof.read(&mut rb);
            let k = U256::from_le_bytes(rb);
            let want = curve.mul(curve.gx, curve.gy, k);
            let got = mul_g(k);
            assert!(got == want, "fastec::mul_g disagrees with curve.mul at sample {i}");
        }
        // Small scalars exercise the infinity / carry edges the random draw misses.
        for k in 0u64..64 {
            let k = U256::from(k);
            assert!(
                mul_g(k) == curve.mul(curve.gx, curve.gy, k),
                "fastec::mul_g disagrees with curve.mul at k={k}"
            );
        }
    }
}

/// The harness's raw input draw: `NUM_TESTS` 64-byte reads, kept unexpanded.
///
/// The XOF is consumed for all `NUM_TESTS` iterations whether or not a draw is kept,
/// so the simulator's own randomness starts at a fixed offset regardless of rejections.
/// See `notes/04-traps.md` #4: drawing lazily from the *shared stream* silently
/// desynchronises the simulator and reports a false `classical=0`. Reading every byte
/// up front and only deferring the curve arithmetic keeps that alignment exact.
struct Inputs {
    raw: Vec<u8>,
    targets: Vec<(U256, U256)>,
    offsets: Vec<(U256, U256)>,
    expected: Vec<(U256, U256)>,
    /// Draws already turned into curve points; `NUM_TESTS` once the draw is complete.
    scanned: usize,
}

impl Inputs {
    /// Expand the raw draw into curve points until `want` shots are available (or the
    /// draw is exhausted). A search trial rejects a nonce after ~7.6 of 141 batches, so
    /// expanding all 9024 up front doubles the cost of the whole grind for nothing.
    fn ensure(&mut self, want: usize) {
        let curve = crate::point_add::secp256k1_curve();
        while self.targets.len() < want && self.scanned < NUM_TESTS {
            let i = self.scanned;
            self.scanned += 1;
            let k1 =
                U256::from_le_bytes(<[u8; 32]>::try_from(&self.raw[i * 64..i * 64 + 32]).unwrap());
            let k2 = U256::from_le_bytes(
                <[u8; 32]>::try_from(&self.raw[i * 64 + 32..i * 64 + 64]).unwrap(),
            );
            let t = fastec::mul_g(k1);
            let o = fastec::mul_g(k2);
            if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) {
                continue;
            }
            self.expected.push(curve.add(t.0, t.1, o.0, o.1));
            self.targets.push(t);
            self.offsets.push(o);
        }
    }
}

fn draw_inputs(xof: &mut sha3::Shake256Reader, want_shots: usize) -> Inputs {
    let mut raw = vec![0u8; NUM_TESTS * 64];
    XofReader::read(xof, &mut raw);
    let mut inp = Inputs {
        raw,
        targets: Vec::with_capacity(NUM_TESTS),
        offsets: Vec::with_capacity(NUM_TESTS),
        expected: Vec::with_capacity(NUM_TESTS),
        scanned: 0,
    };
    inp.ensure(want_shots.min(NUM_TESTS));
    inp
}

fn set_register(reg: &[QubitOrBit], qubits: &mut [u64], bits: &mut [u64], val: U256, shot: usize) {
    for (i, item) in reg.iter().enumerate() {
        let on = val.bit(i);
        match item {
            QubitOrBit::Qubit(id) => {
                let w = &mut qubits[id.0 as usize];
                if on { *w |= 1 << shot } else { *w &= !(1 << shot) }
            }
            QubitOrBit::Bit(id) => {
                let w = &mut bits[id.0 as usize];
                if on { *w |= 1 << shot } else { *w &= !(1 << shot) }
            }
        }
    }
}

fn get_register(reg: &[QubitOrBit], qubits: &[u64], bits: &[u64], shot: usize) -> U256 {
    let mut v = U256::ZERO;
    for (i, item) in reg.iter().enumerate() {
        let b = match item {
            QubitOrBit::Qubit(id) => (qubits[id.0 as usize] >> shot) & 1,
            QubitOrBit::Bit(id) => (bits[id.0 as usize] >> shot) & 1,
        };
        v.set_bit(i, b != 0);
    }
    v
}

/// Faithful mirror of `Simulator::apply_iter`, returning executed Toffoli for the batch.
///
/// Verified against the frozen `crate::sim::Simulator` by `verify_mirror` on every run.
fn apply(
    ops: &[Op],
    qubits: &mut [u64],
    bits: &mut [u64],
    xof: &mut impl XofReader,
) -> (u64, u64) {
    let mut phase = 0u64;
    let mut stack: Vec<u64> = Vec::new();
    let mut base = u64::MAX;
    let mut toffoli = 0u64;

    for op in ops {
        let mut cond = base;
        if op.c_condition != NO_BIT {
            cond &= bits[op.c_condition.0 as usize];
        }
        match op.kind {
            OperationType::CCX => {
                // The scorer charges on the condition alone, before ever looking at
                // the control values (sim.rs:82) -- a gate that never fires still costs.
                toffoli += cond.count_ones() as u64;
                let v = cond & qubits[op.q_control1.0 as usize] & qubits[op.q_control2.0 as usize];
                qubits[op.q_target.0 as usize] ^= v;
            }
            OperationType::CCZ => {
                toffoli += cond.count_ones() as u64;
                phase ^= cond
                    & qubits[op.q_target.0 as usize]
                    & qubits[op.q_control1.0 as usize]
                    & qubits[op.q_control2.0 as usize];
            }
            OperationType::CX => {
                let v = cond & qubits[op.q_control1.0 as usize];
                qubits[op.q_target.0 as usize] ^= v;
            }
            OperationType::Swap => {
                let mut a = qubits[op.q_control1.0 as usize];
                let mut t = qubits[op.q_target.0 as usize];
                a ^= t;
                t ^= cond & a;
                a ^= t;
                qubits[op.q_control1.0 as usize] = a;
                qubits[op.q_target.0 as usize] = t;
            }
            OperationType::X => qubits[op.q_target.0 as usize] ^= cond,
            OperationType::CZ => {
                phase ^=
                    cond & qubits[op.q_target.0 as usize] & qubits[op.q_control1.0 as usize];
            }
            OperationType::Z => phase ^= cond & qubits[op.q_target.0 as usize],
            OperationType::Neg => phase ^= cond,
            OperationType::Hmr | OperationType::R => {
                let mut buf = [0u8; 8];
                xof.read(&mut buf);
                let rng = u64::from_le_bytes(buf);
                if op.kind == OperationType::Hmr {
                    bits[op.c_target.0 as usize] &= !cond;
                    bits[op.c_target.0 as usize] ^= rng & cond;
                }
                phase ^= qubits[op.q_target.0 as usize] & rng & cond;
                qubits[op.q_target.0 as usize] &= !cond;
            }
            OperationType::BitInvert => bits[op.c_target.0 as usize] ^= cond,
            OperationType::BitStore0 => bits[op.c_target.0 as usize] &= !cond,
            OperationType::BitStore1 => bits[op.c_target.0 as usize] |= cond,
            OperationType::AppendToRegister
            | OperationType::Register
            | OperationType::DebugPrint => {}
            OperationType::PushCondition => {
                stack.push(base);
                base &= bits[op.c_condition.0 as usize];
            }
            OperationType::PopCondition => {
                if let Some(v) = stack.pop() {
                    base = v;
                }
            }
        }
    }
    (phase, toffoli)
}

/// Result of screening one candidate nonce.
#[derive(Default, Clone, Copy)]
struct Trial {
    batches_run: u32,
    batches_clean: u32,
    classical_shots: u32,
    phase_batches: u32,
    ancilla_batches: u32,
    toffoli: u64,
    shots: u32,
    passed: bool,
    /// Batches rejected by exactly one channel, and by both. The marginals cannot be
    /// added: a divstep truncation typically corrupts a value AND dirties an ancilla,
    /// and it is the batch-level UNION that sets P(clean run). Splitting them says how
    /// much lambda a fix aimed at one channel could actually remove.
    bad_classical_only: u32,
    bad_phase_only: u32,
    bad_both: u32,
}

/// Screen one nonce along the harness path.
///
/// `early_abort` stops at the first batch the harness would reject on, which is all a
/// search needs; lambda estimation must see every batch.
fn trial(
    ops: &[Op],
    regs: &[Vec<QubitOrBit>],
    num_q: usize,
    num_b: usize,
    prefix: &SeedPrefix,
    nonce: u64,
    early_abort: bool,
    max_batches: usize,
) -> Trial {
    let mut xof = prefix.xof_for(nonce);
    // Curve points are expanded per batch, not up front: the XOF is still consumed in
    // full inside `draw_inputs` (so the simulator's randomness stays aligned), but an
    // early-aborting search touches ~7.6 of 141 batches and must not pay for the rest.
    let mut inp = draw_inputs(&mut xof, BATCH);

    let mut out = Trial { passed: true, ..Default::default() };

    let mut qubits = vec![0u64; num_q];
    let mut bits = vec![0u64; num_b];

    let mut batch = 0usize;
    while batch < max_batches {
        inp.ensure((batch + 1) * BATCH);
        let n = inp.targets.len();
        if n <= batch * BATCH {
            break;
        }
        let bs = BATCH.min(n - batch * BATCH);
        let cond_mask: u64 = if bs == 64 { u64::MAX } else { (1u64 << bs) - 1 };

        qubits.iter_mut().for_each(|e| *e = 0);
        bits.iter_mut().for_each(|e| *e = 0);
        for shot in 0..bs {
            let i = batch * BATCH + shot;
            set_register(&regs[0], &mut qubits, &mut bits, inp.targets[i].0, shot);
            set_register(&regs[1], &mut qubits, &mut bits, inp.targets[i].1, shot);
            set_register(&regs[2], &mut qubits, &mut bits, inp.offsets[i].0, shot);
            set_register(&regs[3], &mut qubits, &mut bits, inp.offsets[i].1, shot);
        }

        let (phase, tof) = apply(ops, &mut qubits, &mut bits, &mut xof);
        out.toffoli += tof;
        out.batches_run += 1;

        let mut dirty = false;
        let mut classical = 0u32;
        for shot in 0..bs {
            let i = batch * BATCH + shot;
            let gx = get_register(&regs[0], &qubits, &bits, shot);
            let gy = get_register(&regs[1], &qubits, &bits, shot);
            if (gx, gy) != inp.expected[i] {
                classical += 1;
            }
        }
        out.classical_shots += classical;
        let bad_c = classical > 0;
        let bad_p = phase & cond_mask != 0;
        if bad_c {
            dirty = true;
        }
        if bad_p {
            out.phase_batches += 1;
            dirty = true;
        }
        match (bad_c, bad_p) {
            (true, true) => out.bad_both += 1,
            (true, false) => out.bad_classical_only += 1,
            (false, true) => out.bad_phase_only += 1,
            (false, false) => {}
        }

        // Registers are exempt from the ancilla check; everything else must be |0>.
        for reg in regs {
            for qb in reg {
                if let QubitOrBit::Qubit(q) = *qb {
                    qubits[q.0 as usize] = 0;
                }
            }
        }
        if qubits.iter().any(|&v| v & cond_mask != 0) {
            out.ancilla_batches += 1;
            dirty = true;
        }

        if dirty {
            out.passed = false;
            if early_abort {
                out.shots = inp.targets.len() as u32;
                return out;
            }
        } else {
            out.batches_clean += 1;
        }
        batch += 1;
    }
    out.shots = inp.targets.len() as u32;
    out
}

/// Prove the mirror against the frozen simulator on the real harness seed.
///
/// Without this the whole rig is an assumption; `notes/04` #4 is a case of exactly
/// this class of bug reporting a false clean.
fn verify_mirror(ops: &[Op], regs: &[Vec<QubitOrBit>], num_q: usize, num_b: usize, prefix: &SeedPrefix, nonce: u64) {
    use crate::sim::Simulator;

    // Reference: the frozen simulator, seeded exactly as eval_circuit does.
    let mut ref_xof = prefix.xof_for(nonce);
    let inp = draw_inputs(&mut ref_xof, BATCH);
    let mut sim = Simulator::new(num_q, num_b, &mut ref_xof);
    for shot in 0..BATCH {
        sim.set_register(&regs[0], inp.targets[shot].0, shot);
        sim.set_register(&regs[1], inp.targets[shot].1, shot);
        sim.set_register(&regs[2], inp.offsets[shot].0, shot);
        sim.set_register(&regs[3], inp.offsets[shot].1, shot);
    }
    sim.apply_iter(ops.iter());
    let ref_tof = sim.stats.toffoli_gates;
    let (ref_q, ref_b, ref_phase) = (sim.qubits.clone(), sim.bits.clone(), sim.phase);
    drop(sim);

    // Mirror: this file's own loop, same seed.
    let mut xof = prefix.xof_for(nonce);
    let inp2 = draw_inputs(&mut xof, BATCH);
    assert!(
        inp2.targets == inp.targets && inp2.expected == inp.expected,
        "grind: input draw is not reproducible"
    );
    let mut qubits = vec![0u64; num_q];
    let mut bits = vec![0u64; num_b];
    for shot in 0..BATCH {
        set_register(&regs[0], &mut qubits, &mut bits, inp.targets[shot].0, shot);
        set_register(&regs[1], &mut qubits, &mut bits, inp.targets[shot].1, shot);
        set_register(&regs[2], &mut qubits, &mut bits, inp.offsets[shot].0, shot);
        set_register(&regs[3], &mut qubits, &mut bits, inp.offsets[shot].1, shot);
    }
    let (phase, tof) = apply(ops, &mut qubits, &mut bits, &mut xof);

    assert!(
        qubits == ref_q && bits == ref_b && phase == ref_phase && tof == ref_tof,
        "grind mirror diverged from crate::sim::Simulator (phase {:#x} vs {:#x}, tof {} vs {})",
        phase, ref_phase, tof, ref_tof
    );
    eprintln!("GRIND mirror_check -> FAITHFUL (qubits, bits, phase, toffoli agree at nonce {nonce})");
}

pub(crate) fn run(ops: &[Op]) {
    let mode = std::env::var("TLM_GRIND_MODE").unwrap_or_else(|_| "lambda".to_string());
    let nonces = env_u64("TLM_GRIND_NONCES", 16);
    let start = env_u64("TLM_GRIND_START", 0);
    let threads = env_usize(
        "TLM_GRIND_THREADS",
        std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4),
    );
    let max_batches = env_usize("TLM_GRIND_BATCHES", usize::MAX);

    let (num_q, num_b, _nregs, regs) = analyze_ops(ops.iter());
    let (num_q, num_b) = (num_q as usize, num_b as usize);

    eprintln!(
        "GRIND start: mode={mode} ops={} qubits={num_q} bits={num_b} nonces={nonces} start={start} threads={threads}",
        ops.len()
    );

    fastec::verify_against_reference(512);
    eprintln!("GRIND fastec_check -> FAITHFUL (512 random + 64 small scalars match curve.mul)");

    let t0 = std::time::Instant::now();
    let prefix = SeedPrefix::new(ops);
    eprintln!("GRIND seed prefix absorbed in {:.2}s (per-nonce hashing is now {} ops)", t0.elapsed().as_secs_f64(), TAIL_OPS);

    verify_mirror(ops, &regs, num_q, num_b, &prefix, start);

    let early = mode == "search";
    let done = AtomicBool::new(false);
    let tried = AtomicU64::new(0);
    let hit = AtomicU64::new(u64::MAX);

    // Aggregates for the lambda estimate.
    let agg_batches = AtomicU64::new(0);
    let agg_clean = AtomicU64::new(0);
    let agg_classical = AtomicU64::new(0);
    let agg_phase = AtomicU64::new(0);
    let agg_ancilla = AtomicU64::new(0);
    let agg_toffoli = AtomicU64::new(0);
    let agg_shots = AtomicU64::new(0);
    let agg_pass = AtomicU64::new(0);
    let agg_conly = AtomicU64::new(0);
    let agg_ponly = AtomicU64::new(0);
    let agg_both = AtomicU64::new(0);

    let t1 = std::time::Instant::now();
    std::thread::scope(|scope| {
        for t in 0..threads {
            let (prefix, regs, done, tried, hit) = (&prefix, &regs, &done, &tried, &hit);
            let (agg_batches, agg_clean, agg_classical, agg_phase, agg_ancilla, agg_toffoli, agg_shots, agg_pass) = (
                &agg_batches, &agg_clean, &agg_classical, &agg_phase, &agg_ancilla, &agg_toffoli, &agg_shots, &agg_pass,
            );
            let (agg_conly, agg_ponly, agg_both) = (&agg_conly, &agg_ponly, &agg_both);
            scope.spawn(move || {
                let mut k = t as u64;
                while k < nonces {
                    if done.load(Ordering::Relaxed) {
                        return;
                    }
                    let nonce = start.wrapping_add(k);
                    let r = trial(ops, regs, num_q, num_b, prefix, nonce, early, max_batches);

                    agg_batches.fetch_add(r.batches_run as u64, Ordering::Relaxed);
                    agg_clean.fetch_add(r.batches_clean as u64, Ordering::Relaxed);
                    agg_classical.fetch_add(r.classical_shots as u64, Ordering::Relaxed);
                    agg_phase.fetch_add(r.phase_batches as u64, Ordering::Relaxed);
                    agg_ancilla.fetch_add(r.ancilla_batches as u64, Ordering::Relaxed);
                    agg_conly.fetch_add(r.bad_classical_only as u64, Ordering::Relaxed);
                    agg_ponly.fetch_add(r.bad_phase_only as u64, Ordering::Relaxed);
                    agg_both.fetch_add(r.bad_both as u64, Ordering::Relaxed);
                    agg_toffoli.fetch_add(r.toffoli, Ordering::Relaxed);
                    agg_shots.fetch_add(r.shots as u64, Ordering::Relaxed);
                    let n = tried.fetch_add(1, Ordering::Relaxed) + 1;

                    if r.passed && r.batches_run as usize == (r.shots as usize).div_ceil(BATCH) {
                        agg_pass.fetch_add(1, Ordering::Relaxed);
                        eprintln!(
                            "GRIND *** CLEAN NONCE {nonce} *** shots={} avg_toffoli={:.3}",
                            r.shots,
                            r.toffoli as f64 / r.shots.max(1) as f64
                        );
                        hit.store(nonce, Ordering::Relaxed);
                        if early {
                            done.store(true, Ordering::Relaxed);
                            return;
                        }
                    }
                    if !early {
                        eprintln!(
                            "GRIND nonce={nonce} batches={}/{} clean classical={} phase={} ancilla={} avgT={:.3}",
                            r.batches_clean, r.batches_run, r.classical_shots, r.phase_batches, r.ancilla_batches,
                            r.toffoli as f64 / r.shots.max(1) as f64
                        );
                    } else if n % 500 == 0 {
                        eprintln!(
                            "GRIND progress: {n} nonces, {:.1}/s",
                            n as f64 / t1.elapsed().as_secs_f64()
                        );
                    }
                    k += threads as u64;
                }
            });
        }
    });

    let secs = t1.elapsed().as_secs_f64();
    let nb = agg_batches.load(Ordering::Relaxed).max(1);
    let nc = agg_clean.load(Ordering::Relaxed);
    let n_tried = tried.load(Ordering::Relaxed).max(1);
    let p_batch = nc as f64 / nb as f64;
    let batches_per_run = (NUM_TESTS as f64 / BATCH as f64).ceil();
    let lambda = -batches_per_run * p_batch.max(1e-12).ln();

    eprintln!("\n=== GRIND summary ===");
    eprintln!("  nonces tried        : {n_tried} in {secs:.1}s ({:.2}/s, {:.2} nonce-s/core)", n_tried as f64 / secs, secs * threads as f64 / n_tried as f64);
    eprintln!("  batches run         : {nb} ({} clean, p_clean={:.5})", nc, p_batch);
    eprintln!("  classical fail shots: {}", agg_classical.load(Ordering::Relaxed));
    eprintln!("  phase-bad batches   : {}", agg_phase.load(Ordering::Relaxed));
    eprintln!("  ancilla-bad batches : {}", agg_ancilla.load(Ordering::Relaxed));
    if !early {
        eprintln!("  mean classical/run  : {:.2}", agg_classical.load(Ordering::Relaxed) as f64 / n_tried as f64);
        eprintln!("  mean phase-bat/run  : {:.2}", agg_phase.load(Ordering::Relaxed) as f64 / n_tried as f64);
        let shots = agg_shots.load(Ordering::Relaxed).max(1);
        eprintln!("  avg executed Toffoli: {:.3}", agg_toffoli.load(Ordering::Relaxed) as f64 / shots as f64);
    }
    // What each channel is worth: lambda if that channel's exclusive batches were fixed.
    let (co, po, bo) = (
        agg_conly.load(Ordering::Relaxed),
        agg_ponly.load(Ordering::Relaxed),
        agg_both.load(Ordering::Relaxed),
    );
    let lam_of = |clean: u64| -batches_per_run * (clean as f64 / nb as f64).max(1e-12).ln();
    eprintln!("  bad batches         : classical-only={co} phase-only={po} both={bo}");
    eprintln!(
        "  lambda if phase fixed  : {:.2}   (removes the phase-only batches)",
        lam_of(nc + po)
    );
    eprintln!(
        "  lambda if classical fixed: {:.2} (removes the classical-only batches)",
        lam_of(nc + co)
    );
    eprintln!("  LAMBDA (per run)    : {lambda:.2}   P(clean run) = {:.3e}", (-lambda).exp());
    eprintln!("  expected nonces/ship: {:.3e}", lambda.exp());
    eprintln!("  clean nonces found  : {}", agg_pass.load(Ordering::Relaxed));
    let h = hit.load(Ordering::Relaxed);
    if h != u64::MAX {
        eprintln!("  >>> USE SUB4_TAIL_NONCE={h}");
    }
}
