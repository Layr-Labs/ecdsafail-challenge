//! Gate-level selftests of the Skywalk tail: `MIDQ_SKY_TAIL_SELFTEST=1 build_circuit` (the
//! production recipe is installed first, so the cells, codecs and caps are the built ones).
//!
//! 1. codec: all 243 five-letter words through pack3+pack5 and back (injective 8-wire code,
//!    exact letters, zero phase, every other wire zero).
//! 2. rails: every (u, v) with v odd, gcd 1 and u + v < 2^(K-1) (K = MIDQ_SKY_SELFTEST_RAIL_BITS,
//!    default 11) walked forward at its exact envelope table (widths shrink with the envelope),
//!    parked checked, then walked back: rails restored, tape consumed, zero phase and garbage.
//! 3. tail: N real handoff states (MIDQ_SKY_SELFTEST_N, default 4096) of the classical PZ prefix
//!    at the built cut, loaded into registers of the circuit's own handoff widths; the whole
//!    sky tail forward (handoff, R ticks with cells and routes, codec, endpoint) and backward.
//!    Checks: Sig == |x|^-1 at the endpoint; A, B, ca, cb, q, parity, counter and a random
//!    passenger pad restored exactly; zero phase; every other wire zero. Inputs the table model
//!    calls misses (width above esw(t) or T > R) are run and reported separately.

use super::*;
use crate::circuit::Op;
use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
use crate::sim::Simulator;
use ruint::Uint;
use sha3::{digest::{ExtendableOutput, Update}, Shake256};

type U512 = Uint<512, 8>;

fn secp_p() -> U512 {
    (U512::from(1u64) << 256) - (U512::from(1u64) << 32) - U512::from(977u64)
}

fn bl(x: U512) -> usize {
    if x.is_zero() { 0 } else { 512 - x.leading_zeros() }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn field(&mut self, p: U512) -> U512 {
        loop {
            let x = U512::from_limbs([self.next(), self.next(), self.next(), self.next(), 0, 0, 0, 0]);
            if !x.is_zero() && x < p {
                return x;
            }
        }
    }
}

fn threads() -> usize {
    env_usize("MIDQ_SKY_SELFTEST_THREADS", 6).max(1)
}

fn new_sim<'a>(nq: usize, nb: usize, xof: &'a mut sha3::Shake256Reader) -> Simulator<'a, sha3::Shake256Reader> {
    Simulator::new(nq, nb, xof)
}

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = Shake256::default();
    h.update(b"midq-sky-tail-selftest-v1");
    h.update(tag);
    h.finalize_xof()
}

fn set_bits(sim: &mut Simulator<'_, sha3::Shake256Reader>, ids: &[u32], value: U512, shot: usize) {
    for (i, &id) in ids.iter().enumerate() {
        let q = sim.qubit_mut(QubitId(id.into()));
        if value.bit(i) { *q |= 1u64 << shot; } else { *q &= !(1u64 << shot); }
    }
}

fn get_bits(sim: &Simulator<'_, sha3::Shake256Reader>, ids: &[u32], shot: usize) -> U512 {
    let mut v = U512::ZERO;
    for (i, &id) in ids.iter().enumerate() {
        if (sim.qubit(QubitId(id.into())) >> shot) & 1 == 1 {
            v.set_bit(i, true);
        }
    }
    v
}

/// Two's complement of a signed value in `w` bits.
fn twos(v: i128, w: usize) -> U512 {
    let m = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
    U512::from((v as u128) & m)
}

fn signed_of(v: U512, w: usize) -> i128 {
    let raw = v.as_limbs()[0] as u128 | ((v.as_limbs()[1] as u128) << 64);
    let raw = if w >= 128 { raw } else { raw & ((1u128 << w) - 1) };
    if w < 128 && (raw >> (w - 1)) & 1 == 1 { (raw as i128) - (1i128 << w) } else { raw as i128 }
}

fn ids(reg: &[QReg]) -> Vec<u32> {
    reg.iter().map(|q| q.id()).collect()
}

fn assert_counting_circuit(c: &Circuit) {
    assert!(!c.b.count_only, "MIDQ_SKY_TAIL_SELFTEST needs op storage: unset POINT_ADD_COUNT_ONLY");
}

// ─── 1. codec ──────────────────────────────────────────────────────────────────────────────

fn codec_exhaustive() -> usize {
    let mut c = Circuit::new();
    assert_counting_circuit(&c);
    let mut tape = Tape::new(5);
    let mut in_ids = Vec::new();
    for t in 0..5 {
        let typ = c.alloc_qreg(&format!("test.typ[{t}]"));
        let s = c.alloc_qreg(&format!("test.s[{t}]"));
        in_ids.push((typ.id(), s.id()));
        tape.push(t, typ, s);
    }
    tape.pack(&mut c, 0);
    c.flush_pending_frees();
    assert_eq!(c.b.active_qubits, 8, "five letters pack into eight wires");
    let mid = c.b.ops.len();
    let packed = ids(tape.groups[0].as_ref().unwrap());
    tape.unpack(&mut c, 0);
    let out_ids: Vec<(u32, u32)> = (0..5).map(|t| { let (a, b) = tape.letter(t); (a.id(), b.id()) }).collect();
    c.flush_pending_frees();
    let nq = c.b.next_qubit as usize;
    let nb = c.b.next_bit as usize + 1;
    let ops = &c.b.ops;
    let pack_t = ops[..mid].iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count();
    let unpack_t = ops[mid..].iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count();
    let mut seen = std::collections::BTreeSet::new();
    let mut rng = xof(b"codec");
    let mut sim = new_sim(nq, nb, &mut rng);
    let letter = |d: usize| if d == 2 { (1u64, 0u64) } else { (0, d as u64) };
    let mut checked = 0;
    for first in (0..243usize).step_by(64) {
        let valid = 64.min(243 - first);
        let active = if valid == 64 { u64::MAX } else { (1u64 << valid) - 1 };
        sim.clear_for_shot();
        for shot in 0..valid {
            let mut w = first + shot;
            for t in 0..5 {
                let (ty, s) = letter(w % 3);
                w /= 3;
                *sim.qubit_mut(QubitId(in_ids[t].0.into())) |= ty << shot;
                *sim.qubit_mut(QubitId(in_ids[t].1.into())) |= s << shot;
            }
        }
        sim.apply_iter(ops[..mid].iter());
        for shot in 0..valid {
            let v = get_bits(&sim, &packed, shot);
            assert!(seen.insert(v), "codec collision at word {}", first + shot);
            for id in 0..nq as u32 {
                if !packed.contains(&id) {
                    assert_eq!((sim.qubit(QubitId(id.into())) >> shot) & 1, 0, "codec pack garbage");
                }
            }
        }
        sim.apply_iter(ops[mid..].iter());
        assert_eq!(sim.phase & active, 0, "codec phase");
        for shot in 0..valid {
            let mut w = first + shot;
            let mut expect = std::collections::BTreeMap::new();
            for t in 0..5 {
                let (ty, s) = letter(w % 3);
                w /= 3;
                expect.insert(out_ids[t].0, ty);
                expect.insert(out_ids[t].1, s);
            }
            for id in 0..nq as u32 {
                let bit = (sim.qubit(QubitId(id.into())) >> shot) & 1;
                assert_eq!(bit, *expect.get(&id).unwrap_or(&0), "codec roundtrip word {} wire {id}", first + shot);
            }
            checked += 1;
        }
    }
    assert_eq!(seen.len(), 243);
    eprintln!("SKY_CODEC_SELFTEST PASS: 243/243 words, injective 8-wire code, exact unpack, zero phase and garbage; pack {pack_t} + unpack {unpack_t} Toffoli per group");
    checked
}

// ─── 2. rails (exhaustive at small width) ──────────────────────────────────────────────────

fn walk_model(mut u: u64, mut v: u64, widths: &mut Vec<usize>) -> usize {
    let mut t = 0;
    while u != 0 {
        let w = 64 - (u + v).leading_zeros() as usize + 1;
        if widths.len() <= t { widths.push(0); }
        widths[t] = widths[t].max(w);
        if u & 1 == 0 { u >>= 1usize; } else if u > v { u = (u - v) >> 1; } else { let nu = (v - u) >> 1; v = u; u = nu; }
        t += 1;
    }
    t
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 { let t = a % b; a = b; b = t; }
    a
}

fn rails_exhaustive() -> usize {
    let k = env_usize("MIDQ_SKY_SELFTEST_RAIL_BITS", 11);
    let lim = 1u64 << (k - 1);
    let mut inputs = Vec::new();
    let mut env: Vec<usize> = Vec::new();
    let mut max_t = 0;
    for v in (1..lim).step_by(2) {
        for u in 0..lim - v {
            if gcd(u, v) != 1 { continue; }
            max_t = max_t.max(walk_model(u, v, &mut env));
            inputs.push((u, v));
        }
    }
    let r = max_t;
    let mut esw: Vec<usize> = (0..r).map(|t| env.get(t).copied().unwrap_or(2).max(2)).collect();
    for t in (0..r.saturating_sub(1)).rev() {
        esw[t] = esw[t].max(esw[t + 1]);
    }
    esw.push(2);
    let mut c = Circuit::new();
    assert_counting_circuit(&c);
    let mut r1 = c.alloc_qreg_bits("test.r1", esw[0]);
    let mut r2 = c.alloc_qreg_bits("test.r2", esw[0]);
    let in1 = ids(&r1);
    let in2 = ids(&r2);
    let mut tape = Tape::new(r);
    walk_forward(&mut c, &mut r1, &mut r2, &mut tape, &esw, None);
    let mid = c.b.ops.len();
    let (m1, m2) = (ids(&r1), ids(&r2));
    walk_backward(&mut c, &mut r1, &mut r2, &mut tape, &esw, None);
    assert!(tape.is_empty());
    let (o1, o2) = (ids(&r1), ids(&r2));
    c.flush_pending_frees();
    assert_eq!(c.b.active_qubits as usize, 2 * esw[0], "rail walk leaks wires");
    let nq = c.b.next_qubit as usize;
    let nb = c.b.next_bit as usize + 1;
    let ops = &c.b.ops;
    let batches: Vec<&[(u64, u64)]> = inputs.chunks(64).collect();
    let failures = std::sync::atomic::AtomicUsize::new(0);
    let nt = threads();
    std::thread::scope(|s| {
        for tid in 0..nt {
            let batches = &batches;
            let failures = &failures;
            let (esw, in1, in2, m1, m2, o1, o2) = (&esw, &in1, &in2, &m1, &m2, &o1, &o2);
            s.spawn(move || {
                let mut rng = xof(format!("rails{tid}").as_bytes());
                let mut sim = new_sim(nq, nb, &mut rng);
                for batch in batches.iter().skip(tid).step_by(nt) {
                    sim.clear_for_shot();
                    let active = if batch.len() == 64 { u64::MAX } else { (1u64 << batch.len()) - 1 };
                    for (shot, &(u, v)) in batch.iter().enumerate() {
                        set_bits(&mut sim, in1, twos((u + v) as i128, esw[0]), shot);
                        set_bits(&mut sim, in2, twos(u as i128, esw[0]), shot);
                    }
                    sim.apply_iter(ops[..mid].iter());
                    for (shot, _) in batch.iter().enumerate() {
                        let a = signed_of(get_bits(&sim, m1, shot), 2);
                        let b = signed_of(get_bits(&sim, m2, shot), 2);
                        if !matches!((a.abs(), b.abs()), (1, 0) | (0, 1)) {
                            failures.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                    }
                    sim.apply_iter(ops[mid..].iter());
                    if sim.phase & active != 0 {
                        failures.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                    for (shot, &(u, v)) in batch.iter().enumerate() {
                        let ok1 = get_bits(&sim, o1, shot) == twos((u + v) as i128, esw[0]);
                        let ok2 = get_bits(&sim, o2, shot) == twos(u as i128, esw[0]);
                        let clean = (0..nq as u32).filter(|id| !o1.contains(id) && !o2.contains(id))
                            .all(|id| (sim.qubit(QubitId(id.into())) >> shot) & 1 == 0);
                        if !(ok1 && ok2 && clean) {
                            failures.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                    }
                }
            });
        }
    });
    let f = failures.into_inner();
    assert_eq!(f, 0, "SKY_RAIL_SELFTEST: {f} failures");
    eprintln!("SKY_RAIL_SELFTEST PASS: {} inputs (all v odd, gcd 1, u+v < 2^{}), R={r} ticks, esw0={}, parked at R, exact reverse, zero phase and garbage",
        inputs.len(), k - 1, esw[0]);
    inputs.len()
}

// ─── 3. whole tail on real handoff states ──────────────────────────────────────────────────

struct Handoff {
    x: U512,
    a: U512,
    b: U512,
    ca: U512,
    cb: U512,
    q: u128,
    parity: bool,
}

/// The exact PZ prefix (record_sample / pz_prefix) to `cut`, with the parity bit. None if the
/// EEA reached its terminal state before or at the cut (the no-terminal prefix mishandles it),
/// unless MIDQ_SKY_SELFTEST_TERMINAL=1: then the held terminal state (0, 1, p, v, 0) is the
/// handoff (what a terminal-aware prefix would hand over), to exercise the tail's A == 0 map.
fn pz_handoff(x_orig: U512, cut: usize) -> Option<Handoff> {
    let keep_terminal = std::env::var("MIDQ_SKY_SELFTEST_TERMINAL").ok().as_deref() == Some("1");
    let p = secp_p();
    let x = if x_orig > (p >> 1) { p - x_orig } else { x_orig };
    let one = U512::from(1u64);
    let (mut a, mut b, mut ca, mut cb, mut q, mut parity) = (p, x, U512::ZERO, one, 0u128, true);
    for _ in 0..cut {
        if a.is_zero() && q == 0 {
            if keep_terminal {
                break;
            }
            return None;
        }
        if a < b && q != 0 {
            let s2 = q.trailing_zeros() as usize;
            q ^= 1u128 << s2;
            ca += cb << s2;
        }
        if ca < cb {
            let mut s = bl(a) as i64 - bl(b) as i64;
            if s >= 0 && a < (b << (s as usize)) {
                s -= 1;
            }
            if s >= 0 {
                let bsh = b << (s as usize);
                if a >= bsh {
                    a -= bsh;
                    q ^= 1u128 << s;
                }
            }
        }
        if q == 0 && !a.is_zero() {
            std::mem::swap(&mut a, &mut b);
            std::mem::swap(&mut ca, &mut cb);
            parity = !parity;
        }
    }
    if a.is_zero() && q == 0 && !keep_terminal {
        return None;
    }
    Some(Handoff { x, a, b, ca, cb, q, parity })
}

/// The table model: miss iff w(t) = bits(u+v)+1 > esw(t) for some t < T, or T > R.
fn table_miss(h: &Handoff, esw: &[usize]) -> bool {
    let (mut u, mut v) = if h.a.is_zero() { (U512::from(1u64), U512::from(1u64)) } else { (h.a, h.b) };
    if !v.bit(0) {
        std::mem::swap(&mut u, &mut v);
    }
    let r = esw.len() - 1;
    for &w in esw.iter().take(r) {
        if u.is_zero() {
            return false;
        }
        if bl(u + v) + 1 > w {
            return true;
        }
        if !u.bit(0) { u >>= 1usize; } else if u > v { u = (u - v) >> 1; } else { let nu = (v - u) >> 1; v = u; u = nu; }
    }
    !u.is_zero()
}

#[derive(Default, Clone, Copy)]
struct Tally {
    clean: usize,
    clean_ok: usize,
    miss: usize,
    miss_ok: usize,
    a0: usize,
    term: usize,
    sel: usize,
    sig_bad: usize,
}

fn tail_roundtrips() -> Tally {
    let cut = midq_pz_cut();
    let (_, l, esw) = table();
    let r = esw.len() - 1;
    let n = env_usize("MIDQ_SKY_SELFTEST_N", 4096);
    let pad_n = env_usize("MIDQ_SKY_SELFTEST_PAD", 257);
    let (wa, wb, wca, wcb, wq) = reg_widths(cut - 1);
    let wab = trailmix_ab_width(wa.max(wb));
    let wcacb = trailmix_cacb_width(wca.max(wcb));
    let wqe = trailmix_q_width_step(wq, wa, wb, wca, wcb);
    let mut c = Circuit::new();
    assert_counting_circuit(&c);
    let pad = c.alloc_qreg_bits("test.passenger", pad_n);
    let mut a = c.alloc_qreg_bits("A", wab);
    let mut b = c.alloc_qreg_bits("B", wab);
    let mut ca = c.alloc_qreg_bits("ca", wcacb);
    let mut cb = c.alloc_qreg_bits("cb", wcacb);
    let mut q = c.alloc_qreg_bits("q", wqe);
    let mut counter = c.alloc_qreg_bits("ctr", counter_tape::BITS);
    let mut parity = Some(BorrowedQReg::Owned(c.alloc_qreg("par")));
    let inputs_ids = [ids(&a), ids(&b), ids(&ca), ids(&cb), ids(&q)];
    let par_in = parity.as_deref().unwrap().id();
    let pad_ids = ids(&pad);
    c.flush_pending_frees();
    let entry_active = c.b.active_qubits;
    let state = forward(&mut c, &mut a, &mut b, &mut ca, &mut cb, &mut q, &mut counter, &mut parity);
    let mid = c.b.ops.len();
    let sig_ids = ids(&ca);
    assert!(cb.is_empty() && counter.is_empty());
    backward(&mut c, &mut a, &mut b, &mut ca, &mut cb, &mut q, &mut counter, &mut parity, state);
    c.flush_pending_frees();
    let out_ids = [ids(&a), ids(&b), ids(&ca), ids(&cb), ids(&q)];
    let ctr_ids = ids(&counter);
    let par_out = parity.as_deref().unwrap().id();
    let mut keep: std::collections::BTreeSet<u32> = out_ids.iter().flatten().copied().collect();
    keep.extend(ctr_ids.iter().copied());
    keep.insert(par_out);
    keep.extend(pad_ids.iter().copied());
    assert_eq!(c.b.active_qubits, entry_active, "sky tail round trip leaks wires");
    let nq = c.b.next_qubit as usize;
    let nb = c.b.next_bit as usize + 1;
    let ops: &[Op] = &c.b.ops;
    let tof = ops.iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count();
    let tof_fwd = ops[..mid].iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count();
    eprintln!("SKY_TAIL_SELFTEST circuit: cut={cut} L={l} R={r} widths A/B={wab} ca/cb={wcacb} q={wqe} pad={pad_n} entry_active={entry_active} ops={} toffoli fwd={tof_fwd} bwd={}",
        ops.len(), tof - tof_fwd);

    // Inputs: real handoff states that fit the circuit's handoff registers.
    let p = secp_p();
    let mut rng = Rng(env_usize("MIDQ_SKY_SELFTEST_SEED", 71) as u64);
    let mut inputs: Vec<(Handoff, bool)> = Vec::with_capacity(n);
    let (mut skipped_terminal, mut skipped_fit) = (0usize, 0usize);
    while inputs.len() < n {
        let Some(h) = pz_handoff(rng.field(p), cut) else { skipped_terminal += 1; continue; };
        let fits = bl(h.a) <= wab && bl(h.b) <= wab && bl(h.ca) <= wcacb && bl(h.cb) <= wcacb
            && (128 - (h.q | 0).leading_zeros() as usize) <= wqe.min(midq_handoff_q_bits());
        if !fits {
            skipped_fit += 1;
            continue;
        }
        let miss = table_miss(&h, &esw);
        inputs.push((h, miss));
    }
    let batches: Vec<&[(Handoff, bool)]> = inputs.chunks(64).collect();
    let tally = std::sync::Mutex::new(Tally::default());
    let nt = threads();
    std::thread::scope(|s| {
        for tid in 0..nt {
            let (batches, tally, inputs_ids, out_ids, sig_ids, pad_ids, keep, ctr_ids) =
                (&batches, &tally, &inputs_ids, &out_ids, &sig_ids, &pad_ids, &keep, &ctr_ids);
            s.spawn(move || {
                let mut rng_x = xof(format!("tail{tid}").as_bytes());
                let mut sim = new_sim(nq, nb, &mut rng_x);
                let mut padrng = Rng(0x5eed + tid as u64);
                let mut local = Tally::default();
                for batch in batches.iter().skip(tid).step_by(nt) {
                    sim.clear_for_shot();
                    let mut pads = Vec::with_capacity(batch.len());
                    for (shot, (h, _)) in batch.iter().enumerate() {
                        let vals = [h.a, h.b, h.ca, h.cb, U512::from(h.q)];
                        for (reg, v) in inputs_ids.iter().zip(vals) {
                            set_bits(&mut sim, reg, v, shot);
                        }
                        if h.parity {
                            *sim.qubit_mut(QubitId(par_in.into())) |= 1u64 << shot;
                        }
                        let pv = U512::from_limbs([padrng.next(), padrng.next(), padrng.next(), padrng.next(),
                            padrng.next(), 0, 0, 0]) & ((U512::from(1u64) << pad_ids.len()) - U512::from(1u64));
                        set_bits(&mut sim, pad_ids, pv, shot);
                        pads.push(pv);
                    }
                    sim.apply_iter(ops[..mid].iter());
                    let mut sig_ok = [false; 64];
                    for (shot, (h, _)) in batch.iter().enumerate() {
                        let inv = h.x.inv_mod(p).expect("nonzero field element");
                        sig_ok[shot] = get_bits(&sim, sig_ids, shot) == inv;
                    }
                    let phase = sim.phase;
                    sim.apply_iter(ops[mid..].iter());
                    let phase = phase | sim.phase;
                    for (shot, (h, miss)) in batch.iter().enumerate() {
                        let vals = [h.a, h.b, h.ca, h.cb, U512::from(h.q)];
                        let restored = out_ids.iter().zip(vals).all(|(reg, v)| get_bits(&sim, reg, shot) == v)
                            && get_bits(&sim, ctr_ids, shot).is_zero()
                            && ((sim.qubit(QubitId(par_out.into())) >> shot) & 1 == 1) == h.parity
                            && get_bits(&sim, pad_ids, shot) == pads[shot];
                        let clean = (0..nq as u32).filter(|id| !keep.contains(id))
                            .all(|id| (sim.qubit(QubitId(id.into())) >> shot) & 1 == 0);
                        let ok = sig_ok[shot] && restored && clean && (phase >> shot) & 1 == 0;
                        if h.a.is_zero() { local.a0 += 1; if h.q == 0 { local.term += 1; } }
                        if !h.b.bit(0) && !h.a.is_zero() { local.sel += 1; }
                        if *miss {
                            local.miss += 1;
                            local.miss_ok += usize::from(ok);
                        } else {
                            local.clean += 1;
                            local.clean_ok += usize::from(ok);
                            if !sig_ok[shot] { local.sig_bad += 1; }
                            if !ok && local.clean - local.clean_ok <= 3 {
                                eprintln!("SKY_TAIL_SELFTEST FAIL x={:#x} a={} b={} q={} sig_ok={} restored={restored} clean={clean} phase={}",
                                    h.x, h.a, h.b, h.q, sig_ok[shot], (phase >> shot) & 1);
                            }
                        }
                    }
                }
                let mut t = tally.lock().unwrap();
                t.clean += local.clean;
                t.clean_ok += local.clean_ok;
                t.miss += local.miss;
                t.miss_ok += local.miss_ok;
                t.a0 += local.a0;
                t.term += local.term;
                t.sel += local.sel;
                t.sig_bad += local.sig_bad;
            });
        }
    });
    let t = tally.into_inner().unwrap();
    eprintln!("SKY_TAIL_SELFTEST cut={cut} R={r}: {} handoff states ({} skipped as terminal before the cut, {} as not fitting the handoff registers / 18-bit q)",
        inputs.len(), skipped_terminal, skipped_fit);
    eprintln!("SKY_TAIL_SELFTEST table-clean {}/{} exact round trips (Sig == |x|^-1 at the endpoint, handoff restored, zero phase, zero garbage); a==0 handoffs {} ({} terminal, the rest draining), B-even handoffs {}; table misses {} ({} of them still exact)",
        t.clean_ok, t.clean, t.a0, t.term, t.sel, t.miss, t.miss_ok);
    assert_eq!(t.clean_ok, t.clean, "SKY_TAIL_SELFTEST: {} table-clean inputs failed ({} with a wrong Sig)", t.clean - t.clean_ok, t.sig_bad);
    t
}

pub(crate) fn run() {
    std::env::set_var("MIDQ_SKY_TAIL", "1");
    let only = std::env::var("MIDQ_SKY_SELFTEST_ONLY").unwrap_or_default();
    if only.is_empty() || only.contains("codec") {
        codec_exhaustive();
    }
    if only.is_empty() || only.contains("rails") {
        rails_exhaustive();
    }
    if only.is_empty() || only.contains("tail") {
        tail_roundtrips();
    }
    eprintln!("MIDQ_SKY_TAIL_SELFTEST PASS");
}
