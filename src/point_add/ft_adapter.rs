//! s825: run modp_ft (frogtail/Lilypad arithmetic, `super::ftport`) on greedyfrog registers. Each call builds the
//! routine in a fresh ftport builder on stand-in registers, then splices its op stream into the greedyfrog builder:
//! register qubits map onto the caller's registers, every other qubit onto fresh greedyfrog qubits (|0> before and
//! after), scratch bit 0 onto bit 0 and every persistent bit onto fresh greedyfrog bits. modp_ft's measured erases
//! and conditions are carried as emitted.
use super::builder::B as GB;
use super::ftport::builder::B as FB;
use super::ftport::modp_ft::{self, Ms};
use crate::circuit::{BitId, Op, QubitId, NO_BIT, NO_QUBIT};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug)]
pub enum Kind {
    /// z = a y mod p into a zero z
    Product,
    /// z = a y -> 0
    ProductInv,
    /// z += y^2 mod p (a unused)
    SquareAcc,
    /// sz1 HL-001/HL-002: z = a y mod p into a zero z with `a` as the digit supplier; each digit lane of `a` is
    /// X-measured into ext[i] right after its last use (a ends |0>; the phase (-1)^(ext . a) is left to the caller's
    /// recompute, exactly as the old hmr_to after the product) and joins the carry pool of every later add.
    ProductStream,
    /// sz1 HL-003 (+ HL-004): z = a y; phase (-1)^(ext . w), w = z (neg 0) or p - z (neg 1: modp_ft ctrl_neg pair,
    /// neg 2: one ctrl_neg_phase oracle); z -> 0. One private session, so with `paired` the compute's measured
    /// chunk-carry and overflow-flag erases become debts (modp_ft fix_pair) repaid during the matching uncompute.
    /// z is |0> before and after.
    FixRecompute { neg: u8, paired: bool },
    /// sz1 HL-006: z += (-1)^sub ext mod p for the classical 256-bit ext (a, y unused).
    AddClassical { sub: bool },
    /// sz1 HL-005 (mul 3) / HL-004b (mul 1): z <- ~z - K mod p, K = (mul ext + c - 1) mod p formed by in-circuit classical
    /// arithmetic (0 Toffoli): -z - mul ox as one classical-operand subtraction (a, y unused).
    NegSubClassical { mul: u8 },
}

impl Kind {
    fn has_a(self) -> bool {
        matches!(self, Kind::Product | Kind::ProductInv | Kind::ProductStream | Kind::FixRecompute { .. })
    }
    fn has_y(self) -> bool {
        !matches!(self, Kind::AddClassical { .. } | Kind::NegSubClassical { .. })
    }
}

/// Run `kind` with a carry pool of `room` lanes. z, a, y are greedyfrog registers of 256 lanes each; the result is
/// left on z's own qubits in z's lane order (modp_ft's lane relabelings are undone with swaps).
pub fn ft_call(gb: &mut GB, kind: Kind, z: &[QubitId], a: &[QubitId], y: &[QubitId], room: usize) {
    ft_call_inner(gb, kind, z, a, y, room, &[]);
}

/// ft_call with caller classical bits `ext` (measurement receipts or a classical operand).
pub fn ft_call_ext(gb: &mut GB, kind: Kind, z: &[QubitId], a: &[QubitId], y: &[QubitId], room: usize, ext: &[BitId]) {
    ft_call_inner(gb, kind, z, a, y, room, ext);
}

/// The largest pool for which the routine's peak fits under `cap` live qubits (gb.live + extra lanes <= cap).
pub fn ft_call_capped(gb: &mut GB, kind: Kind, z: &[QubitId], a: &[QubitId], y: &[QubitId], cap: u64) {
    ft_call_capped_ext(gb, kind, z, a, y, cap, &[]);
}

pub fn ft_call_capped_ext(gb: &mut GB, kind: Kind, z: &[QubitId], a: &[QubitId], y: &[QubitId], cap: u64,
                          ext: &[BitId]) {
    let free = cap.saturating_sub(gb.live) as usize;
    let mut room = free.min(256);
    loop {
        let extra = ft_extra(kind, room, ext.len());
        if extra <= free || room == 0 {
            assert!(extra <= free, "no pool fits: free {free}");
            let (t0, live) = (gb.tof, gb.live);
            ft_call_inner(gb, kind, z, a, y, room, ext);
            if std::env::var_os("SZ1_POOLS").is_some() {
                eprintln!("SZ1POOL {kind:?} live {live} cap {cap} free {free} room {room} extra {extra} emitT {}",
                          gb.tof - t0);
            }
            return;
        }
        room -= (extra - free).min(room);
    }
}

/// x -= y^2 mod p with the Leapfrog family's closed flat square block (`super::sqport`, odinfree's 852 tree), sized to
/// `cap`: its local lanes 0..256 are x, 256..512 are y and the rest are |0> scratch (fresh greedyfrog qubits); its
/// classical bits map onto fresh greedyfrog bits.
pub fn native_sub_square(gb: &mut GB, x: &[QubitId], y: &[QubitId], cap: u64) {
    assert_eq!(x.len(), 256);
    assert_eq!(y.len(), 256);
    let ops = super::sqport::native_flat_square_ops_at_cap((cap - (gb.live - 512)) as usize);
    let (nq, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
    assert!(gb.live + nq - 512 <= cap, "native square over the cap: live {} + {}", gb.live, nq - 512);
    let scratch = gb.alloc_n(nq as usize - 512);
    let mut qm = x.to_vec();
    qm.extend_from_slice(y);
    qm.extend_from_slice(&scratch);
    let cm = gb.fresh_bits(nb as usize);
    let mut tof = 0;
    let ops: Vec<Op> = ops.into_iter().map(|mut op| {
        assert_eq!(op.r_target, crate::circuit::NO_REG, "square block must have no register declarations");
        for q in [&mut op.q_target, &mut op.q_control1, &mut op.q_control2] {
            if *q != NO_QUBIT {
                *q = qm[q.0 as usize];
            }
        }
        for c in [&mut op.c_target, &mut op.c_condition] {
            if *c != NO_BIT {
                *c = cm[c.0 as usize];
            }
        }
        if matches!(op.kind, crate::circuit::OperationType::CCX | crate::circuit::OperationType::CCZ) {
            assert_eq!(op.c_condition, NO_BIT);
            tof += 1;
        }
        op
    }).collect();
    gb.push_foreign(ops, tof);
    gb.free_n(&scratch);
}

//// One private modp_ft session: stand-in registers z, a, y (as `kind` uses them), the caller's classical bits as the
/// first `nbits` private bits (ids 10_000..), the routine itself, z's lane order restored, scratch released.
struct Session {
    fb: FB,
    fz: Vec<QubitId>,
    fa: Vec<QubitId>,
    fy: Vec<QubitId>,
    base: u64,
}

fn session(kind: Kind, room: usize, nbits: usize) -> Session {
    let mut fb = FB::new();
    let ext = fb.fresh_bits(nbits);
    let fz = fb.alloc_n(256);
    let fa = if kind.has_a() { fb.alloc_n(256) } else { vec![] };
    let fy = if kind.has_y() { fb.alloc_n(256) } else { vec![] };
    let base = fb.live;
    super::ftport::pointadd_lilypad::CAP.with(|c| c.set(base + 1 + room as u64));
    let ms = Ms::with(&mut fb, room);
    let mut zv = fz.clone();
    match kind {
        Kind::Product => modp_ft::product(&mut fb, &ms, &mut zv, &fa, &fy),
        Kind::ProductInv => modp_ft::product_inv(&mut fb, &ms, &mut zv, &fa, &fy),
        Kind::SquareAcc => {
            let tmp = fb.alloc();
            modp_ft::square_acc(&mut fb, &ms, &mut zv, &fy, tmp);
            fb.free(tmp);
        }
        Kind::ProductStream => {
            assert_eq!(nbits, 256);
            product_stream(&mut fb, &ms, &mut zv, &fa, &fy, &ext);
        }
        Kind::FixRecompute { neg, paired } => {
            assert_eq!(nbits, 256);
            if paired {
                modp_ft::fix_pair_begin_save(0);
            }
            modp_ft::product(&mut fb, &ms, &mut zv, &fa, &fy);
            if paired {
                modp_ft::fix_pair_end_save();
            }
            match neg {
                0 => {
                    for i in 0..256 {
                        fb.z_if(zv[i], ext[i]);
                    }
                }
                1 => {
                    modp_ft::ctrl_neg(&mut fb, &ms, &zv, None);
                    for i in 0..256 {
                        fb.z_if(zv[i], ext[i]);
                    }
                    modp_ft::ctrl_neg(&mut fb, &ms, &zv, None);
                }
                2 => {
                    // the key is a |1> pool lane (ctrl_neg_phase needs a real control qubit)
                    let mut r = ms.r.clone();
                    let key = r.pop().unwrap();
                    let ms2 = Ms { k: ms.k, r, one: ms.one };
                    fb.x(key);
                    modp_ft::ctrl_neg_phase(&mut fb, &ms2, &zv, key, &ext);
                    fb.x(key);
                }
                _ => unreachable!(),
            }
            if paired {
                modp_ft::fix_pair_begin_repay();
            }
            modp_ft::product_inv(&mut fb, &ms, &mut zv, &fa, &fy);
            if paired {
                modp_ft::fix_pair_end_repay();
            }
        }
        Kind::AddClassical { sub } => {
            assert_eq!(nbits, 256);
            modp_ft::modadd_classical(&mut fb, &ms, &zv, &ext, sub);
        }
        Kind::NegSubClassical { mul } => {
            assert_eq!(nbits, 256);
            let kq = classical_mox_plus_cm1(&mut fb, &ext, mul);
            for &q in &zv {
                fb.x(q);
            }
            modp_ft::modadd_classical(&mut fb, &ms, &zv, &kq, true);
        }
    }
    // put bit i of z back on fz[i] (Clifford swaps); qubits displaced from z hold |0> afterwards
    for i in 0..256 {
        if zv[i] != fz[i] {
            let j = zv.iter().position(|&q| q == fz[i]);
            fb.swap(zv[i], fz[i]);
            if let Some(j) = j {
                zv[j] = zv[i];
            }
            zv[i] = fz[i];
        }
    }
    // release modp_ft's scratch: the pool lanes and k (free() only needs them |0>, which modp_ft guarantees)
    ms.release(&mut fb);
    assert_eq!(fb.live, base, "modp_ft left scratch live ({} vs {})", fb.live, base);
    Session { fb, fz, fa, fy, base }
}

/// sz1 HL-001/HL-002: modp_ft::product with every digit lane a_k X-measured into m[k] right after its last use (the
/// a_0 fix uses a_0 last) and pushed onto the carry pool: the pool grows by one lane per digit consumed.
fn product_stream(b: &mut FB, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId], m: &[BitId]) {
    use modp_ft::{ctrl_modsub, mod_double, signed_modadd, signed_modadd_double};
    let n = a.len();
    let mut ms2 = Ms { k: ms.k, r: ms.r.clone(), one: ms.one };
    for i in 0..256 {
        b.cx(y[i], z[i]);
    }
    mod_double(b, &ms2, z);
    for k in (0..n - 1).rev() {
        b.x(a[k + 1]);
        if k > 0 {
            signed_modadd_double(b, &ms2, z, y, Some(a[k + 1]));
        } else {
            signed_modadd(b, &ms2, z, y, Some(a[k + 1]));
        }
        b.x(a[k + 1]);
        b.hmr_to(a[k + 1], m[k + 1]);
        if STREAM_GROW {
            ms2.r.push(a[k + 1]);
        }
    }
    b.x(a[0]);
    ctrl_modsub(b, &ms2, z, y, a[0]);
    b.x(a[0]);
    b.hmr_to(a[0], m[0]);
}

/// sz1: measured digit lanes join the stream product's carry pool (false: measured early, pool fixed; diagnostic).
pub const STREAM_GROW: bool = true;

/// K = (mul ox + c - 1) mod p (mul 1 or 3) into fresh classical bits (LSB first), for a classical ox < p: classical
/// ripple arithmetic on the condition stack, 0 Toffoli. mul 3 is odinfree's Lilypad `classical_3ox_plus_cm1`
/// verbatim; mul 1 drops its 2 ox + ox and one conditional subtraction (ox + c - 1 < 2 p).
fn classical_mox_plus_cm1(b: &mut FB, ox: &[BitId], mul: u8) -> Vec<BitId> {
    use super::ftport::builder::CSrc;
    const W: usize = 258;
    assert_eq!(ox.len(), 256);
    let pm = super::ftport::frogdrop_sched::p();
    let pb: Vec<bool> = (0..256).map(|i| pm.bit(i)).collect();
    let a = b.fresh_bits(W);
    match mul {
        3 => {
            for i in 0..256 {
                b.cbit_xor_and(a[i + 1], &[ox[i]]);
            }
            let src: Vec<CSrc> = ox.iter().map(|&o| CSrc::Bit(o)).collect();
            b.c_add(&a, &src, false, None);
            b.c_cond_sub_const(&a, &pb);
            b.c_cond_sub_const(&a, &pb);
        }
        1 => {
            for i in 0..256 {
                b.cbit_xor_and(a[i], &[ox[i]]);
            }
        }
        _ => unreachable!(),
    }
    let cm1 = modp_ft::C - 1;
    let cs: Vec<CSrc> = (0..64).map(|i| if (cm1 >> i) & 1 == 1 { CSrc::One } else { CSrc::Zero }).collect();
    b.c_add(&a, &cs, false, None);
    b.c_cond_sub_const(&a, &pb);
    a[..256].to_vec()
}

/// Lanes the routine needs beyond its registers at a given pool (measured on a dry build).
fn ft_extra(kind: Kind, room: usize, nbits: usize) -> usize {
    let s = session(kind, room, nbits);
    (s.fb.peak - s.base) as usize
}

fn ft_call_inner(gb: &mut GB, kind: Kind, z: &[QubitId], a: &[QubitId], y: &[QubitId], room: usize, ext: &[BitId]) {
    assert_eq!(z.len(), 256);
    if kind.has_a() {
        assert_eq!(a.len(), 256);
    }
    if kind.has_y() {
        assert_eq!(y.len(), 256);
    }
    let Session { fb, fz, fa, fy, base: _ } = session(kind, room, ext.len());
    // ---- splice
    let regs: std::collections::BTreeSet<u64> = fz.iter().chain(&fa).chain(&fy).map(|q| q.0).collect();
    let mut qmap: BTreeMap<u64, QubitId> = BTreeMap::new();
    for (i, q) in fz.iter().enumerate() {
        qmap.insert(q.0, z[i]);
    }
    for (i, q) in fa.iter().enumerate() {
        qmap.insert(q.0, a[i]);
    }
    for (i, q) in fy.iter().enumerate() {
        qmap.insert(q.0, y[i]);
    }
    // every other qubit modp_ft touched maps onto a fresh greedyfrog qubit; the caller's bits are private bits
    // 10_000.., every other persistent bit maps onto a fresh greedyfrog bit
    let mut others: Vec<u64> = vec![];
    let mut seen_q: std::collections::BTreeSet<u64> = Default::default();
    let mut bmap: BTreeMap<u64, BitId> = BTreeMap::new();
    for (i, &c) in ext.iter().enumerate() {
        bmap.insert(10_000 + i as u64, c);
    }
    let mut bits: Vec<u64> = vec![];
    for op in &fb.ops {
        for q in [op.q_target, op.q_control1, op.q_control2] {
            if q != NO_QUBIT && !regs.contains(&q.0) && seen_q.insert(q.0) {
                others.push(q.0);
            }
        }
        for c in [op.c_target, op.c_condition] {
            if c != NO_BIT && c != BitId(0) && !bmap.contains_key(&c.0) {
                assert!(c.0 >= 10_000, "unexpected declared bit {} in a modp_ft stream", c.0);
                bmap.insert(c.0, NO_BIT);
                bits.push(c.0);
            }
        }
    }
    for &q in &others {
        assert!(q < 1 << 40, "sentinel qubit {q:#x} reached the emitted stream");
    }
    let fresh_q = gb.alloc_n(others.len());
    for (k, &q) in others.iter().enumerate() {
        qmap.insert(q, fresh_q[k]);
    }
    let fresh_b = gb.fresh_bits(bits.len());
    for (k, &b) in bits.iter().enumerate() {
        bmap.insert(b, fresh_b[k]);
    }
    let mq = |q: QubitId| if q == NO_QUBIT { q } else { qmap[&q.0] };
    let mb = |c: BitId| if c == NO_BIT || c == BitId(0) { c } else { bmap[&c.0] };
    let ops: Vec<Op> = fb.ops.iter().map(|op| Op {
        kind: op.kind,
        q_target: mq(op.q_target),
        q_control1: mq(op.q_control1),
        q_control2: mq(op.q_control2),
        c_target: mb(op.c_target),
        c_condition: mb(op.c_condition),
        r_target: op.r_target,
    }).collect();
    gb.push_foreign(ops, fb.tof);
    gb.free_n(&fresh_q);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};
    type N = ruint::Uint<512, 8>;

    fn p() -> N {
        (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
    }

    fn load(qs: &mut Vec<u64>, reg: &[QubitId], vals: &[N]) {
        for (s, v) in vals.iter().enumerate() {
            for (i, &q) in reg.iter().enumerate() {
                if v.bit(i) {
                    qs[q.0 as usize] |= 1u64 << s;
                }
            }
        }
    }

    fn read(qs: &[u64], reg: &[QubitId], s: usize) -> N {
        let mut v = N::ZERO;
        for (i, &q) in reg.iter().enumerate() {
            if (qs[q.0 as usize] >> s) & 1 == 1 {
                v |= N::from(1u64) << i;
            }
        }
        v
    }

    /// Exact gate-level check of the spliced modp_ft product / product_inv / square_acc at several pool sizes:
    /// 64 random shots, z = a y, then z -> 0, then z += y^2 on a random z; a, y restored; every other qubit |0>;
    /// phase 0.
    #[test]
    fn ft_adapter_gate_level() {
        let pp = p();
        let rooms: Vec<usize> = std::env::var("FT_ROOMS").ok()
            .map(|v| v.split(',').map(|t| t.parse().unwrap()).collect()).unwrap_or(vec![44, 48, 55]);
        for room in rooms {
            let mut b = GB::new();
            let z = b.alloc_n(256);
            let a = b.alloc_n(256);
            let y = b.alloc_n(256);
            let w = b.alloc_n(256);
            let t0 = b.tof;
            ft_call(&mut b, Kind::Product, &z, &a, &y, room);
            let m1 = b.ops.len();
            let t1 = b.tof;
            ft_call(&mut b, Kind::ProductInv, &z, &a, &y, room);
            let m2 = b.ops.len();
            let t2 = b.tof;
            ft_call(&mut b, Kind::SquareAcc, &w, &[], &y, room);
            let t3 = b.tof;
            eprintln!("FT room {room}: product {} T, product_inv {} T, square_acc {} T (emitted), peak {} (regs 1024)",
                      t1 - t0, t2 - t1, t3 - t2, b.peak);
            let mut s64 = 0x5ee0_1234_9876_abcdu64 ^ room as u64;
            let mut next = || { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; s64 };
            let mut rnd = || {
                let mut v = N::ZERO;
                for i in 0..4 { v |= N::from(next()) << (64 * i); }
                v % pp
            };
            let av: Vec<N> = (0..64).map(|_| rnd()).collect();
            let yv: Vec<N> = (0..64).map(|_| rnd()).collect();
            let wv: Vec<N> = (0..64).map(|_| rnd()).collect();
            let mut h = sha3::Shake256::default();
            h.update(b"ft-adapter");
            h.update(&[room as u8]);
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(b.width() as usize, 200_000, &mut xof);
            load(&mut sim.qubits, &a, &av);
            load(&mut sim.qubits, &y, &yv);
            load(&mut sim.qubits, &w, &wv);
            sim.apply_iter(b.ops[..m1].iter());
            for s in 0..64 {
                assert_eq!(read(&sim.qubits, &z, s), av[s].mul_mod(yv[s], pp), "room {room} shot {s}: product wrong");
            }
            sim.apply_iter(b.ops[m1..m2].iter());
            sim.apply_iter(b.ops[m2..].iter());
            for s in 0..64 {
                assert_eq!(read(&sim.qubits, &z, s), N::ZERO, "room {room} shot {s}: product_inv left z");
                assert_eq!(read(&sim.qubits, &a, s), av[s], "room {room} shot {s}: a changed");
                assert_eq!(read(&sim.qubits, &y, s), yv[s], "room {room} shot {s}: y changed");
                let want = (wv[s] + yv[s].mul_mod(yv[s], pp)) % pp;
                assert_eq!(read(&sim.qubits, &w, s), want, "room {room} shot {s}: square_acc wrong");
            }
            assert_eq!(sim.phase, 0, "room {room}: phase garbage {:016x}", sim.phase);
            let regs: std::collections::BTreeSet<u64> = z.iter().chain(&a).chain(&y).chain(&w).map(|q| q.0).collect();
            for q in 0..b.width() {
                if !regs.contains(&q) {
                    assert_eq!(sim.qubits[q as usize], 0, "room {room}: scratch qubit {q} dirty");
                }
            }
            eprintln!("FT room {room}: exact on 64 shots, scratch clean, phase 0");
            sz1_kinds(room);
        }
    }

    fn rnd_vals(seed: u64, n: usize) -> Vec<N> {
        let pp = p();
        let mut s64 = seed;
        let mut next = || { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; s64 };
        (0..n).map(|_| {
            let mut v = N::ZERO;
            for i in 0..4 { v |= N::from(next()) << (64 * i); }
            v % pp
        }).collect()
    }

    fn load_bitsv(sim_bits: &mut Vec<u64>, bits: &[BitId], vals: &[N]) {
        for (s, v) in vals.iter().enumerate() {
            for (i, &c) in bits.iter().enumerate() {
                if v.bit(i) {
                    sim_bits[c.0 as usize] |= 1u64 << s;
                }
            }
        }
    }

    /// sz1: every new kind at a capped pool of `room` lanes (cap = live + room + 1, the receiver's sizing rule), 64
    /// random shots mod p. Each check closes its own phase: the value whose phase a kind must repay is first placed
    /// in a register w and X-measured by hmr_to into the same receipts, so exactness <=> final phase 0. Checks: result
    /// exact, operands restored (stream: digit lanes |0>), every other qubit |0>, phase 0, peak <= cap.
    fn sz1_kinds(room: usize) {
        let pp = p();
        let only: Option<String> = std::env::var("SZ1_KINDS").ok();
        let want = |k: &str| only.as_ref().map_or(true, |o| o.split(',').any(|t| t == k));
        let kinds: Vec<(&str, Kind)> = vec![
            ("stream", Kind::ProductStream),
            ("fix00", Kind::FixRecompute { neg: 0, paired: false }),
            ("fix01", Kind::FixRecompute { neg: 0, paired: true }),
            ("fix11", Kind::FixRecompute { neg: 1, paired: true }),
            ("fix20", Kind::FixRecompute { neg: 2, paired: false }),
            ("fix21", Kind::FixRecompute { neg: 2, paired: true }),
            ("addc", Kind::AddClassical { sub: false }),
            ("subc", Kind::AddClassical { sub: true }),
            ("neg3", Kind::NegSubClassical { mul: 3 }), ("neg1", Kind::NegSubClassical { mul: 1 }),
        ];
        for (name, kind) in kinds {
            if !want(name) {
                continue;
            }
            let mut b = GB::new();
            let z = b.alloc_n(256);
            let a = b.alloc_n(256);
            let y = b.alloc_n(256);
            let w = b.alloc_n(256);
            let m = b.fresh_bits(256);
            let seed = 0x5a5a_0123_4567_89abu64 ^ ((room as u64) << 32) ^ name.len() as u64 * 0x9e37;
            let av = rnd_vals(seed, 64);
            let yv = rnd_vals(seed ^ 0x1111, 64);
            let zv = rnd_vals(seed ^ 0x2222, 64);
            let ov = rnd_vals(seed ^ 0x3333, 64);
            // w: the value whose phase the kind repays (fix kinds), or a's value (stream: its digits are measured)
            let wv: Vec<N> = (0..64).map(|s| match kind {
                Kind::FixRecompute { neg: 0, .. } => av[s].mul_mod(yv[s], pp),
                Kind::FixRecompute { .. } => (pp - av[s].mul_mod(yv[s], pp)) % pp,
                Kind::ProductStream => av[s],
                _ => N::ZERO,
            }).collect();
            let is_fix = matches!(kind, Kind::FixRecompute { .. });
            let is_stream = matches!(kind, Kind::ProductStream);
            let is_cl = matches!(kind, Kind::AddClassical { .. } | Kind::NegSubClassical { .. });
            // fix kinds: measure w into m first (phase (-1)^(m . w), w -> 0)
            if is_fix {
                for i in 0..256 {
                    b.hmr_to(w[i], m[i]);
                }
            }
            // classical-operand kinds run where only x, y are live (313 free lanes at cap 825; they need 256 + 1)
            let cap = b.live + if is_cl { 313 } else { room as u64 + 1 };
            let m0 = b.ops.len();
            let t0 = b.tof;
            ft_call_capped_ext(&mut b, kind, &z, &a, &y, cap, &m);
            let t1 = b.tof;
            let m1 = b.ops.len();
            // stream: repay a's measured phase from w (= a, loaded below), then w is cleared classically
            if is_stream {
                for i in 0..256 {
                    b.z_if(w[i], m[i]);
                }
            }
            let mut depth = 0i32;
            let mut exp = 0f64;
            for op in &b.ops[m0..m1] {
                match op.kind {
                    crate::circuit::OperationType::PushCondition => depth += 1,
                    crate::circuit::OperationType::PopCondition => depth -= 1,
                    crate::circuit::OperationType::CCX | crate::circuit::OperationType::CCZ =>
                        exp += 2f64.powi(-depth) * if op.c_condition == NO_BIT { 1.0 } else { 0.5 },
                    _ => {}
                }
            }
            eprintln!("SZ1 room {room} {name}: emitted {} T, expected {exp:.1}, peak {} cap {cap}", t1 - t0, b.peak);
            assert!(b.peak <= cap, "room {room} {name}: peak {} over cap {cap}", b.peak);
            let mut h = sha3::Shake256::default();
            h.update(b"sz1-kinds");
            h.update(name.as_bytes());
            h.update(&[room as u8]);
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(b.width() as usize, 400_000, &mut xof);
            if is_cl {
                load(&mut sim.qubits, &z, &zv);
                load_bitsv(&mut sim.bits, &m, &ov);
            } else {
                load(&mut sim.qubits, &a, &av);
                load(&mut sim.qubits, &y, &yv);
            }
            if is_fix {
                load(&mut sim.qubits, &w, &wv);
            }
            sim.apply_iter(b.ops[..m1].iter());
            if is_stream {
                load(&mut sim.qubits, &w, &wv);
            }
            sim.apply_iter(b.ops[m1..].iter());
            if is_stream {
                for &q in &w {
                    sim.qubits[q.0 as usize] = 0;
                }
            }
            for s in 0..64 {
                let got = read(&sim.qubits, &z, s);
                let want = match kind {
                    Kind::ProductStream => av[s].mul_mod(yv[s], pp),
                    Kind::FixRecompute { .. } => N::ZERO,
                    Kind::AddClassical { sub: false } => (zv[s] + ov[s]) % pp,
                    Kind::AddClassical { sub: true } => (zv[s] + pp - ov[s]) % pp,
                    Kind::NegSubClassical { mul } => {
                        let t = (zv[s] + ov[s].mul_mod(N::from(mul as u64), pp)) % pp;
                        (pp - t) % pp
                    }
                    _ => unreachable!(),
                };
                assert_eq!(got, want, "room {room} {name} shot {s}: z wrong");
                if !is_cl {
                    let want_a = if is_stream { N::ZERO } else { av[s] };
                    assert_eq!(read(&sim.qubits, &a, s), want_a, "room {room} {name} shot {s}: a wrong");
                    assert_eq!(read(&sim.qubits, &y, s), yv[s], "room {room} {name} shot {s}: y changed");
                }
            }
            assert_eq!(sim.phase, 0, "room {room} {name}: phase garbage {:016x}", sim.phase);
            let keep: std::collections::BTreeSet<u64> = if is_cl {
                z.iter().map(|q| q.0).collect()
            } else {
                z.iter().chain(&a).chain(&y).map(|q| q.0).collect()
            };
            for q in 0..b.width() {
                if !keep.contains(&q) {
                    assert_eq!(sim.qubits[q as usize], 0, "room {room} {name}: scratch qubit {q} dirty");
                }
            }
            eprintln!("SZ1 room {room} {name}: exact on 64 shots, operands restored, scratch clean, phase 0");
        }
    }

    /// The spliced native flat square: x -= y^2 mod p exactly on 64 random shots, y restored, scratch clean, phase 0.
    #[test]
    fn native_sub_square_gate_level() {
        let pp = p();
        let cap: u64 = std::env::var("NSQ_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(825);
        let mut b = GB::new();
        let x = b.alloc_n(256);
        let y = b.alloc_n(256);
        native_sub_square(&mut b, &x, &y, cap);
        let mut depth = 0i32;
        let mut exp = 0f64;
        for op in &b.ops {
            match op.kind {
                crate::circuit::OperationType::PushCondition => depth += 1,
                crate::circuit::OperationType::PopCondition => depth -= 1,
                crate::circuit::OperationType::CCX | crate::circuit::OperationType::CCZ => exp += 2f64.powi(-depth),
                _ => {}
            }
        }
        eprintln!("NSQ cap {cap}: emitted {} T, expected {exp:.1}, peak {}", b.tof, b.peak);
        assert!(b.peak <= cap);
        let mut s64 = 0x0a5e_77c1_d00d_f00du64;
        let mut next = || { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; s64 };
        let mut rnd = || {
            let mut v = N::ZERO;
            for i in 0..4 { v |= N::from(next()) << (64 * i); }
            v % pp
        };
        let xv: Vec<N> = (0..64).map(|_| rnd()).collect();
        let yv: Vec<N> = (0..64).map(|_| rnd()).collect();
        let mut h = sha3::Shake256::default();
        h.update(b"native-sub-square");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(b.width() as usize, 200_000, &mut xof);
        load(&mut sim.qubits, &x, &xv);
        load(&mut sim.qubits, &y, &yv);
        sim.apply_iter(b.ops.iter());
        for s in 0..64 {
            let want = (xv[s] + pp - yv[s].mul_mod(yv[s], pp)) % pp;
            assert_eq!(read(&sim.qubits, &x, s), want, "shot {s}: x -= y^2 wrong");
            assert_eq!(read(&sim.qubits, &y, s), yv[s], "shot {s}: y changed");
        }
        assert_eq!(sim.phase, 0, "phase garbage {:016x}", sim.phase);
        let regs: std::collections::BTreeSet<u64> = x.iter().chain(&y).map(|q| q.0).collect();
        for q in 0..b.width() {
            if !regs.contains(&q) {
                assert_eq!(sim.qubits[q as usize], 0, "scratch qubit {q} dirty");
            }
        }
        eprintln!("NSQ cap {cap}: exact on 64 shots, scratch clean, phase 0");
    }
}
