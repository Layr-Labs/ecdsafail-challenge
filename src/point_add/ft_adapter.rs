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
}

/// Run `kind` with a carry pool of `room` lanes. z, a, y are greedyfrog registers of 256 lanes each; the result is
/// left on z's own qubits in z's lane order (modp_ft's lane relabelings are undone with swaps).
pub fn ft_call(gb: &mut GB, kind: Kind, z: &[QubitId], a: &[QubitId], y: &[QubitId], room: usize) {
    ft_call_inner(gb, kind, z, a, y, room);
}

/// The largest pool for which the routine's peak fits under `cap` live qubits (gb.live + extra lanes <= cap).
pub fn ft_call_capped(gb: &mut GB, kind: Kind, z: &[QubitId], a: &[QubitId], y: &[QubitId], cap: u64) {
    let free = cap.saturating_sub(gb.live) as usize;
    let mut room = free.min(256);
    loop {
        let extra = ft_extra(kind, room);
        if extra <= free || room == 0 {
            assert!(extra <= free, "no pool fits: free {free}");
            return ft_call_inner(gb, kind, z, a, y, room);
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

/// Lanes the routine needs beyond its 256-lane registers at a given pool (measured on a dry build).
pub fn ft_extra(kind: Kind, room: usize) -> usize {
    let mut fb = FB::new();
    let fz = fb.alloc_n(256);
    let fa = if matches!(kind, Kind::SquareAcc) { vec![] } else { fb.alloc_n(256) };
    let fy = fb.alloc_n(256);
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
    }
    (fb.peak - base) as usize
}

fn ft_call_inner(gb: &mut GB, kind: Kind, z: &[QubitId], a: &[QubitId], y: &[QubitId], room: usize) {
    assert_eq!(z.len(), 256);
    assert_eq!(y.len(), 256);
    let mut fb = FB::new();
    let fz = fb.alloc_n(256);
    let fa = match kind {
        Kind::SquareAcc => vec![],
        _ => {
            assert_eq!(a.len(), 256);
            fb.alloc_n(256)
        }
    };
    let fy = fb.alloc_n(256);
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
    let mut regs: std::collections::BTreeSet<u64> = fz.iter().chain(&fa).chain(&fy).map(|q| q.0).collect();
    let z_set: std::collections::BTreeSet<u64> = fz.iter().map(|q| q.0).collect();
    let _ = &z_set;
    ms.release(&mut fb);
    assert_eq!(fb.live, base, "modp_ft left scratch live ({} vs {})", fb.live, base);
    // ---- splice
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
    let mut others: Vec<u64> = vec![];
    let mut bits: Vec<u64> = vec![];
    let note_q = |q: QubitId, others: &mut Vec<u64>| {
        if q != NO_QUBIT && !regs.contains(&q.0) && !others.contains(&q.0) {
            others.push(q.0);
        }
    };
    for op in &fb.ops {
        for q in [op.q_target, op.q_control1, op.q_control2] {
            note_q(q, &mut others);
        }
        for c in [op.c_target, op.c_condition] {
            if c != NO_BIT && c != BitId(0) && !bits.contains(&c.0) {
                assert!(c.0 >= 10_000, "unexpected declared bit {} in a modp_ft stream", c.0);
                bits.push(c.0);
            }
        }
    }
    regs.clear();
    for &q in &others {
        assert!(q < 1 << 40, "sentinel qubit {q:#x} reached the emitted stream");
    }
    let fresh_q = gb.alloc_n(others.len());
    for (k, &q) in others.iter().enumerate() {
        qmap.insert(q, fresh_q[k]);
    }
    let fresh_b = gb.fresh_bits(bits.len());
    let bmap: BTreeMap<u64, BitId> = bits.iter().enumerate().map(|(k, &b)| (b, fresh_b[k])).collect();
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

    /// gf flatsq: the spliced native flat square at cap NSQ_CAP on one batch of 64 edge pairs and NSQ_BATCHES batches
    /// of 64 random field pairs (seed NSQ_SEED, a fresh simulator per batch). Counts the shots where x -= y^2 is wrong
    /// or y changed, and the shots with phase or scratch garbage. Runs only when NSQ_BATCHES is set. NSQ_FT=1 runs
    /// modp_ft's square_acc (x += y^2, pool NSQ_ROOM, default 256) on the same inputs instead, for comparison.
    #[test]
    fn native_sub_square_classical() {
        let Some(batches) = std::env::var("NSQ_BATCHES").ok().and_then(|v| v.parse::<usize>().ok()) else { return };
        let pp = p();
        let cap: u64 = std::env::var("NSQ_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(825);
        let seed: u64 = std::env::var("NSQ_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0x5eed_f1a7_5a0a_2026);
        let mut b = GB::new();
        let x = b.alloc_n(256);
        let y = b.alloc_n(256);
        let ft = std::env::var("NSQ_FT").is_ok_and(|v| v == "1");
        if ft {
            let room: usize = std::env::var("NSQ_ROOM").ok().and_then(|v| v.parse().ok()).unwrap_or(256);
            ft_call(&mut b, Kind::SquareAcc, &x, &[], &y, room);
        } else {
            native_sub_square(&mut b, &x, &y, cap);
            assert!(b.peak <= cap);
        }
        let regs: std::collections::BTreeSet<u64> = x.iter().chain(&y).map(|q| q.0).collect();
        let one = N::from(1u64);
        let ye = [N::ZERO, one, N::from(2u64), pp - one, pp - N::from(2u64), pp - N::from(3u64), (one << 128) - one,
                  one << 128, (one << 128) + one, (one << 255) - one, one << 255, (one << 64) - one, (one << 192) - one,
                  (one << 32) + N::from(977u64), pp - (one << 32), (one << 255) + one];
        let xe = [N::ZERO, one, pp - one, (one << 255) - one];
        let mut s64 = seed | 1;
        let mut next = || { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; s64 };
        let mut rnd = || {
            let mut v = N::ZERO;
            for i in 0..4 { v |= N::from(next()) << (64 * i); }
            v % pp
        };
        let (mut value_bad, mut source_bad, mut phase_bad, mut scratch_bad, mut edge_bad) = (0u64, 0u64, 0u64, 0u64, 0u64);
        for batch in 0..=batches {
            let (xv, yv): (Vec<N>, Vec<N>) = if batch == 0 {
                (0..64).map(|s| (xe[s / 16], ye[s % 16])).unzip()
            } else {
                (0..64).map(|_| (rnd(), rnd())).unzip()
            };
            let mut h = sha3::Shake256::default();
            h.update(b"native-sub-square-classical");
            h.update(&seed.to_le_bytes());
            h.update(&(batch as u64).to_le_bytes());
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(b.width() as usize, 200_000, &mut xof);
            load(&mut sim.qubits, &x, &xv);
            load(&mut sim.qubits, &y, &yv);
            sim.apply_iter(b.ops.iter());
            let (mut vbad, mut sbad) = (0u64, 0u64);
            for s in 0..64 {
                let y2 = yv[s].mul_mod(yv[s], pp);
                let want = if ft { (xv[s] + y2) % pp } else { (xv[s] + pp - y2) % pp };
                if read(&sim.qubits, &x, s) != want { vbad |= 1 << s; }
                if read(&sim.qubits, &y, s) != yv[s] { sbad |= 1 << s; }
            }
            let mut dirty = 0u64;
            for q in 0..b.width() {
                if !regs.contains(&q) { dirty |= sim.qubits[q as usize]; }
            }
            if batch == 0 {
                // edge shot s: x = xe[s / 16], y = ye[s % 16]
                edge_bad = (vbad | sbad | sim.phase | dirty).count_ones() as u64;
                eprintln!("NSQ_EDGE value {vbad:016x} source {sbad:016x} phase {:016x} scratch {dirty:016x}", sim.phase);
            } else {
                value_bad += vbad.count_ones() as u64;
                source_bad += sbad.count_ones() as u64;
                phase_bad += sim.phase.count_ones() as u64;
                scratch_bad += dirty.count_ones() as u64;
            }
        }
        eprintln!("NSQ_CLASSICAL {{\"block\": \"{}\", \"cap\": {cap}, \"seed\": {seed}, \"edge_shots\": 64, \"random_shots\": {}, \"tof\": {}, \
                   \"peak\": {}, \"value_bad\": {value_bad}, \"source_bad\": {source_bad}, \"phase_bad\": {phase_bad}, \
                   \"scratch_bad\": {scratch_bad}, \"edge_bad\": {edge_bad}}}", if ft { "modp_ft_square_acc" } else { "flat_sub_square" },
                   64 * batches, b.tof, b.peak);
        assert_eq!(value_bad + source_bad + phase_bad + scratch_bad, 0, "random shots failed");
    }
}
