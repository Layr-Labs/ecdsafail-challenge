//! CONE765 (ob-wire, v8 M3): the frame-free stream of the 765-qubit cone design. No S-D' frame and no native walk:
//! the whole point addition is a sequence of GLV2 gate lists (gl/glv2.py; built by gl/cone/seam.py from the exact
//! Python modules) spliced in order, each through its own lane map (list lane -> physical qubit) and bit base
//! (list bit b -> classical bit base + b). The table of lists and splices is generated (`cone_data.rs`,
//! gl/cone/gen_rust.py). Registers as the native build: qubits 0..255 = x, 256..511 = y (in and out), classical
//! bits 0..255 = ox, 256..511 = oy.
//! GLV2 (.glz) = zstd of: b"GLV2" | u32 n_ops | u32 n_lanes | u32 n_bits | u32 n_tof | u32 0 | per op: u8 code (low
//! 5 bits; bit 7 = conditioned) + u32 LE operands + [u32 cond bit]. Codes: 0 X(t) 1 CX(c,t) 2 CCX(a,b,t) 3 Z(t)
//! 4 CZ(a,t) 5 CCZ(a,b,t) 6 SWAP(a,t) 7 NEG 8 HMR(t,bit) 9 R(t) 10 PUSH(bit) 11 POP 12 BINV(bit) 13 BST0(bit) 14 BST1(bit).
//! Every list is checked on load: SHA3-256 of the .glz, op count, CCX + CCZ count, exact length, lanes inside its map.
use super::cone_data::{INST, INST_SHA3, LISTS, NQ_MAX, SPLICES, TPL, TPL_SHA3};
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use sha3::{Digest, Sha3_256};

pub(super) struct ConeList {
    pub name: &'static str,
    pub data: &'static [u8],
    pub sha3: &'static str,
}

pub(super) struct ConeSplice {
    pub list: usize,
    /// list lane -> physical qubit; empty = identity
    pub map: &'static [u32],
    pub bitbase: u64,
}

fn sha3_hex(z: &[u8]) -> String {
    Sha3_256::digest(z).iter().map(|b| format!("{:02x}", b)).collect()
}

const NOQ: u32 = u32::MAX;

/// (kind, number of qubit operands, has a bit operand)
fn code(c: u8) -> (OperationType, usize, bool) {
    use OperationType::*;
    match c {
        0 => (X, 1, false),
        1 => (CX, 2, false),
        2 => (CCX, 3, false),
        3 => (Z, 1, false),
        4 => (CZ, 2, false),
        5 => (CCZ, 3, false),
        6 => (Swap, 2, false),
        7 => (Neg, 0, false),
        8 => (Hmr, 1, true),
        9 => (R, 1, false),
        10 => (PushCondition, 0, true),
        11 => (PopCondition, 0, false),
        12 => (BitInvert, 0, true),
        13 => (BitStore0, 0, true),
        14 => (BitStore1, 0, true),
        _ => panic!("cone: bad GLV2 op code {c}"),
    }
}

/// Decode one GLV2 body and append its ops, lanes through `map` (empty = identity), bits + `bb`.
/// Returns (ops, CCX + CCZ ops, max physical qubit + 1).
pub(super) fn emit_list(raw: &[u8], map: &[u32], bb: u64, out: &mut Vec<Op>) -> (u64, u64, u32) {
    emit_list_b(raw, map, &|b| b as u64 + bb, out)
}

/// As `emit_list`, bits through `bm` (list bit -> global bit).
pub(super) fn emit_list_b(raw: &[u8], map: &[u32], bm: &dyn Fn(u32) -> u64, out: &mut Vec<Op>) -> (u64, u64, u32) {
    assert!(raw.len() >= 24 && &raw[0..4] == b"GLV2", "cone: bad magic");
    let r32 = |o: usize| u32::from_le_bytes([raw[o], raw[o + 1], raw[o + 2], raw[o + 3]]);
    let (n, nl, ntof) = (r32(4) as u64, r32(8), r32(16) as u64);
    assert!(map.is_empty() || map.len() >= nl as usize, "cone: lane map shorter than the list's lanes");
    let (mut o, mut t, mut top) = (24usize, 0u64, 0u32);
    out.reserve(n as usize);
    for _ in 0..n {
        let c = raw[o];
        o += 1;
        let (kind, nq, hb) = code(c & 0x1f);
        let mut q = [NOQ; 3];
        for qi in q.iter_mut().take(nq) {
            let l = r32(o);
            o += 4;
            assert!(l < nl, "cone: lane beyond n_lanes");
            *qi = if map.is_empty() { l } else { map[l as usize] };
            top = top.max(*qi + 1);
        }
        let mut op = Op::empty();
        op.kind = kind;
        if hb {
            let b = bm(r32(o));
            o += 4;
            if kind == OperationType::PushCondition {
                op.c_condition = BitId(b);
            } else {
                op.c_target = BitId(b);
            }
        }
        if c & 0x80 != 0 {
            assert!(kind != OperationType::PushCondition && kind != OperationType::PopCondition, "cone: conditioned PUSH/POP");
            op.c_condition = BitId(bm(r32(o)));
            o += 4;
        }
        // operand order: GLV2 lists (controls..., target); circuit.rs Op: q_control1, q_control2, q_target
        let qq = |x: u32| QubitId(x as u64);
        match nq {
            1 => op.q_target = qq(q[0]),
            2 => {
                op.q_control1 = qq(q[0]);
                op.q_target = qq(q[1]);
            }
            3 => {
                op.q_control1 = qq(q[0]);
                op.q_control2 = qq(q[1]);
                op.q_target = qq(q[2]);
                t += 1;
            }
            _ => {}
        }
        out.push(op);
    }
    assert_eq!(o, raw.len(), "cone: trailing bytes");
    assert_eq!(t, ntof, "cone: CCX + CCZ count");
    (n, t, top)
}

pub(super) fn build() -> Vec<Op> {
    let mut ops: Vec<Op> = Vec::new();
    for r in 0..4u64 {
        let mut o = Op::empty();
        o.kind = OperationType::Register;
        o.r_target = RegisterId(r);
        ops.push(o);
    }
    for r in 0..2u64 {
        for i in 0..256u64 {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.q_target = QubitId(256 * r + i);
            o.r_target = RegisterId(r);
            ops.push(o);
        }
    }
    for r in 0..2u64 {
        for i in 0..256u64 {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.c_target = BitId(256 * r + i);
            o.r_target = RegisterId(2 + r);
            ops.push(o);
        }
    }
    if !TPL.is_empty() {
        let (n, t, top) = emit_cone2(&mut ops);
        assert!(top <= NQ_MAX, "cone: stream uses {top} qubits > NQ_MAX {NQ_MAX}");
        eprintln!("point_add: ops {} (CONE765 frame-free stream, CONE2: {n} list ops), CCX+CCZ ops {t}, qubits {top}", ops.len());
        return ops;
    }
    let mut raws: Vec<Option<Vec<u8>>> = (0..LISTS.len()).map(|_| None).collect();
    let (mut top, mut tof) = (0u32, 0u64);
    for (i, s) in SPLICES.iter().enumerate() {
        let l = &LISTS[s.list];
        if raws[s.list].is_none() {
            assert_eq!(sha3_hex(l.data), l.sha3, "cone: sha3 of list '{}' changed", l.name);
            raws[s.list] = Some(zstd::stream::decode_all(l.data).expect("cone: zstd decode"));
        }
        let (n, t, tp) = emit_list(raws[s.list].as_ref().unwrap(), s.map, s.bitbase, &mut ops);
        top = top.max(tp);
        tof += t;
        eprintln!("cone: splice {i} '{}' ops {n} CCX+CCZ ops {t} bitbase {} max qubit+1 {tp}", l.name, s.bitbase);
        if SPLICES[i + 1..].iter().all(|x| x.list != s.list) {
            raws[s.list] = None; // free the body after its last use
        }
    }
    assert!(top <= NQ_MAX, "cone: stream uses {top} qubits > NQ_MAX {NQ_MAX}");
    eprintln!("point_add: ops {} (CONE765 frame-free stream), CCX+CCZ ops {tof}, qubits {top}", ops.len());
    ops
}

fn varint(b: &[u8], o: &mut usize) -> u64 {
    let (mut v, mut s) = (0u64, 0u32);
    loop {
        let c = b[*o];
        *o += 1;
        v |= ((c & 0x7f) as u64) << s;
        if c < 0x80 {
            return v;
        }
        s += 7;
    }
}

fn delta_list(b: &[u8], o: &mut usize) -> Vec<u64> {
    let n = varint(b, o) as usize;
    let (mut prev, mut l) = (0i64, Vec::with_capacity(n));
    for _ in 0..n {
        let u = varint(b, o);
        prev += if u & 1 == 0 { (u >> 1) as i64 } else { -(((u + 1) >> 1) as i64) };
        l.push(prev as u64);
    }
    l
}

/// CONE2 (gl/cone/dedup.py): templates (CTP2) + records (CIN3: 0 INST template id + lane list + bit list, lanes through
/// the current MAP and bits + the current BASE; 1 MAP list, empty = identity; 2 BASE). Returns (ops, CCX + CCZ ops, max qubit + 1).
pub(super) fn emit_cone2(out: &mut Vec<Op>) -> (u64, u64, u32) {
    assert_eq!(sha3_hex(TPL), TPL_SHA3, "cone: sha3 of tpl changed");
    assert_eq!(sha3_hex(INST), INST_SHA3, "cone: sha3 of inst changed");
    let t = zstd::stream::decode_all(TPL).expect("cone: tpl zstd");
    let i = zstd::stream::decode_all(INST).expect("cone: inst zstd");
    assert!(&t[0..4] == b"CTP2" && &i[0..4] == b"CIN3", "cone: CONE2 magic");
    let r32 = |b: &[u8], o: usize| u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]]) as usize;
    let nt = r32(&t, 4);
    let mut bodies: Vec<&[u8]> = Vec::with_capacity(nt);
    let mut o = 8;
    for _ in 0..nt {
        let l = r32(&t, o);
        bodies.push(&t[o + 4..o + 4 + l]);
        o += 4 + l;
    }
    assert_eq!(o, t.len(), "cone: tpl trailing bytes");
    let nr = r32(&i, 4);
    let (mut o, mut n, mut tof, mut top, mut ni) = (8usize, 0u64, 0u64, 0u32, 0u64);
    let (mut map, mut base): (Vec<u64>, u64) = (vec![], 0);
    for _ in 0..nr {
        let k = i[o];
        o += 1;
        match k {
            1 => map = delta_list(&i, &mut o),
            2 => base = varint(&i, &mut o),
            0 => {
                let tid = varint(&i, &mut o) as usize;
                let lanes: Vec<u32> = delta_list(&i, &mut o)
                    .into_iter()
                    .map(|x| if map.is_empty() { x as u32 } else { map[x as usize] as u32 })
                    .collect();
                let bits: Vec<u64> = delta_list(&i, &mut o).into_iter().map(|x| x + base).collect();
                let b = bodies[tid];
                assert_eq!(r32(b, 8), lanes.len(), "cone: instance lane count");
                assert_eq!(r32(b, 12), bits.len(), "cone: instance bit count");
                let id: &[u32] = if lanes.is_empty() { &[u32::MAX] } else { &lanes }; // non-empty map: no identity fallback
                let (a, c, tp) = emit_list_b(b, id, &|x| bits[x as usize], out);
                n += a;
                tof += c;
                top = top.max(tp);
                ni += 1;
            }
            _ => panic!("cone: bad CIN3 record {k}"),
        }
    }
    assert_eq!(o, i.len(), "cone: inst trailing bytes");
    eprintln!("cone: CONE2 {nt} templates, {ni} instances, {n} ops, {tof} CCX+CCZ ops, max qubit+1 {top}");
    (n, tof, top)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Replay a GLV2 list against Python vectors (gl/glv2.py dump_vectors, GLT2): a sim.rs-semantics simulator over
    /// 64-shot words with random HMR coins; final lanes must match, phase must be 0 when flagged.
    fn replay(glz: &[u8], vec_zst: &[u8]) {
        let raw = zstd::stream::decode_all(glz).unwrap();
        let mut ops = vec![];
        emit_list(&raw, &[], 0, &mut ops);
        let v = zstd::stream::decode_all(vec_zst).unwrap();
        assert_eq!(&v[0..4], b"GLT2");
        let r32 = |o: usize| u32::from_le_bytes([v[o], v[o + 1], v[o + 2], v[o + 3]]) as usize;
        let (nl, nib, nw, ph0) = (r32(4), r32(8), r32(12), r32(16) == 1);
        let rd = |k: usize| u64::from_le_bytes(v[20 + 8 * k..28 + 8 * k].try_into().unwrap());
        let nbits = crate::circuit::analyze_ops(ops.iter()).1 as usize;
        let mut seed = 0x9E3779B97F4A7C15u64;
        let mut rng = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for w in 0..nw {
            let mut q: Vec<u64> = (0..nl).map(|i| rd(i * nw + w)).collect();
            let mut b = vec![0u64; nbits.max(nib)];
            for i in 0..nib {
                b[i] = rd((nl + i) * nw + w);
            }
            let (mut phase, mut base, mut st) = (0u64, u64::MAX, vec![]);
            for op in &ops {
                use OperationType::*;
                let g = |x: QubitId| x.0 as usize;
                if op.kind == PushCondition {
                    st.push(base);
                    base &= b[op.c_condition.0 as usize];
                    continue;
                }
                if op.kind == PopCondition {
                    base = st.pop().unwrap();
                    continue;
                }
                let c = if op.c_condition.0 == u64::MAX { base } else { base & b[op.c_condition.0 as usize] };
                match op.kind {
                    X => q[g(op.q_target)] ^= c,
                    CX => q[g(op.q_target)] ^= c & q[g(op.q_control1)],
                    CCX => q[g(op.q_target)] ^= c & q[g(op.q_control1)] & q[g(op.q_control2)],
                    Z => phase ^= c & q[g(op.q_target)],
                    CZ => phase ^= c & q[g(op.q_target)] & q[g(op.q_control1)],
                    CCZ => phase ^= c & q[g(op.q_target)] & q[g(op.q_control1)] & q[g(op.q_control2)],
                    Swap => {
                        let d = c & (q[g(op.q_control1)] ^ q[g(op.q_target)]);
                        q[g(op.q_control1)] ^= d;
                        q[g(op.q_target)] ^= d;
                    }
                    Neg => phase ^= c,
                    Hmr | R => {
                        let coin = rng();
                        if op.kind == Hmr {
                            let t = op.c_target.0 as usize;
                            b[t] = (b[t] & !c) ^ (coin & c);
                        }
                        phase ^= q[g(op.q_target)] & coin & c;
                        q[g(op.q_target)] &= !c;
                    }
                    BitInvert => b[op.c_target.0 as usize] ^= c,
                    BitStore0 => b[op.c_target.0 as usize] &= !c,
                    BitStore1 => b[op.c_target.0 as usize] |= c,
                    _ => {}
                }
            }
            for i in 0..nl {
                assert_eq!(q[i], rd((nl + nib + i) * nw + w), "lane {i} word {w} differs from the Python replay");
            }
            if ph0 {
                assert_eq!(phase, 0, "phase not 0, word {w}");
            }
        }
    }

    #[test]
    fn glv2_shell0_replay_matches_python() {
        replay(include_bytes!("gl_data/cone_test/shell0.glz"), include_bytes!("gl_data/cone_test/shell0.vec.zst"));
    }

    #[test]
    fn glv2_negative_control_is_caught() {
        // one dropped op of shell0 must change the final lanes or the phase
        let glz = include_bytes!("gl_data/cone_test/shell0_drop.glz");
        let r = std::panic::catch_unwind(|| replay(glz, include_bytes!("gl_data/cone_test/shell0.vec.zst")));
        assert!(r.is_err(), "negative control not caught");
    }

    #[test]
    fn cone_tables_consistent() {
        for s in SPLICES {
            assert!(s.list < LISTS.len());
            let l = &LISTS[s.list];
            assert_eq!(sha3_hex(l.data), l.sha3, "{}", l.name);
        }
    }
}
