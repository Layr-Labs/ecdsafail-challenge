//! Gate-list loader for S-D' (P5_CHECKLIST.md s3 item 2): replays a flat X / CX / CCX list made by the Python
//! models (`gl/gldump.py`) at a fixed point of F's gate stream, through the builder's own `B::t`, so the gates are
//! counted, emitted, MAC-passed and graded like F's native gates. Lanes are F-local (the frame lane map of
//! `f_circuit` / MAP765), in the tree's G(a, b, c) order with NONE padding.
//! File (.glz) = zstd of: b"GLV1" | u32 n_gates | u32 n_lanes | u32 n_ccx | per gate u8 op (0 x, 1 cx, 2 ccx) +
//! that many u16 LE lanes. Every splice is checked on load: SHA3-256 of the file, n_gates, n_ccx, exact length.
use super::{B, G, GL, NONE};
use sha3::{Digest, Sha3_256};

/// Where a list is replayed inside `f_circuit`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum At {
    /// After the lane allocation and page_alloc, before `Machine::init`.
    FBegin,
    /// Just before `Machine::tick(t)`.
    BeforeTick(i32),
    /// After the last tick, before the MAC pass.
    FEnd,
    /// Replaces the gates of Machine::init and of every tick t >= START_CUT (the frame's start region): the list
    /// runs from F's input to the frame's state at boundary START_CUT - 1. The native code still runs (its software
    /// state, e.g. ring-Y relabels and allocations, is kept); only its gates are dropped.
    Start,
    /// Replaces the gates of ticks TAIL_CUT .. 3 (see TAIL_CUT).
    Tail,
}

/// The start region a Start splice replaces: ticks 511 .. START_CUT.
pub(super) const START_CUT: i32 = super::CUT_S;   // op-p5b: follows the start cut (was 448 = P0 / stage 2)
/// The tail region a Tail splice replaces: ticks TAIL_CUT .. 3 (the list runs boundary TAIL_CUT -> the state after
/// the last tick). Its lanes follow the frame's INITIAL labels (logical ring order, as trace2048): ring-Y lanes are
/// remapped onto the labels the frame holds at tick TAIL_CUT.
pub(super) const TAIL_CUT: i32 = super::CUT_T - 1;   // op-p5b: follows the tail cut (was 63)

/// Splice switches (op-p5, q765-v5-p5): a registered list is replayed only when its switch is on.
/// SPLICE_START: op-start's unpaged 773 start module (stage 2, graded 845 x 28,981,964 on 07fdc6b). false = native start.
pub(super) const SPLICE_START: bool = false;
/// SPLICE_TAIL: op-p5's unpaged 773 tail module at tier cap QM 29 (stage 3b, graded 859 x 28,810,112 on a69186a).
pub(super) const SPLICE_TAIL: bool = false;
/// op-p5b in-stream factor builds (COUNT ONLY, the stream is not correct): FAC_START 0 off, 1 empty, 2 M2a@432 (op-start3 s765_432
/// Fa 108), 3 M2b + M2c (handover432); FAC_TAIL 0 off, 1 empty, 2 tail-N stream + restore Z (s2coreZ 40/52 K16 L0 1), 3 + restore Lg.
pub(super) const FAC_START: u8 = 0;
/// SPLICE_START765 (op-p5b, SPLICE765.md): op-start3's full start hand-over at cut 432 on MAP765_v2 PHYSICAL lanes (commit 3089b7c,
/// list 0d54815): x0 on WALK508 -> the paged D16 frame at label 1431. Replayed through mod.rs start765 (physical -> label table and the
/// re-point of the frame's labels); needs ASM_START_PAGED.
pub(super) const SPLICE_START765: bool = true;
/// which start765 list: false = 300e503 (op-start3 40c6330, LT window [20, 51], op-check2 PASS; for the full 765 stream), true = 0d54815 (graded start-alone)
pub(super) const START765_OLD: bool = false;
pub(super) const FAC_TAIL: u8 = 0;

/// Row 764: the start765 list is replaced by the 764-slot sampled-register-allocation rewrite (`start765_s764`,
/// sampled-constant threshold 1 of 1,000,000 training shots; approximate). Default ON; LEFTW_S764=0 restores the parent list.
pub(super) fn s764_on() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("LEFTW_S764").map(|v| v.trim() != "0").unwrap_or(true))
}

fn is_on(s: &Splice) -> bool {
    if s.name == "start765_s764" {
        return SPLICE_START765 && s764_on();
    }
    if s.name == "start765_300e503" {
        return s.on && !s764_on();
    }
    s.on
}

pub(super) fn has(at: At) -> bool {
    SPLICES.iter().any(|s| is_on(s) && s.at == at)
}

pub(super) struct Splice {
    pub at: At,
    pub name: &'static str,
    pub data: &'static [u8],
    pub sha3: &'static str,
    pub on: bool,
}

/// The splice table. P0 form: one EMPTY list at FBegin (the stream must stay byte-identical to P0).
/// SD_BUILD stage 2: op-start's unpaged start module (team40/p2/join.py, narrow machine + gm-hand's v2 hand-over,
/// multiply tail 52) in place of the native slots 511..448.
pub(super) static SPLICES: &[Splice] = &[
    Splice {
        at: At::FBegin,
        name: "empty",
        data: include_bytes!("gl_data/empty.glz"),
        sha3: "2f07b74488ecb86b0e205cd9944a3e7636232d94fe2882f05a6a9b60790c7ebf",
        on: true,
    },
    Splice {
        at: At::Start,
        name: "start773_t52",
        data: include_bytes!("gl_data/start773_t52.glz"),
        sha3: "0654c89baf0eb1bb5051a502a376d1f4fd5f3528b4c81d3d3d2d5526bc63d834",
        on: SPLICE_START,
    },
    Splice {
        at: At::Tail,
        name: "tail773_q29",
        data: include_bytes!("gl_data/tail773_q29.glz"),
        sha3: "2e26949d4fbbfaf7d4ec7af5180ccd294e98f25da0a5edf49230af252424cb91",
        on: SPLICE_TAIL,
    },
    Splice {
        at: At::Start,
        name: "fac_empty_s",
        data: include_bytes!("gl_data/empty.glz"),
        sha3: "2f07b74488ecb86b0e205cd9944a3e7636232d94fe2882f05a6a9b60790c7ebf",
        on: FAC_START == 1,
    },
    Splice {
        at: At::Start,
        name: "fac_m2a",
        data: include_bytes!("gl_data/fac_m2a.glz"),
        sha3: "fc955118b7627c1c387e8b51e4e0f1c5f3f07bfdeb6056547a0f6c8f6fd8cc9a",
        on: FAC_START == 2,
    },
    Splice {
        at: At::Start,
        name: "fac_hand",
        data: include_bytes!("gl_data/fac_hand.glz"),
        sha3: "a0269c058a2d7ae757769aec249f688b52196af153264be5a3fc54f0906bd21a",
        on: FAC_START == 3,
    },
    Splice {
        at: At::Tail,
        name: "fac_empty_t",
        data: include_bytes!("gl_data/empty.glz"),
        sha3: "2f07b74488ecb86b0e205cd9944a3e7636232d94fe2882f05a6a9b60790c7ebf",
        on: FAC_TAIL == 1,
    },
    Splice {
        at: At::Tail,
        name: "fac_tz",
        data: include_bytes!("gl_data/fac_tz.glz"),
        sha3: "e1a7f706d7f82485f973ad2cfe8c9927849a4ff8d076a4b9ff5c2533050acfc6",
        on: FAC_TAIL == 2,
    },
    Splice {
        at: At::Tail,
        name: "fac_tlg",
        data: include_bytes!("gl_data/fac_tlg.glz"),
        sha3: "e9b749746e5286a39ce32516c4433ec611313491132d69c2ed8fc5dd30359c91",
        on: FAC_TAIL == 3,
    },
    Splice {
        at: At::Start,
        name: "start765_0d54815",
        data: include_bytes!("gl_data/start765_0d54815.glz"),
        sha3: "dc09ee7dc2a37be1052e6591bfd35e1b7392f161941121d0669a8efb37a86af8",
        on: SPLICE_START765 && START765_OLD,
    },
    Splice {
        at: At::Start,
        name: "start765_300e503",
        data: include_bytes!("gl_data/start765_300e503.glz"),
        sha3: "01666e318e75709830d67d08a96c60606f9a77403e055985433ec65fcbedd4cc",
        on: SPLICE_START765 && !START765_OLD,
    },
    Splice {
        at: At::Start,
        name: "start765_s764",
        data: include_bytes!("gl_data/start765_s764.glz"),
        sha3: "e98226a9f0889b05db47a5a72241a9ef5590d476601ba7ca28d44f9f064b0eb9",
        on: false,
    },
];

pub(super) struct GlFile {
    pub gates: GL,
    pub n_lanes: u32,
    pub n_ccx: u64,
}

pub(super) fn sha3_hex(z: &[u8]) -> String {
    let d = Sha3_256::digest(z);
    d.iter().map(|b| format!("{:02x}", b)).collect()
}

pub(super) fn decode(z: &[u8]) -> GlFile {
    let raw = zstd::stream::decode_all(z).expect("gl_loader: zstd decode");
    assert!(raw.len() >= 16 && &raw[0..4] == b"GLV1", "gl_loader: bad magic");
    let r32 = |o: usize| u32::from_le_bytes([raw[o], raw[o + 1], raw[o + 2], raw[o + 3]]);
    let r16 = |o: usize| u16::from_le_bytes([raw[o], raw[o + 1]]) as u32;
    let (n, nl, nccx) = (r32(4) as usize, r32(8), r32(12) as u64);
    let mut g: GL = Vec::with_capacity(n);
    let (mut o, mut c, mut top) = (16usize, 0u64, 0u32);
    for _ in 0..n {
        let op = raw[o];
        o += 1;
        let gate = match op {
            0 => G(r16(o), NONE, NONE),
            1 => G(r16(o), r16(o + 2), NONE),
            2 => {
                c += 1;
                G(r16(o), r16(o + 2), r16(o + 4))
            }
            _ => panic!("gl_loader: bad op {op}"),
        };
        o += 2 * (op as usize + 1);
        for q in [gate.0, gate.1, gate.2] {
            if q != NONE {
                top = top.max(q + 1);
            }
        }
        g.push(gate);
    }
    assert_eq!(o, raw.len(), "gl_loader: trailing bytes");
    assert_eq!(c, nccx, "gl_loader: CCX count");
    assert!(top <= nl, "gl_loader: lane beyond n_lanes");
    GlFile { gates: g, n_lanes: nl, n_ccx: c }
}

/// GLV1 encoder (inverse of `decode`): X / CX / CCX gates on u16 lanes, zstd level 19.
pub(super) fn encode(g: &[G], n_lanes: u32) -> Vec<u8> {
    let mut raw: Vec<u8> = b"GLV1".to_vec();
    let nccx = g.iter().filter(|x| x.2 != NONE).count() as u32;
    for v in [g.len() as u32, n_lanes, nccx] { raw.extend_from_slice(&v.to_le_bytes()); }
    for x in g {
        let (op, ls): (u8, Vec<u32>) = if x.2 != NONE { (2, vec![x.0, x.1, x.2]) } else if x.1 != NONE { (1, vec![x.0, x.1]) } else { (0, vec![x.0]) };
        raw.push(op);
        for q in ls { assert!(q < 65536, "gl_loader: lane beyond u16"); raw.extend_from_slice(&(q as u16).to_le_bytes()); }
    }
    zstd::stream::encode_all(&raw[..], 19).expect("gl_loader: zstd encode")
}

/// Replay every list registered at `at`, with every lane passed through `map`.
pub(super) fn splice_mapped(at: At, b: &mut B, map: &dyn Fn(u32) -> u32) {
    for s in SPLICES.iter().filter(|s| is_on(s) && s.at == at) {
        assert_eq!(sha3_hex(s.data), s.sha3, "gl_loader: sha3 of splice '{}' changed", s.name);
        let f = decode(s.data);
        if f.n_lanes > b.next {
            b.next = f.n_lanes;
        }
        let m = |q: u32| if q == NONE { NONE } else { map(q) };
        let g: GL = f.gates.iter().map(|g| G(m(g.0), m(g.1), m(g.2))).collect();
        b.t(&g);
        eprintln!("gl_loader: splice '{}' at {:?} (lane map): {} gates, {} CCX, lanes {}", s.name, at, g.len(), f.n_ccx, f.n_lanes);
    }
}

/// Replay every list registered at `at` into the builder. Lanes the list uses beyond the builder's allocation
/// raise `b.next`, so the peak counts them.
pub(super) fn splice(at: At, b: &mut B) {
    for s in SPLICES.iter().filter(|s| is_on(s) && s.at == at) {
        let h = sha3_hex(s.data);
        assert_eq!(h, s.sha3, "gl_loader: sha3 of splice '{}' changed", s.name);
        let f = decode(s.data);
        if f.n_lanes > b.next {
            b.next = f.n_lanes;
        }
        b.t(&f.gates);
        eprintln!("gl_loader: splice '{}' at {:?}: {} gates, {} CCX, lanes {}", s.name, at, f.gates.len(), f.n_ccx, f.n_lanes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sim(g: &[G], st: &mut [Vec<u64>]) {
        let nw = st[0].len();
        for gate in g {
            let G(a, b0, c) = *gate;
            for w in 0..nw {
                if b0 == NONE {
                    st[a as usize][w] = !st[a as usize][w];
                } else if c == NONE {
                    let v = st[a as usize][w];
                    st[b0 as usize][w] ^= v;
                } else {
                    let v = st[a as usize][w] & st[b0 as usize][w];
                    st[c as usize][w] ^= v;
                }
            }
        }
    }

    fn vectors(z: &[u8]) -> (Vec<Vec<u64>>, Vec<Vec<u64>>) {
        let raw = zstd::stream::decode_all(z).unwrap();
        assert_eq!(&raw[0..4], b"GLT1");
        let r32 = |o: usize| u32::from_le_bytes([raw[o], raw[o + 1], raw[o + 2], raw[o + 3]]) as usize;
        let (nl, nw) = (r32(4), r32(8));
        let rd = |base: usize| -> Vec<Vec<u64>> {
            (0..nl)
                .map(|l| (0..nw).map(|w| {
                    let o = base + 8 * (l * nw + w);
                    u64::from_le_bytes(raw[o..o + 8].try_into().unwrap())
                }).collect())
                .collect()
        };
        let a = rd(12);
        let b = rd(12 + 8 * nl * nw);
        assert_eq!(raw.len(), 12 + 16 * nl * nw);
        (a, b)
    }

    #[test]
    fn empty_splice_is_empty() {
        let f = decode(include_bytes!("gl_data/empty.glz"));
        assert_eq!((f.gates.len(), f.n_lanes, f.n_ccx), (0, 0, 0));
        assert_eq!(sha3_hex(include_bytes!("gl_data/empty.glz")), SPLICES[0].sha3);
    }

    /// The stage-2 start module (773 layout, 845 lanes) replayed on 256 random inputs in the frame's input form:
    /// every lane equal to the Python simulation (gl/gldump.py start773).
    #[test]
    fn start773_replay_matches_python() {
        let z: &[u8] = include_bytes!("gl_data/start773_t52.glz");
        assert_eq!(sha3_hex(z), SPLICES[1].sha3);
        let f = decode(z);
        assert_eq!((f.gates.len(), f.n_lanes, f.n_ccx), (2_756_012, 845, 905_494));
        let (mut st, exp) = vectors(include_bytes!("gl_data/start773_t52.vec.zst"));
        assert_eq!(st.len(), 845);
        sim(&f.gates, &mut st);
        let bad: usize = (0..845).map(|l| (0..st[l].len()).map(|w| (st[l][w] ^ exp[l][w]).count_ones() as usize).sum::<usize>()).sum();
        eprintln!("start773 replay: {} gates, {} CCX, 845 lanes x {} shots, differing bits {}", f.gates.len(), f.n_ccx, 64 * st[0].len(), bad);
        assert_eq!(bad, 0);
    }

    /// op-start's M2a + M2b0 list (765 layout) replayed in Rust on 256 random inputs: every lane equal, bit for bit,
    /// to the Python simulation that wrote the vectors (gl/gldump.py m2a).
    #[test]
    fn m2a_765_replay_matches_python() {
        let z: &[u8] = include_bytes!("gl_data/m2a_765.glz");
        assert_eq!(sha3_hex(z), "799470726f31e7cd44aed3d45c98da889ca4f571514a51c8fb1dbb786979d794");
        let f = decode(z);
        assert_eq!((f.gates.len(), f.n_lanes, f.n_ccx), (1_948_143, 765, 595_983));
        let (mut st, exp) = vectors(include_bytes!("gl_data/m2a_765.vec.zst"));
        assert_eq!(st.len(), 765);
        sim(&f.gates, &mut st);
        let mut bad = 0usize;
        for l in 0..765 {
            for w in 0..st[l].len() {
                bad += (st[l][w] ^ exp[l][w]).count_ones() as usize;
            }
        }
        eprintln!("m2a_765 replay: {} gates, {} CCX, 765 lanes x {} shots, differing bits {}", f.gates.len(), f.n_ccx, 64 * st[0].len(), bad);
        assert_eq!(bad, 0);
    }
    #[test]
    fn start765_replay_matches_python() {
        let z: &[u8] = include_bytes!("gl_data/start765_0d54815.glz");
        assert_eq!(sha3_hex(z), "dc09ee7dc2a37be1052e6591bfd35e1b7392f161941121d0669a8efb37a86af8");
        let f = decode(z);
        assert_eq!((f.gates.len(), f.n_ccx), (5_257_119, 1_884_887));
        let (mut st, exp) = vectors(include_bytes!("gl_data/start765_0d54815.vec.zst"));
        assert_eq!(st.len(), 765);
        sim(&f.gates, &mut st);
        let mut bad = 0usize;
        for l in 0..765 {
            for w in 0..st[l].len() {
                bad += (st[l][w] ^ exp[l][w]).count_ones() as usize;
            }
        }
        eprintln!("start765 replay: {} gates, {} CCX, lanes {}, {} shots, differing bits {}", f.gates.len(), f.n_ccx, f.n_lanes, 64 * st[0].len(), bad);
        assert_eq!(bad, 0);
    }
    #[test]
    fn start765b_replay_matches_python() {
        let z: &[u8] = include_bytes!("gl_data/start765_300e503.glz");
        assert_eq!(sha3_hex(z), "01666e318e75709830d67d08a96c60606f9a77403e055985433ec65fcbedd4cc");
        let f = decode(z);
        assert_eq!((f.gates.len(), f.n_ccx), (5_259_024, 1_886_393));
        let (mut st, exp) = vectors(include_bytes!("gl_data/start765_300e503.vec.zst"));
        assert_eq!(st.len(), 765);
        sim(&f.gates, &mut st);
        let mut bad = 0usize;
        for l in 0..765 {
            for w in 0..st[l].len() {
                bad += (st[l][w] ^ exp[l][w]).count_ones() as usize;
            }
        }
        eprintln!("start765b replay: {} gates, {} CCX, lanes {}, {} shots, differing bits {}", f.gates.len(), f.n_ccx, f.n_lanes, 64 * st[0].len(), bad);
        assert_eq!(bad, 0);
    }

    /// leftW tooling (ignored): encode a raw u16-triple gate list (LEFTW_TRI, 0xFFFF = NONE) as GLV1 into LEFTW_OUT.
    #[test]
    #[ignore]
    fn leftw_encode() {
        let tri = std::fs::read(std::env::var("LEFTW_TRI").unwrap()).unwrap();
        let g: GL = tri.chunks(6).map(|c| {
            let q = |i: usize| { let v = u16::from_le_bytes([c[2 * i], c[2 * i + 1]]) as u32; if v == 0xFFFF { NONE } else { v } };
            G(q(0), q(1), q(2))
        }).collect();
        let z = encode(&g, 765);
        let f = decode(&z);
        eprintln!("leftw_encode: {} gates {} CCX lanes {} bytes {} sha3 {}", f.gates.len(), f.n_ccx, f.n_lanes, z.len(), sha3_hex(&z));
        std::fs::write(std::env::var("LEFTW_OUT").unwrap(), &z).unwrap();
    }

    /// leftW: the 764-slot rewrite of the start list on the tree's own 256 random-input vectors (same vectors as the
    /// parent list): every lane equal, bit for bit, to the Python simulation. Phys lane 762 (logical 745) is never touched.
    #[test]
    fn start765_s764_replay_matches_python() {
        let z: &[u8] = include_bytes!("gl_data/start765_s764.glz");
        let f = decode(z);
        eprintln!("start765_s764: sha3 {}", sha3_hex(z));
        assert_eq!(sha3_hex(z), SPLICES.iter().find(|s| s.name == "start765_s764").unwrap().sha3);
        assert_eq!(f.gates.iter().filter(|g| g.0 == 762 || g.1 == 762 || g.2 == 762).count(), 0, "phys 762 touched");
        let (mut st, exp) = vectors(include_bytes!("gl_data/start765_300e503.vec.zst"));
        assert_eq!(st.len(), 765);
        sim(&f.gates, &mut st);
        let mut bad = 0usize;
        let mut badshots = std::collections::BTreeSet::new();
        for l in 0..765 {
            for w in 0..st[l].len() {
                let d = st[l][w] ^ exp[l][w];
                bad += d.count_ones() as usize;
                for b in 0..64 { if d >> b & 1 == 1 { badshots.insert(64 * w + b); } }
            }
        }
        eprintln!("start765_s764 replay: {} gates, {} CCX, lanes {}, {} shots, differing bits {}, failing shots {} {:?}", f.gates.len(), f.n_ccx, f.n_lanes, 64 * st[0].len(), bad, badshots.len(), badshots);
        assert_eq!(bad, 0);
    }
}
