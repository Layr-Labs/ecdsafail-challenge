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
/// START765_B1 (ob-ends lever B, 2026-11-13): the IIa-fixed start (s765_432 M2a + p2s3/framemap432c: N core gated by B_0, restore 'Lg' + switch
/// dropped, ib-1 Class II circuit for IIa + IIb) with odinfree's rewritten restore-S1 stretch re-spliced (NOTES/v8/pivot/ends/splice_b.py).
/// 1,481,211 CCX vs e4's 1,524,474; equal to e4 on all 765 lanes on 1,048,576 + 4,194,304 random shots. false = e4 (base sha).
pub(super) const START765_B1: bool = false;
/// START765_D1 (ob-ends lever H, 2026-11-13): one shared stream for all four classes, ib-1 dropped (NOTES/v8/pivot/ends: s2n432d core with
/// fastdiv restores + class-II restore on a dirty PAS limb, fold432d, framemap432d with ib-1's Hensel on FREE8). 1,356,828 CCX vs b1's
/// 1,481,211; equal to b1 on all 765 lanes on 65,536 random shots. Takes precedence over START765_B1. false = base sha.
pub(super) const START765_D1: bool = false;
/// START765_D2 (ob-ends): d1 with M2a from ob-tail's clean-lane narrow machine (NOTES/v8/pivot/clean/s765c.py CLMAX 110): AND compute /
/// uncompute markers (GLV1 ops 3 / 4) on structurally clean pools, T 1,179,511 / pass (ops 2-4: 1,356,828); equal to d1 on 32,768 shots,
/// 0 marker violations. Takes precedence over D1 / B1. false = base sha.
pub(super) const START765_D2: bool = false;
/// START765_D3 (ob-ends): d2 with the class-II restore's dirty-limb multiply limited to its 16 limb rows (fastdiv nz) and both of its
/// fastdiv calls in thermometer form (fold 508/508): T 1,158,943 / pass; equal to d2 on 32,768 shots. Takes precedence. false = base sha.
pub(super) const START765_D3: bool = false;
/// START765_D4 (ob-ends): d3 with ob-tail's updated clean-lane machine (s765c CLMAX 110 + cl.cadd_h clean controlled adds):
/// T 1,083,800 / pass (M2a 649,406); equal to d3 on 32,768 shots, 0 marker violations. Takes precedence. false = base sha.
pub(super) const START765_D4: bool = true;
/// v764: OURS' start765_s764 (leftST recolour of 300e503 that never touches phys lane 762); takes the place of D4.
pub(super) const START765_S764: bool = false;
pub(super) const FAC_TAIL: u8 = 0;

/// AND markers (ob-tail, clean-lane primitives): GLV1 op 3 = AND compute (CCX onto a clean |0> target), op 4 = AND uncompute
/// (CCX whose target equals the AND of its controls). Carried in F's GL as flag bits on the target field; MarkerWalk emits
/// them as fd2 AndC / AndU (compute = CCX, uncompute = HMR + CZ under the outcome; roles swapped on an inverse pass).
pub(super) const ANDC: u32 = 1 << 30;
pub(super) const ANDU: u32 = 1 << 29;
pub(super) const AFLAGS: u32 = ANDC | ANDU;
/// (lane, flag) of a gate field: flags only ever sit on a CCX target.
pub(super) fn lane_of(q: u32) -> u32 { if q == NONE { NONE } else { q & !AFLAGS } }
pub(super) fn flag_of(q: u32) -> u32 { if q == NONE { 0 } else { q & AFLAGS } }
/// Relabel a gate through `m`, keeping an AND flag on the target.
pub(super) fn relabel(g: &G, m: &dyn Fn(u32) -> u32) -> G {
    let t = if g.2 == NONE { NONE } else { m(lane_of(g.2)) | flag_of(g.2) };
    G(m(g.0), m(g.1), t)
}

pub(super) fn has(at: At) -> bool {
    SPLICES.iter().any(|s| s.on && s.at == at)
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
        data: &[],
        sha3: "0654c89baf0eb1bb5051a502a376d1f4fd5f3528b4c81d3d3d2d5526bc63d834",
        on: SPLICE_START,
    },
    Splice {
        at: At::Tail,
        name: "tail773_q29",
        data: &[],
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
        data: &[],
        sha3: "fc955118b7627c1c387e8b51e4e0f1c5f3f07bfdeb6056547a0f6c8f6fd8cc9a",
        on: FAC_START == 2,
    },
    Splice {
        at: At::Start,
        name: "fac_hand",
        data: &[],
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
        data: &[],
        sha3: "e1a7f706d7f82485f973ad2cfe8c9927849a4ff8d076a4b9ff5c2533050acfc6",
        on: FAC_TAIL == 2,
    },
    Splice {
        at: At::Tail,
        name: "fac_tlg",
        data: &[],
        sha3: "e9b749746e5286a39ce32516c4433ec611313491132d69c2ed8fc5dd30359c91",
        on: FAC_TAIL == 3,
    },
    Splice {
        at: At::Start,
        name: "start765_0d54815",
        data: &[],
        sha3: "dc09ee7dc2a37be1052e6591bfd35e1b7392f161941121d0669a8efb37a86af8",
        on: SPLICE_START765 && START765_OLD,
    },
    Splice {
        at: At::Start,
        name: "start765_300e503",
        data: &[],
        sha3: "caa071f481c88330927c7c8a12e836bd4928354ccd2f6ca08c130d4b6ab6a510",
        on: SPLICE_START765 && !START765_OLD && !START765_S764 && !START765_B1 && !START765_D1 && !START765_D2 && !START765_D3 && !START765_D4,
    },
    Splice {
        at: At::Start,
        name: "start765_b1",
        data: &[],
        sha3: "775accc04e6eb3bae8f82966fdc4986b67a4e21a6466ff277a40ab1e68b04697",
        on: SPLICE_START765 && !START765_OLD && START765_B1 && !START765_D1 && !START765_D2 && !START765_D3 && !START765_D4,
    },
    Splice {
        at: At::Start,
        name: "start765_d1",
        data: &[],
        sha3: "a039e07bedf180f7af74a1ddf18f9bf0b21333d48a76d9693b19a69ad31dc64d",
        on: SPLICE_START765 && !START765_OLD && START765_D1 && !START765_D2 && !START765_D3 && !START765_D4,
    },
    Splice {
        at: At::Start,
        name: "start765_d2",
        data: &[],
        sha3: "f7453fe2c2b316e3ddfcdab21777abc3a3ff1ece4aaf5cd7c0295f27bc1c407a",
        on: SPLICE_START765 && !START765_OLD && START765_D2 && !START765_D3 && !START765_D4,
    },
    Splice {
        at: At::Start,
        name: "start765_d3",
        data: &[],
        sha3: "c871418ed13756aa041125a5098070714f6bf52305ed32dff53653a3bc15ae3d",
        on: SPLICE_START765 && !START765_OLD && START765_D3 && !START765_D4,
    },
    Splice {
        at: At::Start,
        name: "start765_d4",
        data: include_bytes!("gl_data/start764_d4_nomark.glz"),
        // fb-r7d: the d4 list with its M2a prefix replaced by the NARROW NATIVE F start machine (NOTES/v9/r7_d/nfs_start.py,
        // dump_nfstart.py: start765_nf104, T 799,488 per pass vs d4 1,083,800; equal to d4 on its 256 vectors, all 765 lanes).
        sha3: "cef307c33cb5fadcdb9269639f358c767922629d433b9fd846e2dc9879883cec",
        on: SPLICE_START765 && !START765_OLD && START765_D4,
    },
    Splice {
        at: At::Start,
        name: "start765_s764",
        data: &[],
        sha3: "5676f9f6256dd10b0d2d41779097ef8dbfffbd82039cd95a2b388de5a6c1b8e1",
        on: SPLICE_START765 && !START765_OLD && START765_S764 && !START765_D4,
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
            3 | 4 => {
                c += 1;
                G(r16(o), r16(o + 2), r16(o + 4) | if op == 3 { ANDC } else { ANDU })
            }
            _ => panic!("gl_loader: bad op {op}"),
        };
        o += 2 * (op.min(2) as usize + 1);
        for q in [gate.0, gate.1, gate.2] {
            if q != NONE {
                top = top.max(lane_of(q) + 1);
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
    for s in SPLICES.iter().filter(|s| s.on && s.at == at) {
        assert_eq!(sha3_hex(s.data), s.sha3, "gl_loader: sha3 of splice '{}' changed", s.name);
        let f = decode(s.data);
        if f.n_lanes > b.next {
            b.next = f.n_lanes;
        }
        let m = |q: u32| if q == NONE { NONE } else { map(q) };
        let g: GL = f.gates.iter().map(|g| relabel(g, &m)).collect();
        b.t(&g);
        eprintln!("gl_loader: splice '{}' at {:?} (lane map): {} gates, {} CCX, lanes {}", s.name, at, g.len(), f.n_ccx, f.n_lanes);
    }
}

/// Replay every list registered at `at` into the builder. Lanes the list uses beyond the builder's allocation
/// raise `b.next`, so the peak counts them.
pub(super) fn splice(at: At, b: &mut B) {
    for s in SPLICES.iter().filter(|s| s.on && s.at == at) {
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
    fn start765_b1_replay_matches_python() {
        let z: &[u8] = include_bytes!("gl_data/start765_b1.glz");
        assert_eq!(sha3_hex(z), "775accc04e6eb3bae8f82966fdc4986b67a4e21a6466ff277a40ab1e68b04697");
        let f = decode(z);
        assert_eq!((f.gates.len(), f.n_lanes, f.n_ccx), (4_383_412, 765, 1_481_211));
        let (mut st, exp) = vectors(include_bytes!("gl_data/start765_b1.vec.zst"));
        assert_eq!(st.len(), 765);
        sim(&f.gates, &mut st);
        let bad: usize = (0..765).map(|l| (0..st[l].len()).map(|w| (st[l][w] ^ exp[l][w]).count_ones() as usize).sum::<usize>()).sum();
        eprintln!("start765_b1 replay: differing bits {}", bad);
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
}
