//! Low-qubit point addition around a self-inverse Euclid inverter F: |x>|0> -> |a>|par>|0>, a = +-1/x mod p.
//! F is an exact restoring-row Euclid walk with no history tape: quotient digits grow in the freed top lanes of the
//! dividend ring and are consumed by the inverse of the same row on the cofactors, so the reverse pass is the reversed
//! gate list. The N ring is its own clock: its root rises one wire per slot and acts when it reaches the top wire, so
//! the only length register is E = F - L_frame mod 32. Translated from emit/srm2.py + emit/pa2.py.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};

const N: usize = 256;
const W: usize = N + 1;
const NONE: u32 = u32::MAX;
const EB: usize = 2;
/// Clean lane for the AND of many controls inside F.
const ZB: usize = if PAGE_G { 1 } else { 0 };
/// the clean AND lane (first lane allocated); P1 uses it also as the sandwich's AND lane Z (MCX into it: Barenco)
const ZB_LANE: u32 = 512;
/// f_circuit's y0, y1 (ring Y's two non-x lanes at F's input): 513, 514 when ZB is on
const Y0_LABEL: u32 = 512 + ZB as u32;
const Y1_LABEL: u32 = 513 + ZB as u32;
static IN_F: AtomicBool = AtomicBool::new(false);
/// P1: the ZB lane is held (the sandwich's AND lane): every MCX takes the Barenco form meanwhile.
static ZB_BUSY: AtomicBool = AtomicBool::new(false);
/// debug marks (trace only): slot DBG_T records (100000 + k, gate index) at mk(t, k)
static DBG_T: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(-1);
static DBG_M: std::sync::Mutex<Vec<(i32, usize)>> = std::sync::Mutex::new(Vec::new());
const PIW: usize = 48;
const ECAP: i32 = 26;
/// SD1 (tier split, v4 SDP.md section 3): first big class that waits for a slot 0 mod 16 (its offset has four bits).
/// 0 = off: every big class acts at the next slot 0 mod 8, which is the stream of d4dd7eb1. NOT YET WIRED beyond
/// big_pairs11: see notes v4/SD1_progress.md before setting it.
const TIER_LONG: i32 = 16;
/// L-C banded cadence (op-layout 1e952d1, op-check 09fea3e): with TIER_LONG > 0 a big arrival at slot tn in
/// [CUT_T, CUT_S - 17] that turns out to be a long class (e >= TIER_LONG) waits for a slot 0 mod 16 (wait w up to 15, its
/// 4th bit on the lane W4); every other arrival keeps cadence 8 (the 16 slots above each cut, and the native ends). W4 is
/// set only by those arrivals and cleared at their act slot, so it is 0 at every boundary >= CUT_S - 16 and < CUT_T.
fn long16(tn: i32) -> bool { TIER_LONG > 0 && (CUT_T..=CUT_S - 17).contains(&tn) }
/// cubes over the (hi or u or v mod 16, w) points of big-class cases: p = h | w << 4, p < 256; bit 7 of p (w >= 8) is lane w4
fn hw_cubes(on: &[usize], off: &[usize], lanes: &[u32], w4: u32) -> Vec<Vec<Lit>> {
    let lit = |c: &Cubes| -> Vec<Vec<Lit>> { c.iter().map(|x_| x_.iter().map(|&(v, bt)| (lanes[v], bt == 1)).collect()).collect() };
    let (mut on2, mut off2) = ([0u128; 2], [0u128; 2]);
    for &p_ in on { on2[p_ >> 7] |= 1u128 << (p_ & 127); }
    for &p_ in off { off2[p_ >> 7] |= 1u128 << (p_ & 127); }
    let vs = [0usize, 1, 2, 3, 4, 5, 6];
    if on2[1] == 0 && off2[1] == 0 {
        return if on2[0] == 0 { vec![] } else { lit(&dtree(on2[0], off2[0], &vs, 3)) };
    }
    let mut out: Vec<Vec<Lit>> = vec![];
    for sd in 0..2usize {
        if on2[sd] == 0 { continue; }
        if on2[1 - sd] == 0 && on2[sd] & off2[1 - sd] == 0 {
            return lit(&dtree(on2[sd], off2[sd] | off2[1 - sd], &vs, 3));
        }
        for mut c in lit(&dtree(on2[sd], off2[sd], &vs, 3)) {
            c.push((w4, sd == 1));
            out.push(c);
        }
    }
    out
}
/// P5 shell (op-p5, branch q765-v5-p5shell): the frogdrop product stage at s = 0, w = 5 (module fd2, transplanted
/// from q765-v4-shell 58658f3) around this tree's walk F. false = the stream of d4dd7eb1 (S3 shell, sha of P0).
const P5SHELL: bool = true;
/// P1 (v5 TEAM_40M, op-build): fixed page of the low words between the cuts. false = the stream of d4dd7eb1.
/// Step (a): `page_in` at the boundary below slot T + 1 (T in PAGE_CUTS) and its inverse right after it, no page work.
const PAGE: bool = false;
const PAGE_D: usize = 13;
/// D11 converter: true = the frame runs at page width PAGE_D (set 11) while page_in / page_out, start765,
/// phys765 and the tail stay at PAGE_DI = 16; a converter after page_in(CUT_S - 1) lifts bits 11..15 of the implicit word
/// (K2-LIFT), routes the explicit tops by B's parity and reopens a 10-lane hole per ring at the shot's junction; its inverse
/// runs before page_out(CUT_T - 1). false = every width is PAGE_D (the stream of ae715bcf).
const CONV: bool = true;
/// module-interface page width (= PAGE_D when CONV is off)
const PAGE_DI: usize = if CONV { 16 } else { PAGE_D };
/// ring width at the interfaces after page_in's narrowing
const WHI: usize = W - 2 * PAGE_DI;
/// insertion index of the 10 converter lanes in the narrowed (WHI) ring lists, (ring X, ring Y), at the start and tail cuts
/// (checked in a gate-level model: exact at these values; insertion at the top fails)
const CONV_K_S: (usize, usize) = (27, 25);
const CONV_K_T: (usize, usize) = (203, 187);
/// Catalyst-swap hop: the K2 half's in-place p/B in the frame sandwich by the catalyst swap
/// (D - 1 passenger lanes read as an odd g: X <- X g, G <- G / X, X <- X G, swap) instead of invp. HOPA: dirt restored
/// inside the hop (drop-in). HOPP (implies the hop): the third multiply is left to the post (the catalyst lanes hold B g
/// between pre and post; post = the reversed gates). Both false = the K2 half of ae715bcf.
const HOPA: bool = false;
const HOPP: bool = true;
static HOP_SEEN: AtomicBool = AtomicBool::new(false);
/// P5 cut slots (multiples of 8): the start module covers the slots t >= CUT_S, the tail module the slots t < CUT_T;
/// the paged frame runs slots CUT_S - 1 .. CUT_T (page_in at the boundary below slot CUT_S, page_out below CUT_T).
const CUT_S: i32 = 432;
const CUT_T: i32 = 80;
const PAGE_CUTS: [i32; 2] = [CUT_S - 1, CUT_T - 1];
/// the even / odd frame slots between the cuts (paged with PAGE_G)
fn mid_even(t: i32) -> bool { (CUT_T..=CUT_S - 2).contains(&t) }
fn mid_odd(t: i32) -> bool { (CUT_T + 1..=CUT_S - 1).contains(&t) }
/// P1 step (b), test mode: the V rows of the low classes (e = 2..9) at the even slots 446..64 run through the page
/// (KT5 sliding window), with a per-slot local gather of the acting shots' A and B low words (the rest stays native).
const PAGE_V: bool = false;
/// P1 step (b2), test mode (implies PAGE_V's V rows): the four low words of the acting low-class shots are gathered per
/// slot, the implicit cofactor word is erased, and the C rows run through the page behind the K2 sandwich.
const PAGE_C: bool = false;
/// P1 global page: page_in at the boundary below slot 448, page_out (its inverse) at the boundary below slot 64; in
/// between every slot is page-aware: low classes and e = 0 through the page, e = 1 rows and the big classes still
/// native behind a per-slot controlled unpage / repage (counter 6), a page swap and format switch at every act.
const PAGE_G: bool = true;
/// P5 step 1: with the global page, the rings are narrowed to WH = 257 - 2D wires between the cuts (page_in also
/// closes each ring's 2D-lane hole; the top 2D lanes of each ring are freed). Needs PAGE_G.
const PAGE_N: bool = true;
/// P5 lever L-D (op-lever's lever 1, team40/flags/LEVERS.md): the class flags of the six even-slot page sites (V-win-in,
/// V rows 0..8, V-win-out, cw, C rows 9..1, C-win-out) as thermometer-ladder schedules on d, ZB (and F in the V phase)
/// instead of one fresh AND per class and use (fl_cls / fl_cit). Needs PAGE_G; used where the classes 2..9 all act.
const LADDER: bool = true;
/// P5 frame lever 1 (op-build2): the format switch of post_page (controlled D-bit multiply / divide) with ZB as its one
/// clean lane (ZB is 0 at every post: the sandwich's post has run): each doubly-controlled add is AND + 1 adder instead of
/// the dirty complement trick's 2 adders. AND pairs are emitted as CCX.
const POST_ZB: bool = true;
/// P5 765 assembly (op-p5b, P5_CHECKLIST s9 A2): with a Start splice that ends in the PAGED form at the boundary below CUT_S (M2e at 431),
/// page_in(CUT_S - 1) emits no gates (its software state, the PAGE_N narrowing and W4, still runs).
const ASM_START_PAGED: bool = true;
/// P5 765 assembly (A3): with a Tail splice, page_out(CUT_T - 1) and the re-widening belong to the tail region (the list unpacks the page
/// itself, M3a): the region's gate index is taken before the cut; its labels (y_tail) after it, as before.
const ASM_TAIL_UNPACK: bool = false;
/// op-p5b diagnostic (count builds only): print the frame's labels at the cuts and every label used by gates strictly between
/// page_in(CUT_S - 1) and page_out(CUT_T - 1) (lines ASMDUMP), to build the 765 relabel (A6). No gate changes.
const ASM_DUMP: bool = false;
/// start765 mode (op-p5b): true = after the list, MOVE its output by CX swaps (no Toffoli) onto the native frame's own labels at 1431,
/// so the frame from 431 on is the native one (start-alone fault split, P5_CHECKLIST s8); false = re-point the frame's labels at the
/// list's (the 765 form; needs the 765 tail so that F's output lands on the labels 0..511 + y0, y1).
const START765_SWAP: bool = false;
/// 765 assembly test mode (op-p5b): with start765 in re-point mode and the NATIVE tail, move F's end data by CX swaps onto the labels of
/// the 765 end form (ring Y on phys Y773 = [512, 513, 0..254] through the label table at 79, PAR on the re-pointed par), so the start
/// re-point + label compaction are graded before the real tail list exists (width > 765: the native tail uses T2 and the ring tops).
const TAIL_SWAP765: bool = false;
/// 765 assembly: renumber the labels >= 512 used by F densely (fc.next = 512 + used), so the emitter allocates only used lanes.
const ASM765_COMPACT: bool = true;
/// TAIL765 = 3 (op-p5b): the registered tail list gl_data/tail765.glz + gl_data/tail765.lay (include_bytes, sha3 checked).
const TAIL765_SHA3: &str = "718d206b1292ce8693f22e17c94bcef182a57a264da6203ff53291f48ed40890";
/// P5 frame lever 2 (op-build2, team40/p1/LEVER2.md): the big-class slide flags (after V row k by u, before C row k by
/// v = f - t/2) as a demux walk on the 4 hosted bits (V: prefix lanes F and ZB, C: ZB with d as aux) instead of one fresh
/// decision-tree AND per group; groups with inactive cases of the same u / v get w cubes on the leaf.
const SLIDE_LAD: bool = true;
/// LEVER2 C side: its prefix A (cl & 2 bits on ZB) by cc_core with d as the aux lane (off: Barenco on ZB)
const SLIDE_LAD_CA: bool = true;
/// P5 765 tail splice (op-build2; contract team40/p5b/SPLICE765.md): the region page_out(CUT_T - 1) + ticks CUT_T - 1 .. 3 in
/// MAP765_v2 PHYSICAL lanes (phys765: the frame state at label CUT_T - 1). 0 off; 1 = dump the native region (macro pass off)
/// to TAIL765_DUMP + its end ring layout (.lay); 2 = splice the GLV1 list TAIL765_LIST in its place, then rings X / Y
/// relabelled from TAIL765_LIST.lay ("Y <phys...>", "X <phys...>"; a real tail765 list: Y = Y773 [512, 513, 0..254]).
const TAIL765: u8 = 3;
const TAIL765_DUMP: &str = "/tmp/q765-op-build2/tail765_rt.glz";
const TAIL765_LIST: &str = "/tmp/q765-op-build2/tail765_rt.glz";
static TAIL765_DATA: &[u8] = include_bytes!("gl_data/tail765.glz");
/// leftW: LEFTW_T764=1 swaps the registered tail list for gl_data/tail765_t764.glz (the 764-slot tail rewrite; MERGE.md). Until leftT
/// delivers it that file is a byte copy of tail765.glz (so the switch is a no-op self-test). Default OFF = parent list.
static TAIL765_T764_DATA: &[u8] = include_bytes!("gl_data/tail765_t764.glz");
const TAIL765_T764_SHA3: &str = "c7000d1686a1d22b8beebc190c55b67121bf7a6c36b5044ad5d1b243ccaf53a9"; // MERGE.md rewrites this line
fn leftw_t764() -> bool { std::env::var("LEFTW_T764").map(|v| v.trim() != "0").unwrap_or(true) }
static TAIL765_LAY: &str = include_str!("gl_data/tail765.lay");
#[derive(Clone, Copy)]
enum N { D, ZB, F, Yt, H1, Y(u8), Xt(u8) }
#[derive(Clone, Copy)]
enum LOp { X(N), Cx(N, N), Ccx(N, N, N), U(usize, N) }
#[path = "ladder_data.rs"]
mod ladder_data;
const WH: usize = W - 2 * PAGE_D;
/// P1 cost counters (CCX of the page parts as emitted, MCX macros priced as expanded): 0 gather (test only),
/// 1 page cells, 2 window rotations, 3 window swaps, 4 class flags of 0, 2, 3.
static PG_CNT: [std::sync::atomic::AtomicU64; 20] = [const { std::sync::atomic::AtomicU64::new(0) }; 20];
/// count only: the big_phase flag site being emitted (1..6), its flag CCX also go to PG_CNT[10 + site]
static BIG_SITE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
fn pg_cost(g: &[G]) -> u64 {
    let t = MACS.lock().unwrap();
    g.iter().map(|x| if x.0 == MAC { let m = &t[x.1 as usize]; let k = m.lits.len() as u64; if m.an.is_empty() { 2 * k - 3 } else { 4 * k - 8 } } else if x.2 != NONE { 1 } else { 0 }).sum()
}
fn pg_add(i: usize, g: &[G]) {
    let c = pg_cost(g);
    PG_CNT[i].fetch_add(c, Ordering::Relaxed);
    let st = BIG_SITE.load(Ordering::Relaxed);
    if i == 4 && st > 0 { PG_CNT[10 + st].fetch_add(c, Ordering::Relaxed); }
}
const RW: usize = 64;
/// Clean lanes for the merged fold chain.
const ZL: usize = 4;
/// Each fold chain runs this many wires from its own start: a carry gets j wires with 2^-j.
const CHW: usize = 33;
/// ov is read back on this many top wires.
const CMPW: usize = 34;
/// LEAN_SQ (lane arxiv-research): x += lam^2 by three Karatsuba half-squares in one 258-wire register (Haener,
/// Tripier, Young et al. arXiv:2609.05625 section VII.1 squarer form, Gidney 1709.06648 halved adders whose AND
/// ancillae are the register's still-clean upper wires), folded into x with the parent's chains. Off re-emits the parent.
const LEAN_SQ: bool = true;
const LEAN_NEGCTL: bool = false;
/// LEAN_SB: 256-wire register, cross product L*H by controlled adds (no S^2); LEAN_ZL = fold lanes (3 at Q773).
const LEAN_SB: bool = true;
const LEAN_ZL: usize = 3;
/// carry window above a spill addend (the carry past it is dropped: 2^-64 per spill add)
const SPILL_W: usize = 64;
/// Multiplier bits consumed into the product.
const CAPW: usize = 2;
/// Low lanes read when a seed tests a product for zero.
const ZW: usize = 64;
const C0M1: [usize; 6] = [4, 6, 7, 8, 9, 32]; // bits of 2^32 + 976
const P0: [u64; 4] = [0xFFFFFFFEFFFFFC2F, u64::MAX, u64::MAX, u64::MAX];

fn pbit(i: usize) -> bool {
    (P0[i / 64] >> (i % 64)) & 1 == 1
}

#[derive(Clone, Copy)]
struct G(u32, u32, u32);
type Lit = (u32, bool);
type GL = Vec<G>;
#[inline]
fn gx(a: u32) -> G {
    G(a, NONE, NONE)
}
#[inline]
fn gc(a: u32, b: u32) -> G {
    G(a, b, NONE)
}
#[inline]
fn gt(a: u32, b: u32, c: u32) -> G {
    G(a, b, c)
}
fn rev(g: &[G]) -> GL {
    g.iter().rev().cloned().collect()
}

/// AND of k controls on one clean lane, 2k-3 T: conditionally clean wires, Khattar-Gidney 2024.
fn cc_core(cs: &[u32], tgt: u32, z: u32) -> GL {
    let k = cs.len();
    let m = k / 2;
    let mut up: GL = vec![gt(cs[0], cs[1], z), gc(z, cs[0]), gc(z, cs[1])];
    let (mut guards, mut aa, mut bb) = (vec![z], vec![cs[0]], vec![cs[1]]);
    for i in 1..m {
        let (a, b) = (cs[2 * i], cs[2 * i + 1]);
        let g = aa[i - 1];
        up.extend_from_slice(&[gt(a, b, g), gc(g, a), gc(g, b)]);
        guards.push(g);
        aa.push(a);
        bb.push(b);
    }
    let mut cur = guards[m - 1];
    let mut walk: GL = vec![];
    let mut out = up.clone();
    if k % 2 == 1 {
        let x = cs[k - 1];
        if m == 1 {
            out.push(gt(z, x, tgt));
            out.extend(rev(&up));
            return out;
        }
        walk.push(gt(cur, x, bb[m - 2]));
        cur = bb[m - 2];
    }
    if m >= 2 {
        let mut i = m - 2;
        while i >= 1 {
            walk.push(gt(cur, guards[i], bb[i - 1]));
            cur = bb[i - 1];
            i -= 1;
        }
    }
    out.extend_from_slice(&walk);
    out.push(gt(cur, guards[0], tgt));
    out.extend(rev(&walk));
    out.extend(rev(&up));
    out
}

const MAC_ON: bool = true;
const MAC: u32 = u32::MAX - 1;
#[derive(Clone)]
struct Mac { lits: Vec<Lit>, tgt: u32, an: Vec<u32>, busy: bool }
/// Number of the frame's idle spare lanes (phys 758..762 = start765 table entries) used as extra clean lanes for the
/// multi-controlled-X macros the ZB lane cannot serve (target ZB or ZB_BUSY). 0 = off (no lever); 1 = on, lane t[758 + PAGE_DI - PAGE_D] (needs PAGE_DI - PAGE_D <= 4).
const ZB_EXTRA: usize = 1;
/// labels of the extra clean lanes, filled by start765 once the table exists.
static ZX: std::sync::Mutex<Vec<u32>> = std::sync::Mutex::new(Vec::new());
static MACS: std::sync::Mutex<Vec<Mac>> = std::sync::Mutex::new(Vec::new());
/// Expand one dirty-ancilla MCX (Barenco, the original emission).
fn mac_expand(m: &Mac, out: &mut GL) {
    let l = &m.lits; let k = l.len(); let tgt = m.tgt; let an = &m.an;
    let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    out.extend_from_slice(&pre);
    let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
    if an.is_empty() {
        let z = if m.busy { ZX.lock().unwrap()[0] } else { 512 };
        assert!(z != tgt && !cs.contains(&z), "clean lane {z} used by macro");
        out.extend(cc_core(&cs, tgt, z)); out.extend_from_slice(&pre); return;
    }
    let mut up = vec![gt(cs[k - 1], an[k - 3], tgt)];
    let mut i = k - 2;
    while i > 1 { up.push(gt(cs[i], an[i - 2], an[i - 1])); i -= 1; }
    let mid = gt(cs[0], cs[1], an[0]);
    out.extend_from_slice(&up); out.push(mid); out.extend(up.iter().rev().cloned());
    out.extend_from_slice(&up[1..]); out.push(mid); out.extend(up[1..].iter().rev().cloned());
    out.extend_from_slice(&pre);
}
/// Macro-level analysis + expansion of the F gate list.
fn mac_finish(gates: Vec<G>) -> Vec<G> {
    let t = MACS.lock().unwrap().clone();
    let key = |m: &Mac| { let mut v = m.lits.clone(); v.sort(); v };
    let (mut r1, mut r1t, mut adj, mut sw2, mut sw3) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut prev: Option<usize> = None; let mut prev2: Option<usize> = None;
    for g in &gates {
        if g.0 == MAC {
            let id = g.1 as usize;
            if let Some(p) = prev {
                adj += 1;
                let (a, b) = (&t[p], &t[id]);
                if key(a) == key(b) && a.tgt != b.tgt && !b.lits.iter().any(|x| x.0 == a.tgt) && !a.lits.iter().any(|x| x.0 == b.tgt) { r1 += 1; r1t += 4 * (a.lits.len() as u64) - 8; }
                // swap pair: a = MCX(S+b.tgt -> a.tgt), b = MCX(S+a.tgt -> b.tgt)
                let mut ka: Vec<Lit> = a.lits.iter().filter(|x| x.0 != b.tgt).cloned().collect(); ka.sort();
                let mut kb: Vec<Lit> = b.lits.iter().filter(|x| x.0 != a.tgt).cloned().collect(); kb.sort();
                if a.lits.contains(&(b.tgt, true)) && b.lits.contains(&(a.tgt, true)) && ka == kb {
                    sw2 += 1;
                    if let Some(p2) = prev2 { let c = &t[p2]; if c.tgt == a.tgt && key(c) == key(a) { sw3 += 1; } }
                }
            }
            prev2 = prev; prev = Some(id);
        } else { prev = None; prev2 = None; }
    }
    eprintln!("MAC: {} macros, adjacent pairs {adj}, same-controls pairs {r1} (~{r1t} T), swap pairs {sw2}, swap triples {sw3}", t.len());
    // optimize runs of adjacent macros
    let mut opt: Vec<G> = Vec::with_capacity(gates.len());
    let (mut n_sw, mut n_fan, mut n_fan_t) = (0u64, 0u64, 0u64);
    let mut i = 0usize;
    let n = gates.len();
    while i < n {
        let g = gates[i];
        if g.0 != MAC { opt.push(g); i += 1; continue; }
        // (a) swap triple
        if OPT_SWAP && i + 2 < n && gates[i + 1].0 == MAC && gates[i + 2].0 == MAC {
            let (m1, m2, m3) = (&t[g.1 as usize], &t[gates[i + 1].1 as usize], &t[gates[i + 2].1 as usize]);
            let (a, b) = (m1.tgt, m2.tgt);
            let mut s1: Vec<Lit> = m1.lits.iter().filter(|x| x.0 != b).cloned().collect(); s1.sort();
            let mut s2: Vec<Lit> = m2.lits.iter().filter(|x| x.0 != a).cloned().collect(); s2.sort();
            if a != b && m3.tgt == a && key(m1) == key(m3) && m1.lits.contains(&(b, true)) && m2.lits.contains(&(a, true)) && s1 == s2
                && !s1.iter().any(|x| x.0 == a || x.0 == b) {
                opt.push(gc(b, a)); opt.push(gates[i + 1]); opt.push(gc(b, a));
                n_sw += 1; i += 3; continue;
            }
        }
        // (b) same-controls run -> one MCX + CX fanout
        if OPT_FAN {
            let k0 = key(&t[g.1 as usize]);
            let mut j = i + 1;
            let mut tg: Vec<u32> = vec![t[g.1 as usize].tgt];
            while j < n && gates[j].0 == MAC {
                let m = &t[gates[j].1 as usize];
                if key(m) != k0 || tg.contains(&m.tgt) { break; }
                tg.push(m.tgt); j += 1;
            }
            if j - i >= 2 {
                for &tt in &tg[1..] { opt.push(gc(tg[0], tt)); }
                opt.push(g);
                for &tt in &tg[1..] { opt.push(gc(tg[0], tt)); }
                n_fan += 1; n_fan_t += (j - i - 1) as u64; i = j; continue;
            }
        }
        opt.push(g); i += 1;
    }
    eprintln!("MAC opt: swap triples {n_sw}, fanout groups {n_fan} removing {n_fan_t} MCX");
    let mut out = Vec::with_capacity(opt.len() * 3);
    for g in opt { if g.0 == MAC { mac_expand(&t[g.1 as usize], &mut out); } else { out.push(g); } }
    out
}
const OPT_SWAP: bool = true;
const OPT_FAN: bool = true;
fn mcx(lits: &[Lit], tgt: u32, dirty: &[u32]) -> GL {
    let mut l: Vec<Lit> = Vec::with_capacity(lits.len());
    for &(q0, p) in lits {
        match l.iter().find(|x| x.0 == q0) {
            Some(x) => {
                if x.1 != p {
                    return vec![];
                }
            }
            None => l.push((q0, p)),
        }
    }
    let k = l.len();
    if k == 0 {
        return vec![gx(tgt)];
    }
    let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    let mut g = pre.clone();
    if k == 1 {
        g.push(gc(l[0].0, tgt));
    } else if k == 2 {
        g.push(gt(l[0].0, l[1].0, tgt));
    } else if ZB > 0 && IN_F.load(Ordering::Relaxed) && (ZB_EXTRA > 0 || (tgt != ZB_LANE && !ZB_BUSY.load(Ordering::Relaxed))) {
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        if MAC_ON {
            let mut t = MACS.lock().unwrap();
            t.push(Mac { lits: l.clone(), tgt, an: Vec::new(), busy: tgt == ZB_LANE || ZB_BUSY.load(Ordering::Relaxed) });
            return vec![G(MAC, (t.len() - 1) as u32, NONE)];
        }
        g.extend(cc_core(&cs, tgt, 512));
    } else {
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut an: Vec<u32> = Vec::with_capacity(k - 2);
        for &d in dirty {
            if d != tgt && !cs.contains(&d) {
                an.push(d);
                if an.len() == k - 2 {
                    break;
                }
            }
        }
        assert!(an.len() == k - 2);
        if MAC_ON && IN_F.load(Ordering::Relaxed) {
            let mut t = MACS.lock().unwrap();
            t.push(Mac { lits: l.clone(), tgt, an: an.clone(), busy: false });
            return vec![G(MAC, (t.len() - 1) as u32, NONE)];
        }
        let mut up = vec![gt(cs[k - 1], an[k - 3], tgt)];
        let mut i = k - 2;
        while i > 1 {
            up.push(gt(cs[i], an[i - 2], an[i - 1]));
            i -= 1;
        }
        let mid = gt(cs[0], cs[1], an[0]);
        g.extend_from_slice(&up);
        g.push(mid);
        g.extend(up.iter().rev().cloned());
        g.extend_from_slice(&up[1..]);
        g.push(mid);
        g.extend(up[1..].iter().rev().cloned());
    }
    g.extend_from_slice(&pre);
    g
}

fn cswap(c: u32, a: u32, b: u32, g: &mut GL) {
    g.push(gc(b, a));
    g.push(gt(c, a, b));
    g.push(gc(b, a));
}

fn rotate_up(ctl: u32, w: &[u32], r: usize) -> GL {
    let n = w.len();
    let r = r % n;
    let mut g = vec![];
    if r == 0 {
        return g;
    }
    let mut seen = vec![false; n];
    for st in 0..n {
        if seen[st] {
            continue;
        }
        let mut i = st;
        let mut cyc = vec![];
        while !seen[i] {
            seen[i] = true;
            cyc.push(i);
            i = (i + r) % n;
        }
        for j in 1..cyc.len() {
            cswap(ctl, w[cyc[0]], w[cyc[j]], &mut g);
        }
    }
    g
}

fn inc_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    let mut g = vec![];
    for i in (0..reg.len()).rev() {
        let mut l: Vec<Lit> = lits.to_vec();
        for j in 0..i {
            l.push((reg[j], true));
        }
        g.extend(mcx(&l, reg[i], dirty));
    }
    g
}
fn dec_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    rev(&inc_ctl(reg, lits, dirty))
}

fn add_chain(t: &[u32], s: &[u32], c: u32) -> GL {
    let n = t.len();
    let mut g = Vec::with_capacity(7 * n);
    for i in 0..n {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
        g.push(gt(s[i], t[i], c));
    }
    for i in (0..n).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g
}

fn inc_long(reg: &[u32], ctl: u32, dirty: &[u32], c: u32) -> GL {
    let mut r = vec![ctl];
    r.extend_from_slice(reg);
    let mut d: Vec<u32> = Vec::with_capacity(r.len());
    for &q0 in dirty {
        if q0 != c && !r.contains(&q0) {
            d.push(q0);
            if d.len() == r.len() {
                break;
            }
        }
    }
    assert!(d.len() == r.len());
    let sub = rev(&add_chain(&r, &d, c));
    let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
    let mut g = sub.clone();
    g.extend_from_slice(&nots);
    g.extend_from_slice(&sub);
    g.extend_from_slice(&nots);
    g.push(gx(ctl));
    g
}

fn aligned_blocks(vals: &BTreeSet<i32>) -> Vec<(i32, usize)> {
    let mut out = vec![];
    let mut vals = vals.clone();
    while let Some(&v) = vals.iter().next() {
        let mut k = 0usize;
        loop {
            let k2 = k + 1;
            if v & ((1 << k2) - 1) != 0 {
                break;
            }
            if (0..(1 << k2)).all(|i| vals.contains(&(v + i))) {
                k = k2;
            } else {
                break;
            }
        }
        out.push((v, k));
        for i in 0..(1 << k) {
            vals.remove(&(v + i));
        }
    }
    out
}

const fn maskv(v: usize) -> u128 {
    let mut m = 0u128;
    let mut p = 0;
    while p < 128 {
        if (p >> v) & 1 == 0 {
            m |= 1u128 << p;
        }
        p += 1;
    }
    m
}
const MASKV: [u128; 7] = [maskv(0), maskv(1), maskv(2), maskv(3), maskv(4), maskv(5), maskv(6)];
type Cubes = Vec<Vec<(usize, u8)>>;
/// Minimum cost disjoint decision tree over the hi bits (vars 0..3) and the parity (var 4).
fn tree_rec(on: u128, off: u128, n: i32, base: i32, vs: &[usize], memo: &mut HashMap<(u128, u128, i32), (i64, Cubes)>) -> (i64, Cubes) {
    if on == 0 {
        return (0, vec![]);
    }
    if off == 0 {
        let l = n + base;
        let c = if l <= 1 { 0 } else if l == 2 { 1 } else { 4 * (l as i64 - 2) };
        return (c, vec![vec![]]);
    }
    if let Some(r) = memo.get(&(on, off, n)) {
        return r.clone();
    }
    let mut best: Option<(i64, Cubes)> = None;
    for &v in vs {
        let z = MASKV[v];
        let (on0, on1, off0, off1) = (on & z, on & !z, off & z, off & !z);
        if (on0 == 0 && off0 == 0) || (on1 == 0 && off1 == 0) {
            continue;
        }
        let (c0, l0) = tree_rec(on0, off0, n + 1, base, vs, memo);
        let (c1, l1) = tree_rec(on1, off1, n + 1, base, vs, memo);
        if best.is_none() || c0 + c1 < best.as_ref().unwrap().0 {
            let mut lst: Cubes = vec![];
            for x in &l0 {
                let mut y = vec![(v, 0u8)];
                y.extend_from_slice(x);
                lst.push(y);
            }
            for x in &l1 {
                let mut y = vec![(v, 1u8)];
                y.extend_from_slice(x);
                lst.push(y);
            }
            best = Some((c0 + c1, lst));
        }
    }
    let r = best.expect("cover");
    memo.insert((on, off, n), r.clone());
    r
}
fn dtree(on: u128, off: u128, vs: &[usize], base: i32) -> Cubes {
    let mut memo = HashMap::new();
    tree_rec(on, off, 0, base, vs, &mut memo).1
}

/// lane allocator of the stored inverter (virtual lanes)
struct B {
    free: Vec<u32>,
    next: u32,
    gates: Vec<G>,
}
impl B {
    fn alloc(&mut self) -> u32 {
        if let Some(q0) = self.free.pop() {
            q0
        } else {
            self.next += 1;
            self.next - 1
        }
    }
    fn release(&mut self, q0: u32) {
        self.free.push(q0);
        self.free.sort_by(|a, b| b.cmp(a));
    }
    fn t(&mut self, g: &[G]) {
        self.gates.extend_from_slice(g);
    }
}

struct Machine {
    b: B,
    dirty: Vec<u32>,
    pas: Vec<u32>,
    x: Vec<u32>,
    y: Vec<u32>,
    e: Vec<u32>,
    par: u32,
    /// P1 page lanes (empty when PAGE is off): VA, VB, SC, T2 (T2 is the implicit word's temporary), PAGE_D each.
    pg: Vec<u32>,
    /// ring width (W, or WH between the cuts with PAGE_N) and the lanes freed by the narrowing
    wr: usize,
    freed: Vec<u32>,
    /// L-C: the 4th wait bit of the long classes (a lane freed by the narrowing; NONE outside the cuts)
    w4: u32,
    /// CONV: the D16 T2 lanes and the D16 freed list saved by the start converter for the tail converter
    cv_t2: Vec<u32>,
    cv_freed: Vec<u32>,
    /// CONV: the D16 narrowed ring lists and page at the start converter (their label sets / positions are restored at the tail)
    cv_x16: Vec<u32>,
    cv_y16: Vec<u32>,
    cv_pg16: Vec<u32>,
}

fn lf(t: i32, e: i32) -> (i32, i32) {
    if t % 2 == 1 {
        return ((t - 1) / 2, (t + 1) / 2);
    }
    let m = e >> 1;
    (t / 2 - m, t / 2 + m + (e & 1))
}
fn pairs(t: i32) -> Vec<i32> {
    let n = N as i32;
    if t % 2 == 1 {
        let (l, f) = lf(t, 1);
        return if l >= 1 && f <= n { vec![1] } else { vec![] };
    }
    (0..=ECAP)
        .filter(|&e| {
            let (l, f) = lf(t, e);
            l >= 1 && f <= n && f >= l
        })
        .collect()
}

/// Uncontrolled rotation (CX swaps, no Toffoli): content of w[i] -> w[(i + r) mod n].
fn rot_free(w: &[u32], r: usize) -> GL {
    let mut g = vec![];
    for x in rotate_up(NONE, w, r).chunks(3) {
        // rotate_up emits cswap(c, a, b) = [CX(b, a), CCX(c, a, b), CX(b, a)]: replace by SWAP(a, b)
        let (a, b) = (x[1].1, x[1].2);
        g.extend_from_slice(&[gc(a, b), gc(b, a), gc(a, b)]);
    }
    g
}
fn swap_free(a: u32, b: u32) -> GL { vec![gc(a, b), gc(b, a), gc(a, b)] }
/// Rotate a wire list up by one under c: w[i] to w[i+1], top wraps to the bottom.
fn rot1(c: u32, w: &[u32]) -> GL {
    let mut g = vec![];
    for i in (1..w.len()).rev() {
        cswap(c, w[i], w[i - 1], &mut g);
    }
    g
}

impl Machine {
    /// one ladder site: its flag gates (counted as flags) with use i replaced by uop(set_i, control lane)
    fn ladder(&self, site: &str, uop: &dyn Fn(&[i32], u32) -> GL) -> GL {
        let (sets, ops) = ladder_data::LADDER.iter().find(|s| s.0 == site).map(|s| (s.1, s.2)).expect("ladder site");
        let wv = self.wr;
        let lane = |n: N| -> u32 {
            match n {
                N::D => self.x[0],
                N::ZB => self.pg[4 * PAGE_D + 1],
                N::F => self.pg[4 * PAGE_D],
                N::Yt => self.y[wv - 1],
                N::H1 => self.e[1],
                N::Y(j) => self.y[j as usize],
                N::Xt(j) => self.x[wv - j as usize],
            }
        };
        let (mut g, mut fl): (GL, GL) = (vec![], vec![]);
        for op in ops.iter() {
            let q = match *op {
                LOp::X(a) => gx(lane(a)),
                LOp::Cx(a, b) => gc(lane(a), lane(b)),
                LOp::Ccx(a, b, c) => gt(lane(a), lane(b), lane(c)),
                LOp::U(i, c) => { g.extend(uop(sets[i], lane(c))); continue; }
            };
            g.push(q);
            fl.push(q);
        }
        pg_add(4, &fl);
        g
    }
    /// LEVER2 demux walk: for every group (value v of the 4 bits ub, LSB first; leaf cubes ex; use gates on control d):
    /// d = cl AND [ub == v] AND cube around the use. fa = Some(F): A = cl & ub3 ub2 on F (aux ZB), B = A & ub1 on ZB,
    /// leaf = B & ub0; fa = None: A = cl & ub3 ub2 on ZB, leaf = A & ub1 & ub0 (Barenco while ZB holds A).
    fn demux(&self, cl: &[Lit], ub: &[u32], groups: &mut Vec<(i32, Vec<Vec<Lit>>, GL)>, d: u32, fa: Option<u32>) -> GL {
        let zb = ZB_LANE;
        let bt = |v: i32, i: usize| -> bool { (v >> i) & 1 == 1 };
        groups.sort_by_key(|x| x.0);
        let (mut g, mut fl): (GL, GL) = (vec![], vec![]);
        let a_g = |me: &Self, v: i32| -> GL {
            let mut l = cl.to_vec();
            l.push((ub[3], bt(v, 3)));
            l.push((ub[2], bt(v, 2)));
            match fa {
                Some(f) => me.m(&l, f),
                None => {
                    // A on ZB with d (clean here: no leaf is up) as the AND's aux lane: 2k - 3 instead of Barenco
                    if SLIDE_LAD_CA {
                        let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
                        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
                        let mut q = pre.clone();
                        q.extend(cc_core(&cs, zb, d));
                        q.extend(pre);
                        q
                    } else {
                        me.m(&l, zb)
                    }
                }
            }
        };
        let b_g = |me: &Self, v: i32| -> GL { me.m(&[(fa.unwrap(), true), (ub[1], bt(v, 1))], zb) };
        let (mut ca, mut cb): (Option<i32>, Option<i32>) = (None, None);
        for (v, ex, us) in groups.iter() {
            let v = *v;
            if ca != Some(v >> 2) {
                if let Some(b0) = cb.take() { let q = b_g(self, b0 << 1); fl.extend_from_slice(&q); g.extend(q); }
                if let Some(a0) = ca { let q = a_g(self, a0 << 2); fl.extend_from_slice(&q); g.extend(q); }
                let q = a_g(self, v);
                fl.extend_from_slice(&q);
                g.extend(q);
                ca = Some(v >> 2);
            }
            if fa.is_some() && cb != Some(v >> 1) {
                if let Some(b0) = cb { let q = b_g(self, b0 << 1); fl.extend_from_slice(&q); g.extend(q); }
                let q = b_g(self, v);
                fl.extend_from_slice(&q);
                g.extend(q);
                cb = Some(v >> 1);
            }
            let base: Vec<Lit> = if fa.is_some() { vec![(zb, true), (ub[0], bt(v, 0))] } else { vec![(zb, true), (ub[1], bt(v, 1)), (ub[0], bt(v, 0))] };
            let mut lf: GL = vec![];
            ZB_BUSY.store(true, Ordering::Relaxed);
            for c in ex {
                let mut l = base.clone();
                l.extend_from_slice(c);
                lf.extend(self.m(&l, d));
            }
            ZB_BUSY.store(false, Ordering::Relaxed);
            fl.extend_from_slice(&lf);
            fl.extend_from_slice(&lf);
            g.extend_from_slice(&lf);
            g.extend_from_slice(us);
            g.extend(lf);
        }
        if let Some(b0) = cb { let q = b_g(self, b0 << 1); fl.extend_from_slice(&q); g.extend(q); }
        if let Some(a0) = ca { let q = a_g(self, a0 << 2); fl.extend_from_slice(&q); g.extend(q); }
        pg_add(4, &fl);
        g
    }
    /// MAP765_v2 physical lane -> frame label at the boundary below slot CUT_T (paged, narrowed): YH 0..224, VA 225..240,
    /// VB 241..254 + 512, 513, PAR 255, PAS 256..511, XH 514..738, SC 739..754, h 755, 756, W4 757 + spares 758..762 (freed[0..6]),
    /// ZB 763, F 764; then (test only, >= 765) every other allocated lane in increasing order (T2, the other freed lanes, ...).
    fn phys765(&self, nl: u32) -> Vec<u32> {
        assert!(PAGE_G && PAGE_N && PAGE_DI == 16 && self.wr == 225, "phys765 needs the D16 narrowed frame");
        let (d, pg) = (PAGE_DI, &self.pg);
        let mut t: Vec<u32> = vec![NONE; 765];
        for i in 0..225 {
            t[i] = self.y[i];
            t[514 + i] = self.x[i];
        }
        for j in 0..16 {
            t[225 + j] = pg[j];
            t[739 + j] = pg[2 * d + j];
        }
        for j in 0..14 {
            t[241 + j] = pg[d + j];
        }
        t[512] = pg[d + 14];
        t[513] = pg[d + 15];
        t[255] = self.par;
        for i in 0..256 {
            t[256 + i] = self.pas[i];
        }
        t[755] = self.e[0];
        t[756] = self.e[1];
        for i in 0..6 {
            t[757 + i] = self.freed[i];
        }
        t[763] = pg[4 * d + 1];
        t[764] = pg[4 * d];
        assert!(t.iter().all(|&q| q != NONE));
        let used: BTreeSet<u32> = t.iter().cloned().collect();
        assert_eq!(used.len(), 765, "phys765: lanes not distinct");
        for q in 0..nl {
            if !used.contains(&q) {
                t.push(q);
            }
        }
        t
    }
    fn mk(&self, t: i32, k: i32) {
        if DBG_T.load(Ordering::Relaxed) == t {
            DBG_M.lock().unwrap().push((100000 + k, self.b.gates.len()));
        }
    }
    fn m(&self, l: &[Lit], t: u32) -> GL {
        mcx(l, t, &self.dirty)
    }
    fn hl(&self, v: i32) -> Vec<Lit> {
        (0..EB).map(|i| (self.e[i], (v >> i) & 1 == 1)).collect()
    }
    fn init(&mut self) {
        let mut g: GL = vec![gx(self.x[0])];
        for i in 0..N {
            if pbit(i) {
                g.push(gx(self.x[i + 1]));
            }
        }
        let xl: Vec<u32> = self.y[2..].to_vec();
        for &q0 in &xl {
            g.push(gc(self.par, q0));
        }
        let cl = self.e[0];
        for &i in &C0M1 {
            g.extend(rev(&inc_long(&xl[i..], self.par, &self.dirty, cl)));
        }
        self.b.t(&g);
    }
    #[allow(clippy::too_many_arguments)]
    fn row(&self, t: &[u32], s: &[u32], top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>) -> GL {
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        if top != NONE {
            conj.push(gx(top));
        }
        g.extend_from_slice(&conj);
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| k + 1).unwrap_or(0),
            None => tog.keys().next_back().map(|k| k + 1).unwrap_or(0),
        };
        let gate3 = |g: &mut GL, a0: u32, a1: u32, tgt: u32, i: usize| {
            if let Some(il) = inline {
                for li in &il[&i] {
                    let mut l = vec![(a0, true), (a1, true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, tgt));
                }
            } else {
                g.extend(self.m(&[(a0, true), (a1, true), (m, true)], tgt));
            }
        };
        for i in 0..n {
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend {
                gate3(&mut g, s[i], t[i], c, i);
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        for li in active {
            g.extend(self.m(li, d));
        }
        if top != NONE {
            for li in active {
                let mut l = li.clone();
                l.extend_from_slice(&[(c, true), (top, true)]);
                g.extend(self.m(&l, d));
            }
            g.push(gt(d, c, top));
        } else {
            for li in active {
                let mut l = li.clone();
                l.push((c, true));
                g.extend(self.m(&l, d));
            }
        }
        for i in (0..n).rev() {
            if i < wend {
                gate3(&mut g, s[i], t[i], c, i);
            } else {
                g.push(gt(s[i], t[i], c));
            }
            g.push(gc(c, t[i]));
            if i < wend {
                gate3(&mut g, d, s[i], t[i], i);
            } else {
                g.push(gt(d, s[i], t[i]));
            }
            g.push(gc(c, s[i]));
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        g.extend_from_slice(&conj);
        g
    }
    #[allow(clippy::too_many_arguments)]
    fn row_v(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>) -> GL {
        self.row_vz(t, s, t1, top, d, c, m, tog, active, inline, cv, false)
    }
    fn row_vz(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool) -> GL {
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        g.extend_from_slice(&conj);
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
            None => tog.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
        };
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        for i in 0..n {
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.mz(l, m, d));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(s[i], true), (t[i], true)];
                    l.extend_from_slice(li);
                    g.extend(if nz { self.m(&l, c) } else { self.mz(&l, c, d) });
                }
            } else if m != NONE && i < wend {
                g.extend(self.mz(&[(s[i], true), (t[i], true), (m, true)], c, d));
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        if top != NONE {
            for li in active {
                let mut a2: Vec<Lit> = li.clone();
                a2.extend_from_slice(&[(c, false), (t1, false)]);
                g.extend(self.mz(&a2, top, d));
            }
            for li in active {
                let mut a3: Vec<Lit> = li.clone();
                a3.push((top, true));
                g.extend(self.m(&a3, d));
            }
        } else {
            for li in active {
                let mut a2: Vec<Lit> = li.clone();
                a2.extend_from_slice(&[(c, false), (t1, false)]);
                g.extend(self.m(&a2, d));
            }
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        for i in (0..n).rev() {
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(s[i], true), (t[i], true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, c));
                }
            } else if m != NONE && i < wend {
                g.extend(self.m(&[(s[i], true), (t[i], true), (m, true)], c));
            } else {
                g.push(gt(s[i], t[i], c));
            }
            g.push(gc(c, t[i]));
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(d, true), (s[i], true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, t[i]));
                }
            } else if m != NONE && i < wend {
                g.extend(self.m(&[(d, true), (s[i], true), (m, true)], t[i]));
            } else {
                g.push(gt(d, s[i], t[i]));
            }
            g.push(gc(c, s[i]));
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain_vt(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        conj.push(gx(top));
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        g.extend(self.m(&[(d, true), (c, true)], top));
        g.extend(self.m(&[(d, true), (c, false), (t1, true)], top));
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain_v(&self, t: &[u32], s: &[u32], t1: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain(&self, t: &[u32], s: &[u32], top: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        if top != NONE {
            conj.push(gx(top));
        }
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        if top != NONE {
            g.push(gt(d, c, top));
        }
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn pi_gates(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> GL {
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let mut g = vec![];
        // the top lane of this frame is a known zero (it holds the act flag): only its carry-out matters
        let idx = {
            let v: Vec<usize> = ((W - l)..(W - 1)).collect();
            let k = v.len().saturating_sub(PIW - 1);
            v[k..].to_vec()
        };
        let mut fw = vec![];
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, x[W - 1], f1));
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, y[w]), gc(cc, x[w - 1]), gt(y[w], x[w - 1], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, y[1], f3));
        g.extend(rev(&fw));
        g
    }
    fn flag_e(&self, fl: u32, xt: u32, y: &[u32]) -> GL {
        let h = &self.e;
        let ctl = self.x[0];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        // act shots, hi=0: xt -> 15; not xt, y0=1 -> 13; not xt, y0=0 -> stays 0
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hl(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(0)), ctl));
        g.extend_from_slice(&[gc(ctl, h[0]), gc(ctl, h[2]), gc(ctl, h[3])]);
        g.extend(self.m(&[(ctl, true), (xt, true)], h[1]));
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hl(15)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(13)), ctl));
        g
    }
    /// As m, with z a lane that is clean here: AND of k controls in 2k-3 T.
    fn mz(&self, l0: &[Lit], t: u32, z: u32) -> GL {
        let mut l: Vec<Lit> = Vec::with_capacity(l0.len());
        for &(q0, p) in l0 {
            match l.iter().find(|x| x.0 == q0) {
                Some(x) => {
                    if x.1 != p {
                        return vec![];
                    }
                }
                None => l.push((q0, p)),
            }
        }
        if l.len() < 3 || ZB > 0 {
            return self.m(l0, t);
        }
        let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut g = pre.clone();
        g.extend(cc_core(&cs, t, z));
        g.extend_from_slice(&pre);
        g
    }
    fn hc(&self, c: i32) -> Vec<Lit> {
        vec![(self.e[0], c & 1 == 1), (self.e[1], (c >> 1) & 1 == 1)]
    }
    fn page_alloc(&mut self) {
        if PAGE || PAGE_V || PAGE_C || PAGE_G {
            self.pg = (0..4 * PAGE_DI + 1).map(|_| self.b.alloc()).collect();
            // Z of the sandwich: the frame's clean AND lane when ZB is on (MAP765: 3 clean lanes X[0], F, ZB)
            let z = if ZB > 0 { ZB_LANE } else { self.b.alloc() };
            self.pg.push(z);
        }
    }
    /// One clock value: the P1 format switches at the cuts, then the slot.
    fn tick(&mut self, t: i32) {
        self.cut(t);
        self.slot(t);
    }
    /// the P1 / P5 format switches at the cuts (before slot t)
    fn cut(&mut self, t: i32) {
        if PAGE && PAGE_CUTS.contains(&t) {
            let g = self.page_in(t);
            self.b.t(&g);
            self.b.t(&rev(&g));
        }
        if PAGE_G && t == CUT_S - 1 {
            let g = self.page_in(CUT_S - 1);
            if !(ASM_START_PAGED && gl_loader::has(gl_loader::At::Start)) {
                self.b.t(&g);
            }
            if PAGE_N {
                self.freed = self.x[WHI..].to_vec();
                self.freed.extend_from_slice(&self.y[WHI..]);
                self.x.truncate(WHI);
                self.y.truncate(WHI);
                self.wr = WHI;
                if TIER_LONG > 0 {
                    self.w4 = self.freed[0];
                }
            }
            if CONV {
                self.conv_fwd(CUT_S - 1);
            }
            assert!(TIER_LONG == 0 || (PAGE_N && CUT_S % 16 == 0 && CUT_T % 16 == 0), "L-C needs PAGE_N and cuts 0 mod 16");
        }
        if PAGE_G && t == CUT_T - 1 {
            if PAGE_N {
                assert!(self.wr == WHI, "re-widen from the interface width");
                let fx = self.freed[..W - WHI].to_vec();
                let fy = self.freed[W - WHI..].to_vec();
                self.x.extend_from_slice(&fx);
                self.y.extend_from_slice(&fy);
                self.wr = W;
                self.w4 = NONE;
            }
            let g = rev(&self.page_in(CUT_T - 1));
            self.b.t(&g);
        }
    }
    /// The terms (literal sets, pairwise disjoint) that say "this shot has F = f" at the boundary below slot T + 1,
    /// one entry per f, with E = 2 f - T (odd). Layout facts: notes v3/KT7_progress.md (step 3 groundwork) and
    /// v5/team40/p1/cutlay.py, cutfeat.py: code h0 h1 = 00 -> E = 1; 10 -> E = -1 (yt = 0) or a big shot that waits
    /// (r = 0, e = E >= 11, yt = 1, marker Y[E-1], offset bits Y[4..6]); 01 -> E >= 3, marker Y[E-1], zero below;
    /// 11 -> E <= -3, marker Y[W+E-g], zero above it, g = top zeros of ring X (0 or 1).
    fn page_cases(&self, tt: i32) -> Vec<(i32, Vec<Vec<Lit>>)> {
        self.page_cases_xy(&self.x, &self.y, tt)
    }
    fn page_cases_xy(&self, x: &[u32], y: &[u32], tt: i32) -> Vec<(i32, Vec<Vec<Lit>>)> {
        let h = &self.e;
        let (h0, h1) = (h[0], h[1]);
        let yt = y[W - 1];
        let wi = W as i32;
        let mut out = vec![];
        for ee in (-29..=25).filter(|v: &i32| v.rem_euclid(2) == 1) {
            let f = (tt + ee) / 2;
            let mut terms: Vec<Vec<Lit>> = vec![];
            if ee == 1 {
                terms.push(vec![(h0, false), (h1, false)]);
            } else if ee == -1 {
                terms.push(vec![(h0, true), (h1, false), (yt, false)]);
            } else if ee >= 3 {
                let mut l = vec![(h0, false), (h1, true), (y[ee as usize - 1], true)];
                for j in (2..=(ee - 3)).step_by(2) {
                    l.push((y[j as usize], false));
                }
                terms.push(l);
                if ee >= 11 {
                    let mut l = vec![(h0, true), (h1, false), (yt, true), (y[ee as usize - 1], true)];
                    for j in (10..=(ee - 3)).step_by(2) {
                        l.push((y[j as usize], false));
                    }
                    terms.push(l);
                }
            } else {
                for g in 0..=1 {
                    let mk = (wi + ee - g) as usize;
                    let mut l = vec![(h0, true), (h1, true), (y[mk], true)];
                    for j in (mk + 1)..W {
                        l.push((y[j], false));
                    }
                    if g == 0 {
                        l.push((x[W - 1], true));
                    } else {
                        l.extend_from_slice(&[(x[W - 1], false), (x[W - 2], true)]);
                    }
                    terms.push(l);
                }
            }
            out.push((f, terms));
        }
        out
    }
    /// Format switch explicit -> paged at the boundary below slot tt + 1: gather A, B, tB, tA low words of every
    /// shot into VA, VB, T1, T2 (one case per F, flag on X[0] which is tB's leading one, flipped to 0), select
    /// SC = T1 by the parity of B (B even: SC = tA_low), and erase the implicit word T2 with
    /// T2 = T2 * pivot + other * SC - p = 0 mod 2^D (A tB + B tA = p). The ring lanes of the four words are left 0.
    fn page_in(&self, tt: i32) -> GL {
        let d = PAGE_DI;
        let (x, y) = (&self.x, &self.y);
        let (va, vb, t1, t2) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d], &self.pg[3 * d..4 * d]);
        let x0 = x[0];
        let wi = W as i32;
        let mut g: GL = vec![gx(x0)];
        for (f, terms) in self.page_cases(tt) {
            let bx = wi - f;
            let by = (wi - tt + f).rem_euclid(wi);
            let mut fl: GL = vec![];
            for l in &terms {
                fl.extend(self.m(l, x0));
            }
            g.extend_from_slice(&fl);
            // with PAGE_N the compaction below moves every lane above a hole down 2D, top-referenced literals included:
            // the flag is uncomputed with the literals moved the same way
            let mut fl_post = fl.clone();
            if PAGE_N && PAGE_G {
                let (hx, hy) = ((bx - d as i32) as usize, (by - d as i32) as usize);
                let mv = |q0: u32| -> u32 {
                    if let Some(i) = x.iter().position(|&a| a == q0) { if i >= hx { return x[i - 2 * d]; } }
                    if let Some(i) = y.iter().position(|&a| a == q0) { if i >= hy { return y[i - 2 * d]; } }
                    q0
                };
                fl_post = vec![];
                for l in &terms {
                    let mut l2: Vec<Lit> = l.iter().map(|&(q0, v)| (mv(q0), v)).collect();
                    if l2 != *l {
                        // only a compacted shot has X[W-1] = X[W-2] = 0 (freed lanes); an uncompacted one has a 1 there
                        // (g = F - bl(A) <= 1, proof in P1_progress.md 00:55), so a moved term cannot fire on it
                        l2.extend_from_slice(&[(x[W - 1], false), (x[W - 2], false)]);
                    }
                    fl_post.extend(self.m(&l2, x0));
                }
            }
            for j in 0..d as i32 {
                cswap(x0, va[j as usize], x[(bx + j) as usize], &mut g);
                cswap(x0, t1[j as usize], x[(bx - 1 - j) as usize], &mut g);
                cswap(x0, vb[j as usize], y[(by + j).rem_euclid(wi) as usize], &mut g);
                cswap(x0, t2[j as usize], y[(by - 1 - j).rem_euclid(wi) as usize], &mut g);
            }
            if PAGE_N && PAGE_G {
                // close the holes: everything above a hole moves down 2D (top 2D lanes of each ring become 0)
                let sx: Vec<u32> = x[(bx - d as i32) as usize..].to_vec();
                g.extend(rotate_up(x0, &sx, sx.len() - 2 * d));
                assert!(by >= d as i32 && by <= wi - d as i32);
                let sy: Vec<u32> = y[(by - d as i32) as usize..].to_vec();
                g.extend(rotate_up(x0, &sy, sy.len() - 2 * d));
            }
            g.extend_from_slice(&fl_post);
        }
        g.extend(self.erase_blk_d(x0, PAGE_DI));
        g.push(gx(x0));
        g
    }
    /// CONV: the start-side D16 -> D11 converter on the narrowed D16 state.
    /// xf, yf: the explicit W-lane lists (narrowed ring ++ its freed tops) that page_cases reads; pg16: the D16 page
    /// (VA, VB, SC, T2, F, ZB); spares: 5 lanes clean on every paged shot; k: insertion index of the 10 lanes per ring.
    /// P = VA0 or VB0 (0 exactly on an unpaged all-zero page) sits on ZB for the lift and the route, then on F as a
    /// literal of every reopen flag (ZB is free for the flags' AND). Returns (gates, ring X list, ring Y list) at D11.
    fn conv_gates(&self, tt: i32, xf: &[u32], yf: &[u32], pg16: &[u32], spares: &[u32], k: (usize, usize)) -> (GL, Vec<u32>, Vec<u32>) {
        use self::window_prims::{self as wp, Cfg};
        let (d, dl) = (PAGE_DI, PAGE_D);
        let nl = d - dl;
        assert!(spares.len() == nl && xf.len() == W && yf.len() == W && pg16.len() == 4 * d + 2);
        let (va, vb, sc) = (&pg16[0..d], &pg16[d..2 * d], &pg16[2 * d..3 * d]);
        let (f, zb) = (pg16[4 * d], pg16[4 * d + 1]);
        assert_eq!(zb, ZB_LANE);
        let pon = |t: u32| -> GL { vec![gx(va[0]), gx(vb[0]), gt(va[0], vb[0], t), gx(va[0]), gx(vb[0]), gx(t)] };
        let (pz, pf) = (pon(zb), pon(f));
        // lift: spares ^= P & h[dl..d], h the implicit word (select F = [B even], K2 half, copy, undo)
        let mut sel: GL = vec![gx(vb[0]), gc(vb[0], f), gx(vb[0])];
        for j in 0..d { cswap(f, va[j], vb[j], &mut sel); }
        let (qa, qb, qc, qp) = (Self::qs(va), Self::qs(vb), Self::qs(sc), Self::qs(&self.pas[..64]));
        let mut pb = self::prims_builder::B::new();
        let k2 = Self::pgl(wp::rec(&mut pb, |b| {
            wp::idiv(b, Cfg::PY, &qa, &qb, &qp);
            wp::invp(b, Cfg::PY, &qb, &qp, wp::P256_LO, &[]);
            wp::undo(b, |b| wp::mac(b, Cfg::PY, &qb, &qa, &qc, &qp));
        }));
        let mut g: GL = pz.clone();
        g.extend_from_slice(&sel);
        g.extend_from_slice(&k2);
        for kk in 0..nl { g.push(gt(zb, vb[dl + kk], spares[kk])); }
        g.extend(rev(&k2));
        g.extend(rev(&sel));
        // route: F = P and [B even]; SC tops <-> spares, so SC tops = tB bits, spares = tA bits
        let fg: GL = vec![gx(vb[0]), gt(zb, vb[0], f), gx(vb[0])];
        g.extend_from_slice(&fg);
        for kk in 0..nl { cswap(f, sc[dl + kk], spares[kk], &mut g); }
        g.extend(rev(&fg));
        g.extend_from_slice(&pf);
        g.extend(rev(&pz));
        // the D11 ring lists: 10 lanes inserted at k (ring X: tB 15..11, A 11..15; ring Y: tA 15..11, B 11..15)
        let (x16, y16) = (&xf[..WHI], &yf[..WHI]);
        let mut nx: Vec<u32> = (0..nl).map(|kk| sc[d - 1 - kk]).collect();
        nx.extend((0..nl).map(|kk| va[dl + kk]));
        let mut ny: Vec<u32> = (0..nl).map(|kk| spares[nl - 1 - kk]).collect();
        ny.extend((0..nl).map(|kk| vb[dl + kk]));
        let (kx, ky) = k;
        let xe: Vec<u32> = x16[..kx].iter().chain(nx.iter()).chain(x16[kx..].iter()).copied().collect();
        let ye: Vec<u32> = y16[..ky].iter().chain(ny.iter()).chain(y16[ky..].iter()).copied().collect();
        // reopen: per case, flag (page_in(D11)'s moved terms read on xe / ye, plus P on F) and rotate the segment
        // between k and the shot's junction so that the 10 lanes land in the hole
        let x0 = xe[0];
        assert_eq!(x0, xf[0]);
        let wi = W as i32;
        let seg = |e: &[u32], j: usize, kk: usize| -> GL {
            if j >= kk {
                let s0 = &e[kk..j + 2 * nl];
                rotate_up(x0, s0, s0.len() - 2 * nl)
            } else {
                let s0 = &e[j..kk + 2 * nl];
                rotate_up(x0, s0, 2 * nl)
            }
        };
        let posx: HashMap<u32, usize> = xf.iter().enumerate().map(|(i, &q0)| (q0, i)).collect();
        let posy: HashMap<u32, usize> = yf.iter().enumerate().map(|(i, &q0)| (q0, i)).collect();
        g.push(gx(x0));
        for (fv, terms) in self.page_cases_xy(xf, yf, tt) {
            let bx = (wi - fv) as usize;
            let by = (wi - tt + fv).rem_euclid(wi) as usize;
            let (hx, hy) = (bx - dl, by - dl);
            let mv = |q0: u32| -> u32 {
                if let Some(&i) = posx.get(&q0) { return if i >= hx { xe[i - 2 * dl] } else { xe[i] }; }
                if let Some(&i) = posy.get(&q0) { return if i >= hy { ye[i - 2 * dl] } else { ye[i] }; }
                q0
            };
            let mut fl: GL = vec![];
            for l in &terms {
                let mut l2: Vec<Lit> = l.iter().map(|&(q0, v)| (mv(q0), v)).collect();
                l2.push((f, true));
                fl.extend(self.m(&l2, x0));
            }
            g.extend_from_slice(&fl);
            g.extend(seg(&xe, bx - d, kx));
            g.extend(seg(&ye, by - d, ky));
            g.extend_from_slice(&fl);
        }
        g.push(gx(x0));
        g.extend(rev(&pf));
        (g, xe, ye)
    }
    /// CONV: after page_in(tt) and the narrowing to WHI: emit the converter, move the frame to D11 lists and page.
    fn conv_fwd(&mut self, tt: i32) {
        let (d, dl) = (PAGE_DI, PAGE_D);
        assert!(PAGE_N && PAGE_G && self.wr == WHI && self.x.len() == WHI && self.pg.len() == 4 * d + 2);
        let xf: Vec<u32> = self.x.iter().chain(self.freed[..W - WHI].iter()).copied().collect();
        let yf: Vec<u32> = self.y.iter().chain(self.freed[W - WHI..].iter()).copied().collect();
        let pg16 = self.pg.clone();
        let spares: Vec<u32> = self.freed[1..1 + d - dl].to_vec();
        let (g, xe, ye) = self.conv_gates(tt, &xf, &yf, &pg16, &spares, CONV_K_S);
        eprintln!("conv: start converter at {}: {} gates, {} CCX (pre-MAC)", tt, g.len(), g.iter().filter(|q0| q0.2 != NONE).count());
        self.b.t(&g);
        self.cv_t2 = pg16[3 * d..4 * d].to_vec();
        self.cv_freed = self.freed.clone();
        self.cv_x16 = self.x.clone();
        self.cv_y16 = self.y.clone();
        self.cv_pg16 = pg16.clone();
        let mut pg: Vec<u32> = pg16[0..dl].to_vec();
        pg.extend_from_slice(&pg16[d..d + dl]);
        pg.extend_from_slice(&pg16[2 * d..2 * d + dl]);
        pg.extend_from_slice(&pg16[3 * d..3 * d + dl]);
        pg.push(pg16[4 * d]);
        pg.push(pg16[4 * d + 1]);
        self.pg = pg;
        self.x = xe;
        self.y = ye;
        self.wr = WH;
        self.freed = vec![self.cv_freed[0]];
        assert!(self.x.len() == WH && self.y.len() == WH);
    }
    /// CONV: at the boundary below slot tt + 1 (before page_out(tt) / the tail list): the inverse converter on the
    /// current D11 lists, back to the D16 narrowed lists, page and freed tops.
    fn conv_back(&mut self, tt: i32) {
        let (d, dl) = (PAGE_DI, PAGE_D);
        let nl = d - dl;
        assert!(self.wr == WH && self.x.len() == WH && self.y.len() == WH && self.pg.len() == 4 * dl + 2);
        let (kx, ky) = CONV_K_T;
        let (xe, ye) = (self.x.clone(), self.y.clone());
        let (nx, ny) = (xe[kx..kx + 2 * nl].to_vec(), ye[ky..ky + 2 * nl].to_vec());
        let x16: Vec<u32> = xe[..kx].iter().chain(xe[kx + 2 * nl..].iter()).copied().collect();
        let y16: Vec<u32> = ye[..ky].iter().chain(ye[ky + 2 * nl..].iter()).copied().collect();
        let pg = self.pg.clone();
        let mut pg16: Vec<u32> = pg[0..dl].to_vec();
        pg16.extend_from_slice(&nx[nl..]);
        pg16.extend_from_slice(&pg[dl..2 * dl]);
        pg16.extend_from_slice(&ny[nl..]);
        pg16.extend_from_slice(&pg[2 * dl..3 * dl]);
        pg16.extend((0..nl).map(|kk| nx[nl - 1 - kk]));
        pg16.extend_from_slice(&self.cv_t2);
        pg16.push(pg[4 * dl]);
        pg16.push(pg[4 * dl + 1]);
        let spares: Vec<u32> = (0..nl).map(|kk| ny[nl - 1 - kk]).collect();
        let mut freed: Vec<u32> = vec![self.cv_freed[0]];
        freed.extend_from_slice(&spares);
        freed.extend_from_slice(&self.cv_freed[1 + nl..]);
        let xf: Vec<u32> = x16.iter().chain(freed[..W - WHI].iter()).copied().collect();
        let yf: Vec<u32> = y16.iter().chain(freed[W - WHI..].iter()).copied().collect();
        let (g, xe2, ye2) = self.conv_gates(tt, &xf, &yf, &pg16, &spares, CONV_K_T);
        assert!(xe2 == xe && ye2 == ye, "conv_back: the ring lists do not round-trip");
        eprintln!("conv: tail converter at {}: {} gates, {} CCX (pre-MAC)", tt, g.len(), g.iter().filter(|q0| q0.2 != NONE).count());
        self.b.t(&rev(&g));
        // relabel (CX swaps, no Toffoli): the start's label sets come back, ring X and ring Y as sets, page and freed
        // tops by position, so everything after the cut (page_out / tail list, F's end labels) sees the D16 labels
        let tgt_set = |cur: &[u32], orig: &[u32]| -> Vec<u32> {
            let os: std::collections::HashSet<u32> = orig.iter().copied().collect();
            let cs: std::collections::HashSet<u32> = cur.iter().copied().collect();
            let mut miss = orig.iter().copied().filter(|l| !cs.contains(l));
            let t: Vec<u32> = cur.iter().map(|&l| if os.contains(&l) { l } else { miss.next().expect("conv relabel: set sizes") }).collect();
            assert!(miss.next().is_none(), "conv relabel: set sizes");
            t
        };
        let (tx, ty) = (tgt_set(&x16, &self.cv_x16), tgt_set(&y16, &self.cv_y16));
        let (tp, tf) = (self.cv_pg16.clone(), self.cv_freed.clone());
        let mut dest: HashMap<u32, u32> = HashMap::new();
        for (c, t) in [(&x16, &tx), (&y16, &ty), (&pg16, &tp), (&freed, &tf)] {
            assert_eq!(c.len(), t.len());
            for (&a, &b) in c.iter().zip(t.iter()) { if a != b { dest.insert(a, b); } }
        }
        let vals: std::collections::HashSet<u32> = dest.values().copied().collect();
        assert!(dest.keys().all(|k| vals.contains(k)) && vals.len() == dest.len(), "conv relabel: not a permutation");
        let mut keys: Vec<u32> = dest.keys().copied().collect();
        keys.sort();
        let mut done = std::collections::HashSet::new();
        let mut sw: GL = vec![];
        for &s0 in &keys {
            if done.contains(&s0) { continue; }
            let mut c = vec![s0];
            let mut q0 = dest[&s0];
            while q0 != s0 { c.push(q0); q0 = dest[&q0]; }
            for &l in &c { done.insert(l); }
            for &sj in &c[1..] { sw.extend([G(s0, sj, NONE), G(sj, s0, NONE), G(s0, sj, NONE)]); }
        }
        eprintln!("conv: tail relabel {} labels moved, {} CX", dest.len(), sw.len());
        self.b.t(&sw);
        self.x = tx;
        self.y = ty;
        self.pg = tp;
        self.freed = tf;
        self.wr = WHI;
    }
    /// recorded window_prims gates -> frame gates
    fn pgl(rg: Vec<self::prims_builder::G>) -> GL {
        use self::prims_builder::G as PG;
        let mut g: GL = Vec::with_capacity(rg.len());
        for e in rg {
            match e {
                PG::X(a) => g.push(gx(a.0 as u32)),
                PG::Cx(a, b) => g.push(gc(a.0 as u32, b.0 as u32)),
                PG::Ccx(a, b, c) => g.push(gt(a.0 as u32, b.0 as u32, c.0 as u32)),
                PG::Swap(a, b) => g.extend_from_slice(&[gc(a.0 as u32, b.0 as u32), gc(b.0 as u32, a.0 as u32), gc(a.0 as u32, b.0 as u32)]),
                PG::AndC(a, b, c) | PG::AndU(a, b, c) => g.push(gt(a.0 as u32, b.0 as u32, c.0 as u32)),
                other => panic!("pgl: unexpected prims gate {other:?}"),
            }
        }
        g
    }
    fn qs(v: &[u32]) -> Vec<QubitId> { v.iter().map(|&a| q(a)).collect() }
    /// T1 = tB_low, T2 = tA_low on the page (VA, VB = A, B low) -> SC = the explicit cofactor by the parity of B and
    /// T2 = 0 (T2 = T2 * pivot + other * SC - p). z: a clean lane (0 in and out).
    fn erase_blk(&self, z: u32) -> GL {
        self.erase_blk_d(z, PAGE_D)
    }
    fn erase_blk_d(&self, z: u32, d: usize) -> GL {
        use self::window_prims::{self as wp, Cfg};
        let (va, vb, t1, t2) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d], &self.pg[3 * d..4 * d]);
        let mut g: GL = vec![];
        // z = [B even]
        g.extend_from_slice(&[gx(vb[0]), gc(vb[0], z), gx(vb[0])]);
        for j in 0..d {
            cswap(z, t1[j], t2[j], &mut g);
            cswap(z, va[j], vb[j], &mut g);
        }
        let (qa, qb, q1, q2, qp) = (Self::qs(va), Self::qs(vb), Self::qs(t1), Self::qs(t2), Self::qs(&self.pas[..64]));
        let mut pb = self::prims_builder::B::new();
        let kneg = (1u64 << d) - (wp::P256_LO & ((1u64 << d) - 1));
        let rg = wp::rec(&mut pb, |b| {
            wp::imul(b, Cfg::PY, &q2, &qb, &qp, 0);
            wp::mac(b, Cfg::PY, &q2, &qa, &q1, &qp);
            wp::const_add(b, Cfg::PY, &q2, kneg, &qp);
        });
        g.extend(Self::pgl(rg));
        for j in 0..d {
            cswap(z, va[j], vb[j], &mut g);
        }
        g.extend_from_slice(&[gx(vb[0]), gc(vb[0], z), gx(vb[0])]);
        g
    }
    /// erase_blk controlled by ctrl (the shots whose four low words are being put on / taken off the page).
    fn cerase(&self, ctrl: u32) -> GL {
        use self::window_prims::{self as wp, Cfg};
        let d = PAGE_D;
        let (va, vb, t1, t2) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d], &self.pg[3 * d..4 * d]);
        let z = self.pg[4 * d + 1];
        let zg = self.m(&[(ctrl, true), (vb[0], false)], z);
        let mut g: GL = zg.clone();
        for j in 0..d {
            cswap(z, t1[j], t2[j], &mut g);
            cswap(z, va[j], vb[j], &mut g);
        }
        let (qa, qb, q1, q2, qp) = (Self::qs(va), Self::qs(vb), Self::qs(t1), Self::qs(t2), Self::qs(&self.pas[..64]));
        let mut pb = self::prims_builder::B::new();
        let kneg = (1u64 << d) - (wp::P256_LO & ((1u64 << d) - 1));
        let qc = q(ctrl);
        let rg = wp::rec(&mut pb, |b| {
            wp::cimul(b, Cfg::PY, qc, &q2, &qb, &qp);
            for i in 0..d {
                wp::cc_add_p(b, Cfg::PY, qc, qa[i], &q1[..d - i], &q2[i..], &qp);
            }
            wp::c_const_add(b, Cfg::PY, qc, &q2, kneg, &qp);
        });
        g.extend(Self::pgl(rg));
        for j in 0..d {
            cswap(z, va[j], vb[j], &mut g);
        }
        g.extend(zg);
        g
    }
    /// the four low words of an acting shot (A at X[W-f..], tB under it, B at Y[W-l..], tA under it) <-> the page
    fn swap4(&self, ctrl: u32, l: usize, f: usize) -> GL {
        let d = PAGE_D;
        let (x, y) = (&self.x, &self.y);
        let mut g: GL = vec![];
        for j in 0..d {
            cswap(ctrl, self.pg[j], x[W - f + j], &mut g);
            cswap(ctrl, self.pg[d + j], y[W - l + j], &mut g);
            cswap(ctrl, self.pg[2 * d + j], x[W - f - 1 - j], &mut g);
            cswap(ctrl, self.pg[3 * d + j], y[W - l - 1 - j], &mut g);
        }
        g
    }
    /// at the swap of an act (ctl): the page words trade roles, and when the old B and the new B (A') are both odd the
    /// explicit cofactor changes: SC = tB -> tA' = (p - A' tB) / B = (p - VB SC) / VA after the swap.
    fn post_page(&self, ctl: u32) -> GL {
        use self::window_prims::{self as wp, Cfg};
        let d = PAGE_D;
        let (va, vb, sc) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d]);
        let f = self.pg[4 * d];
        let mut g: GL = vec![];
        for j in 0..d {
            cswap(ctl, va[j], vb[j], &mut g);
        }
        let fg = self.m(&[(ctl, true), (va[0], true), (vb[0], true)], f);
        g.extend_from_slice(&fg);
        let (qa, qb, qc, qp) = (Self::qs(va), Self::qs(vb), Self::qs(sc), Self::qs(&self.pas[..64]));
        let mut pb = self::prims_builder::B::new();
        let k1 = (wp::P256_LO.wrapping_add(1)) & ((1u64 << d) - 1);
        let qf = q(f);
        let zb = [q(ZB_LANE)];
        let cf = if POST_ZB && ZB > 0 { Cfg { clean: &zb, fast: false } } else { Cfg::PY };
        let rg = wp::rec(&mut pb, |b| {
            wp::cimul(b, cf, qf, &qc, &qb, &qp);
            for &s_ in &qc { b.cx(qf, s_); }
            wp::c_const_add(b, cf, qf, &qc, k1, &qp);
            wp::cidiv(b, cf, qf, &qc, &qa, &qp);
        });
        g.extend(Self::pgl(rg));
        g.extend(fg);
        g
    }
    /// K2 step sandwich (v3/c/slot2r_q.py step()): with the quotient's low digits on q (fixed weights, 0 above the
    /// class), A' = A - qB already on VA, B on VB, SC = the explicit cofactor:
    /// select (F = [B even]; cswap VA, VB), K2 half, F = 0: VB -= q SC, F = 1: VB /= (1 + q VA). Returns (pre, post):
    /// pre ends with VB = tA_low (pre-step) when F = 0 and VB = tB_low when F = 1 (the role swap is the caller's);
    /// post = inverse of select and K2 half. act: literals of "this shot acts" (q is junk otherwise).
    fn sandwich(&self, qd: &[u32], z2: u32, acts: &[Vec<Lit>]) -> (GL, GL) {
        self.sandwich_g(qd, z2, acts, &|_j| acts.to_vec(), &|_j| vec![])
    }
    /// as sandwich, with digit j counted only for the shots of actj(j) (pre_S) and with ext(j) added to the AND of
    /// the cubic block (third_T): the classes whose quotient is shorter than j + 1 digits drop digit j (no zero fill).
    fn sandwich_g(&self, qd: &[u32], z2: u32, acts: &[Vec<Lit>], actj: &dyn Fn(usize) -> Vec<Vec<Lit>>, ext: &dyn Fn(usize) -> Vec<Lit>) -> (GL, GL) {
        self.sandwich_x(qd, z2, acts, actj, &|j| vec![ext(j)], &|_j| vec![], &|_j| vec![])
    }
    /// as sandwich_g, with the F = 1 AND gate of digit j split over the disjoint cubes extc(j) (an empty cube = no
    /// extra literal), and extra digit-j terms one0(j) (F = 0 block, act literals included) / one1(j) (F = 1 block,
    /// given z) whose cubes carry their own digit lane: a big class e < D (D > 10) has its weight-e digit on y0.
    fn sandwich_x(&self, qd: &[u32], z2: u32, acts: &[Vec<Lit>], actj: &dyn Fn(usize) -> Vec<Vec<Lit>>, extc: &dyn Fn(usize) -> Vec<Vec<Lit>>, one0: &dyn Fn(usize) -> Vec<Vec<Lit>>, one1: &dyn Fn(usize) -> Vec<Vec<Lit>>) -> (GL, GL) {
        // acts: pairwise disjoint literal sets whose union is "this shot acts" (no ACT lane); qd: the quotient digits
        let qn = qd.len();
        let mx = |me: &Self, base: &[Lit], t: u32| -> GL { let mut g: GL = vec![]; for a in acts { let mut l = base.to_vec(); l.extend_from_slice(a); g.extend(me.m(&l, t)); } g };
        use self::window_prims::{self as wp, Cfg};
        let d = PAGE_D;
        let (va, vb, sc) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d]);
        let (f, z) = (self.pg[4 * d], self.pg[4 * d + 1]);
        let (qa, qb, qc, qp) = (Self::qs(va), Self::qs(vb), Self::qs(sc), Self::qs(&self.pas[..64]));
        // F = [B even] and the shot acts (a non-acting shot takes the F = 0 branch, where every q block is off)
        let mut sel: GL = mx(self, &[(vb[0], false)], f);
        for j in 0..d { cswap(f, va[j], vb[j], &mut sel); }
        let mut pb = self::prims_builder::B::new();
        let k2 = if HOPA || HOPP {
            // catalyst lanes: passenger 1..d (lane 0 is read in even11), the hop's pool: passenger d..64
            let (gd, pl) = (Self::qs(&self.pas[1..d]), Self::qs(&self.pas[d..64]));
            let h = Self::pgl(wp::rec(&mut pb, |b| hop2::hop(b, &qa, &qb, &qc, &gd, &pl, wp::P256_LO, HOPP)));
            if !HOP_SEEN.swap(true, Ordering::Relaxed) {
                eprintln!("hop2: K2 half at D = {} {}: {} CCX one way", d, if HOPP { "parked (HOPP)" } else { "catalyst (HOPA)" }, h.iter().filter(|q0| q0.2 != NONE).count());
            }
            h
        } else {
            Self::pgl(wp::rec(&mut pb, |b| {
                wp::idiv(b, Cfg::PY, &qa, &qb, &qp);
                wp::invp(b, Cfg::PY, &qb, &qp, wp::P256_LO, &[]);
                wp::undo(b, |b| wp::mac(b, Cfg::PY, &qb, &qa, &qc, &qp));
            }))
        };
        let mut pre: GL = sel.clone();
        pre.extend_from_slice(&k2);
        // F = 0: VB -= q SC
        let qm = (0..d).filter(|&j| j < qn || !one0(j).is_empty()).max().map_or(0, |j| j + 1);
        for j in 0..qm {
            let mut zg: GL = vec![];
            if j < qn {
                for a in actj(j) {
                    let mut l: Vec<Lit> = vec![(qd[j], true), (f, false)];
                    l.extend_from_slice(&a);
                    zg.extend(self.m(&l, z));
                }
            }
            for a in one0(j) {
                let mut l: Vec<Lit> = vec![(f, false)];
                l.extend_from_slice(&a);
                zg.extend(self.m(&l, z));
            }
            pre.extend_from_slice(&zg);
            pre.extend(Self::pgl(wp::rec(&mut pb, |b| wp::undo(b, |b| wp::cadd_p(b, Cfg::PY, q(z), &qc[..d - j], &qb[j..], &qp)))));
            pre.extend_from_slice(&zg);
        }
        // F = 1: VB /= (1 + q VA)  (inverse of the top-down multiply)
        let mut mul: GL = vec![];
        for i in (0..=(d - 2)).rev() {
            let zg = mx(self, &[(f, true), (vb[i], true)], z);
            mul.extend_from_slice(&zg);
            for j in 0..qm {
                if i + j + 1 >= d { continue; }
                let ln = d - (i + j + 1);
                let mut z2g: GL = vec![];
                let terms: Vec<(bool, Vec<Lit>)> = {
                    let mut v: Vec<(bool, Vec<Lit>)> = vec![];
                    if j < qn { for c in extc(j) { v.push((true, c)); } }
                    for c in one1(j) { v.push((false, c)); }
                    v
                };
                for (dig_, ex) in terms {
                    if ex.is_empty() {
                        if dig_ { z2g.push(gt(z, qd[j], z2)); } else { z2g.push(gc(z, z2)); }
                    } else {
                        let mut l: Vec<Lit> = vec![(z, true)];
                        if dig_ { l.push((qd[j], true)); }
                        l.extend_from_slice(&ex);
                        ZB_BUSY.store(true, Ordering::Relaxed);
                        z2g.extend(self.m(&l, z2));
                        ZB_BUSY.store(false, Ordering::Relaxed);
                    }
                }
                mul.extend_from_slice(&z2g);
                mul.extend(Self::pgl(wp::rec(&mut pb, |b| wp::cadd_p(b, Cfg::PY, q(z2), &qa[1..1 + ln], &qb[i + j + 1..], &qp))));
                mul.extend_from_slice(&z2g);
            }
            mul.extend_from_slice(&zg);
        }
        pre.extend(rev(&mul));
        let mut post = rev(&k2);
        post.extend(rev(&sel));
        (pre, post)
    }
    fn slot(&mut self, t: i32) {
        if t % 2 == 1 {
            self.odd11(t);
        } else {
            self.even11(t);
        }
    }
    fn odd11(&mut self, t: i32) {
        let wv = self.wr;
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let yt = y[wv - 1];
        let (x0, y0) = (x[0], y[0]);
        let (d, ctl) = (x0, x0);
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let al: Vec<Lit> = cat(&[(yt, true)], &self.hc(0));
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        // a shot at the top with e odd >= 3 waits one slot: code 11
        let g = self.m(&[(yt, true), (h1, true)], h0);
        self.b.t(&g);
        let (l, f) = ((t - 1) / 2, (t + 1) / 2);
        let pgo = PAGE_G && mid_odd(t);
        // P1: every acting shot of an odd slot has e = 1, so its page window is an uncontrolled lane permutation
        let dd = PAGE_D;
        let pd = if pgo { dd } else { 0 };
        let (va, vb, sc) = if pgo { (self.pg[..dd].to_vec(), self.pg[dd..2 * dd].to_vec(), self.pg[2 * dd..3 * dd].to_vec()) } else { (vec![], vec![], vec![]) };
        let (lu, fu) = (l as usize, f as usize);
        if pgo {
            let mut lanes = va.clone();
            lanes.push(x[wv - fu + dd]);
            self.b.t(&rot_free(&lanes, dd));
        }
        if l >= 1 && f <= N as i32 {
            let actv: Vec<Vec<Lit>> = vec![vec![(yt, true), (h0, false)]];
            for k in 0..2usize {
                let alo = wv - l as usize - k + pd;
                let tv: Vec<u32> = (alo..(wv - k - 1)).map(|a| x[a]).collect();
                let sv: Vec<u32> = (alo..(wv - k - 1)).map(|a| y[a + k]).collect();
                let t1 = x[wv - 1 - k];
                let top = if k >= 1 { x[wv - k] } else { NONE };
                let g = self.row_v(&tv, &sv, t1, top, d, h1, NONE, &no_tog, &actv, None, None);
                if pgo {
                    let mut up: GL = vec![];
                    let mut dn: GL = vec![];
                    for b in 0..dd {
                        let (sq, tq) = (vb[b], va[(b + dd - k) % dd]);
                        up.extend_from_slice(&[gx(tq), gc(h1, sq), gc(h1, tq), gt(sq, tq, h1)]);
                    }
                    for b in (0..dd).rev() {
                        let (sq, tq) = (vb[b], va[(b + dd - k) % dd]);
                        dn.extend_from_slice(&[gt(sq, tq, h1), gc(h1, tq), gt(d, sq, tq), gc(h1, sq), gx(tq)]);
                    }
                    pg_add(1, &up); pg_add(1, &dn);
                    self.b.t(&up);
                    self.b.t(&g);
                    self.b.t(&dn);
                } else {
                    self.b.t(&g);
                }
                let mut g: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(x[wv - k], true)]), d));
                    }
                } else {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(d, true)]), y0));
                    }
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(y0, true)]), d));
                    }
                }
                self.b.t(&g);
                if pgo && k == 0 {
                    self.b.t(&swap_free(va[dd - 1], x[wv - lu + dd - 1]));
                }
            }
            let mut sw_post: GL = vec![];
            if pgo {
                self.b.t(&rot_free(&va, 1));
                // digits: dig[0] = Y0 has weight 2, dig[1] = X[wv-1] weight 1; zeros (B's empty ring lanes) above
                // digits: dig[0] = Y0 has weight 2, dig[1] = X[wv-1] weight 1: swap them; q has 2 digits
                let rm: GL = swap_free(y0, x[wv - 1]);
                let q: Vec<u32> = vec![y0, x[wv - 1]];
                let (pre, post) = self.sandwich(&q, d, &[vec![(yt, true), (h0, false)]]);
                let fz = self.pg[4 * dd];
                let mut rs: GL = vec![];
                for j in 0..dd {
                    cswap(fz, vb[j], sc[j], &mut rs);
                }
                pg_add(5, &pre); pg_add(5, &post); pg_add(5, &rs); pg_add(5, &rs);
                self.b.t(&rm);
                self.b.t(&pre);
                self.b.t(&rm);
                self.b.t(&rs);
                self.b.t(&rot_free(&vb, dd - 1));
                sw_post = rs;
                sw_post.extend(post);
            }
            for k in [1usize, 0] {
                let ahi = W - f as usize - 1 + k - pd;
                let wires: Vec<usize> = (k..=ahi).rev().collect();
                let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
                let sv: Vec<u32> = wires.iter().map(|&a| x[a - k]).collect();
                let nn = tv.len();
                let top = if k >= 1 { y[k - 1] } else { NONE };
                let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, h1, NONE, &no_tog, &actv, None, None);
                let mut hh: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(x[wv - k], true)]), d));
                    }
                    hh.push(gc(d, x[wv - k]));
                    let xt = x[wv - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                    }
                    hh.push(gc(d, top));
                } else {
                    let host = x[wv - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(host, true)]), d));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(d, true)]), host));
                    }
                }
                self.b.t(&hh);
                if pgo {
                    let mut gp: GL = vec![];
                    for b in 0..dd {
                        let (sq, tq) = (sc[b], vb[(b + dd - k) % dd]);
                        gp.extend_from_slice(&[gx(tq), gc(h1, sq), gc(h1, tq), gt(sq, tq, h1)]);
                    }
                    pg_add(1, &gp);
                    gp.extend_from_slice(&g);
                    let mut dn: GL = vec![];
                    for b in (0..dd).rev() {
                        let (sq, tq) = (sc[b], vb[(b + dd - k) % dd]);
                        dn.extend_from_slice(&[gt(sq, tq, h1), gc(h1, tq), gt(d, sq, tq), gc(h1, sq), gx(tq)]);
                    }
                    pg_add(1, &dn);
                    gp.extend(dn);
                    self.b.t(&rev(&gp));
                    if k == 1 {
                        self.b.t(&swap_free(vb[dd - 1], y[W - fu - dd]));
                    }
                } else {
                    self.b.t(&rev(&g));
                }
            }
            if pgo {
                let mut lanes = vb.clone();
                lanes.push(y[W - lu - 1 - dd]);
                self.b.t(&rot_free(&lanes, 1));
                self.b.t(&sw_post);
            }
        }
        let g = self.m(&cat(&al, &[(y[0], false)]), ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, wv - 1);
        self.b.t(&g);
        let g = self.m(&al, ctl);
        self.b.t(&g);
        let mut g = vec![];
        for w in 1..wv {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        if pgo {
            let g = self.post_page(ctl);
            pg_add(7, &g);
            self.b.t(&g);
        }
        let xt = x[wv - 1];
        self.b.t(&[gc(ctl, y[wv - 1])]);
        let g = self.m(&al, ctl);
        self.b.t(&g);
        let fl = y[wv - 1];
        let aa = cat(&[(fl, true)], &self.hc(0));
        let win: Vec<u32> = y[..wv - 1].to_vec();
        let g = self.m(&cat(&aa, &[(xt, false), (y[wv - 2], false)]), ctl);
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&cat(&aa, &[(xt, false), (y[0], false)]), ctl);
        self.b.t(&g);
        // acted: E'=0 and the second state take code 01 (the common rise gives 00); E'=2 stays 00 (the rise gives 10 and a marker)
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hc(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hc(0)), ctl));
        g.push(gc(ctl, h0));
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hc(1)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hc(1)), ctl));
        self.b.t(&g);
        let mut g = self.m(&cat(&[(xt, true), (y[0], true)], &self.hc(1)), fl);
        g.extend(self.m(&cat(&[(xt, false), (y[0], false), (y[1], true)], &self.hc(0)), fl));
        g.extend(self.m(&cat(&[(y[wv - 2], true), (xt, false), (y[0], true)], &self.hc(1)), fl));
        self.b.t(&g);
        self.b.t(&[gx(y[wv - 1]), gc(y[wv - 1], ctl), gx(y[wv - 1])]);
        // one slot of rise for every shot not at the top
        let mut g = self.m(&cat(&[(ctl, true)], &self.hc(0)), y[0]);
        g.extend(self.m(&[(ctl, true), (y[0], true), (h0, false)], h1));
        g.extend(self.m(&[(ctl, true), (h1, false)], h0));
        g.extend(self.m(&[(ctl, true), (h0, true), (xt, true), (y[wv - 3], true)], h1));
        g.extend(self.m(&[(ctl, true), (h0, true), (xt, false), (y[wv - 4], true)], h1));
        g.extend(self.m(&cat(&[(ctl, true), (xt, true)], &self.hc(1)), y[wv - 3]));
        g.extend(self.m(&cat(&[(ctl, true), (xt, false)], &self.hc(1)), y[wv - 4]));
        self.b.t(&g);
        let g = rotate_up(ctl, &y, 1);
        self.b.t(&g);
        let yt2 = y[wv - 1];
        let mut g = vec![gx(ctl)];
        g.extend(self.m(&cat(&[(yt2, true)], &self.hc(3)), ctl));
        g.extend(self.m(&cat(&[(yt2, true)], &self.hc(1)), ctl));
        self.b.t(&g);
        self.arrive11(t - 1, &y, ctl);
        // the second state acts at the next even slot
        let g = self.m(&[(yt2, true), (xt, false), (y[0], false), (y[1], true), (h1, false)], h0);
        self.b.t(&g);
        self.b.t(&[gx(ctl)]);
    }
    fn even11(&mut self, t: i32) {
        let wv = self.wr;
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let prs: Vec<i32> = pairs(t).into_iter().filter(|&e| e <= 9).collect();
        let big: Vec<i32> = prs.iter().cloned().filter(|&e| e >= 2).collect();
        let kk = 1 + big.iter().cloned().max().unwrap_or(0);
        let yt = y[wv - 1];
        let (x0, y0, y1) = (x[0], y[0], y[1]);
        let (d, ctl) = (x0, x0);
        let cl: Vec<Lit> = vec![(yt, true), (h1, true)];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        let mut g: GL = vec![];
        for &e in &big {
            if e & 1 == 1 {
                let mut l = cl.clone();
                for j in 1..(e as usize - 1) {
                    l.push((y[j], false));
                }
                l.push((y[e as usize - 1], true));
                g.extend(self.m(&l, h0));
            }
        }
        self.b.t(&g);
        let sp0: Vec<Lit> = cat(&[(yt, true)], &self.hc(0));
        self.mk(t, 1);
        let sp1: Vec<Lit> = cat(&cat(&[(yt, true)], &self.hc(1)), &[(y1, true)]);
        let sp1c: Vec<Lit> = cat(&cat(&[(yt, true)], &self.hc(1)), &[(x[wv - 1], false), (x[wv - 2], false)]);
        let merge0 = prs.contains(&0) && !big.is_empty();
        if prs.contains(&0) && !merge0 {
            let (l, _f) = lf(t, 0);
            let lu = l as usize;
            let c1 = self.m(&sp0, d);
            self.b.t(&c1);
            let tv: Vec<u32> = ((wv - lu)..(wv - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = ((wv - lu)..(wv - 1)).map(|a| y[a]).collect();
            let g = self.plain_v(&tv, &sv, x[wv - 1], d, h0);
            self.b.t(&g);
            self.b.t(&c1);
        }
        if prs.contains(&1) {
            let (l, _f) = lf(t, 1);
            let lu = l as usize;
            let c1 = self.m(&sp1, d);
            self.b.t(&c1);
            // P1: e = 1 at an even slot (q = 1, shift 0): with the global page its chain starts at B bit D
            let pg1 = PAGE_G && mid_even(t);
            let s0 = if pg1 { PAGE_D } else { 0 };
            let tv: Vec<u32> = ((wv - lu - 1 + s0)..(wv - 2)).map(|a| x[a]).collect();
            let sv: Vec<u32> = ((wv - lu - 1 + s0)..(wv - 2)).map(|a| y[a + 1]).collect();
            let g = self.plain_v(&tv, &sv, x[wv - 2], d, h1);
            if pg1 {
                let (pa, pb) = (&self.pg[..PAGE_D], &self.pg[PAGE_D..2 * PAGE_D]);
                let mut up: GL = vec![];
                let mut dn: GL = vec![];
                for b in 0..PAGE_D {
                    up.extend_from_slice(&[gx(pa[b]), gc(h1, pb[b]), gc(h1, pa[b]), gt(pb[b], pa[b], h1)]);
                }
                for b in (0..PAGE_D).rev() {
                    dn.extend_from_slice(&[gt(pb[b], pa[b], h1), gc(h1, pa[b]), gt(d, pb[b], pa[b]), gc(h1, pb[b]), gx(pa[b])]);
                }
                pg_add(1, &up); pg_add(1, &dn);
                self.b.t(&up);
                self.b.t(&g);
                self.b.t(&dn);
            } else {
                self.b.t(&g);
            }
            self.b.t(&c1);
        }
        self.mk(t, 2);
        let lik = |k: i32| -> Vec<Lit> {
            let mut l = cl.clone();
            if k >= 3 {
                for j in 1..(k as usize - 1) {
                    l.push((y[j], false));
                }
            }
            l
        };
        let pgo = PAGE_G && mid_even(t);
        assert!(!pgo || (merge0 && !big.is_empty()));
        let pv = (PAGE_V || PAGE_C || pgo) && mid_even(t) && !big.is_empty();
        let pc = (PAGE_C || pgo) && pv;
        let local = pc && !pgo;
        let pd0 = if pgo { PAGE_D as i32 } else { 0 };
        let pdc = if pc { PAGE_D as i32 } else { 0 };
        let sc: Vec<u32> = if pc { self.pg[2 * PAGE_D..3 * PAGE_D].to_vec() } else { vec![] };
        let dig: Vec<u32> = (0..PAGE_D.min(10)).map(|k| if k == 0 { y0 } else { x[wv - k] }).collect();
        let pd = if pv { PAGE_D as i32 } else { 0 };
        let (va, vb): (Vec<u32>, Vec<u32>) = if pv { (self.pg[..PAGE_D].to_vec(), self.pg[PAGE_D..2 * PAGE_D].to_vec()) } else { (vec![], vec![]) };
        // flag of exactly class e (or of a set of classes sharing l): lik(lo) xor lik(hi + 1)
        let zf = if pv { self.pg[4 * PAGE_D + 1] } else { NONE };
        let lad = LADDER && pgo && (2..=9).all(|e| big.contains(&e));
        // digit remap of class e (reverse dig[0..=e]) under control c
        let rmb = |c: u32, e: i32| -> GL {
            let mut rm: GL = vec![];
            let eu = e as usize;
            let mut i = 0usize;
            while i < eu - i {
                cswap(c, dig[i], dig[eu - i], &mut rm);
                i += 1;
            }
            rm
        };
        let fl_cls = |me: &Self, lo: i32, hi: i32| -> GL {
            // exactly class e: (yt, h1), Y[1..e-2] zero, marker Y[e-1]; AND on the clean lane Z (2k - 3)
            let mut g: GL = vec![];
            for e in lo..=hi {
                let mut l = cl.clone();
                for j in 1..(e as usize - 1) {
                    l.push((y[j], false));
                }
                l.push((y[e as usize - 1], true));
                g.extend(me.mz(&l, d, zf));
            }
            g
        };
        let fl_cit = |me: &Self, kp: i32, es: &[i32]| -> GL {
            let mut g: GL = vec![];
            for &e in es {
                let mut l = lik(kp.max(0));
                l.push((x[wv - e as usize], true));
                for j in kp.max(2)..e {
                    l.push((x[wv - j as usize], false));
                }
                g.extend(me.mz(&l, d, zf));
            }
            g
        };
        // P1 (b2): local gather of the four low words of every acting low-class shot, then the implicit word is erased
        let gather4 = |me: &Self, post: bool| -> GL {
            let mut g: GL = vec![];
            for &e in &big {
                let (l, f) = lf(t, e);
                let (lu, fu) = (l as usize, f as usize);
                let fl = if post { fl_cit(me, 0, &[e]) } else { fl_cls(me, e, e) };
                g.extend_from_slice(&fl);
                let mut ga: GL = vec![];
                for j in 0..PAGE_D {
                    cswap(d, va[j], x[wv - fu + j], &mut ga);
                    cswap(d, vb[j], y[wv - lu + j], &mut ga);
                    cswap(d, me.pg[2 * PAGE_D + j], x[W - fu - 1 - j], &mut ga);
                    cswap(d, me.pg[3 * PAGE_D + j], y[W - lu - 1 - j], &mut ga);
                }
                pg_add(0, &ga); pg_add(4, &fl); pg_add(4, &fl);
                g.extend(ga);
                g.extend_from_slice(&fl);
            }
            g
        };
        if local {
            let mut g = gather4(self, false);
            let er = self.erase_blk(d);
            pg_add(0, &er);
            g.extend(er);
            self.b.t(&g);
        }
        if lad {
            let g = self.ladder("V-win-in", &|set, c| {
                let e = set[0];
                let fu = lf(t, e).1 as usize;
                let mut lanes = va.clone();
                lanes.extend((0..e as usize).map(|i| x[wv - fu + PAGE_D + i]));
                let n = lanes.len();
                let ro = rotate_up(c, &lanes, n - e as usize);
                pg_add(2, &ro);
                ro
            });
            self.b.t(&g);
        } else if pv {
            let mut g: GL = vec![];
            for &e in &big {
                let (l, f) = lf(t, e);
                let (lu, fu) = (l as usize, f as usize);
                let fl = fl_cls(self, e, e);
                g.extend_from_slice(&fl);
                let mut ga: GL = vec![];
                for j in 0..(if pc { 0 } else { PAGE_D }) {
                    cswap(d, va[j], x[wv - fu + j], &mut ga);
                    cswap(d, vb[j], y[wv - lu + j], &mut ga);
                }
                let mut lanes = va.clone();
                lanes.extend((0..e as usize).map(|i| x[wv - fu + PAGE_D + i]));
                let n = lanes.len();
                let ro = rotate_up(d, &lanes, n - e as usize);
                pg_add(0, &ga); pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend(ga);
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
        }
        self.mk(t, 3);
        for k in 0..kk {
            let act: Vec<i32> = big.iter().cloned().filter(|&e| e >= k).collect();
            if act.is_empty() {
                continue;
            }
            let starts: Vec<(i32, i32)> = act.iter().map(|&e| (e, wv as i32 - lf(t, e).0 - k + pd)).collect();
            let m0 = merge0 && k == 0;
            let alo1 = starts.iter().map(|p| p.1).min().unwrap();
            let shi = starts.iter().map(|p| p.1).max().unwrap();
            let alo = if m0 { (wv as i32) - t / 2 + pd0 } else { alo1 };
            assert!(!m0 || alo < alo1);
            let (ku, alo_u) = (k as usize, alo as usize);
            let tv: Vec<u32> = (alo_u..(wv - ku - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = (alo_u..(wv - ku - 1)).map(|a| y[a + ku]).collect();
            let t1 = x[wv - 1 - ku];
            let top = if k >= 1 { x[wv - ku] } else { NONE };
            let li = lik(k);
            let actv: Vec<Vec<Lit>> = vec![li];
            let mn = *act.iter().min().unwrap();
            let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for i in 0..(shi - alo + 1) {
                let a = alo + i;
                let nx = starts.iter().filter(|p| p.1 > a).map(|p| p.0).min();
                let e: Vec<Vec<Lit>> = if m0 && a < alo1 {
                    vec![vec![], vec![(h1, true)]]
                } else {
                    match nx {
                        None => vec![vec![]],
                        Some(n) => {
                            let lo = (mn - 1).max(1) as usize;
                            let mut ch: Vec<Lit> = vec![];
                            if m0 {
                                ch.push((h1, true));
                            }
                            ch.extend((lo..(n as usize - 1)).map(|j| (y[j], false)));
                            vec![vec![], ch]
                        }
                    }
                };
                il.insert(i as usize, e);
            }
            let g = self.row_vz(&tv, &sv, t1, top, d, h0, NONE, &no_tog, &actv, Some(&il), None, m0);
            let c1 = if m0 { self.m(&sp0, d) } else { vec![] };
            self.b.t(&c1);
            if pv {
                // page cells: the bottom D cells of the row's chain, source bit b <-> window lane (b - k) mod D
                let mut up: GL = vec![];
                for b in 0..PAGE_D {
                    let (sq, tq) = (vb[b], va[(b + PAGE_D - ku % PAGE_D) % PAGE_D]);
                    up.extend_from_slice(&[gx(tq), gc(h0, sq), gc(h0, tq), gt(sq, tq, h0)]);
                }
                pg_add(1, &up);
                self.b.t(&up);
                self.b.t(&g);
                let mut dn: GL = vec![];
                for b in (0..PAGE_D).rev() {
                    let (sq, tq) = (vb[b], va[(b + PAGE_D - ku % PAGE_D) % PAGE_D]);
                    dn.extend_from_slice(&[gt(sq, tq, h0), gc(h0, tq), gt(d, sq, tq), gc(h0, sq), gx(tq)]);
                }
                pg_add(1, &dn);
                self.b.t(&dn);
            } else {
                self.b.t(&g);
            }
            let mut g: GL = vec![];
            if k >= 1 {
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(x[wv - ku], true)]), d));
                }
            } else {
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(d, true)]), y0));
                }
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(y0, true)]), d));
                }
            }
            self.b.t(&g);
            self.b.t(&c1);
            if lad && k <= 8 {
                let g = self.ladder(&format!("V-row{k}"), &|set, c| {
                    let es: Vec<i32> = set.iter().cloned().filter(|&e| e >= k + 1).collect();
                    let l = lf(t, es[0]).0;
                    assert!(es.iter().all(|&e| lf(t, e).0 == l));
                    let mut sw: GL = vec![];
                    cswap(c, va[(PAGE_D - 1 - ku % PAGE_D) % PAGE_D], x[wv - l as usize + PAGE_D - ku - 1], &mut sw);
                    pg_add(3, &sw);
                    sw
                });
                self.b.t(&g);
            } else if pv {
                // the window slides down one bit: the lane leaving it trades with the ring wire just below the next start
                let mut g: GL = vec![];
                let mut grp: BTreeMap<i32, Vec<i32>> = BTreeMap::new();
                for &e in big.iter().filter(|&&e| e >= k + 1) {
                    grp.entry(lf(t, e).0).or_default().push(e);
                }
                for (l, es) in grp {
                    let (lo, hi) = (*es.iter().min().unwrap(), *es.iter().max().unwrap());
                    assert!(hi - lo + 1 == es.len() as i32);
                    let fl = fl_cls(self, lo, hi);
                    g.extend_from_slice(&fl);
                    let mut sw: GL = vec![];
                    cswap(d, va[(PAGE_D - 1 - ku % PAGE_D) % PAGE_D], x[wv - l as usize + PAGE_D - ku - 1], &mut sw);
                    pg_add(3, &sw); pg_add(4, &fl); pg_add(4, &fl);
                    g.extend(sw);
                    g.extend_from_slice(&fl);
                }
                self.b.t(&g);
            }
        }
        self.mk(t, 4);
        let mut sw_post: GL = vec![];
        if pv {
            // per class: V window-out; in PAGE_C mode also the digit remap (dig[k] has weight 2^(e-k): reverse
            // dig[0..=e], park B's empty ring lanes as zeros above e). One flag bracket for both.
            let mut g: GL = vec![];
            let mut rms: Vec<GL> = vec![];
            if lad {
                g = self.ladder("V-win-out", &|set, c| {
                    let e = set[0];
                    let mut r = rotate_up(c, &va, e as usize % PAGE_D);
                    let rm = rmb(c, e);
                    pg_add(2, &r); pg_add(5, &rm);
                    r.extend(rm);
                    r
                });
            }
            for &e in big.iter().filter(|_| !lad) {
                let (l, f) = lf(t, e);
                let (lu, fu) = (l as usize, f as usize);
                let fl = fl_cls(self, e, e);
                g.extend_from_slice(&fl);
                let ro = rotate_up(d, &va, e as usize % PAGE_D);
                let mut ga: GL = vec![];
                for j in 0..(if pc { 0 } else { PAGE_D }) {
                    cswap(d, va[j], x[wv - fu + j], &mut ga);
                    cswap(d, vb[j], y[wv - lu + j], &mut ga);
                }
                let mut rm: GL = vec![];
                if pc {
                    let eu = e as usize;
                    let mut i = 0usize;
                    while i < eu - i {
                        cswap(d, dig[i], dig[eu - i], &mut rm);
                        i += 1;
                    }
                }
                pg_add(0, &ga); pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl); pg_add(5, &rm); pg_add(5, &rm);
                g.extend(ro);
                g.extend(ga);
                g.extend_from_slice(&rm);
                g.extend_from_slice(&fl);
                rms.push(rm);
            }
            // e = 0 (global page only): q = 1 -> Q[0] = 1, B's empty ring lanes as zeros above it
            let mut rm0: GL = vec![];
            if pgo {
                let l0 = lf(t, 0).0 as usize;
                let fl = self.mz(&sp0, d, zf);
                rm0.extend_from_slice(&fl);
                rm0.push(gc(d, dig[0]));
                rm0.extend_from_slice(&fl);
                if prs.contains(&1) {
                    let l1 = lf(t, 1).0 as usize;
                    let fl = self.mz(&sp1c, d, zf);
                    rm0.extend_from_slice(&fl);
                    rm0.push(gc(d, dig[0]));
                    rm0.extend_from_slice(&fl);
                }
                pg_add(5, &rm0); pg_add(5, &rm0);
                g.extend_from_slice(&rm0);
            }
            // the acting shots of this slot's rows: low classes, and e = 0 with the global page (disjoint terms)
            let mut acts: Vec<Vec<Lit>> = if pgo { vec![cl.clone(), sp0.clone()] } else { vec![cl.clone()] };
            if pgo && prs.contains(&1) {
                acts.push(sp1c.clone());
            }
            self.b.t(&g);
            if pc {
                // digit j counts for: j = 0 every acting shot; j = 1, 2 the low classes; j >= 3 the classes >= j
                let lowc = cl.clone();
                let ext_y: Vec<u32> = y.clone();
                let actj = |j: usize| -> Vec<Vec<Lit>> {
                    if j == 0 { return acts.clone(); }
                    let mut l = lowc.clone();
                    for i in 1..(j.max(2) - 1) { l.push((ext_y[i], false)); }
                    vec![l]
                };
                let ext = |j: usize| -> Vec<Lit> {
                    if j == 0 { return vec![]; }
                    let mut l = vec![(h1, true)];
                    for i in 1..(j.max(2) - 1) { l.push((ext_y[i], false)); }
                    l
                };
                let (pre, post) = self.sandwich_g(&dig, d, &acts, &actj, &ext);
                let fz = self.pg[4 * PAGE_D];
                let mut rs: GL = vec![];
                for j in 0..PAGE_D {
                    cswap(fz, vb[j], sc[j], &mut rs);
                }
                pg_add(5, &pre); pg_add(5, &post); pg_add(5, &rs); pg_add(5, &rs);
                self.b.t(&pre);
                self.b.t(&rs);
        self.mk(t, 5);
                // per class: remap back, then the cofactor window (inverse of its window-out: rotate VB by -e)
                let mut cw: GL = vec![];
                if lad {
                    cw = self.ladder("cw", &|set, c| {
                        let e = set[0];
                        let mut r = rmb(c, e);
                        let ro = rotate_up(c, &vb, (PAGE_D - e as usize % PAGE_D) % PAGE_D);
                        pg_add(2, &ro); pg_add(5, &r);
                        r.extend(ro);
                        r
                    });
                }
                for (ie, &e) in big.iter().enumerate().filter(|_| !lad) {
                    let fl = fl_cls(self, e, e);
                    let ro = rotate_up(d, &vb, (PAGE_D - e as usize % PAGE_D) % PAGE_D);
                    pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                    cw.extend_from_slice(&fl);
                    cw.extend_from_slice(&rms[ie]);
                    cw.extend(ro);
                    cw.extend_from_slice(&fl);
                }
                self.b.t(&rm0);
                self.b.t(&cw);
                sw_post = rs;
                sw_post.extend(post);
            }
        }
        self.mk(t, 6);
        for k in (0..kk).rev() {
            let act: Vec<i32> = big.iter().cloned().filter(|&e| e >= k).collect();
            if act.is_empty() {
                continue;
            }
            let ku = k as usize;
            let li = lik(k);
            let actv: Vec<Vec<Lit>> = vec![li.clone()];
            let flag = k >= 2 && big.contains(&k);
            if flag {
                let mut g = self.m(&cat(&li, &[(y[ku - 1], true)]), h0);
                g.extend(self.m(&cat(&li, &[(h0, true)]), y[ku - 1]));
                self.b.t(&g);
            }
            let starts: Vec<(i32, i32)> = act.iter().map(|&e| (e, W as i32 - lf(t, e).1 - 1 + k - pdc)).collect();
            let m0 = merge0 && k == 0;
            let ahi1 = starts.iter().map(|p| p.1).max().unwrap();
            let slo = starts.iter().map(|p| p.1).min().unwrap();
            let ahi = if m0 { (W as i32) - t / 2 - 1 - pd0 } else { ahi1 };
            assert!(!m0 || ahi > ahi1);
            let wires: Vec<usize> = (ku..=(ahi as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let c = if k >= 2 { x[wv - ku] } else { h0 };
            let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for i in 0..(ahi - slo + 1) {
                let a = ahi - i;
                let nx = starts.iter().filter(|p| p.1 < a).map(|p| p.0).min();
                let e: Vec<Vec<Lit>> = if m0 && a > ahi1 {
                    vec![vec![], vec![(h1, true)]]
                } else {
                    match nx {
                        None => vec![vec![]],
                        Some(n) => {
                            let jlo = (k + 1).max(2);
                            let mut ch: Vec<Lit> = vec![];
                            if m0 {
                                ch.push((h1, true));
                            }
                            if k >= 2 {
                                ch.push((h0, false));
                            }
                            for j in jlo..n {
                                ch.push((x[wv - j as usize], false));
                            }
                            vec![vec![], ch]
                        }
                    }
                };
                il.insert(i as usize, e);
            }
            let g = self.row_vz(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, NONE, &no_tog, &actv, Some(&il), None, m0);
            let c1 = if m0 { self.m(&sp0, d) } else { vec![] };
            let mut hh: GL = vec![];
            if k >= 1 {
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(x[wv - ku], true)]), d));
                }
                hh.push(gc(d, x[wv - ku]));
                if k == 1 {
                    let xt = x[wv - 1];
                    for l_ in &actv {
                        hh.extend(self.m(&cat(l_, &[(y0, true)]), xt));
                    }
                    for l_ in &actv {
                        hh.extend(self.m(&cat(l_, &[(xt, true)]), y0));
                    }
                }
                hh.push(gc(d, top));
            } else {
                let host = x[wv - 1];
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(host, true)]), d));
                }
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(d, true)]), host));
                }
            }
            self.b.t(&hh);
            self.b.t(&c1);
            if pc {
                let mut gp: GL = vec![];
                for b in 0..PAGE_D {
                    let (sq, tq) = (sc[b], vb[(b + PAGE_D - ku % PAGE_D) % PAGE_D]);
                    gp.extend_from_slice(&[gx(tq), gc(c, sq), gc(c, tq), gt(sq, tq, c)]);
                }
                pg_add(1, &gp);
                gp.extend_from_slice(&g);
                let mut dn: GL = vec![];
                for b in (0..PAGE_D).rev() {
                    let (sq, tq) = (sc[b], vb[(b + PAGE_D - ku % PAGE_D) % PAGE_D]);
                    dn.extend_from_slice(&[gt(sq, tq, c), gc(c, tq), gt(d, sq, tq), gc(c, sq), gx(tq)]);
                }
                pg_add(1, &dn);
                gp.extend(dn);
                self.b.t(&rev(&gp));
            } else {
                self.b.t(&rev(&g));
            }
            self.b.t(&c1);
            if flag {
                let mut g = self.m(&cat(&li, &[(h0, true)]), x[wv - ku]);
                g.extend(self.m(&cat(&li, &[(x[wv - ku], true)]), h0));
                self.b.t(&g);
            }
            if lad && k >= 1 {
                let g = self.ladder(&format!("C-row{k}"), &|set, c| {
                    let es: Vec<i32> = set.iter().cloned().filter(|&e| e >= k).collect();
                    let f = lf(t, es[0]).1;
                    assert!(es.iter().all(|&e| lf(t, e).1 == f));
                    let mut sw: GL = vec![];
                    cswap(c, vb[(PAGE_D - ku % PAGE_D) % PAGE_D], y[W - f as usize - PAGE_D + ku - 1], &mut sw);
                    pg_add(3, &sw);
                    sw
                });
                self.b.t(&g);
            } else if pc && k >= 1 {
                // inverse of the cofactor window's slide after V-style row k - 1 (classes e >= k, grouped by f)
                let mut g: GL = vec![];
                let mut grp: BTreeMap<i32, Vec<i32>> = BTreeMap::new();
                for &e in big.iter().filter(|&&e| e >= k) {
                    grp.entry(lf(t, e).1).or_default().push(e);
                }
                for (f, es) in grp {
                    let fl = fl_cit(self, k, &es);
                    let mut sw: GL = vec![];
                    cswap(d, vb[(PAGE_D - ku % PAGE_D) % PAGE_D], y[W - f as usize - PAGE_D + ku - 1], &mut sw);
                    pg_add(3, &sw); pg_add(4, &fl); pg_add(4, &fl);
                    g.extend_from_slice(&fl);
                    g.extend(sw);
                    g.extend_from_slice(&fl);
                }
                self.b.t(&g);
            }
        }
        if pc {
            let mut g: GL = vec![];
            if lad {
                g = self.ladder("C-win-out", &|set, c| {
                    let e = set[0];
                    let lu = lf(t, e).0 as usize;
                    let mut lanes = vb.clone();
                    lanes.extend((0..e as usize).map(|i| y[W - lu - 1 - PAGE_D - i]));
                    let ro = rotate_up(c, &lanes, e as usize);
                    pg_add(2, &ro);
                    ro
                });
            }
            for &e in big.iter().filter(|_| !lad) {
                let lu = lf(t, e).0 as usize;
                let fl = fl_cit(self, 0, &[e]);
                let mut lanes = vb.clone();
                lanes.extend((0..e as usize).map(|i| y[W - lu - 1 - PAGE_D - i]));
                let ro = rotate_up(d, &lanes, e as usize);
                pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
            if !pgo {
                self.b.t(&sw_post);
            }
            if local {
                let er = rev(&self.erase_blk(d));
                pg_add(0, &er);
                self.b.t(&er);
                let g = gather4(self, true);
                self.b.t(&g);
            }
        }
        self.mk(t, 7);
        if prs.contains(&0) && !merge0 {
            let (_l, f) = lf(t, 0);
            let mb = W - f as usize;
            let wires: Vec<usize> = (0..mb).rev().collect();
            let c1 = self.m(&sp0, d);
            self.b.t(&c1);
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a]).collect();
            let nn = tv.len();
            let g = self.plain_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], d, x[wv - 1]);
            self.b.t(&rev(&g));
            self.b.t(&c1);
        }
        if prs.contains(&1) {
            let (_l, f) = lf(t, 1);
            let mb = W - f as usize;
            let wires: Vec<usize> = (1..=mb).rev().collect();
            let c1 = self.m(&sp1c, d);
            self.b.t(&c1);
            let pg1 = PAGE_G && mid_even(t);
            let wires: Vec<usize> = if pg1 { (1..=(mb - PAGE_D)).rev().collect() } else { wires };
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - 1]).collect();
            let nn = tv.len();
            let g = self.plain_vt(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], y[0], d, x[wv - 1]);
            if pg1 {
                let (pb, ps) = (&self.pg[PAGE_D..2 * PAGE_D], &self.pg[2 * PAGE_D..3 * PAGE_D]);
                let c = x[wv - 1];
                let mut gp: GL = vec![];
                for b in 0..PAGE_D {
                    gp.extend_from_slice(&[gx(pb[b]), gc(c, ps[b]), gc(c, pb[b]), gt(ps[b], pb[b], c)]);
                }
                pg_add(1, &gp);
                gp.extend_from_slice(&g);
                let mut dn: GL = vec![];
                for b in (0..PAGE_D).rev() {
                    dn.extend_from_slice(&[gt(ps[b], pb[b], c), gc(c, pb[b]), gt(d, ps[b], pb[b]), gc(c, ps[b]), gx(pb[b])]);
                }
                pg_add(1, &dn);
                gp.extend(dn);
                self.b.t(&rev(&gp));
            } else {
                self.b.t(&rev(&g));
            }
            self.b.t(&c1);
        }
        self.mk(t, 8);
        if pgo {
            self.b.t(&sw_post);
        }
        self.mk(t, 9);
        // waiters step aside: a down-rotation now, the relabel below undoes it
        let hold1: Vec<Lit> = cat(&[(yt, true)], &self.hc(1));
        let mut g = self.m(&cat(&hold1, &[(x[wv - 1], true)]), ctl);
        g.extend(self.m(&cat(&hold1, &[(x[wv - 1], false), (x[wv - 2], true)]), ctl));
        self.b.t(&g);
        let g = rotate_up(ctl, &y, wv - 1);
        self.b.t(&g);
        let g = self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], true)], &self.hc(1)), ctl);
        self.b.t(&g);
        self.mk(t, 10);
        // post
        let g = self.m(&[(yt, true), (y[0], false)], ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, wv - 1);
        self.b.t(&g);
        self.b.t(&[gc(y[wv - 1], ctl)]);
        let mut g = vec![];
        for w in 1..wv {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        if pgo {
            let g = self.post_page(ctl);
            pg_add(7, &g);
            self.b.t(&g);
        }
        self.mk(t, 11);
        let xt = x[wv - 1];
        self.b.t(&[gc(ctl, y[wv - 1])]);
        self.b.t(&[gc(y[wv - 1], ctl)]);
        self.mk(t, 12);
        let mut ny = vec![y[wv - 1]];
        ny.extend_from_slice(&y[..wv - 1]);
        self.y = ny.clone();
        let y = ny;
        let mut d2 = self.pas.clone();
        d2.extend_from_slice(&self.x);
        d2.extend_from_slice(&y);
        self.dirty = d2;
        let act = y[0];
        let win: Vec<u32> = y[1..].to_vec();
        // parity: rotate the new N by r. The marker sits at wv-e+1, everything above it is zero.
        let mut g = self.m(&cat(&[(act, true)], &self.hc(1)), ctl);
        for &e in &big {
            if e & 1 == 1 {
                let eu = e as usize;
                let mut l = cat(&[(act, true)], &self.hc(2));
                for i in 0..(eu - 2) {
                    l.push((y[wv - 1 - i], false));
                }
                l.push((y[wv - eu + 1], true));
                g.extend(self.m(&l, ctl));
            }
        }
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&[(act, true), (y[1], false)], ctl);
        self.b.t(&g);
        // final codes; the marker of a shot that stays in 11 is already in place
        let aa: Vec<Lit> = vec![(act, true)];
        let mut g = self.m(&cat(&aa, &[(h1, false), (y[1], false)]), h0);
        g.extend(self.m(&cat(&aa, &[(h1, true), (y[wv - 1], true)]), h0));
        g.extend(self.m(&cat(&aa, &self.hc(3)), y[wv - 1]));
        g.extend(self.m(&cat(&aa, &[(h0, true)]), h1));
        g.extend(self.m(&cat(&aa, &[(h1, false), (xt, false)]), h0));
        g.extend(self.m(&cat(&aa, &[(h1, true), (xt, false), (y[wv - 3], true)]), h0));
        g.extend(self.m(&cat(&cat(&aa, &self.hc(3)), &[(xt, false)]), y[wv - 3]));
        g.extend(self.m(&cat(&aa, &[(h0, true), (xt, false)]), h1));
        g.extend(self.m(&cat(&aa, &[(h1, true)]), h0));
        self.b.t(&g);
        let g1 = self.m(&[(act, true), (xt, false)], ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        let mut g = self.m(&[(xt, true), (y[1], true)], act);
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true), (h1, false)], act));
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true), (h1, true), (h0, true)], act));
        g.extend(self.m(&[(xt, true), (y[1], false), (y[2], true), (h0, true)], act));
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], false), (y[3], true)], act));
        self.b.t(&g);
        if t + 1 <= 2 * N as i32 {
            let tau = ctl;
            let gl = cat(&[(xt, true), (y[1], false), (y[2], true)], &self.hc(0));
            let tg = self.m(&gl, tau);
            self.b.t(&tg);
            let p0 = self.pas[0];
            let (p12, p3) = self.pi10(t + 1, h1, h0, y[1], p0);
            self.b.t(&p12);
            let q = self.m(&[(tau, true), (h0, false), (y[1], true), (p0, true)], act);
            self.b.t(&q);
            self.b.t(&p3);
            self.b.t(&q);
            self.b.t(&rev(&p3));
            self.b.t(&rev(&p12));
            self.b.t(&tg);
        }
        if t % 8 == 0 && !self.big_pairs11(t).is_empty() {
            self.big_phase(t);
        }
        self.arrive11(t - 1, &y, ctl);
        self.b.t(&[gx(ctl)]);
    }
    fn big_pairs11(&self, t: i32) -> Vec<(i32, i32, i32, i32)> {
        let mut out = vec![];
        // L-C banded: inside [CUT_T, CUT_S - 17] the long classes act only at slots 0 mod 16 (w < 16), else w < 8
        // a long case whose wait to the slot 0 mod 16 would leave u = (e - w) / 2 = 1 ((16, 14), (17, 15)) acts at the slot
        // 8 mod 16 before it instead, as (e, w - 8) (the frame's post has no u = 1 form)
        let ok = |e: i32, w: i32| -> bool {
            if !(TIER_LONG > 0 && e >= TIER_LONG && long16(t)) {
                return w < 8;
            }
            if t.rem_euclid(16) == 0 { w < 16 && (w < 8 || e - w != 2) } else { w < 8 && e - (w + 8) == 2 }
        };
        for w in 0..16 {
            for e in 10..=ECAP {
                if !ok(e, w) {
                    continue;
                }
                if (e - w).rem_euclid(2) != 0 {
                    continue;
                }
                let (u, v) = ((e - w) / 2, (e + w) / 2);
                let (l, f) = (t / 2 - u, t / 2 + v);
                if l >= 1 && f <= N as i32 && f >= l {
                    out.push((e, w, u, v));
                }
            }
        }
        out
    }
    /// A shot that has just reached the top with e >= 10 takes code 01 and w = tn mod 8. ctl is clean.
    fn arrive11(&mut self, tn: i32, y: &[u32], ctl: u32) {
        let wv = self.wr;
        let (h0, h1) = (self.e[0], self.e[1]);
        let w = tn.rem_euclid(8);
        let yt2 = y[wv - 1];
        let mut l: Vec<Lit> = vec![(yt2, true)];
        l.extend(self.hc(2));
        for j in 1..9 {
            l.push((y[j], false));
        }
        let mut g = self.m(&l, ctl);
        g.push(gc(ctl, h0));
        g.push(gc(ctl, h1));
        for i in 0..3 {
            if (w >> i) & 1 == 1 {
                g.push(gc(ctl, y[4 + i]));
            }
        }
        if long16(tn) && tn.rem_euclid(16) >= 8 {
            g.push(gc(ctl, self.w4));
        }
        let mut l: Vec<Lit> = vec![(yt2, true)];
        l.extend(self.hc(1));
        l.push((y[1], false));
        for i in 0..3 {
            l.push((y[4 + i], (w >> i) & 1 == 1));
        }
        if long16(tn) {
            // a long waiter that arrived 8 slots earlier has the same 3 low wait bits: W4 tells them apart
            l.push((self.w4, tn.rem_euclid(16) >= 8));
        }
        g.extend(self.m(&l, ctl));
        self.b.t(&g);
    }
    /// Rows, marker and post of the waiting big shots (code 01) at a tier slot, after the slot's own low work.
    fn big_phase(&mut self, t: i32) {
        let wv = self.wr;
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let prs = self.big_pairs11(t);
        let es: BTreeSet<i32> = prs.iter().map(|p| p.0).collect();
        let kk = *es.iter().next_back().unwrap() + 1;
        let yt = y[wv - 1];
        let (d, ctl) = (x[0], x[0]);
        let (y0, y1) = (y[0], y[1]);
        let (w0, w1, w2) = (y[4], y[5], y[6]);
        let hb0: Vec<u32> = vec![y[2], y[3], y[7], y[8]];
        let cv9 = y[9];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        // L-C: at a slot 8 mod 16 of the long region only the short classes (marker in Y[9..TIER_LONG-2]) act; the long
        // waiters keep code 10. Every short actor there arrived at tn = 8..15 mod 16, so its W4 is 1: clear it.
        let band8 = TIER_LONG > 0 && long16(t) && t.rem_euclid(16) == 8;
        let full16 = TIER_LONG > 0 && long16(t) && t.rem_euclid(16) == 0;
        let g = if band8 {
            let mut g: GL = vec![];
            for j in 9..=(TIER_LONG.max(11) as usize - 2) {
                let mut l: Vec<Lit> = vec![(yt, true), (h0, true)];
                for i in 9..j { l.push((y[i], false)); }
                l.push((y[j], true));
                g.extend(self.m(&l, h1));
            }
            // the long cases moved here from the next slot 0 mod 16 (u would be 1): class e with w = e - 10
            for e in (TIER_LONG.max(11))..=17 {
                let mut l: Vec<Lit> = vec![(yt, true), (h0, true)];
                for i in 9..(e as usize - 1) { l.push((y[i], false)); }
                l.push((y[e as usize - 1], true));
                for i in 0..3 { l.push((y[4 + i], ((e - 10) >> i) & 1 == 1)); }
                g.extend(self.m(&l, h1));
            }
            g
        } else {
            self.m(&[(yt, true), (h0, true)], h1)
        };
        self.b.t(&g);
        let cl: Vec<Lit> = cat(&[(yt, true)], &self.hc(3));
        if band8 {
            let g = self.m(&cl, self.w4);
            self.b.t(&g);
        }
        let pgo = PAGE_G && mid_even(t);
        let case_st = |e: i32, w: i32| -> Vec<Lit> {
            let mut l = cl.clone();
            for i in 0..3 {
                l.push((y[4 + i], (w >> i) & 1 == 1));
            }
            for j in 9..(e as usize - 1) {
                l.push((y[j], false));
            }
            l.push((y[e as usize - 1], true));
            l
        };
        let case_end = |e: i32, w: i32| -> Vec<Lit> {
            let mut l = cl.clone();
            for i in 0..3 {
                l.push((x[wv - 2 - i], (w >> i) & 1 == 1));
            }
            l.push((x[wv - e as usize], true));
            for j in 10..(e as usize) {
                l.push((x[wv - j], false));
            }
            l
        };
        let mut g: GL = vec![];
        for &e in &es {
            let mut li = cl.clone();
            for j in 9..(e as usize - 1) {
                li.push((y[j], false));
            }
            li.push((y[e as usize - 1], true));
            let m = e >> 1;
            for i in 0..4 {
                if (m >> i) & 1 == 1 {
                    g.extend(self.m(&li, hb0[i]));
                }
            }
        }
        for &e in &es {
            let mut li = cl.clone();
            for i in 0..4 {
                li.push((hb0[i], ((e >> 1) >> i) & 1 == 1));
            }
            li.push((w0, e & 1 == 1));
            g.extend(self.m(&li, y[e as usize - 1]));
        }
        self.b.t(&g);
        let lits = |cubes: &Cubes, lanes: &[u32]| -> Vec<Vec<Lit>> { cubes.iter().map(|x_| x_.iter().map(|&(v, bt)| (lanes[v], bt == 1)).collect()).collect() };
        let exact = |k: i32, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &e in &es {
                let p_ = (e >> 1) | ((e & 1) << 4);
                if e >= k {
                    on |= 1u128 << p_;
                } else {
                    off |= 1u128 << p_;
                }
            }
            lits(&dtree(on, off, &[0, 1, 2, 3, 4], 1), lanes).into_iter().map(|x_| cat(&x_, &cl)).collect()
        };
        let hterm = |vals: &BTreeSet<i32>, others: &BTreeSet<i32>, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &x_ in vals {
                on |= 1u128 << (x_ % 16);
            }
            for &x_ in others {
                off |= 1u128 << (x_ % 16);
            }
            lits(&dtree(on, off, &[0, 1, 2, 3], 0), lanes)
        };
        // P1 big classes through the page: case flags on (hi, w) by decision trees (7 vars: hi bits 0..3, w bits 4..6)
        let dd = PAGE_D;
        let (va, vb, sc) = if pgo { (self.pg[..dd].to_vec(), self.pg[dd..2 * dd].to_vec(), self.pg[2 * dd..3 * dd].to_vec()) } else { (vec![], vec![], vec![]) };
        let pd = if pgo { dd as i32 } else { 0 };
        let cpt = |e: i32, w: i32| -> usize { ((e >> 1) | (w << 4)) as usize };
        // hsel: 0 -> the hosted lanes hold hi = e >> 1, 1 -> u (after cv_v), 2 -> v mod 16 (after cv_c)
        let cflagh = |me: &Machine, on_set: &[(i32, i32)], lanes: &[u32], hsel: u8| -> GL {
            let (mut on, mut off): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
            for &(e, w, u, v) in &prs {
                let h = match hsel { 0 => e >> 1, 1 => u, _ => v % 16 };
                let pt = (h | (w << 4)) as usize;
                if on_set.contains(&(e, w)) { on.push(pt); } else { off.push(pt); }
            }
            let mut g: GL = vec![];
            for cube in hw_cubes(&on, &off, lanes, me.w4) {
                g.extend(me.m(&cat(&cube, &cl), d));
            }
            g
        };
        let cflag = |me: &Machine, on_set: &[(i32, i32)], lanes: &[u32]| -> GL { cflagh(me, on_set, lanes, 0) };
        let lanes_v: Vec<u32> = vec![hb0[0], hb0[1], hb0[2], hb0[3], w0, w1, w2];
        if pgo {
            BIG_SITE.store(1, Ordering::Relaxed);
            let mut g: GL = vec![];
            for &(e, w, _u, v) in &prs {
                let fu = (t / 2 + v) as usize;
                let fl = cflag(self, &[(e, w)], &lanes_v);
                let mut lanes = va.clone();
                lanes.extend((0..e as usize).map(|i| x[wv - fu + dd + i]));
                let n = lanes.len();
                let ro = rotate_up(d, &lanes, n - e as usize);
                pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
        }
        let mut cv_v = dec_ctl(&hb0, &[(w1, true)], &self.dirty);
        cv_v.extend(dec_ctl(&hb0[1..], &[(w2, true)], &self.dirty));
        if full16 {
            cv_v.extend(dec_ctl(&hb0[2..], &[(self.w4, true)], &self.dirty));
        }
        for k in 0..kk {
            let act: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
            for &(_e, _w, u, _v) in &act {
                starts.entry(wv as i32 - (t / 2 - u) - k + pd).or_default().insert(u);
            }
            let alo = *starts.keys().next().unwrap();
            assert!(alo + k >= 10);
            let (ku, alo_u) = (k as usize, alo as usize);
            let tv: Vec<u32> = (alo_u..(wv - ku - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = (alo_u..(wv - ku - 1)).map(|a| y[a + ku]).collect();
            let t1 = x[wv - 1 - ku];
            let top = if k >= 1 { x[wv - ku] } else { NONE };
            let actv = exact(k, &[hb0[0], hb0[1], hb0[2], hb0[3], w0]);
            let allu: BTreeSet<i32> = act.iter().map(|p| p.2).collect();
            let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for (&a, us) in &starts {
                let rest: BTreeSet<i32> = allu.difference(us).cloned().collect();
                tg.insert((a - alo) as usize, hterm(us, &rest, &hb0));
            }
            let g = self.row_v(&tv, &sv, t1, top, d, cv9, y1, &tg, &actv, None, Some(&cv_v));
            if pgo {
                let mut up: GL = vec![];
                let mut dn: GL = vec![];
                for b in 0..dd {
                    let (sq, tq) = (vb[b], va[(b + 3 * dd - ku) % dd]);
                    up.extend_from_slice(&[gx(tq), gc(cv9, sq), gc(cv9, tq), gt(sq, tq, cv9)]);
                }
                for b in (0..dd).rev() {
                    let (sq, tq) = (vb[b], va[(b + 3 * dd - ku) % dd]);
                    dn.extend_from_slice(&[gt(sq, tq, cv9), gc(cv9, tq), gt(d, sq, tq), gc(cv9, sq), gx(tq)]);
                }
                pg_add(1, &up); pg_add(1, &dn);
                self.b.t(&up);
                self.b.t(&g);
                self.b.t(&dn);
            } else {
                self.b.t(&g);
            }
            let mut g: GL = vec![];
            if k >= 1 {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(x[wv - ku], true)]), d));
                }
            } else {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(d, true)]), y0));
                }
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(y0, true)]), d));
                }
            }
            self.b.t(&g);
            if pgo {
                // window slide for the cases with e > k, one swap per u (same ring wire)
                BIG_SITE.store(2, Ordering::Relaxed);
                let mut grp: BTreeMap<i32, Vec<(i32, i32)>> = BTreeMap::new();
                for &(e, w, u, _v) in prs.iter().filter(|p| p.0 >= k + 1) {
                    grp.entry(u).or_default().push((e, w));
                }
                let mut g: GL = cv_v.clone();
                pg_add(4, &cv_v); pg_add(4, &cv_v);
                if SLIDE_LAD {
                    let mut gr: Vec<(i32, Vec<Vec<Lit>>, GL)> = vec![];
                    for (u, cs) in &grp {
                        let on: Vec<usize> = cs.iter().map(|&(_e, w)| (w << 4) as usize).collect();
                        let off: Vec<usize> = prs.iter().filter(|p| p.2 == *u && p.0 < k + 1).map(|p| (p.1 << 4) as usize).collect();
                        let ex = if off.is_empty() { vec![vec![]] } else { hw_cubes(&on, &off, &lanes_v, self.w4) };
                        let mut sw: GL = vec![];
                        cswap(d, va[(3 * dd - 1 - ku) % dd], x[wv - (t / 2 - u) as usize + dd - ku - 1], &mut sw);
                        pg_add(3, &sw);
                        gr.push((*u, ex, sw));
                    }
                    g.extend(self.demux(&cl, &hb0, &mut gr, d, Some(self.pg[4 * dd])));
                    grp.clear();
                }
                for (u, cs) in grp {
                    let fl = cflagh(self, &cs, &lanes_v, 1);
                    let mut sw: GL = vec![];
                    cswap(d, va[(3 * dd - 1 - ku) % dd], x[wv - (t / 2 - u) as usize + dd - ku - 1], &mut sw);
                    pg_add(3, &sw); pg_add(4, &fl); pg_add(4, &fl);
                    g.extend_from_slice(&fl);
                    g.extend(sw);
                    g.extend_from_slice(&fl);
                }
                g.extend(rev(&cv_v));
                self.b.t(&g);
            }
        }
        // P1: window out + digit remap (weights 0..9 of class e sit on X[wv-e..wv-e+9] -> Q = X[wv-10..wv-1]), sandwich,
        // remap back, role swap, cofactor window out (inverse)
        let mut sw_post: GL = vec![];
        BIG_SITE.store(3, Ordering::Relaxed);
        if pgo {
            let es_l: Vec<i32> = es.iter().cloned().collect();
            let cls_cases = |e: i32| -> Vec<(i32, i32)> { prs.iter().filter(|p| p.0 == e).map(|p| (p.0, p.1)).collect() };
            let mut g: GL = vec![];
            let mut rms: Vec<GL> = vec![];
            for &e in &es_l {
                let fl = cflag(self, &cls_cases(e), &lanes_v);
                let ro = rotate_up(d, &va, e as usize % dd);
                // class e >= D: weights 0..D-1 of its digits (X[wv-e+j]) -> Q = X[wv-D..wv-1]; class e < D (D > 10): the
                // D top lanes rotate up by e (weight j -> Q[j]); Q[e..D) then hold non-digits: weight e is row 0's digit
                // on y0, weights above it are 0 (both by the class gating of the sandwich)
                let eu = e as usize;
                let rm = if eu >= dd {
                    let lanes: Vec<u32> = (0..eu).map(|i| x[wv - eu + i]).collect();
                    if eu > dd { rotate_up(d, &lanes, eu - dd) } else { vec![] }
                } else {
                    let lanes: Vec<u32> = (0..dd).map(|i| x[wv - dd + i]).collect();
                    rotate_up(d, &lanes, eu)
                };
                pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl); pg_add(5, &rm); pg_add(5, &rm);
                g.extend_from_slice(&fl);
                g.extend(ro);
                g.extend_from_slice(&rm);
                g.extend_from_slice(&fl);
                rms.push(rm);
            }
            self.b.t(&g);
            let q: Vec<u32> = (0..dd).map(|j| x[wv - dd + j]).collect();
            let (pre, post) = if es_l.iter().all(|&e| e as usize >= dd) {
                self.sandwich(&q, d, &[cl.clone()])
            } else {
                // cubes over the hosted (hi, w) lanes of the acting classes that satisfy p (given cl)
                let cubes = |p: &dyn Fn(i32) -> bool| -> Vec<Vec<Lit>> {
                    let (mut on, mut off): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
                    for &(e, w, _u, _v) in &prs {
                        let pt = ((e >> 1) | (w << 4)) as usize;
                        if p(e) { on.push(pt); } else { off.push(pt); }
                    }
                    if on.is_empty() { return vec![]; }
                    if off.is_empty() { return vec![vec![]]; }
                    hw_cubes(&on, &off, &lanes_v, self.w4)
                };
                let withcl = |v: Vec<Vec<Lit>>| -> Vec<Vec<Lit>> { v.into_iter().map(|c| cat(&c, &cl)).collect() };
                // weight e of class e is row 0's digit, on y0 (not an implicit 1: q of class e can be below 2^e)
                let ony0 = |v: Vec<Vec<Lit>>| -> Vec<Vec<Lit>> { v.into_iter().map(|c| cat(&c, &[(y0, true)])).collect() };
                self.sandwich_x(&q, d, &[cl.clone()], &|j| withcl(cubes(&|e| e as usize > j)), &|j| cubes(&|e| e as usize > j),
                    &|j| ony0(withcl(cubes(&|e| e as usize == j))), &|j| ony0(cubes(&|e| e as usize == j)))
            };
            let fz = self.pg[4 * dd];
            let mut rs: GL = vec![];
            for j in 0..dd {
                cswap(fz, vb[j], sc[j], &mut rs);
            }
            pg_add(5, &pre); pg_add(5, &post); pg_add(5, &rs); pg_add(5, &rs);
            self.b.t(&pre);
            self.b.t(&rs);
            BIG_SITE.store(4, Ordering::Relaxed);
            let mut g: GL = vec![];
            for (ie, &e) in es_l.iter().enumerate() {
                let fl = cflag(self, &cls_cases(e), &lanes_v);
                let ro = rotate_up(d, &vb, (dd - e as usize % dd) % dd);
                pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(rev(&rms[ie]));
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
            sw_post = rs;
            sw_post.extend(post);
        }
        let mv = |me: &Machine, src: u32, dst: u32| -> GL {
            let mut g = me.m(&cat(&cl, &[(src, true)]), dst);
            g.extend(me.m(&cat(&cl, &[(dst, true)]), src));
            g
        };
        let mut hb = hb0.clone();
        let (mut a0, mut a1, mut a2) = (w0, w1, w2);
        for k in (0..kk).rev() {
            let act: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let ku = k as usize;
            if k == 9 {
                let g = mv(self, hb[3], x[wv - 10]);
                self.b.t(&g);
                hb[3] = x[wv - 10];
            }
            if k == 8 {
                let g = mv(self, hb[2], x[wv - 9]);
                self.b.t(&g);
                hb[2] = x[wv - 9];
            }
            if k == 7 {
                let g = mv(self, a2, x[wv - 8]);
                self.b.t(&g);
                a2 = x[wv - 8];
            }
            if k == 6 {
                let g = mv(self, a1, x[wv - 7]);
                self.b.t(&g);
                a1 = x[wv - 7];
            }
            if k == 5 {
                let g = mv(self, a0, x[wv - 6]);
                self.b.t(&g);
                a0 = x[wv - 6];
            }
            if k == 4 {
                let g = mv(self, hb[1], x[wv - 5]);
                self.b.t(&g);
                hb[1] = x[wv - 5];
            }
            if k == 3 {
                let g = mv(self, hb[0], x[wv - 4]);
                self.b.t(&g);
                hb[0] = x[wv - 4];
            }
            let mut cv_c = inc_ctl(&hb, &[(a0, true)], &self.dirty);
            cv_c.extend(inc_ctl(&hb, &[(a1, true)], &self.dirty));
            cv_c.extend(inc_ctl(&hb[1..], &[(a2, true)], &self.dirty));
            if full16 {
                cv_c.extend(inc_ctl(&hb[2..], &[(self.w4, true)], &self.dirty));
            }
            let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
            for &(_e, _w, _u, v) in &act {
                starts.entry(W as i32 - (t / 2 + v) - 1 + k - pd).or_default().insert(v);
            }
            let ahi = *starts.keys().next_back().unwrap();
            let wires: Vec<usize> = (ku..=(ahi as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let cc = if k >= 2 {
                x[wv - ku]
            } else if k == 1 {
                x[wv - 2]
            } else {
                x[wv - 1]
            };
            let mask = if k >= 3 { y1 } else { x[wv - 3] };
            let actv = exact(k, &[hb[0], hb[1], hb[2], hb[3], a0]);
            let allv: BTreeSet<i32> = act.iter().map(|p| p.3).collect();
            let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for (&a, vs) in &starts {
                let rest: BTreeSet<i32> = allv.difference(vs).cloned().collect();
                tg.insert((ahi - a) as usize, hterm(vs, &rest, &hb));
            }
            let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, mask, &tg, &actv, None, Some(&cv_c));
            let mut hh: GL = vec![];
            if k >= 1 {
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(x[wv - ku], true)]), d));
                }
                hh.push(gc(d, x[wv - ku]));
                if k == 1 {
                    let xt = x[wv - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                    }
                }
                hh.push(gc(d, top));
            } else {
                let host = x[wv - 1];
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(host, true)]), d));
                }
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(d, true)]), host));
                }
            }
            self.b.t(&hh);
            if pgo {
                let mut gp: GL = vec![];
                for b in 0..dd {
                    let (sq, tq) = (sc[b], vb[(b + 3 * dd - ku) % dd]);
                    gp.extend_from_slice(&[gx(tq), gc(cc, sq), gc(cc, tq), gt(sq, tq, cc)]);
                }
                pg_add(1, &gp);
                gp.extend_from_slice(&g);
                let mut dn: GL = vec![];
                for b in (0..dd).rev() {
                    let (sq, tq) = (sc[b], vb[(b + 3 * dd - ku) % dd]);
                    dn.extend_from_slice(&[gt(sq, tq, cc), gc(cc, tq), gt(d, sq, tq), gc(cc, sq), gx(tq)]);
                }
                pg_add(1, &dn);
                gp.extend(dn);
                self.b.t(&rev(&gp));
                if k >= 1 {
                    // inverse of the cofactor window's slide after V-style row k - 1 (cases e >= k, one swap per f)
                    BIG_SITE.store(5, Ordering::Relaxed);
                    let lanes_c: Vec<u32> = vec![hb[0], hb[1], hb[2], hb[3], a0, a1, a2];
                    let mut grp: BTreeMap<i32, Vec<(i32, i32)>> = BTreeMap::new();
                    for &(e, w, _u, v) in prs.iter().filter(|p| p.0 >= k) {
                        grp.entry(t / 2 + v).or_default().push((e, w));
                    }
                    let mut g: GL = cv_c.clone();
                    pg_add(4, &cv_c); pg_add(4, &cv_c);
                    if SLIDE_LAD {
                        let mut gr: Vec<(i32, Vec<Vec<Lit>>, GL)> = vec![];
                        for (f, cs) in &grp {
                            let v = *f - t / 2;
                            let on: Vec<usize> = cs.iter().map(|&(_e, w)| (w << 4) as usize).collect();
                            let off: Vec<usize> = prs.iter().filter(|p| p.3 == v && p.0 < k).map(|p| (p.1 << 4) as usize).collect();
                            let ex = if off.is_empty() { vec![vec![]] } else { hw_cubes(&on, &off, &lanes_c, self.w4) };
                            let mut sw: GL = vec![];
                            cswap(d, vb[(3 * dd - ku) % dd], y[W - *f as usize - dd + ku - 1], &mut sw);
                            pg_add(3, &sw);
                            gr.push((v % 16, ex, sw));
                        }
                        g.extend(self.demux(&cl, &hb, &mut gr, d, None));
                        grp.clear();
                    }
                    for (f, cs) in grp {
                        let fl = cflagh(self, &cs, &lanes_c, 2);
                        let mut sw: GL = vec![];
                        cswap(d, vb[(3 * dd - ku) % dd], y[W - f as usize - dd + ku - 1], &mut sw);
                        pg_add(3, &sw); pg_add(4, &fl); pg_add(4, &fl);
                        g.extend_from_slice(&fl);
                        g.extend(sw);
                        g.extend_from_slice(&fl);
                    }
                    g.extend(rev(&cv_c));
                    self.b.t(&g);
                }
            } else {
                self.b.t(&rev(&g));
            }
        }
        if pgo {
            // inverse of the cofactor window-in, then the sandwich's post
            BIG_SITE.store(6, Ordering::Relaxed);
            let lanes_c: Vec<u32> = vec![hb[0], hb[1], hb[2], hb[3], a0, a1, a2];
            let mut g: GL = vec![];
            for &(e, w, u, _v) in &prs {
                let lu = (t / 2 - u) as usize;
                let fl = cflag(self, &[(e, w)], &lanes_c);
                let mut lanes = vb.clone();
                lanes.extend((0..e as usize).map(|i| y[W - lu - 1 - dd - i]));
                let ro = rotate_up(d, &lanes, e as usize);
                pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
            self.b.t(&sw_post);
        }
        BIG_SITE.store(0, Ordering::Relaxed);
        // hi -> marker on X[wv-e], largest e first
        let mut g: GL = vec![];
        for &e in es.iter().rev() {
            let m = e >> 1;
            let mk = x[wv - e as usize];
            let mut li = cl.clone();
            for i in 0..4 {
                li.push((hb[i], (m >> i) & 1 == 1));
            }
            li.push((a0, e & 1 == 1));
            g.extend(self.m(&li, ctl));
            for i in 0..4 {
                if (m >> i) & 1 == 1 {
                    g.push(gc(ctl, hb[i]));
                }
            }
            g.push(gc(ctl, mk));
            let mut li = cl.clone();
            for i in 0..4 {
                if hb[i] != mk {
                    li.push((hb[i], false));
                }
            }
            li.push((mk, true));
            g.extend(self.m(&li, ctl));
        }
        self.b.t(&g);
        let g = mv(self, a0, x[wv - 2]);
        self.b.t(&g);
        let g = mv(self, a1, x[wv - 3]);
        self.b.t(&g);
        let g = mv(self, a2, x[wv - 4]);
        self.b.t(&g);
        // its own post
        let g = self.m(&cat(&cl, &[(y[0], false)]), ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, wv - 1);
        self.b.t(&g);
        let g = self.m(&cl, ctl);
        self.b.t(&g);
        let mut g = vec![];
        for w in 1..wv {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        if pgo {
            let g = self.post_page(ctl);
            pg_add(7, &g);
            self.b.t(&g);
        }
        let xt = x[wv - 1];
        self.b.t(&[gc(ctl, y[wv - 1])]);
        let g = self.m(&cl, ctl);
        self.b.t(&g);
        let fl = y[wv - 1];
        let aa: Vec<Lit> = cat(&[(fl, true)], &self.hc(3));
        for &(idx, rot) in &[(wv - 4, 4usize), (wv - 3, 2), (wv - 2, 1)] {
            let mut g = self.m(&cat(&aa, &[(y[idx], true)]), ctl);
            g.extend(self.m(&cat(&aa, &[(ctl, true)]), y[idx]));
            self.b.t(&g);
            let g = rotate_up(ctl, &y[0..=idx], rot);
            self.b.t(&g);
            let mut g: GL = vec![];
            if rot == 4 {
                g.extend(self.m(&cat(&aa, &[(y[0], false)]), ctl));
            } else if rot == 2 {
                g.extend(self.m(&cat(&aa, &[(y[0], false), (y[2], true)]), ctl));
                g.extend(self.m(&cat(&aa, &[(y[0], false), (y[2], false), (y[4], false)]), ctl));
            } else {
                for &p_ in &[1usize, 3, 5, 7] {
                    let mut l = aa.clone();
                    for i in 0..p_ {
                        l.push((y[i], false));
                    }
                    l.push((y[p_], true));
                    g.extend(self.m(&l, ctl));
                }
            }
            self.b.t(&g);
        }
        // L-C: the 4th wait bit: rotate by 8 under W4 (last: the shots rotated by w & 7 have their first one at y[w & 7]),
        // W4 moved into ctl and back out by the 8 zeros a rotated shot has at the bottom
        if full16 && prs.iter().any(|p_| p_.1 >= 8) {
            let mut g = self.m(&cat(&aa, &[(self.w4, true)]), ctl);
            g.extend(self.m(&cat(&aa, &[(ctl, true)]), self.w4));
            self.b.t(&g);
            let g = rotate_up(ctl, &y[0..=wv - 2], 8);
            self.b.t(&g);
            let mut l = aa.clone();
            for i in 0..8 { l.push((y[i], false)); }
            let g = self.m(&l, ctl);
            self.b.t(&g);
        }
        // u=2, g=1 ends with E'=-1: no marker, code 01
        // L-C: at a slot 8 mod 16 the long waiters (code 10, yt = 1) are still here and are not acting; they all have W4 = 1
        // there and the actors W4 = 0 (cleared above), so the terms below that are not gated by code 11 also read W4 = 0
        let nw4: Vec<Lit> = if band8 { vec![(self.w4, false)] } else { vec![] };
        let fc1 = cat(&cat(&[(fl, true), (xt, false)], &self.hc(1)), &nw4);
        let mut g = self.m(&cat(&aa, &[(xt, false), (y[wv - 4], true)]), ctl);
        g.push(gc(ctl, h1));
        g.extend(self.m(&fc1, ctl));
        self.b.t(&g);
        let g = self.m(&fc1, y[wv - 4]);
        self.b.t(&g);
        let ab: Vec<Lit> = cat(&[(fl, true), (h0, true)], &nw4);
        let win: Vec<u32> = y[..wv - 1].to_vec();
        let g1 = self.m(&cat(&ab, &[(xt, false)]), ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        let g1 = self.m(&ab, ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        // erase the act flag
        let mut g: GL = vec![];
        for gg in 0..2usize {
            for w in 0..(if full16 { 16 } else { 8 }) {
                let sub: Vec<&(i32, i32, i32, i32)> = prs.iter().filter(|p| p.1 == w).collect();
                if sub.is_empty() {
                    continue;
                }
                let gq = 1 + gg + w as usize;
                let mut li: Vec<Lit> = vec![(xt, gg == 0)];
                for i in 0..gq {
                    li.push((y[i], false));
                }
                li.push((y[gq], true));
                if sub.iter().any(|p| !(gg == 1 && p.2 == 2)) {
                    let mut l = cat(&li, &self.hc(3));
                    // an acted shot of class e has zeros from y[wv-2] down to y[wv-(e-1)] before its rotation by w: the
                    // top literals cover what is left above it (e_min = 10 for w < 8, as before; L-C long cases: their e_min)
                    let emin = if w >= 8 { sub.iter().map(|p| p.0).min().unwrap() as usize } else { 10 };
                    for j in (wv + gq + 1 - emin)..(wv - 1) {
                        l.push((y[j], false));
                    }
                    g.extend(self.m(&l, fl));
                }
                if sub.iter().any(|p| gg == 1 && p.2 == 2) {
                    g.extend(self.m(&cat(&cat(&li, &self.hc(1)), &nw4), fl));
                }
            }
        }
        self.b.t(&g);
    }
    fn pi10(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> (GL, GL) {
        let wv = self.wr;
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let mut g = vec![];
        // the top lane of this frame is a known zero (it holds the act bit): only its carry-out matters
        // narrowed rings (PAGE_N): for the tau shots the X and y' holes sit at native lanes [W-l-D, W-l+D) (bX = W - l),
        // at the carry-in end of all three chains. Drop them exactly (op-layout's DROP model, NARROW.md s3 L3 / s6): the
        // top chain starts at narrowed lane wv - l + D, the bottom chains (C lanes, native indices) end at W - l - D.
        let hs = if wv < W { PAGE_D } else { 0 };
        let idx = {
            let v: Vec<usize> = ((wv - l + hs)..(wv - 1)).collect();
            let k = v.len().saturating_sub(PIW - 1);
            v[k..].to_vec()
        };
        let mut fw = vec![];
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, x[wv - 1], f1));
        g.extend(rev(&fw));
        let idx = last((2..(wv - l + hs)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        let idx = last((2..(wv - l + hs)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, y[w]), gc(cc, x[w - 1]), gt(y[w], x[w - 1], cc)]);
        }
        let mut h = fw.clone();
        h.push(gt(cc, y[1], f3));
        h.extend(rev(&fw));
        (g, h)
    }
}

/// F on virtual lanes: 0..255 x, 256..511 borrowed passenger, 512.. the rest.
struct FCirc {
    gates: Vec<G>,
    next: u32,
    y0: u32,
    y1: u32,
    par: u32,
    xtop: u32,
    ar: Vec<u32>,
    last: GL,
}
fn f_circuit() -> FCirc {
    IN_F.store(true, Ordering::Relaxed);
    let mut b = B { free: vec![], next: 512, gates: Vec::with_capacity(48_000_000) };
    for _ in 0..ZB {
        b.alloc();
    }
    let xl: Vec<u32> = (0..256).collect();
    let pas: Vec<u32> = (256..512).collect();
    let y0 = b.alloc();
    let par = xl[N - 1];
    let y1 = b.alloc();
    let mut y = vec![y0, y1];
    y.extend_from_slice(&xl[..N - 1]);
    let x: Vec<u32> = (0..W).map(|_| b.alloc()).collect();
    let e: Vec<u32> = (0..EB).map(|_| b.alloc()).collect();
    let mut dirty = pas.clone();
    dirty.extend_from_slice(&x);
    dirty.extend_from_slice(&y);
    let mut mc = Machine { b, dirty, pas, x, y, e, par, pg: vec![], wr: W, freed: vec![], w4: NONE, cv_t2: vec![], cv_freed: vec![], cv_x16: vec![], cv_y16: vec![], cv_pg16: vec![] };
    mc.page_alloc();
    gl_loader::splice(gl_loader::At::FBegin, &mut mc.b);
    let g_start = mc.b.gates.len();
    let y_init = mc.y.clone();
    mc.init();
    let (mut y_tail, mut g_tail) = (vec![], 0usize);
    let mut asm_a = 0usize;
    let (mut tab765, mut g765): (Vec<u32>, usize) = (vec![], 0usize);
    for t in (3..=(2 * N as i32 - 1)).rev() {
        if CONV && t == CUT_T - 1 {
            mc.conv_back(CUT_T - 1);
        }
        if (TAIL765 > 0 || TAIL_SWAP765) && t == CUT_T - 1 {
            tab765 = mc.phys765(mc.b.next);
            g765 = mc.b.gates.len();
        }
        if t == gl_loader::TAIL_CUT {
            // the cut's format switch (PAGE_G: page_out at 63, PAGE_N: rings re-widened) belongs to the frame, not to
            // the tail region a Tail splice replaces: run it first, then take the tail's labels and gate index.
            gl_loader::splice(gl_loader::At::BeforeTick(t), &mut mc.b);
            let g_pre = mc.b.gates.len();
            if ASM_DUMP {
                let l = |v: &[u32]| v.iter().map(|q| q.to_string()).collect::<Vec<_>>().join(",");
                eprintln!("ASMDUMP 79 y[{}] {}", mc.y.len(), l(&mc.y));
                eprintln!("ASMDUMP 79 x[{}] {}", mc.x.len(), l(&mc.x));
                let mut used: Vec<u32> = mc.b.gates[asm_a..g_pre].iter().flat_map(|g| [g.0, g.1, g.2]).filter(|&q| q != NONE && q < MAC).collect();
                let nmac = mc.b.gates[asm_a..g_pre].iter().filter(|g| g.0 == MAC).count();
                used.sort(); used.dedup();
                eprintln!("ASMDUMP used between cuts: {} labels (gates {}, MAC macros {} not expanded here) {}", used.len(), g_pre - asm_a, nmac, l(&used));
                eprintln!("ASMDUMP b.next {}", mc.b.next);
            }
            mc.cut(t);
            y_tail = mc.y.clone();
            g_tail = if ASM_TAIL_UNPACK && gl_loader::has(gl_loader::At::Tail) { g_pre } else { mc.b.gates.len() };
            mc.slot(t);
            continue;
        }
        if t == gl_loader::START_CUT - 1 {
            // boundary 447: the native init + ticks 511..448 have run (their software state, e.g. the ring-Y relabels,
            // is kept); with a Start splice their gates are replaced by the module's (frame input -> boundary 447).
            let native = &mc.b.gates[g_start..];
            let ccx = native.iter().filter(|g| g.2 != NONE).count();
            eprintln!("gl_loader: native start region (init + ticks 511..{}): {} gates, {} CCX (pre-MAC)", gl_loader::START_CUT, native.len(), ccx);
            if gl_loader::SPLICE_START765 {
                assert!(ASM_START_PAGED && PAGE_G && PAGE_N && PAGE_DI == 16 && CUT_S == 432, "start765 needs the D16 / 432 paged frame");
                mc.b.gates.truncate(g_start);
                start765(&mut mc);
            } else if gl_loader::has(gl_loader::At::Start) {
                mc.b.gates.truncate(g_start);
                gl_loader::splice(gl_loader::At::Start, &mut mc.b);
                // the module writes ring Y's logical lane i on the INITIAL label y[i] (trace2048 is in logical order,
                // and the native slots relabel y one wire per slot): continue the frame on those labels.
                mc.y = y_init.clone();
            }
        }
        gl_loader::splice(gl_loader::At::BeforeTick(t), &mut mc.b);
        if ASM_DUMP && t == CUT_S - 1 {
            mc.cut(t);
            asm_a = mc.b.gates.len();
            let l = |v: &[u32]| v.iter().map(|q| q.to_string()).collect::<Vec<_>>().join(",");
            eprintln!("ASMDUMP 431 y[{}] {}", mc.y.len(), l(&mc.y));
            eprintln!("ASMDUMP 431 x[{}] {}", mc.x.len(), l(&mc.x));
            eprintln!("ASMDUMP 431 pg[{}] {}", mc.pg.len(), l(&mc.pg));
            eprintln!("ASMDUMP 431 e {} par {} w4 {} freed[{}] {}", l(&mc.e), mc.par, mc.w4, mc.freed.len(), l(&mc.freed));
            mc.slot(t);
            continue;
        }
        mc.tick(t);
    }
    {
        let native = &mc.b.gates[g_tail..];
        let ccx = native.iter().filter(|g| g.2 != NONE).count();
        eprintln!("gl_loader: native tail region (ticks {}..3): {} gates, {} CCX (pre-MAC)", gl_loader::TAIL_CUT, native.len(), ccx);
        if gl_loader::has(gl_loader::At::Tail) {
            // ring-Y lanes of the list follow the initial labels y_init (logical order); the frame holds y_tail at tick
            // TAIL_CUT: map y_init[i] -> y_tail[i], and continue (exit, FCirc fields) on y_tail.
            mc.b.gates.truncate(g_tail);
            let pos: HashMap<u32, usize> = y_init.iter().enumerate().map(|(i, &q)| (q, i)).collect();
            let yt = y_tail.clone();
            gl_loader::splice_mapped(gl_loader::At::Tail, &mut mc.b, &|q| pos.get(&q).map(|&i| yt[i]).unwrap_or(q));
            mc.y = y_tail.clone();
        }
    }
    let mut keep_last = true;
    if TAIL_SWAP765 {
        assert!(TAIL765 == 0 && gl_loader::SPLICE_START765 && !START765_SWAP, "TAIL_SWAP765: native tail after a re-pointed start765");
        let y773: Vec<usize> = [512usize, 513].into_iter().chain(0..255).collect();
        let tgt: Vec<u32> = y773.iter().map(|&p| tab765[p]).collect();
        assert_eq!(mc.y.len(), W);
        let xs: std::collections::HashSet<u32> = mc.x.iter().copied().collect();
        let src: std::collections::HashSet<u32> = mc.y.iter().copied().collect();
        let dst: std::collections::HashSet<u32> = tgt.iter().copied().collect();
        assert!(src.iter().chain(dst.iter()).all(|l| !xs.contains(l)) && !src.contains(&mc.par) && !dst.contains(&mc.par), "tail swap: ring X / par involved");
        let mut dest: HashMap<u32, u32> = mc.y.iter().copied().zip(tgt.iter().copied()).collect();
        let mut a: Vec<u32> = dst.iter().copied().filter(|l| !src.contains(l)).collect();
        let mut bz: Vec<u32> = src.iter().copied().filter(|l| !dst.contains(l)).collect();
        a.sort();
        bz.sort();
        for (s0, d0) in a.into_iter().zip(bz) { dest.insert(s0, d0); }
        let mut keys: Vec<u32> = dest.keys().copied().collect();
        keys.sort();
        let mut done = std::collections::HashSet::new();
        let mut g: GL = vec![];
        for &s0 in &keys {
            if done.contains(&s0) || dest[&s0] == s0 { done.insert(s0); continue; }
            let mut c = vec![s0];
            let mut q = dest[&s0];
            while q != s0 { c.push(q); q = dest[&q]; }
            for &l in &c { done.insert(l); }
            for &sj in &c[1..] { g.extend([G(s0, sj, NONE), G(sj, s0, NONE), G(s0, sj, NONE)]); }
        }
        eprintln!("tail swap765: ring Y moved onto the Y773 labels: {} CX", g.len());
        mc.b.t(&g);
        mc.y = tgt;
    }
    if TAIL765 > 0 {
        let inv: HashMap<u32, u32> = tab765.iter().enumerate().map(|(p, &q)| (q, p as u32)).collect();
        let lay = format!("{}.lay", if TAIL765 == 1 { TAIL765_DUMP } else { TAIL765_LIST });
        if TAIL765 == 1 {
            assert!(!MAC_ON, "TAIL765 = 1 dumps plain gates: macro pass off");
            let ph = |q: u32| -> u32 { if q == NONE { NONE } else { *inv.get(&q).expect("tail765 dump: lane outside the table") } };
            let reg: GL = mc.b.gates[g765..].iter().map(|g| G(ph(g.0), ph(g.1), ph(g.2))).collect();
            let top = reg.iter().flat_map(|g| [g.0, g.1, g.2]).filter(|&q| q != NONE).max().unwrap_or(0) + 1;
            std::fs::write(TAIL765_DUMP, gl_loader::encode(&reg, top)).expect("tail765 dump write");
            let ys: Vec<String> = mc.y.iter().map(|&q| ph(q).to_string()).collect();
            let xs: Vec<String> = mc.x.iter().map(|&q| ph(q).to_string()).collect();
            std::fs::write(&lay, format!("Y {}\nX {}\n", ys.join(" "), xs.join(" "))).expect("tail765 lay write");
            eprintln!("tail765: dumped {} gates, {} CCX, phys lanes {} -> {}", reg.len(), reg.iter().filter(|g| g.2 != NONE).count(), top, TAIL765_DUMP);
        } else {
            let t764 = TAIL765 == 3 && leftw_t764();
            let z: Vec<u8> = if t764 { TAIL765_T764_DATA.to_vec() } else if TAIL765 == 3 { TAIL765_DATA.to_vec() } else { std::fs::read(TAIL765_LIST).expect("tail765 list read") };
            if t764 { assert_eq!(gl_loader::sha3_hex(&z), TAIL765_T764_SHA3, "tail765: LEFTW_T764 list sha3"); }
            else if TAIL765 == 3 { assert_eq!(gl_loader::sha3_hex(&z), TAIL765_SHA3, "tail765: registered list sha3"); }
            eprintln!("tail765: list {} sha3 {}", TAIL765_LIST, gl_loader::sha3_hex(&z));
            let f = gl_loader::decode(&z);
            let rl = |p: u32| -> u32 { if p == NONE { NONE } else { tab765[p as usize] } };
            let native = mc.b.gates.len() - g765;
            mc.b.gates.truncate(g765);
            let g: GL = f.gates.iter().map(|g| G(rl(g.0), rl(g.1), rl(g.2))).collect();
            eprintln!("tail765: native region {} gates replaced by the list: {} gates, {} CCX, phys lanes {}", native, g.len(), f.n_ccx, f.n_lanes);
            mc.b.t(&g);
            let txt = if TAIL765 == 3 { TAIL765_LAY.to_string() } else { std::fs::read_to_string(&lay).expect("tail765 lay read") };
            // a 765 tail list leaves ring X zero (SHELL.md s3d): without an X line the X-ring constant clear (fc.last) is dropped
            keep_last = txt.lines().any(|l| l.starts_with("X "));
            for ln in txt.lines() {
                let mut it = ln.split_whitespace();
                let k = it.next().unwrap_or("");
                let v: Vec<u32> = it.map(|w| rl(w.parse().unwrap())).collect();
                if k == "Y" { mc.y = v; } else if k == "X" { mc.x = v; }
            }
        }
    }
    gl_loader::splice(gl_loader::At::FEnd, &mut mc.b);
    IN_F.store(false, Ordering::Relaxed);
    if PAGE || PAGE_V || PAGE_C || PAGE_G {
        let c: Vec<u64> = PG_CNT.iter().map(|a| a.load(Ordering::Relaxed)).collect();
        eprintln!("P1 page CCX per pass: gather(test) {} cells {} rotations {} swaps {} flags {} sandwich+remap {} unpage/repage(e=1 even) {} (e=1 odd) {} (big) {} post swap+format {}", c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[8], c[9], c[7]);
        eprintln!("P1 big-phase flags per pass: win-in {} V-slides {} V-win-out {} cw {} C-slides {} C-win-out {}", c[11], c[12], c[13], c[14], c[15], c[16]);
    }
    if MAC_ON { let g = std::mem::take(&mut mc.b.gates); mc.b.gates = mac_finish(g); }
    let mut last: GL = vec![gx(mc.x[W - 1])];
    for i in 0..N {
        if pbit(i) {
            last.push(gx(mc.x[W - 2 - i]));
        }
    }
    if !keep_last {
        last.clear();
    }
    // with start765 re-pointed, the sign ends on the re-pointed par (= y0's label), not on xl[255]
    let par = if gl_loader::SPLICE_START765 && !START765_SWAP { mc.par } else { par };
    let mut fc = FCirc {
        gates: mc.b.gates,
        next: mc.b.next,
        y0,
        y1,
        par,
        xtop: mc.y[W - 1],
        ar: (0..N).map(|i| mc.y[W - 2 - i]).collect(),
        last,
    };
    if ASM765_COMPACT {
        let mut used = vec![false; fc.next as usize];
        for g in fc.gates.iter().chain(fc.last.iter()) {
            for q in [g.0, g.1, g.2] { if q != NONE { used[q as usize] = true; } }
        }
        for q in [fc.y0, fc.y1, fc.par, fc.xtop].into_iter().chain(fc.ar.iter().copied()) { used[q as usize] = true; }
        let mut rn = vec![NONE; fc.next as usize];
        for q in 0..512 { rn[q] = q as u32; }
        let mut nx = 512u32;
        for q in 512..fc.next as usize { if used[q] { rn[q] = nx; nx += 1; } }
        let r = |q: u32| if q == NONE { NONE } else { rn[q as usize] };
        for g in fc.gates.iter_mut().chain(fc.last.iter_mut()) { *g = G(r(g.0), r(g.1), r(g.2)); }
        fc.y0 = r(fc.y0);
        fc.y1 = r(fc.y1);
        fc.par = r(fc.par);
        fc.xtop = r(fc.xtop);
        for q in fc.ar.iter_mut() { *q = r(*q); }
        eprintln!("asm765 compaction: labels >= 512 used {} of {} -> fc.next {} (width {})", nx - 512, fc.next - 512, nx, nx);
        fc.next = nx;
        // leftW: with S and T both off the evicted label the compaction itself lands on 764; LEFTW_EXPECT764=1 asserts it
        if std::env::var("LEFTW_EXPECT764").map(|v| v.trim() == "1").unwrap_or(false) { assert_eq!(nx, 764, "LEFTW_EXPECT764: walk labels {} (want 764: S and T must both avoid the evicted label)", nx); }
    }
    fc
}

/// op-p5b (SPLICE765.md): replay a start list written on MAP765_v2 PHYSICAL lanes (x0 on WALK508 -> the paged D16 frame at label 1431)
/// in place of the native start region, then re-point the frame's software labels at the list's output layout. Table phys -> label:
/// the lanes holding F's input keep their input labels (x0 bit i on WALK508[i] -> label i, PAS -> pas), ZB (763) -> ZB_LANE, every
/// other (clean) lane -> a frame label that is clean at F's input (its own role label where that is free). After the list the ring /
/// page / code / parity roles are read off the table; the ring tops (freed by page_in's narrowing) and T2 get labels outside the
/// table (clean, unused by the list). page_in(431) then emits no gates (ASM_START_PAGED) but narrows the rings as usual.
fn start765(mc: &mut Machine) {
    const NP: usize = 765;
    let walk: Vec<u32> = (0..255).chain(512..765).collect();
    let yh: Vec<u32> = (0..225).collect();
    let va: Vec<u32> = (225..241).collect();
    let vb: Vec<u32> = (241..255).chain([512, 513]).collect();
    let xh: Vec<u32> = (514..739).collect();
    let sc: Vec<u32> = (739..755).collect();
    let (h, w4s, zbp, fp, parp) = ([755u32, 756], 757u32..763, 763u32, 764u32, 255u32);
    assert_eq!(mc.x.len(), W);
    assert_eq!(mc.y.len(), W);
    assert_eq!(mc.e.len(), 2);
    assert_eq!(mc.pg.len(), 4 * PAGE_DI + 2);
    assert_eq!(mc.pg[4 * PAGE_DI + 1], ZB_LANE);
    let mut t = vec![NONE; NP];
    let mut used = vec![false; mc.b.next as usize];
    let mut set = |t: &mut Vec<u32>, used: &mut Vec<bool>, p: u32, l: u32| {
        assert!(t[p as usize] == NONE && !used[l as usize], "start765 table: phys {p} label {l}");
        t[p as usize] = l;
        used[l as usize] = true;
    };
    for i in 0..256 { set(&mut t, &mut used, walk[i], i as u32); }
    for k in 0..256 { set(&mut t, &mut used, 256 + k as u32, mc.pas[k]); }
    set(&mut t, &mut used, zbp, ZB_LANE);
    if !START765_SWAP {
        // F's end data must sit on labels 0..511 + y0, y1 (the emitters free every other label >= 512 after F): ring Y ends on
        // phys Y773 = [512, 513, 0..254] -> labels {255, t[513], 0..254 via the table at 79}, PAR on t[255]: so t[255], t[513] = y0, y1.
        set(&mut t, &mut used, parp, Y0_LABEL);
        set(&mut t, &mut used, 513, Y1_LABEL);
    }
    // preferred role labels for the clean lanes (labels >= 513 are clean at F's input)
    let mut pref: Vec<(u32, u32)> = vec![];
    for i in 0..225 { pref.push((xh[i], mc.x[i])); }
    for j in 0..PAGE_DI { pref.push((sc[j], mc.pg[2 * PAGE_DI + j])); }
    pref.push((vb[15], mc.pg[PAGE_DI + 15]));
    pref.push((h[0], mc.e[0]));
    pref.push((h[1], mc.e[1]));
    pref.push((fp, mc.pg[4 * PAGE_DI]));
    for (k, p) in w4s.clone().enumerate() { pref.push((p, mc.x[WHI + k])); }
    for (p, l) in pref {
        if l >= 513 && (l as usize) < used.len() && !used[l as usize] && t[p as usize] == NONE { set(&mut t, &mut used, p, l); }
    }
    let mut pool = (513..mc.b.next).filter(|&l| !used[l as usize]).collect::<Vec<u32>>().into_iter();
    for p in 0..NP as u32 {
        if t[p as usize] == NONE {
            let l = pool.next().expect("start765: label pool exhausted");
            set(&mut t, &mut used, p, l);
        }
    }
    let _ = parp;
    if ZB_EXTRA > 0 {
        assert!(ZB_EXTRA == 1, "ZB_EXTRA: one extra clean lane");
        // between the cuts the converter's lifted bits take the first PAGE_DI - PAGE_D spares (freed[1..]); the next one stays idle
        assert!(PAGE_DI - PAGE_D <= 4, "ZB_EXTRA needs an idle spare: PAGE_D >= PAGE_DI - 4");
        let mut zx = ZX.lock().unwrap();
        zx.clear();
        zx.push(t[758 + PAGE_DI - PAGE_D]);
        eprintln!("ZB_EXTRA {} labels {:?}", ZB_EXTRA, *zx);
    }
    gl_loader::splice_mapped(gl_loader::At::Start, &mut mc.b, &|q| {
        assert!((q as usize) < NP, "start765 list lane {q} >= 765");
        t[q as usize]
    });
    if START765_SWAP {
        // native role labels at 1431 (cut(431) keeps the prefix [0, WHI) of each ring and frees the tops; W4 = freed[0] = x[WHI])
        let mut n = vec![NONE; NP];
        for i in 0..225 { n[yh[i] as usize] = mc.y[i]; n[xh[i] as usize] = mc.x[i]; }
        for j in 0..PAGE_DI { n[va[j] as usize] = mc.pg[j]; n[vb[j] as usize] = mc.pg[PAGE_DI + j]; n[sc[j] as usize] = mc.pg[2 * PAGE_DI + j]; }
        n[h[0] as usize] = mc.e[0];
        n[h[1] as usize] = mc.e[1];
        n[parp as usize] = mc.par;
        for k in 0..256 { n[256 + k] = mc.pas[k]; }
        for (k, p) in w4s.clone().enumerate() { n[p as usize] = mc.x[WHI + k]; }
        n[zbp as usize] = mc.pg[4 * PAGE_DI + 1];
        n[fp as usize] = mc.pg[4 * PAGE_DI];
        assert!(n.iter().all(|&l| l != NONE));
        let mut seen = std::collections::HashSet::new();
        assert!(n.iter().all(|&l| seen.insert(l)), "start765: native role labels not distinct");
        // permutation: data on t[p] goes to n[p]; labels in n not in t (zero) fill the labels in t not in n
        let ti: std::collections::HashSet<u32> = t.iter().copied().collect();
        let ni: std::collections::HashSet<u32> = n.iter().copied().collect();
        let mut dest: HashMap<u32, u32> = (0..NP).map(|p| (t[p], n[p])).collect();
        let mut a: Vec<u32> = ni.iter().copied().filter(|l| !ti.contains(l)).collect();
        let mut bz: Vec<u32> = ti.iter().copied().filter(|l| !ni.contains(l)).collect();
        a.sort();
        bz.sort();
        assert_eq!(a.len(), bz.len());
        for (s0, d0) in a.into_iter().zip(bz) { dest.insert(s0, d0); }
        let mut keys: Vec<u32> = dest.keys().copied().collect();
        keys.sort();
        let mut done = std::collections::HashSet::new();
        let (mut nsw, mut ncyc) = (0usize, 0usize);
        let mut g: GL = vec![];
        for &s0 in &keys {
            if done.contains(&s0) || dest[&s0] == s0 { done.insert(s0); continue; }
            ncyc += 1;
            let mut c = vec![s0];
            let mut q = dest[&s0];
            while q != s0 { c.push(q); q = dest[&q]; }
            for &l in &c { done.insert(l); }
            for &sj in &c[1..] {
                g.extend([G(s0, sj, NONE), G(sj, s0, NONE), G(s0, sj, NONE)]);
                nsw += 1;
            }
        }
        mc.b.t(&g);
        eprintln!("start765 (swap mode): data moved onto the native labels at 1431: {} cycles, {} swaps, {} CX, 0 CCX", ncyc, nsw, g.len());
        return;
    }
    let mut extra = move |b: &mut B| -> u32 { pool.next().unwrap_or_else(|| b.alloc()) };
    let tm = |v: &[u32]| -> Vec<u32> { v.iter().map(|&p| t[p as usize]).collect() };
    let mut x = tm(&xh);
    x.extend(tm(&w4s.clone().collect::<Vec<u32>>()));
    while x.len() < W { x.push(extra(&mut mc.b)); }
    let mut y = tm(&yh);
    while y.len() < W { y.push(extra(&mut mc.b)); }
    let mut pg = tm(&va);
    pg.extend(tm(&vb));
    pg.extend(tm(&sc));
    for _ in 0..PAGE_DI { pg.push(extra(&mut mc.b)); }
    pg.push(t[fp as usize]);
    pg.push(t[zbp as usize]);
    mc.x = x;
    mc.y = y;
    mc.pg = pg;
    mc.e = tm(&h);
    mc.par = t[parp as usize];
    // stale software state of the dropped native start: its free list and dirty pool name labels the list now uses
    let live: std::collections::HashSet<u32> = t.iter().copied().chain(mc.x.iter().copied()).chain(mc.y.iter().copied()).chain(mc.pg.iter().copied()).collect();
    mc.b.free.retain(|l| !live.contains(l));
    let mut dirty = mc.pas.clone();
    dirty.extend_from_slice(&mc.x);
    dirty.extend_from_slice(&mc.y);
    mc.dirty = dirty;
    eprintln!("start765: table built (765 phys lanes), par label {}, W4 label {}, b.next {}", mc.par, mc.x[WHI], mc.b.next);
}

/// physical emitter
struct P {
    ops: Vec<Op>,
    free: Vec<u32>,
    next: u32,
    bits: u64,
}
const fn q(i: u32) -> QubitId {
    QubitId(i as u64)
}
impl P {
    fn alloc(&mut self) -> u32 {
        if let Some(a) = self.free.pop() {
            a
        } else {
            self.next += 1;
            self.next - 1
        }
    }
    fn allocn(&mut self, k: usize) -> Vec<u32> {
        (0..k).map(|_| self.alloc()).collect()
    }
    fn rel(&mut self, a: u32) {
        self.free.push(a);
        self.free.sort_by(|x, y| y.cmp(x));
    }
    #[inline]
    fn gate(&mut self, g: G) {
        let mut o = Op::empty();
        if g.2 != NONE {
            o.kind = OperationType::CCX;
            o.q_control1 = q(g.0);
            o.q_control2 = q(g.1);
            o.q_target = q(g.2);
        } else if g.1 != NONE {
            o.kind = OperationType::CX;
            o.q_control1 = q(g.0);
            o.q_target = q(g.1);
        } else {
            o.kind = OperationType::X;
            o.q_target = q(g.0);
        }
        self.ops.push(o);
    }
    fn g(&mut self, l: &[G]) {
        for &x in l {
            self.gate(x);
        }
    }
    fn xc(&mut self, a: u32, b: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::X;
        o.q_target = q(a);
        o.c_condition = BitId(b);
        self.ops.push(o);
    }
    fn zc(&mut self, a: u32, b: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::Z;
        o.q_target = q(a);
        o.c_condition = BitId(b);
        self.ops.push(o);
    }
    /// LEAN_SQ: CZ(a, b) under the classical bit (Gidney's AND uncompute correction).
    fn czc(&mut self, a: u32, b: u32, bit: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::CZ;
        o.q_control1 = q(a);
        o.q_target = q(b);
        o.c_condition = BitId(bit);
        self.ops.push(o);
    }
    fn hmr(&mut self, a: u32) -> u64 {
        let b = self.bits;
        self.bits += 1;
        let mut o = Op::empty();
        o.kind = OperationType::Hmr;
        o.q_target = q(a);
        o.c_target = BitId(b);
        self.ops.push(o);
        b
    }
}

fn add_gl(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(3 * t.len());
    for i in 0..t.len() {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
        g.push(gt(s[i], t[i], c));
    }
    g
}
fn add_back(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(4 * t.len());
    for i in (0..t.len()).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g
}

/// The shell. No spare lane for the doubling: it is a rotation, the top bit is already the LSB of its multiple of c0.
/// The carry lane doubles as the fold's clean lane. a has 255 bits, its top lane and N's top lane are free after F.
/// x is squared into in place and classical offsets load 128 bits at a time. The top CAPW multiplier bits can move into the
/// product's top lanes with a descending seed, an idea from the public frogdrop 765 note 153caee.
/// LEAN_SQ: Gidney halved adder (arXiv:1709.06648): tgt += add mod 2^w (w = tgt.len() = add.len()); the carries
/// c_1..c_(w-1) live on anc[0..w-1) (clean in, clean out) and are uncomputed by measurement (Hmr, then CZ under the
/// bit). With cout = Some(s) the carry-out c_w is computed onto s and kept. w-1 Toffoli (w with cout).
fn gid_add(p: &mut P, tgt: &[u32], add: &[u32], anc: &[u32], cout: Option<u32>) {
    let w = tgt.len();
    assert!(w >= 1 && add.len() == w);
    let kmax = if cout.is_some() { w } else { w - 1 };
    assert!(anc.len() + 1 >= kmax, "gid_add: {} ancillae for {} carries", anc.len(), kmax);
    for k in 0..kmax {
        let ck = if k == 0 { NONE } else { anc[k - 1] };
        let tc = if k == w - 1 { cout.unwrap() } else { anc[k] };
        if ck != NONE {
            p.g(&[gc(ck, add[k]), gc(ck, tgt[k])]);
        }
        p.g(&[gt(add[k], tgt[k], tc)]);
        if ck != NONE {
            p.g(&[gc(ck, tc)]);
        }
    }
    for k in (0..w).rev() {
        let ck = if k == 0 { NONE } else { anc[k - 1] };
        let processed = k < kmax;
        if processed && k < w - 1 {
            if ck != NONE {
                p.g(&[gc(ck, anc[k])]);
            }
            let m = p.hmr(anc[k]);
            p.czc(add[k], tgt[k], m);
        }
        if processed {
            if ck != NONE {
                p.g(&[gc(ck, add[k])]);
            }
            p.g(&[gc(add[k], tgt[k])]);
        } else {
            p.g(&[gc(add[k], tgt[k])]);
            if ck != NONE {
                p.g(&[gc(ck, tgt[k])]);
            }
        }
    }
}
/// LEAN_SQ: tgt -= add mod 2^w as not(not tgt + add).
fn gid_sub(p: &mut P, tgt: &[u32], add: &[u32], anc: &[u32]) {
    let x: GL = tgt.iter().map(|&q0| gx(q0)).collect();
    p.g(&x);
    gid_add(p, tgt, add, anc, None);
    p.g(&x);
}
/// LEAN_SQ: Haener's squarer, LSB first: z (2n or more wires, zero) += v^2. v^2 = -v + sum_i (2 v_i - 1) 2^(2i+1) (h_i + v_i),
/// h_i = v >> (i + 1). Step 0: z[0..n+1) -= v. Step i: sign-extend z[n+i] -> z[n+i+1]; window z[2i+1 .. n+i+2) -= u, u = h_i
/// padded to the window and inverted under v_i. Last: z[2n-1] ^= v_(n-1). AND ancillae: z above the window, then xa.
fn sq_fwd(p: &mut P, v: &[u32], z: &[u32], pad: [u32; 2], xa: [u32; 2]) {
    let n = v.len();
    let zb = z.len();
    assert!(zb >= 2 * n);
    {
        let w = n + 1;
        let mut add: Vec<u32> = v.to_vec();
        add.push(pad[0]);
        let mut anc: Vec<u32> = z[w..].to_vec();
        anc.extend_from_slice(&xa);
        gid_sub(p, &z[0..w], &add, &anc);
    }
    for i in 0..n - 1 {
        let (lo, top) = (2 * i + 1, n + i + 2);
        let w = top - lo;
        p.g(&[gc(z[n + i], z[n + i + 1])]);
        let mut add: Vec<u32> = v[i + 1..].to_vec();
        add.push(pad[0]);
        add.push(pad[1]);
        assert!(add.len() == w);
        let inv: GL = add.iter().map(|&q0| gc(v[i], q0)).collect();
        let mut anc: Vec<u32> = z[top..].to_vec();
        anc.extend_from_slice(&xa);
        p.g(&inv);
        gid_sub(p, &z[lo..top], &add, &anc);
        p.g(&inv);
    }
    p.g(&[gc(v[n - 1], z[2 * n - 1])]);
}
/// LEAN_SQ: the exact reverse of sq_fwd (z -= v^2 back to zero).
fn sq_rev(p: &mut P, v: &[u32], z: &[u32], pad: [u32; 2], xa: [u32; 2]) {
    let n = v.len();
    p.g(&[gc(v[n - 1], z[2 * n - 1])]);
    for i in (0..n - 1).rev() {
        let (lo, top) = (2 * i + 1, n + i + 2);
        let w = top - lo;
        let mut add: Vec<u32> = v[i + 1..].to_vec();
        add.push(pad[0]);
        add.push(pad[1]);
        assert!(add.len() == w);
        let inv: GL = add.iter().map(|&q0| gc(v[i], q0)).collect();
        let mut anc: Vec<u32> = z[top..].to_vec();
        anc.extend_from_slice(&xa);
        p.g(&inv);
        gid_add(p, &z[lo..top], &add, &anc, None);
        p.g(&inv);
        p.g(&[gc(z[n + i], z[n + i + 1])]);
    }
    {
        let w = n + 1;
        let mut add: Vec<u32> = v.to_vec();
        add.push(pad[0]);
        let mut anc: Vec<u32> = z[w..].to_vec();
        anc.extend_from_slice(&xa);
        gid_add(p, &z[0..w], &add, &anc, None);
    }
}
/// LEAN_SB: z[0..2n) += v * h by controlled window adds z[i..i+n+1) += v_i * h (h padded with one zero lane); 3 T per wire.
/// Partial sums stay below 2^(i+n+1), so no window overflows and the carry lane returns clean.
fn cross_fwd(p: &mut P, v: &[u32], h: &[u32], z: &[u32], pad: u32, c: u32) {
    let n = v.len();
    let mut u: Vec<u32> = h.to_vec();
    u.push(pad);
    for i in 0..n {
        let w = n + 1;
        let tgt = &z[i..i + w];
        let mut g = add_gl(tgt, &u, c);
        for j in (0..w).rev() {
            g.extend_from_slice(&[gt(u[j], tgt[j], c), gc(c, tgt[j]), gt(v[i], u[j], tgt[j]), gc(c, u[j])]);
        }
        p.g(&g);
    }
}
fn cross_rev(p: &mut P, v: &[u32], h: &[u32], z: &[u32], pad: u32, c: u32) {
    let n = v.len();
    let mut u: Vec<u32> = h.to_vec();
    u.push(pad);
    for i in (0..n).rev() {
        let w = n + 1;
        let tgt = &z[i..i + w];
        let mut g = add_gl(tgt, &u, c);
        for j in (0..w).rev() {
            g.extend_from_slice(&[gt(u[j], tgt[j], c), gc(c, tgt[j]), gt(v[i], u[j], tgt[j]), gc(c, u[j])]);
        }
        p.g(&rev(&g));
    }
}

struct S3 {
    dirty: Vec<u32>,
    zl: Vec<u32>,
}
impl S3 {
    fn m(&self, l: &[Lit], t: u32) -> GL {
        mcx(l, t, &self.dirty)
    }
    /// reg += f at its LSB, plus sign*f*2^pos for (pos,sign,z) in terms, z clean. One two-pass chain: a clean lane z in place of
    /// the borrowed bit takes f on one pass. f's wire reads f^d0 between the passes; the corrections are CNOTs.
    fn merged(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && !r.contains(&q0) && !terms.iter().any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait signed digits: `merged` whose extra terms (pos, sign, lane) add sign * (W - c) * 2^pos, W and c wires.
    /// Lane values across the two passes: positive (not W, c), negative (W, not c) (tools/chain_signed.py, exhaustive).
    fn merged_s(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], wt: u32, cc: u32, dterms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().chain(dterms.iter()).find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && q0 != wt && q0 != cc && !r.contains(&q0) && !terms.iter().chain(dterms.iter()).any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        for t in dterms.iter() {
            g.push(gc(wt, t.2));
            if t.1 > 0 {
                g.push(gx(t.2));
            }
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        for t in dterms.iter() {
            g.push(gc(wt, t.2));
            g.push(gc(cc, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        for t in dterms.iter() {
            g.push(gc(cc, t.2));
            if t.1 > 0 {
                g.push(gx(t.2));
            }
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait: acc += a with no control, carry-out on ov (zuiris's add_ctl with the control removed: 2 T per wire).
    fn add_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g: GL;
        if a.len() == 256 {
            g = add_gl(acc, a, c);
            g.push(gc(c, ov));
            for j in (0..256).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gc(a[j], acc[j]), gc(c, a[j])]);
            }
        } else {
            g = add_gl(&acc[..255], a, c);
            g.push(gt(c, acc[255], ov));
            g.push(gc(c, acc[255]));
            for j in (0..255).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gc(a[j], acc[j]), gc(c, a[j])]);
            }
        }
        g
    }
    /// ZFOR-wait: zuiris's clear_ov with the control removed.
    fn clear_ov_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        let mut h: GL = acc[k..].iter().map(|&q0| gx(q0)).collect();
        let mut g;
        if a.len() == 256 {
            h.extend(add_gl(&acc[k..], &a[k..], c));
            g = h.clone();
            g.push(gc(c, ov));
        } else {
            h.extend(add_gl(&acc[k..255], &a[k..], c));
            g = h.clone();
            g.push(gt(c, acc[255], ov));
        }
        g.extend(rev(&h));
        g
    }
    /// ZFOR-wait signed round: acc = acc + a (bit = 1) or acc - a (bit = 0), the subtraction as ~(~acc + a). The bit wire
    /// holds c = not bit inside the bracket; the next doubling's fold rides the ov chain as (K/2)(W255 - c).
    fn round3(&self, acc: &[u32], a: &[u32], bit: u32, c: u32, ov: u32, nxt: bool) -> GL {
        let mut g: GL = vec![gx(bit)];
        for &q0 in acc {
            g.push(gc(bit, q0));
        }
        g.extend(self.add_plain(acc, a, c, ov));
        if nxt {
            let z = &self.zl;
            g.extend(self.merged_s(&acc[0..RW], ov, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], acc[255], bit, &[(3, 1, z[4]), (5, -1, z[5]), (9, 1, z[6]), (31, 1, z[7])], c));
        } else {
            g.extend(self.lean(acc, ov, RW, c));
        }
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        for &q0 in acc {
            g.push(gc(bit, q0));
        }
        g.push(gx(bit));
        g
    }
    /// ZFOR-wait: acc += a, no control (one plain round).
    fn add_round(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g = self.add_plain(acc, a, c, ov);
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        g
    }
    /// ZFOR-wait: acc -= a (fixed subtraction round, no doubling term).
    fn sub_round(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g: GL = acc.iter().map(|&q0| gx(q0)).collect();
        g.extend(self.add_plain(acc, a, c, ov));
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        g.extend(acc.iter().map(|&q0| gx(q0)));
        g
    }
    /// ZFOR-wait: acc := acc / 2 mod p (inverse of zuiris's doubling), returns the new labeling.
    fn halve(&self, acc: &[u32], c: u32) -> (Vec<u32>, GL) {
        let mut prev: Vec<u32> = acc[1..].to_vec();
        prev.push(acc[0]);
        let (t2, h) = self.dbl(&prev, c);
        assert!(t2 == acc);
        (prev, rev(&h))
    }
    fn lean(&self, t: &[u32], f: u32, _window: usize, c2: u32) -> GL {
        let z = &self.zl;
        if ZL >= 4 {
            return self.merged(&t[0..RW], f, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], c2);
        }
        let mut g = inc_long(&t[0..CHW], f, &self.dirty, c2);
        g.extend(self.merged(&t[4..RW], f, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c2));
        g
    }
    fn dbl(&self, t: &[u32], c2: u32) -> (Vec<u32>, GL) {
        let mut t2 = vec![t[255]];
        t2.extend_from_slice(&t[..255]);
        let f = t2[0];
        let z = &self.zl;
        let g = self.merged(&t2[4..RW], f, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c2);
        (t2, g)
    }
    fn add_ctl(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let mut g: GL;
        if a.len() == 256 {
            g = add_gl(acc, a, c);
            g.push(gt(ctl, c, ov));
            for j in (0..256).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gt(ctl, a[j], acc[j]), gc(c, a[j])]);
            }
        } else {
            g = add_gl(&acc[..255], a, c);
            g.extend(self.m(&[(ctl, true), (c, true), (acc[255], true)], ov));
            g.push(gt(ctl, c, acc[255]));
            for j in (0..255).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gt(ctl, a[j], acc[j]), gc(c, a[j])]);
            }
        }
        g
    }
    /// ov = ctl & (T < a), read on the top CMPW wires. An equal window reads as T >= a, so T = a (the first add) is right.
    fn clear_ov(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        let mut h: GL = acc[k..].iter().map(|&q0| gx(q0)).collect();
        let mut g;
        if a.len() == 256 {
            h.extend(add_gl(&acc[k..], &a[k..], c));
            g = h.clone();
            g.push(gt(ctl, c, ov));
        } else {
            h.extend(add_gl(&acc[k..255], &a[k..], c));
            g = h.clone();
            g.extend(self.m(&[(ctl, true), (c, true), (acc[255], true)], ov));
        }
        g.extend(rev(&h));
        g
    }
    fn round(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let mut g = self.add_ctl(acc, a, ctl, c, ov);
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov(acc, a, ctl, c, ov));
        g
    }
    /// acc = a * sum bits[i] 2^i mod p; the top w bits move into acc's top lanes. Returns acc, the fresh lanes, the gates.
    fn product(&self, p: &mut P, a: &[u32], bits: &[u32], c: u32, ov: u32, w: usize) -> (Vec<u32>, Vec<u32>, GL) {
        let nb = bits.len();
        let j_: Vec<u32> = bits[nb - w..].to_vec();
        let low = p.allocn(256 - w);
        let mut acc = low.clone();
        acc.extend_from_slice(&j_);
        let mut g: GL = vec![];
        let mut al = NONE;
        if w > 0 {
            al = p.alloc();
            let zl: Vec<Lit> = (0..ZW).map(|r| (acc[r], false)).collect();
            for k in (1..(1usize << w)).rev() {
                let mut l: Vec<Lit> = vec![(al, false)];
                for i in 0..w {
                    l.push((j_[i], (k >> i) & 1 == 1));
                }
                g.extend(self.m(&l, c));
                for i in 0..w {
                    if (k >> i) & 1 == 1 {
                        g.push(gc(c, j_[i]));
                    }
                }
                g.push(gc(c, al));
                let mut l2: Vec<Lit> = vec![(al, true)];
                l2.extend_from_slice(&zl);
                g.extend(self.m(&l2, c));
                g.extend(self.round(&acc, a, al, c, ov));
            }
            g.push(gx(al));
            g.extend(self.m(&zl, al));
        }
        // ZFOR-wait signed digits. With CAPW = w > 0, zuiris's seed loop above leaves acc = S a (S = the top w bits).
        // Then acc := 2 acc + a (one plain round), m = nb - w signed rounds on the low bits give 2ab + a; subtract a, halve.
        if w == 0 {
            for j in 0..a.len() {
                g.push(gc(a[j], acc[j]));
            }
        } else {
            let (t2, h) = self.dbl(&acc, c);
            acc = t2;
            g.extend(h);
            g.extend(self.add_round(&acc, a, c, ov));
        }
        let idx: Vec<usize> = (0..(nb - w)).rev().collect();
        for (j, &i) in idx.iter().enumerate() {
            if j == 0 && w == 0 && a.len() < 256 {
                // acc = a with a 255-bit a: top wire 0, so this doubling's fold is dead
                let mut t2 = vec![acc[255]];
                t2.extend_from_slice(&acc[..255]);
                acc = t2;
            } else {
                let (t2, h) = self.dbl(&acc, c);
                acc = t2;
                g.extend(h);
            }
            g.extend(self.round3(&acc, a, bits[i], c, ov, false));
        }
        g.extend(self.sub_round(&acc, a, c, ov));
        let (t2, h) = self.halve(&acc, c);
        acc = t2;
        g.extend(h);
        if w > 0 {
            p.rel(al);
        }
        (acc, low, g)
    }
    fn neg(&self, p: &mut P, t: &[u32], c2: u32) {
        let u = p.alloc();
        p.g(&[gx(u)]);
        let mut g: GL = t.iter().map(|&q0| gx(q0)).collect();
        for &b in &C0M1 {
            g.extend(rev(&inc_long(&t[b..], u, &self.dirty, c2)));
        }
        g.push(gx(u));
        p.g(&g);
        p.rel(u);
    }
    fn cneg_list(&self, t: &[u32], ctl: u32, neg_when: bool, c2: u32) -> GL {
        let pre: GL = if neg_when { vec![] } else { vec![gx(ctl)] };
        let mut g = pre.clone();
        for &q0 in t {
            g.push(gc(ctl, q0));
        }
        for &b in &C0M1 {
            g.extend(rev(&inc_long(&t[b..], ctl, &self.dirty, c2)));
        }
        g.extend_from_slice(&pre);
        g
    }
    /// t += classical s mod p (t -= s when sub), 128 lanes at a time.
    fn cl_add(&mut self, p: &mut P, t: &[u32], bits: u64, sub: bool) {
        const K: usize = 128;
        let l = p.allocn(K);
        let (k, c, o) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(ZL);
        let keep = self.dirty.clone();
        self.dirty.extend_from_slice(&l);
        let (lo, hi) = (&t[..K], &t[K..]);
        let flip = |r: &[u32]| -> GL { r.iter().map(|&q0| gx(q0)).collect() };
        enum It {
            Load(u64),
            Gs(GL),
        }
        let mut seq: Vec<It> = vec![];
        let a1 = {
            let mut g = add_gl(lo, &l, c);
            g.push(gc(c, k));
            g.extend(add_back(lo, &l, c));
            g
        };
        let a2 = {
            let mut g = add_gl(hi, &l, k);
            g.push(gc(k, o));
            g.extend(add_back(hi, &l, k));
            g
        };
        let h = {
            let mut h0 = flip(lo);
            h0.extend(add_gl(lo, &l, c));
            let mut g = h0.clone();
            g.push(gc(c, k));
            g.extend(rev(&h0));
            g
        };
        let h2 = {
            let mut h0 = flip(hi);
            h0.extend(add_gl(hi, &l, k));
            let mut g = h0.clone();
            g.push(gc(k, o));
            g.extend(rev(&h0));
            g
        };
        seq.push(It::Load(0));
        seq.push(It::Gs(a1));
        seq.push(It::Load(0));
        seq.push(It::Load(K as u64));
        seq.push(It::Gs(a2));
        seq.push(It::Load(K as u64));
        seq.push(It::Load(0));
        seq.push(It::Gs(h.clone()));
        seq.push(It::Load(0));
        seq.push(It::Gs(self.lean(t, o, 256, c)));
        seq.push(It::Load(0));
        seq.push(It::Gs(h.clone()));
        seq.push(It::Load(0));
        seq.push(It::Load(K as u64));
        seq.push(It::Gs(h2));
        seq.push(It::Load(K as u64));
        seq.push(It::Load(0));
        seq.push(It::Gs(h));
        seq.push(It::Load(0));
        if sub {
            seq.reverse();
        }
        for it in &seq {
            match it {
                It::Load(off) => {
                    for i in 0..K {
                        p.xc(l[i], bits + off + i as u64);
                    }
                }
                It::Gs(g) => {
                    if sub {
                        p.g(&rev(g));
                    } else {
                        p.g(g);
                    }
                }
            }
        }
        self.dirty = keep;
        for &q0 in &l {
            p.rel(q0);
        }
        p.rel(k);
        p.rel(c);
        p.rel(o);
        for i in 0..ZL {
            p.rel(self.zl[i]);
        }
    }
    /// x += lam^2 in place: halve 256 times, then Horner on x.
    /// LEAN_SQ: ov ^= [x_top < atop] on the top CMPW wires (the parent's compare with the addend's top wires given).
    fn clear_ov_top(&self, x: &[u32], atop: &[u32], c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        assert!(atop.len() == CMPW);
        let mut h: GL = x[k..].iter().map(|&q0| gx(q0)).collect();
        h.extend(add_gl(&x[k..], atop, c));
        let mut g = h.clone();
        g.push(gc(c, ov));
        g.extend(rev(&h));
        g
    }
    /// LEAN_SQ: x[j..256) += a (a.len() = 256 - j), carry-out on ov, fold ov c0 (the parent's chain), erase ov by the
    /// top-window compare against (a << j)'s top wires. The parent's add_plain + lean + clear_ov_plain, shifted.
    fn fold_shift(&self, x: &[u32], a: &[u32], j: usize, c: u32, ov: u32) -> GL {
        let w = 256 - j;
        assert!(a.len() == w && w >= CMPW);
        let mut g = add_gl(&x[j..], a, c);
        g.push(gc(c, ov));
        g.extend(add_back(&x[j..], a, c));
        if LEAN_ZL >= 4 {
            g.extend(self.lean(x, ov, RW, c));
        } else {
            let z = &self.zl;
            g.extend(inc_long(&x[0..CHW], ov, &self.dirty, c));
            g.extend(self.merged(&x[4..RW], ov, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c));
        }
        g.extend(self.clear_ov_top(x, &a[w - CMPW..], c, ov));
        g
    }
    /// LEAN_SQ: x[o..o+wv) += v, the carry-out carried on through the next SPILL_W wires by the borrowed-lane increment,
    /// then erased by the window compare (t = [x_window < v]). Exact unless the carry runs past the window (2^-64).
    fn spill_add(&self, x: &[u32], v: &[u32], o: usize, c: u32, t: u32) -> GL {
        let wv = v.len();
        let hi = o + wv;
        assert!(hi <= 256);
        let mut g = add_gl(&x[o..hi], v, c);
        g.push(gc(c, t));
        g.extend(add_back(&x[o..hi], v, c));
        let top = (hi + SPILL_W).min(256);
        if top > hi {
            g.extend(inc_long(&x[hi..top], t, &self.dirty, c));
        }
        let mut h: GL = x[o..hi].iter().map(|&q0| gx(q0)).collect();
        h.extend(add_gl(&x[o..hi], v, c));
        g.extend(h.clone());
        g.push(gc(c, t));
        g.extend(rev(&h));
        g
    }
    /// LEAN_SQ: x += (Z << sh) mod p (pos) or x -= (Z << sh) mod p, Z = z[0..zw) an integer below 2^zw. The low 256 - sh
    /// wires shift into x; the top zw - 256 + sh wires are the spill, added times c0 = 2^32 + 2^10 - 2^6 + 2^4 + 1.
    fn weighted(&self, x: &[u32], z: &[u32], zw: usize, sh: usize, pos: bool, c: u32, ov: u32) -> GL {
        let flip: GL = x.iter().map(|&q0| gx(q0)).collect();
        let mut g: GL = vec![];
        if !pos {
            g.extend(flip.clone());
        }
        let wlo = 256 - sh;
        g.extend(self.fold_shift(x, &z[..wlo], sh, c, ov));
        if zw > wlo {
            let hi = &z[wlo..zw];
            for (o, sg) in [(32usize, true), (10, true), (6, false), (4, true), (0, true)] {
                if !sg {
                    g.extend(flip.clone());
                }
                g.extend(self.spill_add(x, hi, o, c, ov));
                if !sg {
                    g.extend(flip.clone());
                }
            }
        }
        if !pos {
            g.extend(flip);
        }
        g
    }
    /// LEAN_SQ: x += lam^2 mod p. lam = L + 2^128 H, S = L + H: lam^2 = L^2 (1 - 2^128) + H^2 (c0 - 2^128) + 2^128 S^2.
    fn sq_into_lean(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
        let next0 = p.next;
        let (c, ov) = (p.alloc(), p.alloc());
        self.zl = p.allocn(LEAN_ZL);
        let (l, h) = (&lam[..128], &lam[128..]);
        let xa = [self.zl[0], self.zl[1]];
        if LEAN_SB {
            // 256-wire variant: lam^2 = L^2 + 2^129 L H + c0 H^2; pads = zl[2] and ov (ov idle during the squarers).
            let z = p.allocn(256);
            assert!(p.next == next0, "LEAN_SQ raised the peak: {} -> {}", next0, p.next);
            let pad = [self.zl[2], ov];
            sq_fwd(p, l, &z, pad, xa);
            p.g(&self.weighted(x, &z, 256, 0, true, c, ov));
            sq_rev(p, l, &z, pad, xa);
            sq_fwd(p, h, &z, pad, xa);
            for (sh, pos) in [(32usize, true), (10, true), (6, false), (4, true), (0, true)] {
                p.g(&self.weighted(x, &z, 256, sh, pos, c, ov));
            }
            if !LEAN_NEGCTL {
                sq_rev(p, h, &z, pad, xa);
            }
            cross_fwd(p, l, h, &z, self.zl[2], c);
            p.g(&self.weighted(x, &z, 256, 129, true, c, ov));
            cross_rev(p, l, h, &z, self.zl[2], c);
            for &q0 in z.iter().rev() {
                p.rel(q0);
            }
            for i in 0..LEAN_ZL {
                p.rel(self.zl[i]);
            }
            p.rel(ov);
            p.rel(c);
            assert!(p.next == next0);
            return;
        }
        let z = p.allocn(258);
        let s = p.alloc();
        assert!(p.next == next0, "LEAN_SQ raised the peak: {} -> {}", next0, p.next);
        let pad = [self.zl[2], self.zl[3]];
        sq_fwd(p, l, &z, pad, xa);
        p.g(&self.weighted(x, &z, 256, 0, true, c, ov));
        p.g(&self.weighted(x, &z, 256, 128, false, c, ov));
        sq_rev(p, l, &z, pad, xa);
        sq_fwd(p, h, &z, pad, xa);
        for (sh, pos) in [(32usize, true), (10, true), (6, false), (4, true), (0, true), (128, false)] {
            p.g(&self.weighted(x, &z, 256, sh, pos, c, ov));
        }
        sq_rev(p, h, &z, pad, xa);
        gid_add(p, l, h, &z[..128], Some(s));
        let sv: Vec<u32> = [l, &[s][..]].concat();
        sq_fwd(p, &sv, &z, pad, xa);
        p.g(&self.weighted(x, &z, 258, 128, true, c, ov));
        sq_rev(p, &sv, &z, pad, xa);
        if !LEAN_NEGCTL {
            let mut hp: Vec<u32> = h.to_vec();
            hp.push(pad[0]);
            let fl: GL = sv.iter().map(|&q0| gx(q0)).collect();
            p.g(&fl);
            gid_add(p, &sv, &hp, &z[..128], None);
            p.g(&fl);
        }
        p.rel(s);
        for &q0 in z.iter().rev() {
            p.rel(q0);
        }
        for i in 0..LEAN_ZL {
            p.rel(self.zl[i]);
        }
        p.rel(ov);
        p.rel(c);
        assert!(p.next == next0);
    }
    fn sq_into(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
        if LEAN_SQ {
            self.sq_into_lean(p, x, lam);
            return;
        }
        let (c, ov, d) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(ZL);
        let mut cur = x.to_vec();
        for _ in 0..256 {
            let mut prev: Vec<u32> = cur[1..].to_vec();
            prev.push(cur[0]);
            let (t2, h) = self.dbl(&prev, c);
            assert!(t2 == cur);
            p.g(&rev(&h));
            cur = prev;
        }
        // ZFOR-wait signed digits: cur = x / 2^256. One plain round (2 cur + lam), 256 signed rounds on lam's bits
        // (2 cur + s_i lam), subtract lam, halve: x + lam^2.
        {
            let (t2, h) = self.dbl(&cur, c);
            cur = t2;
            p.g(&h);
            p.g(&[gx(d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, false));
            p.g(&[gx(d)]);
        }
        for i in (0..256).rev() {
            let (t2, h) = self.dbl(&cur, c);
            cur = t2;
            p.g(&h);
            p.g(&[gc(lam[i], d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, false));
            p.g(&[gc(lam[i], d)]);
        }
        p.g(&self.sub_round(&cur, lam, c, ov));
        let (t2, h) = self.halve(&cur, c);
        cur = t2;
        p.g(&h);
        assert!(cur == x);
        p.rel(c);
        p.rel(ov);
        p.rel(d);
        for i in 0..ZL {
            p.rel(self.zl[i]);
        }
    }
}
struct Kept {
    y0: u32,
    y1: u32,
    par: u32,
    xtop: u32,
}
fn map_lanes(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32], kept: Option<&Kept>) -> Vec<u32> {
    let mut m = vec![NONE; fc.next as usize];
    for i in 0..256 {
        m[i] = x[i];
        m[256 + i] = pas[i];
    }
    if let Some(k) = kept {
        m[fc.y0 as usize] = k.y0;
        m[fc.y1 as usize] = k.y1;
    }
    for v in 0..fc.next as usize {
        if m[v] == NONE {
            m[v] = p.alloc();
        }
    }
    m
}
fn mapg(m: &[u32], g: G) -> G {
    if g.2 != NONE {
        G(m[g.0 as usize], m[g.1 as usize], m[g.2 as usize])
    } else if g.1 != NONE {
        G(m[g.0 as usize], m[g.1 as usize], NONE)
    } else {
        G(m[g.0 as usize], NONE, NONE)
    }
}
fn emit_f(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32]) -> (Vec<u32>, Kept) {
    let m = map_lanes(p, fc, x, pas, None);
    for &g in &fc.gates {
        p.gate(mapg(&m, g));
    }
    for &g in &fc.last {
        p.gate(mapg(&m, g));
    }
    let a: Vec<u32> = fc.ar.iter().map(|&v| m[v as usize]).collect();
    let kept = Kept { y0: m[fc.y0 as usize], y1: m[fc.y1 as usize], par: m[fc.par as usize], xtop: m[fc.xtop as usize] };
    for v in 512..fc.next {
        if v != fc.y0 && v != fc.y1 {
            p.rel(m[v as usize]);
        }
    }
    (a, kept)
}
fn emit_finv(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32], k: &Kept) {
    let m = map_lanes(p, fc, x, pas, Some(k));
    for &g in fc.last.iter().rev() {
        p.gate(mapg(&m, g));
    }
    for &g in fc.gates.iter().rev() {
        p.gate(mapg(&m, g));
    }
    for v in 512..fc.next {
        p.rel(m[v as usize]);
    }
}

/// P5 shell: this tree's walk F (`f_circuit`) as the division walk of the frogdrop product stage, emitted through the
/// Track 2 builder. Lanes as in `emit_f` / `emit_finv` (map_lanes), with B allocating. After `forward` the 2 lanes known
/// to be 0 (ring positions 0 and W-1 after F: inv bit 255 = a[255], and xtop; the ring is rotated, so these are
/// whatever lanes sit there) are freed, so the products see 255 inv + sign + 256 passenger
/// = 512 live, the ledger of the count of record; `inverse` takes them back (acquire) before the reversed gate list.
struct MarkerWalk {
    fc: FCirc,
    kept: Vec<(u64, u64, u64, u64)>, // (y0, y1, z255, ztop) physical lanes of each open division
}
impl MarkerWalk {
    fn emit(b: &mut fd2::builder::B, m: &[u64], g: G) {
        let l = |v: u32| QubitId(m[v as usize]);
        if g.2 != NONE {
            b.ccx(l(g.0), l(g.1), l(g.2));
        } else if g.1 != NONE {
            b.cx(l(g.0), l(g.1));
        } else {
            b.x(l(g.0));
        }
    }
}
impl fd2::pointadd_frogdrop::Walk for MarkerWalk {
    fn forward(&mut self, b: &mut fd2::builder::B, x: &[QubitId], pas: &[QubitId]) -> (Vec<QubitId>, (QubitId, bool)) {
        let fc = &self.fc;
        let mut m = vec![u64::MAX; fc.next as usize];
        for i in 0..256 {
            m[i] = x[i].0;
            m[256 + i] = pas[i].0;
        }
        for v in 512..fc.next as usize {
            m[v] = b.alloc().0;
        }
        let (tof0, (_, c0, e0)) = (b.tof, b.census());
        for &g in fc.gates.iter().chain(fc.last.iter()) {
            Self::emit(b, &m, g);
        }
        let (_, c1, e1) = b.census();
        eprintln!("P5WALK fwd list_ccx {} B_tof_delta {} census_ccx_delta {} census_exp_delta {:.1}",
                  fc.gates.iter().chain(fc.last.iter()).filter(|g| g.2 != NONE).count(), b.tof - tof0, c1 - c0, e1 - e0);
        let a: Vec<QubitId> = fc.ar.iter().map(|&v| QubitId(m[v as usize])).collect();
        let (y0, y1) = (m[fc.y0 as usize], m[fc.y1 as usize]);
        let (z255, ztop) = (a[255].0, m[fc.xtop as usize]);
        assert!(z255 != ztop && !pas.iter().any(|q| q.0 == z255 || q.0 == ztop), "zero lanes are ring lanes");
        for v in 512..fc.next {
            if v != fc.y0 && v != fc.y1 {
                b.free(QubitId(m[v as usize]));
            }
        }
        b.free(QubitId(z255)); // inv < 2^255: bit 255 is 0 (J6, team40/shell/SHELL.md)
        b.free(QubitId(ztop)); // ring position W-1 = 0 at the end of F
        self.kept.push((y0, y1, z255, ztop));
        (a[..255].to_vec(), (QubitId(m[fc.par as usize]), true))
    }
    fn inverse(&mut self, b: &mut fd2::builder::B, x: &[QubitId], pas: &[QubitId]) {
        let (y0, y1, z255, ztop) = self.kept.pop().expect("inverse without forward");
        b.acquire(QubitId(ztop));
        b.acquire(QubitId(z255));
        let fc = &self.fc;
        let mut m = vec![u64::MAX; fc.next as usize];
        for i in 0..256 {
            m[i] = x[i].0;
            m[256 + i] = pas[i].0;
        }
        m[fc.y0 as usize] = y0;
        m[fc.y1 as usize] = y1;
        for v in 512..fc.next as usize {
            if m[v] == u64::MAX {
                m[v] = b.alloc().0;
            }
        }
        let (tof0, (_, c0, e0)) = (b.tof, b.census());
        for &g in fc.last.iter().rev().chain(fc.gates.iter().rev()) {
            Self::emit(b, &m, g);
        }
        let (_, c1, e1) = b.census();
        eprintln!("P5WALK inv list_ccx {} B_tof_delta {} census_ccx_delta {} census_exp_delta {:.1}",
                  fc.gates.iter().chain(fc.last.iter()).filter(|g| g.2 != NONE).count(), b.tof - tof0, c1 - c0, e1 - e0);
        for v in 512..fc.next as usize {
            b.free(QubitId(m[v]));
        }
    }
}
fn build_fd2() -> Vec<Op> {
    let fc = f_circuit();
    let mut b = fd2::builder::B::new();
    let mut w = MarkerWalk { fc, kept: vec![] };
    fd2::pointadd_frogdrop::point_add_walk(&mut b, &mut w);
    assert!(w.kept.is_empty());
    let ops = fd2::finish(b);
    eprintln!("point_add: ops {} (P5SHELL: fd2 product stage around F)", ops.len());
    ops
}

pub fn build() -> Vec<Op> {
    if P5SHELL {
        return build_fd2();
    }
    let fc = f_circuit();
    let mut p = P { ops: Vec::with_capacity(190_000_000), free: vec![], next: 0, bits: 0 };
    let x = p.allocn(256);
    let y = p.allocn(256);
    let (ox, oy) = (0u64, 256u64);
    p.bits = 512;
    for r in 0..4u64 {
        let mut o = Op::empty();
        o.kind = OperationType::Register;
        o.r_target = RegisterId(r);
        p.ops.push(o);
    }
    for (r, lanes) in [(0u64, &x), (1u64, &y)] {
        for &a in lanes.iter() {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.q_target = q(a);
            o.r_target = RegisterId(r);
            p.ops.push(o);
        }
    }
    for (r, base) in [(2u64, ox), (3u64, oy)] {
        for i in 0..256u64 {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.c_target = BitId(base + i);
            o.r_target = RegisterId(r);
            p.ops.push(o);
        }
    }
    let w = CAPW;
    let mut a = S3 { dirty: y.clone(), zl: vec![] };
    a.cl_add(&mut p, &x, ox, true);
    a.dirty = x.clone();
    a.cl_add(&mut p, &y, oy, true);
    // division 1
    let (a1, k1) = emit_f(&mut p, &fc, &x, &y);
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    a.zl = p.allocn(ZL);
    let (lam, _low1, g) = a.product(&mut p, &a1[..255], &y, k1.xtop, a1[255], w);
    p.g(&g);
    drop(g);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    let cg = a.cneg_list(&lam, k1.par, false, k1.xtop);
    p.g(&cg);
    let m1: Vec<u64> = y[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
    for &q0 in &y[..256 - w] {
        p.rel(q0);
    }
    emit_finv(&mut p, &fc, &x, &lam, &k1);
    // dy recompute
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(ZL);
    a.dirty = [&lam[..], &x[..256 - w]].concat();
    let (dy2, low2, g) = a.product(&mut p, &lam, &x, c, ov, w);
    p.g(&g);
    for i in 0..(256 - w) {
        p.zc(dy2[i], m1[i]);
    }
    p.g(&rev(&g));
    drop(g);
    for &q0 in &low2 {
        p.rel(q0);
    }
    p.rel(c);
    p.rel(ov);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    // x: dx' = lam^2 - dx - 3 ox
    let c2 = p.alloc();
    a.dirty = lam.clone();
    a.neg(&mut p, &x, c2);
    p.rel(c2);
    a.dirty = lam.clone();
    a.sq_into(&mut p, &x, &lam);
    for _ in 0..3 {
        a.dirty = lam.clone();
        a.cl_add(&mut p, &x, ox, true);
    }
    // y: ndy = -lam dx'; lam's top bits go on living inside it
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(ZL);
    a.dirty = [&x[..], &lam[..256 - w]].concat();
    let (ndy, _low4, g) = a.product(&mut p, &x, &lam, c, ov, w);
    p.g(&g);
    drop(g);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    p.rel(ov);
    a.neg(&mut p, &ndy, c);
    p.rel(c);
    let m2: Vec<u64> = lam[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
    for &q0 in &lam[..256 - w] {
        p.rel(q0);
    }
    // division 2
    let (a2, k2) = emit_f(&mut p, &fc, &x, &ndy);
    a.dirty = [&a2[..255 - w], &ndy[..]].concat();
    a.zl = p.allocn(ZL);
    let (l2, low5, g) = a.product(&mut p, &ndy, &a2[..255], k2.xtop, a2[255], w);
    p.g(&g);
    let cg = a.cneg_list(&l2, k2.par, true, k2.xtop);
    p.g(&cg);
    for i in 0..(256 - w) {
        p.zc(l2[i], m2[i]);
    }
    p.g(&rev(&cg));
    p.g(&rev(&g));
    drop(g);
    for &q0 in &low5 {
        p.rel(q0);
    }
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    emit_finv(&mut p, &fc, &x, &ndy, &k2);
    a.dirty = ndy.clone();
    a.cl_add(&mut p, &x, ox, false);
    a.dirty = x.clone();
    a.cl_add(&mut p, &ndy, oy, true);
    // move ndy onto the y register
    let mut cur = ndy.clone();
    for i in 0..256 {
        if cur[i] == y[i] {
            continue;
        }
        for j in (i + 1)..256 {
            if cur[j] == y[i] {
                cur[j] = cur[i];
                break;
            }
        }
        p.g(&[gc(cur[i], y[i]), gc(y[i], cur[i]), gc(cur[i], y[i])]);
        cur[i] = y[i];
    }
    eprintln!("point_add: ops {} peak qubits {}", p.ops.len(), p.next);
    p.ops
}

// v3 KT7 step 3: KT8 start machine (wide experiment)
#[allow(dead_code, unused)]
pub mod kt8;
// P5 shell (op-p5): the transplanted Track 2 builder + frogdrop product stage, used only when P5SHELL = true.
#[allow(dead_code, unused)]
pub mod fd2;

// v3 G2: window primitives (INV4 port from wt-q765-prims f5deab0, builder shim from wt-q765-v3-s1), not called by build(); tests only.
#[allow(dead_code, unused_imports)]
mod prims_builder;
#[allow(dead_code, unused_imports)]
mod window_prims;

/// Catalyst-swap hop for the K2 half (gate lists checked in a gate-level model).
mod hop2 {
    use super::prims_builder::{B, G};
    use super::window_prims::{self as wp, Cfg};
    use crate::circuit::QubitId as Q;
    /// R *= x for odd R and odd x; rb, xb = lanes of bits 1.. of each (bit 0 of both a known 1, never touched).
    pub fn imul_odd(b: &mut B, rb: &[Q], xb: &[Q], pool: &[Q]) {
        let n = rb.len() + 1;
        assert!(n >= 3 && xb.len() == n - 1);
        for i in (1..=n - 2).rev() {
            wp::cadd_p(b, Cfg::PY, rb[i - 1], &xb[..n - i - 1], &rb[i..], pool);
        }
        wp::add_p(b, Cfg::PY, &xb[..n - 1], rb, pool, None);
    }
    fn ccx(g: &[G]) -> usize { g.iter().filter(|e| matches!(e, G::Ccx(..))).count() }
    /// R *= K (K = 1 mod 4) as a product of (1 + 2^j)^(+-1) factors, cheapest signed plan by search (r2_inv.kmul).
    pub fn kmul(b: &mut B, r: &[Q], k: u64, pool: &[Q]) {
        let m = r.len();
        let mk: u64 = if m >= 64 { u64::MAX } else { (1u64 << m) - 1 };
        let k = k & mk;
        assert!(m < 2 || k % 4 == 1, "kmul needs K = 1 mod 4");
        let cost: Vec<usize> = (0..m).map(|j| if j >= 2 { ccx(&wp::rec(b, |b| wp::mul1p(b, Cfg::PY, r, j, pool))) } else { 0 }).collect();
        let mulm = |a: u64, c: u64| -> u64 { ((a as u128 * c as u128) as u64) & mk };
        fn dfs(j0: usize, k: u64, m: usize, cost: &[usize], mulm: &dyn Fn(u64, u64) -> u64, plan: &mut Vec<(usize, bool)>, c: usize, best: &mut (Vec<(usize, bool)>, usize)) {
            if c >= best.1 { return; }
            let mut j = j0;
            while j < m && (k >> j) & 1 == 0 { j += 1; }
            if j >= m { *best = (plan.clone(), c); return; }
            let f = 1u64.wrapping_add(1u64 << j);
            plan.push((j, true));
            dfs(j + 1, mulm(k, wp::inv2k(f, m)), m, cost, mulm, plan, c + cost[j], best);
            plan.pop();
            plan.push((j, false));
            dfs(j + 1, mulm(k, f), m, cost, mulm, plan, c + cost[j], best);
            plan.pop();
        }
        let mut best: (Vec<(usize, bool)>, usize) = (vec![], usize::MAX);
        dfs(2, k, m, &cost, &mulm, &mut vec![], 0, &mut best);
        for &(j, fwd) in &best.0 {
            if fwd { wp::mul1p(b, Cfg::PY, r, j, pool); } else { wp::undo(b, |b| wp::mul1p(b, Cfg::PY, r, j, pool)); }
        }
    }
    /// x -> p / x in place (x odd), catalyst gd (len(x) - 1 dirty lanes). park: the third multiply is skipped, gd is
    /// left holding x g (the reversed gates give it back if x is the same word on the way out).
    pub fn cat_invp(b: &mut B, x: &[Q], gd: &[Q], pool: &[Q], p: u64, park: bool) {
        let xb = &x[1..];
        assert_eq!(gd.len(), xb.len());
        imul_odd(b, xb, gd, pool);
        wp::undo(b, |b| imul_odd(b, gd, xb, pool));
        if !park { imul_odd(b, xb, gd, pool); }
        for (&a, &c) in xb.iter().zip(gd.iter()) { b.cx(a, c); b.cx(c, a); b.cx(a, c); }
        for &q in xb { b.x(q); }
        kmul(b, x, p.wrapping_neg(), pool);
    }
    /// (A, B, tB) -> (A / B, tA, tB): the map of window_prims::k2_fwd with invp replaced by the catalyst swap.
    pub fn hop(b: &mut B, va: &[Q], vb: &[Q], sc: &[Q], gd: &[Q], pool: &[Q], p: u64, park: bool) {
        wp::idiv(b, Cfg::PY, va, vb, pool);
        cat_invp(b, vb, gd, pool, p, park);
        wp::undo(b, |b| wp::mac(b, Cfg::PY, vb, va, sc, pool));
    }
}

// S-D' P5: gate-list loader (Python lists replayed at fixed points of F; gl/gldump.py packs them).
mod gl_loader;
