//! Skywalk tail for the shrunken-PZ hybrid (974 / 999 lineage), behind `MIDQ_SKY_TAIL=1`.
//! Default off: the ping-pong tail and the whole op stream are unchanged.
//!
//! Design: `lab/skywalk/TAIL_DESIGN.md` v2 (per-tick rail tables at 5e-6 misses per input,
//! variant c5). This builds on mochimodev's GCD Skywalk (submission `4f0d213`, Matt Zweil and
//! MAI-A.A.E.): Stein binary GCD in the {u+v, u} rail frame, one controlled rail exchange and
//! one signed add per tick, the three-symbol history packed five ticks into eight wires (the
//! `heo_carry.rs` pack3/pack5 codec, ported here with its pack CCZ applied at once instead of
//! deferred), and the Sig/Del payloads mod p in the butterfly frame. The inherited notice and
//! limiting contract are reproduced in `SKYWALK_NOTICE.md` at the tree root.
//!
//! Handoff (forward), from the prefix state (A, B, ca, cb, q, parity) at the cut:
//!   0. the eight counter wires (zero at the cut) are released before the codec transient;
//!   1. the quotient flush, the 18-bit q truncation and the quotient codec run with A and B at
//!      their prefix widths (no resize before the codec);
//!   2. terminal := [A == 0] (terminal or draining handoff): ca -= cb, A ^= 1, mapping
//!      (0, 1, p, v) to the canonical (1, 1, p - v, v);
//!   3. parity signs as the ping-pong handoff: afterwards A == ca*x and B == cb*x (mod p);
//!   4. sel := [B even]; swap (A, B) and (ca, cb) on sel, so B is odd;
//!   5. rails (R1, R2) = (A + B, A) at the table width esw(0) (a TTK add), i.e. u = A, v = B;
//!   6. Sig := 2*ca + cb (one inverse cell), Del := cb; both narrowed to 256 wires.
//! Tick t (heo.rs `fwd_tick`, gate for gate): ctl = R1[0]; Fredkin R1[i] <-> R2[i] (i >= 1) on
//! ctl; R2[0] ^= ctl; ctl leaves the rail and becomes typ_t = typ_{t-1} ^ ctl; tau :=
//! [sign E == sign R2]; R2 -= E if tau else R2 += E (E = R1 >> 1, sign-extended by one wire);
//! tau := sign-flip of R2 (the letter's s_t); both rails resized to esw(t+1); then the payload
//! cell Sig <- (Sig - (-1)^typ Del) / 2 (`midq_mod_signed_add_halve`, subtract = !typ) and the
//! 256-Fredkin route swap(Sig, Del) on s_t. The group of letters 5g..5g+4 is packed into eight
//! wires right after tick 5g+5 has read typ_{5g+4}. Endpoint: Sig == Del == |x|^-1, Del ^= Sig.
//! The backward tail is the exact mirror.

use super::*;
use crate::point_add::trailmix_port::arith::gidney_const_adder::hybrid_add_refs;
use crate::point_add::trailmix_port::arith::mcx::mcx_clean_k;
use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{ctrl_add, ctrl_sub};

#[path = "sky_tail_tables.rs"]
mod tables;

pub(crate) fn enabled() -> bool {
    std::env::var("MIDQ_SKY_TAIL").ok().as_deref() == Some("1")
}

/// Plain payload cells (no fused rotation, no top-120 compares): the default for the Skywalk
/// tail, because those two proofs are keyed to the ping-pong coefficient-margin support.
pub(crate) fn plain_cells() -> bool {
    enabled() && std::env::var("MIDQ_SKY_FULL_CELLS").ok().as_deref() != Some("1")
}

/// (cut, L, esw[0..=R]) for the built cut (fixed per process).
pub(crate) fn table() -> (usize, usize, Vec<usize>) {
    static TABLE: std::sync::OnceLock<(usize, usize, Vec<usize>)> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let cut = midq_pz_cut();
        let &(c, l, esw) = tables::SKY_TABLES
            .iter()
            .find(|e| e.0 == cut)
            .unwrap_or_else(|| panic!("no Skywalk tail table for cut {cut}"));
        // MIDQ_SKY_TABLE_SHRINK=k (diagnostic only): every pre-park width k narrower, to check
        // that gate-level failures happen exactly on the table model's misses.
        let shrink = env_usize("MIDQ_SKY_TABLE_SHRINK", 0);
        let r = esw.len() - 1;
        let esw: Vec<usize> = esw.iter().enumerate()
            .map(|(t, &w)| if t < r { (w as usize).saturating_sub(shrink).max(2) } else { w as usize })
            .collect();
        (c, l, esw)
    }).clone()
}

/// The table's rail widths without a copy (support model hot path).
pub(crate) fn table_widths() -> &'static [usize] {
    static WIDTHS: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    WIDTHS.get_or_init(|| table().2)
}

fn trace_enabled() -> bool {
    std::env::var_os("MIDQ_TRACE_TAIL").is_some()
}

// ─── History tape: raw letters (typ_t, s_t) and packed groups of five ───────────────────────

pub(crate) struct Tape {
    raw: Vec<Option<(QReg, QReg)>>,
    groups: Vec<Option<Vec<QReg>>>,
}

impl Tape {
    fn new(r: usize) -> Self {
        Tape {
            raw: (0..r).map(|_| None).collect(),
            groups: (0..r.div_ceil(5)).map(|_| None).collect(),
        }
    }
    fn typ(&self, t: usize) -> &QReg {
        &self.raw[t].as_ref().unwrap_or_else(|| panic!("sky tape letter {t} is not raw")).0
    }
    fn letter(&self, t: usize) -> (&QReg, &QReg) {
        let (typ, s) = self.raw[t].as_ref().unwrap_or_else(|| panic!("sky tape letter {t} is not raw"));
        (typ, s)
    }
    fn push(&mut self, t: usize, typ: QReg, s: QReg) {
        assert!(self.raw[t].is_none());
        self.raw[t] = Some((typ, s));
    }
    fn take(&mut self, t: usize) -> (QReg, QReg) {
        self.raw[t].take().unwrap_or_else(|| panic!("sky tape letter {t} is not raw"))
    }
    fn pack(&mut self, c: &mut Circuit, g: usize) {
        let t0 = 5 * g;
        let l0 = self.take(t0);
        let l1 = self.take(t0 + 1);
        let l2 = self.take(t0 + 2);
        let p3 = pack3(c, l0, l1, l2);
        let l3 = self.take(t0 + 3);
        let l4 = self.take(t0 + 4);
        assert!(self.groups[g].is_none());
        self.groups[g] = Some(pack5(c, p3, l3, l4));
    }
    fn unpack(&mut self, c: &mut Circuit, g: usize) {
        let t0 = 5 * g;
        let p5 = self.groups[g].take().expect("packed sky group");
        let (p3, l3, l4) = unpack5(c, p5);
        let (l0, l1, l2) = unpack3(c, p3);
        self.push(t0, l0.0, l0.1);
        self.push(t0 + 1, l1.0, l1.1);
        self.push(t0 + 2, l2.0, l2.1);
        self.push(t0 + 3, l3.0, l3.1);
        self.push(t0 + 4, l4.0, l4.1);
    }
    fn is_empty(&self) -> bool {
        self.raw.iter().all(Option::is_none) && self.groups.iter().all(Option::is_none)
    }
}

// Skywalk's trit codec (heo_carry.rs to_hl / pair_pack / pack3 / pack5 and inverses). A letter
// (typ, s) is one of D = (0,0), S = (0,1), H = (1,0); (1,1) never occurs on the walk.
// (h, l) = (s, NOT(typ XOR s)) maps D -> (0,1), S -> (1,0), H -> (0,0).

fn to_hl(c: &mut Circuit, (typ, s): (QReg, QReg)) -> (QReg, QReg) {
    c.cx(&s, &typ);
    c.x(&typ);
    (s, typ)
}

fn from_hl(c: &mut Circuit, h: QReg, l: QReg) -> (QReg, QReg) {
    c.x(&l);
    c.cx(&h, &l);
    (l, h)
}

/// `anc == a AND b` on entry: measure it away with the CZ phase repair.
fn measure_clear_and(c: &mut Circuit, anc: QReg, a: &QReg, b: &QReg) {
    let m = c.alloc_bit();
    c.hmr(&anc, m);
    c.cz_if_bit(a, b, m);
    c.free_bit(m);
    c.zero_and_free(anc);
}

fn pair_pack(c: &mut Circuit, h1: &QReg, l1: &QReg, h2: &QReg, l2: &QReg) {
    let anc = c.alloc_qreg("midq.sky.codec.anc");
    c.cx(h1, h2);
    c.ccx(h1, h2, &anc);
    c.cswap(&anc, l1, l2);
    c.cx(&anc, l2);
    c.cx(&anc, h1);
    measure_clear_and(c, anc, h2, l2);
}

fn pair_unpack(c: &mut Circuit, h1: &QReg, l1: &QReg, h2: &QReg, l2: &QReg) {
    let anc = c.alloc_qreg("midq.sky.codec.anc");
    c.ccx(h2, l2, &anc);
    c.cx(&anc, h1);
    c.cx(&anc, l2);
    c.cswap(&anc, l1, l2);
    measure_clear_and(c, anc, h1, h2);
    c.cx(h1, h2);
}

/// Three letters (6 wires) -> 5 wires [a2, a1, a0, h3, l3].
fn pack3(c: &mut Circuit, l0: (QReg, QReg), l1: (QReg, QReg), l2: (QReg, QReg)) -> Vec<QReg> {
    let (h1, lo1) = to_hl(c, l0);
    let (h2, lo2) = to_hl(c, l1);
    let (h3, lo3) = to_hl(c, l2);
    pair_pack(c, &h1, &lo1, &h2, &lo2);
    let (f, a2, a1, a0) = (h1, lo1, h2, lo2);
    c.cswap(&f, &a1, &h3);
    c.cswap(&f, &a0, &lo3);
    c.cx(&f, &h3);
    c.cx(&f, &lo3);
    measure_clear_and(c, f, &h3, &lo3);
    vec![a2, a1, a0, h3, lo3]
}

fn unpack3(c: &mut Circuit, p3: Vec<QReg>) -> ((QReg, QReg), (QReg, QReg), (QReg, QReg)) {
    let [a2, a1, a0, h3, l3]: [QReg; 5] = p3.try_into().map_err(|_| ()).expect("P3 group has 5 wires");
    let f = c.alloc_qreg("midq.sky.codec.f");
    c.ccx(&h3, &l3, &f);
    c.cx(&f, &h3);
    c.cx(&f, &l3);
    c.cswap(&f, &a1, &h3);
    c.cswap(&f, &a0, &l3);
    pair_unpack(c, &f, &a2, &a1, &a0);
    let l0 = from_hl(c, f, a2);
    let l1 = from_hl(c, a1, a0);
    let l2 = from_hl(c, h3, l3);
    (l0, l1, l2)
}

/// P3 (5 wires) + two letters -> P5 (8 wires) [a2, a1, a0, h3, l3, b2, b1, b0].
fn pack5(c: &mut Circuit, p3: Vec<QReg>, l3: (QReg, QReg), l4: (QReg, QReg)) -> Vec<QReg> {
    let [a2, a1, a0, h3, lo3]: [QReg; 5] = p3.try_into().map_err(|_| ()).expect("P3 group has 5 wires");
    let (h4, lo4) = to_hl(c, l3);
    let (h5, lo5) = to_hl(c, l4);
    pair_pack(c, &h4, &lo4, &h5, &lo5);
    let (g, b2, b1, b0) = (h4, lo4, h5, lo5);
    c.cswap(&g, &a2, &b2);
    c.cswap(&g, &h3, &b1);
    c.cswap(&g, &lo3, &b0);
    c.cx(&g, &a2);
    c.cx(&g, &h3);
    c.cx(&g, &lo3);
    // g == a2 AND h3 AND lo3 here. Measure it away and apply its CCZ repair now (heo_carry.rs
    // defers this CCZ to the next unpack5; HEO_CODEC_NODEFER is the same repair, applied at once).
    let m = c.alloc_bit();
    c.hmr(&g, m);
    c.zero_and_free(g);
    c.ccz_if_bit(&a2, &h3, &lo3, m);
    c.free_bit(m);
    vec![a2, a1, a0, h3, lo3, b2, b1, b0]
}

fn unpack5(c: &mut Circuit, p5: Vec<QReg>) -> (Vec<QReg>, (QReg, QReg), (QReg, QReg)) {
    let [a2, a1, a0, h3, l3, b2, b1, b0]: [QReg; 8] =
        p5.try_into().map_err(|_| ()).expect("P5 group has 8 wires");
    let g = c.alloc_qreg("midq.sky.codec.g");
    let an2 = c.alloc_qreg("midq.sky.codec.an2");
    c.ccx(&a2, &h3, &an2);
    c.ccx(&an2, &l3, &g);
    measure_clear_and(c, an2, &a2, &h3);
    c.cx(&g, &a2);
    c.cx(&g, &h3);
    c.cx(&g, &l3);
    c.cswap(&g, &a2, &b2);
    c.cswap(&g, &h3, &b1);
    c.cswap(&g, &l3, &b0);
    pair_unpack(c, &g, &b2, &b1, &b0);
    let l3o = from_hl(c, g, b2);
    let l4o = from_hl(c, b1, b0);
    (vec![a2, a1, a0, h3, l3], l3o, l4o)
}

// ─── Rails ─────────────────────────────────────────────────────────────────────────────────

/// Forward tick's signed add: tau := [sign E == sign R2]; R2 -= E if tau else R2 += E
/// (complemented-target TTK add, no ancilla); tau := sign(R2 before) XOR sign(R2 after).
fn tick_add(c: &mut Circuit, e: &[QReg], r2: &[QReg], tau: &QReg) {
    let w = e.len();
    assert_eq!(r2.len(), w);
    c.cx(&e[w - 1], tau);
    c.cx(&r2[w - 1], tau);
    c.x(tau);
    for q in r2 {
        c.cx(tau, q);
    }
    let r2r: Vec<&QReg> = r2.iter().collect();
    let er: Vec<&QReg> = e.iter().collect();
    hybrid_add_refs(c, &r2r, &er, 0);
    for q in r2 {
        c.cx(tau, q);
    }
    c.x(tau);
    c.cx(&e[w - 1], tau);
    c.cx(&r2[w - 1], tau);
}

/// Exact inverse of [`tick_add`]; leaves tau = 0.
fn tick_unadd(c: &mut Circuit, e: &[QReg], r2: &[QReg], tau: &QReg) {
    let w = e.len();
    assert_eq!(r2.len(), w);
    // s ^ sign E ^ sign R2' = NOT(forward subtract flag).
    c.cx(&r2[w - 1], tau);
    c.cx(&e[w - 1], tau);
    for q in r2 {
        c.cx(tau, q);
    }
    let r2r: Vec<&QReg> = r2.iter().collect();
    let er: Vec<&QReg> = e.iter().collect();
    hybrid_add_refs(c, &r2r, &er, 0);
    for q in r2 {
        c.cx(tau, q);
    }
    c.cx(&r2[w - 1], tau);
    c.cx(&e[w - 1], tau);
}

/// Rail part of forward tick t: rails at w = esw(t) on entry, esw(t+1) on exit; letter t raw.
fn fwd_rails(c: &mut Circuit, r1: &mut Vec<QReg>, r2: &mut Vec<QReg>, tape: &mut Tape, t: usize, w: usize, w_next: usize) {
    assert_eq!(r1.len(), w, "sky rail R1 width at tick {t}");
    assert_eq!(r2.len(), w, "sky rail R2 width at tick {t}");
    assert!(w >= 2 && w_next >= 2);
    for i in 1..w {
        c.cswap(&r1[0], &r1[i], &r2[i]);
    }
    c.cx(&r1[0], &r2[0]);
    let ctl = r1.remove(0);
    if t > 0 {
        c.cx(tape.typ(t - 1), &ctl);
    }
    if t >= 5 && t % 5 == 0 {
        tape.pack(c, t / 5 - 1);
    }
    let ext = c.alloc_qreg("midq.sky.e_sign");
    c.cx(r1.last().expect("E keeps a sign bit"), &ext);
    r1.push(ext);
    let tau = c.alloc_qreg("midq.sky.s");
    tick_add(c, r1, r2, &tau);
    midq_signed_resize(c, r1, w_next, "midq.sky.r1");
    midq_signed_resize(c, r2, w_next, "midq.sky.r2");
    tape.push(t, ctl, tau);
}

/// Exact inverse of [`fwd_rails`].
fn rev_rails(c: &mut Circuit, r1: &mut Vec<QReg>, r2: &mut Vec<QReg>, tape: &mut Tape, t: usize, w: usize, w_next: usize) {
    assert_eq!(r1.len(), w_next);
    assert_eq!(r2.len(), w_next);
    midq_signed_resize(c, r1, w, "midq.sky.r1");
    midq_signed_resize(c, r2, w, "midq.sky.r2");
    let (ctl, tau) = tape.take(t);
    tick_unadd(c, r1, r2, &tau);
    c.zero_and_free(tau);
    let ext = r1.pop().expect("E sign extension");
    c.cx(r1.last().expect("E keeps a sign bit"), &ext);
    c.zero_and_free(ext);
    if t >= 5 && t % 5 == 0 {
        tape.unpack(c, t / 5 - 1);
    }
    if t > 0 {
        c.cx(tape.typ(t - 1), &ctl);
    }
    r1.insert(0, ctl);
    c.cx(&r1[0], &r2[0]);
    for i in 1..w {
        c.cswap(&r1[0], &r1[i], &r2[i]);
    }
}

fn with_section<R>(c: &mut Circuit, name: &str, body: impl FnOnce(&mut Circuit) -> R) -> R {
    // Sections flush pending frees, so (as in the ping-pong tail) they exist only under trace.
    if trace_enabled() {
        let prev = c.push_section(name);
        let out = body(c);
        c.pop_section(&prev);
        out
    } else {
        body(c)
    }
}

fn cell_and_route(c: &mut Circuit, sig: &[QReg], del: &[QReg], typ: &QReg, s: &QReg, inverse: bool) {
    let route = |c: &mut Circuit| {
        for (x, y) in sig.iter().zip(del) {
            c.cswap(s, x, y);
        }
    };
    let dir = if inverse { "backward" } else { "forward" };
    if inverse {
        with_section(c, &format!("midq.sky.{dir}.route"), route);
    }
    // MIDQ_SKY_TRACE_ROOM=1 (diagnostic): live count at cell entry and the cell's Toffoli.
    let room_trace = std::env::var_os("MIDQ_SKY_TRACE_ROOM").is_some();
    let before = room_trace.then(|| {
        c.flush_pending_frees();
        (c.b.active_qubits, c.b.counted_kind_ops[OperationType::CCX as usize]
            + c.b.counted_kind_ops[OperationType::CCZ as usize])
    });
    with_section(c, &format!("midq.sky.{dir}.cell"), |c| {
        c.x(typ);
        midq_mod_signed_add_halve(c, sig, del, typ, inverse);
        c.x(typ);
    });
    if let Some((active, tof)) = before {
        let after = c.b.counted_kind_ops[OperationType::CCX as usize]
            + c.b.counted_kind_ops[OperationType::CCZ as usize];
        eprintln!("MIDQ_SKY_CELL_ROOM inv={} active={active} tof={}", u8::from(inverse), after - tof);
    }
    if !inverse {
        with_section(c, &format!("midq.sky.{dir}.route"), route);
    }
}

/// R forward ticks (R = esw.len() - 1), each with its payload cell and route when `payload`
/// is given; then the last complete group is packed.
fn walk_forward(c: &mut Circuit, r1: &mut Vec<QReg>, r2: &mut Vec<QReg>, tape: &mut Tape, esw: &[usize],
    payload: Option<(&[QReg], &[QReg])>) {
    let r = esw.len() - 1;
    for t in 0..r {
        with_section(c, "midq.sky.forward.rails", |c| fwd_rails(c, r1, r2, tape, t, esw[t], esw[t + 1]));
        if let Some((sig, del)) = payload {
            let (typ, s) = tape.letter(t);
            cell_and_route(c, sig, del, typ, s, false);
        }
    }
    if r >= 5 && r % 5 == 0 {
        with_section(c, "midq.sky.forward.rails", |c| tape.pack(c, r / 5 - 1));
    }
}

fn walk_backward(c: &mut Circuit, r1: &mut Vec<QReg>, r2: &mut Vec<QReg>, tape: &mut Tape, esw: &[usize],
    payload: Option<(&[QReg], &[QReg])>) {
    let r = esw.len() - 1;
    if r >= 5 && r % 5 == 0 {
        with_section(c, "midq.sky.backward.rails", |c| tape.unpack(c, r / 5 - 1));
    }
    for t in (0..r).rev() {
        if let Some((sig, del)) = payload {
            let (typ, s) = tape.letter(t);
            cell_and_route(c, sig, del, typ, s, true);
        }
        with_section(c, "midq.sky.backward.rails", |c| rev_rails(c, r1, r2, tape, t, esw[t], esw[t + 1]));
    }
}

// ─── Handoff, endpoint and the two directions ──────────────────────────────────────────────

pub(crate) struct SkyTailState {
    tape: Tape,
    esw: Vec<usize>,
    qcode: Option<Vec<QReg>>,
    terminal: QReg,
    sel: QReg,
    original_widths: [usize; 4],
    original_q_width: usize,
    handoff_q_width: usize,
    counter_width: usize,
    packed_parity: bool,
}

/// terminal ^= [A == 0].
fn xor_a_zero(c: &mut Circuit, a: &[QReg], out: &QReg) {
    for q in a {
        c.x(q);
    }
    let refs: Vec<&QReg> = a.iter().collect();
    mcx_clean_k(c, &refs, out);
    for q in a {
        c.x(q);
    }
}

fn toffoli_since(c: &Circuit, start: usize) -> usize {
    midq_toffoli_since(c, start)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn forward(
    c: &mut Circuit,
    a: &mut Vec<QReg>,
    b: &mut Vec<QReg>,
    ca: &mut Vec<QReg>,
    cb: &mut Vec<QReg>,
    q: &mut Vec<QReg>,
    counter: &mut Vec<QReg>,
    parity: &mut Option<BorrowedQReg<'_>>,
) -> SkyTailState {
    let (cut, l, esw) = table();
    let r = esw.len() - 1;
    let trace = trace_enabled();
    let start = c.b.current_ops_len();
    let original_widths = [a.len(), b.len(), ca.len(), cb.len()];
    assert_eq!(a.len(), b.len(), "sky handoff: A and B share the prefix width");
    if trace {
        c.flush_pending_frees();
        eprintln!("MIDQ_SKY_HANDOFF cut={cut} L={l} R={r} widths={original_widths:?} q_width={} esw0={} active={}",
            q.len(), esw[0], c.b.active_qubits);
    }
    let (qcode, terminal, original_q_width, handoff_q_width, counter_width, packed_parity, sel) =
        with_section(c, "midq.sky.forward.handoff", |c| {
            // The counter is zero at the cut (no-terminal prefix, popcount cache erased): release
            // its eight wires before the codec transient (the backward re-allocates them last).
            let counter_width = counter.len();
            for wire in std::mem::take(counter) {
                c.zero_and_free(wire);
            }
            // 1. Flush, truncation and quotient codec at the prefix widths of A and B.
            shrunken_pz_resize(c, ca, 257, "midq.ca");
            shrunken_pz_resize(c, cb, 257, "midq.cb");
            midq_flush_quotient(c, ca, cb, q, false);
            let original_q_width = q.len();
            let handoff_q_bits = midq_handoff_q_bits();
            if q.len() > handoff_q_bits {
                shrunken_pz_resize(c, q, handoff_q_bits, "q");
            }
            let handoff_q_width = q.len();
            let qcode = quotient_code::enabled().then(|| quotient_code::compress(c, ca, cb, q));
            // 2. Terminal / draining handoff: (0, 1, p, v) -> (1, 1, p - v, v).
            let terminal = c.alloc_qreg("midq.sky.terminal");
            xor_a_zero(c, a, &terminal);
            {
                let car: Vec<&QReg> = ca.iter().collect();
                let cbr: Vec<&QReg> = cb.iter().collect();
                ctrl_sub(c, &terminal, &car, &cbr);
            }
            c.cx(&terminal, &a[0]);
            // 3. Parity signs: A == ca*x, B == cb*x (mod p) afterwards.
            {
                let par = parity.as_deref().expect("live PZ parity");
                midq_field_neg(c, par, ca, cb);
                c.x(par);
                midq_field_neg(c, par, cb, ca);
                c.x(par);
            }
            let packed_parity = sign_storage::pack_parity(c, cb, original_widths[3], parity);
            // 4. sel = [B even]; afterwards B (= v) is odd.
            let sel = c.alloc_qreg("midq.sky.sel");
            c.x(&sel);
            c.cx(&b[0], &sel);
            midq_controlled_swap_registers(c, &sel, a, b);
            midq_controlled_swap_registers(c, &sel, ca, cb);
            (qcode, terminal, original_q_width, handoff_q_width, counter_width, packed_parity, sel)
        });
    let handoff_t = toffoli_since(c, start);
    let seed_start = c.b.current_ops_len();
    with_section(c, "midq.sky.forward.seed", |c| {
        // 5. Rails (R1, R2) = (A + B, A): R1 lives in the B register, R2 in the A register.
        shrunken_pz_resize(c, a, esw[0], "midq.sky.r2");
        shrunken_pz_resize(c, b, esw[0], "midq.sky.r1");
        let br: Vec<&QReg> = b.iter().collect();
        let ar: Vec<&QReg> = a.iter().collect();
        hybrid_add_refs(c, &br, &ar, 0);
        // 6. Sig = 2*ca + cb (the inverse cell with subtract = 1), Del = cb.
        let one = c.alloc_qreg("midq.sky.seed_one");
        c.x(&one);
        midq_mod_signed_add_halve(c, ca, cb, &one, true);
        c.x(&one);
        c.zero_and_free(one);
        // Both payloads are canonical here, so bit 256 is zero on the support.
        shrunken_pz_resize(c, ca, 256, "midq.ca");
        shrunken_pz_resize(c, cb, 256, "midq.cb");
    });
    let seed_t = toffoli_since(c, seed_start);
    let walk_start = c.b.current_ops_len();
    let mut tape = Tape::new(r);
    walk_forward(c, b, a, &mut tape, &esw, Some((&ca[..], &cb[..])));
    let walk_t = toffoli_since(c, walk_start);
    let end_start = c.b.current_ops_len();
    with_section(c, "midq.sky.forward.endpoint", |c| {
        // Parked: Sig == Del == |x|^-1. Keep Sig at the 257-wire payload ABI; clear Del.
        shrunken_pz_resize(c, ca, 257, "midq.ca");
        for (keep, duplicate) in ca.iter().zip(cb.iter()) {
            c.cx(keep, duplicate);
        }
        for wire in std::mem::take(cb) {
            c.zero_and_free(wire);
        }
    });
    if trace {
        eprintln!(
            "MIDQ_SKY_TAIL_FORWARD total={} handoff={handoff_t} seed={seed_t} walk={walk_t} endpoint={}",
            toffoli_since(c, start), toffoli_since(c, end_start)
        );
    }
    SkyTailState {
        tape,
        esw,
        qcode,
        terminal,
        sel,
        original_widths,
        original_q_width,
        handoff_q_width,
        counter_width,
        packed_parity,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn backward(
    c: &mut Circuit,
    a: &mut Vec<QReg>,
    b: &mut Vec<QReg>,
    ca: &mut Vec<QReg>,
    cb: &mut Vec<QReg>,
    q: &mut Vec<QReg>,
    counter: &mut Vec<QReg>,
    parity: &mut Option<BorrowedQReg<'_>>,
    state: SkyTailState,
) {
    let SkyTailState {
        mut tape,
        esw,
        qcode,
        terminal,
        sel,
        original_widths,
        original_q_width,
        handoff_q_width,
        counter_width,
        packed_parity,
    } = state;
    let trace = trace_enabled();
    let start = c.b.current_ops_len();
    assert!(counter.is_empty(), "the counter wires were released by the sky handoff");
    with_section(c, "midq.sky.backward.endpoint", |c| {
        assert_eq!(ca.len(), 257, "Sig keeps the 257-wire payload ABI");
        assert!(cb.is_empty());
        *cb = c.alloc_qreg_bits("midq.cb", 256);
        for (keep, duplicate) in ca.iter().zip(cb.iter()) {
            c.cx(keep, duplicate);
        }
        shrunken_pz_resize(c, ca, 256, "midq.ca");
    });
    walk_backward(c, b, a, &mut tape, &esw, Some((&ca[..], &cb[..])));
    assert!(tape.is_empty(), "every sky letter is consumed by the reverse walk");
    with_section(c, "midq.sky.backward.seed", |c| {
        shrunken_pz_resize(c, ca, 257, "midq.ca");
        shrunken_pz_resize(c, cb, 257, "midq.cb");
        let one = c.alloc_qreg("midq.sky.seed_one");
        c.x(&one);
        midq_mod_signed_add_halve(c, ca, cb, &one, false);
        c.x(&one);
        c.zero_and_free(one);
        // R1 = A + B back to B: B = NOT(NOT R1 + A).
        for wire in b.iter() {
            c.x(wire);
        }
        let br: Vec<&QReg> = b.iter().collect();
        let ar: Vec<&QReg> = a.iter().collect();
        hybrid_add_refs(c, &br, &ar, 0);
        for wire in b.iter() {
            c.x(wire);
        }
        shrunken_pz_resize(c, a, original_widths[0], "A");
        shrunken_pz_resize(c, b, original_widths[1], "B");
    });
    with_section(c, "midq.sky.backward.handoff", |c| {
        midq_controlled_swap_registers(c, &sel, ca, cb);
        midq_controlled_swap_registers(c, &sel, a, b);
        c.cx(&b[0], &sel);
        c.x(&sel);
        c.zero_and_free(sel);
        if packed_parity {
            sign_storage::restore_parity(c, cb, parity);
        }
        {
            let par = parity.as_deref().expect("restored PZ parity");
            c.x(par);
            midq_field_neg(c, par, cb, ca);
            c.x(par);
            midq_field_neg(c, par, ca, cb);
        }
        c.cx(&terminal, &a[0]);
        {
            let car: Vec<&QReg> = ca.iter().collect();
            let cbr: Vec<&QReg> = cb.iter().collect();
            ctrl_add(c, &terminal, &car, &cbr);
        }
        xor_a_zero(c, a, &terminal);
        c.zero_and_free(terminal);
        if let Some(code) = qcode {
            quotient_code::restore(c, ca, cb, q, code, handoff_q_width);
        }
        debug_assert_eq!(q.len(), handoff_q_width);
        shrunken_pz_resize(c, q, original_q_width, "q");
        midq_flush_quotient(c, ca, cb, q, true);
        shrunken_pz_resize(c, ca, original_widths[2], "ca");
        shrunken_pz_resize(c, cb, original_widths[3], "cb");
        *counter = c.alloc_qreg_bits("midq.sky.counter", counter_width);
    });
    if trace {
        eprintln!("MIDQ_SKY_TAIL_BACKWARD total={}", toffoli_since(c, start));
    }
}

#[path = "sky_tail_selftest.rs"]
mod checks;
pub(crate) use checks::run as selftest;
