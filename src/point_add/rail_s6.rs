// ======================================================================================================================
// Lane S: the rail barrel for shift letters e = k1 + 2 k2 + 4 k3 in 0..=5 (promise) at ~7w/4 Toffoli, round 61's
// seven-block word in ring coordinates with the promise aligned to the top slot. No ancilla, no pad, any width >= 5.
//
// Rail: wires t[0..w) with S = t[w-1]; X = 2^e * odd: wires 0..e-1 zero, wire e one, data e+1..w-2, sign on w-1.
// Forward: X -> X >> e with S on the top e+1 wires, wire 0 = 1 (drop0: wire 0 released, returns true). Inverse: back.
// R1 (`l = Some([b1, s3])`): wires 1 ..= e of X carry L = b1 ^ s3 as well; absorbed at no Toffoli.
//
// S never enters the ring. Ring wires j = w-2-i (i = 0..w-2) are coefficients of c R^j, R = 1+z, c = (1+z^3)^-M, where
// w-1 = 4M + r. Conversions are CNOT only: Pascal (R^j -> z^i), the homogeneous radix split
// P = (1+z^(3H)) L + z^(4 M_L) U down to slots, then 5 CNOT per slot to lanes x[k][j] with
// P = sum_k z^(4k) (1+z^3)^(M-1-k) sum_j x[k][j] s[j], s = (1+z^3, 1+z+z^3, 1+z^2+z^3, 1+z+z^2) = (1+z^3) t[j];
// the top slot k = M holds z^(4M) t[j] mod z^(4M+4) (r wires).
// In lanes the word is, in time order: G(k2), F(k1): x[k][3] ^= h (x[k-1][0..=2]), E(k1+k2), D(k1+k3), C(k3), B(k1+k2+k3),
// A(k2+k3); G E D B are Fredkin layers on lane pairs (0,2) (1,3) (2,3) (0,1), C and A the two sheared layers.
// Why the alignment: the promise's known functionals become the top slot's lane coordinates, so the top gates' reads
// vanish on the data and they go (`gate_rule`, MEASURED by rank at n = 8, 12, 16 over all c, exact by the test):
//   r = 0, 1: every k < M except C[M-1], A[M-1]            7M-3 gates
//   r = 2:    + A[M-1], F'[M], B[M]                        7M     (F'[M] = F[M]+E[M] merged: writes (M,1), no pad)
//   r = 3:    + A[M]                                       7M+1
// Plus one Toffoli F[0] = CCX(k1, S ^ L; lane (0,3)): the only S k1 term the ring cannot read from a gate.
// Forward free gates (known output functional): r = 0 A[M-2] (wire 0's functional = 1), r = 2 B[M].
// r = 1, 3: wire 0's lane is untouched and holds [e == 0]: forward erases it (X-measure, phase quadratic on letters 0..=5,
// so Clifford), inverse writes it with one AND k1 (k2 + k3).
// Toffoli: forward 7M-3, 7M-2, 7M, 7M+2; inverse 7M-2, 7M-1, 7M+1, 7M+3 for r = 0, 1, 2, 3 (w >= 7).
// ======================================================================================================================
use super::builder::Builder;
use crate::circuit::QubitId;

/// Recorded op, flushed to the Builder after CNOT cancellation (slots name classical bits).
#[derive(Clone, Copy, PartialEq, Debug)]
enum AOp {
    Cx(QubitId, QubitId),
    Ccx(QubitId, QubitId, QubitId),
    X(QubitId),
    Hmr(QubitId, usize),
    CzIf(QubitId, QubitId, usize),
    ZIf(QubitId, usize),
    Free(usize),
}
#[derive(Default)]
struct Buf {
    ops: Vec<AOp>,
    nbits: usize,
}
impl Buf {
    fn cx(&mut self, a: QubitId, b: QubitId) {
        // cancel against an earlier identical CNOT across commuting ops
        let mut i = self.ops.len();
        let mut steps = 0;
        while i > 0 && steps < 2000 {
            i -= 1;
            steps += 1;
            let o = self.ops[i];
            if o == AOp::Cx(a, b) {
                self.ops.remove(i);
                return;
            }
            let ok = match o {
                AOp::Cx(c2, t2) => t2 != a && c2 != b,
                AOp::Ccx(x, y, t2) => t2 != a && x != b && y != b,
                AOp::X(q) => q != a,
                AOp::Hmr(q, _) | AOp::ZIf(q, _) => q != a && q != b,
                AOp::CzIf(x, y, _) => x != a && x != b && y != a && y != b,
                AOp::Free(_) => true,
            };
            if !ok { break; }
        }
        self.ops.push(AOp::Cx(a, b));
    }
    fn ccx(&mut self, a: QubitId, b: QubitId, t: QubitId) { self.ops.push(AOp::Ccx(a, b, t)); }
    fn x(&mut self, q: QubitId) { self.ops.push(AOp::X(q)); }
    fn alloc_bit(&mut self) -> usize { self.nbits += 1; self.nbits - 1 }
    fn hmr(&mut self, q: QubitId, m: usize) { self.ops.push(AOp::Hmr(q, m)); }
    fn cz_if(&mut self, a: QubitId, b: QubitId, m: usize) { self.ops.push(AOp::CzIf(a, b, m)); }
    fn z_if(&mut self, a: QubitId, m: usize) { self.ops.push(AOp::ZIf(a, m)); }
    fn free_bit(&mut self, m: usize) { self.ops.push(AOp::Free(m)); }
    fn flush(self, c: &mut Builder) {
        let mut bits = vec![None; self.nbits];
        for o in self.ops {
            match o {
                AOp::Cx(a, b) => c.cx(a, b),
                AOp::Ccx(a, b, t) => c.ccx(a, b, t),
                AOp::X(q) => c.x(q),
                AOp::Hmr(q, m) => { let b = c.alloc_bit(); bits[m] = Some(b); c.hmr(q, b); }
                AOp::CzIf(a, b, m) => c.cz_if(a, b, bits[m].unwrap()),
                AOp::ZIf(a, m) => c.z_if(a, bits[m].unwrap()),
                AOp::Free(m) => c.free_bit(bits[m].unwrap()),
            }
        }
    }
}

const FORMS: [u8; 7] = [2, 1, 3, 5, 4, 7, 6]; // G F E D C B A: control as a mask over (k1, k2, k3)
const B_G: usize = 0;
const B_F: usize = 1;
const B_E: usize = 2;
const B_D: usize = 3;
const B_C: usize = 4;
const B_B: usize = 5;
const B_A: usize = 6;
const B_END: usize = 7;
// fill forms
const F_S: u8 = 0;
const F_SK1: u8 = 1;
const F_ONE: u8 = 2;
const F_K1: u8 = 3;
const F_K2: u8 = 4;
const F_K3: u8 = 5;
const F_L: u8 = 6;
const F_LK1: u8 = 7;

#[derive(Clone, Debug)]
struct RsGate {
    u: Vec<usize>,
    phi: Vec<usize>,
}
#[derive(Clone, Debug)]
struct RsFree {
    block: usize,
    gate: RsGate,
    psi: Vec<usize>,
    value: bool,
}
#[derive(Clone, Debug)]
pub struct RailS6Plan {
    pub w: usize,
    pub big_m: usize,
    pub r: usize,
    conv: Vec<(usize, usize)>,
    /// wire (ring index j after the conversion) of each lane
    lane_wire: Vec<Option<usize>>,
    blocks: Vec<Vec<RsGate>>,
    free_fwd: Vec<RsFree>,
    fills: Vec<(usize, u8, usize)>,
    /// lane untouched by the word that holds [e == 0] on input: forward MBU erase, inverse one AND
    w0: Option<usize>,
    /// the F layer's reads: target lane -> S and L parity added to its control (S k1 and L k1 fills ride on F, slot 0 is
    /// a bare CCX(k1, S ^ L; lane (0, 3)))
    f_reads: Vec<(usize, bool, bool)>,
    /// R1 only: the L fills (boundary, form, lane)
    l_fills: Vec<(usize, u8, usize)>,
}
fn ln(k: usize, j: usize) -> usize { 4 * k + j }
fn xor_set(v: &mut Vec<usize>, a: usize) {
    if let Some(p) = v.iter().position(|&x| x == a) { v.swap_remove(p); } else { v.push(a); }
}
fn base_gate(name: usize, k: usize, top: usize) -> RsGate {
    let mut u = Vec::new();
    let mut phi = Vec::new();
    let pair = |a: usize, b: usize| -> (Vec<usize>, Vec<usize>) { (vec![ln(k, a), ln(k, b)], vec![ln(k, a), ln(k, b)]) };
    match name {
        B_G => (u, phi) = pair(0, 2),
        B_E => (u, phi) = pair(1, 3),
        B_D => (u, phi) = pair(2, 3),
        B_B => (u, phi) = pair(0, 1),
        B_F => { u.push(ln(k, 3)); phi.extend([ln(k - 1, 0), ln(k - 1, 1), ln(k - 1, 2)]); }
        B_C => {
            u.extend([ln(k, 2), ln(k, 3)]);
            if k + 1 <= top { u.push(ln(k + 1, 2)); }
            phi.extend([ln(k, 2), ln(k, 3)]);
            if k > 0 { phi.extend([ln(k - 1, 0), ln(k - 1, 1), ln(k - 1, 3)]); }
        }
        B_A => {
            u.extend([ln(k, 0), ln(k, 1)]);
            if k + 1 <= top { u.push(ln(k + 1, 0)); }
            phi.extend([ln(k, 0), ln(k, 1)]);
            if k > 0 { phi.extend([ln(k - 1, 1), ln(k - 1, 2), ln(k - 1, 3)]); }
        }
        _ => unreachable!(),
    }
    RsGate { u, phi }
}
/// Which gates survive the promise (MEASURED rank drop, checked by the test at every width).
fn gate_rule(big_m: usize, r: usize, name: usize, k: usize) -> bool {
    let m = big_m;
    match name {
        B_G | B_D | B_E => k < m,
        B_F => k >= 1 && (k < m || r >= 2),
        B_C => k + 1 < m,
        B_B => k < m || r >= 2,
        B_A => (k + 1 < m) || (k + 1 == m && r >= 2) || (k == m && r == 3),
        _ => unreachable!(),
    }
}
/// S-part of the fills for the lane basis vector e_j, slot 0 (universal, MEASURED on the unbounded word).
fn base_s(j: usize) -> &'static [(usize, u8, usize, usize)] {
    match j {
        0 => &[(B_G, F_SK1, 0, 3), (B_C, F_S, 0, 2), (B_B, F_S, 0, 2), (B_A, F_S, 0, 0), (B_END, F_S, 0, 0)],
        1 => &[(B_G, F_S, 0, 0), (B_G, F_SK1, 0, 3), (B_G, F_SK1, 1, 3), (B_C, F_S, 0, 3), (B_A, F_S, 0, 0), (B_END, F_S, 0, 3)],
        2 => &[(B_G, F_S, 0, 0), (B_G, F_S, 0, 1), (B_G, F_SK1, 0, 3), (B_C, F_S, 0, 2), (B_B, F_S, 0, 2), (B_A, F_S, 0, 0), (B_END, F_S, 0, 1)],
        _ => &[(B_G, F_S, 0, 1), (B_G, F_SK1, 0, 3), (B_F, F_S, 0, 2), (B_C, F_S, 0, 2), (B_B, F_S, 0, 0), (B_A, F_S, 0, 0), (B_END, F_S, 0, 1)],
    }
}
/// Fills for the lane coordinates `x` (by wire) of an element, slots below M; a k1 fill falling on (M, 3) lands on (M, 1).
fn linear_fills(x: &[bool], big_m: usize, r: usize, lane_wire: &[Option<usize>]) -> std::collections::BTreeMap<(usize, u8, usize), bool> {
    let mut tog: std::collections::BTreeMap<(usize, u8, usize), bool> = Default::default();
    for j in 0..4 {
        for k in 0..big_m {
            if !x[lane_wire[ln(k, j)].unwrap()] { continue; }
            for &(b, f, s, l) in base_s(j) {
                let slot = s + k;
                let target = if slot < big_m {
                    Some(ln(slot, l))
                } else if slot == big_m && f == F_SK1 && l == 3 && r >= 2 {
                    Some(ln(big_m, 1))
                } else {
                    None
                };
                if let Some(t) = target { *tog.entry((b, f, t)).or_insert(false) ^= true; }
            }
        }
    }
    tog
}
fn radix_split(off: usize, m: usize, out: &mut Vec<(usize, usize)>) {
    if m <= 1 { return; }
    let mut h = 1;
    while h * 2 < m { h *= 2; }
    let ml = m - h;
    for i in 3 * h..3 * h + 4 * ml {
        out.push((off + i - 3 * h, off + i));
    }
    radix_split(off, ml, out);
    radix_split(off + 4 * ml, h, out);
}
/// The plan for width w (cached, like `rail8_plan`); None below width 5.
pub fn rail_s6_plan(w: usize) -> Option<RailS6Plan> {
    thread_local! { static C: std::cell::RefCell<std::collections::HashMap<usize, Option<RailS6Plan>>> = std::cell::RefCell::new(std::collections::HashMap::new()); }
    if let Some(p) = C.with(|c| c.borrow().get(&w).cloned()) { return p; }
    let p = rail_s6_plan_new(w);
    C.with(|c| c.borrow_mut().insert(w, p.clone()));
    p
}
fn rail_s6_plan_new(w: usize) -> Option<RailS6Plan> {
    if w < 5 { return None; }
    let j_n = w - 1;
    let big_m = j_n / 4;
    let r = j_n % 4;
    let mut conv = Vec::new();
    // Pascal
    let mut a = 1;
    while a < j_n {
        for j in 0..j_n { if j & a != 0 { conv.push((j, j - a)); } }
        a *= 2;
    }
    let npascal = conv.len();
    // homogeneous radix, then the per-slot adapter
    let mut low = Vec::new();
    radix_split(0, big_m, &mut low);
    for k in 0..big_m {
        let q = |i: usize| 4 * k + i;
        low.extend([(q(3), q(0)), (q(1), q(3)), (q(2), q(3)), (q(0), q(1)), (q(0), q(2))]);
    }
    conv.extend(low.iter().copied());
    // top slot
    if r >= 2 { conv.push((4 * big_m + 1, 4 * big_m)); }
    if r == 3 { conv.push((4 * big_m + 2, 4 * big_m)); }
    let _ = npascal;
    let top = if r == 0 { big_m - 1 } else { big_m };
    let mut lane_wire = vec![None; 4 * (big_m + 1)];
    for k in 0..big_m {
        lane_wire[ln(k, 0)] = Some(4 * k + 3);
        lane_wire[ln(k, 1)] = Some(4 * k + 1);
        lane_wire[ln(k, 2)] = Some(4 * k + 2);
        lane_wire[ln(k, 3)] = Some(4 * k);
    }
    for i in 0..r { lane_wire[ln(big_m, i)] = Some(4 * big_m + i); }
    // gates
    let mut blocks: Vec<Vec<RsGate>> = vec![Vec::new(); 7];
    let mut free_fwd = Vec::new();
    for name in 0..7 {
        for k in 0..=big_m {
            if !gate_rule(big_m, r, name, k) { continue; }
            let mut g = base_gate(name, k, top);
            if name == B_F && k == big_m { g.u = vec![ln(big_m, 1)]; }
            // MBU-free in the forward direction: known output functional
            if r == 0 && name == B_A && k + 2 == big_m {
                free_fwd.push(RsFree { block: name, gate: g, psi: vec![ln(big_m - 1, 0), ln(big_m - 1, 1), ln(big_m - 1, 2)], value: true });
                continue;
            }
            if r == 2 && name == B_B && k == big_m {
                free_fwd.push(RsFree { block: name, gate: g, psi: vec![ln(big_m, 1)], value: false });
                continue;
            }
            blocks[name].push(g);
        }
    }
    // the sign fills: A-linear from the lane coordinates of c, slot M folded by rule
    let mut x = vec![false; 4 * big_m];
    x[0] = true;
    for &(a, b) in &low { if x[a] { x[b] = !x[b]; } }
    let tog = linear_fills(&x, big_m, r, &lane_wire);
    let mut fills: Vec<(usize, u8, usize)> = tog.iter().filter(|(_, &v)| v).map(|(&k, _)| k).collect();
    // the same for L: c_L = c R^(w-2) (Lucas), plus the top repair, all free
    let mut xl: Vec<bool> = (0..4 * big_m).map(|i| (w - 2) & i == i).collect();
    for &(a, b) in &low { if xl[a] { xl[b] = !xl[b]; } }
    let togl = linear_fills(&xl, big_m, 0, &lane_wire);
    let mut l_fills: Vec<(usize, u8, usize)> = togl.iter().filter(|(_, &v)| v).map(|(&(b, f, l), _)| (b, if f == F_S { F_L } else { F_LK1 }, l)).collect();
    {
        let m = big_m;
        let mut add = |b: usize, l: usize| l_fills.push((b, F_L, l));
        if r == 2 {
            add(B_G, ln(m, 0));
            add(B_A, ln(m, 0));
        }
        if r == 3 {
            match m {
                1 => { for &(b, l) in &[(B_E, ln(0, 0)), (B_D, ln(0, 1)), (B_END, ln(0, 0)), (B_END, ln(0, 1))] { add(b, l); } }
                2 => { for &(b, l) in &[(B_E, ln(0, 0)), (B_E, ln(1, 0)), (B_D, ln(0, 1)), (B_D, ln(1, 1)), (B_A, ln(1, 0)), (B_END, ln(0, 0)), (B_END, ln(0, 1)), (B_END, ln(1, 1))] { add(b, l); } }
                _ => {
                    for d in 1..=3 {
                        add(B_E, ln(m - d, 0));
                        add(B_D, ln(m - d, 1));
                    }
                    for d in 1..=2 { add(B_A, ln(m - d, 0)); }
                    for &l in &[ln(m - 3, 0), ln(m - 3, 1), ln(m - 2, 1), ln(m - 1, 1)] { add(B_END, l); }
                }
            }
        }
    }
    // S k1 and L k1 fills are moved onto the F layer (block G does not read lane 3 or the top slot)
    let mut f_reads: Vec<(usize, bool, bool)> = Vec::new();
    let mut note = |t: usize, is_l: bool| {
        if let Some(e) = f_reads.iter_mut().find(|e| e.0 == t) { if is_l { e.2 ^= true } else { e.1 ^= true } }
        else { f_reads.push((t, !is_l, is_l)); }
    };
    // F'_M reads L: MEASURED rule per residue
    if (r == 2 && big_m % 3 != 2) || (r == 3 && big_m % 3 == 0) { note(ln(big_m, 1), true); }
    fills.retain(|f| { if f.1 == F_SK1 { note(f.2, false); false } else { true } });
    l_fills.retain(|f| { if f.1 == F_LK1 { note(f.2, true); false } else { true } });
    let m = big_m;
    let cf: Vec<(usize, u8, usize)> = match r {
        1 => vec![(B_G, F_K3, ln(m - 1, 0)), (B_G, F_K2, ln(m - 1, 2)), (B_G, F_K1, ln(m - 1, 3)), (B_G, F_K2, ln(m - 1, 3)), (B_D, F_K1, ln(m - 1, 1)), (B_D, F_K3, ln(m - 1, 1))],
        2 => vec![(B_G, F_K1, ln(m, 0)), (B_G, F_ONE, ln(m, 1)), (B_G, F_K1, ln(m, 1)), (B_END, F_ONE, ln(m, 1))],
        3 => vec![
            (B_G, F_K3, ln(m - 1, 0)), (B_G, F_K3, ln(m - 1, 1)), (B_G, F_K2, ln(m - 1, 2)), (B_G, F_K3, ln(m - 1, 2)), (B_G, F_K3, ln(m - 1, 3)),
            (B_G, F_K2, ln(m, 0)), (B_G, F_K1, ln(m, 1)), (B_G, F_K2, ln(m, 1)), (B_E, F_K2, ln(m - 1, 0)), (B_E, F_K3, ln(m - 1, 0)), (B_D, F_K3, ln(m - 1, 1)), (B_A, F_K2, ln(m, 0)),
        ],
        _ => vec![],
    };
    fills.extend(cf);
    let w0 = match r { 1 => Some(ln(m, 0)), 3 => Some(ln(m, 2)), _ => None };
    Some(RailS6Plan { w, big_m, r, conv, lane_wire, blocks, free_fwd, fills, w0, f_reads, l_fills })
}
impl RailS6Plan {
    /// Toffoli count (forward, inverse).
    pub fn costs(&self) -> (usize, usize) {
        let g: usize = self.blocks.iter().map(|b| b.len()).sum();
        let f0 = usize::from(self.f_reads.iter().any(|f| f.0 == ln(0, 3) && (f.1 || f.2)));
        let q = usize::from(self.w0.is_some());
        (g + f0, g + self.free_fwd.len() + f0 + q)
    }
}
fn host(k: [QubitId; 3], mask: u8) -> (QubitId, Vec<QubitId>) {
    let idx: Vec<usize> = (0..3).filter(|i| mask >> i & 1 == 1).collect();
    (k[idx[0]], idx[1..].iter().map(|&i| k[i]).collect())
}
fn pivot(g: &RsGate) -> usize {
    g.phi.iter().copied().find(|a| g.u.contains(a)).unwrap_or(g.phi[0])
}
fn emit_block(c: &mut Buf, k: [QubitId; 3], lq: &[Option<QubitId>], mask: u8, gs: &[RsGate], reads: &[(usize, Vec<QubitId>)]) {
    if gs.is_empty() { return; }
    let wire = |a: usize| lq[a].expect("rail_s6: a lane without a wire");
    let (h, others) = host(k, mask);
    for &o in &others { c.cx(o, h); }
    let pv: Vec<usize> = gs.iter().map(pivot).collect();
    for (g, &p) in gs.iter().zip(&pv) {
        for &a in &g.phi { if a != p { c.cx(wire(a), wire(p)); } }
        if let Some((_, rs)) = reads.iter().find(|r| g.u.contains(&r.0)) { for &q in rs { c.cx(q, wire(p)); } }
    }
    for (g, &p) in gs.iter().zip(&pv) {
        let tg: Vec<usize> = g.u.iter().copied().filter(|a| !pv.contains(a)).collect();
        for &t in &tg[1..] { c.cx(wire(tg[0]), wire(t)); }
        c.ccx(h, wire(p), wire(tg[0]));
        for &t in &tg[1..] { c.cx(wire(tg[0]), wire(t)); }
    }
    for (g, &p) in gs.iter().zip(&pv).rev() {
        if let Some((_, rs)) = reads.iter().find(|r| g.u.contains(&r.0)) { for &q in rs.iter().rev() { c.cx(q, wire(p)); } }
        for &a in g.phi.iter().rev() { if a != p { c.cx(wire(a), wire(p)); } }
    }
    for &o in others.iter().rev() { c.cx(o, h); }
}
/// The transvection x += h phi(x) u with psi(x) known after it: CNOTs, one measured wire, a Clifford phase fix.
fn emit_free(c: &mut Buf, k: [QubitId; 3], lq: &[Option<QubitId>], mask: u8, f: &RsFree, known: &[QubitId]) {
    let wire = |a: usize| lq[a].expect("rail_s6: a lane without a wire");
    let a = f.psi.iter().copied().find(|x| f.gate.u.contains(x)).expect("rail_s6: psi(u) = 0");
    for &o in &f.psi { if o != a { c.cx(wire(o), wire(a)); } }
    if f.value { c.x(wire(a)); }
    for &q in known { c.cx(q, wire(a)); }
    for &b in &f.gate.u { if b != a { c.cx(wire(a), wire(b)); } }
    let m = c.alloc_bit();
    c.hmr(wire(a), m);
    if f.value { c.x(wire(a)); }
    for &q in known { c.cx(q, wire(a)); }
    for &o in f.psi.iter().rev() { if o != a { c.cx(wire(o), wire(a)); } }
    let (h, others) = host(k, mask);
    for &o in &others { c.cx(o, h); }
    let p = f.gate.phi[0];
    for &o in &f.gate.phi[1..] { c.cx(wire(o), wire(p)); }
    c.cz_if(h, wire(p), m);
    for &o in f.gate.phi[1..].iter().rev() { c.cx(wire(o), wire(p)); }
    for &o in others.iter().rev() { c.cx(o, h); }
    c.free_bit(m);
}
/// Forward: X on t -> X >> e, wire 0 = 1, or released when `drop0` (returns true). Inverse: back to X. e = k1 + 2 k2 + 4 k3 <= 5.
/// `l = Some([b1, s3])`: R1, the input X^ has wires 1 ..= e XORed with L = b1 ^ s3 (live on both sides); wire 0 untouched.
pub fn rail_s6_barrel_g(b0: &mut Builder, k: [QubitId; 3], t: &[QubitId], l: Option<[QubitId; 2]>, inverse: bool, drop0: bool) -> bool {
    let mut buf = Buf::default();
    let c = &mut buf;
    let w = t.len();
    let pl = rail_s6_plan(w).unwrap_or_else(|| panic!("rail_s6: no plan at w = {w}"));
    let s = t[w - 1];
    let q: Vec<QubitId> = (0..w - 1).map(|j| t[w - 2 - j]).collect();
    let lq: Vec<Option<QubitId>> = pl.lane_wire.iter().map(|x| x.map(|j| q[j])).collect();
    let fill = |c: &mut Buf, b: usize| {
        for &(_, f, lane) in pl.fills.iter().filter(|x| x.0 == b) {
            let tq = lq[lane].unwrap();
            match f {
                F_S => c.cx(s, tq),
                F_ONE => c.x(tq),
                F_K1 => c.cx(k[0], tq),
                F_K2 => c.cx(k[1], tq),
                _ => c.cx(k[2], tq),
            }
        }
        if let Some(ll) = l {
            for &(_, _, lane) in pl.l_fills.iter().filter(|x| x.0 == b) {
                let tq = lq[lane].unwrap();
                c.cx(ll[0], tq);
                c.cx(ll[1], tq);
            }
        }
    };
    // the F layer's reads; slot 0 has no read of its own
    let mut reads: Vec<(usize, Vec<QubitId>)> = Vec::new();
    for &(lane, rs, rl) in &pl.f_reads {
        if lane == ln(0, 3) { continue; }
        let mut v = Vec::new();
        if rs { v.push(s); }
        if rl { if let Some(ll) = l { v.extend(ll); } }
        if !v.is_empty() { reads.push((lane, v)); }
    }
    let f0 = |c: &mut Buf| {
        let e = pl.f_reads.iter().find(|f| f.0 == ln(0, 3));
        let (rs, rl) = e.map_or((false, false), |f| (f.1, f.2 && l.is_some()));
        let tq = lq[ln(0, 3)].unwrap();
        if !rs && !rl { return; }
        // CCX(k1, S ^ L; lane (0, 3)): S is only read by this op here, so it hosts the parity
        if rl { let ll = l.unwrap(); c.cx(ll[0], s); c.cx(ll[1], s); }
        if rs {
            c.ccx(k[0], s, tq);
        } else {
            c.cx(s, tq);
            c.ccx(k[0], s, tq);
            c.cx(s, tq);
        }
        if rl { let ll = l.unwrap(); c.cx(ll[1], s); c.cx(ll[0], s); }
    };
    let block = |c: &mut Buf, b: usize, gs: &[RsGate]| {
        let rr: &[(usize, Vec<QubitId>)] = if b == B_F { &reads } else { &[] };
        emit_block(c, k, &lq, FORMS[b], gs, rr);
    };
    for &(a, b) in &pl.conv { c.cx(q[a], q[b]); }
    let kl_keep = RS6_KEEP_KL.with(|x| x.get());
    let tau = if !inverse && kl_keep != usize::MAX { (w - 1).saturating_sub(kl_keep) } else { 0 };
    if tau > 0 {
        let kp = keep_plan_cached(w, tau, l.is_some());
        for b in 0..7 {
            fill(c, b);
            if b == B_F { f0(c); }
            block(c, b, &kp.kept[b]);
            for f in kp.frees.iter().filter(|f| f.block == b) { emit_keep_free(c, k, &lq, s, l, FORMS[b], f); }
        }
        fill(c, B_END);
        if let Some(lane) = pl.w0 {
            let a = lq[lane].unwrap();
            c.x(a);
            let m = c.alloc_bit();
            c.hmr(a, m);
            c.z_if(k[0], m);
            c.z_if(k[1], m);
            c.z_if(k[2], m);
            c.cx(k[2], k[1]);
            c.cz_if(k[0], k[1], m);
            c.cx(k[2], k[1]);
            c.free_bit(m);
            c.x(a);
        }
    } else if !inverse {
        for b in 0..7 {
            fill(c, b);
            if b == B_F { f0(c); }
            block(c, b, &pl.blocks[b]);
            for f in pl.free_fwd.iter().filter(|f| f.block == b) {
                // the known value counts the next boundary's fills on psi: not applied yet here
                let mut known: Vec<QubitId> = pl.fills.iter().filter(|x| x.0 == b + 1 && f.psi.contains(&x.2)).map(|x| match x.1 {
                    F_S => s,
                    F_K1 => k[0],
                    F_K2 => k[1],
                    F_K3 => k[2],
                    _ => panic!("rail_s6: a constant fill on psi"),
                }).collect();
                if let Some(ll) = l {
                    for x in pl.l_fills.iter().filter(|x| x.0 == b + 1 && f.psi.contains(&x.2)) { let _ = x; known.extend(ll); }
                }
                emit_free(c, k, &lq, FORMS[b], f, &known);
            }
        }
        fill(c, B_END);
        if let Some(lane) = pl.w0 {
            // this lane holds [e == 0]: erase it, the phase is quadratic on the letters 0..=5
            let a = lq[lane].unwrap();
            c.x(a);
            let m = c.alloc_bit();
            c.hmr(a, m);
            c.z_if(k[0], m);
            c.z_if(k[1], m);
            c.z_if(k[2], m);
            c.cx(k[2], k[1]);
            c.cz_if(k[0], k[1], m);
            c.cx(k[2], k[1]);
            c.free_bit(m);
            c.x(a);
        }
    } else {
        if let Some(lane) = pl.w0 {
            // this lane holds 1: write [e == 0] = 1 + k1 + k2 + k3 + k1 (k2 + k3), one AND
            let a = lq[lane].unwrap();
            c.x(a);
            c.cx(k[0], a);
            c.cx(k[1], a);
            c.cx(k[2], a);
            c.cx(k[2], k[1]);
            c.ccx(k[0], k[1], a);
            c.cx(k[2], k[1]);
            c.x(a);
        }
        fill(c, B_END);
        for b in (0..7).rev() {
            for f in pl.free_fwd.iter().filter(|f| f.block == b) {
                block(c, b, std::slice::from_ref(&f.gate));
            }
            block(c, b, &pl.blocks[b]);
            if b == B_F { f0(c); }
            fill(c, b);
        }
    }
    for &(a, b) in pl.conv.iter().rev() { c.cx(q[a], q[b]); }
    if drop0 && !inverse { c.x(t[0]); }
    buf.flush(b0);
    if drop0 && !inverse {
        b0.release_clean(t[0]);
        return true;
    }
    false
}
pub fn rail_s6_barrel(c: &mut Builder, k: [QubitId; 3], t: &[QubitId], inverse: bool, drop0: bool) -> bool {
    rail_s6_barrel_g(c, k, t, None, inverse, drop0)
}

// ======================================================================================================================
// laneG: DROP_KEEP on the S6 word. The caller cuts the output's top wires at the next tick, so t[w-1-tau ..= w-2] = S on
// every shot that fits; as covectors on the lanes these are known output functionals, and together with whatever else
// the promise fixes, each block's forward gates that a known functional separates are MBU-free. Everything is derived
// from the plan by linear algebra at the first call: run the word symbolically for each letter, solve for the covectors
// whose value carries no data and is affine in (1, k1, k2, k3, S, L), then rank them against the block's targets.
// ======================================================================================================================
thread_local! {
    /// The caller's retained length after the barrel (index into the rail once wire 0 is gone), usize::MAX = off.
    pub static RS6_KEEP_KL: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };
}
#[derive(Clone, Copy, PartialEq, Eq, Default)]
struct Vb([u64; 5]);
impl Vb {
    fn x(&mut self, o: &Vb) { for i in 0..5 { self.0[i] ^= o.0[i]; } }
    fn flip(&mut self, i: usize) { self.0[i / 64] ^= 1 << (i % 64); }
    fn get(&self, i: usize) -> bool { self.0[i / 64] >> (i % 64) & 1 == 1 }
}
#[derive(Clone, Debug)]
struct KeepFree { block: usize, gate: RsGate, psi: Vec<usize>, c0: bool, ck: [bool; 3], cs: bool, cl: bool }
#[derive(Clone, Debug)]
struct KeepPlan { kept: Vec<Vec<RsGate>>, frees: Vec<KeepFree> }
impl RailS6Plan {
    fn fill_vb(&self, st: &mut [Vb], b: usize, e: usize, vs: usize, vl: usize, vo: usize, r1: bool) {
        for &(_, f, lane) in self.fills.iter().filter(|x| x.0 == b) {
            let j = self.lane_wire[lane].unwrap();
            match f {
                F_S => st[j].flip(vs),
                F_ONE => st[j].flip(vo),
                F_K1 => if e & 1 == 1 { st[j].flip(vo) },
                F_K2 => if e >> 1 & 1 == 1 { st[j].flip(vo) },
                _ => if e >> 2 & 1 == 1 { st[j].flip(vo) },
            }
        }
        if r1 { for &(_, _, lane) in self.l_fills.iter().filter(|x| x.0 == b) { st[self.lane_wire[lane].unwrap()].flip(vl); } }
    }
    fn gates_vb(&self, st: &mut [Vb], gs: &[RsGate], b: usize, e: usize, vs: usize, vl: usize, r1: bool) {
        if (FORMS[b] as usize & e).count_ones() % 2 == 0 { return; }
        let mut add: Vec<(usize, Vb)> = Vec::new();
        for g in gs {
            let mut p = Vb::default();
            for &a in &g.phi { p.x(&st[self.lane_wire[a].unwrap()]); }
            if b == B_F {
                if let Some(f) = self.f_reads.iter().find(|f| g.u.contains(&f.0)) {
                    if f.1 { p.flip(vs); }
                    if f.2 && r1 { p.flip(vl); }
                }
            }
            for &a in &g.u { add.push((self.lane_wire[a].unwrap(), p)); }
        }
        for (j, p) in add { st[j].x(&p); }
    }
    /// The plan for `tau` known top output wires; `r1` = the word also runs the L fills.
    fn keep_plan(&self, tau: usize, r1: bool) -> KeepPlan {
        let nj = self.w - 1;
        let (vs, vl, vo) = (nj, nj + 1, nj + 2);
        // the state for each letter, after the conversion
        let mut st: Vec<Vec<Vb>> = Vec::new();
        for e in 0..6usize {
            let mut q = vec![Vb::default(); nj];
            for j in 0..nj {
                let i = nj - 1 - j; // t wire
                if e >= nj { continue; }
                if i > e { if j + e < tau { q[j].flip(vs); } else { q[j].flip(j); } }
                if i == e { q[j].flip(vo); }
                if r1 && i >= 1 && i <= e { q[j].flip(vl); }
            }
            for &(a, b) in &self.conv { let qa = q[a]; q[b].x(&qa); }
            st.push(q);
        }
        let mut kept: Vec<Vec<RsGate>> = self.blocks.clone();
        for f in &self.free_fwd { kept[f.block].push(f.gate.clone()); }
        // the F layer's slot 0 read
        let f0 = self.f_reads.iter().find(|f| f.0 == ln(0, 3)).copied();
        let mut frees = Vec::new();
        for b in 0..7 {
            let all = kept[b].clone();
            for e in 0..6 {
                self.fill_vb(&mut st[e], b, e, vs, vl, vo, r1);
                if b == B_F && e & 1 == 1 {
                    if let Some(f) = f0 {
                        let j = self.lane_wire[f.0].unwrap();
                        if f.1 { st[e][j].flip(vs); }
                        if f.2 && r1 { st[e][j].flip(vl); }
                    }
                }
                self.gates_vb(&mut st[e], &all, b, e, vs, vl, r1);
            }
            if b == B_F { continue; }
            // covectors psi (columns = wires) with no data, S and L independent of the letter, constant affine in (k1, k2, k3)
            let mut rows: Vec<Vec<u64>> = Vec::new();
            let word = |r: &[Vb], f: &dyn Fn(&Vb) -> bool| -> Vec<u64> {
                let mut v = vec![0u64; nj / 64 + 1];
                for (j, x) in r.iter().enumerate() { if f(x) { v[j / 64] |= 1 << (j % 64); } }
                v
            };
            for e in 0..6 {
                for d in 0..nj { rows.push(word(&st[e], &|x: &Vb| x.get(d))); }
                if e > 0 {
                    rows.push(word(&st[e], &|x: &Vb| x.get(vs)).iter().zip(word(&st[0], &|x: &Vb| x.get(vs))).map(|(a, b)| a ^ b).collect());
                    rows.push(word(&st[e], &|x: &Vb| x.get(vl)).iter().zip(word(&st[0], &|x: &Vb| x.get(vl))).map(|(a, b)| a ^ b).collect());
                }
            }
            for set in [[0usize, 1, 2, 3], [0, 1, 4, 5]] {
                let mut v = vec![0u64; nj / 64 + 1];
                for &e in &set { let w = word(&st[e], &|x: &Vb| x.get(vo)); for i in 0..v.len() { v[i] ^= w[i]; } }
                rows.push(v);
            }
            let basis = nullspace(&rows, nj);
            // rank against the block's targets; each pivot gate gets a covector that vanishes on the other pivots' targets
            let u_of: Vec<Vec<usize>> = all.iter().map(|g| g.u.iter().map(|&a| self.lane_wire[a].unwrap()).collect()).collect();
            let dot = |psi: &[u64], u: &[usize]| -> bool { u.iter().filter(|&&j| psi[j / 64] >> (j % 64) & 1 == 1).count() % 2 == 1 };
            let mut piv: Vec<(usize, Vec<u64>)> = Vec::new();
            let mut pool = basis;
            for (gi, u) in u_of.iter().enumerate() {
                let Some(p) = pool.iter().position(|v| dot(v, u)) else { continue };
                let v = pool.swap_remove(p);
                for o in pool.iter_mut() { if dot(o, u) { for i in 0..o.len() { o[i] ^= v[i]; } } }
                for (_, o) in piv.iter_mut() { if dot(o, u) { for i in 0..o.len() { o[i] ^= v[i]; } } }
                piv.push((gi, v));
            }
            let mut is_free = vec![false; all.len()];
            for (gi, v) in &piv {
                is_free[*gi] = true;
                let psi_w: Vec<usize> = (0..nj).filter(|j| v[j / 64] >> (j % 64) & 1 == 1).collect();
                let val = |e: usize, var: usize| -> bool { psi_w.iter().filter(|&&j| st[e][j].get(var)).count() % 2 == 1 };
                let c0 = val(0, vo);
                let ck = [val(1, vo) ^ c0, val(2, vo) ^ c0, val(4, vo) ^ c0];
                for e in 0..6 {
                    debug_assert!(val(e, vo) == c0 ^ (e & 1 == 1 && ck[0]) ^ (e >> 1 & 1 == 1 && ck[1]) ^ (e >> 2 & 1 == 1 && ck[2]));
                }
                let lane_of = |j: usize| self.lane_wire.iter().position(|x| *x == Some(j)).unwrap();
                frees.push(KeepFree { block: b, gate: all[*gi].clone(), psi: psi_w.iter().map(|&j| lane_of(j)).collect(), c0, ck, cs: val(0, vs), cl: val(0, vl) });
            }
            kept[b] = all.iter().zip(&is_free).filter(|(_, &f)| !f).map(|(g, _)| g.clone()).collect();
        }
        KeepPlan { kept, frees }
    }
}
/// A basis of the covectors (n columns) annihilating every row.
fn nullspace(rows: &[Vec<u64>], n: usize) -> Vec<Vec<u64>> {
    let nw = n / 64 + 1;
    let mut m: Vec<Vec<u64>> = Vec::new();
    let mut pivc: Vec<usize> = Vec::new();
    for r in rows {
        let mut v = r.clone();
        for (b, &c) in m.iter().zip(&pivc) { if v[c / 64] >> (c % 64) & 1 == 1 { for i in 0..nw { v[i] ^= b[i]; } } }
        if let Some(c) = (0..n).find(|c| v[c / 64] >> (c % 64) & 1 == 1) {
            for b in m.iter_mut() { if b[c / 64] >> (c % 64) & 1 == 1 { for i in 0..nw { b[i] ^= v[i]; } } }
            m.push(v);
            pivc.push(c);
        }
    }
    let mut out = Vec::new();
    for f in 0..n {
        if pivc.contains(&f) { continue; }
        let mut x = vec![0u64; nw];
        x[f / 64] |= 1 << (f % 64);
        for (b, &c) in m.iter().zip(&pivc) { if b[f / 64] >> (f % 64) & 1 == 1 { x[c / 64] |= 1 << (c % 64); } }
        out.push(x);
    }
    out
}
fn keep_plan_cached(w: usize, tau: usize, r1: bool) -> std::rc::Rc<KeepPlan> {
    thread_local! { static C: std::cell::RefCell<std::collections::HashMap<(usize, usize, bool), std::rc::Rc<KeepPlan>>> = std::cell::RefCell::new(std::collections::HashMap::new()); }
    if let Some(p) = C.with(|c| c.borrow().get(&(w, tau, r1)).cloned()) { return p; }
    let p = std::rc::Rc::new(rail_s6_plan(w).unwrap().keep_plan(tau, r1));
    C.with(|c| c.borrow_mut().insert((w, tau, r1), p.clone()));
    p
}
/// Forward Toffoli count with `tau` known top wires (harness and pricing).
pub fn rail_s6_keep_cost(w: usize, tau: usize, r1: bool) -> usize {
    let pl = rail_s6_plan(w).unwrap();
    let kp = keep_plan_cached(w, tau, r1);
    let g: usize = kp.kept.iter().map(|b| b.len()).sum();
    let f0 = usize::from(pl.f_reads.iter().any(|f| f.0 == ln(0, 3) && (f.1 || f.2)));
    g + f0
}
fn emit_keep_free(c: &mut Buf, k: [QubitId; 3], lq: &[Option<QubitId>], s: QubitId, l: Option<[QubitId; 2]>, mask: u8, f: &KeepFree) {
    let mut known: Vec<QubitId> = Vec::new();
    for i in 0..3 { if f.ck[i] { known.push(k[i]); } }
    if f.cs { known.push(s); }
    if f.cl { if let Some(ll) = l { known.extend(ll); } }
    let fr = RsFree { block: f.block, gate: f.gate.clone(), psi: f.psi.clone(), value: f.c0 };
    emit_free(c, k, lq, mask, &fr, &known);
}

// ======================================================================================================================
// laneW: the true rotation on 4M wires. Rotation by e on 2^m wires is multiplication by (1+z)^e in F2[z]/z^(2^m), the
// ring of the rail above with n = 2^m, so the same conversions and lanes apply with no promise: every gate, no fills, no
// S. M = 64: G, E, D, C, B, A 64 each and F 63 = 447 Toffoli, about 5.6k CNOTs. Exact on e = 0 ..= 5, all data.
// ======================================================================================================================
struct RotS6 { conv: Vec<(usize, usize)>, lane_wire: Vec<Option<usize>>, blocks: Vec<Vec<RsGate>> }
fn rot_s6_plan(n: usize) -> std::rc::Rc<RotS6> {
    thread_local! { static C: std::cell::RefCell<std::collections::HashMap<usize, std::rc::Rc<RotS6>>> = std::cell::RefCell::new(std::collections::HashMap::new()); }
    if let Some(p) = C.with(|c| c.borrow().get(&n).cloned()) { return p; }
    assert!(n % 4 == 0 && n >= 8, "rot_s6: n = {n}");
    let big_m = n / 4;
    let mut conv = Vec::new();
    let mut a = 1;
    while a < n {
        for j in 0..n { if j & a != 0 { conv.push((j, j - a)); } }
        a *= 2;
    }
    let mut low = Vec::new();
    radix_split(0, big_m, &mut low);
    for k in 0..big_m {
        let q = |i: usize| 4 * k + i;
        low.extend([(q(3), q(0)), (q(1), q(3)), (q(2), q(3)), (q(0), q(1)), (q(0), q(2))]);
    }
    conv.extend(low.iter().copied());
    let mut lane_wire = vec![None; 4 * (big_m + 1)];
    for k in 0..big_m {
        lane_wire[ln(k, 0)] = Some(4 * k + 3);
        lane_wire[ln(k, 1)] = Some(4 * k + 1);
        lane_wire[ln(k, 2)] = Some(4 * k + 2);
        lane_wire[ln(k, 3)] = Some(4 * k);
    }
    let mut blocks: Vec<Vec<RsGate>> = vec![Vec::new(); 7];
    for name in 0..7 {
        for k in 0..big_m {
            if name == B_F && k == 0 { continue; }
            blocks[name].push(base_gate(name, k, big_m - 1));
        }
    }
    let p = std::rc::Rc::new(RotS6 { conv, lane_wire, blocks });
    C.with(|c| c.borrow_mut().insert(n, p.clone()));
    p
}
/// t rotated down by e = k1 + 2 k2 + 4 k3 <= 5 (wire i -> wire i - e mod n), inverse back; no ancilla, 447 Toffoli at n = 256.
pub fn rot_s6(b0: &mut Builder, k: [QubitId; 3], t: &[QubitId], inverse: bool) {
    let n = t.len();
    let pl = rot_s6_plan(n);
    let mut buf = Buf::default();
    let c = &mut buf;
    let q: Vec<QubitId> = (0..n).map(|j| t[n - 1 - j]).collect();
    let lq: Vec<Option<QubitId>> = pl.lane_wire.iter().map(|x| x.map(|j| q[j])).collect();
    for &(a, b) in &pl.conv { c.cx(q[a], q[b]); }
    if !inverse {
        for b in 0..7 { emit_block(c, k, &lq, FORMS[b], &pl.blocks[b], &[]); }
    } else {
        for b in (0..7).rev() { emit_block(c, k, &lq, FORMS[b], &pl.blocks[b], &[]); }
    }
    for &(a, b) in pl.conv.iter().rev() { c.cx(q[a], q[b]); }
    buf.flush(b0);
}
