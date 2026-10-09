//! froghop-double: bit-serial 4-phase extended Euclid on exact-packed registers (W = 258), two hops per Euclid step,
//! with lean bookkeeping (quotient bits in V's gap, 6-bit offset boundary, 3-bit phase code).
//!
//! D and V each hold a value (LSB at lane 0, growing up) and a cofactor (LSB at lane W-1, growing down). V is
//! rotated up by pi relative to D. One shared boundary register b (bits of the current dividend during AL, of the
//! divisor afterwards; stored as b - 1 in 8 bits) gives every per-shot mask; ladders mask only inside classical
//! per-slot windows.
//!
//! Slot order: S0 frozen counter; S2 value ladder P1 (mask [pi <= lane <= b + [DV] pi]); S3 turn: probe, b update,
//! probe erase; S4 DV push / DV0 bit 0, AL->DV and DV0->CO moves; S1 CO pop (shots that were CO at slot start);
//! S5 RT0 swap, RT0->AL / DONE; S6 cofactor ladder P2 (COEF, mask lane >= b + pi); S7 CO->RT; S8 discriminator
//! ladder P3; S9 rotation and pi update.
//!
//! Scratch: one pool of POOL_D qubits, all |0> between slots, handed out per step (`Pl`).

use super::arith::{and_lits, cswap_regs, rot2_up, ttk_add};
use super::builder::B;
use super::mask::{mc_xor, mcx_dirty, mdown, mup, onehot_scan, top_carry, Lad, Mscr, Src};
use crate::circuit::{QubitId, NO_QUBIT};

pub const WD: usize = 258;
pub const PIB: usize = 5;
pub const DEPB: usize = 5;
/// b (1..=256) is stored as the offset u = (b - 1) - base(sigma) mod 2^BB, base a per-slot classical constant
pub const BB: usize = 6;
pub const CNTB: usize = 8;
pub const POOL_D: usize = 5;
thread_local! { pub static STEP: std::cell::Cell<&'static str> = std::cell::Cell::new(""); }
/// P3 compares only lanes within this depth below the lowest shot boundary of the slot
pub const P3DEPTH: usize = 20;

#[derive(Clone)]
pub struct LayDouble {
    pub w: usize,
    pub s: usize,
    /// per slot: Lv jw p1lo lc p2hi pb0 pb1 pe0 pe1 sc0 sc1
    pub rows: Vec<[usize; 11]>,
    /// per slot: base of the offset boundary register (non-increasing, 0 from before the first DONE)
    pub base: Vec<usize>,
    pub smax: usize,
}

impl LayDouble {
    pub fn from_text(txt: &str, smax: usize) -> LayDouble {
        let mut lines = txt.lines();
        let hdr: Vec<usize> = lines.next().unwrap().split_whitespace().map(|t| t.parse().unwrap()).collect();
        let mut base = vec![];
        let rows: Vec<[usize; 11]> = lines
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                let v: Vec<usize> = l.split_whitespace().map(|t| t.parse().unwrap()).collect();
                let (s0, s1) = if v.len() >= 11 { (v[9], v[10]) } else { (0, hdr[0]) };
                base.push(if v.len() >= 12 { v[11] } else { 0 });
                [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], s0, s1]
            })
            .collect();
        assert_eq!(rows.len(), hdr[1]);
        LayDouble { w: hdr[0], s: hdr[1], rows, base, smax }
    }
}

/// Scratch hand-out for one slot (LIFO). Every qubit goes back |0>. `dirty`: borrowed qubits (any state, restored)
/// for multi-controlled gates when the pool is short.
struct Pl {
    free: Vec<QubitId>,
    pub low: usize,
    dirty: Vec<QubitId>,
}

impl Pl {
    fn new(pool: &[QubitId], dirty: &[QubitId]) -> Pl {
        let mut free = pool.to_vec();
        free.reverse();
        let low = free.len();
        Pl { free, low, dirty: dirty.to_vec() }
    }
    fn get(&mut self) -> QubitId {
        let q = match self.free.pop() { Some(q) => q, None => panic!("froghop-double scratch pool exhausted in {}", STEP.with(|c| c.get())) };
        self.low = self.low.min(self.free.len());
        q
    }
    fn get_n(&mut self, n: usize) -> Vec<QubitId> {
        (0..n).map(|_| self.get()).collect()
    }
    fn put(&mut self, q: QubitId) {
        debug_assert!(!self.free.contains(&q));
        self.free.push(q);
    }
    fn put_n(&mut self, qs: &[QubitId]) {
        for &q in qs.iter().rev() {
            self.put(q);
        }
    }
    /// claim specific (currently free) qubits again
    fn take(&mut self, qs: &[QubitId]) {
        for q in qs {
            let i = self.free.iter().position(|x| x == q).expect("take of a busy scratch qubit");
            self.free.remove(i);
        }
        self.low = self.low.min(self.free.len());
    }
}

/// target ^= AND of literals, chained through as many free pool qubits as help, the rest as a dirty-borrowed MCX
fn xand(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], target: QubitId) {
    let k = pl.free.len().min(lits.len().saturating_sub(2));
    let temps = pl.get_n(k);
    let dirty = std::mem::take(&mut pl.dirty);
    mc_xor(b, lits, target, &temps, &dirty);
    pl.dirty = dirty;
    pl.put_n(&temps);
}

/// out ^= AND of literals (qubit, negated?), transient chain from the pool (n >= 2). `undo`: measurement-uncompute
/// (out must hold exactly that AND). Falls back to `xand` when the pool cannot hold the chain.
fn and_into(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], out: QubitId, undo: bool) {
    let n = lits.len();
    assert!(n >= 2);
    let (q, neg) = lits[n - 1];
    if n == 2 {
        let (p, ng) = lits[0];
        if ng {
            b.x(p);
        }
        if neg {
            b.x(q);
        }
        if undo { b.and_u(p, q, out) } else { b.and_c(p, q, out) }
        if neg {
            b.x(q);
        }
        if ng {
            b.x(p);
        }
        return;
    }
    if pl.free.len() < n - 2 {
        xand(b, pl, lits, out);
        return;
    }
    let m = pl.get();
    let anc = pl.get_n(n.saturating_sub(3));
    let r = and_lits(b, &lits[..n - 1], m, &anc);
    b.play(&r, false);
    if neg {
        b.x(q);
    }
    if undo { b.and_u(m, q, out) } else { b.and_c(m, q, out) }
    if neg {
        b.x(q);
    }
    b.play(&r, true);
    pl.put_n(&anc);
    pl.put(m);
}

/// bits += ctrl with the pool's free qubits as carry chain (n - 2 suffice: the top carry is a Toffoli), any top bits
/// beyond the chain as dirty-borrowed MCX
fn incp(b: &mut B, pl: &mut Pl, ctrl: QubitId, bits: &[QubitId]) {
    let n = bits.len();
    if n == 0 {
        return;
    }
    let l = pl.free.len().min(n.saturating_sub(2));
    let anc = pl.get_n(l);
    let mut prev = ctrl;
    for i in 1..=l {
        b.and_c(prev, bits[i - 1], anc[i - 1]);
        prev = anc[i - 1];
    }
    for i in (l + 1..n).rev() {
        let mut lits = vec![(prev, false)];
        lits.extend(bits[l..i].iter().map(|&q| (q, false)));
        mc_xor(b, &lits, bits[i], &[], &pl.dirty);
    }
    for i in (1..=l).rev() {
        b.cx(anc[i - 1], bits[i]);
        let p = if i == 1 { ctrl } else { anc[i - 2] };
        b.and_u(p, bits[i - 1], anc[i - 1]);
    }
    b.cx(ctrl, bits[0]);
    pl.put_n(&anc);
}

fn decp(b: &mut B, pl: &mut Pl, ctrl: QubitId, bits: &[QubitId]) {
    for &q in bits {
        b.x(q);
    }
    incp(b, pl, ctrl, bits);
    for &q in bits {
        b.x(q);
    }
}

#[derive(Clone, Copy)]
enum GC {
    Lit(usize),
    Q(QubitId),
}

struct GLevel {
    q: QubitId,
    xor: bool,
    a: GC,
    b: GC,
    /// deepest literal index the level depends on
    d: usize,
}

/// For j in [lo, hi): per(b, j, o) with o = g & [u == j + off] in a clean qubit. Top decoder levels (ANDs of u's
/// top bits) are XOR-held in `cc`, qubits known |0> whenever g = 1 (garbage elsewhere, restored); g enters the first
/// clean level, so every clean level is exact for every shot.
fn gated_scan(b: &mut B, pl: &mut Pl, u: &[QubitId], g: QubitId, cc: &[QubitId], lo: usize, hi: usize, off: isize,
              mut per: impl FnMut(&mut B, usize, QubitId)) {
    let n = u.len();
    let avail = pl.free.len();
    let kc = if n <= avail { 0 } else { n - avail };
    assert!(kc <= cc.len() && kc < n, "gated_scan: pool too small");
    let clean = pl.get_n(n - kc);
    let mut lv: Vec<GLevel> = vec![];
    if kc == 0 {
        lv.push(GLevel { q: clean[0], xor: false, a: GC::Q(g), b: GC::Lit(0), d: 0 });
        for k in 1..n {
            lv.push(GLevel { q: clean[k], xor: false, a: GC::Q(clean[k - 1]), b: GC::Lit(k), d: k });
        }
    } else {
        lv.push(GLevel { q: cc[0], xor: true, a: GC::Lit(0), b: GC::Lit(1), d: 1 });
        for c in 1..kc {
            lv.push(GLevel { q: cc[c], xor: true, a: GC::Q(cc[c - 1]), b: GC::Lit(c + 1), d: c + 1 });
        }
        lv.push(GLevel { q: clean[0], xor: false, a: GC::Q(cc[kc - 1]), b: GC::Q(g), d: kc });
        for k in 1..n - kc {
            lv.push(GLevel { q: clean[k], xor: false, a: GC::Q(clean[k - 1]), b: GC::Lit(kc + k), d: kc + k });
        }
    }
    let apply = |b: &mut B, l: &GLevel, j: usize, undo: bool| {
        let get = |c: GC| match c {
            GC::Lit(i) => (u[n - 1 - i], (j >> (n - 1 - i)) & 1 == 0),
            GC::Q(q) => (q, false),
        };
        let (qa, na) = get(l.a);
        let (qb, nb) = get(l.b);
        if na {
            b.x(qa);
        }
        if nb {
            b.x(qb);
        }
        if l.xor {
            b.ccx(qa, qb, l.q)
        } else if undo {
            b.and_u(qa, qb, l.q)
        } else {
            b.and_c(qa, qb, l.q)
        }
        if nb {
            b.x(qb);
        }
        if na {
            b.x(qa);
        }
    };
    let mut cur: Option<usize> = None;
    for j in lo..hi {
        let val = j as isize + off;
        if val < 0 || val as usize >= (1usize << n) {
            continue;
        }
        let val = val as usize;
        let first = match cur {
            None => 0,
            Some(c) if c == val => n,
            Some(c) => n - 1 - (usize::BITS - 1 - (c ^ val).leading_zeros()) as usize,
        };
        if let Some(c) = cur {
            for l in lv.iter().rev() {
                if l.d >= first {
                    apply(b, l, c, true);
                }
            }
        }
        for l in lv.iter() {
            if cur.is_none() || l.d >= first {
                apply(b, l, val, false);
            }
        }
        cur = Some(val);
        per(b, j, lv.last().unwrap().q);
    }
    if let Some(c) = cur {
        for l in lv.iter().rev() {
            apply(b, l, c, true);
        }
    }
    pl.put_n(&clean);
}

/// bits += AND(lits) (mod 2^n): bit i flips where lits and bits 0..i are all 1, top bit first
fn inc_lits(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], bits: &[QubitId]) {
    for i in (0..bits.len()).rev() {
        let mut l = lits.to_vec();
        l.extend(bits[..i].iter().map(|&q| (q, false)));
        xand(b, pl, &l, bits[i]);
    }
}

/// bits -= AND(lits) (mod 2^n)
fn dec_lits(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], bits: &[QubitId]) {
    for &q in bits {
        b.x(q);
    }
    inc_lits(b, pl, lits, bits);
    for &q in bits {
        b.x(q);
    }
}

/// bits += 1 (unconditional): the upper lanes take bit 0 as their carry, then bit 0 flips
fn inc_uncond(b: &mut B, pl: &mut Pl, bits: &[QubitId]) {
    if bits.len() > 1 {
        incp(b, pl, bits[0], &bits[1..]);
    }
    b.x(bits[0]);
}

/// target ^= CO & !A & !(B & e) with A = AND(negpi) (pi == 0), B = AND(negdep) (depth == 0), e an optional extra
/// literal: the XOR of the four AND terms CO, CO A, CO B e, CO A B e
fn po_terms(b: &mut B, pl: &mut Pl, target: QubitId, co: &[(QubitId, bool)], negpi: &[(QubitId, bool)],
            negdep: &[(QubitId, bool)], e: Option<(QubitId, bool)>) {
    let mut ca = co.to_vec();
    ca.extend_from_slice(negpi);
    let mut cb = co.to_vec();
    cb.extend_from_slice(negdep);
    if let Some(x) = e {
        cb.push(x);
    }
    let mut cab = ca.clone();
    cab.extend_from_slice(&cb[co.len()..]);
    for t in [co.to_vec(), ca, cb, cab] {
        xand(b, pl, &t, target);
    }
}

/// For j in [lo, hi): per(b, j, c, g) where c & g = g & [u == j + off]. Every decoder level is XOR-held in `cc`
/// (len >= u.len() - 1), qubits known |0> whenever g = 1 (garbage elsewhere, restored), so c = [u == j + off]
/// exactly when g = 1; the caller folds g into its own multi-controlled gate. No clean qubit.
fn gated_scan0(b: &mut B, u: &[QubitId], g: QubitId, cc: &[QubitId], lo: usize, hi: usize, off: isize,
               mut per: impl FnMut(&mut B, usize, QubitId, QubitId)) {
    let n = u.len();
    assert!(n >= 2 && cc.len() >= n - 1);
    // level c (0..n-1): cc[c] ^= (c == 0 ? lit0 : cc[c-1]) & lit_{c+1}; depends on literals 0..=c+1
    let apply = |b: &mut B, c: usize, j: usize| {
        let lit = |i: usize| (u[n - 1 - i], (j >> (n - 1 - i)) & 1 == 0);
        let (qa, na) = if c == 0 { lit(0) } else { (cc[c - 1], false) };
        let (qb, nb) = lit(c + 1);
        if na {
            b.x(qa);
        }
        if nb {
            b.x(qb);
        }
        b.ccx(qa, qb, cc[c]);
        if nb {
            b.x(qb);
        }
        if na {
            b.x(qa);
        }
    };
    let mut cur: Option<usize> = None;
    for j in lo..hi {
        let val = j as isize + off;
        if val < 0 || val as usize >= (1usize << n) {
            continue;
        }
        let val = val as usize;
        // first literal index whose value changes
        let first = match cur {
            None => 0,
            Some(c) if c == val => n,
            Some(c) => n - 1 - (usize::BITS - 1 - (c ^ val).leading_zeros()) as usize,
        };
        if let Some(c) = cur {
            for l in (0..n - 1).rev() {
                if l + 1 >= first {
                    apply(b, l, c);
                }
            }
        }
        for l in 0..n - 1 {
            if cur.is_none() || l + 1 >= first {
                apply(b, l, val);
            }
        }
        cur = Some(val);
        per(b, j, cc[n - 2], g);
    }
    if let Some(c) = cur {
        for l in (0..n - 1).rev() {
            apply(b, l, c);
        }
    }
}

pub struct FhDouble {
    pub d: Vec<QubitId>,
    pub v: Vec<QubitId>,
    pub pi: Vec<QubitId>,
    /// phase code p0 p1 p2: AL 001 (p0), DV 010 (p1), CO 011, RT 000, DONE 100 (p2); p0 = AL|CO = rotate up,
    /// p1 = DV|CO
    pub p0: QubitId,
    pub p1: QubitId,
    pub p2: QubitId,
    /// quotient-bit stack depth (counts the never-stored top bit c_k); the bits live in V's gap
    pub dep: Vec<QubitId>,
    /// b - 1
    pub bq: Vec<QubitId>,
    /// swap parity (starts at whatever the caller put there, e.g. the reflection bit)
    pub par: QubitId,
    pub pool: Vec<QubitId>,
    /// borrowed qubits (the idle passenger register): any state, always restored
    pub dirty: Vec<QubitId>,
    pub marks: Vec<(&'static str, usize)>,
    pub peaks: std::collections::BTreeMap<&'static str, usize>,
    pub cur_step: &'static str,
}

impl FhDouble {
    pub fn alloc(b: &mut B, d: Vec<QubitId>, v: Vec<QubitId>, lay: &LayDouble, par: QubitId, dirty: Vec<QubitId>) -> FhDouble {
        let mut q = || b.alloc();
        let (p0, p1, p2) = (q(), q(), q());
        let pi = b.alloc_n(PIB);
        let dep = b.alloc_n(DEPB);
        let bq = b.alloc_n(BB);
        let pool = b.alloc_n(POOL_D);
        FhDouble { d, v, pi, p0, p1, p2, dep, bq, par, pool, dirty, marks: vec![], peaks: Default::default(), cur_step: "S0" }
    }

    /// every qubit the traversal allocated (not D, V or par)
    pub fn all_meta(&self) -> Vec<QubitId> {
        let mut v = self.pool.clone();
        v.extend(&self.pi);
        v.extend([self.p0, self.p1, self.p2]);
        v.extend(&self.dep);
        v.extend(&self.bq);
        v
    }

    /// DONE counter: D lanes holding p's top bits (all 1 while a shot is DONE, D = (1, p)); bit j = lane ^ 1
    pub fn cnt_lanes(&self) -> Vec<QubitId> {
        (0..CNTB).map(|j| self.d[WD - 256 + j]).collect()
    }

    /// Initial state: D = (R = p, cd = 1), V = (rv = x' already in V lanes [1, 257), cv = 0), b = 256, pi = 1, AL.
    pub fn init(&mut self, b: &mut B, lay: &LayDouble) {
        let w = WD;
        let pp = super::refmodel_double::p();
        for i in 0..256 {
            if pp.bit(i) {
                b.x(self.d[i]);
            }
        }
        b.x(self.d[w - 1]);
        let u0 = (255 - lay.base[0]) & ((1 << BB) - 1); // b - 1 = 255
        for (i, &q) in self.bq.iter().enumerate() {
            if (u0 >> i) & 1 == 1 {
                b.x(q);
            }
        }
        b.x(self.pi[0]);
        b.x(self.p0); // AL
    }

    /// bq += pi (sub = false) or bq -= pi (sub = true), mod 2^BB, everywhere (g = None) or where g = 1.
    /// `inverse` plays the exact inverse. Scratch is transient.
    fn bq_pi(&self, b: &mut B, pl: &mut Pl, g: Option<QubitId>, sub: bool, inverse: bool) {
        let pi = self.pi.clone();
        let t = self.bq.clone();
        self.reg_add(b, pl, &t, &pi, g, sub, inverse);
    }

    fn bq_add(&self, b: &mut B, pl: &mut Pl, a: &[QubitId], g: Option<QubitId>, sub: bool, inverse: bool) {
        let t = self.bq.clone();
        self.reg_add(b, pl, &t, a, g, sub, inverse);
    }

    /// t += a (sub = false) or t -= a, a = PIB-bit register (pi or dep); mod 2^len(t); g as in bq_pi.
    fn reg_add(&self, b: &mut B, _pl: &mut Pl, t: &[QubitId], a: &[QubitId], g: Option<QubitId>, sub: bool,
               inverse: bool) {
        assert_eq!(a.len(), PIB);
        assert_eq!(t.len(), PIB + 1);
        // ancilla-free ripple on the low PIB lanes; its carry out is XORed into the top lane (t mod 2^(PIB + 1));
        // the flag's helper is a borrowed passenger qubit
        let d = self.dirty[0];
        b.begin();
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        ttk_add(b, a, &t[..PIB], g, Some((t[PIB], d)));
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let rec = b.end();
        b.play(&rec, inverse);
    }

    /// bq += c (classical, mod 2^BB), as one increment per set bit of c
    fn u_add_const(&self, b: &mut B, pl: &mut Pl, c: usize) {
        let c = c & ((1 << BB) - 1);
        if c == 0 {
            return;
        }
        for i in 0..BB {
            if (c >> i) & 1 == 1 {
                let bits = self.bq[i..].to_vec();
                inc_uncond(b, pl, &bits);
            }
        }
    }

    /// u -= po with po = CO & !z0 & [depth != 0] (a popping CO shot). With three free qubits po is computed through
    /// z0 and nz and erased in place; otherwise u -= CO - CO A - CO B + CO A B (A = [pi == 0], B = [depth == 0];
    /// neither involves u) as four literal-controlled steps, no clean qubit
    fn po_dec_u(&self, b: &mut B, pl: &mut Pl, lit_co: &[(QubitId, bool)], negpi: &[(QubitId, bool)],
                negdep: &[(QubitId, bool)]) {
        if pl.free.len() >= 3 {
            let z0 = pl.get();
            and_into(b, pl, negpi, z0, false);
            let nz = pl.get();
            and_into(b, pl, negdep, nz, false);
            let mut lpo = lit_co.to_vec();
            lpo.push((z0, true));
            lpo.push((nz, true));
            let po = pl.get();
            and_into(b, pl, &lpo, po, false);
            decp(b, pl, po, &self.bq);
            and_into(b, pl, &lpo, po, true);
            pl.put(po);
            and_into(b, pl, negdep, nz, true);
            pl.put(nz);
            and_into(b, pl, negpi, z0, true);
            pl.put(z0);
            return;
        }
        let bq = self.bq.clone();
        let co = lit_co.to_vec();
        let mut ca = co.clone();
        ca.extend_from_slice(negpi);
        let mut cb = co.clone();
        cb.extend_from_slice(negdep);
        let mut cab = ca.clone();
        cab.extend_from_slice(negdep);
        dec_lits(b, pl, &co, &bq);
        inc_lits(b, pl, &ca, &bq);
        inc_lits(b, pl, &cb, &bq);
        dec_lits(b, pl, &cab, &bq);
    }

    fn negdep(&self) -> Vec<(QubitId, bool)> {
        self.dep.iter().map(|&q| (q, true)).collect()
    }

    pub fn slot(&mut self, b: &mut B, lay: &LayDouble, sigma: usize) {
        let w = WD;
        let row = lay.rows[sigma];
        let (lv, jw, p1lo, lc, p2hi, pb0, pb1, pe0, pe1, sc0, sc1) =
            (row[0], row[1], row[2], row[3], row[4], row[5], row[6].min(w), row[7], row[8].min(w), row[9], row[10].min(w));
        let base = lay.base[sigma] as isize;
        let next_base = if sigma + 1 < lay.s { lay.base[sigma + 1] as isize } else { 0 };
        assert!(next_base <= base);
        let mut pl = Pl::new(&self.pool, &self.dirty);
        let (p0, p1, p2) = (self.p0, self.p1, self.p2);
        let lit_al = [(p0, false), (p1, true)];
        let lit_dv = [(p1, false), (p0, true)];
        let lit_co = [(p0, false), (p1, false)];
        let negdep = self.negdep();
        let negpi: Vec<(QubitId, bool)> = self.pi.iter().map(|&q| (q, true)).collect();
        let cnt: Vec<QubitId> = self.cnt_lanes();

        // S0 frozen counter
        self.marks.push(("S0", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S0"; STEP.with(|c| c.set("S0")); }
        {
            for &q in &cnt {
                b.x(q);
            }
            incp(b, &mut pl, p2, &cnt);
            for &q in &cnt {
                b.x(q);
            }
        }

        // DONE parking (S2 .. S8 end): DONE shots move p2 into depth bit 0 (they have depth 0), so that p2 = m, the
        // moving DIV / COEF bit, for every DV / CO shot and 0 elsewhere (RT = 000 with dep0 = 0)
        let dep0 = self.dep[0];
        b.cx(p2, dep0);
        xand(b, &mut pl, &[(p0, true), (p1, true), (dep0, false)], p2);

        // S2 value ladder P1 over lanes [0, lv): p2 ^= DIV bit (DV shots); the AL turn bit is parked in depth bit 4
        // (AL shots have depth 0), so turning shots carry depth 16 until the AL -> DV move in S4
        self.marks.push(("S2", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S2"; STEP.with(|c| c.set("S2")); }
        let tt4 = self.dep[DEPB - 1];
        if lv > 0 {
            self.bq_pi(b, &mut pl, Some(p1), false, false); // DV (and CO, whose P1 result is unused)
            let c0 = pl.get();
            let mf = if pl.free.len() >= 2 { pl.get_n(2) } else { pl.get_n(1) };
            let tq = mf.get(1).copied().unwrap_or(NO_QUBIT);
            let np = pl.free.len();
            let pp = pl.get_n(np);
            let pihi = jw.min(lv);
            // decoder prefixes: shared when the two windows are disjoint, split otherwise
            let (pa, pre) = if p1lo < lv && pihi > p1lo { (pp[..np / 2].to_vec(), pp[np / 2..].to_vec()) }
                            else { (pp.clone(), pp.clone()) };
            let t: Vec<QubitId> = self.d[0..lv].to_vec();
            let s: Vec<QubitId> = self.v[0..lv].to_vec();
            let mut srcs = vec![Src { lo: 0, hi: pihi, v: self.pi.clone(), a: 0, d: 1, pre: pa.clone(), late: false }];
            if p1lo < lv {
                srcs.push(Src { lo: p1lo, hi: lv, v: self.bq.clone(), a: -2 - base, d: 1, pre: pre.clone(), late: false });
            }
            let ms = Mscr { f: mf[0], t: tq, gf: tq, chain: pp.clone(), dirty: self.dirty.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: false, cmpl: true, sc: &ms, keep_f: true };
            let ru = mup(b, &ld);
            let rd = mdown(b, &ld, Some(p2));
            b.play(&ru, false);
            let ct = top_carry(&ld); // [rv<<pi > R]
            // decoders are cleared at the top: lend the prefix qubits (and the cell temp) to the two flag writes
            pl.put_n(&pp);
            pl.put_n(&mf[1..]);
            let mut ldv = lit_dv.to_vec();
            ldv.push((ct, true));
            xand(b, &mut pl, &ldv, p2); // DIV bit (p2 = 0 for every shot here)
            let mut lal = lit_al.to_vec();
            lal.push((ct, false));
            xand(b, &mut pl, &lal, tt4); // AL turn
            pl.take(&mf[1..]);
            pl.take(&pp);
            b.play(&rd, false);
            pl.put_n(&pp);
            pl.put_n(&mf);
            pl.put(c0);
            self.bq_pi(b, &mut pl, Some(p1), false, true);
        }

        // S3 turn: dl = tt & !V[b]; b <- b - pi + 1 - dl; erase dl with D[b + pi - 1]. tt = AL & turn bit; the
        // decoders' top levels live in depth bits 0..3 (|0> for every AL shot)
        self.marks.push(("S3", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3"; STEP.with(|c| c.set("S3")); }
        let ltt = [(p0, false), (p1, true), (tt4, false)];
        if pl.free.len() >= 4 {
            let dl = pl.get();
            let g = pl.get();
            let ltt = [(p0, false), (p1, true), (tt4, false)];
            xand(b, &mut pl, &ltt, g);
            let cc: Vec<QubitId> = self.dep[..DEPB - 1].to_vec();
            if pb1 > pb0 {
                let vref = self.v.clone();
                let u = self.bq.clone();
                gated_scan(b, &mut pl, &u, g, &cc, pb0, pb1, -1 - base, |b, j, o| {
                    b.x(vref[j]);
                    b.ccx(o, vref[j], dl);
                    b.x(vref[j]);
                });
            }
            self.marks.push(("S3 bupd", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3 bupd"; STEP.with(|c| c.set("S3 bupd")); }
            {
                self.bq_pi(b, &mut pl, Some(g), true, false);
                let h = pl.get();
                b.x(dl);
                b.and_c(g, dl, h);
                b.x(dl);
                let bq = self.bq.clone();
                incp(b, &mut pl, h, &bq);
                b.x(dl);
                b.and_u(g, dl, h);
                b.x(dl);
                pl.put(h);
            }
            if pe1 > pe0 {
                self.marks.push(("S3 erase", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3 erase"; STEP.with(|c| c.set("S3 erase")); }
                self.bq_pi(b, &mut pl, None, false, false); // bq = b + pi - 1 = e
                let dref = self.d.clone();
                let u = self.bq.clone();
                gated_scan(b, &mut pl, &u, g, &cc, pe0, pe1, -base, |b, j, o| b.ccx(o, dref[j], dl));
                self.bq_pi(b, &mut pl, None, false, true);
            }
            xand(b, &mut pl, &ltt, g);
            pl.put(g);
            pl.put(dl);
        } else {
            let dl = pl.get();
            let g = pl.get();
            let ltt = [(p0, false), (p1, true), (tt4, false)];
            xand(b, &mut pl, &ltt, g);
            let mut cc: Vec<QubitId> = self.dep[..DEPB - 1].to_vec();
            cc.push(p1);
            let dirty_s3 = self.dirty.clone();
            if pb1 > pb0 {
                let vref = self.v.clone();
                let u = self.bq.clone();
                gated_scan0(b, &u, g, &cc, pb0, pb1, -1 - base, |b, j, c, gg| {
                    b.x(vref[j]);
                    mcx_dirty(b, &[c, gg, vref[j]], dl, &dirty_s3);
                    b.x(vref[j]);
                });
            }
            self.marks.push(("S3 bupd", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3 bupd"; STEP.with(|c| c.set("S3 bupd")); }
            {
                self.bq_pi(b, &mut pl, Some(g), true, false);
                // bq += g & !dl: a g-controlled increment of the register (!dl, bq) adds !dl into bq and flips !dl
                b.x(dl);
                let mut r = vec![dl];
                r.extend(&self.bq);
                incp(b, &mut pl, g, &r);
                b.cx(g, dl);
                b.x(dl);
            }
            if pe1 > pe0 {
                self.marks.push(("S3 erase", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3 erase"; STEP.with(|c| c.set("S3 erase")); }
                self.bq_pi(b, &mut pl, None, false, false); // bq = b + pi - 1 = e
                let dref = self.d.clone();
                let u = self.bq.clone();
                gated_scan0(b, &u, g, &cc, pe0, pe1, -base, |b, j, c, gg| mcx_dirty(b, &[c, gg, dref[j]], dl, &dirty_s3));
                self.bq_pi(b, &mut pl, None, false, true);
            }
            xand(b, &mut pl, &ltt, g);
            pl.put(g);
            pl.put(dl);
        }

        // S4 DV bit bookkeeping (m = p2): the first DV slot's c_k is always 1 and never stored; depth += 1 for DV at
        // pi > 0; moves DV0 -> CO (p2 keeps DV0's bit 0 as the COEF bit) and AL -> DV (turn bit cleared)
        self.marks.push(("S4", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S4"; STEP.with(|c| c.set("S4")); }
        if pl.free.len() >= 3 {
            {
                let z0 = pl.get();
                and_into(b, &mut pl, &negpi, z0, false);
                {
                    let nz = pl.get();
                    and_into(b, &mut pl, &negdep, nz, false);
                    xand(b, &mut pl, &[(p1, false), (p0, true), (z0, true), (nz, false)], p2); // virtual c_k
                    and_into(b, &mut pl, &negdep, nz, true);
                    pl.put(nz);
                }
                {
                    let upq = pl.get();
                    let lpush = [(p1, false), (p0, true), (z0, true)];
                    and_into(b, &mut pl, &lpush, upq, false);
                    let dep = self.dep.clone();
                    incp(b, &mut pl, upq, &dep);
                    and_into(b, &mut pl, &lpush, upq, true);
                    pl.put(upq);
                }
                {
                    let dv0 = pl.get();
                    and_into(b, &mut pl, &[(p1, false), (p0, true), (z0, false)], dv0, false);
                    b.cx(dv0, p0); // DV0 -> CO: 010 -> 011
                    and_into(b, &mut pl, &[(p1, false), (p0, false), (z0, false)], dv0, true); // = CO & z0 (post)
                    pl.put(dv0);
                }
                {
                    let tt = pl.get();
                    and_into(b, &mut pl, &ltt, tt, false);
                    b.cx(tt, p0); // AL -> DV: 001 -> 010
                    b.cx(tt, p1);
                    b.cx(tt, tt4);
                    let nz = pl.get();
                    and_into(b, &mut pl, &negdep, nz, false);
                    and_into(b, &mut pl, &[(p1, false), (p0, true), (nz, false)], tt, true); // DV, empty stack (post)
                    and_into(b, &mut pl, &negdep, nz, true);
                    pl.put(nz);
                    pl.put(tt);
                }
                and_into(b, &mut pl, &negpi, z0, true);
                pl.put(z0);
            }
        } else {
            {
                let z0 = pl.get();
                and_into(b, &mut pl, &negpi, z0, false);
                {
                    let mut l = vec![(p1, false), (p0, true), (z0, true)];
                    l.extend(negdep.iter().cloned());
                    xand(b, &mut pl, &l, p2); // virtual c_k
                }
                {
                    let upq = pl.get();
                    let lpush = [(p1, false), (p0, true), (z0, true)];
                    and_into(b, &mut pl, &lpush, upq, false);
                    let dep = self.dep.clone();
                    incp(b, &mut pl, upq, &dep);
                    and_into(b, &mut pl, &lpush, upq, true);
                    pl.put(upq);
                }
                {
                    let dv0 = pl.get();
                    and_into(b, &mut pl, &[(p1, false), (p0, true), (z0, false)], dv0, false);
                    b.cx(dv0, p0); // DV0 -> CO: 010 -> 011
                    and_into(b, &mut pl, &[(p1, false), (p0, false), (z0, false)], dv0, true); // = CO & z0 (post)
                    pl.put(dv0);
                }
                {
                    let tt = pl.get();
                    and_into(b, &mut pl, &ltt, tt, false);
                    b.cx(tt, p0); // AL -> DV: 001 -> 010
                    b.cx(tt, p1);
                    b.cx(tt, tt4);
                    let mut l = vec![(p1, false), (p0, true)];
                    l.extend(negdep.iter().cloned());
                    xand(b, &mut pl, &l, tt); // DV, empty stack (post)
                    pl.put(tt);
                }
                and_into(b, &mut pl, &negpi, z0, true);
                pl.put(z0);
            }
        }

        // SC stack scan: DV pushes m and CO pops into m at physical lane b + k = (b - 1) + depth + pi (DV depth
        // already incremented; CO depth is decremented only at P2's top), gated by (DV | CO) & !z0 & depth >= 2
        self.marks.push(("SC", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "SC"; STEP.with(|c| c.set("SC")); }
        if sc1 > sc0 {
            let gq = pl.get();
            let hi: Vec<(QubitId, bool)> = self.dep[1..].iter().map(|&q| (q, true)).collect();
            // gq = p1 & !(pi == 0) & !(depth <= 1): with two free qubits an AND chain through z0 and d01, otherwise
            // the XOR of the AND terms p1, p1 A, p1 D, p1 A D
            let gate = |b: &mut B, pl: &mut Pl, undo: bool| {
                if pl.free.len() >= 2 {
                    let z0 = pl.get();
                    and_into(b, pl, &negpi, z0, false);
                    let d01 = pl.get();
                    and_into(b, pl, &hi, d01, false); // [depth <= 1]
                    and_into(b, pl, &[(p1, false), (z0, true), (d01, true)], gq, undo);
                    and_into(b, pl, &hi, d01, true);
                    pl.put(d01);
                    and_into(b, pl, &negpi, z0, true);
                    pl.put(z0);
                } else {
                    po_terms(b, pl, gq, &[(p1, false)], &negpi, &hi, None);
                }
            };
            gate(b, &mut pl, false);
            let dep = self.dep.clone();
            let pi = self.pi.clone();
            let bx = self.bq.clone();
            self.reg_add(b, &mut pl, &bx, &dep, None, false, false);
            self.reg_add(b, &mut pl, &bx, &pi, None, false, false);
            let mut bg = bx.clone();
            bg.push(gq);
            let npre = pl.free.len().min(BB);
            let pre = pl.get_n(npre);
            let vref = self.v.clone();
            let dirty = self.dirty.clone();
            onehot_scan(b, &bg, &pre, sc0, sc1, (1isize << BB) - base, |b, j, c| {
                let mut l = c.to_vec();
                l.push((p2, false));
                b.cx(vref[j], p2);
                mc_xor(b, &l, vref[j], &[], &dirty);
                b.cx(vref[j], p2);
            });
            pl.put_n(&pre);
            self.reg_add(b, &mut pl, &bx, &pi, None, false, true);
            self.reg_add(b, &mut pl, &bx, &dep, None, false, true);
            gate(b, &mut pl, true);
            pl.put(gq);
        }

        // S1 CO pop for shots that were CO at slot start (CO & !z0): the scan left the popped bit in m; at depth 1 the
        // virtual c_k = 1 is popped. The depth decrement is deferred to P2's top.
        self.marks.push(("S1", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S1"; STEP.with(|c| c.set("S1")); }
        if pl.free.len() >= 3 {
            {
                let z0 = pl.get();
                and_into(b, &mut pl, &negpi, z0, false);
                let mut lco = lit_co.to_vec();
                lco.push((z0, true));
                let co = pl.get();
                and_into(b, &mut pl, &lco, co, false);
                let d1: Vec<(QubitId, bool)> = self.dep.iter().enumerate().map(|(i, &q)| (q, i != 0)).collect();
                let one = pl.get();
                and_into(b, &mut pl, &d1, one, false); // [depth == 1]
                b.ccx(co, one, p2); // virtual c_k
                and_into(b, &mut pl, &d1, one, true);
                pl.put(one);
                and_into(b, &mut pl, &lco, co, true);
                pl.put(co);
                and_into(b, &mut pl, &negpi, z0, true);
                pl.put(z0);
            }
        } else {
            {
                // p2 ^= CO & !(pi == 0) & [depth == 1] = CO E ^ CO A E
                let d1: Vec<(QubitId, bool)> = self.dep.iter().enumerate().map(|(i, &q)| (q, i != 0)).collect();
                let mut t1 = lit_co.to_vec();
                t1.extend(d1.iter().cloned());
                let mut t2 = lit_co.to_vec();
                t2.extend(negpi.iter().cloned());
                t2.extend(d1.iter().cloned());
                xand(b, &mut pl, &t1, p2);
                xand(b, &mut pl, &t2, p2);
            }
        }

        // S5 RT0: swap; RT0 -> AL, or DONE (parked: dep0 = 1) when b == 1
        self.marks.push(("S5", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S5"; STEP.with(|c| c.set("S5")); }
        if pl.free.len() >= 4 {
            {
                let z0 = pl.get();
                and_into(b, &mut pl, &negpi, z0, false);
                let rt0 = pl.get();
                let l5 = [(p0, true), (p1, true), (dep0, true), (z0, false)];
                and_into(b, &mut pl, &l5, rt0, false); // RT at pi = 0
                let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&q| (q, true)).collect();
                let b1 = pl.get();
                if base == 0 {
                    and_into(b, &mut pl, &bz, b1, false); // b == 1; no shot can finish while base > 0
                }
                let dn = pl.get();
                b.and_c(rt0, b1, dn);
                cswap_regs(b, rt0, &self.d, &self.v);
                b.cx(rt0, self.par);
                b.cx(dn, dep0); // RT0 -> DONE (parked)
                b.cx(rt0, p0); // RT0 -> AL: 000 -> 001
                b.cx(dn, p0);
                b.and_u(rt0, b1, dn);
                pl.put(dn);
                if base == 0 {
                    and_into(b, &mut pl, &bz, b1, true);
                }
                pl.put(b1);
                // rt0 = (AL & z0) ^ (DONE & z0 & [cnt == 0])
                {
                    let mut la = lit_al.to_vec();
                    la.push((z0, false));
                    let w2 = pl.get();
                    and_into(b, &mut pl, &la, w2, false);
                    b.cx(w2, rt0);
                    and_into(b, &mut pl, &la, w2, true);
                    pl.put(w2);
                }
                let mut ldn = vec![(p0, true), (p1, true), (dep0, false), (z0, false)];
                ldn.extend(cnt.iter().map(|&q| (q, false)));
                xand(b, &mut pl, &ldn, rt0);
                pl.put(rt0);
                and_into(b, &mut pl, &negpi, z0, true);
                pl.put(z0);
            }
        } else {
            {
                let rt0 = pl.get();
                let mut l5 = vec![(p0, true), (p1, true), (dep0, true)];
                l5.extend(negpi.iter().cloned());
                xand(b, &mut pl, &l5, rt0); // RT at pi = 0
                // dn = rt0 & [b == 1] (no shot can finish while base > 0), used as literals
                let mut ldn1 = vec![(rt0, false)];
                ldn1.extend(self.bq.iter().map(|&q| (q, true)));
                cswap_regs(b, rt0, &self.d, &self.v);
                b.cx(rt0, self.par);
                if base == 0 {
                    xand(b, &mut pl, &ldn1, dep0); // RT0 -> DONE (parked)
                }
                b.cx(rt0, p0); // RT0 -> AL: 000 -> 001
                if base == 0 {
                    xand(b, &mut pl, &ldn1, p0);
                }
                // rt0 = (AL & z0) ^ (DONE & z0 & [cnt == 0])
                let mut la = lit_al.to_vec();
                la.extend(negpi.iter().cloned());
                xand(b, &mut pl, &la, rt0);
                let mut ldn = vec![(p0, true), (p1, true), (dep0, false)];
                ldn.extend(negpi.iter().cloned());
                ldn.extend(cnt.iter().map(|&q| (q, false)));
                xand(b, &mut pl, &ldn, rt0);
                pl.put(rt0);
            }
        }

        // S6 cofactor ladder P2 (COEF, g = m = p2). Boundary u + pi + depth - po (po = popping CO shot, transient;
        // the depth decrement happens at P2's top), ladder lane l <-> phys W-1-l over phys [lc, W)
        self.marks.push(("S6", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S6"; STEP.with(|c| c.set("S6")); }
        self.bq_pi(b, &mut pl, None, false, false);
        let dep = self.dep.clone();
        self.bq_add(b, &mut pl, &dep, None, false, false);
        self.po_dec_u(b, &mut pl, &lit_co, &negpi, &negdep);
        if lc < w {
            let n = w - lc;
            let c0 = pl.get();
            let mf = if pl.free.len() >= 2 { pl.get_n(2) } else { pl.get_n(1) };
            let tq = mf.get(1).copied().unwrap_or(NO_QUBIT);
            let np = pl.free.len();
            let pre = pl.get_n(np);
            let t: Vec<QubitId> = (0..n).map(|l| self.v[w - 1 - l]).collect();
            let s: Vec<QubitId> = (0..n).map(|l| self.d[w - 1 - l]).collect();
            let mut srcs = vec![];
            if p2hi > lc {
                srcs.push(Src { lo: w - p2hi, hi: w - lc, v: self.bq.clone(), a: w as isize - 1 - base, d: -1,
                                pre: pre.clone(), late: false });
            }
            let ms = Mscr { f: mf[0], t: tq, gf: tq, chain: pre.clone(), dirty: self.dirty.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, keep_f: true };
            let ru = mup(b, &ld);
            let rd = mdown(b, &ld, Some(p2));
            b.play(&rd, true);
            // decoder prefixes and the cell temp are |0> here (c0 holds a carry, f the mask): lend them out
            pl.put_n(&pre);
            pl.put_n(&mf[1..]);
            let ct = top_carry(&ld); // [cd<<pi > cv']; cmp = !ct
            // m ^= CO & cmp (a CO shot that has finished popping has ct = 1)
            xand(b, &mut pl, &[(p0, false), (p1, false), (ct, true)], p2);
            if pl.free.len() >= 4 {
                // deferred depth decrement for po = CO & !z0 & depth != 0 (pre)
                let z0 = pl.get();
                and_into(b, &mut pl, &negpi, z0, false);
                let po = pl.get();
                {
                    let dz = pl.get();
                    and_into(b, &mut pl, &negdep, dz, false);
                    and_into(b, &mut pl, &[(p0, false), (p1, false), (z0, true), (dz, true)], po, false);
                    and_into(b, &mut pl, &negdep, dz, true);
                    pl.put(dz);
                }
                decp(b, &mut pl, po, &dep);
                // erase po = CO & !z0 & !([depth == 0] & ct) from the post state
                {
                    let dz = pl.get();
                    and_into(b, &mut pl, &negdep, dz, false);
                    let h = pl.get();
                    b.and_c(dz, ct, h);
                    and_into(b, &mut pl, &[(p0, false), (p1, false), (z0, true), (h, true)], po, true);
                    b.and_u(dz, ct, h);
                    pl.put(h);
                    and_into(b, &mut pl, &negdep, dz, true);
                    pl.put(dz);
                }
                pl.put(po);
                and_into(b, &mut pl, &negpi, z0, true);
                pl.put(z0);
            } else if pl.free.len() >= 1 {
                // deferred depth decrement for po = CO & !z0 & depth != 0 (pre), po as the XOR of four AND terms
                let po = pl.get();
                po_terms(b, &mut pl, po, &lit_co, &negpi, &negdep, None);
                decp(b, &mut pl, po, &dep);
                // erase po = CO & !z0 & !([depth == 0] & ct) from the post state
                po_terms(b, &mut pl, po, &lit_co, &negpi, &negdep, Some((ct, false)));
                pl.put(po);
            } else {
                // deferred depth decrement for po = CO & !z0 & depth != 0 (pre). depth -= CO !A (A = [pi == 0]) as
                // depth -= CO, depth += CO A; the shots that had depth 0 wrapped to 2^DEPB - 1. Those are exactly the
                // CO !A shots with ct = 1 at depth 2^DEPB - 1 (a CO !A shot at depth <= 1 has ct = [depth == 0]), and
                // (depth 0, ct = 1) is unreachable for CO !A shots, so a swap 0 <-> 2^DEPB - 1 under CO !A ct returns them
                {
                    let mut ca = lit_co.to_vec();
                    ca.extend(negpi.iter().cloned());
                    dec_lits(b, &mut pl, &lit_co, &dep);
                    inc_lits(b, &mut pl, &ca, &dep);
                    for i in 1..dep.len() {
                        b.cx(dep[0], dep[i]);
                    }
                    let z: Vec<(QubitId, bool)> = dep[1..].iter().map(|&q| (q, true)).collect();
                    let mut t1 = lit_co.to_vec();
                    t1.push((ct, false));
                    t1.extend(z.iter().cloned());
                    let mut t2 = ca.clone();
                    t2.push((ct, false));
                    t2.extend(z.iter().cloned());
                    xand(b, &mut pl, &t1, dep[0]);
                    xand(b, &mut pl, &t2, dep[0]);
                    for i in 1..dep.len() {
                        b.cx(dep[0], dep[i]);
                    }
                }
            }
            pl.take(&mf[1..]);
            pl.take(&pre);
            b.play(&ru, true);
            pl.put_n(&pre);
            pl.put_n(&mf);
            pl.put(c0);
        }

        // S7 CO -> RT marker: a CO shot (pi > 0) whose stack is now empty gets p2 = 1 (011 -> 111); P3 completes the
        // move
        self.marks.push(("S7", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S7"; STEP.with(|c| c.set("S7")); }
        if pl.free.len() >= 2 {
            {
                let z0 = pl.get();
                and_into(b, &mut pl, &negpi, z0, false);
                let nz = pl.get();
                and_into(b, &mut pl, &negdep, nz, false);
                xand(b, &mut pl, &[(p0, false), (p1, false), (z0, true), (nz, false)], p2);
                and_into(b, &mut pl, &negdep, nz, true);
                pl.put(nz);
                and_into(b, &mut pl, &negpi, z0, true);
                pl.put(z0);
            }
        } else {
            {
                // p2 ^= CO & !(pi == 0) & [depth == 0] = CO B ^ CO A B
                let mut t1 = lit_co.to_vec();
                t1.extend(negdep.iter().cloned());
                let mut t2 = lit_co.to_vec();
                t2.extend(negpi.iter().cloned());
                t2.extend(negdep.iter().cloned());
                xand(b, &mut pl, &t1, p2);
                xand(b, &mut pl, &t2, p2);
            }
        }

        // S8 discriminator P3: z = [cv >= cd << (pi_pre + 1)] (= model's pi_post + 2). Marked shots (111) have
        // ct = !z = 1 and move to RT; RT shots (000, not a parked DONE) have ct = 0
        self.marks.push(("S8", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S8"; STEP.with(|c| c.set("S8")); }
        if lc >= w {
            // degenerate (no cofactor lanes, early slots): every RT shot here is a marked one, ct = 1
            b.cx(p1, p0);
            b.cx(p2, p1);
            xand(b, &mut pl, &[(p0, true), (p1, true), (dep0, true)], p2);
            b.cx(p2, p1);
            b.cx(p1, p0);
        } else {
            // truncated compare: only ladder lanes >= cut (P3DEPTH below the lowest shot boundary; lane 0 never
            // carries since cd << 1 has bit 0 = 0); highest differing lane <= 25 below a boundary in 6e7 samples
            let cut = if p2hi > lc { (w - p2hi).saturating_sub(P3DEPTH) } else { 0 }.max(1);
            let n = w - lc - cut;
            let c0 = pl.get();
            let mf = if pl.free.len() >= 2 { pl.get_n(2) } else { pl.get_n(1) };
            let tq = mf.get(1).copied().unwrap_or(NO_QUBIT);
            let np = pl.free.len();
            let pre = pl.get_n(np);
            let t: Vec<QubitId> = (cut..cut + n).map(|l| self.v[w - 1 - l]).collect();
            let s: Vec<QubitId> = (cut..cut + n).map(|l| self.d[w - l]).collect();
            let mut srcs = vec![];
            if p2hi > lc {
                // late: the shot's boundary lane W - b - pi stays in the compare with T there (rv's MSB, always 1)
                // flipped to the 0 it stands for, so cd << 1 may use it (q = 1 CO->RT needs it when W = 258)
                let lo = (w - p2hi).saturating_sub(cut);
                srcs.push(Src { lo, hi: w - lc - cut, v: self.bq.clone(), a: w as isize - 1 - base - cut as isize,
                                d: -1, pre: pre.clone(), late: true });
            }
            let ms = Mscr { f: mf[0], t: tq, gf: tq, chain: pre.clone(), dirty: self.dirty.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, keep_f: true };
            let ru = mup(b, &ld);
            b.play(&ru, false);
            let ct = top_carry(&ld); // [cd<<(pi+1) > cv] = !z
            pl.put_n(&pre);
            pl.put_n(&mf[1..]);
            // 111 <-> 000 gated by ct & !dep0: in the basis (p0^p1, p1^p2, p2) a p2 flip
            b.cx(p1, p0);
            b.cx(p2, p1);
            xand(b, &mut pl, &[(ct, false), (p0, true), (p1, true), (dep0, true)], p2);
            b.cx(p2, p1);
            b.cx(p1, p0);
            pl.take(&mf[1..]);
            pl.take(&pre);
            b.play(&ru, true);
            pl.put_n(&pre);
            pl.put_n(&mf);
            pl.put(c0);
        }
        self.bq_add(b, &mut pl, &dep, None, false, true);
        self.bq_pi(b, &mut pl, None, false, true);
        // DONE un-parking
        xand(b, &mut pl, &[(p0, true), (p1, true), (dep0, false)], p2);
        b.cx(p2, dep0);

        // S9 rotation and pi update from the post phase
        self.marks.push(("S9", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S9"; STEP.with(|c| c.set("S9")); }
        let v0 = self.v[0];
        for j in 0..w - 1 {
            self.v[j] = self.v[j + 1];
        }
        self.v[w - 1] = v0;
        // up = AL | CO (post), or DONE with pi even
        let upq = pl.get();
        b.cx(p0, upq); // AL | CO
        b.x(self.pi[0]);
        b.ccx(p2, self.pi[0], upq);
        b.x(self.pi[0]);
        rot2_up(b, upq, &self.v);
        {
            // pi -= 1 (complement, +1, complement), then pi += 2 up
            let pi = self.pi.clone();
            for &q in &pi {
                b.x(q);
            }
            inc_uncond(b, &mut pl, &pi);
            for &q in &pi {
                b.x(q);
            }
            incp(b, &mut pl, upq, &pi[1..]);
        }
        b.ccx(p2, self.pi[0], upq); // DONE shots flipped pi's parity: post pi0 = !pre pi0
        b.cx(p0, upq);
        pl.put(upq);
        // re-centre the offset register for the next slot: u += base(sigma) - base(sigma + 1)
        self.u_add_const(b, &mut pl, (base - next_base) as usize);
        {
            let used = self.pool.len() - pl.low;
            let e = self.peaks.entry(self.cur_step).or_insert(0);
            *e = (*e).max(used);
            self.cur_step = "S0"; STEP.with(|c| c.set("S0"));
        }
        assert_eq!(pl.free.len(), self.pool.len(), "scratch leak");
    }

    pub fn forward(&mut self, b: &mut B, lay: &LayDouble) -> Vec<Vec<QubitId>> {
        let mut maps = Vec::with_capacity(lay.s);
        for sigma in 0..lay.s {
            maps.push(self.v.clone());
            self.slot(b, lay, sigma);
        }
        maps
    }

    pub fn inverse(&mut self, b: &mut B, lay: &LayDouble, maps: &[Vec<QubitId>]) {
        for sigma in (0..lay.s).rev() {
            self.v = maps[sigma].clone();
            b.begin();
            self.slot(b, lay, sigma);
            let rec = b.end();
            b.play(&rec, true);
            self.v = maps[sigma].clone();
        }
    }
}
