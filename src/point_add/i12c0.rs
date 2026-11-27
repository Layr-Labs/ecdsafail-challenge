//! q631 / i12 copy of agent i10's i10c0.rs (agent i12, 2026-11-19; local research, not submitted): ripple adders WITHOUT their
//! clean carry-in lane c0, used by i12w.rs for ITEM 12's phase B (c0 = lane 257).  Self-contained (local Row / NONE / qubits) so
//! that local tools include it by path; parser, emitters and the per-instance random-state check unchanged.
//!
//! The non-walk parts of ITEM 10 are qkit.cjs code: Cuccaro ripple adders whose carry-in is a clean lane c0 (wire 636, the
//! walks' tst lane).  Each instance is parsed from its records (MAJ / UMA / UMA-C / MAJ^-1 / UMA^-1 / UMA-C^-1 chains, qkit.cjs
//! add / sub / carry / gt) and re-emitted as the ancilla-free ripple adder of the tree's walk generator (UnitWalk.add, Takahashi
//! style: the carries live in the operand lanes), same function on every state with c0 = 0:
//!     add (ctrl?, cout?):  b += [ctrl] a mod 2^n,  cout ^= [ctrl] carry     sub (ctrl?, bout?):  b -= [ctrl] a,  bout ^= [ctrl] borrow
//!     carry (ctrl?):       flag ^= [ctrl] carry(a + b),  a, b unchanged
//! Every replacement is checked against the original records on random states (c0 = 0) before it is accepted; an instance
//! that does not parse or does not check is left as it is (counted).
type Row = [u16; 4];
const NONE: u16 = u16::MAX;
#[inline] fn qubits(kind: u16) -> usize { match kind { 13 => 3, 8 | 9 => 2, 6 | 7 | 12 => 1, _ => 0 } }

thread_local! { pub static FAIL: std::cell::Cell<u32> = std::cell::Cell::new(0); static FAIL_AT: std::cell::Cell<usize> = std::cell::Cell::new(0); static FAIL_LANES: std::cell::RefCell<Vec<u16>> = std::cell::RefCell::new(Vec::new()); static MID: std::cell::Cell<usize> = std::cell::Cell::new(0); static FAIL_CTRL: std::cell::Cell<u16> = std::cell::Cell::new(u16::MAX); }
#[derive(Clone, Copy, PartialEq, Debug)]
enum Kind { Add, Carry, Sub, Ident }
#[derive(Debug)]
pub struct Inst { kind: Kind, a: Vec<u16>, b: Vec<u16>, ctrl: Option<u16>, ctrl2: Option<u16>, out: Option<u16>, start: usize, end: usize, mid: usize }

#[inline] fn cx(r: &Row, c: u16, t: u16) -> bool { r[0] == 8 && r[1] == c && r[2] == t && r[3] == NONE }
#[inline] fn ccx(r: &Row, c1: u16, c2: u16, t: u16) -> bool { r[0] == 13 && r[3] == t && ((r[1] == c1 && r[2] == c2) || (r[1] == c2 && r[2] == c1)) }
/// the other control of a CCX with target t and one control c
#[inline] fn ccx_other(r: &Row, c: u16, t: u16) -> Option<u16> { if r[0] == 13 && r[3] == t { if r[1] == c { Some(r[2]) } else if r[2] == c { Some(r[1]) } else { None } } else { None } }

/// parse one instance whose first record is rows[p] (c0 = the clean carry-in lane)
pub fn parse(rows: &[Row], p: usize, c0: u16) -> Option<Inst> {
    let g = |i: usize| -> Option<&Row> { rows.get(i) };
    #[derive(Clone, Copy, PartialEq)] enum Up { Maj, UmaInv, UmaCInv }
    // ascending chain start
    let (up, ctrl0, a0, b0, mut q) = {
        let r0 = g(p)?;
        if r0[0] == 8 && r0[1] != c0 && r0[2] != c0 { // maj(c0, b0, a0): CX(a0, b0) CX(a0, c0) CCX(c0, b0, a0)
            let (a0, b0) = (r0[1], r0[2]); if !(cx(g(p + 1)?, a0, c0) && ccx(g(p + 2)?, c0, b0, a0)) { { FAIL.with(|f| f.set(1)); return None; } } (Up::Maj, None, a0, b0, p + 3) }
        else if r0[0] == 8 && r0[1] == c0 { // umaInv(c0, b0, a0): CX(c0, b0) CX(a0, c0) CCX(c0, b0, a0)
            let b0 = r0[2]; let r1 = g(p + 1)?; if !(r1[0] == 8 && r1[2] == c0 && r1[3] == NONE) { { FAIL.with(|f| f.set(2)); return None; } } let a0 = r1[1];
            if !ccx(g(p + 2)?, c0, b0, a0) { { FAIL.with(|f| f.set(3)); return None; } } (Up::UmaInv, None, a0, b0, p + 3) }
        else if r0[0] == 13 && (r0[1] == c0 || r0[2] == c0) { // umaCInv(ctrl, c0, b0, a0): CCX(ctrl, c0, b0) CCX(ctrl, a0, b0) CX(a0, b0) CX(a0, c0) CCX(c0, b0, a0)
            let b0 = r0[3]; let ctrl = if r0[1] == c0 { r0[2] } else { r0[1] }; let a0 = ccx_other(g(p + 1)?, ctrl, b0)?;
            if !(cx(g(p + 2)?, a0, b0) && cx(g(p + 3)?, a0, c0) && ccx(g(p + 4)?, c0, b0, a0)) { { FAIL.with(|f| f.set(4)); return None; } } (Up::UmaCInv, Some(ctrl), a0, b0, p + 5) }
        else { { FAIL.with(|f| f.set(5)); return None; } } };
    let mut a = vec![a0]; let mut b = vec![b0];
    let used = |a: &Vec<u16>, b: &Vec<u16>, x: u16| a.contains(&x) || b.contains(&x) || x == c0 || Some(x) == ctrl0;
    loop { let x = *a.last().unwrap();
        let step = match up {
            Up::Maj => { let r0 = match g(q) { Some(r) => r, None => break }; if r0[0] != 8 || r0[3] != NONE { break; } let (ai, bi) = (r0[1], r0[2]);
                if used(&a, &b, ai) || used(&a, &b, bi) || ai == bi { break; }
                if g(q + 1).map_or(false, |r| cx(r, ai, x)) && g(q + 2).map_or(false, |r| ccx(r, x, bi, ai)) { Some((ai, bi, 3)) } else { None } }
            Up::UmaInv => { let r0 = match g(q) { Some(r) => r, None => break }; if !(r0[0] == 8 && r0[1] == x && r0[3] == NONE) { break; } let bi = r0[2];
                let r1 = match g(q + 1) { Some(r) => r, None => break }; if !(r1[0] == 8 && r1[2] == x && r1[3] == NONE) { break; } let ai = r1[1];
                if used(&a, &b, ai) || used(&a, &b, bi) || ai == bi { break; }
                if g(q + 2).map_or(false, |r| ccx(r, x, bi, ai)) { Some((ai, bi, 3)) } else { None } }
            Up::UmaCInv => { let c = ctrl0.unwrap(); let r0 = match g(q) { Some(r) => r, None => break }; if !(r0[0] == 13 && ((r0[1] == c && r0[2] == x) || (r0[2] == c && r0[1] == x))) { break; }
                let bi = r0[3]; let ai = match g(q + 1).and_then(|r| ccx_other(r, c, bi)) { Some(v) => v, None => break };
                if used(&a, &b, ai) || used(&a, &b, bi) || ai == bi { break; }
                if g(q + 2).map_or(false, |r| cx(r, ai, bi)) && g(q + 3).map_or(false, |r| cx(r, ai, x)) && g(q + 4).map_or(false, |r| ccx(r, x, bi, ai)) { Some((ai, bi, 5)) } else { None } } };
        match step { Some((ai, bi, len)) => { a.push(ai); b.push(bi); q += len; } None => break } }
    let n = a.len();
    FAIL_AT.with(|f| f.set(q)); FAIL_CTRL.with(|f| f.set(ctrl0.unwrap_or(u16::MAX))); FAIL_LANES.with(|l| { let mut v = a.clone(); v.extend(b.iter().cloned()); v.push(c0); if let Some(c) = ctrl0 { v.push(c); } *l.borrow_mut() = v; });
    let xs = |i: usize, a: &Vec<u16>| if i == 0 { c0 } else { a[i - 1] };
    // top and descending chain
    match up {
        Up::UmaInv | Up::UmaCInv => { // [top: borrow out CX(top, z) / CCX(ctrl, top, z)], descending majInv(x, b_i, a_i) = CCX(x, b_i, a_i) CX(a_i, x) CX(a_i, b_i), i = n-1 .. 0
            let top = a[n - 1]; let mut out: Option<u16> = None;
            // i12: truncated top of a mod 2^n subtraction (uncontrolled): CX(x, b_t) [CX(a_t, x) CX(a_t, x)] CX(a_t, b_t), x = a[n - 1]
            let mut trunc: Option<(u16, u16)> = None;
            if up == Up::UmaInv { if let Some(r) = g(q) { if r[0] == 8 && r[1] == top && r[3] == NONE { let bt = r[2]; let fresh = |y: u16| !(a.contains(&y) || b.contains(&y) || y == c0);
                if fresh(bt) { if let Some(r1) = g(q + 1) { if r1[0] == 8 && r1[3] == NONE && fresh(r1[1]) && r1[1] != bt {
                    let at = r1[1];
                    if r1[2] == top && g(q + 2).map_or(false, |r| cx(r, at, top)) && g(q + 3).map_or(false, |r| cx(r, at, bt)) { trunc = Some((at, bt)); q += 4; }
                    else if r1[2] == bt { trunc = Some((at, bt)); q += 2; } } } } } } }
            if let Some((at, bt)) = trunc {
                MID.with(|m| m.set(q));
                for i in (0..n).rev() { let x = xs(i, &a); FAIL_AT.with(|f| f.set(q)); if !(g(q).map_or(false, |r| ccx(r, x, b[i], a[i])) && g(q + 1).map_or(false, |r| cx(r, a[i], x)) && g(q + 2).map_or(false, |r| cx(r, a[i], b[i]))) { FAIL.with(|f| f.set(94)); return None; } q += 3; }
                let mut a = a; let mut b = b; a.push(at); b.push(bt);
                return Some(Inst { kind: Kind::Sub, a, b, ctrl: None, ctrl2: None, out: None, start: p, end: q, mid: MID.with(|m| m.get()) }); }
            if let Some(r) = g(q) { let fresh = |x: u16| !(a.contains(&x) || b.contains(&x) || x == c0 || Some(x) == ctrl0);
                if ctrl0.is_none() && r[0] == 8 && r[1] == top && r[3] == NONE && fresh(r[2]) { out = Some(r[2]); q += 1; }
                else if let Some(c) = ctrl0 { if r[0] == 13 && fresh(r[3]) && ((r[1] == c && r[2] == top) || (r[2] == c && r[1] == top)) { out = Some(r[3]); q += 1; } } }
            MID.with(|m| m.set(q));
            for i in (0..n).rev() { let x = xs(i, &a); FAIL_AT.with(|f| f.set(q)); if !(g(q).map_or(false, |r| ccx(r, x, b[i], a[i])) && g(q + 1).map_or(false, |r| cx(r, a[i], x)) && g(q + 2).map_or(false, |r| cx(r, a[i], b[i]))) { { FAIL.with(|f| f.set(6)); return None; } } q += 3; }
            Some(Inst { kind: Kind::Sub, a, b, ctrl: ctrl0, ctrl2: None, out, start: p, end: q, mid: MID.with(|m| m.get()) }) }
        Up::Maj => {
            let top = a[n - 1];
            // i12: truncated top (a mod 2^n add whose top MAJ / UMA Toffoli pair the tree's peephole cancelled):
            // CX(a_t, b_t) [CX(a_t, x) CX(a_t, x)] CX(x, b_t) with x = the last carry lane a[n - 1]; the top bit joins the registers
            let mut trunc: Option<(u16, u16, Option<u16>)> = None;
            if let Some(r) = g(q) { let fresh = |y: u16| !(a.contains(&y) || b.contains(&y) || y == c0);
                if r[0] == 8 && r[3] == NONE { let (at, bt) = (r[1], r[2]);
                    if fresh(at) && fresh(bt) && at != bt {
                        if g(q + 1).map_or(false, |r| cx(r, at, top)) && g(q + 2).map_or(false, |r| cx(r, at, top)) && g(q + 3).map_or(false, |r| cx(r, top, bt)) { trunc = Some((at, bt, None)); q += 4; }
                        else if g(q + 1).map_or(false, |r| cx(r, top, bt)) { trunc = Some((at, bt, None)); q += 2; } } }
                else if r[0] == 13 { // controlled top (peephole-normalized): CCX(c, a_t, b_t) CCX(c, x, b_t)
                    let bt = r[3]; if let Some(r1) = g(q + 1) { if r1[0] == 13 && r1[3] == bt && (r1[1] == top || r1[2] == top) {
                        let c = if r1[1] == top { r1[2] } else { r1[1] }; if let Some(at) = ccx_other(r, c, bt) { if fresh(at) && fresh(bt) && fresh(c) && at != bt && at != c { trunc = Some((at, bt, Some(c))); q += 2; } } } } } }
            // optional top gate: CX(top, z) or CCX(c, top, z) with z (and c) outside the chain
            let mut out: Option<u16> = None; let mut tctl: Option<u16> = None;
            if trunc.is_none() { if let Some(r) = g(q) { let fresh = |x: u16| !(a.contains(&x) || b.contains(&x) || x == c0);
                if r[0] == 8 && r[1] == top && r[3] == NONE && fresh(r[2]) { out = Some(r[2]); q += 1; }
                else if r[0] == 13 && fresh(r[3]) && (r[1] == top || r[2] == top) { let c = if r[1] == top { r[2] } else { r[1] }; if fresh(c) { out = Some(r[3]); tctl = Some(c); q += 1; } } } }
            // descending: uma / umaC / majInv, decided at i = n - 1
            MID.with(|m| m.set(q)); let i0 = n - 1; let x0 = xs(i0, &a);
            if !(g(q).map_or(false, |r| ccx(r, x0, b[i0], a[i0])) && g(q + 1).map_or(false, |r| cx(r, a[i0], x0))) { { FAIL.with(|f| f.set(7)); return None; } }
            let r2 = g(q + 2)?;
            #[derive(Clone, Copy, PartialEq)] enum Dn { Uma, UmaC(u16), UmaC2(u16, u16, u16), MajInv }
            let inst_lane = |c: u16| a.contains(&c) || b.contains(&c) || c == c0;
            let dn = if cx(r2, x0, b[i0]) { Dn::Uma } else if cx(r2, a[i0], b[i0]) {
                    // umaC with a two-lane control c1 c2 on a dirty loan L: ccx(c, z, y) = CCX(c1, c2, L) CCX(z, L, y) CCX(c1, c2, L) CCX(z, L, y)
                    let c2 = match (g(q + 3), g(q + 4)) { (Some(r3), Some(r4)) if r3[0] == 13 && !inst_lane(r3[3]) && !inst_lane(r3[1]) && !inst_lane(r3[2]) && ccx(r4, a[i0], r3[3], b[i0]) => Some(Dn::UmaC2(r3[1], r3[2], r3[3])), _ => None };
                    if let Some(d) = c2 { d } else {
                    match (g(q + 3).and_then(|r| ccx_other(r, a[i0], b[i0])), g(q + 4)) { (Some(c), Some(r4)) if ccx(r4, c, x0, b[i0]) && !(a.contains(&c) || b.contains(&c) || c == c0) => Dn::UmaC(c), _ => Dn::MajInv } } }
                else { { FAIL.with(|f| f.set(8)); return None; } };
            for i in (0..n).rev() { let x = xs(i, &a); FAIL_AT.with(|f| f.set(q));
                let ok = match dn {
                    Dn::Uma => g(q).map_or(false, |r| ccx(r, x, b[i], a[i])) && g(q + 1).map_or(false, |r| cx(r, a[i], x)) && (g(q + 2).map_or(false, |r| cx(r, x, b[i])) || (i == 0 && x == c0)),
                    Dn::UmaC(c) => g(q).map_or(false, |r| ccx(r, x, b[i], a[i])) && g(q + 1).map_or(false, |r| cx(r, a[i], x)) && g(q + 2).map_or(false, |r| cx(r, a[i], b[i])) && g(q + 3).map_or(false, |r| ccx(r, c, a[i], b[i])) && g(q + 4).map_or(false, |r| ccx(r, c, x, b[i])),
                    Dn::UmaC2(c1, c2, l) => { let cc = |r: Option<&Row>| r.map_or(false, |r| ccx(r, c1, c2, l));
                        g(q).map_or(false, |r| ccx(r, x, b[i], a[i])) && g(q + 1).map_or(false, |r| cx(r, a[i], x)) && g(q + 2).map_or(false, |r| cx(r, a[i], b[i]))
                        && cc(g(q + 3)) && g(q + 4).map_or(false, |r| ccx(r, a[i], l, b[i])) && cc(g(q + 5)) && g(q + 6).map_or(false, |r| ccx(r, a[i], l, b[i]))
                        && cc(g(q + 7)) && g(q + 8).map_or(false, |r| ccx(r, x, l, b[i])) && cc(g(q + 9)) && g(q + 10).map_or(false, |r| ccx(r, x, l, b[i])) }
                    Dn::MajInv => g(q).map_or(false, |r| ccx(r, x, b[i], a[i])) && g(q + 1).map_or(false, |r| cx(r, a[i], x)) && g(q + 2).map_or(false, |r| cx(r, a[i], b[i])) };
                if !ok { { FAIL.with(|f| f.set(9)); return None; } }
                // i12: the last UMA's CX(c0, b0) is a no-op when c0 = 0 (restored by the CX before it); the tree's passes drop it
                let short = dn == Dn::Uma && i == 0 && x == c0 && !g(q + 2).map_or(false, |r| cx(r, x, b[i]));
                q += match dn { Dn::UmaC(_) => 5, Dn::UmaC2(..) => 11, _ => if short { 2 } else { 3 } }; }
            if let Some((at, bt, tc)) = trunc { let ok = match (dn, tc) { (Dn::Uma, None) => true, (Dn::UmaC(c), Some(c2)) => c == c2, _ => false };
                if !ok { FAIL.with(|f| f.set(95)); return None; } let mut a = a; let mut b = b; a.push(at); b.push(bt);
                return Some(Inst { kind: Kind::Add, a, b, ctrl: tc, ctrl2: None, out: None, start: p, end: q, mid: MID.with(|m| m.get()) }); }
            match dn {
                Dn::Uma => { if tctl.is_some() { { FAIL.with(|f| f.set(10)); return None; } } Some(Inst { kind: Kind::Add, a, b, ctrl: None, ctrl2: None, out, start: p, end: q, mid: MID.with(|m| m.get()) }) }
                Dn::UmaC(c) => { if tctl.is_some() && tctl != Some(c) { { FAIL.with(|f| f.set(11)); return None; } } Some(Inst { kind: Kind::Add, a, b, ctrl: Some(c), ctrl2: None, out, start: p, end: q, mid: MID.with(|m| m.get()) }) }
                Dn::UmaC2(c1, c2, _) => { if out.is_some() { FAIL.with(|f| f.set(97)); return None; } Some(Inst { kind: Kind::Add, a, b, ctrl: Some(c1), ctrl2: Some(c2), out: None, start: p, end: q, mid: MID.with(|m| m.get()) }) }
                Dn::MajInv => { match out { Some(f) => Some(Inst { kind: Kind::Carry, a, b, ctrl: tctl, ctrl2: None, out: Some(f), start: p, end: q, mid: MID.with(|m| m.get()) }),
                    // MAJ chain followed by its inverse with nothing in between: the identity (a comparison whose flag the tree's
                    // passes folded into a constant; the X that remains is kept by parse_x)
                    None => Some(Inst { kind: Kind::Ident, a, b, ctrl: None, ctrl2: None, out: None, start: p, end: q, mid: MID.with(|m| m.get()) }) } } } } }
}

// ---------------------------------------------------------------- ancilla-free emitters (the walk generator's UnitWalk.add / lt bodies)
struct E<'a> { o: &'a mut Vec<Row>, loan: u16 }
impl E<'_> {
    fn raw(&mut self, c: &[u16], t: u16) { match c.len() { 0 => self.o.push([6, t, NONE, NONE]), 1 => self.o.push([8, c[0], t, NONE]), 2 => self.o.push([13, c[0], c[1], t]),
        3 => { let l = self.loan; assert!(!c.contains(&l) && l != t); for _ in 0..2 { self.o.push([13, c[0], c[1], l]); self.o.push([13, c[2], l, t]); } } // dirty-loan Toffoli: t ^= c0 c1 c2
        _ => panic!("i12c0: more than three controls") } }
    fn cat(c: &[u16], x: &[u16]) -> Vec<u16> { let mut v = c.to_vec(); v.extend_from_slice(x); v }
    /// UnitWalk.add: b += [c] a mod 2^n, h ^= [c] carry
    fn add(&mut self, c: &[u16], a: &[u16], b: &[u16], h: Option<u16>) {
        let n = a.len(); let k = n - 1;
        if n == 1 { if let Some(h) = h { self.raw(&Self::cat(c, &[a[0], b[0]]), h); } self.raw(&Self::cat(c, &[a[0]]), b[0]); return; }
        for i in 1..n { self.raw(&[a[i]], b[i]); }
        if let Some(h) = h { self.raw(&Self::cat(c, &[a[k]]), h); }
        for i in (1..=n - 2).rev() { self.raw(&[a[i]], a[i + 1]); }
        for i in 0..n - 1 { self.raw(&[b[i], a[i]], a[i + 1]); }
        if let Some(h) = h { self.raw(&Self::cat(c, &[b[k], a[k]]), h); }
        self.raw(&Self::cat(c, &[a[k]]), b[k]);
        for i in (0..=n - 2).rev() { self.raw(&[b[i], a[i]], a[i + 1]); self.raw(&Self::cat(c, &[a[i]]), b[i]); }
        for i in 1..n - 1 { self.raw(&[a[i]], a[i + 1]); }
        for i in 1..n { self.raw(&[a[i]], b[i]); }
    }
    /// lt without its X(b) frame: h ^= [c] carry(a + b)
    fn carry(&mut self, c: &[u16], a: &[u16], b: &[u16], h: u16) {
        let n = a.len(); let k = n - 1;
        if n == 1 { self.raw(&Self::cat(c, &[a[0], b[0]]), h); return; }
        for i in 1..n { self.raw(&[a[i]], b[i]); }
        self.raw(&Self::cat(c, &[a[k]]), h);
        for i in (1..=n - 2).rev() { self.raw(&[a[i]], a[i + 1]); }
        for i in 0..n - 1 { self.raw(&[b[i], a[i]], a[i + 1]); }
        self.raw(&Self::cat(c, &[b[k], a[k]]), h);
        for i in (0..=n - 2).rev() { self.raw(&[b[i], a[i]], a[i + 1]); }
        for i in 1..n - 1 { self.raw(&[a[i]], a[i + 1]); }
        for i in 1..n { self.raw(&[a[i]], b[i]); }
    }
}
/// the ancilla-free replacement of an instance (loan: a lane the instance does not name; only used with 3 controls)
pub fn emit(inst: &Inst, loan: u16) -> Vec<Row> {
    let mut o: Vec<Row> = Vec::new(); let c: Vec<u16> = inst.ctrl.into_iter().chain(inst.ctrl2.into_iter()).collect();
    { let mut e = E { o: &mut o, loan };
      match inst.kind { Kind::Add => e.add(&c, &inst.a, &inst.b, inst.out), Kind::Carry => e.carry(&c, &inst.a, &inst.b, inst.out.unwrap()),
        Kind::Sub => { let s = e.o.len(); e.add(&c, &inst.a, &inst.b, inst.out); e.o[s..].reverse(); }
        Kind::Ident => {} } }   // inverse of (b += a, out ^= carry): b -= a, out ^= borrow
    o
}
fn lanes_of(rows: &[Row]) -> Vec<u16> { let mut v: Vec<u16> = Vec::new(); for r in rows { for j in 1..=qubits(r[0]) { if !v.contains(&r[j]) { v.push(r[j]); } } } v }
/// random-state check: original records vs replacement, all named lanes + the loan, c0 = 0 (256 states)
pub fn check(orig: &[Row], rep: &[Row], c0: u16, seed: u64) -> bool {
    let mut ls = lanes_of(orig); for l in lanes_of(rep) { if !ls.contains(&l) { ls.push(l); } }
    let idx = |l: u16| ls.iter().position(|&x| x == l).unwrap();
    let mut x = seed | 1; let mut nx = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    let init: Vec<[u64; 4]> = ls.iter().map(|&l| if l == c0 { [0; 4] } else { [nx(), nx(), nx(), nx()] }).collect();
    let run = |rows: &[Row]| -> Vec<[u64; 4]> { let mut s = init.clone();
        for r in rows { match r[0] { 6 => { let t = idx(r[1]); for w in 0..4 { s[t][w] = !s[t][w]; } } 8 => { let (c, t) = (idx(r[1]), idx(r[2])); for w in 0..4 { s[t][w] ^= s[c][w]; } }
            13 => { let (c1, c2, t) = (idx(r[1]), idx(r[2]), idx(r[3])); for w in 0..4 { s[t][w] ^= s[c1][w] & s[c2][w]; } } _ => panic!("i12c0: record kind {}", r[0]) } }
        s };
    run(orig) == run(rep)
}
pub struct Stats { pub found: usize, pub replaced: usize, pub rejected: usize, pub left: usize, pub rec_before: usize, pub rec_after: usize, pub dropped: usize,
    /// replaced instances: (old start, old end, new start, new end); first leftover positions (old)
    pub moves: Vec<(usize, usize, usize, usize)>, pub left_at: Vec<usize> }
/// parse at p with unconditioned X records skipped (the tree's passes move the X frame of a complemented operand next to the
/// lane's last / first use): returns the instance in ORIGINAL positions plus the replacement prefix / suffix X records, or None
/// when an X falls between two uses of its lane
pub fn parse_x(rows: &[Row], p: usize, c0: u16) -> Option<(Inst, Vec<Row>, Vec<Row>)> {
    let lim = (p + 8000).min(rows.len());
    let mut skip: Vec<usize> = Vec::new();   // ORIGINAL indices of foreign records (lanes disjoint from the instance) hoisted before it
    // one parse attempt with a skip set: Ok(instance) or Err((original index of the failure, partial instance lanes))
    let attempt = |skip: &Vec<usize>| -> Result<(Vec<usize>, Inst), (usize, Vec<usize>, Vec<u16>)> {
        let idx: Vec<usize> = (p..lim).filter(|&i| !(rows[i][0] == 6 && rows[i][2] == NONE) && !skip.contains(&i)).collect();
        let fil: Vec<Row> = idx.iter().map(|&i| rows[i]).collect();
        FAIL_AT.with(|f| f.set(usize::MAX));
        match parse(&fil, 0, c0) { Some(inst) => Ok((idx, inst)), None => { let at = FAIL_AT.with(|f| f.get()); let at = if at == usize::MAX { 0 } else { at };
            Err((idx.get(at).copied().unwrap_or(usize::MAX), idx, FAIL_LANES.with(|l| l.borrow().clone()))) } } };
    // greedy: skip the first foreign-looking record at the failure each time; if that fails, a small search (the candidate that
    // parses, else the one that gets furthest)
    let greedy = |mut skip: Vec<usize>| -> Option<(Vec<usize>, Vec<usize>, Inst)> { loop {
        match attempt(&skip) { Ok((idx, inst)) => return Some((skip, idx, inst)), Err((at, idx, lanes)) => {
            if at == usize::MAX || skip.len() >= 12 || FAIL_AT.with(|f| f.get()) == usize::MAX { return None; }
            let j0 = idx.iter().position(|&i| i == at)?;
            let cand = (j0..(j0 + 6).min(idx.len())).find(|&j| { let r = rows[idx[j]]; matches!(r[0], 8 | 13) && (r[0] != 8 || r[3] == NONE) && !(1..=qubits(r[0])).any(|k| lanes.contains(&r[k])) });
            match cand { Some(j) => skip.push(idx[j]), None => return None } } } } };
    let searched = |mut skip: Vec<usize>| -> Option<(Vec<usize>, Vec<usize>, Inst)> { loop {
        match attempt(&skip) { Ok((idx, inst)) => return Some((skip, idx, inst)), Err((at, idx, lanes)) => {
            if at == usize::MAX || skip.len() >= 12 || FAIL_AT.with(|f| f.get()) == usize::MAX { return None; }
            let j0 = idx.iter().position(|&i| i == at)?;
            let mut best: Option<(usize, usize)> = None; let mut done: Option<Vec<usize>> = None;
            let fc = FAIL_CTRL.with(|f| f.get());
            let foreign = |j: usize| { let r = rows[idx[j]]; matches!(r[0], 8 | 13) && (r[0] != 8 || r[3] == NONE) && !(1..=qubits(r[0])).any(|k| lanes.contains(&r[k]) && r[k] != fc) };
            // blocks of 1..3 consecutive foreign records (a 3-CX swap of two parked lanes inside a step)
            for j in j0..(j0 + 8).min(idx.len()) { for k in 1..=3usize { if j + k > idx.len() || !(j..j + k).all(|q| foreign(q)) { break; }
                let mut sk = skip.clone(); for q in j..j + k { sk.push(idx[q]); }
                match attempt(&sk) { Ok(_) => { done = Some(sk); break; } Err((at2, _, _)) => { if at2 != usize::MAX && best.map_or(true, |b| at2 > b.0) { best = Some((at2, j * 4 + k)); } } } }
                if done.is_some() { break; } }
            if let Some(sk) = done { skip = sk; continue; }
            match best { Some((at2, jk)) if at2 > at => { let (j, k) = (jk / 4, jk % 4); for q in j..j + k { skip.push(idx[q]); } } _ => return None } } } } };
    let (sk, idx, mut inst) = match greedy(Vec::new()) { Some(x) => x, None => searched(Vec::new())? };
    skip = sk;
    // the hoisted records must not name any lane of the instance (they commute with it); checked again by the random test
    let named_inst: Vec<u16> = idx[inst.start..inst.end].iter().flat_map(|&i| (1..=qubits(rows[i][0])).map(move |j| rows[i][j])).collect();
    let mut hoist: Vec<Row> = Vec::new();
    // (a hoisted record may name an instance lane that the instance does not touch before the record's position, e.g. the
    // move that clears a carry-out lane; the random check of the replacement decides)
    let _ = &named_inst;
    for &i in skip.iter() { let r = rows[i]; if i >= idx[inst.start] && i < idx[inst.end - 1] { if (1..=qubits(r[0])).any(|k| r[k] == c0) { FAIL.with(|f| f.set(98)); return None; } } }
    // place each skipped record by the instance lanes it names: none -> before the replacement; after the last instance use of
    // every such lane -> after it; before the first use -> before it; otherwise the instance is not converted
    let mut tail: Vec<Row> = Vec::new();
    { let mut sk = skip.clone(); sk.sort();
      for &i in sk.iter() { if !(i > idx[inst.start] && i < idx[inst.end - 1]) { continue; } let r = rows[i];
        let ls: Vec<u16> = (1..=qubits(r[0])).map(|k| r[k]).filter(|l| named_inst.contains(l)).collect();
        if ls.is_empty() { hoist.push(r); continue; }
        let uses: Vec<usize> = idx[inst.start..inst.end].iter().copied().filter(|&j| (1..=qubits(rows[j][0])).any(|k| ls.contains(&rows[j][k]))).collect();
        if i > *uses.last().unwrap() { tail.push(r); } else if i < uses[0] { hoist.push(r); } else { FAIL.with(|f| f.set(96)); return None; } } }
    let (s, e) = (idx[inst.start], idx[inst.end - 1] + 1);
    let named: Vec<(usize, u16)> = idx[inst.start..inst.end].iter().flat_map(|&i| (1..=qubits(rows[i][0])).map(move |j| (i, rows[i][j]))).collect();
    let (mut pre, mut post) = (hoist, Vec::new());
    for i in s..e { let r = rows[i]; if !(r[0] == 6 && r[2] == NONE) { continue; } let l = r[1];
        let uses: Vec<usize> = named.iter().filter(|x| x.1 == l).map(|x| x.0).collect();
        if uses.is_empty() || i < uses[0] { pre.push(r); } else if i > *uses.last().unwrap() { post.push(r); } else { FAIL.with(|f| f.set(99)); return None; } }
    inst.start = s; inst.end = e;
    let mut post2 = tail; post2.extend(post);
    Some((inst, pre, post2))
}
/// replace every parsable c0 instance inside the ranges [s, e) of `rows`; returns the new rows and statistics.  `loans`: candidate
/// lanes for the dirty-loan Toffolis (the first one the instance does not name is used)
pub fn convert(rows: &[Row], ranges: &[(usize, usize)], c0: u16, loans: &[u16]) -> (Vec<Row>, Stats) {
    let mut o: Vec<Row> = Vec::with_capacity(rows.len() + rows.len() / 8);
    let mut st = Stats { found: 0, replaced: 0, rejected: 0, left: 0, rec_before: 0, rec_after: 0, dropped: 0, moves: Vec::new(), left_at: Vec::new() };
    let inr = |i: usize| ranges.iter().any(|&(s, e)| i >= s && i < e);
    let mut i = 0usize;
    // c0 is 0 after a converted instance (qkit's clean carry-in, restored) until a record writes it: a record that only READS c0
    // in that state acts as the identity and is dropped (CX(c0, t), CCX(c0, x, t))
    let mut zero = false;
    while i < rows.len() {
        let r = rows[i];

        // an instance starts at a record that names c0 (CX(a0, c0) of maj, CX(c0, b0) of umaInv, CCX(ctrl, c0, b0) of umaCInv) or one before it (CX(a0, b0) of maj)
        if inr(i) {
            let cand = if r[0] == 8 && r[3] == NONE && i + 1 < rows.len() && rows[i + 1][0] == 8 && rows[i + 1][2] == c0 && r[1] == rows[i + 1][1] { true }
                else { r[0] == 8 && r[1] == c0 || r[0] == 13 && (r[1] == c0 || r[2] == c0) && r[3] != c0 };
            if cand { if let Some((inst, pre, post)) = parse_x(rows, i, c0) {
                st.found += 1; let orig = &rows[inst.start..inst.end]; let named = lanes_of(orig);
                let loan = *loans.iter().find(|&&l| !named.contains(&l) && l != c0).expect("i12c0: no loan");
                let mut rep = pre; rep.extend(emit(&inst, loan)); rep.extend(post);
                if check(orig, &rep, c0, 0x9E37_79B9 ^ i as u64) { st.replaced += 1; st.rec_before += orig.len(); st.rec_after += rep.len(); st.moves.push((inst.start, inst.end, o.len(), o.len() + rep.len())); o.extend_from_slice(&rep); i = inst.end; zero = true; continue; }
                st.rejected += 1; } }
            if zero && (1..=qubits(r[0])).any(|j| r[j] == c0) {
                let reads_only = match r[0] { 8 => r[1] == c0 && r[2] != c0 && r[3] == NONE, 13 => (r[1] == c0 || r[2] == c0) && r[3] != c0, _ => false };
                if reads_only { st.dropped += 1; i += 1; continue; } else { zero = false; } }
            if (1..=qubits(r[0])).any(|j| r[j] == c0) { st.left += 1; if st.left_at.len() < 200000 { st.left_at.push(i); } }
        }
        o.push(r); i += 1;
    }
    (o, st)
}

/// debugging aid: how far the parse gets at p (ascending steps) and the rows there
pub fn diagnose(rows: &[Row], p: usize, c0: u16) -> String {
    FAIL.with(|f| f.set(0)); let r = parse_x(rows, p, c0);
    format!("{} (fail tag {}) | rows {:?}", if r.is_some() { "parses" } else { "no parse" }, FAIL.with(|f| f.get()), &rows[p..(p + 6).min(rows.len())])
}

/// i12: cancel adjacent identical X / CX / CCX records (CCX controls unordered), iterated (a stack pass); exact.  Only inside [s, e).
pub fn cancel_adjacent(rows: &[Row], s: usize, e: usize) -> Vec<Row> {
    let same = |a: &Row, b: &Row| a[0] == b[0] && match a[0] { 13 => a[3] == b[3] && ((a[1] == b[1] && a[2] == b[2]) || (a[1] == b[2] && a[2] == b[1])), 6 => a[1] == b[1] && a[2] == NONE && b[2] == NONE, 8 => a[1] == b[1] && a[2] == b[2] && a[3] == NONE && b[3] == NONE, _ => false };
    let mut out: Vec<Row> = Vec::with_capacity(rows.len()); out.extend_from_slice(&rows[..s]); let base = out.len();
    for r in &rows[s..e] { if out.len() > base && same(out.last().unwrap(), r) { out.pop(); } else { out.push(*r); } }
    out.extend_from_slice(&rows[e..]); out
}

/// i12: second pass for c0 instances the parser does not recognise (the dirty-controlled forms of ITEM 12's phase B): an instance
/// starts at a MAJ start CX(a0, b0) CX(a0, c0) CCX(c0, b0, a0) (optionally preceded by dirty-control blocks naming b0) and ends
/// after the record that restores c0 (CX(a0, c0) after CCX(c0, b0, a0), plus CX(c0, b0) when present).  Registers = the MAJ
/// triples CX(A, B) CX(A, X) CCX(X, B, A) in order (+ the top pair CX(a_t, b_t) that follows them); controls = the pair of the
/// CCX(c1, c2, L) records inside.  Candidates add / sub (b +- [c1 c2] a mod 2^n, n = chain or chain + top) are emitted with the
/// ancilla-free adder and accepted only if equal to the instance on random states (c0 = 0); otherwise the instance is left.
pub fn convert2(rows: &[Row], range: (usize, usize), c0: u16, loans: &[u16]) -> (Vec<Row>, Stats) {
    let mut o: Vec<Row> = Vec::with_capacity(rows.len() + rows.len() / 16);
    let mut st = Stats { found: 0, replaced: 0, rejected: 0, left: 0, rec_before: 0, rec_after: 0, dropped: 0, moves: Vec::new(), left_at: Vec::new() };
    let names = |r: &Row, l: u16| (1..=qubits(r[0])).any(|j| r[j] == l);
    let mut i = 0usize;
    while i < rows.len() {
        let r = rows[i];
        if i >= range.0 && i + 2 < range.1 && r[0] == 8 && r[3] == NONE && cx(&rows[i + 1], r[1], c0) && ccx(&rows[i + 2], c0, r[2], r[1]) {
            let (a0, b0) = (r[1], r[2]);
            // end: first CCX(c0, b0, a0) CX(a0, c0) after i + 2
            let mut e = usize::MAX; let mut q = i + 3;
            while q + 1 < range.1.min(i + 20000) { if ccx(&rows[q], c0, b0, a0) && cx(&rows[q + 1], a0, c0) { e = q + 2; if q + 2 < rows.len() && cx(&rows[q + 2], c0, b0) { e += 1; } break; } q += 1; }
            // start: back over dirty-control blocks naming b0 or the loan (records already emitted are in `o`)
            if e != usize::MAX {
                let mut s = i; let mut e = e; while s >= 3 && s - 3 >= range.0 && rows[s - 3][0] == 13 && rows[s - 2][0] == 13 && rows[s - 1] == rows[s - 3] && (rows[s - 1][3] == b0) { s -= 3; }
                // registers
                let mut a: Vec<u16> = vec![a0]; let mut b: Vec<u16> = vec![b0]; let mut x = a0;
                let mut k = i + 3;
                while k + 2 < e { let r0 = rows[k]; if r0[0] == 8 && r0[3] == NONE && cx(&rows[k + 1], r0[1], x) && ccx(&rows[k + 2], x, r0[2], r0[1]) && !a.contains(&r0[1]) && !b.contains(&r0[2]) { a.push(r0[1]); b.push(r0[2]); x = r0[1]; k += 3; } else { k += 1; } }
                // top pair: the first CX(a_t, b_t) after the chain with fresh lanes
                let mut top: Option<(u16, u16)> = None;
                for kk in i..e { let r0 = rows[kk]; if r0[0] == 8 && r0[3] == NONE && !a.contains(&r0[1]) && !b.contains(&r0[2]) && !a.contains(&r0[2]) && !b.contains(&r0[1]) && r0[1] != c0 && r0[2] != c0 {
                    if rows[i..e].iter().any(|z| z[0] == 13 && (z[1] == x || z[2] == x) && z[3] == r0[2]) || rows[i..e].iter().any(|z| cx(z, x, r0[2])) { top = Some((r0[1], r0[2])); break; } } }
                // controls
                let mut cc: std::collections::HashMap<(u16, u16, u16), usize> = std::collections::HashMap::new();
                for z in &rows[s..e] { if z[0] == 13 && !a.contains(&z[3]) && !b.contains(&z[3]) && z[3] != c0 { *cc.entry((z[1].min(z[2]), z[1].max(z[2]), z[3])).or_default() += 1; } }
                let ctrl: Option<(u16, u16)> = cc.iter().max_by_key(|x| x.1).map(|(k, _)| (k.0, k.1));
                // the shared dirty-AND toggles CCX(c1, c2, L) of neighbouring blocks: include a lone one right before s / at e
                if let Some((c1, c2)) = ctrl { if s > range.0 && rows[s - 1][0] == 13 && ((rows[s - 1][1] == c1 && rows[s - 1][2] == c2) || (rows[s - 1][1] == c2 && rows[s - 1][2] == c1)) && i - s < 64 { s -= 1; }
                    if e < range.1 && rows[e][0] == 13 && ((rows[e][1] == c1 && rows[e][2] == c2) || (rows[e][1] == c2 && rows[e][2] == c1)) { e += 1; } }
                st.found += 1;
                if st.found == 1 && std::env::var("C0DBG").is_ok() { eprintln!("convert2 first instance [{s}, {e}) a {} {:?}..{:?} b {:?}..{:?} top {:?} ctrl {:?}", a.len(), &a[..3], &a[a.len() - 3..], &b[..3], &b[b.len() - 3..], top, ctrl); }
                let orig = &rows[s..e]; let named = lanes_of(orig);
                let loan = *loans.iter().find(|&&l| !named.contains(&l) && l != c0).expect("i12c0: no loan");
                let mut done = false;
                let regs: Vec<(Vec<u16>, Vec<u16>)> = { let mut v = vec![(a.clone(), b.clone())]; if let Some((at, bt)) = top { let mut a2 = a.clone(); a2.push(at); let mut b2 = b.clone(); b2.push(bt); v.insert(0, (a2, b2)); } v };
                'cand: for (ra, rb) in regs.iter() { for kind in [Kind::Add, Kind::Sub] { for cs in [ctrl, None] { for xr in 0..3u8 {
                    let inst = Inst { kind, a: ra.clone(), b: rb.clone(), ctrl: cs.map(|c| c.0), ctrl2: cs.map(|c| c.1), out: None, start: s, end: e, mid: 0 };
                    // xr: 0 = plain, 1 = then b ^= a (the tree's form keeps the sum XOR-ed with a), 2 = b ^= a first
                    let xo: Vec<Row> = ra.iter().zip(rb.iter()).map(|(&x, &y)| [8, x, y, NONE]).collect();
                    let mut rep: Vec<Row> = Vec::new(); if xr == 2 { rep.extend_from_slice(&xo); } rep.extend(emit(&inst, loan)); if xr == 1 { rep.extend_from_slice(&xo); }
                    if st.found == 1 && std::env::var("C0DBG").is_ok() { eprintln!("  cand n {} kind {:?} ctrl {:?} xr {}: check {}", ra.len(), kind, cs, xr, check(orig, &rep, c0, 0x5EED_1234 ^ s as u64)); }
                    if check(orig, &rep, c0, 0x5EED_1234 ^ s as u64) && check(orig, &rep, c0, 0xA5A5_0F0F ^ (s as u64).rotate_left(17)) {
                        // drop what `o` already holds of the prefix (s < i: those records were pushed)
                        let pushed = i - s; for _ in 0..pushed { o.pop(); }
                        st.replaced += 1; st.rec_before += orig.len(); st.rec_after += rep.len(); st.moves.push((s, e, o.len(), o.len() + rep.len())); o.extend_from_slice(&rep); i = e; done = true; break 'cand; } } } } }
                if done { continue; }
                st.rejected += 1;
            }
        }
        if i >= range.0 && i < range.1 && names(&r, c0) { st.left += 1; if st.left_at.len() < 200000 { st.left_at.push(i); } }
        o.push(r); i += 1;
    }
    (o, st)
}

/// i12: third pass (instances whose MAJ start lacks the leading CX(a0, b0) or that carry a single control): start CX(a0, c0)
/// CCX(c0, b0, a0); the records just before it that target b0 are included; end after CCX(c0, b0, a0) CX(a0, c0) (+ CX(c0 | a0,
/// b0)); registers from the 2- or 3-record MAJ steps; candidates add / sub x controls (single lane, dirty pair, none) x XOR
/// frames (none, all bits after / before, bit 0 after / before), accepted only on an exact random-state match (two seeds).
pub fn convert3(rows: &[Row], range: (usize, usize), c0: u16, loans: &[u16]) -> (Vec<Row>, Stats) {
    let mut o: Vec<Row> = Vec::with_capacity(rows.len() + rows.len() / 16);
    let mut st = Stats { found: 0, replaced: 0, rejected: 0, left: 0, rec_before: 0, rec_after: 0, dropped: 0, moves: Vec::new(), left_at: Vec::new() };
    let names = |r: &Row, l: u16| (1..=qubits(r[0])).any(|j| r[j] == l);
    let mut i = 0usize; let mut writes = 0usize;
    while i < rows.len() {
        let r = rows[i];
        if i >= range.0 && i + 1 < range.1 && writes % 2 == 0 && r[0] == 8 && r[3] == NONE && r[2] == c0 && r[1] != c0 && rows[i + 1][0] == 13 && rows[i + 1][3] == r[1] && (rows[i + 1][1] == c0 || rows[i + 1][2] == c0) {
            let a0 = r[1]; let b0 = if rows[i + 1][1] == c0 { rows[i + 1][2] } else { rows[i + 1][1] };
            let mut e = usize::MAX; let mut q = i + 2;
            while q + 1 < range.1.min(i + 20000) { if ccx(&rows[q], c0, b0, a0) && cx(&rows[q + 1], a0, c0) { e = q + 2; break; } q += 1; }
            if e != usize::MAX {
                let mut ends = vec![e]; let mut ee = e; while ee < range.1 && ee < e + 3 && matches!(rows[ee][0], 8 | 13) && rows[ee][qubits(rows[ee][0])] == b0 { ee += 1; ends.push(ee); }
                let mut s = i; while s > range.0 && i - s < 6 && matches!(rows[s - 1][0], 8 | 13) && rows[s - 1][qubits(rows[s - 1][0])] == b0 { s -= 1; }
                let mut starts = vec![i]; if s < i { starts.push(s); }
                let mut a: Vec<u16> = vec![a0]; let mut b: Vec<u16> = vec![b0]; let mut x = a0; let mut k = i + 2;
                while k + 1 < e { let r0 = rows[k]; if r0[0] == 8 && r0[3] == NONE && r0[2] == x && !a.contains(&r0[1]) && rows[k + 1][0] == 13 && rows[k + 1][3] == r0[1] && (rows[k + 1][1] == x || rows[k + 1][2] == x) {
                        let bb = if rows[k + 1][1] == x { rows[k + 1][2] } else { rows[k + 1][1] }; if !b.contains(&bb) && bb != c0 { a.push(r0[1]); b.push(bb); x = r0[1]; k += 2; continue; } } k += 1; }
                let mut top: Option<(u16, u16)> = None;
                for kk in i..e { let r0 = rows[kk]; if r0[0] == 8 && r0[3] == NONE && !a.contains(&r0[1]) && !b.contains(&r0[2]) && !a.contains(&r0[2]) && !b.contains(&r0[1]) && r0[1] != c0 && r0[2] != c0 {
                    if rows[i..e].iter().any(|z| z[0] == 13 && (z[1] == x || z[2] == x) && z[3] == r0[2]) || rows[i..e].iter().any(|z| cx(z, x, r0[2])) { top = Some((r0[1], r0[2])); break; } } }
                let mut sc: std::collections::HashMap<u16, usize> = std::collections::HashMap::new(); let mut pc: std::collections::HashMap<(u16, u16), usize> = std::collections::HashMap::new();
                for z in &rows[s..e] { if z[0] == 13 { let t = z[3];
                    if b.contains(&t) { for (c, y) in [(z[1], z[2]), (z[2], z[1])] { if !a.contains(&c) && !b.contains(&c) && c != c0 && (a.contains(&y) || y == c0) { *sc.entry(c).or_default() += 1; } } }
                    else if !a.contains(&t) && t != c0 { *pc.entry((z[1].min(z[2]), z[1].max(z[2]))).or_default() += 1; } } }
                // carry / borrow-out candidates: lanes the instance writes outside the registers (besides c0)
                let mut outs: Vec<Option<u16>> = vec![None];
                { let mut oc: std::collections::HashMap<u16, usize> = std::collections::HashMap::new();
                  for z in &rows[i..e] { let tg = z[qubits(z[0])]; if matches!(z[0], 8 | 13) && !a.contains(&tg) && !b.contains(&tg) && tg != c0 { *oc.entry(tg).or_default() += 1; } }
                  let mut v: Vec<(u16, usize)> = oc.into_iter().collect(); v.sort_by_key(|x| std::cmp::Reverse(x.1)); for (l, _) in v.into_iter().take(2) { outs.push(Some(l)); } }
                let mut ctrls: Vec<Option<(u16, Option<u16>)>> = vec![None];
                if let Some((&c, _)) = sc.iter().max_by_key(|x| x.1) { ctrls.insert(0, Some((c, None))); }
                if let Some((&(c1, c2), _)) = pc.iter().max_by_key(|x| x.1) { ctrls.insert(0, Some((c1, Some(c2)))); }
                st.found += 1;
                let regs: Vec<(Vec<u16>, Vec<u16>)> = { let mut v = vec![(a.clone(), b.clone())]; if let Some((at, bt)) = top { let mut a2 = a.clone(); a2.push(at); let mut b2 = b.clone(); b2.push(bt); v.insert(0, (a2, b2)); } v };
                let mut done = false;
                'cand: for &ss in &starts { for &ee2 in &ends { let orig = &rows[ss..ee2]; let named = lanes_of(orig);
                    let loan = match loans.iter().find(|&&l| !named.contains(&l) && l != c0) { Some(&l) => l, None => continue };
                    for (ra, rb) in regs.iter() { for kind in [Kind::Add, Kind::Sub] { for cs in ctrls.iter() { for &ou in outs.iter() { for xr in 0..5u8 {
                        if ou.map_or(false, |l| ra.contains(&l) || rb.contains(&l) || cs.map_or(false, |c| c.0 == l || c.1 == Some(l))) { continue; }
                        if ou.is_some() && cs.map_or(false, |c| c.1.is_some()) { continue; }   // the emitter takes at most three controls
                        let inst = Inst { kind, a: ra.clone(), b: rb.clone(), ctrl: cs.map(|c| c.0), ctrl2: cs.and_then(|c| c.1), out: ou, start: ss, end: ee2, mid: 0 };
                        let xo: Vec<Row> = ra.iter().zip(rb.iter()).map(|(&x, &y)| [8, x, y, NONE]).collect(); let x0: Vec<Row> = vec![[8, ra[0], rb[0], NONE]];
                        let mut rep: Vec<Row> = Vec::new(); if xr == 2 { rep.extend_from_slice(&xo); } if xr == 4 { rep.extend_from_slice(&x0); }
                        rep.extend(emit(&inst, loan)); if xr == 1 { rep.extend_from_slice(&xo); } if xr == 3 { rep.extend_from_slice(&x0); }
                        if check(orig, &rep, c0, 0x5EED_1234 ^ ss as u64) && check(orig, &rep, c0, 0xA5A5_0F0F ^ (ss as u64).rotate_left(17)) {
                            for _ in 0..(i - ss) { o.pop(); }
                            st.replaced += 1; st.rec_before += orig.len(); st.rec_after += rep.len(); st.moves.push((ss, ee2, o.len(), o.len() + rep.len())); o.extend_from_slice(&rep); i = ee2; done = true; break 'cand; } } } } } } } }
                if done { continue; }
                st.rejected += 1;
            }
        }
        if i >= range.0 && i < range.1 && names(&r, c0) { st.left += 1; if st.left_at.len() < 200000 { st.left_at.push(i); } if matches!(r[0], 6 | 8 | 13) && r[qubits(r[0])] == c0 { writes += 1; } }
        o.push(r); i += 1;
    }
    (o, st)
}
