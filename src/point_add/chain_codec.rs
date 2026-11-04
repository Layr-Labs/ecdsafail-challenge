//! A2: exact chained base-243 codec for idle P5 tape groups.
//!
//! A P5 group holds 5 trits (243 valid codes) in 8 wires; 13 codes per group are unused. The chain pools that
//! slack: state x (w wires) and the next group's digit d = pi(code) in [0,243) form Y = 243*x + d; the group keeps
//! 8 wires holding b = Y mod 256 and the state becomes x' = Y >> 8, whose bound shrinks by ~243/256 per group. When
//! the bound falls to a power of two the top state wire is provably zero and is freed. Pop (unmerge) is in-place
//! restoring division of Y by 243; push is its exact inverse.
use super::*;
use super::super::super::const_arith::csub_const_trunc;
use crate::circuit::{Op, OperationType as K, NO_BIT};

/// Letter value of trit v in the walk's (typ, s) encoding (codec_probe convention).
fn letter(v: usize) -> (bool, bool) {
    let h = v == 2;
    let l = v == 1;
    (true ^ h ^ l, h)
}

// ---------------------------------------------------------------------------------------------------------------
// Configuration

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.trim().parse().ok()).unwrap_or(default)
}
/// `SQ_A2_CHAINS` chains of `SQ_A2_LEN` consecutive groups starting at group `SQ_A2_FIRST`. Off by default.
fn chain_of(g: usize) -> Option<(usize, usize)> {
    let (n, len, first) = (env_usize("SQ_A2_CHAINS", 0), env_usize("SQ_A2_LEN", 14), env_usize("SQ_A2_FIRST", 0));
    if n == 0 || g < first || g - first >= n * len {
        return None;
    }
    let cid = (g - first) / len;
    Some((cid, first + cid * len))
}

/// Number of wires holding values in [0, x).
pub fn nbits(x: u64) -> usize {
    assert!(x >= 2);
    (64 - (x - 1).leading_zeros()) as usize
}
/// State bound after one push: x' = (243 x + d) >> 8 over x < X, d < 243.
pub fn next_bound(x: u64) -> u64 {
    ((243 * (x - 1) + 242) >> 8) + 1
}

pub(super) struct Chain {
    pub base: usize,
    pub top: usize,
    /// State wires, LSB first (`nbits(bound)` of them).
    pub state: Vec<QubitId>,
    /// Bound history: `bounds.last()` is the current state bound.
    pub bounds: Vec<u64>,
}

// ---------------------------------------------------------------------------------------------------------------
// The digit map: P5 code (wire i = code bit i, order a2 a1 a0 h3 l3 b2 b1 b0) -> binary digit < 243, with the 13
// unused codes onto 243..255. The code set depends on the P3 codec:
// - synthesized P3 (HEO_CODEC_SYNTH, the production recipe): unused {15,47,79,111,127,143,175,207,239,249,251,253,
//   255}. Controlled by code bit 4 swap wire pairs (1,5), (2,6); digit = [w6, w5, w7, ~w4, w0, w1, w2, w3]. 2 CCX.
// - pair-pack P3: unused {30,62,94,126,158,190,222,223,249,251,253,254,255}. Controlled by code bit 0 swap (1,5),
//   (2,6), (1,7); digit = [w6, w5, w7, ~w0, w1, w2, w3, w4]. 3 CCX.
// No scratch either way.

fn synth_codes() -> bool {
    truthy("HEO_CODEC_SYNTH")
}
pub(super) fn digit_wires(code: [QubitId; 8]) -> [QubitId; 8] {
    if synth_codes() {
        [code[6], code[5], code[7], code[4], code[0], code[1], code[2], code[3]]
    } else {
        [code[6], code[5], code[7], code[0], code[1], code[2], code[3], code[4]]
    }
}
pub(super) fn code_wires(d: [QubitId; 8]) -> [QubitId; 8] {
    if synth_codes() {
        [d[4], d[5], d[6], d[7], d[3], d[1], d[0], d[2]]
    } else {
        [d[3], d[4], d[5], d[6], d[7], d[1], d[0], d[2]]
    }
}
pub(super) fn pi_fwd(c: &mut Builder, w: [QubitId; 8]) -> [QubitId; 8] {
    if synth_codes() {
        fredkin(c, w[4], w[1], w[5]);
        fredkin(c, w[4], w[2], w[6]);
        c.x(w[4]);
    } else {
        fredkin(c, w[0], w[1], w[5]);
        fredkin(c, w[0], w[2], w[6]);
        fredkin(c, w[0], w[1], w[7]);
        c.x(w[0]);
    }
    digit_wires(w)
}
pub(super) fn pi_inv(c: &mut Builder, d: [QubitId; 8]) -> [QubitId; 8] {
    let w = code_wires(d);
    if synth_codes() {
        c.x(w[4]);
        fredkin(c, w[4], w[2], w[6]);
        fredkin(c, w[4], w[1], w[5]);
    } else {
        c.x(w[0]);
        fredkin(c, w[0], w[1], w[7]);
        fredkin(c, w[0], w[2], w[6]);
        fredkin(c, w[0], w[1], w[5]);
    }
    w
}

// ---------------------------------------------------------------------------------------------------------------
// One chain step. Register R = d (8 wires, low) ++ state (w wires, high). Pop is restoring division by 243 in place:
// for j = w-1 .. 0 the 9-bit window Z = R[j..j+9] (< 486 by the invariant R < 243 * 2^(j+1)) becomes
// Z + 13 [Z >= 243], i.e. Z - 243 with the quotient bit in window bit 8. That is: add 13 to the window, then subtract
// 13 from its low 8 bits unless window bit 8 is set. Push runs the inverse steps j = 0 .. w-1.

/// Push: (x < bound, d < 243) -> state x' = (243 x + d) >> 8, d's wires hold (243 x + d) & 255. Returns the new bound.
pub(super) fn push_step(c: &mut Builder, d: [QubitId; 8], state: &mut Vec<QubitId>, bound: u64) -> u64 {
    let w = nbits(bound);
    assert_eq!(state.len(), w, "chain state width");
    let mut r: Vec<QubitId> = d.to_vec();
    r.extend(state.iter().copied());
    let k13 = U256::from(13u64);
    for j in 0..w {
        let top = r[j + 8];
        c.x(top);
        cadd_const_trunc(c, &r[j..j + 8], k13, top, false);
        c.x(top);
        sub_const(c, &r[j..j + 9], k13);
    }
    let nb = next_bound(bound);
    let w2 = nbits(nb);
    assert!(w2 <= w && w2 + 1 >= w);
    if w2 < w {
        c.free(r[w + 7]);
        r.truncate(w + 7);
    }
    *state = r[8..].to_vec();
    nb
}

/// Pop: exact inverse of `push_step` (state bound `now` back to `prev`).
pub(super) fn pop_step(c: &mut Builder, d: [QubitId; 8], state: &mut Vec<QubitId>, now: u64, prev: u64) {
    assert_eq!(next_bound(prev), now);
    let (w2, w) = (nbits(now), nbits(prev));
    assert_eq!(state.len(), w2, "chain state width");
    let mut r: Vec<QubitId> = d.to_vec();
    r.extend(state.iter().copied());
    if w > w2 {
        r.push(c.alloc_qubit());
    }
    let k13 = U256::from(13u64);
    for j in (0..w).rev() {
        add_const(c, &r[j..j + 9], k13);
        let top = r[j + 8];
        c.x(top);
        csub_const_trunc(c, &r[j..j + 8], k13, top);
        c.x(top);
    }
    *state = r[8..].to_vec();
}

impl Tape {
    /// After group g reached P5 in a forward leg: start or extend its chain.
    pub(super) fn chain_push(&mut self, c: &mut Builder, g: usize) {
        let Some((cid, base)) = chain_of(g) else { return };
        let grp = self.groups[g].as_mut().unwrap();
        assert_eq!(grp.state, GState::P5);
        let code = [grp.a2, grp.a1, grp.a0, grp.h3, grp.l3, grp.b2, grp.b1, grp.b0];
        let d = pi_fwd(c, code);
        if g == base {
            assert!(self.chains[cid].is_none());
            self.chains[cid] = Some(Chain { base, top: g, state: d.to_vec(), bounds: vec![243] });
            grp.state = GState::ChainBase;
        } else {
            let ch = self.chains[cid].as_mut().expect("chain base not pushed");
            assert_eq!(ch.top + 1, g, "chain push out of order");
            let x = *ch.bounds.last().unwrap();
            let nb = push_step(c, d, &mut ch.state, x);
            ch.bounds.push(nb);
            ch.top = g;
            grp.state = GState::Chained;
        }
        if std::env::var_os("SQ_A2_TRACE").is_some() {
            let ch = self.chains[cid].as_ref().unwrap();
            eprintln!("SQ_A2 push g={g} chain={cid} bound={} wires={} live={}", ch.bounds.last().unwrap(), ch.state.len(), c.active_qubits());
        }
    }

    /// Pop chain entries until group g is a plain P5 group again (LIFO; the walk reads groups top-down).
    pub(super) fn unchain(&mut self, c: &mut Builder, g: usize) {
        let (cid, _) = chain_of(g).expect("unchain: group not in a chain");
        loop {
            let ch = self.chains[cid].as_mut().expect("unchain: no chain");
            let top = ch.top;
            assert!(top >= g, "unchain below the chain top");
            if top == ch.base {
                let ch = self.chains[cid].take().unwrap();
                assert_eq!(ch.bounds, vec![243]);
                let code = pi_inv(c, ch.state.try_into().unwrap());
                let grp = self.groups[top].as_mut().unwrap();
                assert_eq!(grp.state, GState::ChainBase);
                [grp.a2, grp.a1, grp.a0, grp.h3, grp.l3, grp.b2, grp.b1, grp.b0] = code;
                grp.state = GState::P5;
            } else {
                let now = ch.bounds.pop().unwrap();
                let prev = *ch.bounds.last().unwrap();
                let grp = self.groups[top].as_mut().unwrap();
                assert_eq!(grp.state, GState::Chained);
                let d = digit_wires([grp.a2, grp.a1, grp.a0, grp.h3, grp.l3, grp.b2, grp.b1, grp.b0]);
                pop_step(c, d, &mut ch.state, now, prev);
                pi_inv(c, d);
                grp.state = GState::P5;
                ch.top = top - 1;
            }
            if std::env::var_os("SQ_A2_TRACE").is_some() {
                eprintln!("SQ_A2 pop g={top} chain={cid} live={}", c.active_qubits());
            }
            if top == g {
                return;
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Exhaustive gate-level selftests (formal measurement variables: every HMR outcome is an independent symbol, so a
// zero final phase holds on every measurement branch).

/// Phase as an XOR of formal symbols; bit 0 is the constant -1.
#[derive(Clone, Default, PartialEq, Debug)]
struct Phase(Vec<u64>);
impl Phase {
    fn flip(&mut self, sym: usize) {
        let (w, b) = (sym / 64, sym % 64);
        if self.0.len() <= w {
            self.0.resize(w + 1, 0);
        }
        self.0[w] ^= 1 << b;
    }
    fn is_zero(&self) -> bool {
        self.0.iter().all(|&x| x == 0)
    }
}

struct Sim {
    q: Vec<bool>,
    bits: Vec<usize>,
    phase: Phase,
    nsym: usize,
}
const SYM_ZERO: usize = usize::MAX;
impl Sim {
    fn new(nq: usize, nb: usize) -> Self {
        Sim { q: vec![false; nq], bits: vec![SYM_ZERO; nb], phase: Phase::default(), nsym: 1 }
    }
    fn cond(&mut self, op: &Op, hit: bool) {
        if !hit {
            return;
        }
        if op.c_condition == NO_BIT {
            self.phase.flip(0);
            return;
        }
        let s = self.bits[op.c_condition.0 as usize];
        if s != SYM_ZERO {
            self.phase.flip(s);
        }
    }
    fn step(&mut self, op: &Op) {
        let t = op.q_target.0 as usize;
        let a = op.q_control1.0 as usize;
        let b = op.q_control2.0 as usize;
        let uncond = op.c_condition == NO_BIT;
        match op.kind {
            K::X => { assert!(uncond); self.q[t] ^= true; }
            K::CX => { assert!(uncond); self.q[t] ^= self.q[a]; }
            K::CCX => { assert!(uncond); self.q[t] ^= self.q[a] & self.q[b]; }
            K::Swap => { assert!(uncond); self.q.swap(t, a); }
            K::Z => { let h = self.q[t]; self.cond(op, h); }
            K::CZ => { let h = self.q[t] & self.q[a]; self.cond(op, h); }
            K::CCZ => { let h = self.q[t] & self.q[a] & self.q[b]; self.cond(op, h); }
            K::Hmr => {
                let s = self.nsym;
                self.nsym += 1;
                self.bits[op.c_target.0 as usize] = s;
                if self.q[t] {
                    self.phase.flip(s);
                }
                self.q[t] = false;
            }
            K::R => { assert!(!self.q[t], "reset of nonzero wire {t}"); }
            K::BitStore0 => self.bits[op.c_target.0 as usize] = SYM_ZERO,
            K::Register | K::AppendToRegister => {}
            _ => panic!("unsupported gate {:?}", op.kind),
        }
    }
}

fn ccx_count(ops: &[Op]) -> usize {
    ops.iter().filter(|o| matches!(o.kind, K::CCX | K::CCZ)).count()
}
fn val(q: &[bool], ws: &[QubitId]) -> u64 {
    ws.iter().enumerate().fold(0, |v, (i, w)| v | ((q[w.0 as usize] as u64) << i))
}
fn set(q: &mut [bool], ws: &[QubitId], v: u64) {
    for (i, w) in ws.iter().enumerate() {
        q[w.0 as usize] = v >> i & 1 != 0;
    }
}

/// The P5 code (wire order a2 a1 a0 h3 l3 b2 b1 b0, bit i = wire i) of every 5-trit word (trit i = digit i),
/// computed by simulating the walk's own pack3 + pack5.
pub fn p5_table() -> Vec<u8> {
    let mut out = Vec::new();
    for word in 0..243usize {
        let mut c = Builder::new();
        let mut tape = Tape::new(5);
        let mut inputs = Vec::new();
        for t in 0..5 {
            let qs = c.alloc_qubits(2);
            inputs.push((c.op_count(), qs[0], qs[1]));
            tape.raw[t] = Some((qs[0], qs[1]));
            if t == 2 {
                tape.pack3(&mut c, 0);
            }
            if t == 4 {
                tape.pack5(&mut c, 0);
            }
        }
        let g = tape.groups[0].clone().unwrap();
        let wires = [g.a2, g.a1, g.a0, g.h3, g.l3, g.b2, g.b1, g.b0];
        let (nq, nb) = c.i13_dims();
        let ops = c.take_ops();
        let mut s = Sim::new(nq, nb);
        let mut digits = word;
        let vals: Vec<(bool, bool)> = (0..5).map(|_| { let v = digits % 3; digits /= 3; letter(v) }).collect();
        for pos in 0..=ops.len() {
            for (i, (at, a, b)) in inputs.iter().enumerate() {
                if *at == pos {
                    s.q[a.0 as usize] = vals[i].0;
                    s.q[b.0 as usize] = vals[i].1;
                }
            }
            if pos < ops.len() {
                s.step(&ops[pos]);
            }
        }
        out.push(val(&s.q, &wires) as u8);
    }
    out
}

pub fn study() {
    let t = p5_table();
    let mut seen = [false; 256];
    for &c in &t {
        assert!(!seen[c as usize], "P5 code not injective");
        seen[c as usize] = true;
    }
    println!("P5_TABLE {}", t.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(","));
    let inv: Vec<usize> = (0..256).filter(|&c| !seen[c]).collect();
    println!("P5_INVALID {:?}", inv);
    let mut b = 243u64;
    for k in 1..=60 {
        b = next_bound(b);
        print!("{k}:{b}/{} ", nbits(b));
    }
    println!();
}

/// pi over all 256 codes: valid P5 codes -> [0,243) bijectively, unused -> [243,256); pi_inv o pi = id.
fn test_pi(table: &[u8]) {
    let mut c = Builder::new();
    let w: [QubitId; 8] = c.alloc_qubits(8).try_into().unwrap();
    let d = pi_fwd(&mut c, w);
    let mid = c.op_count();
    let back = pi_inv(&mut c, d);
    assert_eq!(back, w);
    let (nq, nb) = c.i13_dims();
    let ops = c.take_ops();
    let mut valid = [false; 256];
    for &code in table {
        valid[code as usize] = true;
    }
    let mut seen = [false; 256];
    for code in 0..256u64 {
        let mut s = Sim::new(nq, nb);
        set(&mut s.q, &w, code);
        for op in &ops[..mid] {
            s.step(op);
        }
        let dv = val(&s.q, &d);
        assert_eq!(dv < 243, valid[code as usize], "pi code {code} -> {dv}");
        assert!(!seen[dv as usize]);
        seen[dv as usize] = true;
        for op in &ops[mid..] {
            s.step(op);
        }
        assert_eq!(val(&s.q, &w), code);
        assert!(s.phase.is_zero());
    }
    println!("{{\"kind\":\"a2-digit-map\",\"codes\":256,\"valid_to_0_242\":243,\"unused_to_243_255\":13,\"ccx\":{},\"scratch\":0,\"value\":\"pass\",\"phase\":\"pass\"}}", ccx_count(&ops[..mid]));
}

/// One push step and its pop, exhaustively over x < bound, d < 243: values, garbage-free scratch, zero phase.
fn test_step(bound: u64) -> (usize, usize, u32, u32) {
    let w = nbits(bound);
    let mut c = Builder::new();
    let d: [QubitId; 8] = c.alloc_qubits(8).try_into().unwrap();
    let st0 = c.alloc_qubits(w);
    let base = c.active_qubits();
    let mut st = st0.clone();
    let nb = push_step(&mut c, d, &mut st, bound);
    let mid = c.op_count();
    let pushed = st.clone();
    let peak_push = c.peak_total() - base;
    let base2 = c.active_qubits();
    pop_step(&mut c, d, &mut st, nb, bound);
    let peak_pop = c.peak_total().saturating_sub(base2);
    let (nq, nbits_) = c.i13_dims();
    let ops = c.take_ops();
    let (ccx_push, ccx_pop) = (ccx_count(&ops[..mid]), ccx_count(&ops[mid..]));
    let live_push: std::collections::HashSet<u64> = d.iter().chain(pushed.iter()).map(|q| q.0).collect();
    let live_pop: std::collections::HashSet<u64> = d.iter().chain(st.iter()).map(|q| q.0).collect();
    for x in 0..bound {
        for dv in 0..243u64 {
            let mut s = Sim::new(nq, nbits_);
            set(&mut s.q, &st0, x);
            set(&mut s.q, &d, dv);
            for op in &ops[..mid] {
                s.step(op);
            }
            let y = 243 * x + dv;
            assert_eq!(val(&s.q, &d), y & 255, "push low byte bound={bound} x={x} d={dv}");
            assert_eq!(val(&s.q, &pushed), y >> 8, "push state bound={bound} x={x} d={dv}");
            assert!(y >> 8 < nb);
            assert!(s.q.iter().enumerate().all(|(i, &b)| !b || live_push.contains(&(i as u64))), "push garbage bound={bound} x={x} d={dv}");
            assert!(s.phase.is_zero(), "push phase bound={bound} x={x} d={dv}");
            for op in &ops[mid..] {
                s.step(op);
            }
            assert_eq!(val(&s.q, &d), dv);
            assert_eq!(val(&s.q, &st), x);
            assert!(s.q.iter().enumerate().all(|(i, &b)| !b || live_pop.contains(&(i as u64))), "pop garbage bound={bound} x={x} d={dv}");
            assert!(s.phase.is_zero(), "pop phase bound={bound} x={x} d={dv}");
        }
    }
    (ccx_push, ccx_pop, peak_push, peak_pop)
}

/// Whole chain lifecycle through the walk's own Tape calls (pack_due in forward order, ensure_raw + take in reverse
/// order, as the walkback does). `words` = None: every word of the `len` chained groups (243^len); Some(n): n
/// pseudo-random words.
fn test_lifecycle(len: usize, words: Option<usize>) -> (usize, usize, usize, u32) {
    std::env::set_var("SQ_A2_CHAINS", "1");
    std::env::set_var("SQ_A2_LEN", len.to_string());
    std::env::set_var("SQ_A2_FIRST", "0");
    let r = 5 * len + 5;
    let mut c = Builder::new();
    let mut tape = Tape::new(r);
    let mut inputs = Vec::new();
    let plain = 8 * len;
    for t in 0..r {
        let qs = c.alloc_qubits(2);
        inputs.push((c.op_count(), qs[0], qs[1]));
        tape.raw[t] = Some((qs[0], qs[1]));
        tape.pack_due(&mut c, t, r, false);
    }
    // groups 0..len-1 are chained; the extra group stays live, as the walk's head does
    assert!(tape.chains[0].as_ref().is_some_and(|ch| ch.top == len - 1));
    let chained_wires: usize = tape.chains[0].as_ref().unwrap().state.len() + 8 * (len - 1);
    let mut reads = Vec::new();
    for t in (0..r).rev() {
        tape.ensure_raw(&mut c, t);
        if t > 0 {
            tape.ensure_raw(&mut c, t - 1);
        }
        let (a, b) = tape.raw[t].take().unwrap();
        reads.push((c.op_count(), t, a, b));
        c.free(a);
        c.free(b);
    }
    assert!(tape.all_consumed());
    let (nq, nb) = c.i13_dims();
    let peak = c.peak_total();
    let ops = c.take_ops();
    let total = words.unwrap_or_else(|| 243usize.pow(len as u32));
    let mut rng = 0x9E3779B97F4A7C15u64 ^ len as u64;
    for word in 0..total {
        let mut s = Sim::new(nq, nb);
        let letters: Vec<usize> = (0..r)
            .map(|t| {
                if words.is_none() && t < 5 * len {
                    (word / 3usize.pow(t as u32)) % 3
                } else {
                    rng ^= rng << 13;
                    rng ^= rng >> 7;
                    rng ^= rng << 17;
                    (rng % 3) as usize
                }
            })
            .collect();
        let (mut ii, mut ri) = (0, 0);
        for pos in 0..=ops.len() {
            while ii < inputs.len() && inputs[ii].0 == pos {
                let (_, a, b) = inputs[ii];
                assert!(!s.q[a.0 as usize] && !s.q[b.0 as usize]);
                let (va, vb) = letter(letters[ii]);
                s.q[a.0 as usize] = va;
                s.q[b.0 as usize] = vb;
                ii += 1;
            }
            while ri < reads.len() && reads[ri].0 == pos {
                let (_, t, a, b) = reads[ri];
                assert_eq!((s.q[a.0 as usize], s.q[b.0 as usize]), letter(letters[t]), "lifecycle len={len} word={word} t={t}");
                s.q[a.0 as usize] = false;
                s.q[b.0 as usize] = false;
                ri += 1;
            }
            if pos < ops.len() {
                s.step(&ops[pos]);
            }
        }
        assert!(s.q.iter().all(|b| !b), "lifecycle garbage len={len} word={word}");
        assert!(s.phase.is_zero(), "lifecycle phase len={len} word={word}");
    }
    std::env::remove_var("SQ_A2_CHAINS");
    (total, plain, chained_wires, peak)
}

pub fn selftest() {
    for synth in [true, false] {
        if synth { std::env::set_var("HEO_CODEC_SYNTH", "1"); } else { std::env::remove_var("HEO_CODEC_SYNTH"); }
        println!("{{\"kind\":\"a2-codec-mode\",\"p3_synthesized\":{synth}}}");
        selftest_mode(synth);
    }
}

fn selftest_mode(full: bool) {
    let table = p5_table();
    test_pi(&table);
    // every push/pop step of chains up to 60 groups (bounds 243 -> 19), exhaustive over its whole input domain
    let mut b = 243u64;
    let mut tot = (0, 0);
    let maxk: usize = if full { env_usize("SQ_A2_TEST_STEPS", 59) } else { 0 };
    for k in 1..=maxk {
        let (cp, cq, pk, pq) = test_step(b);
        let nb = next_bound(b);
        if k <= 13 {
            tot.0 += cp;
            tot.1 += cq;
        }
        println!("{{\"kind\":\"a2-chain-step\",\"push\":{k},\"bound_in\":{b},\"bound_out\":{nb},\"register_in\":{},\"register_out\":{},\"cases\":{},\"ccx_push\":{cp},\"ccx_pop\":{cq},\"scratch_push\":{pk},\"scratch_pop\":{pq},\"value\":\"pass\",\"phase\":\"pass\",\"cleanup\":\"pass\"}}",
                 nbits(b) + 8, nbits(nb) + 8, b * 243);
        b = nb;
    }
    if full {
        println!("{{\"kind\":\"a2-chain14-cost\",\"groups\":14,\"wires_saved\":1,\"ccx_merge_steps\":{},\"ccx_unmerge_steps\":{}}}", tot.0, tot.1);
    }
    let (n, plain, wires, peak) = test_lifecycle(2, None);
    println!("{{\"kind\":\"a2-tape-lifecycle\",\"chain_groups\":2,\"words\":{n},\"exhaustive\":true,\"plain_wires\":{plain},\"chained_wires\":{wires},\"peak\":{peak},\"value\":\"pass\",\"phase\":\"pass\",\"cleanup\":\"pass\"}}");
    let nw = env_usize("SQ_A2_TEST_WORDS", 3000);
    let (n, plain, wires, peak) = test_lifecycle(14, Some(if full { nw } else { nw / 10 }));
    println!("{{\"kind\":\"a2-tape-lifecycle\",\"chain_groups\":14,\"words\":{n},\"exhaustive\":false,\"plain_wires\":{plain},\"chained_wires\":{wires},\"peak\":{peak},\"value\":\"pass\",\"phase\":\"pass\",\"cleanup\":\"pass\"}}");
}
