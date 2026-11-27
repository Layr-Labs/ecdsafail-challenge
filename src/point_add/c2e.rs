//! (internal) (internal) (internal) ((internal)): the ECHO COMPILER (rewrite step `echo:<f>[,<gap/100>]`).
//!
//! The flag wire f (a clean, held control bit: the loop enable) is re-hosted as a DIRTY TOGGLE on a wire D that the
//! window never touches.  Inside a rewritten window wire f is never written.  D holds d (its foreign value) or
//! d ^ f_cur; every change between the two states is an evaluation EV = replay of the window's toggle sections with
//! target D.
//!   rule TS  : a toggle section (records that target f, plus the records between them) is emitted with target D
//!              (state E) or with its target records dropped (state DD); f_cur's replay list is updated.
//!   rule CH  : f-controlled Fredkin chain = rotation R = Pa ; Pb (two reversals): Pa[D] EV Pa[D] Pb[D] EV Pb[D].
//!   rule BLK : Q = records with the uses CCX(f,s,h) (a controlled add written as XORs of carries).  With Q0 = Q
//!              without its uses, Block(u) = Q0^-1 ; Q[u] satisfies N Block(1) N = Block(1)^-1 (N = X on the sum
//!              wires; checked on 256 random states per instance).  Emitted, starting with D = d:
//!              Q[D] N[D] Q0^-1 EV Q[D] EV N[D].
//!   rule MAC : a short range M with M(f=0) = I and M(f=1)^2 = I (checked exhaustively): M[D] now, M[D] again in the
//!              other D-state (deferred until a record does not commute with it).
//! Exact on every input for which f = 0 at the window's entry and the original leaves f = 0 at its exit.
use super::*;
use super::w2::*;
use super::c2::{touches, chain_at};

thread_local! {
    /// the windows to rewrite (pre-echo row ranges); None = every cluster of f-touching records
    pub static ECHO_WLIST: std::cell::RefCell<Option<Vec<(usize, usize, usize)>>> = std::cell::RefCell::new(None);
    /// (old start, old end, new start, new end, D wire) of every rewritten window
    pub static ECHO_WINS: std::cell::RefCell<Vec<[usize; 5]>> = std::cell::RefCell::new(Vec::new());
}
#[inline] fn gate_ok(r: &Row) -> bool { match r[0] { 6 => r[2] == NONE, 8 => r[3] == NONE, 13 => true, _ => false } }
#[inline] fn tgt(r: &Row) -> u16 { match r[0] { 6 => r[1], 8 => r[2], 13 => r[3], _ => NONE } }
#[inline] fn ctl(r: &Row) -> [u16; 2] { match r[0] { 8 => [r[1], NONE], 13 => [r[1], r[2]], _ => [NONE, NONE] } }
#[inline] fn subst(r: Row, f: u16, d: u16) -> Row { let mut q = r; for j in 1..=qubits(r[0]) { if q[j] == f { q[j] = d; } } q }
#[inline] fn fuse(r: &Row, f: u16) -> bool { let c = ctl(r); c[0] == f || c[1] == f }

pub struct Mini { pub q: Vec<V> }
impl Mini {
    /// like `random`, with bit density 1/2 (mode 0), 1/8 (1), 7/8 (2), 1/64 (3), 63/64 (4): sparse and dense states
    pub fn random_d(seed: u64, mode: u64) -> Mini { let mut x = seed | 1; let mut q = vec![Z; 1024];
        let mut nx = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
        for l in q.iter_mut() { for i in 0..W { l[i] = match mode % 5 { 0 => nx(), 1 => nx() & nx() & nx(), 2 => nx() | nx() | nx(), 3 => nx() & nx() & nx() & nx() & nx() & nx(), _ => nx() | nx() | nx() | nx() | nx() | nx() }; } }
        Mini { q } }
    pub fn random(seed: u64) -> Mini { let mut x = seed | 1; let mut q = vec![Z; 1024]; for l in q.iter_mut() { for i in 0..W { x ^= x << 13; x ^= x >> 7; x ^= x << 17; l[i] = x; } } Mini { q } }
    #[inline] pub fn exec(&mut self, r: &Row) { match r[0] {
        6 => { for i in 0..W { self.q[r[1] as usize][i] ^= u64::MAX; } }
        8 => { let v = self.q[r[1] as usize]; xor(&mut self.q[r[2] as usize], v); }
        13 => { let v = and(self.q[r[1] as usize], self.q[r[2] as usize]); xor(&mut self.q[r[3] as usize], v); }
        _ => panic!("mini kind") } }
}


