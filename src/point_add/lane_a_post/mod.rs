//! Round 105 lane A's exact post-passes, one shared source for the in-build call (`apply`, used by `build()` after the
//! truth round) and the merge lane's streamed driver (`stool`, which includes these files by path from the tree).
//! Chain: peep, peep, hold (XOR-hash keys, in place, truth-model zeros), peep, peep. The passes run on the stream
//! without the final nonce X X pair, which is appended afterwards, so the pair's target never reaches a pass.
//! Lane A's rtool code (peep.rs, hold.rs, holdx.rs) with the I/O abstracted (scan closures and an output sink) and the
//! chain's knobs fixed: no environment variable is read. Ours (lane A + merge lane), written from public descriptions.
use crate::circuit::{Op, OperationType, QubitId, NO_BIT};

pub mod counts;
pub mod hold;
pub mod holdx;
pub mod peep;
pub mod tzmodel;

#[allow(unused_imports)]
pub use counts::Counts;

/// Multiply-rotate hasher for the passes' hash maps (speed only: no pass output depends on hash order; the only map
/// iteration is `retain`, whose result does not depend on order).
#[derive(Default, Clone, Copy)]
pub struct Fx(u64);
impl Fx {
    #[inline]
    fn add(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}
impl std::hash::Hasher for Fx {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.add(b as u64);
        }
    }
    #[inline]
    fn write_u8(&mut self, x: u8) {
        self.add(x as u64);
    }
    #[inline]
    fn write_u16(&mut self, x: u16) {
        self.add(x as u64);
    }
    #[inline]
    fn write_u32(&mut self, x: u32) {
        self.add(x as u64);
    }
    #[inline]
    fn write_u64(&mut self, x: u64) {
        self.add(x);
    }
    #[inline]
    fn write_u128(&mut self, x: u128) {
        self.add(x as u64);
        self.add((x >> 64) as u64);
    }
    #[inline]
    fn write_usize(&mut self, x: usize) {
        self.add(x as u64);
    }
}
pub type FxMap<K, V> = std::collections::HashMap<K, V, std::hash::BuildHasherDefault<Fx>>;

/// Ops per in-memory chunk (only memory; the op sequence a pass sees does not depend on it).
pub const CHUNK: usize = 1 << 22;

/// The chain's hold settings: XOR-hash keys, in-place releases, truth-model zeros, horizon 2^26, no conditional
/// deliveries, conditional writes followed symbolically (lane A's HOLD_KEY=xor HOLD_INPLACE=1 HOLD_TZ=1 run).
#[derive(Clone, Copy, Debug)]
pub struct HoldCfg {
    pub horizon: u32,
    pub hold_cond: bool,
    pub xcond: bool,
    pub inplace: bool,
    pub tz: bool,
    /// truth model on its own thread (the result does not depend on it)
    pub tz_thread: bool,
    /// the inline-storage port of the truth model (tzmodel.rs) instead of the tree's own (same answers, faster)
    pub tz_fast: bool,
}
pub const HOLD: HoldCfg =
    HoldCfg { horizon: 1 << 26, hold_cond: false, xcond: true, inplace: true, tz: true, tz_thread: true, tz_fast: true };

/// One pass of the chain.
#[derive(Clone, Copy, Debug)]
pub enum Pass {
    Peep,
    Hold(HoldCfg),
}
pub const CHAIN: [Pass; 5] = [Pass::Peep, Pass::Peep, Pass::Hold(HOLD), Pass::Peep, Pass::Peep];

/// Ops in stream order, held as chunks so that a consuming pass frees its input as it writes its output.
pub struct Chunks {
    pub v: Vec<Vec<Op>>,
    pub n: u64,
}
impl Chunks {
    pub fn from_vec(mut ops: Vec<Op>) -> Chunks {
        let n = ops.len() as u64;
        let mut v = Vec::new();
        while ops.len() > CHUNK {
            let tail = ops.split_off(ops.len() - CHUNK);
            ops.shrink_to_fit();
            v.push(tail);
        }
        v.push(ops);
        v.reverse();
        Chunks { v, n }
    }
    pub fn iter(&self) -> impl Iterator<Item = Op> + '_ {
        self.v.iter().flat_map(|c| c.iter().copied())
    }
    pub fn into_vec(self, extra: usize) -> Vec<Op> {
        let mut out = Vec::with_capacity(self.n as usize + extra);
        for c in self.v {
            out.extend_from_slice(&c);
        }
        out
    }
}
/// Emptied chunk buffers, handed from a consuming pass's input to its output, so a pass writes into memory that is
/// already mapped (no fresh page faults, no frees) and the store stays about one copy of the stream.
pub type Pool = std::rc::Rc<std::cell::RefCell<Vec<Vec<Op>>>>;

/// Consuming iterator over `Chunks` that returns each emptied buffer to the pool.
pub struct Drain {
    chunks: std::vec::IntoIter<Vec<Op>>,
    cur: Vec<Op>,
    k: usize,
    pool: Pool,
}
impl Drain {
    pub fn new(c: Chunks, pool: Pool) -> Self {
        Drain { chunks: c.v.into_iter(), cur: Vec::new(), k: 0, pool }
    }
}
impl Iterator for Drain {
    type Item = Op;
    #[inline]
    fn next(&mut self) -> Option<Op> {
        while self.k == self.cur.len() {
            let next = self.chunks.next()?;
            let mut done = std::mem::replace(&mut self.cur, next);
            self.k = 0;
            if done.capacity() >= CHUNK {
                done.clear();
                self.pool.borrow_mut().push(done);
            }
        }
        self.k += 1;
        Some(self.cur[self.k - 1])
    }
}

/// Output sink building `Chunks`, taking buffers from the pool first.
pub struct ChunkOut {
    v: Vec<Vec<Op>>,
    cur: Vec<Op>,
    n: u64,
    pool: Pool,
}
impl ChunkOut {
    pub fn new(pool: Pool) -> Self {
        let cur = pool.borrow_mut().pop().unwrap_or_else(|| Vec::with_capacity(CHUNK));
        Self { v: Vec::new(), cur, n: 0, pool }
    }
    #[inline]
    pub fn push(&mut self, op: Op) {
        if self.cur.len() == CHUNK {
            let fresh = self.pool.borrow_mut().pop().unwrap_or_else(|| Vec::with_capacity(CHUNK));
            self.v.push(std::mem::replace(&mut self.cur, fresh));
        }
        self.cur.push(op);
        self.n += 1;
    }
    pub fn finish(mut self) -> Chunks {
        if !self.cur.is_empty() || self.v.is_empty() {
            self.v.push(self.cur);
        }
        Chunks { v: self.v, n: self.n }
    }
}

/// The final nonce pair: the last two ops when both are an unconditioned X on qubit `nonce`.
pub fn is_tail(a: &Op, b: &Op, nonce: usize) -> bool {
    let x = |o: &Op| o.kind == OperationType::X && o.q_target == QubitId(nonce as u64) && o.c_condition == NO_BIT;
    x(a) && x(b)
}

/// One pass on in-memory chunks; returns the output and a log line.
pub fn run_pass(p: Pass, input: Chunks, pool: &Pool) -> (Chunks, String) {
    let t0 = std::time::Instant::now();
    let n = input.n;
    let line = match p {
        Pass::Peep => {
            let plan = peep::decide(n, &|| input.iter());
            let mut out = ChunkOut::new(pool.clone());
            let mut emit = |o: Op| out.push(o);
            let line = peep::rewrite(&plan, Drain::new(input, pool.clone()), &mut emit);
            (out.finish(), line)
        }
        Pass::Hold(cfg) => {
            let a = holdx::analyze_xor(&|| input.iter(), n, &cfg);
            let plan = hold::select(a);
            let mut out = ChunkOut::new(pool.clone());
            let mut emit = |o: Op| out.push(o);
            let line = hold::rewrite(plan, Drain::new(input, pool.clone()), &mut emit);
            (out.finish(), line)
        }
    };
    (line.0, format!("{} wall_s={:.1}", line.1, t0.elapsed().as_secs_f64()))
}

/// In-build entry: the chain on `ops` (the truth round's output). The final nonce pair is taken off first and put back
/// last. Returns the ops for `ops.bin`.
pub fn apply(mut ops: Vec<Op>, nonce: usize) -> Vec<Op> {
    if ops.len() < 4 {
        return ops;
    }
    let k = ops.len();
    let tail: Vec<Op> = if is_tail(&ops[k - 2], &ops[k - 1], nonce) { ops.split_off(k - 2) } else { vec![] };
    let t0 = std::time::Instant::now();
    let mut cur = Chunks::from_vec(ops);
    eprintln!("LANE_A_POST chunks={} split_s={:.1}", cur.v.len(), t0.elapsed().as_secs_f64());
    let pool: Pool = Default::default();
    for (i, &p) in CHAIN.iter().enumerate() {
        let (next, line) = run_pass(p, cur, &pool);
        eprintln!("LANE_A_POST step={} {}", i + 1, line);
        cur = next;
    }
    pool.borrow_mut().clear();
    let t1 = std::time::Instant::now();
    let mut out = cur.into_vec(tail.len());
    out.extend_from_slice(&tail);
    eprintln!("LANE_A_POST tail={} ops={} join_s={:.1} total_s={:.1}", tail.len(), out.len(), t1.elapsed().as_secs_f64(),
              t0.elapsed().as_secs_f64());
    out
}
