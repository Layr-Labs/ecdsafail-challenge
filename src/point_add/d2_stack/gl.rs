//! A small recorded gate list over persistent wires and block-local temporaries.
//!
//! Every D2 stack/park block is built here first and then emitted into the [`Builder`], either forward
//! or as its exact inverse (reverse order, `AndC` <-> `AndU`, `Alloc` <-> `Free`).  Blocks that contain a
//! measurement (`Meas`/`CzIf`, the park detector's phase-fixed erase) are self-inverse by construction and
//! are always emitted forward; `emit(.., rev = true)` refuses them.
//!
//! Gate meanings (`T` = scored Toffoli):
//!   `X`, `Cx`                      Clifford.
//!   `Ccx(a, b, t)`                 1 T.
//!   `Fred(c, a, b)`                controlled swap, 1 T (CX, CCX, CX).
//!   `AndC(a, b, t)`                t = a AND b into a clean temporary, 1 T.
//!   `AndU(a, b, t)`                measurement-based erase of t == a AND b (HMR + classically controlled CZ), 0 T.
//!   `Leaf(a, b, z)`                CCX(a, b, z); in the phase-fixed erase sweep it becomes CZ(a, b) under the bit
//!                                  measured from z.
//!   `Alloc(t)` / `Free(t)`         temporary lifetime (clean on both ends).
//!   `Meas(t, s)`, `CzIf(a, b, s)`  X-basis demolition measurement of t into classical slot s, CZ under slot s.
use super::super::builder::Builder;
use crate::circuit::{BitId, QubitId};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum W {
    Q(QubitId),
    T(u32),
}

#[derive(Clone, Copy, Debug)]
pub enum G {
    X(W),
    Cx(W, W),
    Ccx(W, W, W),
    Fred(W, W, W),
    AndC(W, W, W),
    AndU(W, W, W),
    Leaf(W, W, W),
    Alloc(W),
    Free(W),
    Meas(W, u32),
    CzIf(W, W, u32),
    /// Multi-controlled leaf `z ^= AND(ctrls)` (entry of [`Gl::mleaves`]), built from Toffolis on borrowed dirty
    /// wires; in the phase-fixed erase sweep it becomes [`G::MPhaseIf`].
    MLeaf(u32),
    /// Phase `(-1)^AND(ctrls)` of multi-leaf entry `.0`, under classical slot `.1` (dirty-wire construction).
    MPhaseIf(u32, u32),
}

/// A multi-controlled leaf: controls (at least 3), target, and dirty wires (at least `ctrls.len() - 2`) that are
/// neither controls nor the target and are restored by the construction.
#[derive(Clone, Debug)]
pub struct MLeafDesc {
    pub ctrls: Vec<W>,
    pub z: W,
    pub dirty: Vec<W>,
}

/// Toffolis of `t ^= AND(n controls)` with `n - 2` dirty wires (n >= 3): 4 (n - 2).
pub fn mcx_t(n: usize) -> usize {
    match n {
        0 | 1 => 0,
        2 => 1,
        _ => 4 * (n - 2),
    }
}

/// Toffolis of the phase `(-1)^AND(m wires)` with `m - 2` dirty wires: 0 (m <= 2), else 2 * mcx_t(m - 1).
pub fn mphase_t(m: usize) -> usize {
    if m <= 2 {
        0
    } else {
        2 * mcx_t(m - 1)
    }
}

/// The gate sequence of `t ^= AND(ctrls)` on borrowed dirty wires (Barenco et al., Lemma 7.2), as Toffoli /
/// CX triples through `ccx` / `cx`. `dirty.len() >= ctrls.len() - 2`; every dirty wire is restored.
pub fn mcx_seq<Q: Copy>(ctrls: &[Q], t: Q, dirty: &[Q], ccx: &mut dyn FnMut(Q, Q, Q), cx: &mut dyn FnMut(Q, Q)) {
    let n = ctrls.len();
    match n {
        0 => panic!("mcx_seq: no controls"),
        1 => cx(ctrls[0], t),
        2 => ccx(ctrls[0], ctrls[1], t),
        _ => {
            assert!(dirty.len() >= n - 2, "mcx_seq: {n} controls need {} dirty wires, got {}", n - 2, dirty.len());
            let d = &dirty[..n - 2];
            let mut half = |ccx: &mut dyn FnMut(Q, Q, Q)| {
                for i in (3..n).rev() {
                    ccx(ctrls[i - 1], d[i - 3], d[i - 2]);
                }
                ccx(ctrls[0], ctrls[1], d[0]);
                for i in 3..n {
                    ccx(ctrls[i - 1], d[i - 3], d[i - 2]);
                }
            };
            ccx(ctrls[n - 1], d[n - 3], t);
            half(ccx);
            ccx(ctrls[n - 1], d[n - 3], t);
            half(ccx);
        }
    }
}

#[derive(Default)]
pub struct Gl {
    pub g: Vec<G>,
    nt: u32,
    free: Vec<u32>,
    live: u32,
    /// Peak number of simultaneously live temporaries.
    pub peak: u32,
    nslots: u32,
    /// Multi-controlled leaves referenced by [`G::MLeaf`] / [`G::MPhaseIf`].
    pub mleaves: Vec<MLeafDesc>,
}

impl Gl {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn alloc(&mut self) -> W {
        let i = self.free.pop().unwrap_or_else(|| {
            self.nt += 1;
            self.nt - 1
        });
        self.live += 1;
        self.peak = self.peak.max(self.live);
        let w = W::T(i);
        self.g.push(G::Alloc(w));
        w
    }
    pub fn release(&mut self, w: W) {
        match w {
            W::T(i) => {
                self.g.push(G::Free(w));
                self.free.push(i);
                self.live -= 1;
            }
            W::Q(_) => panic!("release of a persistent wire"),
        }
    }
    pub fn live(&self) -> u32 {
        self.live
    }
    pub fn slot(&mut self) -> u32 {
        self.nslots += 1;
        self.nslots - 1
    }
    pub fn x(&mut self, a: W) {
        self.g.push(G::X(a));
    }
    pub fn cx(&mut self, a: W, b: W) {
        assert_ne!(a, b);
        self.g.push(G::Cx(a, b));
    }
    pub fn ccx(&mut self, a: W, b: W, t: W) {
        assert!(a != b && a != t && b != t);
        self.g.push(G::Ccx(a, b, t));
    }
    pub fn fred(&mut self, c: W, a: W, b: W) {
        assert!(c != a && c != b && a != b);
        self.g.push(G::Fred(c, a, b));
    }
    /// `t = a AND b` into a fresh temporary.
    pub fn and_c(&mut self, a: W, b: W) -> W {
        let t = self.alloc();
        assert!(a != b);
        self.g.push(G::AndC(a, b, t));
        t
    }
    /// Erase `t == a AND b` (0 T) and free it.
    pub fn and_u(&mut self, a: W, b: W, t: W) {
        assert!(a != b && a != t && b != t);
        self.g.push(G::AndU(a, b, t));
        self.release(t);
    }
    pub fn leaf(&mut self, a: W, b: W, z: W) {
        assert!(a != b && a != z && b != z);
        self.g.push(G::Leaf(a, b, z));
    }
    pub fn meas(&mut self, t: W, s: u32) {
        self.g.push(G::Meas(t, s));
    }
    pub fn cz_if(&mut self, a: W, b: W, s: u32) {
        self.g.push(G::CzIf(a, b, s));
    }
    /// `z ^= AND(ctrls)` as a leaf of a phase-fixed erase range (2 controls: a plain [`G::Leaf`]).
    pub fn mleaf(&mut self, ctrls: &[W], z: W, dirty: &[W]) {
        assert!(ctrls.len() >= 2 && !ctrls.contains(&z));
        if ctrls.len() == 2 {
            self.leaf(ctrls[0], ctrls[1], z);
            return;
        }
        assert!(dirty.len() >= ctrls.len() - 2);
        for d in dirty {
            assert!(!ctrls.contains(d) && *d != z, "mleaf: dirty wire aliases a control or the target");
        }
        self.mleaves.push(MLeafDesc { ctrls: ctrls.to_vec(), z, dirty: dirty[..ctrls.len() - 2].to_vec() });
        self.g.push(G::MLeaf(self.mleaves.len() as u32 - 1));
    }
    /// `t ^= AND(ctrls)` expanded into Toffolis on dirty wires (not a leaf: replayed as plain gates).
    pub fn mcx(&mut self, ctrls: &[W], t: W, dirty: &[W]) {
        for d in dirty.iter().take(ctrls.len().saturating_sub(2)) {
            assert!(!ctrls.contains(d) && *d != t, "mcx: dirty wire aliases a control or the target");
        }
        let gl = std::cell::RefCell::new(&mut *self);
        mcx_seq(ctrls, t, dirty, &mut |a, b, c| gl.borrow_mut().ccx(a, b, c), &mut |a, b| gl.borrow_mut().cx(a, b));
    }
    /// Append `other`, remapping its temporaries onto fresh temporaries of `self` (lifetimes preserved).
    pub fn append(&mut self, other: &Gl) {
        let mut map: Vec<Option<W>> = vec![None; other.nt as usize];
        let soff = self.nslots;
        self.nslots += other.nslots;
        let m = |map: &Vec<Option<W>>, w: W| -> W {
            match w {
                W::Q(_) => w,
                W::T(i) => map[i as usize].expect("append: temp used before alloc"),
            }
        };
        for &op in &other.g {
            match op {
                G::Alloc(W::T(i)) => {
                    let n = self.alloc();
                    map[i as usize] = Some(n);
                }
                G::Free(w) => {
                    let n = m(&map, w);
                    self.release(n);
                }
                G::X(a) => self.x(m(&map, a)),
                G::Cx(a, b) => self.cx(m(&map, a), m(&map, b)),
                G::Ccx(a, b, t) => self.ccx(m(&map, a), m(&map, b), m(&map, t)),
                G::Fred(c, a, b) => self.fred(m(&map, c), m(&map, a), m(&map, b)),
                G::AndC(a, b, t) => self.g.push(G::AndC(m(&map, a), m(&map, b), m(&map, t))),
                G::AndU(a, b, t) => self.g.push(G::AndU(m(&map, a), m(&map, b), m(&map, t))),
                G::Leaf(a, b, z) => self.leaf(m(&map, a), m(&map, b), m(&map, z)),
                G::Meas(t, s) => self.meas(m(&map, t), s + soff),
                G::CzIf(a, b, s) => self.cz_if(m(&map, a), m(&map, b), s + soff),
                G::MLeaf(i) | G::MPhaseIf(i, _) => {
                    let d = &other.mleaves[i as usize];
                    let nd = MLeafDesc {
                        ctrls: d.ctrls.iter().map(|&w| m(&map, w)).collect(),
                        z: m(&map, d.z),
                        dirty: d.dirty.iter().map(|&w| m(&map, w)).collect(),
                    };
                    self.mleaves.push(nd);
                    let ni = self.mleaves.len() as u32 - 1;
                    self.g.push(match op {
                        G::MLeaf(_) => G::MLeaf(ni),
                        G::MPhaseIf(_, s) => G::MPhaseIf(ni, s + soff),
                        _ => unreachable!(),
                    });
                }
                G::Alloc(W::Q(_)) => unreachable!(),
            }
        }
    }
    /// Append the phase-fixed erase of `z`: measure `z` (X basis) into a fresh slot, then replay
    /// `self.g[start..end]` in reverse (ops after `end`, the "act", are not replayed and must leave every
    /// wire the range reads unchanged) (`AndC` <-> `AndU`, `Alloc` <-> `Free`) with every `Leaf(a, b, z)`
    /// replaced by `CZ(a, b)` under the measured bit.  Exact iff `z` is the XOR of the `Leaf` terms of that
    /// range and every other gate of the range is undone by the replay.  Temporaries alive at the end of the
    /// range (pebbles, `z`) are released by the replay.
    pub fn append_erase_sweep(&mut self, start: usize, end: usize, z: W) {
        let s = self.slot();
        self.meas(z, s);
        let sub: Vec<G> = self.g[start..end].to_vec();
        let mut map: std::collections::HashMap<u32, W> = std::collections::HashMap::new();
        let get = |map: &std::collections::HashMap<u32, W>, w: W| -> W {
            match w {
                W::Q(_) => w,
                W::T(i) => *map.get(&i).unwrap_or(&w),
            }
        };
        for &op in sub.iter().rev() {
            match op {
                G::Free(W::T(i)) => {
                    let n = self.alloc();
                    map.insert(i, n);
                }
                G::Alloc(W::T(i)) => {
                    let w = get(&map, W::T(i));
                    self.release(w);
                    map.remove(&i);
                }
                G::X(a) => self.x(get(&map, a)),
                G::Cx(a, b) => self.cx(get(&map, a), get(&map, b)),
                G::Ccx(a, b, t) => self.ccx(get(&map, a), get(&map, b), get(&map, t)),
                G::Fred(c, a, b) => self.fred(get(&map, c), get(&map, a), get(&map, b)),
                G::AndC(a, b, t) => self.g.push(G::AndU(get(&map, a), get(&map, b), get(&map, t))),
                G::AndU(a, b, t) => self.g.push(G::AndC(get(&map, a), get(&map, b), get(&map, t))),
                G::Leaf(a, b, zz) => {
                    assert_eq!(get(&map, zz), z, "erase sweep: a Leaf targets another wire");
                    self.cz_if(get(&map, a), get(&map, b), s)
                }
                G::MLeaf(i) => {
                    let d = self.mleaves[i as usize].clone();
                    assert_eq!(get(&map, d.z), z, "erase sweep: an MLeaf targets another wire");
                    let nd = MLeafDesc {
                        ctrls: d.ctrls.iter().map(|&w| get(&map, w)).collect(),
                        z,
                        dirty: d.dirty.iter().map(|&w| get(&map, w)).collect(),
                    };
                    self.mleaves.push(nd);
                    self.g.push(G::MPhaseIf(self.mleaves.len() as u32 - 1, s));
                }
                G::Meas(..) | G::CzIf(..) | G::MPhaseIf(..) => panic!("erase sweep over a measured range"),
                G::Alloc(W::Q(_)) | G::Free(W::Q(_)) => unreachable!(),
            }
        }
    }
    /// Scored Toffoli when emitted forward / reversed.
    pub fn t_fwd(&self) -> usize {
        self.g.iter().filter(|o| matches!(o, G::Ccx(..) | G::Fred(..) | G::AndC(..) | G::Leaf(..))).count() + self.t_multi()
    }
    pub fn t_rev(&self) -> usize {
        self.g.iter().filter(|o| matches!(o, G::Ccx(..) | G::Fred(..) | G::AndU(..) | G::Leaf(..))).count() + self.t_multi()
    }
    /// Toffolis of the multi-controlled leaves (static count; a phase entry runs only under its measured bit).
    fn t_multi(&self) -> usize {
        self.g
            .iter()
            .map(|o| match o {
                G::MLeaf(i) => mcx_t(self.mleaves[*i as usize].ctrls.len()),
                G::MPhaseIf(i, _) => mphase_t(self.mleaves[*i as usize].ctrls.len()),
                _ => 0,
            })
            .sum()
    }
    /// Expected executed Toffolis forward: AndU erases are free, phase entries run half the time.
    pub fn t_expected(&self) -> f64 {
        self.g
            .iter()
            .map(|o| match o {
                G::Ccx(..) | G::Fred(..) | G::AndC(..) | G::Leaf(..) => 1.0,
                G::MLeaf(i) => mcx_t(self.mleaves[*i as usize].ctrls.len()) as f64,
                G::MPhaseIf(i, _) => 0.5 * mphase_t(self.mleaves[*i as usize].ctrls.len()) as f64,
                _ => 0.0,
            })
            .sum()
    }
    pub fn has_meas(&self) -> bool {
        self.g.iter().any(|o| matches!(o, G::Meas(..) | G::CzIf(..) | G::MPhaseIf(..)))
    }
}

fn q(map: &[Option<QubitId>], w: W) -> QubitId {
    match w {
        W::Q(x) => x,
        W::T(i) => map[i as usize].expect("temp used while not allocated"),
    }
}

fn fredkin(c: &mut Builder, ctrl: QubitId, a: QubitId, b: QubitId) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

fn and_meas(c: &mut Builder, t: QubitId, a: QubitId, b: QubitId) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.cz_if(a, b, m);
    c.free_bit(m);
}

/// Phase `(-1)^AND(qs)` under classical bit `bit`, on `qs.len() - 2` dirty wires: m <= 2 is a conditioned CZ / Z;
/// otherwise, inside a condition block, toggle the first dirty wire by AND(qs[..m-1]) around two CZs with qs[m-1].
fn mphase_emit(c: &mut Builder, qs: &[QubitId], dirty: &[QubitId], bit: BitId) {
    let m = qs.len();
    if m <= 2 {
        let (a, b) = if m == 1 { (qs[0], qs[0]) } else { (qs[0], qs[1]) };
        c.cz_if(a, b, bit);
        return;
    }
    assert!(dirty.len() >= m - 2);
    let (dd, rest) = (dirty[0], &dirty[1..]);
    c.push_condition(bit);
    for _ in 0..2 {
        {
            let cc = std::cell::RefCell::new(&mut *c);
            mcx_seq(&qs[..m - 1], dd, rest, &mut |a, b, t| cc.borrow_mut().ccx(a, b, t), &mut |a, b| cc.borrow_mut().cx(a, b));
        }
        c.cz(dd, qs[m - 1]);
    }
    c.pop_condition();
}

/// Emit `gl` forward (`rev = false`) or as its exact inverse.
pub fn emit(c: &mut Builder, gl: &Gl, rev: bool) {
    assert!(!(rev && gl.has_meas()), "a block with measurements is self-inverse: emit it forward");
    let mut map: Vec<Option<QubitId>> = vec![None; gl.nt as usize];
    let mut slots: Vec<Option<BitId>> = vec![None; gl.nslots as usize];
    let ops: Box<dyn Iterator<Item = &G>> = if rev { Box::new(gl.g.iter().rev()) } else { Box::new(gl.g.iter()) };
    for &op in ops {
        match (op, rev) {
            (G::Alloc(W::T(i)), false) | (G::Free(W::T(i)), true) => {
                map[i as usize] = Some(c.alloc_qubit());
            }
            (G::Free(W::T(i)), false) | (G::Alloc(W::T(i)), true) => {
                let x = map[i as usize].take().unwrap();
                c.release_clean(x);
            }
            (G::X(a), _) => c.x(q(&map, a)),
            (G::Cx(a, b), _) => c.cx(q(&map, a), q(&map, b)),
            (G::Ccx(a, b, t), _) | (G::Leaf(a, b, t), _) => c.ccx(q(&map, a), q(&map, b), q(&map, t)),
            (G::Fred(x, a, b), _) => fredkin(c, q(&map, x), q(&map, a), q(&map, b)),
            (G::AndC(a, b, t), false) | (G::AndU(a, b, t), true) => c.ccx(q(&map, a), q(&map, b), q(&map, t)),
            (G::AndU(a, b, t), false) | (G::AndC(a, b, t), true) => and_meas(c, q(&map, t), q(&map, a), q(&map, b)),
            (G::Meas(t, s), false) => {
                let b = c.alloc_bit();
                c.hmr(q(&map, t), b);
                slots[s as usize] = Some(b);
            }
            (G::CzIf(a, b, s), false) => c.cz_if(q(&map, a), q(&map, b), slots[s as usize].expect("slot")),
            (G::MLeaf(i), _) => {
                // self-inverse (a CX-type map), so the same sequence serves both directions
                let d = &gl.mleaves[i as usize];
                let ctrls: Vec<QubitId> = d.ctrls.iter().map(|&w| q(&map, w)).collect();
                let dirty: Vec<QubitId> = d.dirty.iter().map(|&w| q(&map, w)).collect();
                let cc = std::cell::RefCell::new(&mut *c);
                mcx_seq(&ctrls, q(&map, d.z), &dirty, &mut |a, b, t| cc.borrow_mut().ccx(a, b, t), &mut |a, b| cc.borrow_mut().cx(a, b));
            }
            (G::MPhaseIf(i, s), false) => {
                let d = &gl.mleaves[i as usize];
                let qs: Vec<QubitId> = d.ctrls.iter().map(|&w| q(&map, w)).collect();
                let dirty: Vec<QubitId> = d.dirty.iter().map(|&w| q(&map, w)).collect();
                let bit = slots[s as usize].expect("slot");
                mphase_emit(c, &qs, &dirty, bit);
            }
            _ => unreachable!("{op:?}"),
        }
    }
    for b in slots.into_iter().flatten() {
        c.free_bit(b);
    }
}
