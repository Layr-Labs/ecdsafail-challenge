//! O3's three-band crossing sessions on the K0 donor-Rust research vehicle.
//! The source contract is scratch/r8-o3.md; this module is below S1 assurance.
use super::*;
use std::cell::Cell;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum G3pSess { None, Hr, Ht, HtQ0 }
thread_local! {
    static G3P_SESS: Cell<G3pSess> = const { Cell::new(G3pSess::None) };
    static G3P_FRAME_DEPTH: Cell<usize> = const { Cell::new(0) };
}

pub(super) fn g3p_frame_active() -> bool { G3P_FRAME_DEPTH.with(Cell::get) > 0 }

pub(super) fn t1(sy: usize) -> usize {
    match sy { 1..=120 => 5, 121..=123 => 4, 124..=127 => 2, 128 => 1,
               _ => panic!("sy outside O3 public support: {sy}") }
}
pub(super) fn t2(sy: usize) -> usize {
    match sy { 1..=118 => 13, 119..=120 => 11, 121 => 10,
               122..=123 => 8, 124..=128 => 5,
               _ => panic!("sy outside O3 public support: {sy}") }
}

/// lowq-672: tier A (h = 1) for session `sess` (0 top, 1 middle, 2 bottom band, 3 the band holding bit 0) of an
/// act shot at (sy, sz): the session's parked band reaches Q[e0..) (bl(q) <= g + 1, the O3 frame tb = min(22, g)).
/// The predictor's QUOT_PRED_TBOCC uses the same occupancy.
pub(crate) fn tier_a(sess: u8, sy: usize, sz: usize, e0: usize) -> bool {
    let g = 257isize - sz as isize - sy as isize;
    let tbf = g.clamp(0, 22) as usize;
    let syc = sy.clamp(1, 128);
    let (a1, a2) = (t1(syc), t2(syc));
    let cnt = [a1.min(tbf + 1), (tbf + 1).saturating_sub(a1).min(a2 - a1), (tbf + 1).saturating_sub(a2)];
    let s = if sess == 3 { if tbf < a1 { 0 } else if tbf < a2 { 1 } else { 2 } } else { sess as usize };
    sy + cnt[s] > e0
}

fn t1_limit(j: usize) -> Option<usize> {
    match j { 0 => Some(128), 1 => Some(127), 2..=3 => Some(123),
              4 => Some(120), _ => None }
}
fn t2_limit(j: usize) -> Option<usize> {
    match j { 0..=4 => Some(128), 5..=7 => Some(123),
              8..=9 => Some(121), 10 => Some(120),
              11..=12 => Some(118), _ => None }
}

pub(super) struct Cross<'a> {
    pub fd: &'a Fd,
    pub cp: &'a ColPar,
    pub sc: &'a ColScr,
    pub pl: Option<&'a PlCol>,
    pub vform: &'a [G],
    /// lowq-672: the HT plays' unparked form (= vform without the two-engine tiers)
    pub vform_ht: &'a [G],
    pub parked: &'a [Vec<G>],
    pub parked_ht: &'a [Vec<G>],
    pub vg: &'a [G],
    pub zshift: &'a [G],
    pub zflip: &'a [G],
    pub zoff_on: bool,
    pub kmax: usize,
    pub mt: usize,
    /// lowq-672 two-engine tiers: (flag lane h, TH); every play sets h = [sy > TH] around its form
    pub tier: Option<(QubitId, usize)>,
}

impl Cross<'_> {
    fn c59e_g3(&self) -> bool { std::env::var_os("C59E_G3").is_some() }
    fn g3p(&self) -> bool { std::env::var("C59E_G3").as_deref() == Ok("3") }
    fn c63b_d7(&self) -> bool { self.g3p() && std::env::var("C63B_D7").as_deref() == Ok("1") }
    fn d7_boundary(&self, b: &B, mark: usize) {
        if self.c63b_d7() {
            super::super::frogdrop_col::mark(b, mark);
            #[cfg(test)] super::super::c59e_tests::c63b_play_boundary(b.ops.len(), mark,
                self.ak(), self.c(), self.fd.sx[0]);
        }
    }
    fn cc(&self, b: &mut B, hosts: &[(QubitId, bool)], body: impl FnOnce(&mut B)) {
        let mut seen = std::collections::BTreeSet::new();
        for &(q, negated) in hosts {
            assert!(seen.insert(q), "G3' duplicate CC host");
            if negated { b.x(q); }
            super::super::mask::R11O11_DECCC.with(|cc| cc.borrow_mut().push(q));
        }
        body(b);
        for &(q, negated) in hosts.iter().rev() {
            super::super::mask::R11O11_DECCC.with(|cc| {
                assert_eq!(cc.borrow_mut().pop(), Some(q), "G3' CC scope");
            });
            if negated { b.x(q); }
        }
    }
    fn cc_act(&self, b: &mut B, body: impl FnOnce(&mut B)) {
        self.cc(b, &[(self.act(), true)], body);
    }
    fn stage_begin(&self, stage: G3pSess, name: &'static str) {
        if self.g3p() {
            assert_eq!(G3P_SESS.with(Cell::get), G3pSess::None, "G3' nested session");
            assert_eq!(G3P_FRAME_DEPTH.with(Cell::get), 0, "G3' frame at stage entry");
            super::super::mask::R11O11_DECCC.with(|cc| assert!(cc.borrow().is_empty(), "G3' CC at stage entry"));
            G3P_SESS.with(|s| s.set(stage));
        }
        #[cfg(test)]
        super::super::g3p_audit::enter_session(name, &self.fd.sx, &self.sc.sz, self.fd.ph);
    }
    fn stage_end(&self) {
        if self.g3p() {
            assert_eq!(G3P_FRAME_DEPTH.with(Cell::get), 0, "G3' frame at stage exit");
            super::super::mask::R11O11_DECCC.with(|cc| assert!(cc.borrow().is_empty(), "G3' CC at stage exit"));
            G3P_SESS.with(|s| s.set(G3pSess::None));
        }
        #[cfg(test)]
        super::super::g3p_audit::exit_session();
    }
    fn ht_q0(&self, live: bool) {
        if self.g3p() {
            G3P_SESS.with(|s| {
                assert_eq!(s.get(), if live { G3pSess::Ht } else { G3pSess::HtQ0 });
                s.set(if live { G3pSess::HtQ0 } else { G3pSess::Ht });
            });
        }
    }
    fn play_frame(&self, b: &mut B, frame: &[G], inverse: bool) {
        if self.g3p() && inverse {
            G3P_FRAME_DEPTH.with(|d| { assert!(d.get() > 0); d.set(d.get() - 1); });
        }
        b.play(frame, inverse);
        if self.g3p() && !inverse { G3P_FRAME_DEPTH.with(|d| d.set(d.get() + 1)); }
    }
    fn z7(&self) -> QubitId {
        assert!(self.g3p());
        assert!(G3P_FRAME_DEPTH.with(Cell::get) > 0, "G3' sz7 outside frame");
        let z7 = self.sc.sz[7];
        assert!(z7 != self.act() && z7 != self.ak() && z7 != self.c(), "G3' sz7 role collision");
        z7
    }
    fn c0_host(&self) -> (QubitId, bool) {
        assert!(self.g3p());
        let neg = match G3P_SESS.with(Cell::get) {
            G3pSess::Hr => false, G3pSess::Ht => true,
            state => panic!("G3' c0 unavailable in {state:?}"),
        };
        (self.fd.ph, neg)
    }
    fn unique(&self, label: &str, lanes: &[QubitId]) {
        if self.g3p() {
            let set: std::collections::BTreeSet<_> = lanes.iter().copied().collect();
            assert_eq!(set.len(), lanes.len(), "G3' {label} lane collision");
        }
    }
    fn read_unique(&self, label: &str, source: &[QubitId], pre: &[QubitId]) {
        if self.g3p() {
            let mut lanes = self.fd.sy.clone();
            lanes.extend_from_slice(source);
            lanes.extend([self.ak(), self.c()]);
            lanes.extend_from_slice(pre);
            self.unique(label, &lanes);
        }
    }
    fn act(&self) -> QubitId { self.sc.g }
    fn c0(&self) -> QubitId { assert!(!self.g3p(), "G3' c0 needs explicit host"); self.c0_669() }
    fn c0_669(&self) -> QubitId { self.sc.f }
    fn x128(&self) -> QubitId { self.sc.bq }
    fn pzero(&self) -> QubitId { assert!(!self.g3p(), "G3' pzero needs explicit host"); self.pzero_669() }
    fn pzero_669(&self) -> QubitId { self.sc.cmpc }
    fn ak(&self) -> QubitId { if self.g3p() { self.sc.cmpc } else { self.fd.sx[VB] } }
    fn c(&self) -> QubitId { self.fd.sx[VB + 1] }
    fn sylo(&self) -> usize { self.cp.sy.0.max(1) }
    fn syhi(&self) -> usize { self.cp.sy.1.min(128) }
    fn dirty(&self) -> &[QubitId] { &self.sc.dirty }
    fn source(&self, span: usize) -> Vec<QubitId> {
        let mut s: Vec<_> = self.fd.q.iter().copied().take(span).collect();
        if s.len() < span { s.push(self.x128()); }
        assert_eq!(s.len(), span);
        s
    }
    fn natural_tl(&self, kk: usize) -> Vec<QubitId> {
        let span = (self.syhi() + 1).min(self.fd.ring.len() - kk);
        (0..span).map(|i| self.fd.ring[self.fd.ring.len() - 1 - kk - i]).collect()
    }
    fn frame_tl(&self, j: usize) -> Vec<QubitId> {
        let kk = 22 - j;
        let n = self.fd.ring.len();
        let span = (self.syhi() + 1).min(n - kk);
        (0..span).map(|i| self.fd.ring[(n - 1 - kk - i + 22) % n]).collect()
    }
    fn frame(&self, b: &mut B) -> Vec<G> {
        b8b_tb_frame(b, &self.fd.ring, &self.sc.sz, &self.fd.sy, self.dirty())
    }
    fn safe_chain(&self) -> [QubitId; 3] { assert!(!self.g3p(), "G3' safe_chain"); [self.c0(), self.pzero(), self.fd.sx[4]] }
    fn plain_chain(&self) -> Vec<QubitId> { if self.g3p() { vec![self.x128()] } else { vec![self.c0(), self.pzero(), self.x128()] } }
    /// lowq-672 L672_MID8=1: the crossing middle touches only sx0, sx1, sx6, sx7 of the spare register (plus act, c0,
    /// x128, pzero): selector temps on sx1 / c0 / pzero, compares through the exact dirty compact comparator,
    /// two-lane decoder banks (needs L672_J1Q=1: no top-band SX slots)
    fn mid8(&self) -> bool { mid8() }
    /// the three selector temps (x[1], x[2], x[3] of the 13-lane layout)
    fn xt(&self, i: usize) -> QubitId {
        assert!(!self.g3p(), "G3' xt");
        if self.c59e_g3() { return [self.c(), self.pzero(), self.pzero()][i - 1]; }
        if self.mid8() { [self.fd.sx[1], self.c0(), self.pzero()][i - 1] } else { self.fd.sx[i] }
    }
    /// the erase / take selector (sx[4] of the 13-lane layout)
    fn sel(&self) -> QubitId { if self.g3p() { self.z7() } else if self.c59e_g3() { self.pzero() } else if self.mid8() { self.fd.sx[1] } else { self.fd.sx[4] } }

    fn sy_le(&self, b: &mut B, limit: usize, target: QubitId, safe: bool) {
        if limit == 128 { b.x(target); }
        else if self.c59e_g3() {
            super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize, target, &[], self.dirty());
            b.x(target);
        }
        else if self.mid8() {
            super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize, target, &[], self.dirty());
            b.x(target);
        }
        else {
            let chain = if safe {
                if target == self.fd.sx[4] { vec![self.c0(), self.pzero(), self.fd.sx[5]] }
                else { self.safe_chain().to_vec() }
            } else { self.plain_chain() };
            super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize,
                                               target, &chain, self.dirty());
            b.x(target);
        }
    }
    fn sy_le_alt(&self, b: &mut B, limit: usize, target: QubitId) {
        if limit == 128 { b.x(target); }
        else if self.c59e_g3() || self.mid8() { self.sy_le(b, limit, target, true); }
        else {
            let chain = [self.c0(), self.pzero(), self.fd.sx[5]];
            super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize,
                                               target, &chain, self.dirty());
            b.x(target);
        }
    }
    fn tb_ge(&self, b: &mut B, j: usize, target: QubitId, safe: bool) {
        if j == 0 { b.x(target); }
        else {
            let chain: Vec<QubitId> = if self.c59e_g3() || self.mid8() { vec![] }
                                      else if safe { self.safe_chain().to_vec() } else { self.plain_chain().to_vec() };
            super::super::frogdrop_col::ge_cd(b, &self.sc.sz[..5], j as isize,
                                               target, &chain, self.dirty());
        }
    }

    /// Prepare ak from restored sy and the frame code, clear the selector
    /// temps before `body`, then reverse the same prep after the body.
    fn with_tb_gate(&self, b: &mut B, j: usize, family: u8, body: impl FnOnce(&mut B)) {
        assert!(j <= 12 && family < 3);
        if self.c59e_g3() {
            let (xt1, xt23) = (self.c(), if self.g3p() { self.z7() } else { self.pzero() });
            let prep = rec(b, |b| {
                self.tb_ge(b, j, xt1, true);
                if family == 0 {
                    if let Some(s) = t1_limit(j) { self.sy_le(b, s, xt23, true); }
                } else if family == 1 {
                    if let Some(s) = t2_limit(j) { self.sy_le(b, s, xt23, true); }
                    if let Some(s) = t1_limit(j) { self.sy_le(b, s, xt23, true); }
                } else if let Some(s) = t2_limit(j) { self.sy_le(b, s, xt23, true); }
                let exists = if family == 0 { t1_limit(j).is_some() } else { t2_limit(j).is_some() };
                if exists { mc_xor(b, &[(self.act(), false), (xt1, false), (xt23, false)], self.ak(), &[], self.dirty()); }
                if family == 0 {
                    if let Some(s) = t1_limit(j) { self.sy_le(b, s, xt23, true); }
                } else if family == 1 {
                    if let Some(s) = t1_limit(j) { self.sy_le(b, s, xt23, true); }
                    if let Some(s) = t2_limit(j) { self.sy_le(b, s, xt23, true); }
                } else if let Some(s) = t2_limit(j) { self.sy_le(b, s, xt23, true); }
                self.tb_ge(b, j, xt1, true);
            });
            b.play(&prep, false);
            body(b);
            b.play(&prep, true);
            return;
        }
        let x = [self.fd.sx[0], self.xt(1), self.xt(2), self.xt(3)];
        let prep = rec(b, |b| {
            self.tb_ge(b, j, x[1], true);
            let mut ctl = vec![(self.act(), false), (x[1], false)];
            if family == 0 {
                if let Some(s) = t1_limit(j) { self.sy_le(b, s, x[2], true); ctl.push((x[2], false)); }
            } else {
                if family == 1 {
                    if let Some(s) = t1_limit(j) { self.sy_le(b, s, x[2], true); ctl.push((x[2], true)); }
                }
                if let Some(s) = t2_limit(j) { self.sy_le(b, s, x[3], true); ctl.push((x[3], false)); }
            }
            if family == 0 && t1_limit(j).is_none() { /* no top bit at this j */ }
            else if family != 0 && t2_limit(j).is_none() { /* no bit */ }
            else { mc_xor(b, &ctl, self.ak(), &[], self.dirty()); }
            if let Some(s) = t2_limit(j) { if family != 0 { self.sy_le(b, s, x[3], true); } }
            if let Some(s) = t1_limit(j) { if family != 2 { self.sy_le(b, s, x[2], true); } }
            self.tb_ge(b, j, x[1], true);
        });
        b.play(&prep, false);
        body(b);
        b.play(&prep, true);
    }

    /// Top slots fill sx[1..5] as they are unpacked. Decode without those
    /// slots, using the returned carry and P-zero lanes only between plays.
    fn with_top_slot_gate(&self, b: &mut B, j: usize, body: impl FnOnce(&mut B)) {
        let xt23 = if self.g3p() { self.z7() } else { self.pzero() };
        let exists = |b: &mut B| {
            if j == 0 { b.x(self.c()); }
            else { super::super::frogdrop_col::ge_cd(b, &self.sc.sz[..5], j as isize,
                self.c(), &[], self.dirty()); }
        };
        let prep = rec(b, |b| {
            exists(b);
            if let Some(limit) = t1_limit(j) {
                if limit == 128 { b.x(xt23); }
                else {
                    super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize,
                        xt23, &[], self.dirty());
                    b.x(xt23);
                }
                mc_xor(b, &[(self.act(), false), (self.c(), false), (xt23, false)],
                       self.ak(), &[], self.dirty());
                if limit == 128 { b.x(xt23); }
                else {
                    b.x(xt23);
                    super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize,
                        xt23, &[], self.dirty());
                }
            }
            exists(b);
        });
        b.play(&prep, false);
        body(b);
        b.play(&prep, true);
    }

    /// In a join the five top bits occupy sx[1..5], so no decoder may use
    /// those lanes. The bit exists iff j<=tb.
    fn with_tb_exists(&self, b: &mut B, j: usize, safe: bool, body: impl FnOnce(&mut B)) {
        let prep = rec(b, |b| {
            self.tb_ge(b, j, self.c(), safe);
            mc_xor(b, &[(self.act(), false), (self.c(), false)], self.ak(), &[], self.dirty());
            self.tb_ge(b, j, self.c(), safe);
        });
        b.play(&prep, false);
        body(b);
        b.play(&prep, true);
    }

    /// Form v'=v+T2(sy) modulo 64 after vg, and reverse before vg is undone.
    fn vprime(&self, b: &mut B) -> Vec<G> {
        let v = &self.sc.sz[..VB];
        rec(b, |b| {
            super::super::modp_frogdrop::add_const_exact(b, v, None, 5, self.dirty());
            for &(limit, amount) in &[(123, 3u64), (121, 2), (120, 1), (118, 2)] {
                // (sx[1]: a selector temp in both layouts)
                let temp = if self.c59e_g3() { self.c() } else { self.fd.sx[1] };
                self.sy_le(b, limit, temp, true);
                super::super::modp_frogdrop::add_const_exact(b, v, Some(temp), amount, self.dirty());
                self.sy_le(b, limit, temp, true);
            }
        })
    }
    fn with_bottom_gate(&self, b: &mut B, kk: usize, body: impl FnOnce(&mut B)) {
        assert!(kk < 10);
        let v = &self.sc.sz[..VB];
        let t = if self.c59e_g3() { self.c() } else { self.fd.sx[1] };
        let chain: Vec<QubitId> = if self.c59e_g3() || self.mid8() { vec![] } else { self.safe_chain().to_vec() };
        let prep = rec(b, |b| {
            super::super::frogdrop_col::ge_cd(b, v, (40 - kk) as isize, t, &chain, self.dirty());
            b.x(t);
            mc_xor(b, &[(self.act(), false), (t, false)], self.ak(), &[], self.dirty());
            b.x(t);
            super::super::frogdrop_col::ge_cd(b, v, (40 - kk) as isize, t, &chain, self.dirty());
        });
        b.play(&prep, false);
        body(b);
        b.play(&prep, true);
    }

    fn top_flag(&self, b: &mut B, j: usize) {
        if j == 0 {
            mc_xor(b, &[(self.sc.sz[5], true), (self.sc.sz[6], true)],
                   self.fd.sx[0], &[], self.dirty());
        }
    }
    fn inplace_at(&self, b: &mut B, tl: &[QubitId]) {
        let leaves: Vec<(usize, QubitId)> = (self.sylo()..=self.syhi())
            .filter_map(|v| tl.get(v).copied().map(|q| (v, q))).collect();
        let mut swaps = vec![];
        let root = swap_tree(&self.fd.sy, &leaves, self.fd.sy.len(), &mut swaps);
        for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
        super::super::mid2::mc_swap(b, &[(self.ak(), false)], root, self.c(), &[], self.dirty());
        for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
    }
    fn park_lane(&self, b: &mut B, family: u8, bit: usize, mode: u8, flight: QubitId,
                 control: QubitId) {
        // family: 0 top-relative j, 1 middle-relative j, 2 natural kk.
        // mode: 0 XOR flight into the Q position; 1 controlled swap.
        let leaves: Vec<(usize, QubitId)> = (self.sylo()..=self.syhi())
            .filter_map(|sy| {
                let idx = match family { 0 | 2 => bit, 1 => bit.saturating_sub(t1(sy)),
                                         _ => unreachable!() };
                let pos = sy + idx;
                if pos < self.fd.q.len() { Some((sy, self.fd.q[pos])) }
                else if pos == self.fd.q.len() { Some((sy, self.x128())) }
                else { None }
            }).collect();
        assert!(!leaves.is_empty());
        let mut swaps = vec![];
        let root = swap_tree(&self.fd.sy, &leaves, self.fd.sy.len(), &mut swaps);
        for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
        if mode == 0 { b.cx(flight, root); }
        else if mode == 1 {
            super::super::mid2::mc_swap(b, &[(control, false)], root, flight, &[], self.dirty());
        } else if mode == 2 {
            mc_xor(b, &[(control, false), (flight, false)], root, &[], self.dirty());
        } else {
            assert_eq!(mode, 3);
            super::super::mid2::mc_swap(b, &[(self.ak(), false), (control, false)],
                                        root, flight, &[], self.dirty());
        }
        for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
    }
    fn q0_move(&self, b: &mut B, slot: QubitId) {
        let pre: &[QubitId] = if self.g3p() { &[] } else { &self.fd.sx[1..4] };
        b7b_move_q0(b, &self.fd.q, self.x128(), &self.fd.sy,
                    self.sylo(), self.syhi(), slot, self.act(),
                    pre, self.dirty());
    }
    fn cmp_y_at(&self, b: &mut B, tl: &[QubitId], masked: bool) {
        let s = self.source(tl.len());
        if masked {
            if self.g3p() {
                let frame = G3P_FRAME_DEPTH.with(Cell::get) > 0;
                let (c0, ht) = self.c0_host();
                let pre = if frame { vec![self.act()] } else {
                    assert_eq!(G3P_SESS.with(Cell::get), G3pSess::Hr);
                    vec![]
                };
                let mask = if frame { self.z7() } else { self.act() };
                let mut roles = vec![self.ak(), self.c(), c0, mask];
                roles.extend_from_slice(&pre);
                self.unique("masked compare", &roles);
                let mut hosts = vec![(self.act(), true)];
                if frame { hosts.push((mask, false)); }
                hosts.push((c0, ht));
                self.cc(b, &hosts, |b| b7b_masked_cmp_y(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                    self.ak(), self.c(), c0, mask, &pre, self.dirty(), true));
                return;
            }
            if self.c59e_g3() {
                self.cc_act(b, |b| b7b_masked_cmp_y(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                    self.ak(), self.c(), self.c0(), self.pzero(), &[self.act()], self.dirty(), true));
                return;
            }
            let (pre, mask): (Vec<QubitId>, QubitId) = if self.mid8() { (vec![self.fd.sx[1]], self.pzero()) }
                else { (vec![self.fd.sx[1], self.fd.sx[2], self.fd.sx[3], self.fd.sx[4], self.pzero()], self.fd.sx[5]) };
            b7b_masked_cmp_y(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                             self.ak(), self.c(), self.c0(), mask,
                             &pre, self.dirty(), true);
        } else {
            if self.g3p() { self.read_unique("unmasked read", &s, &[]); }
            let rd = s.clone();
            let mut mid = |b: &mut B| {
                let lane = |v: usize| rd.get(v).copied();
                read_lane(b, &self.fd.sy, self.sylo(), self.syhi(), &lane, true,
                          &[(self.ak(), false)], self.c(), &[], &[], self.dirty());
            };
            let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| self.c());
            if self.g3p() {
                let (c0, ht) = self.c0_host();
                self.cc(b, &[(c0, ht)], |b| ripple(b, tl, &s, c0, true, &mut mid, &mut gate));
            } else { ripple(b, tl, &s, self.c0(), true, &mut mid, &mut gate); }
        }
    }
    fn mul_back_at(&self, b: &mut B, tl: &[QubitId]) {
        let r = rec(b, |b| self.cmp_y_at(b, tl, false));
        b.play(&r, true);
    }
    fn masked_mul_back_at(&self, b: &mut B, tl: &[QubitId]) {
        let r = rec(b, |b| self.cmp_y_at(b, tl, true));
        b.play(&r, true);
    }
    fn masked_add_at(&self, b: &mut B, tl: &[QubitId]) {
        let s = self.source(tl.len());
        if self.g3p() {
            assert_eq!(G3P_SESS.with(Cell::get), G3pSess::HtQ0, "G3' masked add outside q0 window");
            let frame = G3P_FRAME_DEPTH.with(Cell::get) > 0;
            let mut pre = vec![self.act()];
            let mut hosts = vec![(self.act(), true)];
            if frame { let z7 = self.z7(); pre.push(z7); hosts.push((z7, false)); }
            let mask = self.fd.sx[0];
            let mut roles = vec![self.c(), self.ak(), mask];
            roles.extend_from_slice(&pre);
            self.unique("masked add", &roles);
            hosts.push((self.ak(), true));
            self.cc(b, &hosts, |b| b7b_masked_add_y(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                self.c(), self.ak(), mask, &pre, self.dirty(), false));
            return;
        }
        if self.c59e_g3() {
            self.cc_act(b, |b| b7b_masked_add_y(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                self.c(), self.c0(), self.pzero(), &[self.act()], self.dirty(), false));
            return;
        }
        let (pre, mask): (Vec<QubitId>, QubitId) = if self.mid8() { (vec![self.pzero()], self.fd.sx[1]) }
            else { (vec![self.fd.sx[1], self.fd.sx[2], self.fd.sx[3], self.fd.sx[4], self.pzero()], self.fd.sx[5]) };
        b7b_masked_add_y(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                         self.c(), self.c0(), mask, &pre, self.dirty(), false);
    }
    fn vbit_at(&self, b: &mut B, tl: &[QubitId], top_live: bool) {
        let s = self.source(tl.len());
        if self.g3p() {
            let (c0, ht) = self.c0_host();
            let second = if top_live { self.z7() } else { self.fd.sx[0] };
            let pre = [self.act(), second];
            self.unique("v-bit pre", &pre);
            self.unique("v-bit roles", &[self.ak(), self.c(), c0, pre[0], pre[1]]);
            self.read_unique("v-bit read", &s, &pre);
            if top_live { assert_ne!(second, self.fd.sx[0]); }
            let mut hosts = vec![(self.act(), true)];
            if top_live { hosts.push((second, false)); }
            hosts.push((c0, ht));
            self.cc(b, &hosts, |b| b7b_v_bit(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                self.ak(), self.fd.sx[0], self.c(), c0, &pre, self.dirty()));
            return;
        }
        if self.c59e_g3() {
            self.cc_act(b, |b| b7b_v_bit(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                self.ak(), self.fd.sx[0], self.c(), self.c0(), &[self.act(), self.pzero()], self.dirty()));
            return;
        }
        let pre: Vec<QubitId> = if self.mid8() {
            let mut p = vec![self.fd.sx[1]];
            if self.pzero() != self.sc.sw { p.push(self.pzero()); }
            p
        }
            else { vec![self.fd.sx[1], self.fd.sx[2], self.fd.sx[3], self.fd.sx[4], self.fd.sx[5], self.c0(), self.pzero()] };
        b7b_v_bit(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                  self.ak(), self.fd.sx[0], self.c(), self.c0(), &pre, self.dirty());
    }
    fn extract_at(&self, b: &mut B, tl: &[QubitId]) {
        b7b_extract_v_bit(b, tl, &self.fd.sy, self.sylo(), self.syhi(),
                          self.ak(), self.fd.sx[0], self.c(), self.dirty());
    }
    fn store_at(&self, b: &mut B, tl: &[QubitId]) {
        b7b_store_v_bit(b, tl, &self.fd.sy, self.sylo(), self.syhi(),
                        self.ak(), self.fd.sx[0], self.c(), self.dirty());
    }

    fn sy_t1_eq(&self, b: &mut B, j: usize, target: QubitId) {
        match j {
            1 => { self.sy_le(b, 128, target, true); self.sy_le(b, 127, target, true); }
            2 => { self.sy_le(b, 127, target, true); self.sy_le(b, 123, target, true); }
            4 => { self.sy_le(b, 123, target, true); self.sy_le(b, 120, target, true); }
            5 => self.sy_le(b, 120, target, true),
            _ => {}
        }
    }
    fn sy_mid_high(&self, b: &mut B, j: usize, target: QubitId) {
        if j <= 1 || j >= 13 { return; }
        if self.c59e_g3() {
            if let Some(limit) = t2_limit(j) { self.sy_le(b, limit, target, true); }
            if let Some(limit) = t1_limit(j - 1) { self.sy_le(b, limit, target, true); }
            return;
        }
        let x = [self.fd.sx[0], self.xt(1), self.xt(2), self.xt(3)];
        if let Some(limit) = t1_limit(j - 1) { self.sy_le_alt(b, limit, x[2]); b.x(x[2]); }
        else { b.x(x[2]); }
        if let Some(limit) = t2_limit(j) { self.sy_le_alt(b, limit, x[3]); }
        mc_xor(b, &[(x[2], false), (x[3], false)], target, &[], self.dirty());
        if let Some(limit) = t2_limit(j) { self.sy_le_alt(b, limit, x[3]); }
        if let Some(limit) = t1_limit(j - 1) { b.x(x[2]); self.sy_le_alt(b, limit, x[2]); }
        else { b.x(x[2]); }
    }
    fn erase_mid(&self, b: &mut B, j: usize) {
        let sel = self.sel();
        if matches!(j, 1 | 2 | 4 | 5) {
            self.sy_t1_eq(b, j, sel);
            mc_xor(b, &[(self.c(), false), (sel, false)], self.fd.sx[0], &[], self.dirty());
            self.sy_t1_eq(b, j, sel);
        }
        if j >= 2 {
            self.sy_mid_high(b, j, sel);
            self.park_lane(b, 1, j, 2, self.c(), sel);
            self.sy_mid_high(b, j, sel);
        }
    }

    pub(super) fn toggle_hr_act(&self, b: &mut B) {
        let mut lits = vec![(self.fd.ph, true)];
        // Pool8 holds w on act itself in the off window.  Since w => !ph,
        // w XOR !ph is precisely the original HR act predicate.
        if self.cp.sw && !super::super::frogdrop_col::c55_pool8() { lits.push((self.sc.sw, true)); }
        mc_xor(b, &lits, self.act(), &[], self.dirty());
    }
    fn toggle_ht_w(&self, b: &mut B) {
        if !self.cp.sw || !super::super::frogdrop_col::c55_pool8() { return; }
        // Raw sz and sy are available at each HT play boundary.  Recreate
        // w = !ph & (sz <= 128) & (sz <= sy) into its parked host, then erase it with
        // the same reversible circuit after the parked form.
        let (w, fa, carry) = (if super::super::frogdrop_col::c66_direct() { self.fd.sx[7] } else { self.fd.sx[1] }, self.pzero_669(),
            if self.c63b_d7() { self.fd.sx[0] } else { self.c0_669() });
        assert!(fa != carry && w != carry, "D7 HT-w carry alias");
        super::super::frogdrop_col::ge_cd(b, &self.sc.sz, 129, fa, &[carry], self.dirty());
        let gt = super::super::arith::up_m(b, &self.fd.sy, &self.sc.sz, carry, true);
        b.play(&gt, false);
        mc_xor(b, &[(self.fd.ph, true), (fa, true), (self.sc.sz[7], true)], w, &[], self.dirty());
        b.play(&gt, true);
        super::super::frogdrop_col::ge_cd(b, &self.sc.sz, 129, fa, &[carry], self.dirty());
    }
    fn toggle_ht_act(&self, b: &mut B, flipped: bool) {
        if flipped { b.x(self.fd.ph); }
        if self.zoff_on && self.cp.dq { b.play(self.zshift, false); }
        let carry = if flipped {
            if self.c63b_d7() { self.ak() } else { self.c0_669() }
        } else { self.x128() };
        ht_act(b, self.fd, self.cp, self.sc, self.act(), &self.fd.sx[..1], carry, self.dirty());
        if self.zoff_on && self.cp.dq { b.play(self.zshift, true); }
        if flipped { b.x(self.fd.ph); }
    }
    /// lowq-672: h ^= tier_a(sess, sy, sz) over the column's public envelope (the two-engine tier flag): runs of
    /// consecutive sy values with one set of sz intervals, h ^= [a1 <= sy <= a2] & [l <= sz <= r] through a borrowed
    /// dirty lane d (h ^= Q d; d ^= P; h ^= Q d; d ^= P gives h ^= Q P)
    fn tier_flag(&self, b: &mut B, sess: u8) {
        if self.g3p() { assert!(self.tier.is_none(), "G3' requires B12A_P1=1"); }
        let Some((h, e0)) = self.tier else { return };
        // (L672_FORCE=A / B: every shot in tier A / B, a debugging control)
        match std::env::var("L672_FORCE").as_deref() { Ok("A") => { b.x(h); return; } Ok("B") => return, _ => {} }
        let (sylo, syhi) = (self.sylo(), self.syhi());
        let (szlo, szhi) = (self.cp.sz.0, self.cp.sz.1.min(255));
        let mut groups: Vec<(usize, usize, Vec<(usize, usize)>)> = vec![];
        for a in sylo..=syhi {
            let mut iv: Vec<(usize, usize)> = vec![];
            for z in szlo..=szhi {
                if !tier_a(sess, a, z, e0) { continue; }
                match iv.last_mut() { Some(l) if l.1 + 1 == z => l.1 = z, _ => iv.push((z, z)) }
            }
            match groups.last_mut() { Some(gr) if gr.2 == iv => gr.1 = a, _ => groups.push((a, a, iv)) }
        }
        let n = self.dirty().len();
        let d = self.dirty()[n - 1];
        let dl = &self.dirty()[..n - 1];
        let sy = &self.fd.sy;
        let sz = &self.sc.sz[..8];
        // t ^= [lo <= v <= hi] & AND(extra) ([v < hi + 1] ^ [v < lo], an interval reaching 255 as the complement)
        let iv_and = |b: &mut B, v: &[QubitId], lo: usize, hi: usize, extra: &[(QubitId, bool)], t: QubitId| {
            lt_const_and(b, v, hi + 1, extra, t, dl);
            lt_const_and(b, v, lo, extra, t, dl);
        };
        for (a1, a2, iv) in &groups {
            if iv.is_empty() { continue; }
            if iv.len() == 1 && iv[0] == (szlo, szhi) { iv_and(b, sy, *a1, *a2, &[], h); continue; }
            for _ in 0..2 {
                for &(lo, hi) in iv { iv_and(b, sz, lo, hi, &[(d, false)], h); }
                iv_and(b, sy, *a1, *a2, &[], d);
            }
        }
    }
    pub(super) fn play_hr(&self, b: &mut B, form: Option<usize>, inverse: bool, sess: u8) {
        #[cfg(test)] super::super::g3p_audit::enter_excluded();
        self.d7_boundary(b, 7300);
        self.toggle_hr_act(b);
        self.tier_flag(b, sess);
        self.d7_boundary(b, 7301);
        super::super::frogdrop_col::mark(b, 4000);
        b.play(form.map(|i| self.parked[i].as_slice()).unwrap_or(self.vform), inverse);
        super::super::frogdrop_col::mark(b, 7001); // qexact: end of an HR crossing play
        self.d7_boundary(b, 7302);
        self.tier_flag(b, sess);
        self.toggle_hr_act(b);
        self.d7_boundary(b, 7303);
        #[cfg(test)] super::super::g3p_audit::exit_excluded();
    }
    fn play_ht(&self, b: &mut B, form: Option<usize>, inverse: bool, sess: u8) {
        #[cfg(test)] super::super::g3p_audit::enter_excluded();
        self.d7_boundary(b, 7400);
        self.toggle_ht_w(b);
        b.cx(self.act(), self.fd.ph);
        self.toggle_ht_act(b, true);
        self.tier_flag(b, sess);
        self.d7_boundary(b, 7401);
        super::super::frogdrop_col::mark(b, 7100); // qexact: an HT crossing play
        b.play(form.map(|i| self.parked_ht[i].as_slice()).unwrap_or(self.vform_ht), inverse);
        super::super::frogdrop_col::mark(b, 7101);
        self.d7_boundary(b, 7402);
        self.tier_flag(b, sess);
        self.toggle_ht_act(b, true);
        b.cx(self.act(), self.fd.ph);
        self.toggle_ht_w(b);
        self.d7_boundary(b, 7403);
        #[cfg(test)] super::super::g3p_audit::exit_excluded();
    }

    fn search_frame(&self, b: &mut B, family: u8) {
        let (lo, hi) = if family == 0 { (0, 5) } else { (1, 13) };
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        for j in lo..hi {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, family, |b| {
                self.top_flag(b, j);
                self.vbit_at(b, &tl, family == 0 && j == 0);
                self.top_flag(b, j);
            });
        }
        for j in lo..hi {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, family, |b| {
                self.top_flag(b, j);
                self.extract_at(b, &tl);
                self.park_lane(b, family, j, 1, self.c(), self.ak());
                self.top_flag(b, j);
            });
        }
        self.play_frame(b, &frame, true);
    }

    fn search_bottom(&self, b: &mut B) {
        b.play(self.vg, false);
        let vp = self.vprime(b);
        b.play(&vp, false);
        for kk in (0..10).rev() {
            let tl = self.natural_tl(kk);
            self.with_bottom_gate(b, kk, |b| self.vbit_at(b, &tl, false));
        }
        for kk in (0..10).rev() {
            let tl = self.natural_tl(kk);
            self.with_bottom_gate(b, kk, |b| {
                self.extract_at(b, &tl);
                self.park_lane(b, 2, kk, 1, self.c(), self.ak());
            });
        }
        b.play(&vp, true);
        b.play(self.vg, true);
    }

    fn tt_adjust(&self, b: &mut B, down: bool) {
        if !self.cp.tt { return; }
        let xl: Vec<QubitId> = (0..self.mt).map(|m| self.fd.ring[self.fd.ring.len() - 1 - m]).collect();
        let dec = rec(b, |b| super::super::modp_frogdrop::inc_dirty(b, &xl, self.dirty(), self.c0()));
        b.play(&dec, down);
    }

    /// HR sessions S1-S3 and joins J1/J2. Stage 4 follows in a separate
    /// method so the original `stage(b)` boundary remains in the parent.
    pub(super) fn hr_pre(&self, b: &mut B) {
        self.stage_begin(G3pSess::Hr, "hr_pre");
        assert!((257..=259).contains(&self.fd.ring.len()));
        assert_eq!(self.kmax, 23);
        assert_eq!(self.parked.len(), 3);
        assert!(!self.cp.tt);
        if self.fd.ring.len() == 257 { b.play(self.zflip, false); }
        self.toggle_hr_act(b);

        // S1: clean top-down search in V, then extract the whole top band.
        self.play_hr(b, None, false, 0);
        super::super::frogdrop_col::mark(b, 4001);
        self.search_frame(b, 0);
        super::super::frogdrop_col::mark(b, 4002);
        self.play_hr(b, Some(0), true, 0);
        super::super::frogdrop_col::mark(b, 4003);
        // lowq-672 L672_J1Q=1: the top band stays parked in Q (no SX slots); J1 runs J2's masked form on it
        let j1q = std::env::var("L672_J1Q").map(|v| v == "1").unwrap_or(false);
        if self.g3p() { assert!(j1q, "G3' requires L672_J1Q=1"); }
        if !j1q {
            let frame = self.frame(b);
            self.play_frame(b, &frame, false);
            for j in 0..5 {
                self.with_top_slot_gate(b, j, |b| {
                    self.park_lane(b, 0, j, 1, self.fd.sx[1 + j], self.ak());
                });
            }
            self.play_frame(b, &frame, true);
        }
        super::super::frogdrop_col::mark(b, 4004);

        // J1: the top band is in SX slots, leaving a clean Y source (J1Q: parked in Q, a dirty source above sy).
        // (J1Q: the masked compare reads Q[sy] as its carry lane, so the band's bit 0 moves to sx0 first, as S2's
        // index zero does)
        if j1q { self.q0_move(b, self.fd.sx[0]); }
        self.tt_adjust(b, true);
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        // (J1Q: bit j is a top-band bit only where the top slot exists, j <= tb and sy <= t1_limit(j); elsewhere
        // Q[sy + j] is not the band's lane)
        let gate = |b: &mut B, j: usize, safe: bool, body: &mut dyn FnMut(&mut B)| {
            if j1q { self.with_top_slot_gate(b, j, |b| body(b)); } else { self.with_tb_exists(b, j, safe, |b| body(b)); }
        };
        for j in 0..5 {
            let tl = self.frame_tl(j);
            gate(b, j, j1q, &mut |b: &mut B| {
                self.cmp_y_at(b, &tl, j1q);
                if j1q && j == 0 { mc_xor(b, &[(self.ak(), false), (self.c(), false)], self.fd.sx[0], &[], self.dirty()); }
                else if j1q { self.park_lane(b, 0, j, 2, self.c(), self.ak()); }
                else { b.cx(self.c(), self.fd.sx[1 + j]); }
                self.inplace_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 4300 + j);
        }
        for j in (0..5).rev() {
            let tl = self.frame_tl(j);
            gate(b, j, false, &mut |b: &mut B| {
                self.inplace_at(b, &tl);
                self.mul_back_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 4400 + j);
        }
        self.play_frame(b, &frame, true);
        self.tt_adjust(b, false);
        super::super::frogdrop_col::mark(b, 4005);

        // S2: middle band into Q; its index zero moves to sx0.
        self.play_hr(b, None, false, 1);
        super::super::frogdrop_col::mark(b, 4006);
        self.search_frame(b, 1);
        super::super::frogdrop_col::mark(b, 4007);
        self.play_hr(b, Some(1), true, 1);
        self.q0_move(b, self.fd.sx[0]);
        super::super::frogdrop_col::mark(b, 4008);

        // J2: high parked Q is dirty source. Erase the middle band before
        // the clean exact inverse restores the search starting value.
        self.tt_adjust(b, true);
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        for j in 0..13 {
            let tl = self.frame_tl(j);
            self.with_tb_exists(b, j, true, |b| {
                self.cmp_y_at(b, &tl, true);
                self.erase_mid(b, j);
                self.inplace_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 4100 + j);
        }
        for j in (0..13).rev() {
            let tl = self.frame_tl(j);
            self.with_tb_exists(b, j, false, |b| {
                self.inplace_at(b, &tl);
                self.mul_back_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 4200 + j);
        }
        self.play_frame(b, &frame, true);
        self.tt_adjust(b, false);
        super::super::frogdrop_col::mark(b, 4009);

        // S3: bottom-aligned natural rounds. The bottom Q park persists
        // through the stage-4 masked division.
        self.play_hr(b, None, false, 2);
        super::super::frogdrop_col::mark(b, 4010);
        self.search_bottom(b);
        super::super::frogdrop_col::mark(b, 4011);
        self.play_hr(b, Some(2), true, 2);
        self.q0_move(b, self.fd.sx[0]);
        super::super::frogdrop_col::mark(b, 4012);
        self.toggle_hr_act(b);
        self.stage_end();
    }

    fn gate_nat(&self, b: &mut B, kk: usize, on: bool) {
        #[cfg(test)] super::super::g3p_audit::enter_gate_nat();
        if on { b.play(self.vg, false); }
        let v = &self.sc.sz[..VB];
        let t = self.fd.sx[0];
        super::super::frogdrop_col::ge_cd(b, v, (40 - kk) as isize, t,
                                           &self.plain_chain(), self.dirty());
        b.x(t);
        if on { b.and_c(self.act(), t, self.ak()); }
        else { b.and_u(self.act(), t, self.ak()); }
        b.x(t);
        super::super::frogdrop_col::ge_cd(b, v, (40 - kk) as isize, t,
                                           &self.plain_chain(), self.dirty());
        if !on { b.play(self.vg, true); }
        #[cfg(test)] super::super::g3p_audit::exit_gate_nat();
    }

    pub(super) fn hr_stage4(&self, b: &mut B) {
        self.stage_begin(G3pSess::Hr, "hr_stage4");
        #[cfg(test)] super::super::c59e_tests::C63_AK_LANES.with(|m| {
            *m.borrow_mut() = Some((self.sc.cmpc.0 as usize, self.fd.sx[6].0 as usize));
        });
        if self.g3p() { assert!(!self.cp.tt, "G3' tt_adjust uses old c0"); }
        self.tt_adjust(b, true);
        self.toggle_hr_act(b);
        // Phase 1: clear the in-place top/middle quotient while the bottom
        // band occupies Q above Y. These are no-erase masked divisions.
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        for j in 0..13 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 2, |b| {
                self.cmp_y_at(b, &tl, true);
                self.inplace_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 5100 + j);
        }
        self.play_frame(b, &frame, true);

        // Phase 2: bottom band in natural coordinates, with v'=v+T2(sy).
        b.play(self.vg, false);
        let vp = self.vprime(b);
        b.play(&vp, false);
        for kk in (0..10).rev() {
            let tl = self.natural_tl(kk);
            self.with_bottom_gate(b, kk, |b| {
                self.cmp_y_at(b, &tl, true);
                if kk == 0 { b.cx(self.c(), self.fd.sx[0]); }
                else { self.park_lane(b, 2, kk, 0, self.c(), self.act()); }
                self.inplace_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 5200 + kk);
        }
        b.play(&vp, true);
        b.play(self.vg, true);

        // The full quotient is now in the in-place lanes, Q and sx0 clean.
        if self.fd.ring.len() == 257 {
            if let Some(pl) = self.pl {
                #[cfg(test)] super::super::g3p_audit::enter_excluded();
                b.play(self.zshift, false);
                self.toggle_hr_act(b);
                super::super::payload::col_digit_phase_hr(b, self.fd, self.cp, self.sc, pl,
                    Some(false), super::super::payload::HrDigit::Cross { act_freed: true });
                self.toggle_hr_act(b);
                b.play(self.zshift, true);
                #[cfg(test)] super::super::g3p_audit::exit_excluded();
            }
        }
        // The exact inverse division shares each bit with the payload tick.
        let wtop = 259 - if self.cp.dl { self.cp.dlr.min(L0P + 1) } else { L0P + 1 };
        let nopad = std::env::var("FD_DINV_NOPAD").map(|v| v == "1").unwrap_or(false);
        if self.g3p() { assert!(nopad, "G3' requires FD_DINV_NOPAD=1"); }
        let pads = if nopad { vec![] } else if self.cp.dl {
            vec![self.x128(), self.pzero(), self.fd.sx[1], self.fd.sx[6], self.sc.sw, self.fd.ph]
        } else { vec![self.x128(), self.pzero()] };
        let slen = if nopad { wtop.min(self.fd.q.len()) } else { wtop.min(self.fd.q.len() + pads.len()) };
        let src = if self.pl.is_some() {
            if nopad { self.fd.q[..slen].to_vec() }
            else { super::super::payload::pad(&self.fd.q, &pads, slen) }
        } else { vec![] };
        for kk in 0..self.kmax {
            let tl = self.natural_tl(kk);
            self.gate_nat(b, kk, true);
            self.inplace_at(b, &tl);
            if self.cp.dl { self.gate_nat(b, kk, false); }
            if let Some(pl) = self.pl {
                let t: Vec<QubitId> = (kk..wtop).map(|pos| super::super::payload::wl(&pl.p, pos)).collect();
                let sl = (wtop - kk).min(slen);
                if self.g3p() {
                    self.cc(b, &[(self.fd.ph, false)], |b| super::super::payload::trans_one(b,
                        &t, &src[..sl], kk, false, vec![(self.c(), false)], None,
                        self.fd.sx[0], self.fd.ph, &[], &pl.dirty));
                } else {
                    super::super::payload::trans_one(b, &t, &src[..sl], kk, false,
                        vec![(self.c(), false)], None, self.fd.sx[0], self.c0(), &[], &pl.dirty);
                }
                super::super::frogdrop_col::mark(b, 1000 + kk);
            }
            if self.cp.dl { self.gate_nat(b, kk, true); }
            self.mul_back_at(b, &tl);
            self.gate_nat(b, kk, false);
            super::super::frogdrop_col::mark(b, 5300 + kk);
        }
        if self.fd.ring.len() == 257 { b.play(self.zflip, false); }
        self.toggle_hr_act(b);
        self.tt_adjust(b, false);
        self.stage_end();
    }

    fn take_mid(&self, b: &mut B, j: usize) {
        let sel = self.sel();
        if matches!(j, 1 | 2 | 4 | 5) {
            self.sy_t1_eq(b, j, sel);
            super::super::mid2::mc_swap(b, &[(self.ak(), false), (sel, false)],
                self.fd.ph, self.c(), &[], self.dirty());
            self.sy_t1_eq(b, j, sel);
        }
        if j >= 2 {
            self.sy_mid_high(b, j, sel);
            self.park_lane(b, 1, j, 3, self.c(), sel);
            self.sy_mid_high(b, j, sel);
        }
    }
    fn undo_frame_search(&self, b: &mut B, family: u8) {
        let (lo, hi) = if family == 0 { (0, 5) } else { (1, 13) };
        let r = rec(b, |b| {
            let frame = self.frame(b);
            self.play_frame(b, &frame, false);
            for j in lo..hi {
                let tl = self.frame_tl(j);
                self.with_tb_gate(b, j, family, |b| {
                    self.top_flag(b, j);
                    self.vbit_at(b, &tl, family == 0 && j == 0);
                    self.top_flag(b, j);
                });
            }
            self.play_frame(b, &frame, true);
        });
        b.play(&r, true);
    }
    fn undo_bottom_search(&self, b: &mut B) {
        let r = rec(b, |b| {
            b.play(self.vg, false);
            let vp = self.vprime(b);
            b.play(&vp, false);
            for kk in (0..10).rev() {
                let tl = self.natural_tl(kk);
                self.with_bottom_gate(b, kk, |b| self.vbit_at(b, &tl, false));
            }
            b.play(&vp, true);
            b.play(self.vg, true);
        });
        b.play(&r, true);
    }

    /// Stage 6: bottom, middle, top HT parked plays and exact add-back
    /// replay. Stage 5's quotient is in the X in-place lanes on entry.
    pub(super) fn ht_stage6(&self, b: &mut B) {
        self.stage_begin(G3pSess::Ht, "ht_stage6");
        self.toggle_ht_act(b, false);

        // S1 prep: park bottom, then fold top/middle while Q is dirty.
        b.play(self.vg, false);
        let vp = self.vprime(b);
        b.play(&vp, false);
        for kk in 0..10 {
            let tl = self.natural_tl(kk);
            self.with_bottom_gate(b, kk, |b| {
                self.inplace_at(b, &tl);
                self.park_lane(b, 2, kk, 1, self.c(), self.ak());
            });
            super::super::frogdrop_col::mark(b, 6100 + kk);
        }
        b.play(&vp, true);
        b.play(self.vg, true);
        self.q0_move(b, self.fd.sx[0]);
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        for j in (0..13).rev() {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 2, |b| {
                self.inplace_at(b, &tl);
                self.masked_mul_back_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 6120 + j);
        }
        self.play_frame(b, &frame, true);
        self.q0_move(b, self.fd.sx[0]);

        // S1: parked bottom into V by controlled add-back, then erase the
        // in-place search with the now-clean source.
        self.play_ht(b, Some(2), false, 2);
        b.cx(self.act(), self.fd.ph);
        self.q0_move(b, self.fd.ph);
        self.ht_q0(true);
        b.play(self.vg, false);
        let vp = self.vprime(b);
        b.play(&vp, false);
        for kk in (0..10).rev() {
            let tl = self.natural_tl(kk);
            self.with_bottom_gate(b, kk, |b| {
                if kk == 0 {
                    super::super::mid2::mc_swap(b, &[(self.ak(), false)],
                        self.fd.ph, self.c(), &[], self.dirty());
                } else { self.park_lane(b, 2, kk, 1, self.c(), self.ak()); }
                self.masked_add_at(b, &tl);
                self.store_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 6140 + kk);
        }
        b.play(&vp, true);
        b.play(self.vg, true);
        self.ht_q0(false);
        b.cx(self.act(), self.fd.ph);
        self.undo_bottom_search(b);
        self.play_ht(b, None, true, 2);

        // S2 prep: divide top+middle into place, park middle, then fold
        // the top band with the middle Q park as dirty source.
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        for j in 0..13 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 2, |b| {
                self.cmp_y_at(b, &tl, false);
                self.inplace_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 6160 + j);
        }
        for j in 1..13 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 1, |b| {
                self.inplace_at(b, &tl);
                self.park_lane(b, 1, j, 1, self.c(), self.ak());
            });
            super::super::frogdrop_col::mark(b, 6180 + j);
        }
        self.q0_move(b, self.fd.sx[0]);
        for j in (0..5).rev() {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 0, |b| {
                self.inplace_at(b, &tl);
                self.masked_mul_back_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 6200 + j);
        }
        self.play_frame(b, &frame, true);
        self.q0_move(b, self.fd.sx[0]);

        // S2 replay of the middle band.
        self.play_ht(b, Some(1), false, 1);
        b.cx(self.act(), self.fd.ph);
        self.q0_move(b, self.fd.ph);
        self.ht_q0(true);
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        for j in 1..13 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 1, |b| {
                self.take_mid(b, j);
                self.masked_add_at(b, &tl);
                self.store_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 6220 + j);
        }
        self.play_frame(b, &frame, true);
        self.ht_q0(false);
        b.cx(self.act(), self.fd.ph);
        self.undo_frame_search(b, 1);
        self.play_ht(b, None, true, 1);

        // S3 prep and top replay.
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        for j in 0..5 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 0, |b| {
                self.cmp_y_at(b, &tl, false);
                self.inplace_at(b, &tl);
            });
            super::super::frogdrop_col::mark(b, 6240 + j);
        }
        for j in 0..5 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 0, |b| {
                self.inplace_at(b, &tl);
                self.park_lane(b, 0, j, 1, self.c(), self.ak());
            });
            super::super::frogdrop_col::mark(b, 6260 + j);
        }
        self.play_frame(b, &frame, true);
        self.play_ht(b, Some(0), false, 0);
        b.cx(self.act(), self.fd.ph);
        self.q0_move(b, self.fd.ph);
        self.ht_q0(true);
        let frame = self.frame(b);
        self.play_frame(b, &frame, false);
        for j in 0..5 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 0, |b| {
                if j == 0 {
                    super::super::mid2::mc_swap(b, &[(self.ak(), false)],
                        self.fd.ph, self.c(), &[], self.dirty());
                } else { self.park_lane(b, 0, j, 1, self.c(), self.ak()); }
                self.masked_add_at(b, &tl);
                self.top_flag(b, j);
                self.store_at(b, &tl);
                self.top_flag(b, j);
            });
            super::super::frogdrop_col::mark(b, 6280 + j);
        }
        self.play_frame(b, &frame, true);
        self.ht_q0(false);
        b.cx(self.act(), self.fd.ph);
        self.undo_frame_search(b, 0);
        self.play_ht(b, None, true, 0);
        self.toggle_ht_act(b, false);
        if self.fd.ring.len() == 257 { b.play(self.zflip, false); }
        self.stage_end();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::super::tests_frogdrop::run;
    use super::super::super::g3p_audit;

    /// Emitted-op audit of the proposed 666 keep-set, independent of owners666.json.
    /// A single forbidden touch is a replayable counterexample for this trial.
    #[test]
    fn c59e_13s_kernel_emitted_lane_audit() {
        assert!(std::env::var_os("C59E_G3").is_some());
        let (mut b, fd, mut cp, sc, dirty) = rig();
        cp.col = 121;
        cp.hr = false;
        cp.ht = true;
        let cross = Cross { fd: &fd, cp: &cp, sc: &sc, pl: None,
            vform: &[], vform_ht: &[], parked: &[], parked_ht: &[], vg: &[], zshift: &[], zflip: &[],
            zoff_on: false, kmax: 23, mt: 129, tier: None };
        let flag = b.alloc();
        if cross.g3p() { G3P_FRAME_DEPTH.with(|d| d.set(1)); }
        cross.with_tb_gate(&mut b, 2, 1, |b| b.cx(cross.ak(), flag));
        if cross.g3p() { G3P_FRAME_DEPTH.with(|d| d.set(0)); }
        b.flush_global();
        let banned = [("sx1", fd.sx[1]), ("sx4", fd.sx[4]), ("sx6", fd.sx[6])];
        for (i, op) in b.ops.iter().enumerate() {
            for (name, lane) in banned {
                assert!(![op.q_control1, op.q_control2, op.q_target].contains(&lane),
                    "C59E_13S_FORBIDDEN col=HT121 kernel=with_tb_gate family=1 j=2 op={i} lane={name} kind={:?} control1={} control2={} target={}",
                    op.kind, op.q_control1.0, op.q_control2.0, op.q_target.0);
            }
        }
        let _ = dirty;
        if std::env::var("C59E_G3").as_deref() == Ok("3") {
            g3p_extended_emitted_lane_audit();
        }
    }

    fn g3p_extended_emitted_lane_audit() {
        // Each prep is emitted separately. A flush makes the inspected span
        // independent of cancellation in the next prep.
        let (mut b, fd, cp, sc, _) = rig();
        let cross = Cross { fd: &fd, cp: &cp, sc: &sc, pl: None,
            vform: &[], vform_ht: &[], parked: &[], parked_ht: &[], vg: &[],
            zshift: &[], zflip: &[], zoff_on: false, kmax: 23, mt: 129, tier: None };
        let flag = b.alloc();
        let mut census = 0usize;
        let mut check = |b: &mut B, label: &str| {
            b.flush_global();
            assert!(!b.ops.is_empty(), "G3P_AUDIT empty prep {label}");
            for (i, op) in b.ops.iter().enumerate() {
                for (name, lane) in [("sx1", fd.sx[1]), ("sx4", fd.sx[4]), ("sx6", fd.sx[6])] {
                    assert!(![op.q_control1, op.q_control2, op.q_target].contains(&lane),
                        "G3P_AUDIT prep={label} op={i} lane={name} kind={:?} control1={} control2={} target={}",
                        op.kind, op.q_control1.0, op.q_control2.0, op.q_target.0);
                }
            }
            census += 1;
            b.ops.clear();
        };
        G3P_FRAME_DEPTH.with(|d| d.set(1));
        for family in 0..3u8 {
            for j in 0..13 {
                cross.with_tb_gate(&mut b, j, family, |b| b.cx(cross.ak(), flag));
                check(&mut b, &format!("with_tb_gate family={family} j={j}"));
            }
        }
        for j in 0..5 {
            cross.with_top_slot_gate(&mut b, j, |b| b.cx(cross.ak(), flag));
            check(&mut b, &format!("with_top_slot_gate j={j}"));
        }
        for j in 0..13 {
            cross.with_tb_exists(&mut b, j, true, |b| b.cx(cross.ak(), flag));
            check(&mut b, &format!("with_tb_exists safe j={j}"));
            cross.with_tb_exists(&mut b, j, false, |b| b.cx(cross.ak(), flag));
            check(&mut b, &format!("with_tb_exists plain j={j}"));
        }
        G3P_FRAME_DEPTH.with(|d| d.set(0));
        for kk in 0..10 {
            cross.with_bottom_gate(&mut b, kk, |b| b.cx(cross.ak(), flag));
            check(&mut b, &format!("with_bottom_gate kk={kk}"));
        }
        assert_eq!(census, 80, "G3P_AUDIT prep census");
        eprintln!("G3P_PREP_AUDIT_PASS cases={census} families=3 top=5 exists=26 bottom=10");

        fn whole_stage(audit_col: usize, col: usize, hr: bool,
                       sw: bool, dl: bool, dq: bool, sy: (usize, usize),
                       sz: (usize, usize), mode: &str) {
            if mode == "3" { std::env::set_var("C59E_G3", "3"); }
            else { std::env::remove_var("C59E_G3"); }
            let (mut b, fd, mut cp, sc, dirty) = rig();
            cp.col = col;
            cp.hr = hr;
            cp.ht = !hr;
            cp.sw = sw; cp.dl = dl; cp.dq = dq;
            cp.sy = sy; cp.sz = sz;
            cp.dlr = if dl { 3 } else { 0 };
            let v = &sc.sz[..VB];
            let vg = record_vg(&mut b, v, &fd.sy[..VB],
                if mode == "3" { sc.cmpc } else { sc.f }, VOFF, &dirty);
            let parked: Vec<Vec<G>> = vec![vec![], vec![], vec![]];
            let cross = Cross { fd: &fd, cp: &cp, sc: &sc, pl: None,
                vform: &[], vform_ht: &[], parked: &parked, parked_ht: &parked, vg: &vg,
                zshift: &[], zflip: &[], zoff_on: false, kmax: 23, mt: 129, tier: None };
            g3p_audit::set_column(audit_col);
            cross.hr_pre(&mut b);
            cross.hr_stage4(&mut b);
            cross.ht_stage6(&mut b);
            b.flush_global();
            eprintln!("G3P_WHOLE_STAGE_BUILD audit_col={audit_col} col={col} hr={hr} mode={mode} ops={}", b.ops.len());
        }
        let settings = [
            (26, 26, true, false, false, false, (13, 99), (155, 241)),
            (76, 76, true, true, true, true, (1, 128), (105, 254)),
            (121, 121, false, false, false, false, (1, 128), (1, 255)),
            (1076, 76, false, true, false, true, (1, 128), (105, 254)),
        ];
        g3p_audit::begin_control();
        g3p_audit::set_pl_mode(false);
        for &(audit_col, col, hr, sw, dl, dq, sy, sz) in &settings {
            whole_stage(audit_col, col, hr, sw, dl, dq, sy, sz, "669");
        }
        g3p_audit::finish();
        g3p_audit::begin_candidate();
        g3p_audit::set_pl_mode(false);
        for &(audit_col, col, hr, sw, dl, dq, sy, sz) in &settings {
            whole_stage(audit_col, col, hr, sw, dl, dq, sy, sz, "3");
        }
        g3p_audit::finish();
        std::env::set_var("C59E_G3", "3");
        eprintln!("G3P_WHOLE_STAGE_AUDIT_PASS settings=4 stages=3");
    }

    fn rig() -> (B, Fd, ColPar, ColScr, Vec<QubitId>) {
        super::super::super::bake_knobs();
        let mut b = B::new();
        let ring = b.alloc_n(259);
        let q = b.alloc_n(128);
        let sy = b.alloc_n(8);
        let sx = b.alloc_n(8);
        let ph = b.alloc();
        let dirty = b.alloc_n(24);
        let pool = b.alloc_n(super::super::super::frogdrop_col::pool_size(24, 23, 8));
        let sc0 = ColScr::carve(&pool, &sx, &dirty, 24, 23, 40);
        let sc = if std::env::var_os("C59E_G3").is_some() { sc0.mid_alias(&sx) } else { sc0 };
        let fd = Fd { ring, q, sy, sx, ph, cnt: vec![] };
        let cp = ColPar {
            n: 259, nq: 128, h: 2, k: 0, kp: 24, qb: 23, tot: 83,
            sz: (1, 255), sy: (1, 128), smax: (1, 255), m: 0, tail: 40, emax: 28,
            hr: true, ht: true, sw: false, l0: 128, swl: (0, 0), dn: false, fin: false,
            nomap: false, tt: false, pht: false, psy: (0, 0), xw: 0, psw: false,
            cntw: 0, cntmax: 0, col: usize::MAX, dl: false, dq: false, dlr: 0,
        };
        (b, fd, cp, sc, dirty)
    }

    fn put_num(input: &mut [u64], bits: &[QubitId], shot: usize, value: usize) {
        for (i, &q) in bits.iter().enumerate() {
            if value >> i & 1 != 0 { input[q.0 as usize] |= 1u64 << shot; }
        }
    }

    /// lowq-672: the tier flag circuit equals tier_a on every (sy, sz) of the envelope, restores its borrowed lanes
    #[test]
    fn l672_tier_flag_matches_tier_a() {
        if std::env::var("C59E_G3").as_deref() == Ok("3") { return; }
        for &(szlo, szhi, sylo, syhi) in &[(101usize, 205usize, 52usize, 128usize), (105, 254, 1, 128), (110, 213, 42, 128)] {
            for sess in 0..4u8 {
                let (mut b, fd, mut cp, sc, dirty) = rig();
                cp.sz = (szlo, szhi); cp.sy = (sylo, syhi);
                let h = b.alloc();
                let cross = Cross { fd: &fd, cp: &cp, sc: &sc, pl: None,
                    vform: &[], vform_ht: &[], parked: &[], parked_ht: &[], vg: &[], zshift: &[], zflip: &[],
                    zoff_on: false, kmax: 23, mt: 129, tier: Some((h, 121)) };
                let r = rec(&mut b, |b| cross.tier_flag(b, sess));
                b.play(&r, false);
                let width = b.width() as usize;
                let pairs: Vec<(usize, usize)> = (sylo..=syhi).flat_map(|y| (szlo..=szhi).map(move |z| (y, z))).collect();
                for chunk in pairs.chunks(64) {
                    let mut input = vec![0u64; width];
                    for (i, &q) in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate() {
                        input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left((i * 7 % 64) as u32);
                    }
                    for (shot, &(y, z)) in chunk.iter().enumerate() {
                        put_num(&mut input, &fd.sy, shot, y);
                        put_num(&mut input, &sc.sz[..8], shot, z);
                    }
                    let mut expected = input.clone();
                    for (shot, &(y, z)) in chunk.iter().enumerate() {
                        if tier_a(sess, y, z, 121) { expected[h.0 as usize] |= 1u64 << shot; }
                    }
                    let out = run(&b.ops, width, &|q| *q = input.clone());
                    assert_eq!(out.phase, 0);
                    for (shot, &(y, z)) in chunk.iter().enumerate() {
                        let got = (out.q[h.0 as usize] >> shot) & 1;
                        assert_eq!(got == 1, tier_a(sess, y, z, 121), "sess {sess} sy {y} sz {z}");
                    }
                    assert_eq!(out.q, expected, "sess {sess} lanes restored");
                }
            }
        }
        eprintln!("L672_TIER_FLAG ok");
    }

    #[test]
    fn b8b_o3_all_threshold_predicates_and_vprime_all_wire() {
        // All active public (sy,g) pairs, including the twelve threshold
        // boundaries, with arbitrary ring/Q/dirty passengers and inverse.
        let pairs: Vec<(usize, usize)> = (1..=128)
            .flat_map(|sy| (0..=25).filter(move |&g| {
                let sz = 257 - sy - g;
                sy <= sz && sz <= 255
            }).map(move |g| (sy, g)))
            .collect();
        assert!(pairs.len() > 3000);

        let (mut b, fd, cp, sc, dirty) = rig();
        let flags = b.alloc_n(59);
        let cross = Cross { fd: &fd, cp: &cp, sc: &sc, pl: None,
            vform: &[], vform_ht: &[], parked: &[], parked_ht: &[], vg: &[], zshift: &[], zflip: &[],
            zoff_on: false, kmax: 23, mt: 129, tier: None };
        let pred = rec(&mut b, |b| {
            if cross.g3p() { G3P_FRAME_DEPTH.with(|d| d.set(1)); }
            for family in 0..3u8 {
                for j in 0..13 {
                    let flag = flags[(family as usize) * 13 + j];
                    cross.with_tb_gate(b, j, family, |b| b.cx(cross.ak(), flag));
                }
            }
            for j in 0..5 {
                cross.with_top_slot_gate(b, j, |b| b.cx(cross.ak(), flags[39 + j]));
            }
            for (i, &j) in [1usize, 2, 4, 5].iter().enumerate() {
                cross.sy_t1_eq(b, j, flags[44 + i]);
            }
            for j in 2..13 { cross.sy_mid_high(b, j, flags[48 + j - 2]); }
            if cross.g3p() { G3P_FRAME_DEPTH.with(|d| d.set(0)); }
        });
        b.play(&pred, false); let forward = b.ops.len();
        b.play(&pred, true);
        let width = b.width() as usize;
        for chunk in pairs.chunks(if cross.g3p() { 32 } else { 64 }) {
            let mut input = vec![0u64; width];
            for (i, &q) in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate() {
                input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left((i * 7 % 64) as u32);
            }
            input[sc.bq.0 as usize] = 0x6868_3c3c_f0f0_9696;
            input[fd.sx[0].0 as usize] = 0x7135_1a2b_c4d5_e6f7;
            if std::env::var_os("C59E_G3").is_none() {
                input[fd.sx[7].0 as usize] = 0x29c3_85f1_7a6b_402d;
            }
            if cross.g3p() {
                input[fd.sx[1].0 as usize] = 0x5a6c_72f0_961e_d3b4;
                input[fd.sx[4].0 as usize] = 0xd56b_394a_87e1_c02f;
                input[fd.sx[6].0 as usize] = 0x9462_ea31_57bc_d880;
                for shot in chunk.len()..64 {
                    put_num(&mut input, &fd.sy, shot, 1 + ((shot * 37 + chunk.len()) % 128));
                    put_num(&mut input, &sc.sz, shot, (shot * 73 + 135) & 255);
                    if shot % 2 == 1 { input[fd.ph.0 as usize] |= 1u64 << shot; }
                }
            }
            for (shot, &(sy, g)) in chunk.iter().enumerate() {
                put_num(&mut input, &fd.sy, shot, sy);
                let code = if g <= 22 { g } else { 22 + 32 * (g - 22) };
                put_num(&mut input, &sc.sz, shot, code);
                input[sc.g.0 as usize] |= 1u64 << shot;
            }
            let mut expected = input.clone();
            for (shot, &(sy, g)) in chunk.iter().enumerate() {
                let tb = g.min(22);
                for family in 0..3u8 {
                    for j in 0..13 {
                        let yes = j <= tb && match family {
                            0 => j < t1(sy),
                            1 => t1(sy) <= j && j < t2(sy),
                            _ => j < t2(sy),
                        };
                        if yes { expected[flags[(family as usize)*13+j].0 as usize] |= 1u64 << shot; }
                    }
                }
                for j in 0..5 {
                    if j <= tb && j < t1(sy) { expected[flags[39 + j].0 as usize] |= 1u64 << shot; }
                }
                for (i, &j) in [1usize, 2, 4, 5].iter().enumerate() {
                    if t1(sy) == j { expected[flags[44 + i].0 as usize] |= 1u64 << shot; }
                }
                for j in 2..13 {
                    let high = t2_limit(j).is_some_and(|limit| sy <= limit)
                        ^ t1_limit(j - 1).is_some_and(|limit| sy <= limit);
                    if high { expected[flags[48 + j - 2].0 as usize] |= 1u64 << shot; }
                }
            }
            if cross.g3p() {
                for shot in chunk.len()..64 {
                    let sy = 1 + ((shot * 37 + chunk.len()) % 128);
                    for (i, &j) in [1usize, 2, 4, 5].iter().enumerate() {
                        if t1(sy) == j { expected[flags[44 + i].0 as usize] |= 1u64 << shot; }
                    }
                    for j in 2..13 {
                        let high = t2_limit(j).is_some_and(|limit| sy <= limit)
                            ^ t1_limit(j - 1).is_some_and(|limit| sy <= limit);
                        if high { expected[flags[48 + j - 2].0 as usize] |= 1u64 << shot; }
                    }
                }
            }
            let out = run(&b.ops[..forward], width, &|q| *q = input.clone());
            assert_eq!(out.phase, 0);
            assert_eq!(out.q, expected, "frame predicates chunk={:?}", chunk.first());
            let back = run(&b.ops, width, &|q| *q = input.clone());
            assert_eq!(back.phase, 0);
            assert_eq!(back.q, input);
        }

        let (mut b, fd, cp, sc, dirty) = rig();
        let flags = b.alloc_n(10);
        let cross = Cross { fd: &fd, cp: &cp, sc: &sc, pl: None,
            vform: &[], vform_ht: &[], parked: &[], parked_ht: &[], vg: &[], zshift: &[], zflip: &[],
            zoff_on: false, kmax: 23, mt: 129, tier: None };
        let bottom = rec(&mut b, |b| {
            let vp = cross.vprime(b);
            b.play(&vp, false);
            for kk in 0..10 {
                cross.with_bottom_gate(b, kk, |b| b.cx(cross.ak(), flags[kk]));
            }
            b.play(&vp, true);
        });
        b.play(&bottom, false); let forward = b.ops.len();
        b.play(&bottom, true);
        let width = b.width() as usize;
        for chunk in pairs.chunks(64) {
            let mut input = vec![0u64; width];
            for (i, &q) in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate() {
                input[q.0 as usize] = 0x243f_6a88_85a3_08d3u64.rotate_left((i * 11 % 64) as u32);
            }
            input[sc.bq.0 as usize] = 0x69e2_31a5_52cb_467d;
            input[fd.sx[0].0 as usize] = 0xc368_2a74_59fb_10ed;
            for (shot, &(sy, g)) in chunk.iter().enumerate() {
                put_num(&mut input, &fd.sy, shot, sy);
                put_num(&mut input, &sc.sz[..6], shot, (39 + 64 - g) % 64);
                input[sc.g.0 as usize] |= 1u64 << shot;
            }
            let mut expected = input.clone();
            for (shot, &(sy, g)) in chunk.iter().enumerate() {
                let vp = (39 + 64 - g + t2(sy)) % 64;
                for kk in 0..10 {
                    if vp <= 39 - kk { expected[flags[kk].0 as usize] |= 1u64 << shot; }
                }
            }
            let out = run(&b.ops[..forward], width, &|q| *q = input.clone());
            assert_eq!(out.phase, 0);
            assert_eq!(out.q, expected, "vprime/bottom chunk={:?}", chunk.first());
            let back = run(&b.ops, width, &|q| *q = input.clone());
            assert_eq!(back.phase, 0);
            assert_eq!(back.q, input);
        }
        eprintln!("B8B_O3_PREDICATES pairs={} all_wire=true phase=0", pairs.len());
    }

    /// Compare the eight G3' body allocations with the trial-1 kernels on
    /// identical payload states. The withheld G3' lanes carry dirty passengers.
    #[test]
    fn g3p_eight_body_kernel_differential() {
        super::super::super::bake_knobs();
        assert_eq!(std::env::var("C59E_G3").as_deref(), Ok("3"));
        assert!(mid8(), "G3' short decoder bank required");
        fn build(form: usize, mode: &str) -> (B, Fd, ColScr, Vec<QubitId>) {
            std::env::set_var("C59E_G3", mode);
            let (mut b, fd, cp, sc, dirty) = rig();
            let cross = Cross { fd: &fd, cp: &cp, sc: &sc, pl: None,
                vform: &[], vform_ht: &[], parked: &[], parked_ht: &[], vg: &[],
                zshift: &[], zflip: &[], zoff_on: false, kmax: 23, mt: 129, tier: None };
            let frame = matches!(form, 0 | 1 | 3 | 7);
            let ht = matches!(form, 3 | 5 | 6 | 7);
            if mode == "3" {
                G3P_FRAME_DEPTH.with(|d| d.set(usize::from(frame)));
                G3P_SESS.with(|s| s.set(if matches!(form, 6 | 7) { G3pSess::HtQ0 }
                    else if ht { G3pSess::Ht } else { G3pSess::Hr }));
            }
            let tl = if frame { cross.frame_tl(usize::from(form == 1)) }
                     else { cross.natural_tl(0) };
            match form {
                0 => cross.vbit_at(&mut b, &tl, true),
                1 | 2 => cross.vbit_at(&mut b, &tl, false),
                3 | 4 => cross.cmp_y_at(&mut b, &tl, true),
                5 => cross.cmp_y_at(&mut b, &tl, false),
                6 | 7 => cross.masked_add_at(&mut b, &tl),
                _ => unreachable!(),
            }
            if mode == "3" {
                G3P_FRAME_DEPTH.with(|d| d.set(0));
                G3P_SESS.with(|s| s.set(G3pSess::None));
            }
            b.flush_global();
            (b, fd, sc, dirty)
        }
        let names = ["vbit_frame_top", "vbit_frame", "vbit_natural",
            "masked_cmp_frame", "masked_cmp_natural", "unmasked_cmp",
            "masked_add_natural", "masked_add_frame"];
        for form in 0..8 {
            let (control, fc, sc, dc) = build(form, "1");
            let (candidate, fp, sp, dp) = build(form, "3");
            assert_eq!(control.width(), candidate.width());
            assert_eq!(fc.sx, fp.sx);
            assert_eq!(fc.sy, fp.sy);
            assert_eq!(fc.q, fp.q);
            assert_eq!(fc.ring, fp.ring);
            assert_eq!(dc, dp);
            assert_eq!(sc.sz, sp.sz);
            let width = control.width() as usize;
            let act = 0x5555_5555_5555_5555u64;
            let ht = matches!(form, 3 | 5 | 6 | 7);
            for chunk in 0..4u64 {
                let mut base = vec![0u64; width];
                for (i, &q) in fc.ring.iter().chain(fc.q.iter()).chain(dc.iter()).enumerate() {
                    let mut x = (i as u64 + 0x9e37_79b9_7f4a_7c15u64) ^ (chunk << 40);
                    x ^= x >> 30; x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
                    x ^= x >> 27; x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
                    base[q.0 as usize] = x ^ (x >> 31);
                }
                for shot in 0..64 {
                    put_num(&mut base, &fc.sy, shot, 1 + ((shot * 29 + chunk as usize * 17) % 128));
                    put_num(&mut base, &sc.sz[..7], shot, (shot * 43 + chunk as usize * 19) & 127);
                }
                base[sc.sz[7].0 as usize] = 0xa5a5_3c3c_f0f0_9696 & !act;
                base[fc.ph.0 as usize] = (if ht { act } else { 0 }) | (0x8c3a_7e91_602d_b4f5 & !act);
                base[sc.bq.0 as usize] = 0x63a5_9bd7_4f12_e8c0u64.rotate_left((chunk * 9) as u32);
                base[sc.g.0 as usize] = act;
                base[fc.sx[VB + 1].0 as usize] = if form >= 6 { act & 0x1144_5511_4455_1144 } else { 0 };
                if form == 0 { base[fc.sx[0].0 as usize] = act & 0x1111_1111_1111_1111; }
                else if matches!(form, 3 | 4 | 5) { base[fc.sx[0].0 as usize] = 0x18c3_7a5e_d290_b641; }
                let mut ci = base.clone();
                let mut pi = base;
                ci[fc.sx[VB].0 as usize] = act;
                pi[fp.sx[3].0 as usize] = act;
                pi[fp.sx[1].0 as usize] = 0x9246_8ade_1357_bdf0;
                pi[fp.sx[4].0 as usize] = 0x7e1d_c59a_36b4_80f2;
                pi[fp.sx[6].0 as usize] = 0x5a0f_3c96_e172_b84d;
                let co = run(&control.ops, width, &|q| *q = ci.clone());
                let po = run(&candidate.ops, width, &|q| *q = pi.clone());
                assert_eq!(co.phase, po.phase, "{} chunk={chunk} phase", names[form]);
                assert_eq!(co.phase, 0, "{} chunk={chunk} residual phase", names[form]);
                for lane in 0..width {
                    let q = QubitId(lane as u64);
                    let got_c = co.q[lane]; let got_p = po.q[lane];
                    if q == fc.sx[3] {
                        assert_eq!(got_c, 0, "{} chunk={chunk} control pzero", names[form]);
                        assert_eq!(got_p, co.q[fc.sx[6].0 as usize], "{} chunk={chunk} ak", names[form]);
                    } else if q == fc.sx[6] {
                        assert_eq!(got_p, pi[lane], "{} chunk={chunk} withheld sx6", names[form]);
                    } else if q == fc.sx[1] || q == fc.sx[4] {
                        assert_eq!(got_c, 0, "{} chunk={chunk} control clean lane", names[form]);
                        assert_eq!(got_p, pi[lane], "{} chunk={chunk} withheld lane", names[form]);
                    } else {
                        assert_eq!(got_c, got_p, "{} chunk={chunk} lane={lane}", names[form]);
                    }
                }
            }
            eprintln!("G3P_D4 form={} chunks=4 phase=0", names[form]);
        }
        std::env::set_var("C59E_G3", "3");
    }
}
