//! O3's three-band crossing sessions on the K0 donor-Rust research vehicle.
//! The source contract is scratch/r8-o3.md; this module is below S1 assurance.
use super::*;

pub(super) fn t1(sy: usize) -> usize {
    match sy { 1..=120 => 5, 121..=123 => 4, 124..=127 => 2, 128 => 1,
               _ => panic!("sy outside O3 public support: {sy}") }
}
pub(super) fn t2(sy: usize) -> usize {
    match sy { 1..=118 => 13, 119..=120 => 11, 121 => 10,
               122..=123 => 8, 124..=128 => 5,
               _ => panic!("sy outside O3 public support: {sy}") }
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
    pub parked: &'a [Vec<G>],
    pub parked_ht: &'a [Vec<G>],
    pub vg: &'a [G],
    pub zshift: &'a [G],
    pub zoff_on: bool,
    pub kmax: usize,
    pub mt: usize,
}

impl Cross<'_> {
    fn act(&self) -> QubitId { self.sc.g }
    fn c0(&self) -> QubitId { self.sc.f }
    fn x128(&self) -> QubitId { self.sc.bq }
    fn pzero(&self) -> QubitId { self.sc.cmpc }
    fn ak(&self) -> QubitId { self.fd.sx[VB] }
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
    fn safe_chain(&self) -> [QubitId; 3] { [self.c0(), self.pzero(), self.fd.sx[4]] }
    fn plain_chain(&self) -> [QubitId; 3] { [self.c0(), self.pzero(), self.x128()] }

    fn sy_le(&self, b: &mut B, limit: usize, target: QubitId, safe: bool) {
        if limit == 128 { b.x(target); }
        else {
            let chain = if safe {
                if target == self.fd.sx[4] { [self.c0(), self.pzero(), self.fd.sx[5]] }
                else { self.safe_chain() }
            } else { self.plain_chain() };
            super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize,
                                               target, &chain, self.dirty());
            b.x(target);
        }
    }
    fn sy_le_alt(&self, b: &mut B, limit: usize, target: QubitId) {
        if limit == 128 { b.x(target); }
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
            let chain = if safe { self.safe_chain() } else { self.plain_chain() };
            super::super::frogdrop_col::ge_cd(b, &self.sc.sz[..5], j as isize,
                                               target, &chain, self.dirty());
        }
    }

    /// Prepare ak from restored sy and the frame code, clear the selector
    /// temps before `body`, then reverse the same prep after the body.
    fn with_tb_gate(&self, b: &mut B, j: usize, family: u8, body: impl FnOnce(&mut B)) {
        assert!(j <= 12 && family < 3);
        let x = &self.fd.sx;
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
        let exists = |b: &mut B| {
            if j == 0 { b.x(self.c()); }
            else { super::super::frogdrop_col::ge_cd(b, &self.sc.sz[..5], j as isize,
                self.c(), &[], self.dirty()); }
        };
        let prep = rec(b, |b| {
            exists(b);
            if let Some(limit) = t1_limit(j) {
                if limit == 128 { b.x(self.pzero()); }
                else {
                    super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize,
                        self.pzero(), &[], self.dirty());
                    b.x(self.pzero());
                }
                mc_xor(b, &[(self.act(), false), (self.c(), false), (self.pzero(), false)],
                       self.ak(), &[], self.dirty());
                if limit == 128 { b.x(self.pzero()); }
                else {
                    b.x(self.pzero());
                    super::super::frogdrop_col::ge_cd(b, &self.fd.sy, (limit + 1) as isize,
                        self.pzero(), &[], self.dirty());
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
                self.sy_le(b, limit, self.fd.sx[1], true);
                super::super::modp_frogdrop::add_const_exact(b, v, Some(self.fd.sx[1]), amount, self.dirty());
                self.sy_le(b, limit, self.fd.sx[1], true);
            }
        })
    }
    fn with_bottom_gate(&self, b: &mut B, kk: usize, body: impl FnOnce(&mut B)) {
        assert!(kk < 10);
        let v = &self.sc.sz[..VB];
        let t = self.fd.sx[1];
        let prep = rec(b, |b| {
            super::super::frogdrop_col::ge_cd(b, v, (40 - kk) as isize, t,
                                               &self.safe_chain(), self.dirty());
            b.x(t);
            mc_xor(b, &[(self.act(), false), (t, false)], self.ak(), &[], self.dirty());
            b.x(t);
            super::super::frogdrop_col::ge_cd(b, v, (40 - kk) as isize, t,
                                               &self.safe_chain(), self.dirty());
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
        b7b_move_q0(b, &self.fd.q, self.x128(), &self.fd.sy,
                    self.sylo(), self.syhi(), slot, self.act(),
                    &self.fd.sx[1..4], self.dirty());
    }
    fn cmp_y_at(&self, b: &mut B, tl: &[QubitId], masked: bool) {
        let s = self.source(tl.len());
        if masked {
            let pre = [self.fd.sx[1], self.fd.sx[2], self.fd.sx[3], self.fd.sx[4], self.pzero()];
            b7b_masked_cmp_y(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                             self.ak(), self.c(), self.c0(), self.fd.sx[5],
                             &pre, self.dirty(), true);
        } else {
            let rd = s.clone();
            let mut mid = |b: &mut B| {
                let lane = |v: usize| rd.get(v).copied();
                read_lane(b, &self.fd.sy, self.sylo(), self.syhi(), &lane, true,
                          &[(self.ak(), false)], self.c(), &[], &[], self.dirty());
            };
            let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| self.c());
            ripple(b, tl, &s, self.c0(), true, &mut mid, &mut gate);
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
        let pre = [self.fd.sx[1], self.fd.sx[2], self.fd.sx[3], self.fd.sx[4], self.pzero()];
        b7b_masked_add_y(b, tl, &s, &self.fd.sy, self.sylo(), self.syhi(),
                         self.c(), self.c0(), self.fd.sx[5], &pre, self.dirty(), false);
    }
    fn vbit_at(&self, b: &mut B, tl: &[QubitId]) {
        let s = self.source(tl.len());
        let pre = [self.fd.sx[1], self.fd.sx[2], self.fd.sx[3], self.fd.sx[4],
                   self.fd.sx[5], self.c0(), self.pzero()];
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
        let x = &self.fd.sx;
        if let Some(limit) = t1_limit(j - 1) { self.sy_le_alt(b, limit, x[2]); b.x(x[2]); }
        else { b.x(x[2]); }
        if let Some(limit) = t2_limit(j) { self.sy_le_alt(b, limit, x[3]); }
        mc_xor(b, &[(x[2], false), (x[3], false)], target, &[], self.dirty());
        if let Some(limit) = t2_limit(j) { self.sy_le_alt(b, limit, x[3]); }
        if let Some(limit) = t1_limit(j - 1) { b.x(x[2]); self.sy_le_alt(b, limit, x[2]); }
        else { b.x(x[2]); }
    }
    fn erase_mid(&self, b: &mut B, j: usize) {
        let sel = self.fd.sx[4];
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

    fn toggle_hr_act(&self, b: &mut B) {
        let mut lits = vec![(self.fd.ph, true)];
        if self.cp.sw { lits.push((self.sc.sw, true)); }
        mc_xor(b, &lits, self.act(), &[], self.dirty());
    }
    fn toggle_ht_act(&self, b: &mut B, flipped: bool) {
        if flipped { b.x(self.fd.ph); }
        if self.zoff_on && self.cp.dq { b.play(self.zshift, false); }
        let carry = if flipped { self.c0() } else { self.x128() };
        ht_act(b, self.fd, self.cp, self.sc, self.act(), &self.fd.sx[..1], carry, self.dirty());
        if self.zoff_on && self.cp.dq { b.play(self.zshift, true); }
        if flipped { b.x(self.fd.ph); }
    }
    fn play_hr(&self, b: &mut B, form: Option<usize>, inverse: bool) {
        self.toggle_hr_act(b);
        super::super::frogdrop_col::mark(b, 4000);
        b.play(form.map(|i| self.parked[i].as_slice()).unwrap_or(self.vform), inverse);
        self.toggle_hr_act(b);
    }
    fn play_ht(&self, b: &mut B, form: Option<usize>, inverse: bool) {
        b.cx(self.act(), self.fd.ph);
        self.toggle_ht_act(b, true);
        b.play(form.map(|i| self.parked_ht[i].as_slice()).unwrap_or(self.vform), inverse);
        self.toggle_ht_act(b, true);
        b.cx(self.act(), self.fd.ph);
    }

    fn search_frame(&self, b: &mut B, family: u8) {
        let (lo, hi) = if family == 0 { (0, 5) } else { (1, 13) };
        let frame = self.frame(b);
        b.play(&frame, false);
        for j in lo..hi {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, family, |b| {
                self.top_flag(b, j);
                self.vbit_at(b, &tl);
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
        b.play(&frame, true);
    }

    fn search_bottom(&self, b: &mut B) {
        b.play(self.vg, false);
        let vp = self.vprime(b);
        b.play(&vp, false);
        for kk in (0..10).rev() {
            let tl = self.natural_tl(kk);
            self.with_bottom_gate(b, kk, |b| self.vbit_at(b, &tl));
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
        assert_eq!(self.fd.ring.len(), 259);
        assert_eq!(self.kmax, 23);
        assert_eq!(self.parked.len(), 3);
        self.toggle_hr_act(b);

        // S1: clean top-down search in V, then extract the whole top band.
        self.play_hr(b, None, false);
        super::super::frogdrop_col::mark(b, 4001);
        self.search_frame(b, 0);
        super::super::frogdrop_col::mark(b, 4002);
        self.play_hr(b, Some(0), true);
        super::super::frogdrop_col::mark(b, 4003);
        let frame = self.frame(b);
        b.play(&frame, false);
        for j in 0..5 {
            self.with_top_slot_gate(b, j, |b| {
                self.park_lane(b, 0, j, 1, self.fd.sx[1 + j], self.ak());
            });
        }
        b.play(&frame, true);
        super::super::frogdrop_col::mark(b, 4004);

        // J1: the top band is in SX slots, leaving a clean Y source.
        self.tt_adjust(b, true);
        let frame = self.frame(b);
        b.play(&frame, false);
        for j in 0..5 {
            let tl = self.frame_tl(j);
            self.with_tb_exists(b, j, false, |b| {
                self.cmp_y_at(b, &tl, false);
                b.cx(self.c(), self.fd.sx[1 + j]);
                self.inplace_at(b, &tl);
            });
        }
        for j in (0..5).rev() {
            let tl = self.frame_tl(j);
            self.with_tb_exists(b, j, false, |b| {
                self.inplace_at(b, &tl);
                self.mul_back_at(b, &tl);
            });
        }
        b.play(&frame, true);
        self.tt_adjust(b, false);
        super::super::frogdrop_col::mark(b, 4005);

        // S2: middle band into Q; its index zero moves to sx0.
        self.play_hr(b, None, false);
        super::super::frogdrop_col::mark(b, 4006);
        self.search_frame(b, 1);
        super::super::frogdrop_col::mark(b, 4007);
        self.play_hr(b, Some(1), true);
        self.q0_move(b, self.fd.sx[0]);
        super::super::frogdrop_col::mark(b, 4008);

        // J2: high parked Q is dirty source. Erase the middle band before
        // the clean exact inverse restores the search starting value.
        self.tt_adjust(b, true);
        let frame = self.frame(b);
        b.play(&frame, false);
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
        b.play(&frame, true);
        self.tt_adjust(b, false);
        super::super::frogdrop_col::mark(b, 4009);

        // S3: bottom-aligned natural rounds. The bottom Q park persists
        // through the stage-4 masked division.
        self.play_hr(b, None, false);
        super::super::frogdrop_col::mark(b, 4010);
        self.search_bottom(b);
        super::super::frogdrop_col::mark(b, 4011);
        self.play_hr(b, Some(2), true);
        self.q0_move(b, self.fd.sx[0]);
        super::super::frogdrop_col::mark(b, 4012);
        self.toggle_hr_act(b);
    }

    fn gate_nat(&self, b: &mut B, kk: usize, on: bool) {
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
    }

    pub(super) fn hr_stage4(&self, b: &mut B) {
        self.tt_adjust(b, true);
        self.toggle_hr_act(b);
        // Phase 1: clear the in-place top/middle quotient while the bottom
        // band occupies Q above Y. These are no-erase masked divisions.
        let frame = self.frame(b);
        b.play(&frame, false);
        for j in 0..13 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 2, |b| {
                self.cmp_y_at(b, &tl, true);
                self.inplace_at(b, &tl);
            });
        }
        b.play(&frame, true);

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
        }
        b.play(&vp, true);
        b.play(self.vg, true);

        // The full quotient is now in the in-place lanes, Q and sx0 clean.
        // The exact inverse division shares each bit with the payload tick.
        let wtop = 259 - if self.cp.dl { self.cp.dlr.min(L0P + 1) } else { L0P + 1 };
        let pads = if self.cp.dl {
            vec![self.x128(), self.pzero(), self.fd.sx[1], self.fd.sx[6], self.sc.sw, self.fd.ph]
        } else { vec![self.x128(), self.pzero()] };
        let nopad = std::env::var("FD_DINV_NOPAD").map(|v| v == "1").unwrap_or(false);
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
                super::super::payload::trans_one(b, &t, &src[..sl], kk, false,
                    vec![(self.c(), false)], None, self.fd.sx[0], self.c0(), &[], &pl.dirty);
                super::super::frogdrop_col::mark(b, 1000 + kk);
            }
            if self.cp.dl { self.gate_nat(b, kk, true); }
            self.mul_back_at(b, &tl);
            self.gate_nat(b, kk, false);
        }
        self.toggle_hr_act(b);
        self.tt_adjust(b, false);
    }

    fn take_mid(&self, b: &mut B, j: usize) {
        let sel = self.fd.sx[4];
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
            b.play(&frame, false);
            for j in lo..hi {
                let tl = self.frame_tl(j);
                self.with_tb_gate(b, j, family, |b| {
                    self.top_flag(b, j);
                    self.vbit_at(b, &tl);
                    self.top_flag(b, j);
                });
            }
            b.play(&frame, true);
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
                self.with_bottom_gate(b, kk, |b| self.vbit_at(b, &tl));
            }
            b.play(&vp, true);
            b.play(self.vg, true);
        });
        b.play(&r, true);
    }

    /// Stage 6: bottom, middle, top HT parked plays and exact add-back
    /// replay. Stage 5's quotient is in the X in-place lanes on entry.
    pub(super) fn ht_stage6(&self, b: &mut B) {
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
        }
        b.play(&vp, true);
        b.play(self.vg, true);
        self.q0_move(b, self.fd.sx[0]);
        let frame = self.frame(b);
        b.play(&frame, false);
        for j in (0..13).rev() {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 2, |b| {
                self.inplace_at(b, &tl);
                self.masked_mul_back_at(b, &tl);
            });
        }
        b.play(&frame, true);
        self.q0_move(b, self.fd.sx[0]);

        // S1: parked bottom into V by controlled add-back, then erase the
        // in-place search with the now-clean source.
        self.play_ht(b, Some(2), false);
        b.cx(self.act(), self.fd.ph);
        self.q0_move(b, self.fd.ph);
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
        }
        b.play(&vp, true);
        b.play(self.vg, true);
        b.cx(self.act(), self.fd.ph);
        self.undo_bottom_search(b);
        self.play_ht(b, None, true);

        // S2 prep: divide top+middle into place, park middle, then fold
        // the top band with the middle Q park as dirty source.
        let frame = self.frame(b);
        b.play(&frame, false);
        for j in 0..13 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 2, |b| {
                self.cmp_y_at(b, &tl, false);
                self.inplace_at(b, &tl);
            });
        }
        for j in 1..13 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 1, |b| {
                self.inplace_at(b, &tl);
                self.park_lane(b, 1, j, 1, self.c(), self.ak());
            });
        }
        self.q0_move(b, self.fd.sx[0]);
        for j in (0..5).rev() {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 0, |b| {
                self.inplace_at(b, &tl);
                self.masked_mul_back_at(b, &tl);
            });
        }
        b.play(&frame, true);
        self.q0_move(b, self.fd.sx[0]);

        // S2 replay of the middle band.
        self.play_ht(b, Some(1), false);
        b.cx(self.act(), self.fd.ph);
        self.q0_move(b, self.fd.ph);
        let frame = self.frame(b);
        b.play(&frame, false);
        for j in 1..13 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 1, |b| {
                self.take_mid(b, j);
                self.masked_add_at(b, &tl);
                self.store_at(b, &tl);
            });
        }
        b.play(&frame, true);
        b.cx(self.act(), self.fd.ph);
        self.undo_frame_search(b, 1);
        self.play_ht(b, None, true);

        // S3 prep and top replay.
        let frame = self.frame(b);
        b.play(&frame, false);
        for j in 0..5 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 0, |b| {
                self.cmp_y_at(b, &tl, false);
                self.inplace_at(b, &tl);
            });
        }
        for j in 0..5 {
            let tl = self.frame_tl(j);
            self.with_tb_gate(b, j, 0, |b| {
                self.inplace_at(b, &tl);
                self.park_lane(b, 0, j, 1, self.c(), self.ak());
            });
        }
        b.play(&frame, true);
        self.play_ht(b, Some(0), false);
        b.cx(self.act(), self.fd.ph);
        self.q0_move(b, self.fd.ph);
        let frame = self.frame(b);
        b.play(&frame, false);
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
        }
        b.play(&frame, true);
        b.cx(self.act(), self.fd.ph);
        self.undo_frame_search(b, 0);
        self.play_ht(b, None, true);
        self.toggle_ht_act(b, false);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::super::tests_frogdrop::run;

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
        let sc = ColScr::carve(&pool, &sx, &dirty, 24, 23, 40);
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
        let flags = b.alloc_n(39);
        let cross = Cross { fd: &fd, cp: &cp, sc: &sc, pl: None,
            vform: &[], parked: &[], parked_ht: &[], vg: &[], zshift: &[],
            zoff_on: false, kmax: 23, mt: 129 };
        let pred = rec(&mut b, |b| {
            for family in 0..3u8 {
                for j in 0..13 {
                    let flag = flags[(family as usize) * 13 + j];
                    cross.with_tb_gate(b, j, family, |b| b.cx(cross.ak(), flag));
                }
            }
        });
        b.play(&pred, false); let forward = b.ops.len();
        b.play(&pred, true);
        let width = b.width() as usize;
        for chunk in pairs.chunks(64) {
            let mut input = vec![0u64; width];
            for (i, &q) in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate() {
                input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left((i * 7 % 64) as u32);
            }
            input[sc.bq.0 as usize] = 0x6868_3c3c_f0f0_9696;
            input[fd.sx[0].0 as usize] = 0x7135_1a2b_c4d5_e6f7;
            input[fd.sx[7].0 as usize] = 0x29c3_85f1_7a6b_402d;
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
            vform: &[], parked: &[], parked_ht: &[], vg: &[], zshift: &[],
            zoff_on: false, kmax: 23, mt: 129 };
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
}
