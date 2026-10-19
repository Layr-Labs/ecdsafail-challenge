//! O3's three-band crossing sessions on the K0 donor-Rust research vehicle.
//! The source contract is scratch/r8-o3.md; this module is below S1 assurance.
use super::*;

// Provisional O5 relabel primitive. A Gray-path transposition of two five-bit
// gap codes, selected only by restored sy[0..7) and clean inactive guards.
// Its physical all-wire test is below; no production path calls it yet.
#[cfg(test)]
fn b9b_relabel_gap(b:&mut B,sy:&[QubitId],gap:&[QubitId],size:u8,a:u8,z:u8,
    guards:&[QubitId],dirty:&[QubitId]){
    assert!(sy.len()>=7&&gap.len()>=5&&a<32&&z<32&&a!=z);
    let mut path=vec![a];let mut cur=a;
    for bit in 0..5 {if (a^z)>>bit&1!=0{cur^=1<<bit;path.push(cur);}}
    assert_eq!(cur,z);
    let step=|b:&mut B,u:u8,v:u8|{
        let bit=(u^v).trailing_zeros()as usize;
        assert_eq!((u^v).count_ones(),1);
        let mut ct:Vec<_>=(0..7).map(|i|(sy[i],size>>i&1==0)).collect();
        ct.extend(guards.iter().map(|&q|(q,true)));
        ct.extend((0..5).filter(|&i|i!=bit).map(|i|(gap[i],u>>i&1==0)));
        mc_xor(b,&ct,gap[bit],&[],dirty);
    };
    for p in path.windows(2){step(b,p[0],p[1]);}
    for i in(1..path.len()-1).rev(){step(b,path[i-1],path[i]);}
}

// Four-owner N258 layout after the Y-root gather. Positions above sy that
// are not owner preimages come first; occupied owner preimages come last.
fn b9b_skip_positions(sy: usize) -> Vec<usize> {
    assert!((1..=128).contains(&sy));
    let q125 = match sy % 4 { 0 => 125, 1 => 126, 2 => 123, _ => 124 };
    let q126 = if sy % 2 == 0 { 126 } else { 125 };
    let owners = [128, 127, q126, q125];
    let mut free: Vec<usize> = (sy..=128).filter(|p| !owners.contains(p)).collect();
    let mut parked_owners: Vec<usize> = owners.into_iter().filter(|&p| p >= sy).collect();
    parked_owners.sort_unstable();
    parked_owners.dedup();
    free.extend(parked_owners);
    assert_eq!(free.len(), 129 - sy);
    assert_eq!(free[0], sy);
    free
}

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
fn hr_t1(sy:usize)->usize {match sy {1..=121=>5,122..=123=>3,124..=125=>2,126..=128=>1,_=>panic!("bad sy")}}
fn hr_t2(sy:usize)->usize {match sy {1..=117=>13,118..=119=>12,120..=121=>10,122..=123=>7,124=>5,125=>4,126..=128=>2,_=>panic!("bad sy")}}
fn hr_t1_limit(j:usize)->Option<usize>{match j {0=>Some(128),1=>Some(125),2=>Some(123),3..=4=>Some(121),_=>None}}
fn hr_t2_limit(j:usize)->Option<usize>{match j {0..=1=>Some(128),2..=3=>Some(125),4=>Some(124),5..=6=>Some(123),7..=9=>Some(121),10..=11=>Some(119),12=>Some(117),_=>None}}
fn ht_t1min(sy:usize)->usize{match sy{1..=121=>5,122=>4,123=>3,124..=125=>2,126..=128=>1,_=>panic!("bad sy")}}
fn ht_t2(sy:usize)->usize{match sy{1..=118=>13,119=>12,120..=121=>10,122=>8,123=>7,124=>5,125=>4,126..=128=>2,_=>panic!("bad sy")}}
fn ht_t1_limit(j:usize)->Option<usize>{match j{0=>Some(128),1=>Some(125),2=>Some(123),3=>Some(122),4=>Some(121),_=>None}}
fn ht_t2_limit(j:usize)->Option<usize>{match j{0..=1=>Some(128),2..=3=>Some(125),4=>Some(124),5..=6=>Some(123),7=>Some(122),8..=9=>Some(121),10..=11=>Some(119),12=>Some(118),_=>None}}

#[derive(Clone,Copy)]
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
    pub ht_mode: bool,
    pub kmax: usize,
    pub mt: usize,
}

impl Cross<'_> {
    fn hr3(&self)->bool {self.fd.ring.len()==258 && self.parked.len()==3 && !self.ht_mode}
    fn ht3(&self)->bool {self.fd.ring.len()==258 && self.parked_ht.len()==3 && self.ht_mode}
    fn cut_t1(&self,sy:usize)->usize {if self.ht3(){ht_t1min(sy)}else if self.hr3(){hr_t1(sy)}else{t1(sy)}}
    fn cut_t2(&self,sy:usize)->usize {if self.ht3(){ht_t2(sy)}else if self.hr3(){hr_t2(sy)}else{t2(sy)}}
    fn cut_t1_limit(&self,j:usize)->Option<usize>{if self.ht3(){ht_t1_limit(j)}else if self.hr3(){hr_t1_limit(j)}else{t1_limit(j)}}
    fn cut_t2_limit(&self,j:usize)->Option<usize>{if self.ht3(){ht_t2_limit(j)}else if self.hr3(){hr_t2_limit(j)}else{t2_limit(j)}}
    fn ht_frame_extra(&self,b:&mut B,j:usize,family:u8){
        if !self.ht3(){return;}
        const CELLS:&[(usize,usize,u8,usize)]=&[
            (124,5,1,4),(124,5,2,4),(124,9,1,5),(124,9,2,5),
            (125,5,1,4),(125,5,2,4),(126,4,1,2),(126,4,2,2),
            (126,5,0,1),(126,5,1,1),(126,5,1,2),(126,5,2,2),
            (126,5,1,3),(126,5,2,3),
        ];
        for &(sy,g,f,jj) in CELLS{if j!=jj||family!=f{continue;}
            let mut ctl=vec![(self.act(),false)];
            ctl.extend((0..7).map(|i|(self.fd.sy[i],sy>>i&1==0)));
            ctl.extend((0..5).map(|i|(self.sc.sz[i],g>>i&1==0)));
            mc_xor(b,&ctl,self.ak(),&[],self.dirty());
        }
    }
    fn ht_bottom_extra(&self,b:&mut B,kk:usize){
        if !self.ht3(){return;}
        const CELLS:&[(usize,usize,usize)]=&[
            (124,39,1),(124,35,4),(125,38,1),(126,37,2),(126,36,2),(126,36,3),
        ];
        for &(sy,code,k) in CELLS{if kk!=k{continue;}
            let mut ctl=vec![(self.act(),false)];
            ctl.extend((0..7).map(|i|(self.fd.sy[i],sy>>i&1==0)));
            ctl.extend((0..6).map(|i|(self.sc.sz[i],code>>i&1==0)));
            mc_xor(b,&ctl,self.ak(),&[],self.dirty());
        }
    }
    fn q675_frame(&self,b:&mut B)->Vec<G>{rec(b,|b|{if self.zoff_on{b.play(self.zshift,false);}let frame=super::q675_frame_probe(b,&self.fd.ring,&self.sc.sz,&self.fd.sy,self.dirty());b.play(&frame,false);})}
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
        if self.fd.ring.len() == 258 {
            self.q675_frame(b)
        } else {
            b8b_tb_frame(b, &self.fd.ring, &self.sc.sz, &self.fd.sy, self.dirty())
        }
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
                if let Some(s) = self.cut_t1_limit(j) { self.sy_le(b, s, x[2], true); ctl.push((x[2], false)); }
            } else {
                if family == 1 {
                    if let Some(s) = self.cut_t1_limit(j) { self.sy_le(b, s, x[2], true); ctl.push((x[2], true)); }
                }
                if let Some(s) = self.cut_t2_limit(j) { self.sy_le(b, s, x[3], true); ctl.push((x[3], false)); }
            }
            if family == 0 && self.cut_t1_limit(j).is_none() { /* no top bit at this j */ }
            else if family != 0 && self.cut_t2_limit(j).is_none() { /* no bit */ }
            else { mc_xor(b, &ctl, self.ak(), &[], self.dirty()); }
            self.ht_frame_extra(b,j,family);
            if let Some(s) = self.cut_t2_limit(j) { if family != 0 { self.sy_le(b, s, x[3], true); } }
            if let Some(s) = self.cut_t1_limit(j) { if family != 2 { self.sy_le(b, s, x[2], true); } }
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
            if let Some(limit) = self.cut_t1_limit(j) {
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
            super::super::modp_frogdrop::add_const_exact(b, v, None, if self.hr3()||self.ht3(){2}else{5}, self.dirty());
            let adds:&[(usize,u64)]=if self.ht3(){&[(125,2),(124,1),(123,2),(122,1),(121,2),(119,2),(118,1)]}
                                   else if self.hr3(){&[(125,2),(124,1),(123,2),(121,3),(119,2),(117,1)]}
                                   else{&[(123,3),(121,2),(120,1),(118,2)]};
            for &(limit, amount) in adds {
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
            self.ht_bottom_extra(b,kk);
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
        let mut leaves: Vec<(usize, QubitId)> = (self.sylo()..=self.syhi())
            .filter_map(|sy| {
                let idx = match family { 0 | 2 => bit, 1 => bit.saturating_sub(self.cut_t1(sy)),
                                         _ => unreachable!() };
                let pos = if self.fd.ring.len() == 258 {
                    match b9b_skip_positions(sy).get(idx) { Some(&p) => p, None => return None }
                } else { sy + idx };
                if pos < self.fd.q.len() { Some((sy, self.fd.q[pos])) }
                else if pos == self.fd.q.len() { Some((sy, self.x128())) }
                else { None }
            }).collect();
        assert!(!leaves.is_empty());
        // The N258 skip map may send two sy values to the same physical Q
        // lane at a fixed bit index. swap_tree needs distinct leaves. Give
        // each repeated leaf an unused Q shadow and conditionally exchange
        // it with the desired lane around the tree. All exchanges undo.
        let mut used: std::collections::BTreeSet<QubitId> = std::collections::BTreeSet::new();
        let mut collisions = vec![];
        let spare: Vec<QubitId> = self.fd.q.iter().copied().chain(std::iter::once(self.x128()))
            .filter(|q| !leaves.iter().any(|&(_, target)| target == *q)).collect();
        for (sy, target) in &mut leaves {
            if !used.insert(*target) {
                let shadow = spare[collisions.len()];
                assert!(used.insert(shadow));
                collisions.push((*sy, *target, shadow));
                *target = shadow;
            }
        }
        let shadow_swap = |b: &mut B, sy: usize, target: QubitId, shadow: QubitId| {
            let ctl: Vec<_> = (0..self.fd.sy.len())
                .map(|i| (self.fd.sy[i], sy >> i & 1 == 0)).collect();
            super::super::mid2::mc_swap(b, &ctl, target, shadow, &[], self.dirty());
        };
        for &(sy, target, shadow) in &collisions { shadow_swap(b, sy, target, shadow); }
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
        for &(sy, target, shadow) in collisions.iter().rev() { shadow_swap(b, sy, target, shadow); }
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
        if self.ht3(){match j {
            1 => { self.sy_le(b, 128, target, true); self.sy_le(b, 125, target, true); }
            2 => { self.sy_le(b, 125, target, true); self.sy_le(b, 123, target, true); }
            3 => { self.sy_le(b, 123, target, true); self.sy_le(b, 122, target, true); }
            4 => { self.sy_le(b, 122, target, true); self.sy_le(b, 121, target, true); }
            5 => self.sy_le(b, 121, target, true),
            _ => {}
        }}else if self.hr3(){match j {
            1 => { self.sy_le(b, 128, target, true); self.sy_le(b, 125, target, true); }
            2 => { self.sy_le(b, 125, target, true); self.sy_le(b, 123, target, true); }
            3 => { self.sy_le(b, 123, target, true); self.sy_le(b, 121, target, true); }
            5 => self.sy_le(b, 121, target, true),
            _ => {}
        }}else{match j {
            1 => { self.sy_le(b, 128, target, true); self.sy_le(b, 127, target, true); }
            2 => { self.sy_le(b, 127, target, true); self.sy_le(b, 123, target, true); }
            4 => { self.sy_le(b, 123, target, true); self.sy_le(b, 120, target, true); }
            5 => self.sy_le(b, 120, target, true),
            _ => {}
        }}
    }
    fn sy_mid_high(&self, b: &mut B, j: usize, target: QubitId) {
        if j <= 1 || j >= 13 { return; }
        let x = &self.fd.sx;
        if let Some(limit) = self.cut_t1_limit(j - 1) { self.sy_le_alt(b, limit, x[2]); b.x(x[2]); }
        else { b.x(x[2]); }
        if let Some(limit) = self.cut_t2_limit(j) { self.sy_le_alt(b, limit, x[3]); }
        mc_xor(b, &[(x[2], false), (x[3], false)], target, &[], self.dirty());
        if let Some(limit) = self.cut_t2_limit(j) { self.sy_le_alt(b, limit, x[3]); }
        if let Some(limit) = self.cut_t1_limit(j - 1) { b.x(x[2]); self.sy_le_alt(b, limit, x[2]); }
        else { b.x(x[2]); }
    }
    fn erase_mid(&self, b: &mut B, j: usize) {
        let sel = self.fd.sx[4];
        if if self.hr3(){matches!(j,1|2|3|5)}else{matches!(j,1|2|4|5)} {
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
        if self.fd.ring.len()==258 && self.parked.len()==5 {
            self.all_bands_probe(b,false,false);return;
        }
        assert!(matches!(self.fd.ring.len(),258|259));
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
        if self.fd.ring.len()==258 && self.parked.len()==5 {self.tt_adjust(b,true);self.toggle_hr_act(b);self.q675_divide_natural(b);self.q675_multiply_natural(b,self.pl.is_some());self.toggle_hr_act(b);self.tt_adjust(b,false);return;}
        assert_eq!(self.parked.len(),3);
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
        if if self.ht3(){matches!(j,1|2|3|4|5)}else{matches!(j,1|2|4|5)} {
            self.sy_t1_eq(b, j, sel);
            super::super::mid2::mc_swap(b, &[(self.ak(), false), (sel, false)],
                self.fd.ph, self.c(), &[], self.dirty());
            self.sy_t1_eq(b, j, sel);
        }
        if j >= 2 {
            if self.ht3(){self.sy_ht_mid_park(b,j,sel);}else{self.sy_mid_high(b, j, sel);}
            self.park_lane(b, 1, j, 3, self.c(), sel);
            if self.ht3(){self.sy_ht_mid_park(b,j,sel);}else{self.sy_mid_high(b, j, sel);}
        }
    }
    /// HT's middle index uses T1min; ak already includes the upper T2 bound.
    fn sy_ht_mid_park(&self,b:&mut B,j:usize,target:QubitId){
        assert!(self.ht3() && (2..13).contains(&j));
        match j {
            2 => { self.sy_le_alt(b,125,target); b.x(target); }
            3 => { self.sy_le_alt(b,123,target); b.x(target); }
            4 => { self.sy_le_alt(b,122,target); b.x(target); }
            5 => { self.sy_le_alt(b,121,target); b.x(target); }
            _ => b.x(target),
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
        let c=Cross{ht_mode:true,..*self};
        c.ht_stage6_inner(b);
    }
    fn ht_stage6_inner(&self,b:&mut B){
        if self.fd.ring.len()==258 && self.parked_ht.len()==5 {
            #[cfg(test)] let start=b.tof;
            self.toggle_ht_act(b,false);self.q675_multiply_natural(b,false);self.toggle_ht_act(b,false);
            #[cfg(test)] let natural=b.tof-start;
            let r=rec(b,|b|self.all_bands_probe(b,true,false));b.play(&r,true);
            #[cfg(test)] if std::env::var_os("B9B_COST").is_some() && matches!(self.cp.col,37|100) {
                eprintln!("B9B_COST col={} phase=ht_stage6_natural T={natural}",self.cp.col);
                eprintln!("B9B_COST col={} phase=ht_stage6_inverse_probe T={}",self.cp.col,b.tof-start-natural);
            }
            return;
        }
        assert_eq!(self.parked_ht.len(),3);
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
            zoff_on: false, ht_mode:false, kmax: 23, mt: 129 };
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
            zoff_on: false, ht_mode:false, kmax: 23, mt: 129 };
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

    #[test]
    fn b9b_hr3_thresholds_vprime_all_wire(){
        let pairs:Vec<_>=(1..=128).flat_map(|sy|(0..=25).filter(move |&g|{
            let sz=257-sy-g;sz>=sy+1&&sz<=255
        }).map(move |g|(sy,g))).collect();
        let(mut b,mut fd,mut cp,sc,dirty)=rig();fd.ring.pop();cp.n=258;cp.h=1;
        let flags=b.alloc_n(39);let parked=vec![vec![];3];
        let cross=Cross{fd:&fd,cp:&cp,sc:&sc,pl:None,vform:&[],parked:&parked,parked_ht:&[],vg:&[],zshift:&[],zoff_on:false,ht_mode:false,kmax:23,mt:129};
        let pred=rec(&mut b,|b|for family in 0..3u8{for j in 0..13{
            let flag=flags[family as usize*13+j];cross.with_tb_gate(b,j,family,|b|b.cx(cross.ak(),flag));
        }});
        b.play(&pred,false);let forward=b.ops.len();b.play(&pred,true);let width=b.width()as usize;
        for chunk in pairs.chunks(64){
            let mut input=vec![0u64;width];
            for(i,&q)in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate(){input[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left((i*7%64)as u32);}
            input[sc.bq.0 as usize]=0x68683c3cf0f09696;input[fd.sx[0].0 as usize]=0x71351a2bc4d5e6f7;
            for(shot,&(sy,g))in chunk.iter().enumerate(){put_num(&mut input,&fd.sy,shot,sy);
                let code=if g<=22{g}else{22+32*(g-22)};put_num(&mut input,&sc.sz,shot,code);input[sc.g.0 as usize]|=1<<shot;}
            let mut want=input.clone();
            for(shot,&(sy,g))in chunk.iter().enumerate(){let tb=g.min(22);
                for family in 0..3{for j in 0..13{
                    let yes=j<=tb&&match family{0=>j<hr_t1(sy),1=>hr_t1(sy)<=j&&j<hr_t2(sy),_=>j<hr_t2(sy)};
                    if yes{want[flags[family*13+j].0 as usize]|=1<<shot;}
                }}
            }
            let out=run(&b.ops[..forward],width,&|q|*q=input.clone());assert_eq!(out.q,want,"pred {:?}",chunk.first());assert_eq!(out.phase,0);
            let back=run(&b.ops,width,&|q|*q=input.clone());assert_eq!(back.q,input);assert_eq!(back.phase,0);
        }
        let(mut b,mut fd,mut cp,sc,dirty)=rig();fd.ring.pop();cp.n=258;cp.h=1;
        let flags=b.alloc_n(10);let parked=vec![vec![];3];
        let cross=Cross{fd:&fd,cp:&cp,sc:&sc,pl:None,vform:&[],parked:&parked,parked_ht:&[],vg:&[],zshift:&[],zoff_on:false,ht_mode:false,kmax:23,mt:129};
        let bottom=rec(&mut b,|b|{let vp=cross.vprime(b);b.play(&vp,false);
            for kk in 0..10{cross.with_bottom_gate(b,kk,|b|b.cx(cross.ak(),flags[kk]));}b.play(&vp,true);});
        b.play(&bottom,false);let forward=b.ops.len();b.play(&bottom,true);let width=b.width()as usize;
        for chunk in pairs.chunks(64){
            let mut input=vec![0u64;width];
            for(i,&q)in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate(){input[q.0 as usize]=0x243f6a8885a308d3u64.rotate_left((i*11%64)as u32);}
            input[sc.bq.0 as usize]=0x69e231a552cb467d;input[fd.sx[0].0 as usize]=0xc3682a7459fb10ed;
            for(shot,&(sy,g))in chunk.iter().enumerate(){put_num(&mut input,&fd.sy,shot,sy);
                put_num(&mut input,&sc.sz[..6],shot,(39+64-g)%64);input[sc.g.0 as usize]|=1<<shot;}
            let mut want=input.clone();
            for(shot,&(sy,g))in chunk.iter().enumerate(){let vp=(39+64-g+hr_t2(sy))%64;
                for kk in 0..10{if vp<=39-kk{want[flags[kk].0 as usize]|=1<<shot;}}
            }
            let out=run(&b.ops[..forward],width,&|q|*q=input.clone());assert_eq!(out.q,want,"bottom {:?}",chunk.first());assert_eq!(out.phase,0);
            let back=run(&b.ops,width,&|q|*q=input.clone());assert_eq!(back.q,input);assert_eq!(back.phase,0);
        }
        eprintln!("B9B_HR3_PREDICATES_PASS pairs={} all_wire=true inverse=true phase=0",pairs.len());
    }

    #[test]
    fn b9b_ht3_thresholds_vprime_all_wire(){
        let cases:Vec<(usize,usize,usize,usize,usize)>=include_str!("../b9b_ht3_pred_cases.tsv").lines().map(|line|{
            let v:Vec<_>=line.split_whitespace().map(|x|x.parse::<usize>().unwrap()).collect();
            (v[0],v[1],v[2],v[3],v[4])
        }).collect();
        assert_eq!(cases.len(),3172);
        let(mut b,mut fd,mut cp,sc,dirty)=rig();fd.ring.pop();cp.n=258;cp.h=1;
        let flags=b.alloc_n(39);let parked=vec![vec![];3];
        let cross=Cross{fd:&fd,cp:&cp,sc:&sc,pl:None,vform:&[],parked:&[],parked_ht:&parked,vg:&[],zshift:&[],zoff_on:false,ht_mode:true,kmax:23,mt:129};
        let pred=rec(&mut b,|b|for family in 0..3u8{for j in 0..13{
            let flag=flags[family as usize*13+j];cross.with_tb_gate(b,j,family,|b|b.cx(cross.ak(),flag));
        }});
        b.play(&pred,false);let forward=b.ops.len();b.play(&pred,true);let width=b.width()as usize;
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for(i,&q)in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate(){input[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left((i*7%64)as u32);}
            input[sc.bq.0 as usize]=0x68683c3cf0f09696;input[fd.sx[0].0 as usize]=0x71351a2bc4d5e6f7;
            for(shot,&(sy,g,_,_,_))in chunk.iter().enumerate(){put_num(&mut input,&fd.sy,shot,sy);
                let code=if g<=22{g}else{22+32*(g-22)};put_num(&mut input,&sc.sz,shot,code);input[sc.g.0 as usize]|=1<<shot;}
            let mut want=input.clone();
            for(shot,&(_,g,top,mid,_))in chunk.iter().enumerate(){let tb=g.min(22);
                for family in 0..3{for j in 0..13{
                    let yes=j<=tb&&match family{0=>j<top,1=>top<=j&&j<top+mid,_=>j<top+mid};
                    if yes{want[flags[family*13+j].0 as usize]|=1<<shot;}
                }}
            }
            let out=run(&b.ops[..forward],width,&|q|*q=input.clone());assert_eq!(out.q,want,"HT pred {:?}",chunk.first());assert_eq!(out.phase,0);
            let back=run(&b.ops,width,&|q|*q=input.clone());assert_eq!(back.q,input);assert_eq!(back.phase,0);
        }
        let(mut b,mut fd,mut cp,sc,dirty)=rig();fd.ring.pop();cp.n=258;cp.h=1;
        let flags=b.alloc_n(10);let parked=vec![vec![];3];
        let cross=Cross{fd:&fd,cp:&cp,sc:&sc,pl:None,vform:&[],parked:&[],parked_ht:&parked,vg:&[],zshift:&[],zoff_on:false,ht_mode:true,kmax:23,mt:129};
        let bottom=rec(&mut b,|b|{let vp=cross.vprime(b);b.play(&vp,false);
            for kk in 0..10{cross.with_bottom_gate(b,kk,|b|b.cx(cross.ak(),flags[kk]));}b.play(&vp,true);});
        b.play(&bottom,false);let forward=b.ops.len();b.play(&bottom,true);let width=b.width()as usize;
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for(i,&q)in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate(){input[q.0 as usize]=0x243f6a8885a308d3u64.rotate_left((i*11%64)as u32);}
            input[sc.bq.0 as usize]=0x69e231a552cb467d;input[fd.sx[0].0 as usize]=0xc3682a7459fb10ed;
            for(shot,&(sy,g,_,_,_))in chunk.iter().enumerate(){put_num(&mut input,&fd.sy,shot,sy);
                put_num(&mut input,&sc.sz[..6],shot,(39+64-g)%64);input[sc.g.0 as usize]|=1<<shot;}
            let mut want=input.clone();
            for(shot,&(_,_,_,_,bot))in chunk.iter().enumerate(){for kk in 0..10{if kk<bot{want[flags[kk].0 as usize]|=1<<shot;}}}
            let out=run(&b.ops[..forward],width,&|q|*q=input.clone());assert_eq!(out.q,want,"HT bottom {:?}",chunk.first());assert_eq!(out.phase,0);
            let back=run(&b.ops,width,&|q|*q=input.clone());assert_eq!(back.q,input);assert_eq!(back.phase,0);
        }
        eprintln!("B9B_HT3_PREDICATES_PASS pairs={} all_wire=true inverse=true phase=0",cases.len());
    }

    #[test]
    fn b9b_ht3_take_mid_selectors_all_wire(){
        let(mut b,mut fd,mut cp,sc,dirty)=rig();fd.ring.pop();cp.n=258;cp.h=1;
        let eq=b.alloc_n(5);let high=b.alloc_n(11);let parked=vec![vec![];3];
        let cross=Cross{fd:&fd,cp:&cp,sc:&sc,pl:None,vform:&[],parked:&[],parked_ht:&parked,vg:&[],zshift:&[],zoff_on:false,ht_mode:true,kmax:23,mt:129};
        let pred=rec(&mut b,|b|{
            for j in 1..=5{cross.sy_t1_eq(b,j,cross.fd.sx[4]);b.cx(cross.fd.sx[4],eq[j-1]);cross.sy_t1_eq(b,j,cross.fd.sx[4]);}
            for j in 2..=12{cross.sy_ht_mid_park(b,j,cross.fd.sx[4]);b.cx(cross.fd.sx[4],high[j-2]);cross.sy_ht_mid_park(b,j,cross.fd.sx[4]);}
        });
        b.play(&pred,false);let forward=b.ops.len();b.play(&pred,true);let width=b.width()as usize;
        for base in [1usize,65]{
            let mut input=vec![0u64;width];
            for(i,&q)in fd.ring.iter().chain(fd.q.iter()).chain(dirty.iter()).enumerate(){input[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left((i*11%64)as u32);}
            for lane in 0..64{put_num(&mut input,&fd.sy,lane,base+lane);}
            let mut want=input.clone();
            for lane in 0..64{let t=ht_t1min(base+lane);
                want[eq[t-1].0 as usize]|=1u64<<lane;
                for j in 2..=12{if t<=j-1{want[high[j-2].0 as usize]|=1u64<<lane;}}
            }
            let out=run(&b.ops[..forward],width,&|q|*q=input.clone());assert_eq!(out.q,want);assert_eq!(out.phase,0);
            let back=run(&b.ops,width,&|q|*q=input.clone());assert_eq!(back.q,input);assert_eq!(back.phase,0);
        }
        eprintln!("B9B_HT_TAKE_MID_SELECTOR_PASS sy=1..128 j=1..12 inverse=true phase=0");
    }
}

// N258 generic five-band source, shared with local tests.
impl Cross<'_> {
    // Clean Q source, ordinary ring-top X -> remainder plus in-place quotient.
    fn q675_divide_natural(&self,b:&mut B) {
        assert_eq!(self.fd.ring.len(),258);
        for kk in(0..self.kmax).rev(){let tl=self.natural_tl(kk);
            self.gate_nat(b,kk,true);self.cmp_y_at(b,&tl,false);self.inplace_at(b,&tl);self.gate_nat(b,kk,false);
        }
    }
    // Exact inverse at the same interface. The optional HR payload consumes
    // each reconstructed quotient bit before its arithmetic erasure.
    fn q675_multiply_natural(&self,b:&mut B,hr_payload:bool) {
        assert_eq!(self.fd.ring.len(),258);
        let wtop=259-if self.cp.dl{self.cp.dlr.min(L0P+1)}else{L0P+1};
        let pads=if self.cp.dl{vec![self.x128(),self.pzero(),self.fd.sx[1],self.fd.sx[6],self.sc.sw,self.fd.ph]}else{vec![self.x128(),self.pzero()]};
        let src=super::super::payload::pad(&self.fd.q,&pads,wtop.min(self.fd.q.len()+pads.len()));
        for kk in 0..self.kmax {let tl=self.natural_tl(kk);self.gate_nat(b,kk,true);self.inplace_at(b,&tl);
            if hr_payload {let pl=self.pl.expect("explicit payload interface");
                // The delayed source borrows ak among its zero pads. Return
                // the gate before reading these pads, then recompute it.
                if self.cp.dl{self.gate_nat(b,kk,false);}
                let t:Vec<_>=(kk..wtop).map(|i|super::super::payload::wl(&pl.p,i)).collect();
                super::super::payload::trans_one(b,&t,&src[..(wtop-kk).min(src.len())],kk,false,vec![(self.c(),false)],None,self.fd.sx[0],self.c0(),&[],&pl.dirty);
                if self.cp.dl{self.gate_nat(b,kk,true);}
            }
            self.mul_back_at(b,&tl);self.gate_nat(b,kk,false);
        }
    }
}

use super::super::q675_support::CUTS;
    fn prefixes(values:&[bool;256])->Vec<(usize,usize)>{
        fn go(v:&[bool;256],lo:usize,n:usize,o:&mut Vec<(usize,usize)>){
            if !v[lo..lo+n].iter().any(|x|*x){return;}
            if v[lo..lo+n].iter().all(|x|*x){o.push((255^(n-1),lo));return;}
            go(v,lo,n/2,o);go(v,lo+n/2,n/2,o);
        }let mut o=vec![];go(values,0,256,&mut o);o
    }
    impl Cross<'_>{
        fn size_select(&self,fam:usize,j:usize,slot:Option<usize>)->Vec<(usize,usize)>{
            let mut vals=[false;256];for sy in self.sylo()..=self.syhi(){
                let a=CUTS[sy-1][fam];let z=CUTS[sy-1][fam+1];
                vals[sy]=if let Some(i)=slot{j>=a&&j<z&&j-a==i}else{j<z};
            }prefixes(&vals)
        }
        fn with_prefix_gate(&self,b:&mut B,fam:usize,j:usize,body:impl FnOnce(&mut B)){
            let ps=self.size_select(fam,j,None);if ps.is_empty(){return;}
            let r=rec(b,|b|{
                super::super::frogdrop_col::ge_cd(b,&self.sc.sz[..5],j as isize,self.c(),&[],self.dirty());
                for &(mask,v)in &ps{let mut ct=vec![(self.act(),false),(self.c(),false)];
                    ct.extend((0..8).filter(|i|mask>>i&1!=0).map(|i|(self.fd.sy[i],v>>i&1==0)));
                    mc_xor(b,&ct,self.ak(),&[],self.dirty());
                }
                super::super::frogdrop_col::ge_cd(b,&self.sc.sz[..5],j as isize,self.c(),&[],self.dirty());
            });b.play(&r,false);body(b);b.play(&r,true);
        }
        fn q675_clean_prefix_join(&self,b:&mut B,fam:usize){
            assert!(fam<5);assert_eq!(self.fd.ring.len(),258);
            let frame=self.q675_frame(b);
            b.play(&frame,false);
            for j in 0..23{let tl=self.frame_tl(j);self.with_prefix_gate(b,fam,j,|b|{
                self.cmp_y_at(b,&tl,false);
                for i in 0..5{for(mask,v)in self.size_select(fam,j,Some(i)){
                    let mut ct=vec![(self.c(),false),(self.ak(),false)];ct.extend((0..8).filter(|k|mask>>k&1!=0).map(|k|(self.fd.sy[k],v>>k&1==0)));
                    mc_xor(b,&ct,self.fd.sx[1+i],&[],self.dirty());
                }}self.inplace_at(b,&tl);
            });}
            for j in(0..23).rev(){let tl=self.frame_tl(j);self.with_prefix_gate(b,fam,j,|b|{self.inplace_at(b,&tl);self.mul_back_at(b,&tl);});}
            b.play(&frame,true);
        }
    }

    impl Cross<'_>{
        fn with_band_gate(&self,b:&mut B,fam:usize,j:usize,body:impl FnOnce(&mut B)){
            let mut ps=vec![];for i in 0..5{ps.extend(self.size_select(fam,j,Some(i)));}if ps.is_empty(){return;}
            let r=rec(b,|b|{
                super::super::frogdrop_col::ge_cd(b,&self.sc.sz[..5],j as isize,self.c(),&[],self.dirty());
                for &(mask,v)in &ps{let mut ct=vec![(self.act(),false),(self.c(),false)];
                    ct.extend((0..8).filter(|i|mask>>i&1!=0).map(|i|(self.fd.sy[i],v>>i&1==0)));
                    mc_xor(b,&ct,self.ak(),&[],self.dirty());
                }
                super::super::frogdrop_col::ge_cd(b,&self.sc.sz[..5],j as isize,self.c(),&[],self.dirty());
            });b.play(&r,false);body(b);b.play(&r,true);
        }
        fn park_flight(&self,b:&mut B,fam:usize,j:usize){
            assert_eq!(self.ak(),self.fd.sx[6]);assert_eq!(self.c(),self.fd.sx[7]);assert_eq!(self.x128(),self.sc.bq);
            #[cfg(test)] let before=b.tof;
            super::super::q675_lookup::flight_selected(b,self.fd,self.sc,fam,j,self.sylo(),self.syhi());
            #[cfg(test)] if std::env::var_os("B9B_COST").is_some() && matches!(self.cp.col,37|100) {
                eprintln!("B9B_COST col={} family={fam} phase=flight bit={j} T={}",self.cp.col,b.tof-before);
            }
        }
        fn search_band(&self,b:&mut B,fam:usize){
            let frame=self.q675_frame(b);
            b.play(&frame,false);
            for j in 0..23{let tl=self.frame_tl(j);self.with_band_gate(b,fam,j,|b|{self.top_flag(b,j);self.vbit_at(b,&tl);self.top_flag(b,j);});}
            for j in 0..23{let tl=self.frame_tl(j);self.with_band_gate(b,fam,j,|b|{self.top_flag(b,j);self.extract_at(b,&tl);self.park_flight(b,fam,j);self.top_flag(b,j);});}
            b.play(&frame,true);
        }
        fn all_bands_probe(&self,b:&mut B,ht:bool,omit_final_join:bool){
            assert_eq!(if ht{self.parked_ht.len()}else{self.parked.len()},5);
            if ht{self.toggle_ht_act(b,false);}else{self.toggle_hr_act(b);}
            for fam in 0..5{
                #[cfg(test)] let start=b.tof;
                if ht{self.play_ht(b,None,false);}else{self.play_hr(b,None,false);}
                #[cfg(test)] if std::env::var_os("B9B_COST").is_some() && matches!(self.cp.col,37|100) {eprintln!("B9B_COST col={} ht={ht} family={fam} phase=v_enter T={}",self.cp.col,b.tof-start);}
                #[cfg(test)] let start=b.tof;
                self.search_band(b,fam);
                #[cfg(test)] if std::env::var_os("B9B_COST").is_some() && matches!(self.cp.col,37|100) {eprintln!("B9B_COST col={} ht={ht} family={fam} phase=search_flight T={}",self.cp.col,b.tof-start);}
                #[cfg(test)] let start=b.tof;
                if ht{self.play_ht(b,Some(fam),true);}else{self.play_hr(b,Some(fam),true);}
                #[cfg(test)] if std::env::var_os("B9B_COST").is_some() && matches!(self.cp.col,37|100) {eprintln!("B9B_COST col={} ht={ht} family={fam} phase=v_leave T={}",self.cp.col,b.tof-start);}
                #[cfg(test)] let start=b.tof;
                super::super::q675_support::park(b,self.fd,self.sc,fam);
                #[cfg(test)] if std::env::var_os("B9B_COST").is_some() && matches!(self.cp.col,37|100) {eprintln!("B9B_COST col={} ht={ht} family={fam} phase=park T={}",self.cp.col,b.tof-start);}
                #[cfg(test)] let start=b.tof;
                if !(omit_final_join&&fam==4){self.tt_adjust(b,true);self.q675_clean_prefix_join(b,fam);self.tt_adjust(b,false);}
                #[cfg(test)] if std::env::var_os("B9B_COST").is_some() && matches!(self.cp.col,37|100) {eprintln!("B9B_COST col={} ht={ht} family={fam} phase=join T={}",self.cp.col,b.tof-start);}
            }
            if ht{self.toggle_ht_act(b,false);}else{self.toggle_hr_act(b);}
        }
    }

#[cfg(test)]
mod q675_join_probe {
    use super::*;
    use alloy_primitives::U256;
    use super::super::super::{q675_band_handoff_tests::CUTS,tests_frogdrop::run};
    fn put(q:&mut[u64],bits:&[QubitId],lane:usize,v:U256){for(i,&b)in bits.iter().enumerate(){if v.bit(i){q[b.0 as usize]|=1<<lane;}}}
    #[test]
    fn q675_generic_clean_join_value_phase(){
        super::super::super::bake_knobs();let mut count=0;
        for fam in 0..5{
            let(mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
            let(mut cps,_,_)=super::super::super::pointadd_frogdrop::col_pars(&super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP));
            let cp=&mut cps[36];cp.n=258;cp.h=1;cp.sy=(1,128);cp.sz=(1,255);cp.tt=false;
            let c=Cross{fd:&fd,cp,sc:&sc,pl:None,vform:&[],parked:&[],parked_ht:&[],vg:&[],zshift:&[],zoff_on:false,ht_mode:false,kmax:23,mt:129};
            c.q675_clean_prefix_join(&mut b,fam);let width=b.width()as usize;
            assert!(b.ops.iter().all(|o|matches!(o.kind,crate::circuit::OperationType::X|crate::circuit::OperationType::CX|crate::circuit::OperationType::CCX|crate::circuit::OperationType::Swap)));
            let mut cases=vec![];
            for sy in 1usize..=128{for gap in 0usize..=25{if 257-sy-gap>255{continue;}let tb=gap.min(22);let maxq=(1usize<<(tb+1))-1;
                for q in[0,1,maxq/2,maxq]{for rem in[false,true]{cases.push((sy,gap,q,rem));}}
            }}
            for batch in cases.chunks(64){for active in[u64::MAX,0,0x5555555555555555]{
                let mut input=vec![0u64;width];input[sc.g.0 as usize]=active;
                for(i,&q)in dirty.iter().enumerate(){input[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left(i as u32);}
                let mut expected=input.clone();
                for(lane,&(sy,gap,q,rem))in batch.iter().enumerate(){
                    let y=(U256::from(1u64)<<(sy-1))|U256::from(1u64);let r=if rem{y-U256::from(1)}else{U256::ZERO};let x=y*U256::from(q)+r;
                    put(&mut input,&fd.q,lane,y);put(&mut input,&fd.sy,lane,U256::from(sy));put(&mut input,&sc.sz,lane,U256::from(257-sy-gap));
                    let top:Vec<_>=fd.ring.iter().rev().copied().collect();put(&mut input,&top,lane,x);
                    let a=CUTS[sy-1][fam];let end=CUTS[sy-1][fam+1];for j in a..end{if j<=gap.min(22)&&q>>(gap.min(22)-j)&1!=0{input[fd.sx[1+j-a].0 as usize]|=1<<lane;}}
                }
                expected.clone_from(&input);for q in &fd.sx[1..6]{expected[q.0 as usize]&=!active;}
                let out=run(&b.ops,width,&|x|*x=input.clone());
                if out.q!=expected||out.phase!=0{let differences:Vec<_>=out.q.iter().zip(&expected).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,a^b)).collect();panic!("join mismatch fam={fam} batch={batch:?} active={active:x} diff={differences:?} phase={:x}",out.phase);}
                let mut wrong_input=input.clone();wrong_input[fd.sx[1].0 as usize]^=u64::MAX;
                let mut wrong_want=expected.clone();wrong_want[fd.sx[1].0 as usize]^=u64::MAX;
                let wrong=run(&b.ops,width,&|x|*x=wrong_input.clone());assert_eq!(wrong.q,wrong_want);assert_eq!(wrong.phase,0);
                count+=batch.len();
            }}
            eprintln!("Q675_JOIN family={fam} ops={} T={} Q={width}",b.ops.len(),b.tof);
        }eprintln!("Q675_JOIN_PASS lanes={count} local_full_state=true production=false");
    }    #[test]
    fn q675_actual_hr_five_band_composition(){
        super::super::super::bake_knobs();let(mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
        let(mut cps,_,_)=super::super::super::pointadd_frogdrop::col_pars(&super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP));
        // Column 34 remains on the five-form noncrossing path after O5's
        // crossing columns switch to three forms. Keep this regression on
        // the actual five-form path rather than assuming column 36 is five.
        let cp=&mut cps[34];cp.n=258;cp.h=1;let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
        super::super::super::q675_layout_tests::vform_mode(true);
        super::super::middle(&mut b,&fd,cp,&sc,None,&[],&mut |_|panic!("entered production"));
        super::super::super::q675_layout_tests::vform_mode(false);
        let(v,parked)=super::super::super::q675_vform_tests::take();
        let c=Cross{fd:&fd,cp,sc:&sc,pl:None,vform:&v,parked:&parked,parked_ht:&parked,vg:&[],zshift:&[],zoff_on:false,ht_mode:false,kmax:23,mt:129};
        c.all_bands_probe(&mut b,false,false);let hr=b.ops.clone();let hr_t=b.tof;
        b.ops.clear();b.tof=0;let htr=rec(&mut b,|b|c.all_bands_probe(b,true,false));b.play(&htr,true);let ht=b.ops.clone();let ht_t=b.tof;
        b.ops.clear();b.tof=0;c.all_bands_probe(&mut b,false,true);let bad=b.ops.clone();
        let width=b.width()as usize;
        let hr_hmr=super::super::super::q675_vform_tests::receipt_audit(&hr);let ht_hmr=super::super::super::q675_vform_tests::receipt_audit(&ht);eprintln!("Q675_RECEIPTS hr_HMR={hr_hmr} ht_HMR={ht_hmr} private_bit=0 immediate_CZ=true incoming_bit_dead=true final_private_bit_unspecified=true");
        let mut cases=vec![];for sy in cp.sy.0..=cp.sy.1.min(128){for gap in 0usize..=22{let sz=257-sy-gap;if sz<cp.sz.0||sz>cp.sz.1||sy>sz{continue;}for seed in 0..8usize{cases.push((sy,sz,seed));}}}
        let mut lanes=0;let mut negative=0;
        for tape in 0..3{for active in[u64::MAX,0,0x5555555555555555]{for batch in cases.chunks(64){
            let mut input=vec![0u64;width];input[fd.ph.0 as usize]=!active;
            for(i,&q)in dirty.iter().enumerate(){input[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left(i as u32);}
            let mut expected=input.clone();
            for(lane,&(sy,sz,seed))in batch.iter().enumerate(){
                let ym=(U256::from(1u64)<<(sy-1))-U256::from(1u64);
                let noise=(U256::from(0x9e3779b97f4a7c15u64.rotate_left((seed*7)as u32))<<64)|U256::from(0xd1b54a32d192ed03u64.rotate_left((seed*11)as u32));
                let y=(U256::from(1u64)<<(sy-1))|(if seed==0{U256::ZERO}else if seed==1{ym}else{noise&ym})|U256::from(1u64);
                let zh=U256::from((1u64<<23)|((seed as u64*99991)&((1<<23)-1))|1);
                let z=(zh<<(sz-24))|U256::from(1u64);
                let x=if seed%2==0{U256::from(seed)}else{y-U256::from(seed+1)};
                let l=257-sz;let f=((U256::from(1u64)<<(256-sz+24))-U256::from(1u64))/zh;
                let u=l.saturating_sub(26);let threshold=(f>>u<<u)|((U256::from(1u64)<<u)-U256::from(1u64));
                let x=x.min(threshold);let quotient=(threshold-x)/y;assert!(quotient<(U256::from(1u64)<<23));let result=x+quotient*y;
                put(&mut input,&fd.q,lane,y);put(&mut input,&fd.sy,lane,U256::from(sy));put(&mut input,&sc.sz,lane,U256::from(sz));
                put(&mut input,&fd.ring[..sz],lane,z);let top:Vec<_>=fd.ring.iter().rev().take(l).copied().collect();put(&mut input,&top,lane,x);
                put(&mut expected,&fd.q,lane,y);put(&mut expected,&fd.sy,lane,U256::from(sy));put(&mut expected,&sc.sz,lane,U256::from(sz));
                put(&mut expected,&fd.ring[..sz],lane,z);put(&mut expected,&top,lane,if active>>lane&1!=0{result}else{x});
            }
            let out=super::super::super::q675_vform_tests::run_tape(&hr,width,&input,tape);let diff:Vec<_>=out.q.iter().zip(&expected).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,a^b)).collect();
            assert!(diff.is_empty()&&out.phase==0,"active composition mismatch tape={tape} active={active:x} diff={diff:?} phase={:x}",out.phase);
            let mut ht_input=expected.clone();ht_input[fd.ph.0 as usize]=active;
            let mut ht_want=input.clone();ht_want[fd.ph.0 as usize]=active;
            let back=super::super::super::q675_vform_tests::run_tape(&ht,width,&ht_input,tape);let diff:Vec<_>=back.q.iter().zip(&ht_want).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,a^b)).collect();
            assert!(diff.is_empty()&&back.phase==0,"HT inverse composition mismatch tape={tape} active={active:x} diff={diff:?} phase={:x}",back.phase);
            if active==u64::MAX&&tape==2{let wrong=super::super::super::q675_vform_tests::run_tape(&bad,width,&input,tape);for lane in 0..batch.len(){if fd.sx[1..6].iter().any(|q|wrong.q[q.0 as usize]>>lane&1!=0){negative+=1;}}}
            lanes+=batch.len();
        }}}
        assert!(negative>0);eprintln!("Q675_HR_HT_COMPOSITION_PASS omitted_final_join_detected={negative} lanes_per_arm={lanes} hr_ops={} hr_T={} ht_ops={} ht_T={} Q={width} actual_col=34 payload_none=true arithmetic_oracle=truncated_reciprocal production=false",hr.len(),hr_t,ht.len(),ht_t);
    }

    #[test]
    fn b9b_focused_675_cost_probe(){
        super::super::super::bake_knobs();
        std::env::set_var("B9B_COST","1");
        for col in [37usize,100] {
            let (mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
            let (mut cols,_,_)=super::super::super::pointadd_frogdrop::col_pars(
                &super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP));
            let cp=&mut cols[col];cp.n=258;cp.h=1;
            let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
            let pl=super::super::super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);
            super::super::middle(&mut b,&fd,cp,&sc,Some(&pl),&[],&mut |_|true);
            eprintln!("B9B_COST col={col} phase=whole_middle T={} ops={} Q={}",b.tof,b.ops.len(),b.width());
        }
        for fam in -1i8..5 {
            let (mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
            let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
            super::super::super::q675_support::route(&mut b,fam,&fd.sy[..7],&sc.sz[..5],
                &[sc.bq,fd.q[127],fd.q[126],fd.q[125]],&[fd.ph,sc.sw],&dirty,false);
            eprintln!("B9B_COST family={fam} phase=route T={} ops={}",b.tof,b.ops.len());
        }
        std::env::remove_var("B9B_COST");
    }

    #[test]
    fn b9b_skip_layout_four_owners(){
        for sy in 1..=128 {
            let positions=super::b9b_skip_positions(sy);
            let q125=match sy%4 {0=>125,1=>126,2=>123,_=>124};
            let q126=if sy%2==0 {126}else{125};
            let owners=[128,127,q126,q125];
            assert_eq!(positions.len(),129-sy);
            assert_eq!(positions[0],sy);
            let mut sorted=positions.clone();sorted.sort_unstable();
            assert_eq!(sorted,(sy..=128).collect::<Vec<_>>());
            let split=positions.iter().position(|p|owners.contains(p)).unwrap();
            assert!(positions[..split].iter().all(|p|!owners.contains(p)));
            assert!(positions[split..].iter().all(|p|owners.contains(p)));
            assert!(positions[split..].windows(2).all(|v|v[0]<v[1]));
        }
        assert_eq!(super::b9b_skip_positions(123),vec![123,126,124,125,127,128]);
        assert_eq!(super::b9b_skip_positions(125),vec![125,126,127,128]);
        assert_eq!(super::b9b_skip_positions(128),vec![128]);
    }

    #[test]
    fn b9b_frame_dispatch_n258_zshift_all_wire(){
        let(mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
        let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
        let(mut cps,_,_)=super::super::super::pointadd_frogdrop::col_pars(
            &super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP));
        let cp=&mut cps[36];cp.n=258;cp.h=1;
        let zlo=cp.sz.0;
        let zshift=rec(&mut b,|b|super::super::super::frogdrop::add_const_dirty_exact(
            b,&sc.sz,zlo,&dirty));
        let c=Cross{fd:&fd,cp,sc:&sc,pl:None,vform:&[],parked:&[],parked_ht:&[],
            vg:&[],zshift:&zshift,zoff_on:true,ht_mode:false,kmax:23,mt:129};
        let frame=c.frame(&mut b);b.play(&frame,false);let forward=b.ops.len();b.play(&frame,true);
        let width=b.width()as usize;
        let cases:Vec<_>=(1usize..=128).flat_map(|sy|(0usize..=25).filter_map(move|g|{
            let sz=257-sy-g;(sz<=255).then_some((sy,sz,g))})).collect();
        let mut lanes=0usize;
        for tape in 0..3usize {for batch in cases.chunks(64){
            let mut input=vec![0u64;width];
            for(i,&q)in fd.ring.iter().chain(dirty.iter()).enumerate(){
                input[q.0 as usize]=match tape{0=>0,1=>u64::MAX,
                    _=>0x9e3779b97f4a7c15u64.rotate_left((i*13)as u32)};
            }
            for(lane,&(sy,sz,_))in batch.iter().enumerate(){
                let encoded=(sz+256-zlo%256)%256;
                for i in 0..8 {
                    input[fd.sy[i].0 as usize]|=(((sy>>i)&1)as u64)<<lane;
                    input[sc.sz[i].0 as usize]|=(((encoded>>i)&1)as u64)<<lane;
                }
            }
            let out=run(&b.ops[..forward],width,&|x|*x=input.clone());
            assert_eq!(out.phase,0);
            for(lane,&(_,_,gap))in batch.iter().enumerate(){
                let code=match gap{23=>54,24=>86,25=>118,_=>gap};
                let tb=code&31;
                for i in 0..8 {assert_eq!(out.q[sc.sz[i].0 as usize]>>lane&1,
                    ((code>>i)&1)as u64,"zshift frame code gap={gap}");}
                for i in 107..258 {assert_eq!(out.q[fd.ring[(i+tb)%258].0 as usize]>>lane&1,
                    input[fd.ring[i].0 as usize]>>lane&1,"zshift frame care gap={gap}");}
                for &q in dirty.iter().chain(fd.sy.iter()) {
                    assert_eq!((out.q[q.0 as usize]^input[q.0 as usize])>>lane&1,0);
                }
            }
            let back=run(&b.ops,width,&|x|*x=input.clone());
            assert_eq!(back.q,input);assert_eq!(back.phase,0);
            lanes+=batch.len();
        }}
        eprintln!("B9B_FRAME_ZSHIFT_PASS lanes={lanes} zlo={zlo} forward_ops={forward} Q={width} inverse_full_state=true phase_zero=true");
    }

    #[test]
    fn b9b_skip_park_lane_all_wire(){
        let mut cases=0usize;
        for idx in 0usize..23 {
            let(mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
            let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
            let(mut cps,_,_)=super::super::super::pointadd_frogdrop::col_pars(
                &super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP));
            let cp=&mut cps[36];cp.n=258;cp.h=1;cp.sy=(1,128);
            let c=Cross{fd:&fd,cp,sc:&sc,pl:None,vform:&[],parked:&[],parked_ht:&[],
                vg:&[],zshift:&[],zoff_on:false,ht_mode:false,kmax:23,mt:129};
            b.begin();c.park_lane(&mut b,0,idx,0,sc.cmpc,fd.ph);
            let record=b.end();b.play(&record,false);let forward=b.ops.len();b.play(&record,true);
            let width=b.width()as usize;
            for tape in 0..3usize {
                let sy_cases:Vec<_>=(1..=128-idx).collect();
                for batch in sy_cases.chunks(64) {
                    let mut input=vec![0u64;width];
                    for(i,&q)in fd.ring.iter().chain(fd.q.iter()).chain(fd.sx.iter())
                        .chain(dirty.iter()).enumerate(){
                        input[q.0 as usize]=match tape {0=>0,1=>u64::MAX,
                            _=>0x9e3779b97f4a7c15u64.rotate_left((i*11)as u32)};
                    }
                    input[sc.cmpc.0 as usize]=0x5a69b4c387d2e10fu64 &
                        (if batch.len()==64 {u64::MAX}else{(1u64<<batch.len())-1});
                    for(lane,&sy)in batch.iter().enumerate(){
                        for i in 0..8 {let q=fd.sy[i].0 as usize;
                            input[q]=(input[q]&!(1u64<<lane))|((((sy>>i)&1)as u64)<<lane);}
                    }
                    let mut expected=input.clone();
                    for(lane,&sy)in batch.iter().enumerate(){
                        let pos=super::b9b_skip_positions(sy)[idx];
                        let target=if pos<128{fd.q[pos]}else{sc.bq};
                        expected[target.0 as usize]^=input[sc.cmpc.0 as usize]&(1u64<<lane);
                    }
                    let out=run(&b.ops[..forward],width,&|x|*x=input.clone());
                    assert_eq!(out.q,expected,"skip flight idx={idx} tape={tape} batch={batch:?}");
                    assert_eq!(out.phase,0);
                    let back=run(&b.ops,width,&|x|*x=input.clone());
                    assert_eq!(back.q,input,"skip inverse idx={idx} tape={tape} batch={batch:?}");
                    assert_eq!(back.phase,0);
                    cases+=batch.len();
                }
            }
        }
        eprintln!("B9B_SKIP_PARK_PASS lanes={cases} full_state=true forward_inverse=true phase_zero=true");
    }

    #[test]
    fn b9b_skip_park_modes_all_wire(){
        let mut cases=0usize;
        for (family,bit) in [(0u8,1usize),(1,12),(2,5)] {
            for mode in 1u8..=3 {
                let(mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
                let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
                let(mut cps,_,_)=super::super::super::pointadd_frogdrop::col_pars(
                    &super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP));
                let cp=&mut cps[36];cp.n=258;cp.h=1;cp.sy=(1,128);
                let c=Cross{fd:&fd,cp,sc:&sc,pl:None,vform:&[],parked:&[],parked_ht:&[],
                    vg:&[],zshift:&[],zoff_on:false,ht_mode:false,kmax:23,mt:129};
                b.begin();c.park_lane(&mut b,family,bit,mode,sc.cmpc,fd.ph);
                let record=b.end();b.play(&record,false);let forward=b.ops.len();b.play(&record,true);
                let width=b.width()as usize;
                let sy_cases:Vec<_>=(1..=128).filter(|&sy|{
                    let idx=if family==1{bit.saturating_sub(t1(sy))}else{bit};
                    idx<super::b9b_skip_positions(sy).len()
                }).collect();
                for tape in 0..3usize {for batch in sy_cases.chunks(64){
                    let mut input=vec![0u64;width];
                    for(i,&q)in fd.ring.iter().chain(fd.q.iter()).chain(fd.sx.iter())
                        .chain(dirty.iter()).enumerate(){
                        input[q.0 as usize]=match tape{0=>0,1=>u64::MAX,
                            _=>0x9e3779b97f4a7c15u64.rotate_left((i*13)as u32)};
                    }
                    input[sc.cmpc.0 as usize]=0;
                    input[fd.ph.0 as usize]=0;
                    input[fd.sx[6].0 as usize]=0;
                    for(lane,&sy)in batch.iter().enumerate(){
                        for i in 0..8 {let q=fd.sy[i].0 as usize;
                            input[q]=(input[q]&!(1u64<<lane))|((((sy>>i)&1)as u64)<<lane);}
                        if lane%2==0{input[sc.cmpc.0 as usize]|=1u64<<lane;}
                        if lane%3!=0{input[fd.ph.0 as usize]|=1u64<<lane;}
                        if lane%5!=0{input[fd.sx[6].0 as usize]|=1u64<<lane;}
                    }
                    let mut expected=input.clone();
                    for(lane,&sy)in batch.iter().enumerate(){
                        let idx=if family==1{bit.saturating_sub(t1(sy))}else{bit};
                        let pos=super::b9b_skip_positions(sy)[idx];
                        let target=if pos<128{fd.q[pos]}else{sc.bq};
                        let mask=1u64<<lane;
                        let on= input[fd.ph.0 as usize]&mask!=0 &&
                            (mode!=3 || input[fd.sx[6].0 as usize]&mask!=0);
                        if on {
                            if mode==2 {expected[target.0 as usize]^=input[sc.cmpc.0 as usize]&mask;}
                            else {
                                let a=expected[target.0 as usize]&mask!=0;
                                let b=expected[sc.cmpc.0 as usize]&mask!=0;
                                if a!=b {expected[target.0 as usize]^=mask;
                                    expected[sc.cmpc.0 as usize]^=mask;}
                            }
                        }
                    }
                    let out=run(&b.ops[..forward],width,&|x|*x=input.clone());
                    assert_eq!(out.q,expected,"skip modes family={family} bit={bit} mode={mode} tape={tape}");
                    assert_eq!(out.phase,0);
                    let back=run(&b.ops,width,&|x|*x=input.clone());
                    assert_eq!(back.q,input);
                    assert_eq!(back.phase,0);
                    cases+=batch.len();
                }}
            }
        }
        eprintln!("B9B_SKIP_MODES_PASS lanes={cases} all_modes=true full_state=true phase_zero=true");
    }

    #[test]
    fn b9b_hrht_middle_skip_modes_all_wire(){
        let mut cases=0usize;
        for kind in 0..2{for bit in 1usize..13{for mode in 1u8..=3{
            let(mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
            let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
            let(mut cps,_,_)=super::super::super::pointadd_frogdrop::col_pars(
                &super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP));
            let cp=&mut cps[36];cp.n=258;cp.h=1;cp.sy=(1,128);
            let parked=vec![vec![];3];
            let c=Cross{fd:&fd,cp,sc:&sc,pl:None,vform:&[],
                parked:if kind==0{&parked}else{&[]},parked_ht:if kind==1{&parked}else{&[]},
                vg:&[],zshift:&[],zoff_on:false,ht_mode:kind==1,kmax:23,mt:129};
            let sy_cases:Vec<_>=(1..=128).filter(|&sy|{
                let t=c.cut_t1(sy);bit>=t&&bit-t<super::b9b_skip_positions(sy).len()
            }).collect();
            if sy_cases.is_empty(){continue;}
            b.begin();c.park_lane(&mut b,1,bit,mode,sc.cmpc,fd.ph);
            let record=b.end();b.play(&record,false);let forward=b.ops.len();b.play(&record,true);
            let width=b.width()as usize;
            for tape in 0..3usize{for batch in sy_cases.chunks(64){
                let mut input=vec![0u64;width];
                for(i,&q)in fd.ring.iter().chain(fd.q.iter()).chain(fd.sx.iter()).chain(dirty.iter()).enumerate(){
                    input[q.0 as usize]=match tape{0=>0,1=>u64::MAX,_=>0x9e3779b97f4a7c15u64.rotate_left((i*13)as u32)};
                }
                input[sc.cmpc.0 as usize]=0;input[fd.ph.0 as usize]=0;input[fd.sx[6].0 as usize]=0;
                for(lane,&sy)in batch.iter().enumerate(){
                    for i in 0..8{let q=fd.sy[i].0 as usize;input[q]=(input[q]&!(1<<lane))|((((sy>>i)&1)as u64)<<lane);}
                    if lane%2==0{input[sc.cmpc.0 as usize]|=1<<lane;}
                    if lane%3!=0{input[fd.ph.0 as usize]|=1<<lane;}
                    if lane%5!=0{input[fd.sx[6].0 as usize]|=1<<lane;}
                }
                let mut want=input.clone();
                for(lane,&sy)in batch.iter().enumerate(){
                    let idx=bit-c.cut_t1(sy);let pos=super::b9b_skip_positions(sy)[idx];
                    let target=if pos<128{fd.q[pos]}else{sc.bq};let mask=1u64<<lane;
                    let on=input[fd.ph.0 as usize]&mask!=0&&(mode!=3||input[fd.sx[6].0 as usize]&mask!=0);
                    if on{if mode==2{want[target.0 as usize]^=input[sc.cmpc.0 as usize]&mask;}
                        else{let a=want[target.0 as usize]&mask!=0;let f=want[sc.cmpc.0 as usize]&mask!=0;
                            if a!=f{want[target.0 as usize]^=mask;want[sc.cmpc.0 as usize]^=mask;}}
                    }
                }
                let out=run(&b.ops[..forward],width,&|x|*x=input.clone());
                assert_eq!(out.q,want,"kind={kind} bit={bit} mode={mode} tape={tape}");assert_eq!(out.phase,0);
                let back=run(&b.ops,width,&|x|*x=input.clone());assert_eq!(back.q,input);assert_eq!(back.phase,0);
                cases+=batch.len();
            }}
        }}}
        eprintln!("B9B_HRHT_SKIP_PASS lanes={cases} middle_all_j=true dirty=3 modes=3 inverse=true phase=0");
    }

    #[test]
    fn b9b_gap_relabel_all_wire(){
        let rows=[(117u8,23u8,24u8),(121,15,16),(122,13,16),(123,11,16),
            (124,7,16),(125,7,16),(127,3,16)];
        let mut cases=0usize;
        for &(size,a,z) in &rows {
            let(mut b,fd,pool,dirty)=super::super::super::q675_layout_tests::ports(258);
            let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
            b.begin();super::b9b_relabel_gap(&mut b,&fd.sy,&sc.sz,size,a,z,&[fd.ph,sc.sw],&dirty);
            let record=b.end();b.play(&record,false);let forward=b.ops.len();let t=b.tof;
            b.play(&record,true);
            let width=b.width()as usize;
            let mut states=vec![];
            for code in 0..32usize {for s in [size as usize,(size^1)as usize,128usize] {
                for guard in 0..4usize {states.push((code,s,guard));}
            }}
            for tape in 0..3usize {for chunk in states.chunks(64){
                let mut input=vec![0u64;width];
                for (i,&q) in fd.ring.iter().chain(fd.q.iter()).chain(fd.sx.iter()).chain(dirty.iter()).enumerate(){
                    input[q.0 as usize]=match tape {0=>0,1=>u64::MAX,_=>0x9e3779b97f4a7c15u64.rotate_left((i*7)as u32)};
                }
                for (lane,&(code,s,guard)) in chunk.iter().enumerate(){
                    for i in 0..7 {input[fd.sy[i].0 as usize]=(input[fd.sy[i].0 as usize]&!(1<<lane))|((((s>>i)&1)as u64)<<lane);}
                    for i in 0..5 {input[sc.sz[i].0 as usize]=(input[sc.sz[i].0 as usize]&!(1<<lane))|((((code>>i)&1)as u64)<<lane);}
                    for (i,q) in [fd.ph,sc.sw].iter().enumerate(){input[q.0 as usize]=(input[q.0 as usize]&!(1<<lane))|((((guard>>i)&1)as u64)<<lane);}
                }
                let mut want=input.clone();
                for (lane,&(code,s,guard)) in chunk.iter().enumerate(){
                    if s&127==size as usize && guard==0 && (code==a as usize || code==z as usize){
                        for i in 0..5 {if (a^z)>>i&1!=0 {want[sc.sz[i].0 as usize]^=1<<lane;}}
                    }
                }
                let out=run(&b.ops[..forward],width,&|q|*q=input.clone());
                assert_eq!(out.phase,0);assert_eq!(out.q,want,"relabel forward size={size} tape={tape}");
                let back=run(&b.ops,width,&|q|*q=input.clone());
                assert_eq!(back.phase,0);assert_eq!(back.q,input,"relabel inverse size={size} tape={tape}");
                cases+=chunk.len();
            }}
            eprintln!("B9B_RELABEL size={size} from={a} to={z} forward_T={t} ops={forward}");
        }
        eprintln!("B9B_RELABEL_PASS lane_cases={cases} all_wire=true dirty_passengers=true guards=true phase=0");
    }

    include!("q675_payload_probe.rs");
}
