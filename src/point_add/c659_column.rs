//! Complete three-role outer descriptor. Legacy direct_column is unchanged.
use super::builder::{B,G};
use super::frogdrop_col::ColPar;
use super::mask::mc_xor;
use super::c659::Roles;
use super::outer_three_records::{OuterRecords, ThreeRoles, SwapBoundary};
use super::direct_payload::k4_complete::{narrow3,Address3,FlagHost};
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

pub(crate) struct Column<'a>{
    pub meta:&'a SumSize,
    pub roles:Roles,
    pub ring:&'a [QubitId],
    pub q:&'a [QubitId],
    pub phase:QubitId,
    pub compact:Option<&'a [QubitId]>,
    pub dirty:&'a [QubitId],
    /// Explicit whole-T2/T3 terminal payload zeros; empty on T1/T4.
    pub clean_external:&'a [QubitId],
}

fn wp4_enabled()->bool { std::env::var("C658_WP4").as_deref()==Ok("1") }

// Complete middle entry: Q=Y, E=Y-1, S=Z+Y-226, tag=W,
// cut/toggle zero, PH phase. The complete middle returns all three roles.
// Nonfixed QB30/head32/TC32 and fixed QB23/head25/TC32 remain separate.
fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn merge(a:&[(QubitId,bool)],z:&[(QubitId,bool)])->Option<Vec<(QubitId,bool)>>{
    let mut out=a.to_vec();for &p in z{
        if let Some(q)=out.iter().find(|q|q.0==p.0){if q.1!=p.1{return None;}}
        else{out.push(p);}
    }Some(out)
}
fn xor(b:&mut B,c:&[(QubitId,bool)],t:QubitId,dirty:&[QubitId]){
    assert!(!c.iter().any(|q|q.0==t));let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied().filter(|q|*q!=t
        &&!c.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    assert!(bank.len()>=c.len().saturating_sub(2));
    mc_xor(b,c,t,&[],&bank);
}

impl Column<'_>{
    fn check(&self,cp:&ColPar){
        assert_eq!((cp.n,cp.nq,cp.h,cp.l0),(257,128,0,128));
        assert!(!cp.nomap,"the special endpoint requires its explicit fixed endpoint adapter");
        assert!(98<=cp.sz.0&&cp.sz.0<=cp.sz.1&&cp.sz.1<=256);
        assert!(cp.xw<=257&&cp.swl.0<=128);
        assert_eq!((self.ring.len(),self.q.len()),(257,128));
        let r=self.roles;let mut u=BTreeSet::new();
        assert!(self.meta.y.iter().chain(&self.meta.sum).chain(self.ring).chain(self.q)
            .copied().chain([self.phase,r.tag,r.cut,r.toggle.port()]).filter(|q|super::c659::retained(*q))
            .all(|q|u.insert(q)));
        if let Some(p)=self.compact{assert_eq!(p.len(),258);assert!(p.iter().all(|q|u.insert(*q)));}
    }
    /// No-P donor universe. Queries exclude their actual controls/target;
    /// whole ring probes use raw Q donors, and Q probes use ring donors.
    pub(crate) fn bank(&self)->Vec<QubitId>{
        let r=self.roles;let mut excluded:BTreeSet<_>=self.meta.y.iter().chain(&self.meta.sum)
            .copied().chain([self.phase,r.tag,r.cut,r.toggle.port()]).filter(|q|super::c659::retained(*q)).collect();
        if let Some(p)=self.compact{excluded.extend(p.iter().copied());}
        self.dirty.iter().chain(self.ring).chain(self.q).copied()
            .filter(|q|excluded.insert(*q)).collect()
    }
    /// Parent derived DONE, with unchanged RA64 and counter121..127.
    /// Its exceptional active sparse-Q domain is inherited, not tightened.
    /// Never call inside a V record or PH-as-payload epoch.
    pub(crate) fn xor_done(&self,b:&mut B,target:QubitId,extra:&[(QubitId,bool)]){
        let d=self.bank();let mut a=vec![(self.phase,false)];
        a.extend(self.q[64..121].iter().map(|&q|(q,true)));
        let mut ab=a.clone();ab.extend(self.q[121..128].iter().map(|&q|(q,true)));
        for term in [a,ab]{if let Some(c)=merge(&term,extra){xor(b,&c,target,&d);}}
    }
    /// At the first stage only C from the previous tagged HT boundary is
    /// retained. This computes previous-HT narrow activity, including
    /// fresh DONE(counter1), with C excluded before reading size.
    fn xor_ht_narrow_activity(&self,b:&mut B,cp:&ColPar,target:QubitId){
        let extra=[(self.phase,false),(self.roles.tag,true)];
        xor(b,&extra,target,&self.bank());
        if cp.dn{
            self.xor_done(b,target,&[(self.roles.tag,true)]);
            let mut fresh=vec![(self.roles.tag,true),(self.q[121],false)];
            fresh.extend(self.q[122..128].iter().map(|&q|(q,true)));
            self.xor_done(b,target,&fresh);
        }
    }
    /// W=!PH & (Z<=Y). Can target any returned scalar independently of
    /// the retained outgoing C, so delayed D is not accidentally excluded.
    pub(crate) fn xor_switch(&self,b:&mut B,target:QubitId){
        super::direct_size_predicates::xor_switch(b,self.meta,self.phase,target,&self.bank());
    }
    /// HR entry tag=W -> retained A_HR, and the identical operation on
    /// exit restores W. DONE has PH1 and is therefore already excluded.
    pub(crate) fn toggle_hr_activity(&self,b:&mut B){
        b.x(self.roles.tag);b.cx(self.phase,self.roles.tag);
    }
    /// HT complete activity on an initially zero target; DQ skips Z<Y.
    /// The caller first erases W and closes every PH payload epoch.
    pub(crate) fn xor_ht_activity(&self,b:&mut B,cp:&ColPar,target:QubitId){
        let d=self.bank();
        xor(b,&[(self.phase,false)],target,&d);
        if cp.dn{self.xor_done(b,target,&[]);}
        if cp.dq{
            assert_ne!(target,self.roles.cut);
            let tape=super::direct_size_predicates::ht_excess_record(b,self.meta,self.roles.cut);
            b.play(&tape,false);
            let extra=[(self.phase,false),(self.meta.y[4],false),
                (self.meta.y[5],false),(self.meta.y[6],false),(self.meta.sum[4],false)];
            xor(b,&extra,target,&d);
            if cp.dn{self.xor_done(b,target,&extra);}
            b.play(&tape,true);
        }
    }

    /// Exact cut exchange ring[l] <-> Q[256-l] for l>=Z. Entry S may be
    /// the tagged temporary only when extra=!C disables every swap. Both
    /// z_epoch tapes are still complete literal inverses on that branch.
    fn outer(&self)->OuterRecords<'_>{
        let r=self.roles;
        OuterRecords::new(self.meta,ThreeRoles::new(r.tag,r.cut,r.toggle.port()),self.ring,self.q,wp4_enabled()&&self.compact.is_some())
    }

    /// Input: E is actual top Y-1 on C0 and tagged bottom M-1 on C1;
    /// S=0. Output: Q=Y, original E/S valid, tag=new W. Incoming C exists
    /// only on the original public psw||dq columns; it is erased BEFORE W.
    pub(crate) fn enter_middle(&self,b:&mut B,cp:&ColPar){
        self.check(cp);let d=self.bank();
        let plan=super::outer_three_records::bind_column(cp);
        super::r13prof::mk(b,30);let stage1=self.outer().stage1_record(b,&plan);b.play(&stage1,false);super::r13prof::mk(b,30);
        super::r13prof::mk(b,31);if let Some(p)=self.compact{if cp.pht{
            assert!(cp.col>0);
            let lo=cp.sz.0.max(256-cp.psy.1.min(128));
            let hi=cp.sz.1.min(255).min(257-cp.psy.0.max(1));
            if lo<=hi{
                self.xor_ht_narrow_activity(b,cp,self.roles.cut);
                let flag=if wp4_enabled(){FlagHost::Encoded{tag:self.roles.tag,cut:self.roles.cut}}
                    else{FlagHost::Lane(self.roles.toggle.lane())};
                narrow3(b,self.meta,p,self.q,None,(lo,hi),self.roles.cut,flag,
                    Address3::SevenBit{column_z_floor:cp.sz.0},&d,&[],true);
                self.xor_ht_narrow_activity(b,cp,self.roles.cut);
            }
        }}super::r13prof::mk(b,31);
        super::r13prof::mk(b,32);let swap=self.outer().cut_swap_record(b,&plan,SwapBoundary::Enter);b.play(&swap,false);super::r13prof::mk(b,32);
        super::r13prof::mk(b,33);if cp.psw||cp.dq{
            let refill=self.outer().tagged_refill_record(b);
            b.play(&refill,false);
            let erase=erase_tag_record(b,self.meta,self.roles,
                self.phase,self.ring[128],&d);b.play(&erase,false);
        }super::r13prof::mk(b,33);
        super::r13prof::mk(b,35);if cp.sw{xor_new_switch(b,self.meta,self.roles,self.phase,&d);}super::r13prof::mk(b,35);
    }

    /// Middle returned all roles0 and PH phase. Recreate W, move delayed
    /// data, narrow HR only at Z>=129, update its bottom sum, erase S
    /// with a fresh output probe, then perform the original C bottom/Q swap.
    /// Exit has E=oldY-1, S0, tag=C=W|D and two returned roles for map.
    pub(crate) fn leave_middle(&self,b:&mut B,cp:&ColPar){
        self.check(cp);let d=self.bank();
        let plan=super::outer_three_records::bind_column(cp);
        super::r13prof::mk(b,40);let swap=self.outer().cut_swap_record(b,&plan,SwapBoundary::AfterCompleteMiddle);b.play(&swap,false);super::r13prof::mk(b,40);
        super::r13prof::mk(b,41);if cp.sw{xor_new_switch(b,self.meta,self.roles,self.phase,&d);}super::r13prof::mk(b,41);
        super::r13prof::mk(b,42);if cp.dl{
            let movement=delayed_move_record(b,self.meta,self.roles,
                self.phase,self.ring,cp.xw,&d);b.play(&movement,false);
        }super::r13prof::mk(b,42);
        super::r13prof::mk(b,43);if let Some(p)=self.compact{if cp.hr{
            // Match the inherited HR narrow domain Z>L0P=128. A delayed
            // HR step leaves POST through DQ; the following deferred HT
            // narrow converts it to PRE. Narrowing D here would apply
            // the adjacent-hole transform twice when its boundary moves.
            let range=(cp.sz.0.max(129),cp.sz.1);
            if range.0<=range.1{
                // A=!PH XOR W =!PH&!W; the range also excludes all D.
                let encoded=wp4_enabled();
                if encoded{
                    b.x(self.phase);b.x(self.roles.tag);b.ccx(self.phase,self.roles.tag,self.roles.cut);
                    b.x(self.roles.tag);b.x(self.phase);
                }else{
                    b.x(self.roles.cut);b.cx(self.phase,self.roles.cut);
                    if cp.sw{self.xor_switch(b,self.roles.cut);}
                }
                let address=if range.1==256 {
                    // Only c0 reaches Z256; no incoming/outgoing C or W exists.
                    assert_eq!(cp.col,0);assert!(!(cp.sw||cp.psw||cp.dl||cp.dq));
                    if encoded{Address3::Direct}else{Address3::HostedTag(self.roles.tag)}
                }else{Address3::SevenBit{column_z_floor:cp.sz.0}};
                let flag=if encoded{FlagHost::Encoded{tag:self.roles.tag,cut:self.roles.cut}}
                    else{FlagHost::Lane(self.roles.toggle.lane())};
                narrow3(b,self.meta,p,self.q,Some(self.ring),range,
                    self.roles.cut,flag,address,&d,&[],false);
                if encoded{
                    b.x(self.phase);b.x(self.roles.tag);b.ccx(self.phase,self.roles.tag,self.roles.cut);
                    b.x(self.roles.tag);b.x(self.phase);
                }else{
                    if cp.sw{self.xor_switch(b,self.roles.cut);}
                    b.cx(self.phase,self.roles.cut);b.x(self.roles.cut);
                }
            }
        }}super::r13prof::mk(b,43);
        super::r13prof::mk(b,44);if cp.dl{
            let reprobe=self.outer().delayed_reprobe_record(b,&plan,self.phase);
            b.play(&reprobe,false);
        }super::r13prof::mk(b,44);
        // No inverse of stage1's old-C copy: outgoing C is a different tag.
        super::r13prof::mk(b,45);let erase=self.outer().output_erase_record(b,&plan);b.play(&erase,false);super::r13prof::mk(b,45);
        super::r13prof::mk(b,46);if cp.sw||cp.dl{for lane in 0..cp.swl.0{
            b.cswap(self.roles.tag,self.ring[lane],self.q[lane]);
        }}super::r13prof::mk(b,46);
    }
}


fn bank(size: &SumSize, roles: Roles, source: &[QubitId], extra: &[(QubitId, bool)],
        dirty: &[QubitId]) -> Vec<QubitId> {
    let ports: Vec<_> = size.y.iter().chain(&size.sum).copied()
        .chain([roles.tag, roles.cut, roles.toggle.port()]).filter(|q|super::c659::retained(*q)).collect();
    assert_eq!(ports.iter().copied().collect::<BTreeSet<_>>().len(), if matches!(roles.toggle,super::c659::Toggle::Evicted){14}else{15});
    assert_eq!(source.iter().copied().collect::<BTreeSet<_>>().len(), source.len());
    assert!(!source.iter().any(|q| ports.contains(q)));
    assert!(extra.len() <= 2);
    assert!(!extra.iter().any(|p| size.y.contains(&p.0) || size.sum.contains(&p.0) || source.contains(&p.0)));
    assert!(!extra.iter().any(|p| p.0 == roles.cut || p.0 == roles.toggle.port() ));
    let mut excluded: BTreeSet<_> = ports.into_iter().chain(source.iter().copied())
        .chain(extra.iter().map(|p| p.0)).collect();
    let out: Vec<_> = dirty.iter().copied().filter(|q| excluded.insert(*q)).collect();
    // Probe toggles have at most nine controls; general Z equalities can
    // have fourteen. Twelve donors cover even their plain dirty lowering.
    // No metadata, role, source lane or external control is borrowed.
    assert!(out.len() >= 12, "outer-size helpers require twelve external restored dirty donors");
    out
}
/// XOR an existing supported raw-Z equality while E is in its z_epoch.
fn xor_z(b: &mut B, size: &SumSize, value: usize, target: QubitId,
         extra: &[(QubitId, bool)], dirty: &[QubitId]) {
    size.xor_terms(b, size.z_terms(value), target, extra, dirty);
}

/// Clear the incoming C only AFTER refill has made the sum/size pair valid.
/// The old first-HT/DQ characterization is PH & (Z<=127 | Z128&topbit128).
/// Ordinary/data-inactive states still satisfy this inherited characterization.
pub(crate) fn erase_tag_record(b: &mut B, size: &SumSize, roles: Roles,
    phase: QubitId, old_top_bit128: QubitId, dirty: &[QubitId]) -> Vec<G> {
    let extra = [(phase, false), (old_top_bit128, false)];
    let d = bank(size, roles, &[], &extra, dirty);
    let z = size.z_epoch(b, &d);
    rec(b, |b| {
        b.play(&z, false);
        for v in 98..=127 { xor_z(b, size, v, roles.tag, &[(phase, false)], &d); }
        xor_z(b, size, 128, roles.tag, &extra, &d);
        b.play(&z, true);
    })
}

/// New W=!PH & Z<=Y, or total crossing C=!PH & Z<=128.
/// The exact S-specific thresholds use no raw-Z register or clean comparator.
/// Target normally is roles.tag; no predicate reads that owner.
fn xor_cross_predicate(b: &mut B, size: &SumSize, roles: Roles, phase: QubitId,
    switch_only: bool, dirty: &[QubitId]) {
    let d = bank(size, roles, &[], &[(phase, true)], dirty);
    if switch_only{
        super::direct_size_predicates::xor_switch(b,size,phase,roles.tag,&d);
    }else{
        super::direct_size_predicates::xor_crossing(b,size,phase,roles.tag,roles.cut,&d);
    }
}
pub(crate) fn xor_new_switch(b: &mut B, size: &SumSize, roles: Roles,
    phase: QubitId, dirty: &[QubitId]) {
    xor_cross_predicate(b, size, roles, phase, true, dirty);
}

/// Exact257-ring delayed upper-data relocation, retaining the original cut.
/// Entry tag=W; exit tag=C=W|D. No payload or narrow call is hidden here.
/// The caller performs HR narrowing after this record, before delayed_reprobe.
pub(crate) fn delayed_move_record(b: &mut B, size: &SumSize, roles: Roles,
    phase: QubitId, ring: &[QubitId], xw: usize, dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(ring.len(), 257); assert!(xw <= 257);
    let d = bank(size, roles, ring, &[(phase, true)], dirty);
    let z = size.z_epoch(b, &d);
    rec(b, |b| {
        xor_cross_predicate(b, size, roles, phase, false, &d); // W xor C =D.
        if xw > 129 {
            let lo = 257 - xw;
            b.play(&z, false);
            for v in 98..=127 { xor_z(b, size, v, roles.cut, &[(roles.tag, false)], &d); }
            for a in (lo..128).rev() {
                if a < 127 { xor_z(b, size, a + 1, roles.cut, &[(roles.tag, false)], &d); }
                b.cswap(roles.cut, ring[a], ring[256 - a]);
            }
            for a in lo + 1..128 { xor_z(b, size, a, roles.cut, &[(roles.tag, false)], &d); }
            for v in 98..=127 { xor_z(b, size, v, roles.cut, &[(roles.tag, false)], &d); }
            b.play(&z, true);
        }
        xor_new_switch(b, size, roles, phase, &d); // D xor W =C.
    })
}

