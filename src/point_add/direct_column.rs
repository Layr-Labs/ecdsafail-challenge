//! SOURCE-ONLY direct E7/S5 column boundary adapter, not registered/emitted.
//!
//! This wires stages1,1a,2 and8..10. The complete middle3..7 is an explicit
//! trait boundary with four scalar owners; it is NOT supplied by a legacy
//! global joint-size flag. Map/tail/counter and the special endpoint remain
//! separate caller epochs. No extra quantum owner is hidden in a handle.
use super::builder::{B,G};
use super::direct_payload::{self,Ranges};
use super::frogdrop_col::ColPar;
use super::mask::mc_xor;
use super::outer_size::{self,Roles};
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

/// Concrete remaining integration surface. This is exactly ONE complete
/// middle, not a fragment stopped between reciprocal or payload records.
///
/// Entry: Q=Y, E=Y-1, S=Z+Y-226, tag=W, other three roles0, PH phase.
/// Exit: Q=Y, ring contains X_new, same E/S and PH; ALL four roles0.
/// Counter121..127 is unchanged, and PH payload loans have closed.
///
/// HR controller starts from W in its A owner. XOR !PH into that owner
/// produces !PH&!W (W=>!PH); the identical XOR after HR restores W.
/// Before HT S5, erase W with the unchanged size predicate, then retain HT
/// activity. HT digit/P transition closes before returning A0 and entering
/// the S6 controller (whose own entry toggles HT activity). Return A0 at end.
///
/// Cross keeps QB30/head32/TC32/two bands. Fixed keeps QB23/head24/TC32 and
/// the exact parent's comparator family through FixedRawLayout. A fixed
/// adapter must apply its explicit suffix/R/counter descriptor, not just
/// pretend a seven-bit fd.sy is an old raw8 register.
///
/// T1/T4 use the same complete boundary protocol. T2/T3 have compact=None:
/// they do not open PH payload, but must execute the identical arithmetic,
/// activity transitions and V/park inverse schedule without an extra owner.
pub(crate) trait Middle{
    fn run_complete(&mut self,b:&mut B,column:&Column<'_>,cp:&ColPar);
}

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
fn ranges(word:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    assert!(lo<=hi&&hi<=1usize<<word.len());let mut out=vec![];
    while lo<hi{
        let mut free=if lo==0{word.len()}else{lo.trailing_zeros()as usize};
        free=free.min(word.len());while lo+(1usize<<free)>hi{free-=1;}
        out.push((free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect());
        lo+=1usize<<free;
    }out
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
            .copied().chain([self.phase,r.tag,r.cut,r.toggle,r.prefix])
            .all(|q|u.insert(q)));
        if let Some(p)=self.compact{assert_eq!(p.len(),258);assert!(p.iter().all(|q|u.insert(*q)));}
    }
    /// No-P donor universe. Queries exclude their actual controls/target;
    /// whole ring probes use raw Q donors, and Q probes use ring donors.
    fn bank(&self)->Vec<QubitId>{
        let r=self.roles;let mut excluded:BTreeSet<_>=self.meta.y.iter().chain(&self.meta.sum)
            .copied().chain([self.phase,r.tag,r.cut,r.toggle,r.prefix]).collect();
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
    fn swap_top_record(&self,b:&mut B,extra:&[(QubitId,bool)])->Vec<G>{
        super::byte_cut_swap::record(b,self.meta,self.roles,self.ring,self.q,extra,&self.bank())
    }

    /// Input: E is actual top Y-1 on C0 and tagged bottom M-1 on C1;
    /// S=0. Output: Q=Y, original E/S valid, tag=new W. Incoming C exists
    /// only on the original public psw||dq columns; it is erased BEFORE W.
    pub(crate) fn enter_middle(&self,b:&mut B,cp:&ColPar){
        self.check(cp);let d=self.bank();
        let stage1=outer_size::stage1_record(b,self.meta,self.roles,self.ring,
            (cp.sz.0-1,cp.sz.1),&d);b.play(&stage1,false);
        if let Some(p)=self.compact{if cp.pht{
            assert!(cp.col>0);
            let lo=cp.sz.0.max(256-cp.psy.1.min(128));
            let hi=cp.sz.1.min(255).min(257-cp.psy.0.max(1));
            if lo<=hi{
                self.xor_ht_narrow_activity(b,cp,self.roles.cut);
                direct_payload::narrow_ht(b,self.meta,p,self.q,(lo,hi),
                    self.roles.cut,self.roles.toggle,&d);
                self.xor_ht_narrow_activity(b,cp,self.roles.cut);
            }
        }}
        let swap=self.swap_top_record(b,&[(self.roles.tag,true)]);b.play(&swap,false);
        if cp.psw||cp.dq{
            let refill=outer_size::tagged_refill_record(b,self.meta,self.roles,self.q,&d);
            b.play(&refill,false);
            let erase=outer_size::erase_tag_record(b,self.meta,self.roles,
                self.phase,self.ring[128],&d);b.play(&erase,false);
        }
        if cp.sw{outer_size::xor_new_switch(b,self.meta,self.roles,self.phase,&d);}
    }

    /// Middle returned all roles0 and PH phase. Recreate W, move delayed
    /// data, narrow HR only at Z>=129, update its bottom sum, erase S
    /// with a fresh output probe, then perform the original C bottom/Q swap.
    /// Exit has E=oldY-1, S0, tag=C=W|D and three returned roles for map.
    pub(crate) fn leave_middle(&self,b:&mut B,cp:&ColPar){
        self.check(cp);let d=self.bank();
        let swap=self.swap_top_record(b,&[]);b.play(&swap,false);
        if cp.sw{outer_size::xor_new_switch(b,self.meta,self.roles,self.phase,&d);}
        if cp.dl{
            let movement=outer_size::delayed_move_record(b,self.meta,self.roles,
                self.phase,self.ring,cp.xw,&d);b.play(&movement,false);
        }
        if let Some(p)=self.compact{if cp.hr{
            // Match the inherited HR narrow domain Z>L0P=128. A delayed
            // HR step leaves POST through DQ; the following deferred HT
            // narrow converts it to PRE. Narrowing D here would apply
            // the adjacent-hole transform twice when its boundary moves.
            let range=(cp.sz.0.max(129),cp.sz.1);
            if range.0<=range.1{
                // A=!PH XOR W =!PH&!W; the range also excludes all D.
                b.x(self.roles.cut);b.cx(self.phase,self.roles.cut);
                if cp.sw{self.xor_switch(b,self.roles.cut);}
                direct_payload::narrow_hr(b,self.meta,p,self.q,self.ring,range,
                    self.roles.cut,self.roles.toggle,&d);
                if cp.sw{self.xor_switch(b,self.roles.cut);}
                b.cx(self.phase,self.roles.cut);b.x(self.roles.cut);
            }
        }}
        if cp.dl{
            let reprobe=outer_size::delayed_reprobe_record(b,self.meta,self.roles,
                self.phase,self.ring,cp.dlr.saturating_sub(1),cp.xw,&d);
            b.play(&reprobe,false);
        }
        // No inverse of stage1's old-C copy: outgoing C is a different tag.
        let lo=cp.sz.0.min(if cp.dl{cp.dlr}else{cp.sz.0}).saturating_sub(1);
        let hi=cp.sz.1.max(if cp.dl{cp.xw}else{cp.sz.1}).min(257);
        outer_size::erase_output_sum(b,self.meta,self.roles,self.ring,(lo,hi),&d);
        if cp.sw||cp.dl{for lane in 0..cp.swl.0{
            b.cswap(self.roles.tag,self.ring[lane],self.q[lane]);
        }}
    }
}

/// Complete stage1..10 source assembly. Source records captured by an outer
/// caller have literal inverses, including DONE and inactive payload paths.
/// The trait body is the sole explicit missing integration surface here.
pub(crate) fn through_stage10(b:&mut B,column:&Column<'_>,cp:&ColPar,middle:&mut impl Middle){
    column.enter_middle(b,cp);middle.run_complete(b,column,cp);column.leave_middle(b,cp);
}
