//! SOURCE-ONLY reserve; not connected to a candidate.
//!
//! Ordinary active size state is E=Y-1 in seven bits and
//! S=Z+Y-226 in five bits. Every one of the 4096 binary words is
//! a valid pair: 1<=Y<=128 and 98<=Z<=256. No Q data is packed here.
//! The affine involution E -> 225+S-E (mod128) exposes Z mod128.
//! Its inverse restores E for ALL binary inputs and arbitrary donors.
//! DONE/first-HT/tail protocols and physical ownership are not supplied
//! by this reserve. A caller may enter this view only after those are closed.

use super::builder::{B,G};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone)]
pub(crate) struct SumSize {
    pub y: [QubitId;7],
    pub sum: [QubitId;5],
}

impl SumSize {
    fn bank(&self,target:Option<QubitId>,extra:&[(QubitId,bool)],dirty:&[QubitId])
        ->Vec<QubitId> {
        let mut occupied:BTreeSet<_>=self.y.iter().chain(&self.sum).copied().collect();
        assert_eq!(occupied.len(),12);
        if let Some(q)=target {assert!(occupied.insert(q));}
        occupied.extend(extra.iter().map(|x|x.0));
        let mut seen=BTreeSet::new();
        dirty.iter().copied().filter(|q|!occupied.contains(q)&&seen.insert(*q)).collect()
    }

    /// 34 literal CCX before cancellation, no clean workspace:
    /// TTK7=12, inverse padding TTK2=2, +98 NAF (+2,-32)=20.
    /// Padding donors are arbitrary and restored before the constant add.
    pub(crate) fn z_epoch(&self,b:&mut B,dirty:&[QubitId])->Vec<G> {
        let bank=self.bank(None,&[],dirty);assert!(bank.len()>=6);
        let padded:Vec<_>=self.sum.iter().chain(&bank[..2]).copied().collect();
        b.begin();
        for &q in &self.y {b.x(q);}
        super::arith::ttk_add(b,&padded,&self.y,None,None);
        b.begin();super::arith::ttk_add(b,&bank[..2],&self.y[5..],None,None);
        let correction=b.end();b.play(&correction,true);
        super::frogdrop::add_const_dirty_exact(b,&self.y,98,&bank);
        b.end()
    }

    fn eq(bits:&[QubitId],v:usize)->Vec<(QubitId,bool)> {
        bits.iter().enumerate().map(|(i,&q)|(q,(v>>i)&1==0)).collect()
    }

    /// Disjoint dyadic cover; no circuit construction is used to select it.
    fn interval(bits:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>> {
        assert!(lo<=hi&&hi<=1usize<<bits.len());
        let mut terms=vec![];
        while lo<hi {
            let mut free=if lo==0 {bits.len()}else{lo.trailing_zeros()as usize};
            free=free.min(bits.len());
            while lo+(1usize<<free)>hi {free-=1;}
            terms.push((free..bits.len()).map(|i|(bits[i],(lo>>i)&1==0)).collect());
            lo+=1usize<<free;
        }
        terms
    }

    pub(crate) fn y_terms(&self,size:usize)->Vec<Vec<(QubitId,bool)>> {
        if !(1..=128).contains(&size){return vec![];}
        vec![Self::eq(&self.y,size-1)]
    }

    /// Called ONLY in the complete z_epoch view. The S intervals resolve
    /// both aliases98..127/226..255 and the exceptional128/256 address0.
    /// Equalities are pairwise disjoint over ALL 4096 metadata inputs.
    pub(crate) fn z_terms(&self,size:usize)->Vec<Vec<(QubitId,bool)>> {
        let (lo,hi)=match size {
            98..=127=>(0,size-97),128=>(0,31),129..=225=>(0,32),
            226..=255=>(size-225,32),256=>(31,32),_=>return vec![],
        };
        let eq=Self::eq(&self.y,size%128);
        Self::interval(&self.sum,lo,hi).into_iter().map(|mut c|{
            c.extend(eq.iter().copied());c
        }).collect()
    }

    /// Literal unitary query. No conditional-clean or measurement claim.
    pub(crate) fn xor_terms(&self,b:&mut B,terms:Vec<Vec<(QubitId,bool)>>,
        target:QubitId,extra:&[(QubitId,bool)],dirty:&[QubitId]) {
        assert!(!extra.iter().any(|p|p.0==target));
        let bank=self.bank(Some(target),extra,dirty);
        for mut term in terms {
            let mut contradiction=false;
            for &(q,neg) in extra {
                if let Some((_,n))=term.iter().find(|p|p.0==q) {
                    if *n!=neg {contradiction=true;break;}
                }else{term.push((q,neg));}
            }
            if !contradiction {mc_xor(b,&term,target,&[],&bank);}
        }
    }
}
