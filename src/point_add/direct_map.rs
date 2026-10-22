//! SOURCE-ONLY reserve. Intended child module of point_add::frogdrop.
//! No declaration/callsite enables this file. Sixteen map owners are:
//! M[7], ez[5], T,E,G, plus persistent C. PH and C are outside every tape.
//! Entry ABI: y=positive top size-1; scratch=[C,M0..M6,G].
//! Exit entry tape inverse restores the NEW top size-1 and all scratch.
use super::super::builder::{B,G};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;
fn record(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn unique(q:&[QubitId]){assert_eq!(q.len(),q.iter().collect::<BTreeSet<_>>().len());}

// A donor universe may include other operands. Borrow only across one
// complete primitive and exclude that primitive's live ports before use.
fn bank(universe:&[QubitId],held:&[QubitId])->Vec<QubitId>{
    let mut seen=BTreeSet::new();universe.iter().copied()
        .filter(|q|!held.contains(q)&&seen.insert(*q)).collect()
}
fn xor(b:&mut B,c:&[(QubitId,bool)],t:QubitId,pre:&[QubitId],universe:&[QubitId]){
    let held:Vec<_>=c.iter().map(|x|x.0).chain([t]).chain(pre.iter().copied()).collect();
    let d=bank(universe,&held);assert!(d.len()>=c.len().saturating_sub(2));
    mc_xor(b,c,t,pre,&d);
}
fn cubes(n:usize,mut lo:usize,hi:usize,mut f:impl FnMut(usize,usize)){
    assert!(lo<=hi && hi<=1usize<<n);
    while lo<hi {let a=if lo==0{n}else{lo.trailing_zeros()as usize};
        let r=(usize::BITS-1-(hi-lo).leading_zeros())as usize;let free=a.min(r).min(n);
        f(lo,free);lo+=1usize<<free;}
}
fn range(b:&mut B,w:&[QubitId],lo:usize,hi:usize,extra:&[(QubitId,bool)],
         out:QubitId,pre:&[QubitId],dirty:&[QubitId]){
    cubes(w.len(),lo,hi,|at,free|{let mut c=extra.to_vec();
        c.extend((free..w.len()).map(|i|(w[i],at>>i&1==0)));
        xor(b,&c,out,pre,dirty);});
}
/// One retained found bit, zero on entry/exit. Values are strictly
/// descending and nonzero. `out` starts zero only where gate is true;
/// arbitrary off-gate output is unchanged. Cut cubes per lane are disjoint.
fn priority_probe(b:&mut B,out:&[QubitId],tmp:QubitId,gate:Option<(QubitId,bool)>,
    lanes:Vec<(usize,QubitId,Vec<Vec<(QubitId,bool)>>)>,dirty:&[QubitId]){
    if let Some((c,neg))=gate {if !neg{b.x(tmp);}b.cx(c,tmp);} // tmp=!gate
    let mut previous=usize::MAX;
    for(value,source,cuts)in lanes{
        assert!(0<value && value<1usize<<out.len() && value<previous);previous=value;
        let pivot=value.trailing_zeros()as usize;
        b.x(tmp); // positive !found, already implies gate on the care domain
        for cut in cuts{
            let mut ctl=vec![(tmp,false),(source,false)];ctl.extend(cut);
            xor(b,&ctl,out[pivot],&[],dirty);
        }
        for(i,&q)in out.iter().enumerate(){
            if i!=pivot && value>>i&1!=0{b.ccx(tmp,out[pivot],q);}
        }
        b.x(tmp);
        // No previous found value can equal this lower value. Only the
        // newly selected lane changes tmp from0 to1 on enabled shots.
        let mut ctl:Vec<_>=gate.into_iter().collect();
        ctl.extend(out.iter().enumerate().map(|(i,&q)|(q,value>>i&1==0)));
        xor(b,&ctl,tmp,&[],dirty);
    }
    b.x(tmp);
    let mut ctl:Vec<_>=gate.into_iter().collect();ctl.extend(out.iter().map(|&q|(q,true)));
    xor(b,&ctl,tmp,&[],dirty); // !gate OR found, cleared for all off-gate outputs
}
// Public literal prices, independent of gate emission. Both ordinary and
// clean replay must improve; NAND exposes this complete entry as a literal
// U / U^-1 shell and therefore uses the ordinary column here.
#[derive(Clone,Copy,Default)]
struct ProbePrice { cx:usize, ccx:usize }
impl ProbePrice {
    fn normal(self)->usize { self.ccx }
    fn clean(self)->usize { self.cx+2*self.ccx }
}
fn dirty_mcx_price(n:usize)->usize {
    if n<2 {0} else if n==2 {1} else {4*(n-2)}
}
fn binary_probe_price(n:usize,gated:bool)->ProbePrice {
    assert!(n.is_power_of_two());
    // The gated caller copies !q[0] into the old found helper and clears
    // it only after all source folding has been reversed.
    let mut p=ProbePrice{cx:if gated{2}else{0},ccx:0};
    let mut half=n/2;
    while half>0 {
        if half==1 {if gated{p.ccx+=1;}else{p.cx+=1;}}
        else {p.ccx+=dirty_mcx_price(half+usize::from(gated));
            if gated{p.cx+=1;}}
        // Two complete half swaps, each CSWAP = 2CX + 1CCX.
        p.cx+=4*half;p.ccx+=2*half;half/=2;
    }
    p
}
fn old_probe_price(values:impl Iterator<Item=usize>,gated:bool)->ProbePrice {
    let q=dirty_mcx_price(7+usize::from(gated));
    let mut p=ProbePrice{cx:usize::from(gated),ccx:q};
    for v in values {p.ccx+=v.count_ones()as usize+q;}
    p
}
fn binary_admitted(n:usize,old:ProbePrice,gated:bool)->bool {
    let new=binary_probe_price(n,gated);
    new.normal()<=old.normal() && new.clean()<=old.clean()
}

/// Raw M=max(bl(Q),bl(top))-1 entry, using exactly one clean helper.
/// Care: Q and top positive, both sizes<=m<=q.len(); raw top y is exact;
/// ring top occupies reversed lanes 0..M and the bottom is outside them.
/// The donor universe excludes C/PH; each complete primitive excludes its own live ports.
/// The complete tape is literal-unitary, hence off-care U/U^-1 still cancels.
#[allow(clippy::too_many_arguments)]
pub(crate) fn entry_record(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],
    mword:&[QubitId],helper:QubitId,m:usize,mlo:usize,mhi:usize,dirty:&[QubitId])->Vec<G>{
    assert_eq!(y.len(),7);assert_eq!(mword.len(),7);
    assert!(1<=mlo && mlo<=mhi && mhi<=m && m<=q.len() && q.len()<=128);
    let p:Vec<_>=ring.iter().chain(q).chain(y).chain(mword).copied().chain([helper]).collect();
    unique(&p);
    let carry_ports:Vec<_>=mword.iter().chain(y).copied().chain([helper]).collect();
    let carry_bank=bank(dirty,&carry_ports);
    let d=*carry_bank.first().expect("order carry requires distinct restored donor");
    record(b,|b|{
        // Highest source index is m-1, so padding is to pow2ceil(m),
        // never pow2ceil(m+1). The public source bound proves all padded
        // Q cells zero on the entry care domain. Late Q121 counters are
        // excluded: if the power-of-two slice does not fit, keep priority.
        let first_n=m.next_power_of_two();
        if first_n<=q.len() && binary_admitted(first_n,old_probe_price((1..m).rev(),false),false) {
            let bits=first_n.trailing_zeros()as usize;
            let r=super::binary_msb::record(b,&q[..first_n],&mword[..bits],None,dirty);
            b.play(&r,false);
        } else {
            priority_probe(b,mword,helper,None,(1..m).rev().map(|l|(l,q[l],vec![vec![]])).collect(),dirty);
        }
        // carry(~M + Y) is exactly Y>M. Both addends are restored.
        for &v in mword{b.x(v);}
        super::super::arith::ttk_carry_u(b,mword,y,helper,d);
        for &v in mword{b.x(v);}
        for i in 0..7{b.cswap(helper,mword[i],y[i]);}
        // Put Q[M] on Q0. Strict greater order is now !Q0, so helper clears.
        let rot=record(b,|b|super::rot_by_range(b,q,mword,mlo-1,mhi-1,false,&bank(dirty,mword)));
        b.play(&rot,true);b.x(helper);b.cx(q[0],helper);
        // Q smaller: rotated highest index = Y-M+q.len(). All mod128.
        let translate=record(b,|b|{
            b.x(q[0]);
            let add=record(b,|b|super::super::arith::ttk_add(b,mword,y,Some(q[0]),None));
            b.play(&add,true);
            let held:Vec<_>=y.iter().copied().chain([q[0]]).collect();
            super::super::modp_frogdrop::add_const_exact(b,y,Some(q[0]),(q.len()%128)as u64,&bank(dirty,&held));
            b.x(q[0]);
        });
        b.play(&translate,false);
        let qprobe=record(b,|b|{
            if q.len()==128 && binary_admitted(128,
                old_probe_price((q.len()-m+1..q.len()).rev(),true),true) {
                // Q0 is folded by the probe and cannot remain its live
                // control. The original found helper is zero here.
                b.x(helper);b.cx(q[0],helper); // immutable enable=!Q0
                let r=super::binary_msb::record(b,q,y,Some((helper,false)),dirty);
                b.play(&r,false);
                b.cx(q[0],helper);b.x(helper);
            } else {
                priority_probe(b,y,helper,Some((q[0],true)),
                    (q.len()-m+1..q.len()).rev().map(|l|(l,q[l],vec![vec![]])).collect(),dirty);
            }
        });
        b.play(&qprobe,true);
        let rprobe=record(b,|b|{
            let mut lanes=Vec::new();
            for lane in (1..mhi).rev(){
                let mut cuts=Vec::new();
                if lane<mlo{cuts.push(vec![]);}else{
                    cubes(7,lane,128,|at,free|cuts.push((free..7)
                        .map(|i|(mword[i],at>>i&1==0)).collect()));
                }
                lanes.push((lane,ring[ring.len()-1-lane],cuts));
            }
            priority_probe(b,y,helper,Some((q[0],false)),lanes,dirty);
        });
        b.play(&rprobe,true);b.play(&rot,false);
    })
}

pub(crate) struct Core{
    pub mword:Vec<QubitId>,pub ez:Vec<QubitId>,pub t:QubitId,pub e:QubitId,pub g:QubitId,
    pub source_bound:usize,pub dirty:Vec<QubitId>,
    // Only stages() reads this option: rotations and shifts, never frame rows.
    native_nand:Option<(QubitId,QubitId)>,
    row_recode:bool, row_external:Vec<QubitId>,
}
impl Core{
    fn check(&self,ring:&[QubitId],q:&[QubitId]){
        assert_eq!(self.mword.len(),7);assert_eq!(self.ez.len(),5);
        assert!((2..=q.len()).contains(&self.source_bound) && q.len()<=128);
        let p:Vec<_>=ring.iter().chain(q).chain(&self.mword).chain(&self.ez).copied()
            .chain([self.t,self.e,self.g]).collect();unique(&p);
        assert!(self.dirty.len()>=p.len()); // no-P universe contains these existing owners
    }
    fn eq(&self,b:&mut B,size:usize,out:QubitId,pre:&[QubitId]){
        if !(1..=128).contains(&size){return;}
        let c:Vec<_>=self.mword.iter().enumerate().map(|(i,&q)|(q,(size-1)>>i&1==0)).collect();
        xor(b,&c,out,pre,&self.dirty);
    }
    fn ge(&self,b:&mut B,size:usize,out:QubitId,pre:&[QubitId]){
        if size==0{b.x(out);}else if size<=128{
            range(b,&self.mword,size-1,128,&[],out,pre,&self.dirty);
        }
    }
    fn walk(&self,b:&mut B,n:usize,lo:usize,hi:usize,pre:&[QubitId],
            mut body:impl FnMut(&mut B,usize,QubitId)){
        if lo>=hi{return;}b.x(self.e);self.ge(b,n-lo,self.e,pre);
        for lane in lo..hi {if lane>lo{self.eq(b,n-lane,self.e,pre);}body(b,lane,self.e);}
        b.x(self.e);self.ge(b,n-hi+1,self.e,pre);
    }
    fn stages(&self,b:&mut B,flag:(QubitId,bool),reverse:bool,
              mut body:impl FnMut(&mut B,usize,QubitId)){
        let order:Vec<_>=if reverse{(0..5).rev().collect()}else{(0..5).collect()};
        for k in order{let c=[flag,(self.ez[k],false)];
            let toggle=|b:&mut B|{
                xor(b,&c,self.g,&[],&self.dirty);
                if let Some((ph,done_tag))=self.native_nand {
                    let mut off=c.to_vec();off.extend([(ph,false),(done_tag,false)]);
                    xor(b,&off,self.g,&[],&self.dirty);
                }
            };
            toggle(b);body(b,k,self.g);toggle(b);}
    }
    fn widen(&self,b:&mut B,flag:(QubitId,bool))->Vec<G>{
        record(b,|b|{if flag.1{b.x(flag.0);}
            let add=record(b,|b|super::super::arith::ttk_add(b,
                &self.ez.iter().copied().chain([self.e,self.g]).collect::<Vec<_>>(),
                &self.mword,Some(flag.0),None));
            b.play(&add,true);if flag.1{b.x(flag.0);}
        })
    }
    fn ring_rot(&self,b:&mut B,ring:&[QubitId],flag:(QubitId,bool),up:bool){
        let r=record(b,|b|self.stages(b,flag,false,|b,k,g|super::crot_up(b,g,ring,1usize<<k)));
        b.play(&r,!up);
    }
    fn q_rot(&self,b:&mut B,q:&[QubitId],flag:(QubitId,bool),down:bool){
        let mut support:BTreeSet<_>=(0..self.source_bound).collect();
        let r=record(b,|b|self.stages(b,flag,false,|b,k,g|{
            let step=(1usize<<k)%q.len();super::crot_up_care(b,g,q,step,&support);
            let more:Vec<_>=support.iter().map(|i|(i+step)%q.len()).collect();support.extend(more);
        }));b.play(&r,down);
    }
    fn shift(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,flag:(QubitId,bool),up:bool){
        self.stages(b,flag,up,|b,k,g|{let step=1usize<<k;if step>=hi{return;}
            let r=record(b,|b|{
                for lane in step..lo.max(step){b.cswap(g,ring[lane],ring[lane-step]);}
                self.walk(b,ring.len(),lo.max(step),hi,&[],|b,lane,e|{
                    let(a,z)=(ring[lane],ring[lane-step]);
                    b.cx(a,z);xor(b,&[(g,false),(e,false),(z,false)],a,&[],&self.dirty);b.cx(a,z);
                });
            });b.play(&r,up);
        });
    }
    fn pminus(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,tail:usize,flag:(QubitId,bool)){
        assert!(lo>42+tail && hi<=ring.len());if flag.1{b.x(flag.0);}
        for &v in &ring[..lo.min(256)]{b.cx(flag.0,v);}
        self.walk(b,ring.len(),lo,hi.min(256),&[self.g],|b,lane,e|b.ccx(flag.0,e,ring[lane]));
        for (target,k) in [(&ring[..10+tail],976u64),(&ring[32..33+tail],1u64)]{
            let held:Vec<_>=target.iter().copied().chain([flag.0]).collect();
            let r=record(b,|b|super::super::modp_frogdrop::add_const_exact(b,target,Some(flag.0),k,&bank(&self.dirty,&held)));
            b.play(&r,true);
        }
        if flag.1{b.x(flag.0);}
    }
    /// Same affine cut walk as walk(), with no clean prefix and with
    /// the held G control excluded even from restored dirty donors.
    fn native_walk(&self,b:&mut B,n:usize,lo:usize,hi:usize,dirty:&[QubitId],
        mut body:impl FnMut(&mut B,usize,QubitId)){
        assert!(!dirty.contains(&self.g));
        if lo>=hi{return;}
        let ge=|b:&mut B,size:usize|{
            if size==0{b.x(self.e);}else if size<=128{
                range(b,&self.mword,size-1,128,&[],self.e,&[],dirty);
            }
        };
        b.x(self.e);ge(b,n-lo);
        for lane in lo..hi{
            if lane>lo{let size=n-lane;
                if (1..=128).contains(&size){
                    let ctl:Vec<_>=self.mword.iter().enumerate()
                        .map(|(i,&q)|(q,(size-1)>>i&1==0)).collect();
                    xor(b,&ctl,self.e,&[],dirty);
                }
            }
            body(b,lane,self.e);
        }
        b.x(self.e);ge(b,n-hi+1);
    }
    /// Original complete pminus under one returned G=flag*NAND(PH,C).
    /// No amount/carry span is shortened. E starts and returns zero for
    /// all M codes, while the constant tails keep their literal controls.
    fn native_pminus(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,tail:usize,flag:(QubitId,bool)){
        let(ph,c)=self.native_nand.expect("native pminus requires immutable NAND ports");
        assert!(lo>42+tail&&hi<=ring.len());
        let toggle=|b:&mut B|{
            xor(b,&[flag],self.g,&[],&self.dirty);
            xor(b,&[flag,(ph,false),(c,false)],self.g,&[],&self.dirty);
        };
        let dirty=bank(&self.dirty,&[self.g]);
        toggle(b);
        for &v in &ring[..lo.min(256)]{b.cx(self.g,v);}
        self.native_walk(b,ring.len(),lo,hi.min(256),&dirty,
            |b,lane,e|b.ccx(self.g,e,ring[lane]));
        for(target,k)in[(&ring[..10+tail],976u64),(&ring[32..33+tail],1u64)]{
            let held:Vec<_>=target.iter().copied().chain([self.g]).collect();
            let r=record(b,|b|super::super::modp_frogdrop::add_const_exact(
                b,target,Some(self.g),k,&bank(&dirty,&held)));
            b.play(&r,true);
        }
        toggle(b);
    }
    /// Original masked_swapf under G=NAND(PH,C). The cut is unchanged:
    /// E=1 means lane is BELOW 257-M, so the variable swap uses !E.
    /// The three-control central X is literal dirty4T, not clean-G AND.
    fn native_masked_swap(&self,b:&mut B,ring:&[QubitId],q:&[QubitId],clo:usize,chi:usize){
        let(ph,c)=self.native_nand.expect("native swap requires immutable NAND ports");
        let n=ring.len();let qlo=n.saturating_sub(q.len());
        let dirty=bank(&self.dirty,&[self.g]);
        b.x(self.g);b.ccx(ph,c,self.g);
        for l in chi.max(qlo)..n{b.cswap(self.g,ring[l],q[n-1-l]);}
        let lo=clo.max(qlo);
        self.native_walk(b,n,lo,chi,&dirty,|b,l,e|{
            let(a,z)=(ring[l],q[n-1-l]);
            b.cx(a,z);
            xor(b,&[(self.g,false),(e,true),(z,false)],a,&[],&dirty);
            b.cx(a,z);
        });
        b.ccx(ph,c,self.g);b.x(self.g);
    }
    fn frame(&self,b:&mut B,ring:&[QubitId],q:&[QubitId],par:&super::MapPar,inverse:bool){
        let n=ring.len();let(llo,lhi)=(n-par.chi,n-par.clo);
        assert!(0<llo && llo<=lhi && lhi<n && self.source_bound<=par.m && par.m<=128);
        let plan=if self.row_recode && b.allow_booth && !b.no_rows && !b.force_unitary_and {
            super::direct_map_rows::choose(n,llo,lhi,par.m,self.source_bound,
                par.tail,q.len(),self.row_external.len())
        }else{None};
        let r=record(b,|b|{
            let rot=record(b,|b|super::rot_by_range(b,ring,&self.mword,llo-1,lhi-1,false,&bank(&self.dirty,&self.mword)));
            b.play(&rot,false);let v:Vec<_>=(0..n).map(|i|ring[(i+n-1)%n]).collect();
            let mut begun=false;let remaining=plan.map_or(n-1,|p|p.start);
            if let Some(plan)=plan{
                begun=super::direct_map_rows::emit(b,&v,q,self.source_bound,lhi,plan,
                    self.e,self.g,&self.row_external,&self.dirty,
                    |b,value|self.eq(b,value,self.e,&[self.g]));
            }
            for i in (llo..remaining).rev(){
                let lo=i+1;let nm=(par.m-1).min(n-lo);let nt=par.tail.min(n-lo-nm);
                let width=nm.min(self.source_bound-1);let tw=nm+nt-width;let variable=i<lhi;
                if variable{
                    if !begun{b.x(self.e);begun=true;}self.eq(b,lo,self.e,&[self.g]);
                    b.and_c(v[i],self.e,self.g);b.x(self.e);
                }
                let enable=if variable{self.g}else{v[i]};
                // E is zero whenever enable=1. Off enable its arbitrary
                // carry cancels through the exact MAJ/restore pair.
                let mut cleanbank=q[self.source_bound..].to_vec();if !variable{cleanbank.push(self.g);}
                cleanbank.extend(&self.row_external);
                let na=if tw==0{0}else{tw.min(cleanbank.len())};
                let clean=&cleanbank[..na];let nc=width.min(cleanbank.len()-na);let andc=&cleanbank[na..na+nc];
                let held:Vec<_>=v[lo..lo+nm+nt].iter().chain(&q[1..1+width])
                    .chain(clean).chain(andc).copied().chain([enable,self.e]).collect();
                let row_dirty=bank(&self.dirty,&held);
                let need=if tw<=1{0}else if na==0{tw+2}else{tw-na+2};
                assert!(row_dirty.len()>=need,"no-P restored row donors");
                super::joint_tail::cadd_tail_no_h(b,enable,&v[lo..lo+width],&q[1..1+width],
                    &v[lo+width..lo+nm+nt],self.e,clean,&row_dirty,andc);
                if variable{b.x(self.e);b.and_u(v[i],self.e,self.g);}
            }
            if begun{self.eq(b,llo,self.e,&[self.g]);}b.play(&rot,true);
        });
        super::pair_control::capture_frame(&r,inverse);b.play(&r,inverse);
    }
}
/// Complete parent's TZ map operation, with literal primitive semantics.
/// q is either full physical Q128 or a proved counter-free prefix. In the
/// latter case source_bound<=q.len(); par.m still keeps the original target envelope.
/// Every advertised source suffix q[source_bound..] is zero on enabled shots.
/// A DN wrapper must use literal paired-frame replay, not clean execution of
/// U on off-DONE shots with arbitrary counter passengers in those suffixes.
pub(crate) fn map_tz(b:&mut B,ring:&[QubitId],q:&[QubitId],par:&super::MapPar,sc:&Core){
    sc.check(ring,q);let n=ring.len();assert_eq!(n,257);
    assert!(par.emax<=31 && par.emax<q.len());let(lo,hi)=(par.clo,par.chi);
    let hi2=(hi+par.emax).min(n-1);let wide=super::MapPar{clo:lo,chi:hi2,m:par.m,tail:par.tail,emax:par.emax};
    let rev:Vec<_>=ring.iter().rev().copied().collect();
    let probe=record(b,|b|{
        let held:Vec<_>=q[..par.emax+1].iter().chain(&sc.ez).copied().chain([sc.g,sc.e]).collect();
        super::tz_probe(b,&q[..par.emax+1],&sc.ez,par.emax,&[sc.g],sc.e,&bank(&sc.dirty,&held));
        let held:Vec<_>=rev[..par.emax+1].iter().chain(&sc.ez).copied().chain([sc.g,sc.e,q[0]]).collect();
        super::tz_probe_gated(b,&rev[..par.emax+1],&sc.ez,par.emax,&[sc.g],sc.e,&bank(&sc.dirty,&held),&[(q[0],false)]);
    });b.play(&probe,false);b.x(q[0]);b.cx(q[0],sc.t);b.x(q[0]);
    let(y,x)=((sc.t,true),(sc.t,false));let wy=sc.widen(b,y);let wx=sc.widen(b,x);
    sc.ring_rot(b,ring,y,true);b.play(&wy,false);sc.shift(b,ring,lo,hi2,y,false);sc.q_rot(b,q,x,true);
    sc.frame(b,ring,q,&wide,false);sc.q_rot(b,q,x,false);sc.pminus(b,ring,lo,hi2,par.tail,y);
    b.play(&wy,true);sc.ring_rot(b,ring,y,false);
    let cut=super::Cut{v:sc.mword.clone(),a:n as isize-1,neg:true};
    let held:Vec<_>=sc.mword.iter().copied().chain([sc.e,sc.g]).collect();
    super::masked_swapf(b,ring,q,&cut,lo,hi,sc.e,&[],sc.g,&bank(&sc.dirty,&held));
    sc.ring_rot(b,ring,x,true);b.play(&wx,false);sc.pminus(b,ring,lo,hi2,par.tail,x);
    sc.q_rot(b,q,y,true);sc.frame(b,ring,q,&wide,true);sc.q_rot(b,q,y,false);
    sc.shift(b,ring,lo,hi2,x,true);b.play(&wx,true);sc.ring_rot(b,ring,x,false);
    b.x(ring[n-1]);b.cx(ring[n-1],sc.t);b.x(ring[n-1]);b.play(&probe,true);
}

/// Uncontrolled stage tape. `scratch[0]` is the retained C=W|D passenger,
/// never read/written here. PH likewise remains outside the stage/donor bank.
/// The caller registers frame captures before recording this tape and replays
/// it either plainly or through exact paired NAND2(PH,C) control.
#[allow(clippy::too_many_arguments)]
pub(crate) fn stage_record(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],
    scratch:&[QubitId],ph:QubitId,par:&super::MapPar,source_bound:usize,
    dirty:&[QubitId])->Vec<G>{
    stage_record_rows(b,ring,q,y,scratch,ph,par,source_bound,dirty,false,&[])
}
fn stage_record_rows(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],
    scratch:&[QubitId],ph:QubitId,par:&super::MapPar,source_bound:usize,
    dirty:&[QubitId],row_recode:bool,row_external:&[QubitId])->Vec<G>{
    assert!(row_external.is_empty()||row_external.len()==2);
    assert_eq!(scratch.len(),9);assert_eq!(y.len(),7);
    let p:Vec<_>=ring.iter().chain(q).chain(y).chain(scratch).copied().chain([ph]).collect();
    unique(&p);assert!(row_external.iter().all(|v|!p.contains(v)));unique(row_external);
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=ring.iter().chain(q).chain(y).chain(&scratch[1..]).chain(dirty).copied()
        .filter(|v|![scratch[0],ph].contains(v)&&seen.insert(*v)).collect();
    let core=Core{mword:scratch[1..8].to_vec(),ez:y[..5].to_vec(),t:y[5],e:y[6],
        g:scratch[8],source_bound,dirty:bank,native_nand:None,row_recode,row_external:row_external.to_vec()};
    record(b,|b|{
        let en=entry_record(b,ring,q,y,&core.mword,core.g,source_bound,
            ring.len()-par.chi,ring.len()-par.clo,&core.dirty);
        b.play(&en,false);map_tz(b,ring,q,par,&core);b.play(&en,true);
    })
}

/// Exact literal extension used by the existing paired-frame replay.
/// No deferred rows or measured cleanup survive in the unconditional frame.
fn literal(record:&[G])->Vec<G>{
    record.iter().map(|&g|match g{
        G::AndC(a,c,t)|G::AndU(a,c,t)=>G::Ccx(a,c,t),
        G::X(_)|G::Cx(_,_)|G::Ccx(_,_,_)|G::Swap(_,_)=>g,
        _=>panic!("native map requires a complete literal record"),
    }).collect()
}

/// Full NAND control on every literal, with two restored local donors.
/// Unlike pair_control replay this deliberately lifts NO entry/probe shell.
fn nand_literal(b:&mut B,r:&[G],inverse:bool,ph:QubitId,c:QubitId,universe:&[QubitId]){
    let gates=literal(r);
    for j in 0..gates.len(){let g=gates[if inverse{gates.len()-1-j}else{j}];
        let mut held=vec![ph,c];
        match g{
            G::X(t)=>held.push(t),
            G::Cx(a,t)|G::Swap(a,t)=>held.extend([a,t]),
            G::Ccx(a,d,t)=>held.extend([a,d,t]),
            _=>unreachable!(),
        }
        assert!(held[2..].iter().all(|q|*q!=ph&&*q!=c));
        let work=bank(universe,&held);assert!(work.len()>=2);
        b.play_ctrl_nand2(&[g],ph,c,work[0],work[1]);
    }
}

/// On D=PH&C exchange arbitrary inactive E7 with the zero M7 bank.
/// Active entry already has E7=0. Thus both classes leave all core E/T/ez
/// cells zero and an arbitrary valid M code, with G returned globally zero.
fn inactive_metadata_swap(b:&mut B,y:&[QubitId],m:&[QubitId],g:QubitId,ph:QubitId,c:QubitId){
    assert_eq!((y.len(),m.len()),(7,7));
    b.ccx(ph,c,g);for i in 0..7{b.cswap(g,y[i],m[i]);}b.ccx(ph,c,g);
}

/// Native control only for full-width mixed maps. M is a complete 7-bit
/// code (logical1..128), so the frame's E walk closes even on arbitrary
/// inactive ring/Q data. All lasting changes except stage-gated rotations
/// and shifts remain under exact literal NAND control.
fn native_stage(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],
    scratch:&[QubitId],ph:QubitId,par:&super::MapPar,source_bound:usize,universe:&[QubitId]){
    let n=ring.len();let c=scratch[0];
    assert_eq!((n,q.len(),source_bound,par.m),(257,128,128,128));
    assert_eq!((n-par.chi,n-par.clo),(1,128));
    assert!(par.emax<=31);
    let core=Core{mword:scratch[1..8].to_vec(),ez:y[..5].to_vec(),t:y[5],e:y[6],
        g:scratch[8],source_bound,dirty:universe.to_vec(),native_nand:Some((ph,c)),row_recode:false,row_external:vec![]};
    core.check(ring,q);
    assert!(core.dirty.iter().all(|q|*q!=ph&&*q!=c));
    let (lo,hi)=(par.clo,par.chi);let hi2=(hi+par.emax).min(n-1);
    let wide=super::MapPar{clo:lo,chi:hi2,m:par.m,tail:par.tail,emax:par.emax};
    assert_eq!((n-wide.chi,n-wide.clo),(1,128));
    let en=super::direct_map_entry_native::record(b,ring,q,y,&core.mword,core.g,ph,c,&core.dirty);
    b.play(&en,false);
    inactive_metadata_swap(b,y,&core.mword,core.g,ph,c);
    let rev:Vec<_>=ring.iter().rev().copied().collect();
    let probe=record(b,|b|{
        let held:Vec<_>=q[..par.emax+1].iter().chain(&core.ez).copied().chain([core.g,core.e]).collect();
        super::tz_probe(b,&q[..par.emax+1],&core.ez,par.emax,&[core.g],core.e,&bank(&core.dirty,&held));
        let held:Vec<_>=rev[..par.emax+1].iter().chain(&core.ez).copied().chain([core.g,core.e,q[0]]).collect();
        super::tz_probe_gated(b,&rev[..par.emax+1],&core.ez,par.emax,&[core.g],core.e,
            &bank(&core.dirty,&held),&[(q[0],false)]);
    });
    nand_literal(b,&probe,false,ph,c,universe);
    let t_in=record(b,|b|{b.x(q[0]);b.cx(q[0],core.t);b.x(q[0]);});
    nand_literal(b,&t_in,false,ph,c,universe);
    let (yf,xf)=((core.t,true),(core.t,false));
    let wy=core.widen(b,yf);let wx=core.widen(b,xf);
    // Capture one exact complete frame, then replay the same literal tape
    // in both directions. capture_frame is inert: no pair capture is open.
    let frame=record(b,|b|core.frame(b,ring,q,&wide,false));
    let u=literal(&frame);
    core.ring_rot(b,ring,yf,true);nand_literal(b,&wy,false,ph,c,universe);
    core.shift(b,ring,lo,hi2,yf,false);core.q_rot(b,q,xf,true);
    b.play(&u,false);
    core.q_rot(b,q,xf,false);
    core.native_pminus(b,ring,lo,hi2,par.tail,yf);
    nand_literal(b,&wy,true,ph,c,universe);core.ring_rot(b,ring,yf,false);
    core.native_masked_swap(b,ring,q,lo,hi);
    core.ring_rot(b,ring,xf,true);nand_literal(b,&wx,false,ph,c,universe);
    core.native_pminus(b,ring,lo,hi2,par.tail,xf);
    core.q_rot(b,q,yf,true);b.play(&u,true);core.q_rot(b,q,yf,false);
    core.shift(b,ring,lo,hi2,xf,true);nand_literal(b,&wx,true,ph,c,universe);
    core.ring_rot(b,ring,xf,false);
    let t_out=record(b,|b|{b.x(ring[n-1]);b.cx(ring[n-1],core.t);b.x(ring[n-1]);});
    nand_literal(b,&t_out,false,ph,c,universe);
    nand_literal(b,&probe,true,ph,c,universe);
    inactive_metadata_swap(b,y,&core.mword,core.g,ph,c);
    b.play(&en,true);
}

/// Fresh stage preparation and replay; this is a source prototype, not wired
/// to is_map_ctrl/MAP_CTRL_S. The intended policy is DN && source_bound>121.
/// With the qualified public table it selects columns97..119, including the
/// five former plain partial-counter maps. All later maps use raw Q[..121].
/// `toggle_done` is the inherited PH & Q[RA..121)==0 & cnt!=0 predicate.
/// It returns every helper, excludes C/PH from its restored donor list, and
/// must give the same D before/after the selected full map.
#[allow(clippy::too_many_arguments)]
pub(crate) fn apply_stage(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],
    scratch:&[QubitId],ph:QubitId,par:&super::MapPar,source_bound:usize,
    dn:bool,pure_ht:bool,dirty:&[QubitId],
    toggle_done:impl FnMut(&mut B,QubitId,&[QubitId])){
    apply_stage_with_loans(b,ring,q,y,scratch,ph,par,source_bound,dn,pure_ht,dirty,&[],toggle_done)
}
/// Extra ports are the existing globally clean T2/T3 terminal P0/P1 only.
/// Controlled frames deliberately receive neither recoding nor these loans.
#[allow(clippy::too_many_arguments)]
pub(crate) fn apply_stage_with_loans(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],
    scratch:&[QubitId],ph:QubitId,par:&super::MapPar,source_bound:usize,
    dn:bool,pure_ht:bool,dirty:&[QubitId],clean_external:&[QubitId],
    mut toggle_done:impl FnMut(&mut B,QubitId,&[QubitId])){
    assert!(clean_external.is_empty()||clean_external.len()==2);
    assert_eq!(q.len(),128);assert_eq!(scratch.len(),9);let c=scratch[0];
    let controlled=dn && source_bound>121;let qend=if dn&&!controlled{121}else{128};
    let occupied:Vec<_>=ring.iter().chain(q).chain(y).chain(scratch).copied().chain([ph]).collect();
    unique(&occupied);let mut seen=BTreeSet::new();
    let all:Vec<_>=ring.iter().chain(q).chain(y).chain(&scratch[1..]).chain(dirty).copied()
        .filter(|v|![c,ph].contains(v)&&seen.insert(*v)).collect();
    // This structural selector is exactly mixed public columns97..113 in
    // the pinned203-column schedule. Narrow/pure-HT maps retain old replay.
    if controlled && !pure_ht && source_bound==128 && par.m==128
        && ring.len()-par.chi==1 && ring.len()-par.clo==128 {
        assert_eq!((ring.len(),qend),(257,128));
        let done_bank=bank(&all,q);
        toggle_done(b,c,&done_bank);
        native_stage(b,ring,q,y,scratch,ph,par,source_bound,&all);
        toggle_done(b,c,&done_bank);
        return;
    }
    let old_simple=b.cancel_simple_pairs;let old_commuting=b.cancel_commuting_pairs;
    if controlled{
        // Preserve exact frame/shell occurrences for the paired source plan.
        b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        super::pair_control::begin([c,ph]);
    }
    let r=stage_record_rows(b,ring,&q[..qend],y,scratch,ph,par,source_bound,&all,
        !controlled,if controlled{&[]}else{clean_external});
    b.cancel_simple_pairs=old_simple;b.cancel_commuting_pairs=old_commuting;
    if !controlled{b.play(&r,false);return;}
    super::pair_control::finish(std::collections::BTreeMap::new());
    let done_bank=bank(&all,q); // inherited predicate reads PH/Q; only returned non-Q donors
    toggle_done(b,c,&done_bank);
    if pure_ht{
        // Public PH=1 and C=0 before D-toggle. PH is a clean helper only
        // during this complete controlled replay, and is returned first.
        b.x(c);b.x(ph);super::pair_control::play_ctrl_full(b,&r,c,ph);b.x(ph);b.x(c);
    }else{
        // C=>!PH before D-toggle, while DONE=>PH&&!C. Thus PH&(C^D)=D.
        super::pair_control::play_ctrl_nand2_local(b,&r,ph,c,&all);
    }
    toggle_done(b,c,&done_bank);
}
