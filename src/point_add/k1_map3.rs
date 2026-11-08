//! Complete K1 sibling construction. Production/default dispatch is parent.
//! No traversal allocation or K6 raw entry implementation lives here.
use super::*;
use super::super::super::k1_pad_add::{self as pad,Enable,Literal,Exclusions};
#[path="k1_entry3.rs"] mod entry;

#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
pub(crate) enum Diagnostic { #[default] Parent, ThreeRole }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Error { Shape,Alias,HeldPort,Selector,EarlyCancellation,FrameRecipe,Capacity,Boundary,Loan,Unsupported }
pub(crate) fn require(ok:bool,error:Error) {if !ok {std::panic::panic_any(error);}}
fn capture_ready(b:&B) {
    require(!b.cancel_simple_pairs&&!b.cancel_commuting_pairs&&!b.global_cancel,Error::EarlyCancellation);
    require(!b.force_unitary_and&&!b.no_rows,Error::FrameRecipe);
}
fn lit(b:&mut B,c:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]) {
    require(!c.iter().any(|x|x.0==target),Error::Alias);
    let held:Vec<_>=c.iter().map(|x|x.0).chain([target]).collect();
    let d=bank(dirty,&held);require(d.len()>=c.len().saturating_sub(2),Error::Capacity);
    mc_xor(b,c,target,&[],&d);
}
fn active(b:&mut B,c:&[(QubitId,bool)],target:QubitId,nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    lit(b,c,target,dirty);
    if let Some((ph,tag))=nand {
        #[cfg(test)] if complete_adapter::omits(complete_adapter::Fault::OuterControl){return;}
        let mut off=c.to_vec();off.extend([(ph,false),(tag,false)]);
        #[cfg(test)] let mark=b.recording_len();
        lit(b,&off,target,dirty);
        #[cfg(test)] if complete_adapter::enabled(){complete_adapter::tag("active-off",&b.k1_current_since(mark),&[]);}
    }
}
fn swap(b:&mut B,c:&[(QubitId,bool)],a:QubitId,z:QubitId,nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    b.cx(a,z);let mut ctl=c.to_vec();ctl.push((z,false));active(b,&ctl,a,nand,dirty);b.cx(a,z);
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Mode { HostedZero,Plain,Native,PureHt,HostedOne }
pub(crate) fn mode(column:usize)->Mode {
    match column {0..=35=>Mode::HostedZero,36..=96=>Mode::Plain,97..=113=>Mode::Native,
        114..=119=>Mode::PureHt,120..=202=>Mode::HostedOne,_=>{require(false,Error::Selector);unreachable!()}}
}
pub(crate) fn source_column(cp:&super::super::super::frogdrop_col::ColPar) {
    let schedule=super::super::super::frogdrop_sched::from_text(super::super::super::pointadd_frogdrop::SCHED_FROGDROP);
    let(columns,_,_)=super::super::super::pointadd_frogdrop::col_pars(&schedule);
    require(cp.col<columns.len()&&format!("{cp:?}")==format!("{:?}",columns[cp.col]),Error::Selector);
}
/// K6 must supply this only after through_stage10, both controller coordinates
/// and every raw payload epoch have closed. It grants no additional clean lane.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Boundary { Stage10Returned, EndpointDoneBeforeB0, ControllerOpen, PayloadOpen }
#[derive(Clone,Copy,Debug)]
pub(crate) struct Roles3 {pub tag:QubitId,pub cut:QubitId,pub toggle:QubitId}
pub(crate) struct Context<'a> {
    pub ring:&'a[QubitId],pub q:&'a[QubitId],pub y:&'a[QubitId],pub sum:&'a[QubitId],
    pub roles:Roles3,pub ph:QubitId,pub payload:Option<&'a[QubitId]>,
    pub terminal_loans:&'a[QubitId],pub boundary:Boundary,
}
impl Context<'_> {
    pub(crate) fn scratch(&self)->Vec<QubitId> {
        // Retain the old eight-position logical ABI; the evicted position is
        // a sentinel, never a physical scratch lane or emitted operand.
        let toggle=if super::super::super::c659::drop_enabled()&&self.payload.is_some(){crate::circuit::NO_QUBIT}else{self.roles.toggle};
        std::iter::once(self.roles.tag).chain(self.sum.iter().copied())
            .chain([self.roles.cut,toggle]).collect()}
    pub(crate) fn validate(&self) {
        require(self.boundary==Boundary::Stage10Returned,Error::Boundary);
        self.validate_ports();
    }
    pub(crate) fn validate_endpoint(&self) {
        require(self.boundary==Boundary::EndpointDoneBeforeB0,Error::Boundary);
        self.validate_ports();
    }
    fn validate_ports(&self) {
        require((self.ring.len(),self.q.len(),self.y.len(),self.sum.len())==(257,128,7,5),Error::Shape);
        require(if self.payload.is_some(){self.terminal_loans.is_empty()}else{self.terminal_loans.len()==2||super::super::super::c659::t23_enabled()&&self.terminal_loans.len()==1},Error::Loan);
        if let Some(p)=self.payload {require(p.len()==258,Error::Shape);}
        let ports:Vec<_>=self.ring.iter().chain(self.q).chain(self.y).chain(self.sum).copied()
            .chain([self.roles.tag,self.roles.cut,self.roles.toggle,self.ph]).filter(|q|super::super::super::c659::retained(*q))
            .chain(self.payload.into_iter().flatten().copied()).chain(self.terminal_loans.iter().copied()).collect();
        require(ports.iter().copied().collect::<BTreeSet<_>>().len()==ports.len(),Error::Alias);
    }
    pub(crate) fn donors(&self)->Vec<QubitId> {
        // Explicit universe: no ambient dirty bank and no fourth role exists.
        self.ring.iter().chain(self.q).chain(self.y).chain(self.sum).copied()
            .chain([self.roles.cut]).chain((self.payload.is_none()||
                !super::super::super::direct_map_tail_counter::wp5_enabled())
                .then_some(self.roles.toggle)).collect()
    }
}

#[derive(Clone)]
struct Core3 {
    m:Vec<QubitId>,ez:Vec<QubitId>,t:QubitId,e:QubitId,source:usize,
    dirty:Vec<QubitId>,held:Vec<QubitId>,nand:Option<(QubitId,QubitId)>,
}
fn m6host(core:&Core3,host:QubitId,flag:QubitId)->Core3 {
    let mut c=core.clone();c.m[6]=host;c.t=flag;c
}
fn host_x(b:&mut B,t:QubitId,nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    if nand.is_some(){active(b,&[],t,nand,dirty);}else{b.x(t);}
}
fn host_cx(b:&mut B,c:QubitId,t:QubitId,nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    if nand.is_some(){active(b,&[(c,false)],t,nand,dirty);}else{b.cx(c,t);}
}
fn host_swap(b:&mut B,a:QubitId,z:QubitId,nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    if nand.is_some(){swap(b,&[],a,z,nand,dirty);}else{b.swap(a,z);}
}
fn flip_not(b:&mut B,c:QubitId,t:QubitId,nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]){
    host_x(b,t,nand,dirty);host_cx(b,c,t,nand,dirty);
}
fn flip_or_zero(b:&mut B,c:QubitId,t:QubitId,ez:&[QubitId],nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    host_cx(b,c,t,nand,dirty);
    let mut ctl=vec![(c,true)];ctl.extend(ez.iter().map(|&q|(q,true)));active(b,&ctl,t,nand,dirty);
}
fn flip_not_or_zero(b:&mut B,c:QubitId,t:QubitId,ez:&[QubitId],nand:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    flip_not(b,c,t,nand,dirty);
    let mut ctl=vec![(c,false)];ctl.extend(ez.iter().map(|&q|(q,true)));active(b,&ctl,t,nand,dirty);
}
impl Core3 {
    fn eq(&self,b:&mut B,value:usize) {
        let c:Vec<_>=self.m.iter().enumerate().map(|(j,&q)|(q,value>>j&1==0)).collect();
        lit(b,&c,self.e,&self.dirty);
    }
    fn ge(&self,b:&mut B,size:usize) {
        if size==0 {b.x(self.e);}else if size<=128 {range(b,&self.m,size-1,128,&[],self.e,&[],&self.dirty);}
    }
    fn walk(&self,b:&mut B,n:usize,lo:usize,hi:usize,mut body:impl FnMut(&mut B,usize,QubitId)) {
        if lo>=hi {return;}b.x(self.e);self.ge(b,n-lo);
        for lane in lo..hi {
            if lane>lo {let size=n-lane;if (1..=128).contains(&size) {self.eq(b,size-1);}}
            body(b,lane,self.e);
        }
        b.x(self.e);self.ge(b,n-hi+1);
    }
    fn add_padding(&self,b:&mut B,ring:&[QubitId],source:&[QubitId],target:&[QubitId],
        enable:Enable,controls:&[QubitId])->Vec<G> {
        require(target.len()>=source.len(),Error::Shape);let h=target.len()-source.len();
        let pool:Vec<_>=ring.iter().copied().filter(|q|!source.contains(q)&&!target.contains(q)&&!controls.contains(q)).collect();
        let nd=enable.donors_needed();require(pool.len()>=h+nd,Error::Capacity);
        let padding=&pool[..h];let donors=&pool[h..h+nd];
        let held:Vec<_>=self.held.iter().chain(&self.m).chain(&self.ez).copied().chain([self.t,self.e])
            .filter(|q|!source.contains(q)&&!target.contains(q)&&!padding.contains(q)&&!donors.contains(q)&&!controls.contains(q)).collect();
        let row=pad::pad_add_f(b,source,target,padding,&enable,donors,Exclusions{held:&held,forbidden:&[]})
            .expect("qualified PAD_ADD caller contract");
        #[cfg(test)]
        complete_adapter::pad_tag(&row,source,target,padding,donors,controls);
        row
    }
    fn widen(&self,b:&mut B,ring:&[QubitId],flag:(QubitId,bool))->Vec<G> {
        let signed=Literal{wire:flag.0,positive:true};
        let(enable,controls)=match self.nand {
            None=>(Enable::Literals(vec![signed]),vec![flag.0]),
            Some((ph,c))=>(Enable::Native{flag:signed,ph,c},vec![flag.0,ph,c]),
        };
        let add=self.add_padding(b,ring,&self.ez,&self.m,enable,&controls);
        record(b,|b|{if flag.1{b.x(flag.0);}b.play(&add,true);if flag.1{b.x(flag.0);}})
    }
    fn stages(&self,b:&mut B,flag:(QubitId,bool),mut body:impl FnMut(&mut B,usize,QubitId)) {
        for k in 0..5 {
            let controls=[flag,(self.ez[k],false)];
            active(b,&controls,self.e,self.nand,&self.dirty);body(b,k,self.e);
            active(b,&controls,self.e,self.nand,&self.dirty);
        }
    }
    fn ring_rot(&self,b:&mut B,ring:&[QubitId],flag:(QubitId,bool),up:bool) {
        let r=record(b,|b|self.stages(b,flag,|b,k,e|super::super::crot_up(b,e,ring,1usize<<k)));
        b.play(&r,!up);
    }
    fn q_rot(&self,b:&mut B,q:&[QubitId],flag:(QubitId,bool),down:bool) {
        let mut support:BTreeSet<_>=(0..self.source).collect();
        let r=record(b,|b|self.stages(b,flag,|b,k,e|{
            let step=(1usize<<k)%q.len();super::super::crot_up_care(b,e,q,step,&support);
            let more:Vec<_>=support.iter().map(|i|(i+step)%q.len()).collect();support.extend(more);
        }));b.play(&r,down);
    }
    fn shift(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,flag:(QubitId,bool),up:bool) {
        let order:Vec<_>=if up{(0..5).rev().collect()}else{(0..5).collect()};
        for k in order {
            let step=1usize<<k;if step>=hi {continue;}
            let r=record(b,|b|{
                for lane in step..lo.max(step) {swap(b,&[flag,(self.ez[k],false)],ring[lane],ring[lane-step],self.nand,&self.dirty);}
                self.walk(b,ring.len(),lo.max(step),hi,|b,lane,e|{
                    swap(b,&[flag,(self.ez[k],false),(e,false)],ring[lane],ring[lane-step],self.nand,&self.dirty);
                });
            });b.play(&r,up);
        }
    }
    fn pminus(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,tail:usize,flag:(QubitId,bool)) {
        require(lo>42+tail&&hi<=ring.len(),Error::Shape);
        if flag.1 {b.x(flag.0);}
        for &q in &ring[..lo.min(256)] {active(b,&[(flag.0,false)],q,self.nand,&self.dirty);}
        self.walk(b,ring.len(),lo,hi.min(256),|b,lane,e|active(b,&[(flag.0,false),(e,false)],ring[lane],self.nand,&self.dirty));
        for(target,k)in[(&ring[..10+tail],976u64),(&ring[32..33+tail],1u64)] {
            let held:Vec<_>=target.iter().copied().chain([flag.0]).collect();
            let r=record(b,|b|super::super::super::modp_frogdrop::add_const_exact(b,target,Some(flag.0),k,&bank(&self.dirty,&held)));
            if let Some((ph,c))=self.nand {nand_literal(b,&r,true,ph,c,&self.dirty);}else{b.play(&r,true);}
        }
        if flag.1 {b.x(flag.0);}
    }
    fn masked_swap(&self,b:&mut B,ring:&[QubitId],q:&[QubitId],lo:usize,hi:usize) {
        let n=ring.len();let qlo=n.saturating_sub(q.len());
        for l in hi.max(qlo)..n {swap(b,&[],ring[l],q[n-1-l],self.nand,&self.dirty);}
        self.walk(b,n,lo.max(qlo),hi,|b,l,e|swap(b,&[(e,true)],ring[l],q[n-1-l],self.nand,&self.dirty));
    }
    /// Generalized sibling of qualified c119 ordinary rows. Same physical
    /// rotation, descending widths, ring-order padding and exact E walk.
    fn frame(&self,b:&mut B,ring:&[QubitId],q:&[QubitId],par:&super::super::MapPar)->Vec<G> {
        let(llo,lhi)=(257-par.chi,257-par.clo);
        require(0<llo&&llo<=lhi&&lhi<257&&self.source<=par.m&&par.m<=128,Error::Shape);
        let rot=record(b,|b|super::super::rot_by_range(b,ring,&self.m,llo-1,lhi-1,false,&bank(&self.dirty,&self.m)));
        let v:Vec<_>=(0..257).map(|i|ring[(i+256)%257]).collect();
        record(b,|b|{
            b.play(&rot,false);let mut begun=false;
            for i in (llo..256).rev() {
                let nm=(par.m-1).min(256-i);let n=nm.min(self.source-1);
                let h=nm+par.tail.min(256-i-nm)-n;let variable=i<lhi;
                if variable {if !begun {b.x(self.e);begun=true;}self.eq(b,i);}
                let controls=if variable{vec![self.e,v[i]]}else{vec![v[i]]};
                let target=&v[i+1..i+1+n+h];
                let pool=ring.iter().filter(|q|!target.contains(q)&&!controls.contains(q)).count();
                require(pool>=h+usize::from(variable)+42,Error::Capacity);
                let enable=Enable::Literals(controls.iter().map(|&wire|Literal{wire,positive:true}).collect());
                let row=self.add_padding(b,ring,&q[1..1+n],target,enable,&controls);b.play(&row,false);
            }
            if begun {self.eq(b,llo-1);}b.play(&rot,true);
        })
    }
}

struct Captured {tape:Vec<G>,frame:Vec<G>,first:usize,second:usize}
fn pure(g:&G)->bool {matches!(g,G::X(..)|G::Cx(..)|G::Ccx(..)|G::Swap(..))}
fn ports(g:&G)->Vec<QubitId> {
    match *g {G::X(a)=>vec![a],G::Cx(a,z)|G::Swap(a,z)=>vec![a,z],G::Ccx(a,c,z)=>vec![a,c,z],
        _=>{require(false,Error::FrameRecipe);unreachable!()}}
}
fn body(b:&mut B,ctx:&Context<'_>,par:&super::super::MapPar,core:&Core3)->Captured {
    let(ring,q)=(ctx.ring,ctx.q);require(par.emax==31,Error::Selector);
    let(lo,hi)=(par.clo,par.chi);let hi2=(hi+par.emax).min(256);
    let wide=super::super::MapPar{clo:lo,chi:hi2,m:par.m,tail:par.tail,emax:par.emax};
    let rev:Vec<_>=ring.iter().rev().copied().collect();
    let probe=record(b,|b|{
        let held:Vec<_>=q[..32].iter().chain(&core.ez).copied().chain([core.e]).collect();
        trailing_probe(b,&q[..32],&core.ez,31,&[],core.e,&bank(&core.dirty,&held),None);
        let held:Vec<_>=rev[..32].iter().chain(&core.ez).copied().chain([core.e,q[0]]).collect();
        trailing_probe(b,&rev[..32],&core.ez,31,&[],core.e,&bank(&core.dirty,&held),Some((q[0],false)));
    });
    let play_active=|b:&mut B,r:&[G],inv:bool|if let Some((ph,c))=core.nand {
        nand_literal(b,r,inv,ph,c,&core.dirty);
    }else{b.play(r,inv);};
    let wy=core.widen(b,ring,(core.t,true));let wx=core.widen(b,ring,(core.t,false));
    let frame=core.frame(b,ring,q,&wide);
    #[cfg(test)]
    complete_adapter::tag("frame",&frame,&[]);
    require(!frame.is_empty()&&frame.iter().all(pure),Error::FrameRecipe);
    require(frame.iter().flat_map(ports).all(|q|!core.held.contains(&q)),Error::HeldPort);
    // One literal recipe is deliberately used for both occurrences. Positions
    // are captured in this fresh tape only, before any cancellation.
    #[cfg(test)]
    complete_adapter::tag("probe",&probe,&[]);
    b.begin();super::super::super::r13prof::mm(b,61);play_active(b,&probe,false);
    let t_in=record(b,|b|{b.x(q[0]);b.cx(q[0],core.t);b.x(q[0]);});play_active(b,&t_in,false);super::super::super::r13prof::mm(b,61);
    let(y,x)=((core.t,true),(core.t,false));
    super::super::super::r13prof::mm(b,63);core.ring_rot(b,ring,y,true);super::super::super::r13prof::mm(b,63);super::super::super::r13prof::mm(b,62);b.play(&wy,false);super::super::super::r13prof::mm(b,62);super::super::super::r13prof::mm(b,64);core.shift(b,ring,lo,hi2,y,false);super::super::super::r13prof::mm(b,64);super::super::super::r13prof::mm(b,65);core.q_rot(b,q,x,true);super::super::super::r13prof::mm(b,65);
    super::super::super::r13prof::mm(b,66);let first=b.recording_len();b.play(&frame,false);super::super::super::r13prof::mm(b,66);
    super::super::super::r13prof::mm(b,65);core.q_rot(b,q,x,false);super::super::super::r13prof::mm(b,65);super::super::super::r13prof::mm(b,67);core.pminus(b,ring,lo,hi2,par.tail,y);super::super::super::r13prof::mm(b,67);
    super::super::super::r13prof::mm(b,62);b.play(&wy,true);super::super::super::r13prof::mm(b,62);super::super::super::r13prof::mm(b,63);core.ring_rot(b,ring,y,false);super::super::super::r13prof::mm(b,63);super::super::super::r13prof::mm(b,68);core.masked_swap(b,ring,q,lo,hi);super::super::super::r13prof::mm(b,68);
    super::super::super::r13prof::mm(b,63);core.ring_rot(b,ring,x,true);super::super::super::r13prof::mm(b,63);super::super::super::r13prof::mm(b,62);b.play(&wx,false);super::super::super::r13prof::mm(b,62);super::super::super::r13prof::mm(b,67);core.pminus(b,ring,lo,hi2,par.tail,x);super::super::super::r13prof::mm(b,67);
    super::super::super::r13prof::mm(b,65);core.q_rot(b,q,y,true);super::super::super::r13prof::mm(b,65);super::super::super::r13prof::mm(b,66);let second=b.recording_len();b.play(&frame,true);super::super::super::r13prof::mm(b,66);super::super::super::r13prof::mm(b,65);core.q_rot(b,q,y,false);super::super::super::r13prof::mm(b,65);
    super::super::super::r13prof::mm(b,64);core.shift(b,ring,lo,hi2,x,true);super::super::super::r13prof::mm(b,64);super::super::super::r13prof::mm(b,62);b.play(&wx,true);super::super::super::r13prof::mm(b,62);super::super::super::r13prof::mm(b,63);core.ring_rot(b,ring,x,false);super::super::super::r13prof::mm(b,63);
    let t_out=record(b,|b|{b.x(ring[256]);b.cx(ring[256],core.t);b.x(ring[256]);});
    #[cfg(test)] complete_adapter::tag("tout",&t_out,&[]);
    
    #[cfg(test)] if !complete_adapter::omits(complete_adapter::Fault::TErase){play_active(b,&t_out,false);}
    #[cfg(not(test))] {super::super::super::r13prof::mm(b,61);play_active(b,&t_out,false);}
    
    #[cfg(test)] if !complete_adapter::omits(complete_adapter::Fault::ProbeReturn){play_active(b,&probe,true);}
    #[cfg(not(test))] {play_active(b,&probe,true);super::super::super::r13prof::mm(b,61);}let tape=b.end();
    require(tape[first..first+frame.len()]==frame,Error::FrameRecipe);
    require(tape[second..second+frame.len()].iter().eq(frame.iter().rev()),Error::FrameRecipe);
    Captured{tape,frame,first,second}
}

// M6 migrates among three returned physical hosts. Native gates each
// transition by NAND(PH,tag), while its frame pair remains raw.
// The transitions use the inherited coprime and trailing-zero map contract.
fn body_m6host(b:&mut B,ctx:&Context<'_>,par:&super::super::MapPar,core:&Core3)->Captured {
    let(ring,q)=(ctx.ring,ctx.q);let(q0,r256,y5)=(q[0],ring[256],ctx.y[5]);
    require(par.emax==31,Error::Selector);
    let(lo,hi)=(par.clo,par.chi);let hi2=(hi+par.emax).min(256);
    let wide=super::super::MapPar{clo:lo,chi:hi2,m:par.m,tail:par.tail,emax:par.emax};
    let early=m6host(core,y5,q0);let rotate=m6host(core,r256,y5);let row=m6host(core,q0,y5);
    let rev:Vec<_>=ring.iter().rev().copied().collect();
    let probe=record(b,|b|{
        let held:Vec<_>=q[..32].iter().chain(&core.ez).copied().chain([core.e]).collect();
        trailing_probe(b,&q[..32],&core.ez,31,&[],core.e,&bank(&core.dirty,&held),None);
        let held:Vec<_>=rev[..32].iter().chain(&core.ez).copied().chain([core.e,q0]).collect();
        trailing_probe(b,&rev[..32],&core.ez,31,&[],core.e,&bank(&core.dirty,&held),Some((q0,false)));
    });
    let wy=early.widen(b,ring,(q0,false));let wx=rotate.widen(b,ring,(y5,false));
    let frame=row.frame(b,ring,q,&wide);
    #[cfg(test)] {complete_adapter::tag("frame",&frame,&[]);complete_adapter::tag("probe",&probe,&[]);}
    require(!frame.is_empty()&&frame.iter().all(pure),Error::FrameRecipe);
    require(frame.iter().flat_map(ports).all(|q|!core.held.contains(&q)),Error::HeldPort);
    let play_active=|b:&mut B,r:&[G],inv:bool|if let Some((ph,c))=core.nand {
        nand_literal(b,r,inv,ph,c,&core.dirty);
    }else{b.play(r,inv);};
    let nd=core.nand;let dd=&core.dirty;
    b.begin();super::super::super::r13prof::mm(b,61);play_active(b,&probe,false);super::super::super::r13prof::mm(b,61);
    // 1-5: t is represented by !q0, and y5 carries M6.
    super::super::super::r13prof::mm(b,63);early.ring_rot(b,ring,(q0,false),true);super::super::super::r13prof::mm(b,63);
    super::super::super::r13prof::mm(b,62);b.play(&wy,false);super::super::super::r13prof::mm(b,62);
    super::super::super::r13prof::mm(b,64);early.shift(b,ring,lo,hi2,(q0,false),false);super::super::super::r13prof::mm(b,64);
    host_x(b,r256,nd,dd);host_swap(b,y5,r256,nd,dd);flip_not(b,q0,y5,nd,dd);
    super::super::super::r13prof::mm(b,65);rotate.q_rot(b,q,(y5,false),true);super::super::super::r13prof::mm(b,65);
    host_x(b,q0,nd,dd);host_swap(b,r256,q0,nd,dd);host_x(b,r256,nd,dd);
    super::super::super::r13prof::mm(b,66);let first=b.recording_len();b.play(&frame,false);super::super::super::r13prof::mm(b,66);
    host_x(b,r256,nd,dd);host_swap(b,q0,r256,nd,dd);host_x(b,q0,nd,dd);
    super::super::super::r13prof::mm(b,65);rotate.q_rot(b,q,(y5,false),false);super::super::super::r13prof::mm(b,65);
    flip_not(b,q0,y5,nd,dd);host_swap(b,r256,y5,nd,dd);host_x(b,r256,nd,dd);
    super::super::super::r13prof::mm(b,67);early.pminus(b,ring,lo,hi2,par.tail,(q0,false));super::super::super::r13prof::mm(b,67);
    super::super::super::r13prof::mm(b,62);b.play(&wy,true);super::super::super::r13prof::mm(b,62);
    super::super::super::r13prof::mm(b,63);early.ring_rot(b,ring,(q0,false),false);super::super::super::r13prof::mm(b,63);
    super::super::super::r13prof::mm(b,68);early.masked_swap(b,ring,q,lo,hi);super::super::super::r13prof::mm(b,68);
    flip_not_or_zero(b,r256,q0,&core.ez,nd,dd);host_swap(b,y5,q0,nd,dd);flip_not(b,r256,y5,nd,dd);
    super::super::super::r13prof::mm(b,63);row.ring_rot(b,ring,(y5,false),true);super::super::super::r13prof::mm(b,63);
    host_x(b,r256,nd,dd);host_swap(b,q0,r256,nd,dd);flip_or_zero(b,y5,q0,&core.ez,nd,dd);
    super::super::super::r13prof::mm(b,62);b.play(&wx,false);super::super::super::r13prof::mm(b,62);
    super::super::super::r13prof::mm(b,67);rotate.pminus(b,ring,lo,hi2,par.tail,(y5,false));super::super::super::r13prof::mm(b,67);
    super::super::super::r13prof::mm(b,65);rotate.q_rot(b,q,(y5,true),true);super::super::super::r13prof::mm(b,65);
    host_x(b,q0,nd,dd);host_swap(b,r256,q0,nd,dd);host_x(b,r256,nd,dd);
    super::super::super::r13prof::mm(b,66);let second=b.recording_len();b.play(&frame,true);super::super::super::r13prof::mm(b,66);
    host_x(b,r256,nd,dd);host_swap(b,q0,r256,nd,dd);host_x(b,q0,nd,dd);
    super::super::super::r13prof::mm(b,65);rotate.q_rot(b,q,(y5,true),false);super::super::super::r13prof::mm(b,65);
    super::super::super::r13prof::mm(b,64);rotate.shift(b,ring,lo,hi2,(y5,false),true);super::super::super::r13prof::mm(b,64);
    super::super::super::r13prof::mm(b,62);b.play(&wx,true);super::super::super::r13prof::mm(b,62);
    flip_or_zero(b,y5,q0,&core.ez,nd,dd);host_swap(b,r256,q0,nd,dd);host_x(b,r256,nd,dd);
    super::super::super::r13prof::mm(b,63);row.ring_rot(b,ring,(y5,false),false);super::super::super::r13prof::mm(b,63);
    flip_not(b,r256,y5,nd,dd);host_swap(b,q0,y5,nd,dd);flip_not_or_zero(b,r256,q0,&core.ez,nd,dd);
    #[cfg(test)] if !complete_adapter::omits(complete_adapter::Fault::ProbeReturn){play_active(b,&probe,true);}
    #[cfg(not(test))] play_active(b,&probe,true);
    let tape=b.end();
    require(tape[first..first+frame.len()]==frame,Error::FrameRecipe);
    require(tape[second..second+frame.len()].iter().eq(frame.iter().rev()),Error::FrameRecipe);
    Captured{tape,frame,first,second}
}
fn metadata_swap(b:&mut B,y:&[QubitId],m:&[QubitId],ph:QubitId,c:QubitId,dirty:&[QubitId]) {
    #[cfg(test)] let mark=b.recording_len();
    for i in 0..7 {swap(b,&[(ph,false),(c,false)],y[i],m[i],None,dirty);}
    #[cfg(test)] if complete_adapter::enabled(){complete_adapter::tag("dswap",&b.k1_current_since(mark),&[]);}
}
fn mswap_dm6(b:&mut B,ctx:&Context<'_>,m:&[QubitId],dirty:&[QubitId]) {
    require(m.len()==6&&!dirty.contains(&ctx.roles.toggle),Error::HeldPort);
    #[cfg(test)] let mark=b.recording_len();
    let ctl=[(ctx.ph,false),(ctx.roles.tag,false)];
    for i in 0..6 {swap(b,&ctl,ctx.y[i],m[i],None,dirty);}
    swap(b,&ctl,ctx.y[6],ctx.q[64],None,dirty);
    #[cfg(test)] if complete_adapter::enabled(){complete_adapter::tag("dswap",&b.k1_current_since(mark),&[]);}
}
fn stage(b:&mut B,ctx:&Context<'_>,par:&super::super::MapPar,source:usize,native:bool)->Captured {
    let scratch=ctx.scratch();let m=&scratch[1..];let dirty=ctx.donors();
    let held:Vec<_>=std::iter::once(ctx.ph).chain([ctx.roles.tag]).chain(ctx.terminal_loans.iter().copied())
        .chain(ctx.payload.into_iter().flatten().copied()).collect();
    let nand=native.then_some((ctx.ph,ctx.roles.tag));
    let core=Core3{m:m.to_vec(),ez:ctx.y[..5].to_vec(),t:ctx.y[5],e:ctx.y[6],source,dirty,held,nand};
    if native {require((source,par.m,257-par.chi,257-par.clo)==(128,128,1,128),Error::Selector);}
    let en=entry::entry(b,ctx.ring,ctx.q,ctx.y,m,nand,&core.dirty);
    b.begin();super::super::super::r13prof::mm(b,60);b.play(&en,false);super::super::super::r13prof::mm(b,60);
    if native {super::super::super::r13prof::mm(b,69);metadata_swap(b,ctx.y,m,ctx.ph,ctx.roles.tag,&core.dirty);super::super::super::r13prof::mm(b,69);}
    let middle=body(b,ctx,par,&core);let offset=b.recording_len();b.play(&middle.tape,false);
    #[cfg(test)]
    if native&&!complete_adapter::omits(complete_adapter::Fault::DReturn) {metadata_swap(b,ctx.y,m,ctx.ph,ctx.roles.tag,&core.dirty);}
    #[cfg(not(test))]
    if native {super::super::super::r13prof::mm(b,69);metadata_swap(b,ctx.y,m,ctx.ph,ctx.roles.tag,&core.dirty);super::super::super::r13prof::mm(b,69);}
    super::super::super::r13prof::mm(b,60);b.play(&en,true);super::super::super::r13prof::mm(b,60);let tape=b.end();
    Captured{tape,frame:middle.frame,first:offset+middle.first,second:offset+middle.second}
}

// On the public pure-HT columns PH is one.  The surrounding PureHt arm
// complements it to zero, so it can hold M6 during the controlled tape.
fn stage_m6ph(b:&mut B,ctx:&Context<'_>,par:&super::super::MapPar,source:usize)->Captured {
    let mut m=ctx.sum.to_vec();m.extend([ctx.roles.cut,ctx.ph]);
    let dirty:Vec<_>=ctx.donors().into_iter().filter(|q|*q!=ctx.roles.toggle).collect();
    let held:Vec<_>=std::iter::once(ctx.roles.tag).chain(ctx.payload.into_iter().flatten().copied()).collect();
    let core=Core3{m:m.clone(),ez:ctx.y[..5].to_vec(),t:ctx.y[5],e:ctx.y[6],source,dirty,held,nand:None};
    let en=entry::entry(b,ctx.ring,ctx.q,ctx.y,&m,None,&core.dirty);
    b.begin();super::super::super::r13prof::mm(b,60);b.play(&en,false);super::super::super::r13prof::mm(b,60);
    let middle=body(b,ctx,par,&core);let offset=b.recording_len();b.play(&middle.tape,false);
    super::super::super::r13prof::mm(b,60);b.play(&en,true);super::super::super::r13prof::mm(b,60);let tape=b.end();
    Captured{tape,frame:middle.frame,first:offset+middle.first,second:offset+middle.second}
}

fn stage_m6plain(b:&mut B,ctx:&Context<'_>,par:&super::super::MapPar,source:usize)->Captured {
    let mut m=ctx.sum.to_vec();m.extend([ctx.roles.cut,ctx.roles.tag]);
    let dirty:Vec<_>=ctx.donors().into_iter().filter(|q|*q!=ctx.roles.toggle).collect();
    let held:Vec<_>=std::iter::once(ctx.ph).chain([ctx.roles.tag]).chain(ctx.payload.into_iter().flatten().copied()).collect();
    let core=Core3{m:m.clone(),ez:ctx.y[..5].to_vec(),t:ctx.y[5],e:ctx.y[6],source,dirty,held,nand:None};
    let en=entry::entry_m6fold(b,ctx.ring,ctx.q,ctx.y,&m,&core.dirty);
    b.begin();super::super::super::r13prof::mm(b,60);b.play(&en,false);super::super::super::r13prof::mm(b,60);
    let middle=body_m6host(b,ctx,par,&core);let offset=b.recording_len();b.play(&middle.tape,false);
    super::super::super::r13prof::mm(b,60);b.play(&en,true);super::super::super::r13prof::mm(b,60);let tape=b.end();
    Captured{tape,frame:middle.frame,first:offset+middle.first,second:offset+middle.second}
}
fn stage_m6plain_v(b:&mut B,ctx:&Context<'_>,par:&super::super::MapPar,source:usize)->Captured {
    let mut m=ctx.sum.to_vec();m.push(ctx.roles.cut);
    let dirty=ctx.donors();
    require(!dirty.contains(&ctx.roles.toggle),Error::HeldPort);
    let held:Vec<_>=std::iter::once(ctx.ph).chain([ctx.roles.tag,ctx.roles.toggle]).filter(|q|super::super::super::c659::retained(*q))
        .chain(ctx.payload.into_iter().flatten().copied()).collect();
    let mut mb=m.clone();mb.push(ctx.y[5]);
    let core=Core3{m:mb,ez:ctx.y[..5].to_vec(),t:ctx.y[5],e:ctx.y[6],source,dirty,held,nand:None};
    let (en_a,en_b)=entry::entry_v(b,ctx.ring,ctx.q,ctx.y,&m,None,&core.dirty);
    let en:Vec<G>=en_a.into_iter().chain(en_b).collect();
    b.begin();super::super::super::r13prof::mm(b,60);b.play(&en,false);super::super::super::r13prof::mm(b,60);
    let middle=body_m6host(b,ctx,par,&core);let offset=b.recording_len();b.play(&middle.tape,false);
    super::super::super::r13prof::mm(b,60);b.play(&en,true);super::super::super::r13prof::mm(b,60);
    let tape=b.end();Captured{tape,frame:middle.frame,first:offset+middle.first,second:offset+middle.second}
}
fn stage_m6native_ql4(b:&mut B,ctx:&Context<'_>,par:&super::super::MapPar,source:usize)->Captured {
    require((source,par.m,257-par.chi,257-par.clo)==(128,128,1,128),Error::Selector);
    let mut m=ctx.sum.to_vec();m.push(ctx.roles.cut);
    let dirty=ctx.donors();require(!dirty.contains(&ctx.roles.toggle),Error::HeldPort);
    let held:Vec<_>=[ctx.ph,ctx.roles.tag,ctx.roles.toggle].into_iter().filter(|q|super::super::super::c659::retained(*q))
        .chain(ctx.payload.into_iter().flatten().copied()).collect();
    let mut mb=m.clone();mb.push(ctx.y[5]);
    let core=Core3{m:mb,ez:ctx.y[..5].to_vec(),t:ctx.y[5],e:ctx.y[6],source,dirty,held,
        nand:Some((ctx.ph,ctx.roles.tag))};
    let en=entry::entry_ql4(b,ctx.ring,ctx.q,ctx.y,&m,core.nand,&core.dirty);
    b.begin();super::super::super::r13prof::mm(b,60);b.play(&en,false);super::super::super::r13prof::mm(b,60);
    super::super::super::r13prof::mm(b,69);mswap_dm6(b,ctx,&m,&core.dirty);super::super::super::r13prof::mm(b,69);
    let middle=body_m6host(b,ctx,par,&core);let offset=b.recording_len();b.play(&middle.tape,false);
    #[cfg(test)] if !complete_adapter::omits(complete_adapter::Fault::DReturn){mswap_dm6(b,ctx,&m,&core.dirty);}
    #[cfg(not(test))] {super::super::super::r13prof::mm(b,69);mswap_dm6(b,ctx,&m,&core.dirty);super::super::super::r13prof::mm(b,69);}
    super::super::super::r13prof::mm(b,60);b.play(&en,true);super::super::super::r13prof::mm(b,60);
    let tape=b.end();Captured{tape,frame:middle.frame,first:offset+middle.first,second:offset+middle.second}
}
#[cfg(test)]
pub(crate) fn diagnostic_plain(b:&mut B,ctx:&Context<'_>,cp:&super::super::super::frogdrop_col::ColPar,
    new:bool,entry_only:bool) {
    let par=super::super::MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,m:cp.m,tail:cp.tail,emax:cp.emax};
    if entry_only {
        let m=if new{let mut v=ctx.sum.to_vec();v.extend([ctx.roles.cut,ctx.roles.tag]);v}else{ctx.scratch()[1..].to_vec()};
        let dirty:Vec<_>=ctx.donors().into_iter().filter(|q|!new||*q!=ctx.roles.toggle).collect();
        let r=if new{entry::entry_m6fold(b,ctx.ring,ctx.q,ctx.y,&m,&dirty)}
            else{entry::entry(b,ctx.ring,ctx.q,ctx.y,&m,None,&dirty)};
        b.play(&r,false);
    }else{
        let r=if new{stage_m6plain(b,ctx,&par,cp.m)}else{stage(b,ctx,&par,cp.m,false)};
        b.play(&r.tape,false);
    }
}
#[cfg(test)]
pub(crate) fn diagnostic_v(b:&mut B,ctx:&Context<'_>,cp:&super::super::super::frogdrop_col::ColPar,
    new:bool,entry_only:bool) {
    let par=super::super::MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,m:cp.m,tail:cp.tail,emax:cp.emax};
    if entry_only {
        let dirty=ctx.donors();
        let r=if new {
            let mut m=ctx.sum.to_vec();m.push(ctx.roles.cut);
            let (a,z)=entry::entry_v(b,ctx.ring,ctx.q,ctx.y,&m,None,&dirty);
            a.into_iter().chain(z).collect()
        }else{entry::entry(b,ctx.ring,ctx.q,ctx.y,&ctx.scratch()[1..],None,&dirty)};
        b.play(&r,false);
    }else{
        let r=if new{stage_m6plain_v(b,ctx,&par,cp.m)}else{stage(b,ctx,&par,cp.m,false)};
        b.play(&r.tape,false);
    }
}
#[cfg(test)]
pub(crate) fn diagnostic_add_carry(b:&mut B,a:&[QubitId],t:&[QubitId],z:QubitId,
    nand:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G>{
    entry::diagnostic_add_carry(b,a,t,z,nand,dirty)
}
#[cfg(test)]
pub(crate) fn diagnostic_ql4(b:&mut B,ctx:&Context<'_>,cp:&super::super::super::frogdrop_col::ColPar,
    new:bool,entry_only:bool) {
    let par=super::super::MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,m:128,tail:cp.tail,emax:cp.emax};
    if entry_only{
        let r=if new{
            let mut m=ctx.sum.to_vec();m.push(ctx.roles.cut);
            entry::entry_ql4(b,ctx.ring,ctx.q,ctx.y,&m,Some((ctx.ph,ctx.roles.tag)),&ctx.donors())
        }else{entry::entry(b,ctx.ring,ctx.q,ctx.y,&ctx.scratch()[1..],
            Some((ctx.ph,ctx.roles.tag)),&ctx.donors())};
        b.play(&r,false);
    }else{
        let r=if new{stage_m6native_ql4(b,ctx,&par,cp.m)}else{stage(b,ctx,&par,cp.m,true)};
        b.play(&r.tape,false);
    }
}
fn play_ctrl_per_gate_dirty(b:&mut B,tape:&[G],c:QubitId,ring:&[QubitId]) {
    for &g in tape {
        match g {
            G::X(t)=>b.cx(c,t),
            G::Cx(a,t)=>b.ccx(c,a,t),
            G::Ccx(a,z,t)|G::AndC(a,z,t)|G::AndU(a,z,t)=>{
                let w=*ring.iter().find(|&&w|w!=a&&w!=z&&w!=t&&w!=c).expect("dirty replay helper");
                b.ccx(z,w,t);b.ccx(c,a,w);b.ccx(z,w,t);b.ccx(c,a,w);
            },
            G::Swap(a,z)=>b.cswap(c,a,z),
            _=>{require(false,Error::FrameRecipe);unreachable!()},
        }
    }
}

fn paired_dirty(b:&mut B,r:&Captured,c:QubitId,ring:&[QubitId]) {
    capture_ready(b);
    require(r.tape.iter().all(pure)&&r.tape.iter().flat_map(ports).all(|q|q!=c),Error::HeldPort);
    let n=r.frame.len();require(n>0&&r.first+n<=r.second&&r.second+n<=r.tape.len(),Error::FrameRecipe);
    require(r.tape[r.first..r.first+n]==r.frame,Error::FrameRecipe);
    require(r.tape[r.second..r.second+n].iter().eq(r.frame.iter().rev()),Error::FrameRecipe);
    play_ctrl_per_gate_dirty(b,&r.tape[..r.first],c,ring);b.play(&r.frame,false);
    #[cfg(test)] let mark=b.recording_len();
    #[cfg(test)] {if complete_adapter::omits(complete_adapter::Fault::OuterControl){b.play(&r.tape[r.first+n..r.second],false);}
    else {play_ctrl_per_gate_dirty(b,&r.tape[r.first+n..r.second],c,ring);}}
    #[cfg(not(test))] play_ctrl_per_gate_dirty(b,&r.tape[r.first+n..r.second],c,ring);
    #[cfg(test)] if complete_adapter::enabled(){complete_adapter::tag("controlled-middle",&b.k1_current_since(mark),&[]);}
    b.play(&r.frame,true);
    play_ctrl_per_gate_dirty(b,&r.tape[r.second+n..],c,ring);
}

fn paired_clean(b:&mut B,r:&Captured,c:QubitId,ph:QubitId) {
    capture_ready(b);require(c!=ph,Error::Alias);
    require(r.tape.iter().all(pure)&&r.tape.iter().flat_map(ports).all(|q|q!=c&&q!=ph),Error::HeldPort);
    let n=r.frame.len();require(n>0&&r.first+n<=r.second&&r.second+n<=r.tape.len(),Error::FrameRecipe);
    require(r.tape[r.first..r.first+n]==r.frame,Error::FrameRecipe);
    require(r.tape[r.second..r.second+n].iter().eq(r.frame.iter().rev()),Error::FrameRecipe);
    let ccx=r.frame.iter().filter(|g|matches!(g,G::Ccx(..))).count();
    let cx=r.frame.iter().filter(|g|matches!(g,G::Cx(..)|G::Swap(..))).count();
    require(2*ccx<4*ccx+2*cx,Error::FrameRecipe);
    b.play_ctrl_full(&r.tape[..r.first],c,ph);b.play(&r.frame,false);
    #[cfg(test)] let mark=b.recording_len();
    #[cfg(test)]
    if complete_adapter::omits(complete_adapter::Fault::OuterControl){b.play(&r.tape[r.first+n..r.second],false);}
    else {b.play_ctrl_full(&r.tape[r.first+n..r.second],c,ph);}
    #[cfg(not(test))]
    b.play_ctrl_full(&r.tape[r.first+n..r.second],c,ph);
    #[cfg(test)] if complete_adapter::enabled(){complete_adapter::tag("controlled-middle",&b.k1_current_since(mark),&[]);}
    b.play(&r.frame,true);
    b.play_ctrl_full(&r.tape[r.second+n..],c,ph);
}

/// Hosted parent body, with no second independent PH metadata argument.
/// Core methods, entry, row recoding and all map operations remain inherited.
pub(crate) fn hosted_record(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],
    scratch:&[QubitId],host:QubitId,par:&super::super::MapPar,source:usize,
    dirty:&[QubitId],row_recode:bool,row_external:&[QubitId])->Vec<G> {
    require(scratch.len()==8&&y.len()==7,Error::Shape);
    let p:Vec<_>=ring.iter().chain(q).chain(y).chain(scratch).copied().chain([host]).chain(row_external.iter().copied()).filter(|q|super::super::super::c659::retained(*q)).collect();
    require(p.iter().copied().collect::<BTreeSet<_>>().len()==p.len(),Error::Alias);
    let mut seen=BTreeSet::new();
    let universe:Vec<_>=ring.iter().chain(q).chain(y).chain(&scratch[1..]).chain(dirty).copied()
        .filter(|q|*q!=scratch[0]&&*q!=host&&seen.insert(*q)).collect();
    let core=Core{mword:scratch[1..].to_vec(),ez:y[..5].to_vec(),t:y[5],e:y[6],g:host,
        source_bound:source,dirty:universe,native_nand:None,row_recode,row_external:row_external.to_vec(),
        walk_clean:if row_recode{q[source..].iter().chain(row_external).copied().collect()}else{vec![]}};
    require(2<=source&&source<=q.len()&&q.len()<=128,Error::Shape);
    record(b,|b|{
        let en=entry_record(b,ring,q,y,&core.mword,host,source,ring.len()-par.chi,ring.len()-par.clo,&core.dirty,row_recode);
        super::super::super::r13prof::mm(b,60);b.play(&en,false);super::super::super::r13prof::mm(b,60);super::k1_hosted_map_body(b,ring,q,par,&core);super::super::super::r13prof::mm(b,60);b.play(&en,true);super::super::super::r13prof::mm(b,60);
    })
}

/// Diagnostic S11 map only. Source metadata determines the complete mode;
/// external caller owns DONE and must pass the unchanged parity predicate.
pub(crate) fn apply(b:&mut B,ctx:&Context<'_>,cp:&super::super::super::frogdrop_col::ColPar,
    mut done:impl FnMut(&mut B,QubitId,&[QubitId])) {
    ctx.validate();capture_ready(b);
    source_column(cp);
    require(cp.col<=202&&!cp.nomap&&cp.sz!=(0,0)&&cp.n==257&&cp.nq==128,Error::Selector);
    let selected=mode(cp.col);let pure_ht=cp.ht&&!cp.hr&&!cp.sw&&!cp.dl&&!cp.dq;
    let controlled=cp.dn&&cp.m>121;
    require(controlled==matches!(selected,Mode::Native|Mode::PureHt),Error::Selector);
    require(!controlled||pure_ht==matches!(selected,Mode::PureHt),Error::Selector);
    let par=super::super::MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,m:if cp.dn{128}else{cp.m},tail:cp.tail,emax:cp.emax};
    let dirty=ctx.donors();let scratch=ctx.scratch();
    let old_ok=super::super::super::r13prof::set_map_ok(selected!=Mode::PureHt);
    let _restore=Restore(old_ok);
    match selected {
        Mode::HostedZero|Mode::HostedOne=>{
            let late=selected==Mode::HostedOne;
            require(if late{pure_ht&&cp.dn&&cp.m<=121}else{cp.hr&&!cp.ht&&!cp.dn},Error::Selector);
            // M6 is a returned zero padding lane, selected before the map.
            // The prefix ends before the host, including at the two boundaries
            // where Q127/Q120 would otherwise be a walk_clean donor.
            let wp5=ctx.payload.is_some()&&super::super::super::direct_map_tail_counter::wp5_enabled();
            let host_idx=if cp.col<=159{127}else{120};
            let qend=if wp5&&cp.col<=34{127}else if wp5&&cp.col>=160{120}else if cp.dn{121}else{128};
            require(!wp5||cp.m<=qend,Error::Shape);
            let mut hosted_scratch=scratch.clone();
            if wp5 {
                if cp.col==35 {
                    hosted_scratch[0]=if super::super::super::c659::drop_enabled(){crate::circuit::NO_QUBIT}else{ctx.roles.toggle}; // returned, never an operand
                    hosted_scratch[7]=ctx.roles.tag; // C=0 by no-sw/no-dl source boundary
                }else{hosted_scratch[7]=ctx.q[host_idx];}
            }
            let hosted_dirty:Vec<_>=dirty.iter().copied().filter(|q|!wp5||*q!=ctx.roles.toggle).collect();
            let row_external=if super::super::super::c659::t23_enabled()&&ctx.payload.is_none(){&[][..]}else{ctx.terminal_loans};
            let r=hosted_record(b,ctx.ring,&ctx.q[..qend],ctx.y,&hosted_scratch,ctx.ph,&par,cp.m,&hosted_dirty,true,row_external);
            if late {b.x(ctx.ph);}b.play(&r,false);if late {b.x(ctx.ph);}
        },
        Mode::Plain=>{require(!controlled,Error::Selector);
            if super::super::super::c659::t23_enabled()&&ctx.payload.is_none(){
                let r=hosted_record(b,ctx.ring,ctx.q,ctx.y,&scratch,ctx.terminal_loans[0],&par,cp.m,&dirty,true,&[]);
                b.play(&r,false);
            }else if ctx.payload.is_some()&&super::super::super::direct_map_tail_counter::wp5_enabled()
                &&super::super::super::direct_map_tail_counter::wp5_m6a_enabled()&&(36..=96).contains(&cp.col){
                let r=stage_m6plain_v(b,ctx,&par,cp.m);b.play(&r.tape,false);
            }else if ctx.payload.is_some()&&super::super::super::direct_map_tail_counter::wp5_enabled()&&(41..=81).contains(&cp.col){
                let r=stage_m6plain(b,ctx,&par,cp.m);b.play(&r.tape,false);
            }else{let r=stage(b,ctx,&par,cp.m,false);b.play(&r.tape,false);}
        },
        Mode::Native=>{
            if super::super::super::c659::t23_enabled()&&ctx.payload.is_none(){
                let mut scratch9=scratch.clone();scratch9.push(ctx.terminal_loans[0]);
                super::apply_stage_with_loans(b,ctx.ring,ctx.q,ctx.y,&scratch9,ctx.ph,&par,cp.m,cp.dn,false,&dirty,&[],&mut done);
                return;
            }
            let d=bank(&dirty,ctx.q);done(b,ctx.roles.tag,&d);
            let r=if ctx.payload.is_some()&&super::super::super::direct_map_tail_counter::wp5_enabled()
                &&super::super::super::direct_map_tail_counter::wp5_m6b_enabled(){
                stage_m6native_ql4(b,ctx,&par,cp.m)
            }else{stage(b,ctx,&par,cp.m,true)};
            b.play(&r.tape,false);done(b,ctx.roles.tag,&d);
        },
        Mode::PureHt=>{
            if super::super::super::c659::t23_enabled()&&ctx.payload.is_none(){
                let mut scratch9=scratch.clone();scratch9.push(ctx.terminal_loans[0]);
                super::apply_stage_with_loans(b,ctx.ring,ctx.q,ctx.y,&scratch9,ctx.ph,&par,cp.m,cp.dn,true,&dirty,&[],&mut done);
                return;
            }
            let wp5=ctx.payload.is_some()&&super::super::super::direct_map_tail_counter::wp5_enabled();
            if wp5 {
                let d:Vec<_>=dirty.iter().copied().filter(|q|*q!=ctx.roles.toggle).collect();
                let d=bank(&d,ctx.q);
                done(b,ctx.roles.tag,&d);b.x(ctx.roles.tag);b.x(ctx.ph);
                let r=stage_m6ph(b,ctx,&par,cp.m);
                paired_dirty(b,&r,ctx.roles.tag,ctx.ring);
                b.x(ctx.ph);b.x(ctx.roles.tag);done(b,ctx.roles.tag,&d);
            }else{
                let r=stage(b,ctx,&par,cp.m,false);let d=bank(&dirty,ctx.q);
                done(b,ctx.roles.tag,&d);b.x(ctx.roles.tag);b.x(ctx.ph);
                paired_clean(b,&r,ctx.roles.tag,ctx.ph);b.x(ctx.ph);b.x(ctx.roles.tag);done(b,ctx.roles.tag,&d);
            }
        },
    }
}

#[cfg(test)]
#[path="k1_complete_adapter.rs"]
pub(crate) mod complete_adapter;

struct Restore(bool);
impl Drop for Restore { fn drop(&mut self){ super::super::super::r13prof::set_map_ok(self.0); } }
