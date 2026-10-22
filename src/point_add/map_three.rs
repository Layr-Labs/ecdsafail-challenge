//! Three-role map adapter. Source candidate, not a validated lower-width result.
//!
//! C + M7 + old E7 is the complete fifteen-owner metadata bank. After
//! entry, E7 becomes TZ5/T/G. There is no stored cut E. Cut predicates are
//! read directly, and each odd-source frame borrows its physical Q0=1 as
//! the row carry after an explicit X. All controlled maps control EVERY
//! literal, so no known-one claim is made on inactive DONE data.
use super::builder::{B,G};
use super::direct_three::Column;
use super::frogdrop::{self,MapPar};
use super::frogdrop_col::ColPar;
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

pub(crate) fn record(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
pub(crate) fn bank(universe:&[QubitId],held:&[QubitId])->Vec<QubitId>{
    let mut seen=BTreeSet::new();universe.iter().copied()
        .filter(|q|!held.contains(q)&&seen.insert(*q)).collect()
}
pub(crate) fn xor(b:&mut B,c:&[(QubitId,bool)],t:QubitId,universe:&[QubitId]){
    let mut unique=BTreeSet::new();assert!(c.iter().all(|p|p.0!=t&&unique.insert(p.0)));
    let held:Vec<_>=c.iter().map(|p|p.0).chain([t]).collect();
    let d=bank(universe,&held);assert!(d.len()>=c.len().saturating_sub(2));
    mc_xor(b,c,t,&[],&d);
}
pub(crate) fn eq(w:&[QubitId],v:usize)->Vec<(QubitId,bool)>{
    w.iter().enumerate().map(|(i,&q)|(q,v>>i&1==0)).collect()
}
pub(crate) fn cover(w:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    assert!(lo<=hi&&hi<=1usize<<w.len());let mut out=vec![];
    while lo<hi{let mut f=if lo==0{w.len()}else{lo.trailing_zeros()as usize};
        f=f.min(w.len());while lo+(1usize<<f)>hi{f-=1;}
        out.push((f..w.len()).map(|i|(w[i],lo>>i&1==0)).collect());lo+=1usize<<f;
    }out
}
pub(crate) fn swap(b:&mut B,c:&[(QubitId,bool)],a:QubitId,z:QubitId,d:&[QubitId]){
    assert!(a!=z&&c.iter().all(|p|p.0!=a&&p.0!=z));
    b.cx(a,z);let mut ctl=c.to_vec();ctl.push((z,false));xor(b,&ctl,a,d);b.cx(a,z);
}
/// Exact fixed rotation under a conjunction; no stored conjunction owner.
fn rotate(b:&mut B,w:&[QubitId],amount:usize,c:&[(QubitId,bool)],d:&[QubitId]){
    let s=amount%w.len();if s==0{return;}let mut seen=vec![false;w.len()];
    for start in 0..w.len(){if seen[start]{continue;}seen[start]=true;
        let mut next=(start+s)%w.len();while next!=start{
            seen[next]=true;swap(b,c,w[start],w[next],d);next=(next+s)%w.len();
        }
    }
}
fn rotate_word(b:&mut B,w:&[QubitId],amount:&[QubitId],extra:&[(QubitId,bool)],
    inverse:bool,d:&[QubitId]){
    for(i,&q)in amount.iter().enumerate(){let mut c=extra.to_vec();c.push((q,false));
        let s=(1usize<<i)%w.len();rotate(b,w,if inverse{w.len()-s}else{s},&c,d);
    }
}
/// Swap output basis states 0 and value, leaving every other output word
/// unchanged. Descending distinct nonzero values implement a zero-output
/// priority probe without a found/helper bit. Replay the SAME tape to erase.
pub(crate) fn zero_transposition(b:&mut B,w:&[QubitId],value:usize,
    extra:&[(QubitId,bool)],d:&[QubitId]){
    assert!(value>0&&value<1usize<<w.len());
    let path:Vec<_>=(0..w.len()).filter(|i|value>>i&1!=0).collect();
    let mut state=0usize;let mut edges=vec![];
    for &bit in &path{edges.push((state,bit));state^=1usize<<bit;}
    let emit=|b:&mut B,(state,bit):(usize,usize)|{
        let mut c=extra.to_vec();c.extend(w.iter().enumerate().filter(|p|p.0!=bit)
            .map(|(i,&q)|(q,state>>i&1==0)));xor(b,&c,w[bit],d);
    };
    for &edge in &edges{emit(b,edge);}
    for &edge in edges[..edges.len()-1].iter().rev(){emit(b,edge);}
}
fn msb_probe(b:&mut B,w:&[QubitId],out:&[QubitId],lo:usize,hi:usize,
    extra:&[(QubitId,bool)],d:&[QubitId]){
    for j in(lo.max(1)..hi).rev(){let mut c=extra.to_vec();c.push((w[j],false));
        zero_transposition(b,out,j,&c,d);
    }
}
fn trailing_probe(b:&mut B,w:&[QubitId],out:&[QubitId],max:usize,
    extra:&[(QubitId,bool)],d:&[QubitId]){
    assert!(max<w.len()&&max<1usize<<out.len());
    for j in 1..=max{let mut c=extra.to_vec();c.extend(w[..j].iter().map(|&q|(q,true)));
        if j<max{c.push((w[j],false));}
        for(i,&q)in out.iter().enumerate(){if j>>i&1!=0{xor(b,&c,q,d);}}
    }
}
/// Small exact addition with no carry owner. Descending target writes are
/// a controlled increment; addends and controls are never modified.
fn add_small(b:&mut B,source:&[QubitId],target:&[QubitId],extra:&[(QubitId,bool)],d:&[QubitId]){
    for(i,&s)in source.iter().enumerate(){assert!(i<target.len());
        for j in(i..target.len()).rev(){let mut c=extra.to_vec();c.push((s,false));
            c.extend(target[i..j].iter().map(|&q|(q,false)));xor(b,&c,target[j],d);
        }
    }
}

/// Original direct entry, with no independent helper. A known leading
/// ONE of positive ring-top is transported to ring256 ONLY for ordering.
/// Equal sizes take Q0=1, so the original top-size is min; otherwise its
/// selector Q0 reconstructs the original size before y is erased.
fn entry(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],m:&[QubitId],
    bound:usize,mlo:usize,mhi:usize,d:&[QubitId])->Vec<G>{
    assert_eq!((ring.len(),y.len(),m.len()),(257,7,7));
    assert!(1<=mlo&&mlo<=mhi&&mhi<=bound&&bound<=q.len());
    record(b,|b|{
        msb_probe(b,&q[..bound],m,1,bound,&[],d);
        rotate_word(b,ring,y,&[],false,d);
        let helper=ring[256];b.x(helper);
        let held:Vec<_>=m.iter().chain(y).copied().chain([helper]).collect();
        let carry_d=bank(d,&held);let donor=carry_d[0];
        for &v in m{b.x(v);}super::arith::ttk_carry_u(b,m,y,helper,donor);for &v in m{b.x(v);}
        for i in 0..7{b.cswap(helper,m[i],y[i]);}
        let rot=record(b,|b|frogdrop::rot_by_range(b,q,m,mlo-1,mhi-1,false,&bank(d,m)));
        b.play(&rot,true);b.x(helper);b.cx(q[0],helper); // helper=0
        b.x(helper); // restore transported leading ONE
        rotate_word(b,ring,y,&[(q[0],false)],true,d);
        rotate_word(b,ring,m,&[(q[0],true)],true,d);
        let translate=record(b,|b|{
            b.x(q[0]);let r=record(b,|b|super::arith::ttk_add(b,m,y,Some(q[0]),None));b.play(&r,true);
            let held:Vec<_>=y.iter().copied().chain([q[0]]).collect();
            super::modp_frogdrop::add_const_exact(b,y,Some(q[0]),(q.len()%128)as u64,&bank(d,&held));b.x(q[0]);
        });b.play(&translate,false);
        let qp=record(b,|b|msb_probe(b,q,y,q.len()-bound+1,q.len(),&[(q[0],true)],d));b.play(&qp,true);
        let rp=record(b,|b|for j in(1..mhi).rev(){
            let terms=if j<mlo{vec![vec![]]}else{cover(m,j,128)};
            for mut c in terms{c.extend([(q[0],false),(ring[256-j],false)]);zero_transposition(b,y,j,&c,d);}
        });b.play(&rp,true);b.play(&rot,false);
    })
}

struct Core<'a>{m:&'a[QubitId],ez:&'a[QubitId],t:QubitId,g:QubitId,bound:usize,d:&'a[QubitId]}
impl Core<'_>{
    fn stages(&self,b:&mut B,flag:(QubitId,bool),reverse:bool,mut body:impl FnMut(&mut B,usize,&[(QubitId,bool)])){
        let order:Vec<_>=if reverse{(0..5).rev().collect()}else{(0..5).collect()};
        for k in order{body(b,k,&[flag,(self.ez[k],false)]);}
    }
    fn widen(&self,b:&mut B,flag:(QubitId,bool))->Vec<G>{
        record(b,|b|{let r=record(b,|b|add_small(b,self.ez,self.m,&[flag],self.d));b.play(&r,true);})
    }
    fn ring_rot(&self,b:&mut B,ring:&[QubitId],flag:(QubitId,bool),up:bool){
        self.stages(b,flag,false,|b,k,c|{let s=1usize<<k;rotate(b,ring,if up{s}else{ring.len()-s},c,self.d);});
    }
    fn q_rot(&self,b:&mut B,q:&[QubitId],flag:(QubitId,bool),down:bool){
        self.stages(b,flag,false,|b,k,c|{let s=(1usize<<k)%q.len();rotate(b,q,if down{q.len()-s}else{s},c,self.d);});
    }
    fn cut(&self,lane:usize)->Vec<Vec<(QubitId,bool)>>{cover(self.m,0,(256usize.saturating_sub(lane)).min(128))}
    fn shift(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,flag:(QubitId,bool),up:bool){
        self.stages(b,flag,up,|b,k,c|{let step=1usize<<k;if step>=hi{return;}
            let r=record(b,|b|{
                for lane in step..lo.max(step){swap(b,c,ring[lane],ring[lane-step],self.d);}
                for lane in lo.max(step)..hi{for mut term in self.cut(lane){term.extend_from_slice(c);
                    swap(b,&term,ring[lane],ring[lane-step],self.d);}}
            });b.play(&r,up);
        });
    }
    fn pminus(&self,b:&mut B,ring:&[QubitId],lo:usize,hi:usize,tail:usize,flag:(QubitId,bool)){
        assert!(lo>42+tail&&hi<=ring.len());
        for &v in &ring[..lo.min(256)]{xor(b,&[flag],v,self.d);}
        for lane in lo..hi.min(256){for mut term in self.cut(lane){term.push(flag);xor(b,&term,ring[lane],self.d);}}
        for(target,k)in[(&ring[..10+tail],976u64),(&ring[32..33+tail],1u64)]{
            if flag.1{b.x(flag.0);}let held:Vec<_>=target.iter().copied().chain([flag.0]).collect();
            let r=record(b,|b|super::modp_frogdrop::add_const_exact(b,target,Some(flag.0),k,&bank(self.d,&held)));
            b.play(&r,true);if flag.1{b.x(flag.0);}
        }
    }
    fn masked_swap(&self,b:&mut B,ring:&[QubitId],q:&[QubitId],lo:usize,hi:usize){
        let qlo=ring.len()-q.len();
        for lane in hi.max(qlo)..ring.len(){b.swap(ring[lane],q[256-lane]);}
        for lane in lo.max(qlo)..hi{for term in cover(self.m,(256-lane).min(128),128){
            swap(b,&term,ring[lane],q[256-lane],self.d);
        }}
    }
    fn frame(&self,b:&mut B,ring:&[QubitId],q:&[QubitId],p:&MapPar,inverse:bool){
        let(llo,lhi)=(257-p.chi,257-p.clo);
        let r=record(b,|b|{
            let rot=record(b,|b|frogdrop::rot_by_range(b,ring,self.m,llo-1,lhi-1,false,&bank(self.d,self.m)));
            b.play(&rot,false);let v:Vec<_>=(0..257).map(|i|ring[(i+256)%257]).collect();
            // Both exact map legs supply an odd Q. Q0 is outside every
            // row's source/target. It is restored before any map operation.
            b.x(q[0]);
            for i in(llo..256).rev(){let lo=i+1;let nm=(p.m-1).min(257-lo);let nt=p.tail.min(257-lo-nm);
                let width=nm.min(self.bound-1);let tw=nm+nt-width;
                let terms=if i<lhi{cover(self.m,0,i.min(128))}else{vec![vec![]]};
                for mut term in terms{term.push((v[i],false));xor(b,&term,self.g,self.d);}
                let cleanbank=q[self.bound..].to_vec();let na=tw.min(cleanbank.len());
                let clean=&cleanbank[..na];let nc=width.min(cleanbank.len()-na);let andc=&cleanbank[na..na+nc];
                let held:Vec<_>=v[lo..lo+nm+nt].iter().chain(&q[..1+width]).chain(clean).chain(andc)
                    .copied().chain([self.g]).collect();let row_d=bank(self.d,&held);
                super::frogdrop::joint_tail::cadd_tail_no_h(b,self.g,&v[lo..lo+width],&q[1..1+width],
                    &v[lo+width..lo+nm+nt],q[0],clean,&row_d,andc);
                let terms=if i<lhi{cover(self.m,0,i.min(128))}else{vec![vec![]]};
                for mut term in terms{term.push((v[i],false));xor(b,&term,self.g,self.d);}
            }
            b.x(q[0]);b.play(&rot,true);
        });b.play(&r,inverse);
    }
}

pub(crate) fn stage_record(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],scratch:&[QubitId],
    ph:QubitId,p:&MapPar,bound:usize,dirty:&[QubitId])->Vec<G>{
    assert_eq!((ring.len(),y.len(),scratch.len()),(257,7,8));assert!(2<=bound&&bound<=q.len()&&q.len()<=128);
    let ports:Vec<_>=ring.iter().chain(q).chain(y).chain(scratch).copied().chain([ph]).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    let all:Vec<_>=ring.iter().chain(q).chain(y).chain(&scratch[1..]).chain(dirty).copied().collect();
    let d=bank(&all,&[scratch[0],ph]);
    let sc=Core{m:&scratch[1..8],ez:&y[..5],t:y[5],g:y[6],bound,d:&d};
    record(b,|b|{
        let en=entry(b,ring,q,y,sc.m,bound,257-p.chi,257-p.clo,&d);b.play(&en,false);
        let rev:Vec<_>=ring.iter().rev().copied().collect();
        let probe=record(b,|b|{
            trailing_probe(b,&q[..p.emax+1],sc.ez,p.emax,&[],&d);
            trailing_probe(b,&rev[..p.emax+1],sc.ez,p.emax,&[(q[0],false)],&d);
        });b.play(&probe,false);b.x(q[0]);b.cx(q[0],sc.t);b.x(q[0]);
        let(yf,xf)=((sc.t,true),(sc.t,false));let wy=sc.widen(b,yf);let wx=sc.widen(b,xf);
        let(lo,hi)=(p.clo,p.chi);let hi2=(hi+p.emax).min(256);
        let wide=MapPar{clo:lo,chi:hi2,m:p.m,tail:p.tail,emax:p.emax};
        sc.ring_rot(b,ring,yf,true);b.play(&wy,false);sc.shift(b,ring,lo,hi2,yf,false);sc.q_rot(b,q,xf,true);
        sc.frame(b,ring,q,&wide,false);sc.q_rot(b,q,xf,false);sc.pminus(b,ring,lo,hi2,p.tail,yf);
        b.play(&wy,true);sc.ring_rot(b,ring,yf,false);sc.masked_swap(b,ring,q,lo,hi);
        sc.ring_rot(b,ring,xf,true);b.play(&wx,false);sc.pminus(b,ring,lo,hi2,p.tail,xf);
        sc.q_rot(b,q,yf,true);sc.frame(b,ring,q,&wide,true);sc.q_rot(b,q,yf,false);
        sc.shift(b,ring,lo,hi2,xf,true);b.play(&wx,true);sc.ring_rot(b,ring,xf,false);
        b.x(ring[256]);b.cx(ring[256],sc.t);b.x(ring[256]);b.play(&probe,true);b.play(&en,true);
    })
}

/// Full literal NAND replay, including entry and known-one transports.
pub(crate) fn nand_replay(b:&mut B,r:&[G],ph:QubitId,c:QubitId,universe:&[QubitId]){
    for &gate in r{let g=match gate{G::AndC(a,d,t)|G::AndU(a,d,t)=>G::Ccx(a,d,t),g=>g};
        let mut held=vec![ph,c];match g{G::X(t)=>held.push(t),G::Cx(a,t)|G::Swap(a,t)=>held.extend([a,t]),
            G::Ccx(a,d,t)=>held.extend([a,d,t]),_=>panic!("map-three requires literal tape")}
        let donors=bank(universe,&held);assert!(donors.len()>=2);b.play_ctrl_nand2(&[g],ph,c,donors[0],donors[1]);
    }
}
fn done(b:&mut B,col:&Column<'_>,target:QubitId,extra:&[(QubitId,bool)],d:&[QubitId]){
    let mut base=vec![(col.phase,false)];base.extend(col.q[64..121].iter().map(|&q|(q,true)));
    for &(q,n)in extra{if let Some(old)=base.iter().find(|p|p.0==q){if old.1!=n{return;}}else{base.push((q,n));}}
    xor(b,&base,target,d);base.extend(col.q[121..].iter().map(|&q|(q,true)));xor(b,&base,target,d);
}
pub(crate) fn controlled(cp:&ColPar)->bool{!cp.nomap&&cp.sz!=(0,0)&&cp.dn&&cp.m>121}
pub(crate) fn finish(b:&mut B,col:&Column<'_>,cp:&ColPar){
    assert!(!cp.nomap&&cp.sz!=(0,0));
    assert_eq!((cp.n,cp.nq,col.q.len(),col.ring.len()),(257,128,128,257));
    assert!((2..=128).contains(&cp.m)&&cp.emax<=31);
    let r=col.roles;let scratch:Vec<_>=std::iter::once(r.tag).chain(col.meta.sum.iter().copied()).chain([r.cut,r.work]).collect();
    let all:Vec<_>=col.ring.iter().chain(col.q).chain(&col.meta.y).chain(&scratch[1..]).chain(col.dirty).copied().collect();
    let d=bank(&all,&[r.tag,col.phase]);let ctl=controlled(cp);let qend=if cp.dn&&!ctl{121}else{128};
    let p=MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,m:if cp.dn{128}else{cp.m},tail:cp.tail,emax:cp.emax};
    let tape=stage_record(b,col.ring,&col.q[..qend],&col.meta.y,&scratch,col.phase,&p,cp.m,&d);
    if ctl{let dd=bank(&d,col.q);done(b,col,r.tag,&[],&dd);nand_replay(b,&tape,col.phase,r.tag,&d);done(b,col,r.tag,&[],&dd);}
    else{b.play(&tape,false);}
    if cp.sw||cp.dl{assert!(cp.sw);super::tail_three::apply(b,col.ring,col.q,&col.meta.y,&scratch,col.phase,
        &super::frogdrop::direct_tail::TailPar{l0:cp.l0,qb:cp.qb,szlo:cp.sz.0,sylo:cp.sy.0,swl_hi:cp.swl.1,m:cp.m},false,&d);}
    counter(b,col,cp,&d);
}
fn counter(b:&mut B,col:&Column<'_>,cp:&ColPar,d:&[QubitId]){
    if !cp.dn&&!cp.fin{return;}let r=col.roles;let flag=r.cut;let cnt=&col.q[121..128];
    let sched=super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let first=sched.cols.iter().position(|c|c.fin).expect("public first finisher");
    assert!(cp.col<sched.cols.len()&&cp.col.saturating_sub(first)+1<128);
    if cp.dn{done(b,col,flag,&[(r.tag,true)],d);
        for j in(0..7).rev(){let mut c=vec![(flag,false)];c.extend(cnt[..j].iter().map(|&q|(q,false)));xor(b,&c,cnt[j],d);}
        done(b,col,flag,&[(r.tag,true)],d);
    }
    if cp.fin{let mut fresh=vec![(col.phase,false),(r.tag,true)];fresh.extend(col.meta.y.iter().map(|&q|(q,true)));
        xor(b,&fresh,flag,d);done(b,col,flag,&fresh,d);b.cx(flag,cnt[0]);
        let mut made=fresh;made.push((cnt[0],false));made.extend(cnt[1..].iter().map(|&q|(q,true)));assert_eq!(cp.l0,128);xor(b,&made,flag,d);
    }
}
