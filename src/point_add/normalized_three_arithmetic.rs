//! Three-owner arithmetic in the common MSB-pivot coordinate.
//! Q129 has been rotated UP by 127-E and ring257 DOWN by that amount.
//! Q'[127] is the actual leading ONE on activity; Q'[128] is q0.
//! V6: exact shared arithmetic Bottom comparator plus the public low-Y reduction.
//! Full unparked source epochs still bypass the variable park prefix.
//! The lower fourteen source cells contain a variable data/park separator.
//! Ordinary writes use A/e/data cubic controls, with no metadata query.
//! Only the fourteen parked-prefix cells borrow PH/E4; no owner is allocated.

use super::builder::{B,G};
use super::cross_three::{Cross,Gate,VTop};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone,Copy)]
enum Op { Divide, Add, VBit(VTop) }
#[derive(Clone,Copy)]
enum Close { None, Inplace, EraseInplace(QubitId), Store(VTop) }

fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn cover(word:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    assert!(lo<=hi&&hi<=1usize<<word.len());let mut out=vec![];
    while lo<hi {let mut free=if lo==0{word.len()}else{lo.trailing_zeros()as usize};
        free=free.min(word.len());while lo+(1usize<<free)>hi{free-=1;}
        out.push((free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect());lo+=1usize<<free;
    }out
}
fn product(a:Vec<Vec<(QubitId,bool)>>,z:Vec<Vec<(QubitId,bool)>>)->Vec<Vec<(QubitId,bool)>>{
    let mut out=vec![];for x in a{for y in &z{let mut t=x.clone();t.extend(y);out.push(t);}}out
}
fn lit(b:&mut B,c:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!c.iter().any(|p|p.0==target));let mut seen=BTreeSet::new();
    let d:Vec<_>=dirty.iter().copied().filter(|q|*q!=target&&!c.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    mc_xor(b,c,target,&[],&d);
}
fn bank(c:&Cross<'_>)->Vec<QubitId>{let r=c.roles;
    let mut seen:BTreeSet<_>=c.size.y.iter().chain(&c.size.sum).copied()
        .chain(c.clean_external.iter().copied())
        .chain([c.phase,r.activity,r.flight,r.work,c.q[127]]).collect();
    c.dirty.iter().chain(c.ring).chain(c.q).copied().filter(|q|seen.insert(*q)).collect()
}
fn xor_terms(b:&mut B,t:&[Vec<(QubitId,bool)>],out:QubitId,extra:&[(QubitId,bool)],d:&[QubitId]){
    for term in t{let mut all=term.clone();all.extend_from_slice(extra);lit(b,&all,out,d);}
}

/// One combined Gate witness. No separate low/high-Y activity witness.
/// Unlike the old variable-boundary kernel, Top must retain its capacity
/// condition explicitly: the fixed query at128 cannot enforce Y+j<=128.
fn witness(b:&mut B,c:&Cross<'_>,gate:Gate,d:&[QubitId])->Vec<G>{
    let r=c.roles;
    // A1 and every skipped-flight e1 are images of the same public
    // column envelope. If Yhi+j<=128, capacity is implied throughout
    // this complete guard and its inverse. No arithmetic span is cut.
    let gate=match gate{
        Gate::Top(j) if c.y_bounds.1<=128-j=>Gate::Natural(j),
        Gate::Bottom(k) if c.y_bounds.1<=114=>Gate::Natural(k+15),g=>g};
    if let Gate::Bottom(k)=gate{
        return super::normalized_three_bottom::witness_record(b,c,k,d);
    }
    let (positive,negative)=match gate{
        Gate::Natural(k)=>(cover(&c.size.sum,0,32-k),cover(&c.size.sum,32-k,32)),
        Gate::Top(j)=>{
            assert!(j<15);
            let p=product(cover(&c.size.y,0,128-j),cover(&c.size.sum,0,32-j));
            let ey=cover(&c.size.y,128-j,128);
            let es=cover(&c.size.sum,32-j,32);
            let mut n=ey.clone();
            n.extend(product(cover(&c.size.y,0,128-j),es.clone()));
            // !Gate = Efail OR Sfail = Efail XOR Sfail XOR Efail*Sfail.
            // Every predicate is on unchanged metadata; overlaps cancel
            // algebraically, including all off-activity metadata words.
            let mut union=ey.clone();union.extend(es.clone());union.extend(product(ey,es));
            if price(&union)<price(&n){n=union;}(p,n)
        },Gate::Bottom(_)=>unreachable!(),
    };
    fn price(t:&[Vec<(QubitId,bool)>])->usize{t.iter().map(|x|match x.len()+1{0|1=>0,2=>1,n=>4*(n-2)}).sum()}
    let complement=price(&positive)<price(&negative);
    let terms=if complement{positive}else{negative};
    rec(b,|b|for(a,t)in[(r.activity,r.flight),(r.flight,r.activity)]{
        if complement{b.cx(a,t);}xor_terms(b,&terms,t,&[(a,false)],d);
    })
}

/// A two-level decoder frees E4 as a conditional-zero carry. On active
/// high E, PH is zero and becomes the running prefix mask. At the up/down
/// boundary H-controlled exchange transfers the prefix carry to/from PH;
/// on A, all seven E bits and Q127 are restored before the ordinary ripple.
/// Off A the preparation may permute them until prefix-down; every permanent
/// write retains A and no E query occurs in that interval.
struct Prefix<'a>{e:&'a[QubitId],root:QubitId,cur:Option<usize>}
impl Prefix<'_>{
    fn enter(&self,b:&mut B,d:&[QubitId]){
        b.x(self.root);lit(b,&[(self.e[4],false),(self.e[5],false),(self.e[6],false)],self.root,d);
        for &q in &self.e[4..7]{b.x(q);}
    }
    fn cell(&self,b:&mut B,level:usize,v:usize){
        let(a,na)=if level==0{(self.e[3],v&8==0)}else{(self.e[4+level],false)};
        let(z,nz)=(self.e[2-level],v>>(2-level)&1==0);
        if na{b.x(a);}if nz{b.x(z);}b.ccx(a,z,self.e[5+level]);if nz{b.x(z);}if na{b.x(a);}
    }
    fn goto(&mut self,b:&mut B,v:usize){
        assert!(v<16);let mut keep=0;
        if let Some(old)=self.cur{while keep<2&&((old^v)>>(2-keep))==0{keep+=1;}
            for i in(keep..2).rev(){self.cell(b,i,old);}}
        for i in keep..2{self.cell(b,i,v);}self.cur=Some(v);
    }
    fn eq(&self)->Vec<(QubitId,bool)>{
        vec![(self.root,false),(self.e[6],false),(self.e[0],self.cur.expect("decoder cursor")&1==0)]
    }
    fn xor_eq(&self,b:&mut B,out:QubitId,d:&[QubitId]){lit(b,&self.eq(),out,d);}
    fn leave(&mut self,b:&mut B,d:&[QubitId]){
        if let Some(v)=self.cur{for i in(0..2).rev(){self.cell(b,i,v);}}self.cur=None;
        for &q in &self.e[4..7]{b.x(q);}
        lit(b,&[(self.e[4],false),(self.e[5],false),(self.e[6],false)],self.root,d);b.x(self.root);
    }
}

fn cell(b:&mut B,s:QubitId,t:QubitId,x:QubitId,inverse:bool){
    if inverse{b.ccx(x,t,s);b.cx(s,x);b.cx(s,t);}
    else{b.cx(s,t);b.cx(s,x);b.ccx(x,t,s);}
}
fn controlled_cell(b:&mut B,s:QubitId,t:QubitId,x:QubitId,enable:QubitId,inverse:bool,d:&[QubitId]){
    if inverse{lit(b,&[(enable,false),(x,false),(t,false)],s,d);b.ccx(enable,s,x);b.ccx(enable,s,t);}
    else{b.ccx(enable,s,t);b.ccx(enable,s,x);lit(b,&[(enable,false),(x,false),(t,false)],s,d);}
}
fn lower(b:&mut B,c:&Cross<'_>,s:QubitId,t:QubitId,x:QubitId,d:&[QubitId]){
    let r=c.roles;b.cx(s,x);
    lit(b,&[(r.activity,false),(c.phase,false),(r.flight,false),(x,false)],t,d);b.cx(s,x);
}
fn first_swap(b:&mut B,p:&Prefix<'_>,a:QubitId,z:QubitId,d:&[QubitId]){
    b.cx(a,z);let mut ctl=p.eq();ctl.push((z,false));lit(b,&ctl,a,d);b.cx(a,z);
}
/// Same exact all-data parity as parent, with E5/E6 caches. E0 is the
/// uncached terminal bit: eq0 XOR eq1 cancels it without a clean claim.
fn parity14(b:&mut B,p:&Prefix<'_>,out:QubitId){
    assert_eq!(p.cur,Some(2));
    b.cx(p.root,out);b.ccx(p.root,p.e[5],out);b.ccx(p.root,p.e[6],out);
}
fn prefix(b:&mut B,c:&Cross<'_>,t:&[QubitId],down:bool,d:&[QubitId]){
    let mut p=Prefix{e:&c.size.y,root:c.q[127],cur:None};p.enter(b,d);
    let mask=c.phase;let carry=c.size.y[4];
    if down{b.cswap(p.root,carry,mask);p.goto(b,2);parity14(b,&p,mask);b.cswap(mask,carry,c.q[13]);}
    let order:Vec<_>=if down{(0..14).rev().collect()}else{(0..14).collect()};
    for i in order{let v=15-i;p.goto(b,v);let x=if i==0{carry}else{c.q[i-1]};
        if down{
            controlled_cell(b,c.q[i],t[i],x,mask,true,d);
            lower(b,c,c.q[i],t[i],x,d);
            if i>0{first_swap(b,&p,carry,c.q[i-1],d);}
            p.xor_eq(b,mask,d);
        }else{
            p.xor_eq(b,mask,d);
            if i>0{first_swap(b,&p,carry,c.q[i-1],d);}
            controlled_cell(b,c.q[i],t[i],x,mask,false,d);
        }
    }
    if !down{b.cswap(mask,carry,c.q[13]);parity14(b,&p,mask);b.cswap(p.root,carry,mask);}
    p.leave(b,d);
}
fn top_query(b:&mut B,c:&Cross<'_>,positive:bool,target:QubitId,extra:&[(QubitId,bool)],d:&[QubitId]){
    let lim=32-c.qb;
    let terms=if positive{cover(&c.size.sum,lim,32)}else{cover(&c.size.sum,0,lim)};
    let mut controls=vec![(c.roles.activity,false)];controls.extend_from_slice(extra);
    xor_terms(b,&terms,target,&controls,d);
}
fn normal_decision(b:&mut B,enable:QubitId,e:QubitId,t:QubitId,x:QubitId,d:&[QubitId]){
    b.cx(enable,e);lit(b,&[(enable,false),(t,false),(x,false)],e,d);
}

/// The same stable call surface as cross_running_flight::D, but callers
/// must establish the complete Q/ring coordinate and pass fixed129 targets.
/// payload_open additionally requires NO parked Q bits: Q'[128] is the
/// conditional-zero carry. Otherwise PH is phase and remains the carry.
pub(crate) struct D{pub ht:bool,pub payload_open:bool}
impl D{
    fn record(&self,b:&mut B,c:&Cross<'_>,t:&[QubitId],gate:Gate,op:Op,close:Close)->Vec<G>{
        assert_eq!((c.q.len(),c.size.y.len(),c.size.sum.len(),t.len()),(128,7,5,129));
        assert_eq!(c.qb,30);let r=c.roles;let add=matches!(op,Op::Add);
        if let Gate::Top(j)=gate{if c.y_bounds.0>128-j{return vec![];}}
        // Public source-domain/capacity pruning only. Top additionally
        // has Y<=128-j on the complete acted sector (ADD has e=>Gate).
        // If that upper bound<=114, every source cell below14 is virtual
        // zero, even with all15 parks held; the inactive extension is identity.
        let acted_hi=if let Gate::Top(j)=gate{c.y_bounds.1.min(128-j)}else{c.y_bounds.1};
        let has_prefix=acted_hi>=115&&!self.payload_open;
        // Q is normalized with its leading ONE at127. The unchanged
        // public Y bound makes every bit below128-Yhi logically zero.
        // With held parks only the first14 positions need their separate
        // exact prefix; if absent, zero+target with carry0 has no carry.
        // Omitting those MAJ/restore identities leaves both complete
        // source/target words intact, including arbitrary off-A values.
        let first=if has_prefix{14}else{128-acted_hi};
        let carry=if self.payload_open{r.work}else{c.phase};
        let mut ports=BTreeSet::new();
        assert!(t.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
            .chain([r.activity,r.flight,carry]).all(|q|ports.insert(q)));
        let d=bank(c);let split=matches!(op,Op::VBit(VTop::Frame(0)));
        let complement=matches!(op,Op::Divide);
        b.begin();let guard=if add{vec![]}else{witness(b,c,gate,&d)};b.play(&guard,false);
        if !self.payload_open&&self.ht{b.cx(r.activity,c.phase);}
        if complement{for &q in t{b.x(q);}}
        if has_prefix{prefix(b,c,t,false,&d);}
        for i in first..128{cell(b,c.q[i],t[i],if i==first{carry}else{c.q[i-1]},false);}
        if !add{
            if split{
                top_query(b,c,false,r.flight,&[],&d);
                top_query(b,c,false,r.flight,&[(t[128],false),(c.q[127],false)],&d);
            }
            else{normal_decision(b,r.activity,r.flight,t[128],c.q[127],&d);}
        }
        lit(b,&[(r.activity,false),(r.flight,false),(c.q[127],false)],t[128],&d);
        for i in(first..128).rev(){let x=if i==first{carry}else{c.q[i-1]};cell(b,c.q[i],t[i],x,true);
            if split&&i==127{
                top_query(b,c,true,r.flight,&[(t[i],true),(x,true)],&d);
            }
            b.cx(c.q[i],x);lit(b,&[(r.activity,false),(r.flight,false),(x,false)],t[i],&d);b.cx(c.q[i],x);
        }
        if has_prefix{prefix(b,c,t,true,&d);}
        if complement{for &q in t{b.x(q);}}
        if !self.payload_open&&self.ht{b.cx(r.activity,c.phase);}
        // Complete adjacent pairs only, on their inherited e0 entry/image.
        // W has narrowed A to A&Gate; source/target/phase are now in the
        // old arithmetic output coordinates. Off Gate e holds skipped A,
        // so EVERY moved write retains narrowed A, including park erase.
        // Metadata is unchanged, hence the same W^-1 still closes exactly.
        match close{
            Close::None=>{},
            Close::Inplace|Close::EraseInplace(_)=>{
                assert!(matches!(op,Op::Divide));
                if let Close::EraseInplace(slot)=close{b.ccx(r.activity,r.flight,slot);}
                b.cswap(r.activity,t[128],r.flight);
            },
            Close::Store(top)=>{
                assert!(matches!(op,Op::VBit(_)));
                match top{
                    VTop::Zero=>b.cx(r.activity,t[128]),
                    VTop::Frame(j)=>if j!=0{b.cx(r.activity,t[128]);}else{
                        let donor:Vec<_>=d.iter().copied().filter(|q|*q!=t[128]).collect();
                        for mut term in cover(&c.size.sum,0,32-c.qb){
                            term.push((r.activity,false));
                            mc_xor(b,&term,t[128],c.clean_external,&donor);
                        }
                    },
                }
                b.cswap(r.activity,t[128],r.flight);
            },
        }
        b.play(&guard,true);b.end()
    }
    pub(crate) fn divide(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,inverse:bool){let r=self.record(b,c,t,g,Op::Divide,Close::None);b.play(&r,inverse);}
    /// Forward D;I, inverse I;D^-1, on the complete divide image.
    pub(crate) fn divide_inplace(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,inverse:bool){let r=self.record(b,c,t,g,Op::Divide,Close::Inplace);b.play(&r,inverse);}
    pub(crate) fn divide_erase_inplace(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,slot:QubitId){let r=self.record(b,c,t,g,Op::Divide,Close::EraseInplace(slot));b.play(&r,false);}
    pub(crate) fn add(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate){let r=self.record(b,c,t,g,Op::Add,Close::None);b.play(&r,false);}
    pub(crate) fn vbit(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,top:VTop){let r=self.record(b,c,t,g,Op::VBit(top),Close::None);b.play(&r,false);}
    pub(crate) fn vbit_store(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,top:VTop){let r=self.record(b,c,t,g,Op::VBit(top),Close::Store(top));b.play(&r,false);}
}
