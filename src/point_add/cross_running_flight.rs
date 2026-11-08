//! SOURCE-ONLY complete-Y Cross arithmetic; no registration or execution.
//! The forward decision flight itself is the lower-write mask. Capture
//! the ENTIRE Y sweep before taking its inverse: no inter-band e witness.
//! PH is a conditional-zero carry while it is phase metadata. In an open
//! P258 payload session, the returned x128 port is the global-zero carry.

use super::builder::{B,G};
use super::cross_four::{Cross,Gate,VTop};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[path="cross_running_cached.rs"]
mod cached;

#[derive(Clone,Copy)]
enum Op{Divide,Add,VBit(VTop)}

fn cover(bits:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    let mut out=vec![];
    while lo<hi{
        let mut f=if lo==0{bits.len()}else{lo.trailing_zeros()as usize};
        f=f.min(bits.len());while lo+(1usize<<f)>hi{f-=1;}
        out.push((f..bits.len()).map(|i|(bits[i],lo>>i&1==0)).collect());lo+=1usize<<f;
    }out
}
fn sum_interval(top:Option<bool>,qb:usize)->Option<(usize,usize)>{
    let hi=32;
    let (lo,hi)=match top{Some(true)=>(32-qb,hi),Some(false)=>(0,hi.min(32-qb)),None=>(0,hi)};
    (lo<hi).then_some((lo,hi))
}
fn product(a:Vec<Vec<(QubitId,bool)>>,z:Vec<Vec<(QubitId,bool)>>)->Vec<Vec<(QubitId,bool)>>{
    let mut out=vec![];for x in a{for y in &z{let mut t=x.clone();t.extend_from_slice(y);out.push(t);}}out
}
fn price(terms:&[Vec<(QubitId,bool)>])->usize{
    terms.iter().map(|t|match t.len()+1{0|1=>0,2=>1,n=>4*(n-2)}).sum()
}
/// One combined whole-Y witness. Top's Y capacity condition is enforced
/// by the public query upper bound, so no decision exists beyond it.
/// No Y-band witness is nested around this record.
fn witness(b:&mut B,c:&Cross<'_>,gate:Gate,dirty:&[QubitId])->Vec<G>{
    if let Gate::Bottom(k)=gate{
        assert!(k<15);
        // !Bottom = [S>=17-k] & [Z>=129-k] on ALL E7/S5 words.
        // The returned mask extends E to the exact byte Z-1 only while
        // these two transfers run. It is not a retained predicate owner.
        let r=c.roles;
        let address=super::direct_frame::z_byte_record(b,c.size,r.mask,dirty);
        let byte:Vec<_>=c.size.y.iter().copied().chain([r.mask]).collect();
        let terms=product(cover(&byte,128-k,256),cover(&c.size.sum,17-k,32));
        b.begin();b.play(&address,false);
        for(control,target)in[(r.activity,r.flight),(r.flight,r.activity)]{
            for mut term in terms.clone(){term.push((control,false));literal(b,&term,target,dirty);}
        }
        b.play(&address,true);return b.end();
    }
    let(positive,negative)=match gate{
        Gate::Natural(k)|Gate::Top(k)=>(cover(&c.size.sum,0,32-k),cover(&c.size.sum,32-k,32)),
        Gate::Bottom(_)=>unreachable!(),
    };
    let complement=price(&positive)<price(&negative);
    let terms=if complement{positive}else{negative};let r=c.roles;
    b.begin();
    for(control,target)in[(r.activity,r.flight),(r.flight,r.activity)]{
        if complement{b.cx(control,target);}
        c.size.xor_terms(b,terms.clone(),target,&[(control,false)],dirty);
    }b.end()
}

/// Prefixes Q120..124 are invoked only after all MAJ cells at120+ have
/// returned. They are zero on A & Y<=96 because full parks end atY+14<=110.
/// Hard, uncached E6/E5 literals retain that domain in EVERY final query.
/// High-Y/counter passengers may dirty these cells; literal CCX returns
/// them and the hard class controls forbid their effect on a query.
struct Reader<'a>{e:&'a [QubitId],pre:&'a [QubitId],cur:Option<(usize,usize)>}
impl<'a> Reader<'a>{
    fn cell(&self,b:&mut B,n:usize,level:usize,v:usize){
        let(a,na)=if level==0{(self.e[n-1],v>>(n-1)&1==0)}else{(self.pre[level-1],false)};
        let(c,nc)=(self.e[n-2-level],v>>(n-2-level)&1==0);
        if na{b.x(a);}if nc{b.x(c);}b.ccx(a,c,self.pre[level]);if nc{b.x(c);}if na{b.x(a);}
    }
    fn clear(&mut self,b:&mut B){if let Some((n,v))=self.cur{
        for level in(0..n-1).rev(){self.cell(b,n,level,v);}
    }self.cur=None;}
    fn equality(&mut self,b:&mut B,y:usize)->Vec<(QubitId,bool)>{
        assert!((1..=128).contains(&y));let v=y-1;
        if y>=97{
            self.clear(b);return self.e.iter().enumerate().map(|(i,&q)|(q,v>>i&1==0)).collect();
        }
        let n=if y<=64{6}else{5};let value=v&((1usize<<n)-1);
        if self.cur.map(|p|p.0)!=Some(n){self.clear(b);}
        let mut keep=0;
        if let Some((_,old))=self.cur{
            while keep<n-1&&((old^value)>>(n-2-keep))==0{keep+=1;}
            for level in(keep..n-1).rev(){self.cell(b,n,level,old);}
        }
        for level in keep..n-1{self.cell(b,n,level,value);}
        self.cur=Some((n,value));
        let mut c=vec![(self.pre[n-2],false),(self.e[6],y<=64)];
        if y>64{c.push((self.e[5],true));}c
    }
    fn query(&mut self,b:&mut B,c:&Cross<'_>,y:usize,_gate:Gate,top:Option<bool>,
        target:QubitId,control:QubitId,extra:&[(QubitId,bool)],add:bool,dirty:&[QubitId]){
        let interval=if add{Some((0,32))}else{sum_interval(top,c.qb)};
        let Some((lo,hi))=interval else{return;};
        let eq=self.equality(b,y);
        for mut sum in cover(&c.size.sum,lo,hi){
            sum.extend_from_slice(&eq);sum.push((control,false));sum.extend_from_slice(extra);
            literal(b,&sum,target,dirty);
        }
    }
}
fn literal(b:&mut B,c:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!c.iter().any(|p|p.0==target));let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied().filter(|q|*q!=target&&!c.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    mc_xor(b,c,target,&[],&bank);
}
fn bank(c:&Cross<'_>)->Vec<QubitId>{
    let r=c.roles;let mut used:BTreeSet<_>=c.size.y.iter().chain(&c.size.sum).chain(&c.q[120..125]).copied()
        .chain(c.clean_external.iter().copied()).chain([c.phase,r.activity,r.flight,r.mask,r.x128]).collect();
    c.dirty.iter().chain(c.ring).chain(c.q).copied().filter(|q|used.insert(*q)).collect()
}

pub(crate) struct D{pub ht:bool,pub payload_open:bool}
impl D{
    fn record(&self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,op:Op)->Vec<G>{
        assert_eq!(c.q.len(),128);assert_eq!(c.qb,30);
        let lo=c.y_bounds.0;let mut hi=c.y_bounds.1.min(target.len()-1);
        if let Gate::Top(j)=gate{hi=hi.min(128-j);}
        if lo>hi{return vec![];}
        assert!(lo>=1&&lo<=hi&&hi<=128);
        let t=&target[..hi+1];let s=&c.q[..(hi+1).min(128)];let r=c.roles;
        let carry=if self.payload_open{r.x128}else{c.phase};
        let mut used=BTreeSet::new();
        assert!(t.iter().chain(s).copied().chain([r.activity,r.flight,r.mask,carry]).all(|q|used.insert(q)));
        assert!(c.size.y.iter().chain(&c.size.sum).all(|q|!used.contains(q)));
        let mut external_ports:BTreeSet<_>=c.ring.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum)
            .copied().chain([c.phase,r.activity,r.flight,r.mask,r.x128]).collect();
        assert!(c.clean_external.iter().all(|q|external_ports.insert(*q)),"external clean ports must be independent");
        // The price walk has no builder side effects. Capture exactly one
        // selected implementation; the complete legacy tape stays below.
        if let Some((high,external))=cached::select(c,lo,hi,gate,op){
            return cached::record(b,c,t,gate,op,self.ht,self.payload_open,high,external);
        }
        let dirty=bank(c);let mut reader=Reader{e:&c.size.y,pre:&c.q[120..125],cur:None};
        let complement=matches!(op,Op::Divide);
        b.begin();
        let guard=if matches!(op,Op::Add){vec![]}else{witness(b,c,gate,&dirty)};
        b.play(&guard,false);
        if !self.payload_open&&self.ht{b.cx(r.activity,c.phase);}
        if complement{for &q in t{b.x(q);}}
        for i in 0..s.len(){let x=if i==0{carry}else{s[i-1]};
            b.cx(s[i],t[i]);b.cx(s[i],x);b.ccx(x,t[i],s[i]);}
        for i in(0..t.len()).rev(){
            let x=if i==0{carry}else{s[i-1]};
            if i<s.len(){b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);}
            // The decision is zero above its selected boundary. ADD uses
            // its separate global-zero running mask until that boundary.
            if i<hi{
                b.cx(s[i],x);
                if matches!(op,Op::Add){b.ccx(r.mask,x,t[i]);}
                else{literal(b,&[(r.activity,false),(r.flight,false),(x,false)],t[i],&dirty);}
                b.cx(s[i],x);
            }
            if matches!(op,Op::Add){
                if (lo..=hi).contains(&i){
                    // Incoming e implies A & Gate. The first query is the
                    // virtual-zero boundary write; the second starts the
                    // ordinary lower-word addition mask. e is unchanged.
                    reader.query(b,c,i,gate,None,t[i],r.flight,&[(x,false)],true,&dirty);
                    reader.query(b,c,i,gate,None,r.mask,r.flight,&[],true,&dirty);
                }
                continue;
            }
            let split=matches!(op,Op::VBit(VTop::Frame(0)));
            // Top-leading query comes first, as in the inherited reader.
            for leading in [true,false]{
                if leading&&!split{continue;}
                let y=if leading{i+1}else{i};
                if !(lo..=hi).contains(&y){continue;}
                let top=if split{Some(leading)}else{None};
                reader.query(b,c,y,gate,top,r.mask,r.activity,&[],false,&dirty);
                if leading{
                    literal(b,&[(r.mask,false),(t[i],true),(x,true)],r.flight,&dirty);
                    b.ccx(r.mask,r.flight,t[i]);
                }else{
                    b.cx(r.mask,r.flight);
                    literal(b,&[(r.mask,false),(t[i],false),(x,false)],r.flight,&dirty);
                    literal(b,&[(r.mask,false),(r.flight,false),(x,false)],t[i],&dirty);
                }
                reader.query(b,c,y,gate,top,r.mask,r.activity,&[],false,&dirty);
            }
        }
        reader.clear(b);
        if matches!(op,Op::Add){b.cx(r.flight,r.mask);}
        if complement{for &q in t{b.x(q);}}
        if !self.payload_open&&self.ht{b.cx(r.activity,c.phase);}
        b.play(&guard,true);
        b.end()
    }
    /// Forward e starts globally0. Reverse is the literal inverse of this
    /// complete-Y record, so an incoming quotient from any Y is supported.
    pub(crate) fn divide(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,inverse:bool){
        let tape=self.record(b,c,target,gate,Op::Divide);b.play(&tape,inverse);
    }
    /// Entry e=>A&Gate; e is retained and m starts/returns global0.
    pub(crate) fn add(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate){
        let tape=self.record(b,c,target,gate,Op::Add);b.play(&tape,false);
    }
    /// Decision/addition only; the inherited separate store follows.
    pub(crate) fn vbit(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,top:VTop){
        let tape=self.record(b,c,target,gate,Op::VBit(top));b.play(&tape,false);
    }
}
