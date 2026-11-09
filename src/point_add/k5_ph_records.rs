//! Three-role wrappers around the exact qualified K5 and K3 bodies.
use super::*;
use super::super::k5_ph_ports::Context;
use super::k5_records::Fault;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Source {Parked,EmptyQ}
pub(crate) struct Arithmetic {ht:bool,source:Source,hr_site:Option<HrSite>}
impl Arithmetic {
 pub(crate) fn controller(ht:bool,source:Source)->Self{Self{ht,source,hr_site:None}}
 pub(crate) fn hr(site:HrSite)->Self{Self{ht:false,source:Source::EmptyQ,hr_site:Some(site)}}
 fn record(&self,b:&mut B,c:&Context<'_>,t:&[QubitId],gate:Gate,op:Op,close:Close)->Vec<G> {
 if let Some(site)=self.hr_site {return twin(self,b,c,t,gate,op,close,site);}
 record(self,b,c,t,gate,op,close,Fault::None)
 }
    pub(crate) fn divide(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,inverse:bool){let r=self.record(b,c,t,g,Op::Divide,Close::None);b.play(&r,inverse);}
    /// Forward D;I, inverse I;D^-1, on the complete divide image.
    pub(crate) fn divide_inplace(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,inverse:bool){let r=self.record(b,c,t,g,Op::Divide,Close::Inplace);b.play(&r,inverse);}
    pub(crate) fn divide_erase_inplace(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,slot:QubitId){let r=self.record(b,c,t,g,Op::Divide,Close::EraseInplace(slot));b.play(&r,false);}
    pub(crate) fn add(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate){let r=self.record(b,c,t,g,Op::Add,Close::None);b.play(&r,false);}
    pub(crate) fn vbit(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,top:VTop){let r=self.record(b,c,t,g,Op::VBit(top),Close::None);b.play(&r,false);}
    pub(crate) fn vbit_store(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,top:VTop){let r=self.record(b,c,t,g,Op::VBit(top),Close::Store(top));b.play(&r,false);}
}
fn witness(b:&mut B,c:&Context<'_>,gate:Gate,d:&[QubitId])->Vec<G>{
    let r=c.roles;
    // A1 and every skipped-flight e1 are images of the same public
    // column envelope. If Yhi+j<=128, capacity is implied throughout
    // this complete guard and its inverse. No arithmetic span is cut.
    let gate=match gate{
        Gate::Top(j) if c.y_bounds.1<=128-j=>Gate::Natural(j),
        Gate::Bottom(k) if c.y_bounds.1<=114=>Gate::Natural(k+15),g=>g};
    if let Gate::Bottom(k)=gate{
        assert!(k<15);
        let byte:Vec<_>=c.size.y.iter().copied().chain([r.mask]).collect();
        let negative=product(cover(&byte,128-k,256),cover(&c.size.sum,17-k,32));
        let old_pair=188+4*negative.iter().map(|t|match t.len()+1{0|1=>0,2=>1,n=>4*(n-2)}).sum::<usize>();
        if super::super::bottom_comparator::arithmetic_price(k)<old_pair{
            return super::super::bottom_comparator::witness_record3(b,c,k,d);
        }
        let address=super::super::direct_frame::z_byte_record(b,c.size,r.mask,d);
        return rec(b,|b|{b.play(&address,false);
            for (a,t) in [(r.activity,r.flight),(r.flight,r.activity)]{
                xor_terms(b,&negative,t,&[(a,false)],d);
            }b.play(&address,true);
        });
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

fn twin(dmode:&Arithmetic,b:&mut B,c:&Context<'_>,t:&[QubitId],gate:Gate,op:Op,close:Close,site:HrSite)->Vec<G>{
 c.check();assert!(!dmode.ht&&matches!(op,Op::Divide)&&matches!(gate,Gate::Natural(k) if k<30));
 match(site,close){(HrSite::PayloadTick,Close::None)|(HrSite::NoPayloadTwin,Close::Inplace)=>{},_=>panic!("K5_HR_SITE_CLOSE")}
 assert_eq!(c.traversal.has_payload(),matches!(site,HrSite::PayloadTick));
 assert_eq!(t.len(),129);if let Gate::Natural(k)=gate {assert_eq!(t,super::super::k5_ph_ports::natural_target(c,k),"K5_PH_TARGET_FRAME");}
 let first=128-c.y_bounds.1;assert!(first<=126);let r=c.roles;
 let mut used=BTreeSet::new();assert!(t.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
 .chain([r.activity,r.flight,r.mask]).all(|q|used.insert(q)));
 let dirty=c.bank(&[c.q[127]]);b.begin();let guard=witness(b,c,gate,&dirty);b.play(&guard,false);
 for &q in t{b.x(q);}ttk_natural(b,&t[first..],&c.q[first..],r.activity,r.flight,r.mask,&dirty);
 for &q in t{b.x(q);}if matches!(close,Close::Inplace){b.cswap(r.activity,t[128],r.flight);}
 b.play(&guard,true);b.end()
}
fn record(dmode:&Arithmetic,b:&mut B,c:&Context<'_>,t:&[QubitId],gate:Gate,op:Op,close:Close,fault:Fault)->Vec<G>{
 c.check();assert_eq!(t.len(),129);let r=c.roles;
    let j=match gate {Gate::Top(j)|Gate::Bottom(j)=>{assert!(j<15,"K5_SELECTOR_INDEX");j},Gate::Natural(_)=>panic!("K5_SELECTOR_NATURAL")};
    let expected=match gate{Gate::Top(k)=>super::super::k5_ph_ports::top_target(c,k),Gate::Bottom(k)=>super::super::k5_ph_ports::natural_target(c,k),_=>unreachable!()};assert_eq!(t,expected,"K5_PH_TARGET_FRAME");
    match (op,close) {
        (Op::Add,Close::None)=>assert!(dmode.ht,"K5_SELECTOR_ADD_HR"),
        (Op::Divide,Close::None|Close::Inplace)=>{},
        (Op::Divide,Close::EraseInplace(slot))=>{
            assert_eq!(dmode.source,Source::Parked,"K5_SELECTOR_ERASE_POLICY");assert_eq!(slot,super::super::k5_ph_ports::park(c,j),"K5_SELECTOR_ERASE_SLOT");
        },
        (Op::VBit(top),Close::None)|(Op::VBit(top),Close::Store(_))=>{
            match (gate,top) { (Gate::Top(g),VTop::Frame(v))=>assert_eq!(g,v,"K5_SELECTOR_VFRAME"),(Gate::Bottom(_),VTop::Zero)=>{},_=>panic!("K5_SELECTOR_VFRAME") }
            if let Close::Store(other)=close {assert!(matches!((top,other),(VTop::Zero,VTop::Zero))||matches!((top,other),(VTop::Frame(a),VTop::Frame(z)) if a==z));}
        },_=>panic!("K5_SELECTOR_CLOSE"),
    }
    if let Gate::Top(j)=gate {if c.y_bounds.0>128-j {return vec![];}}
    let hi=if let Gate::Top(j)=gate {c.y_bounds.1.min(128-j)}else{c.y_bounds.1};
    let prefix=hi>=115&&dmode.source==Source::Parked;
    let first=if prefix {14}else{128-hi};assert!(first<=126);
    let mut ports=BTreeSet::new();
    assert!(t.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
        .chain([r.activity,r.flight,r.mask]).all(|q|ports.insert(q)));
    let dirty=c.bank(&[c.q[127]]);let add=matches!(op,Op::Add);let complement=matches!(op,Op::Divide);
    b.begin();let guard=if add {vec![]}else{witness(b,c,gate,&dirty)};b.play(&guard,false);
    if complement {for &q in t {b.x(q);}}
    if prefix {k5_records::form_p(b,t,c.q,&c.size.y,&c.size.sum,r.activity,r.flight,r.mask,14,op,&dirty,fault);}
    else {k5_records::form_n(b,&t[first..],&c.q[first..],r.activity,r.flight,r.mask,&c.size.sum,op,&dirty,fault);}
    if complement {for &q in t {b.x(q);}}
    // The original close, kept in its original coordinate and guard position.
    match close {
        Close::None=>{},
        Close::Inplace|Close::EraseInplace(_)=>{
            if let Close::EraseInplace(slot)=close {b.ccx(r.activity,r.flight,slot);}
            b.cswap(r.activity,t[128],r.flight);
        },
        Close::Store(top)=>{
            match top {
                VTop::Zero=>b.cx(r.activity,t[128]),
                VTop::Frame(j)=>if j!=0 {b.cx(r.activity,t[128]);}else{
                    let donors:Vec<_>=dirty.iter().copied().filter(|q|*q!=t[128]).collect();
                    for mut term in cover(&c.size.sum,0,32-c.qb) {term.push((r.activity,false));mc_xor(b,&term,t[128],c.clean_external,&donors);}
                },
            }
            b.cswap(r.activity,t[128],r.flight);
        },
    }
    b.play(&guard,true);b.end()
}

#[cfg(test)]
pub(crate) fn diagnostic(b:&mut B,c:&Context<'_>,t:&[QubitId],ht:bool,source:Source,kind:usize,fault_id:usize)->Vec<G>{
 let fault=match fault_id{0=>Fault::None,1=>Fault::RootOnQ127,2=>Fault::MissingParityConjugation,3=>Fault::DroppedS2,_=>panic!("fault id")};
 let(op,gate)=match kind{0=>(Op::Divide,Gate::Bottom(0)),1=>(Op::VBit(VTop::Zero),Gate::Bottom(0)),2=>(Op::Add,Gate::Bottom(0)),_=>panic!("kind")};
 record(&Arithmetic::controller(ht,source),b,c,t,gate,op,Close::None,fault)
}
