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
    fn play_priced(&self,b:&mut B,r:&[G],g:Gate,op:Op,close:Close,inverse:bool){
        let family=match g{Gate::Top(_)=>0,Gate::Bottom(_)=>1,Gate::Natural(_)=>2};
        let source=if self.hr_site.is_some(){2}else if self.source==Source::Parked{0}else{1};
        let kind=match op{Op::Divide=>0,Op::Add=>1,Op::VBit(VTop::Frame(0))=>3,Op::VBit(_)=>2};
        let ending=match close{Close::None=>0,Close::Inplace=>1,Close::EraseInplace(_)=>2,Close::Store(_)=>3};
        let mark=3000+family*1000+source*100+kind*10+ending;
        super::super::r13prof::mk(b,mark);b.play(r,inverse);super::super::r13prof::mk(b,mark);
    }
    pub(crate) fn divide(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,inverse:bool){let r=self.record(b,c,t,g,Op::Divide,Close::None);self.play_priced(b,&r,g,Op::Divide,Close::None,inverse);}
    /// Forward D;I, inverse I;D^-1, on the complete divide image.
    pub(crate) fn divide_inplace(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,inverse:bool){let r=self.record(b,c,t,g,Op::Divide,Close::Inplace);self.play_priced(b,&r,g,Op::Divide,Close::Inplace,inverse);}
    pub(crate) fn divide_erase_inplace(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,slot:QubitId){let r=self.record(b,c,t,g,Op::Divide,Close::EraseInplace(slot));self.play_priced(b,&r,g,Op::Divide,Close::EraseInplace(slot),false);}
    pub(crate) fn add(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate){let r=self.record(b,c,t,g,Op::Add,Close::None);self.play_priced(b,&r,g,Op::Add,Close::None,false);}
    pub(crate) fn vbit(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,top:VTop){let r=self.record(b,c,t,g,Op::VBit(top),Close::None);self.play_priced(b,&r,g,Op::VBit(top),Close::None,false);}
    pub(crate) fn vbit_store(&mut self,b:&mut B,c:&Context<'_>,t:&[QubitId],g:Gate,top:VTop){let r=self.record(b,c,t,g,Op::VBit(top),Close::Store(top));self.play_priced(b,&r,g,Op::VBit(top),Close::Store(top),false);}
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
        if wp1(c)&&(std::env::var("C658_WP1_E5").as_deref()==Ok("1")
            ||std::env::var_os("C658_WP1_WF_SPLIT").is_none()){
            return super::super::bottom_comparator::witness_record3_e5(b,c,k,d);
        }
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


fn wp1(c:&Context<'_>)->bool{
    std::env::var("C658_WP1").as_deref()==Ok("1")&&c.traversal.has_payload()
}
fn wf_selected(c:&Context<'_>,gate:Gate,twin:bool)->bool{
    if !wp1(c){return false;}
    if std::env::var_os("C658_WP1_WF_SPLIT").is_none(){return true;}
    let key=if twin{"C658_WP1_WFTWIN"}else{match gate{
        Gate::Top(_)=>"C658_WP1_WFTOP",Gate::Bottom(_)=>"C658_WP1_WFBOT",
        Gate::Natural(_)=>"C658_WP1_WFTWIN"}};
    std::env::var(key).as_deref()==Ok("1")
}
fn wf_borrowed()->bool{std::env::var("C658_WP1_WF_BORROW").as_deref()==Ok("1")}
fn wf_guarded(twin:bool)->bool{
    if std::env::var_os("C658_WP1_WF_SPLIT").is_none(){return !twin;}
    std::env::var("C658_WP1_WF_GUARDED").as_deref()==Ok("1")
        &&(!twin||std::env::var("C658_WP1_WF_GUARDED_TWIN").as_deref()==Ok("1"))
}
fn borrow_host(c:&Context<'_>,t:&[QubitId])->QubitId{
    *c.ring.iter().find(|q|!t.contains(q)).expect("K5_WF_BORROW_HOST")
}
fn fp3_on(c:&Context<'_>,prefix:bool)->bool{prefix&&c.traversal.has_payload()
    &&std::env::var("C658_FP3").as_deref()==Ok("1")}
fn fp3_top_narrow(b:&mut B,c:&Context<'_>,j:usize,d:&[QubitId])->Vec<G>{
    assert!(j<15);let a=c.roles.activity;let q127=c.q[127];
    let ey=cover(&c.size.y,128-j,128);
    let es=cover(&c.size.sum,32-j,32);
    let mut negative=ey.clone();negative.extend(product(cover(&c.size.y,0,128-j),es.clone()));
    let mut union=ey.clone();union.extend(es);union.extend(product(ey,cover(&c.size.sum,32-j,32)));
    let price=|t:&[Vec<(QubitId,bool)>]|t.iter().map(|x|match x.len()+1{0|1=>0,2=>1,n=>4*(n-2)}).sum::<usize>();
    if price(&union)<price(&negative){negative=union;}
    let positive=c.gate_terms(Gate::Top(j));
    let complement=price(&positive)<price(&negative);
    let terms=if complement{positive}else{negative};
    rec(b,|b|{if complement{b.cx(a,q127);}xor_terms(b,&terms,q127,&[(a,false)],d);})
}
/// HT K2's natural Divide/Inplace uses the same WF TTK kernel as the HR
/// payload twin, with a public metadata-only Natural gate.
pub(crate) fn natural_divide_inplace_wf(b:&mut B,t:&[QubitId],q:&[QubitId],
    first:usize,a:QubitId,e:QubitId,sum:&[QubitId],k:usize,d:&[QubitId])->Vec<G>{
    assert_eq!(t.len(),129);assert_eq!(q.len(),128);assert!(k<30);
    let terms=cover(sum,0,32-k);
    b.begin();for &x in t{b.x(x);}
    k5_records::form_n_wf(b,&t[first..],&q[first..],a,e,sum,&terms,Op::Divide,d,Fault::None);
    for &x in t{b.x(x);}
    b.cx(e,t[128]);k5_records::wf_xor_terms(b,&terms,e,
        &[(a,false),(t[128],false)],d);b.cx(e,t[128]);b.end()
}
fn wf_close_inplace(b:&mut B,c:&Context<'_>,t:QubitId,
    gate_terms:&[Vec<(QubitId,bool)>],d:&[QubitId]){
    let r=c.roles;b.cx(r.flight,t);
    k5_records::wf_xor_terms(b,gate_terms,r.flight,&[(r.activity,false),(t,false)],d);
    b.cx(r.flight,t);
}
fn twin(dmode:&Arithmetic,b:&mut B,c:&Context<'_>,t:&[QubitId],gate:Gate,op:Op,close:Close,site:HrSite)->Vec<G>{
 c.check();assert!(!dmode.ht&&matches!(op,Op::Divide)&&matches!(gate,Gate::Natural(k) if k<30));
 match(site,close){(HrSite::PayloadTick,Close::None)|(HrSite::NoPayloadTwin,Close::Inplace)=>{},_=>panic!("K5_HR_SITE_CLOSE")}
 assert_eq!(c.traversal.has_payload(),matches!(site,HrSite::PayloadTick));
 assert_eq!(t.len(),129);if let Gate::Natural(k)=gate {assert_eq!(t,super::super::k5_ph_ports::natural_target(c,k),"K5_PH_TARGET_FRAME");}
 let first=128-c.y_bounds.1;assert!(first<=126);let r=c.roles;
 let mut used=BTreeSet::new();assert!(t.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
 .chain([r.activity,r.flight,r.mask]).filter(|q|super::super::c659::retained(*q)).all(|q|used.insert(q)));
 let dirty=c.bank(&[c.q[127]]);b.begin();
 if wf_selected(c,gate,true){let terms=c.gate_terms(gate);
     let guarded=wf_guarded(true);let guard=if guarded{witness(b,c,gate,&dirty)}else{vec![]};
     b.play(&guard,false);
     for &q in t{b.x(q);}
     if guarded{k5_records::form_n_wf_guarded(b,&t[first..],&c.q[first..],r.activity,r.flight,
             &c.size.sum,op,&dirty);
     }else if wf_borrowed(){let host=borrow_host(c,t);let d:Vec<_>=dirty.iter().copied().filter(|q|*q!=host).collect();
         k5_records::form_n_wf_borrowed(b,&t[first..],&c.q[first..],r.activity,r.flight,
             &c.size.sum,&terms,op,host,&d);
     }else{k5_records::form_n_wf(b,&t[first..],&c.q[first..],r.activity,r.flight,
         &c.size.sum,&terms,op,&dirty,Fault::None);}
     for &q in t{b.x(q);}
     if matches!(close,Close::Inplace){if guarded{b.cswap(r.activity,t[128],r.flight);}else{wf_close_inplace(b,c,t[128],&terms,&dirty);}}
     b.play(&guard,true);
 }else{let guard=witness(b,c,gate,&dirty);b.play(&guard,false);
     for &q in t{b.x(q);}ttk_natural(b,&t[first..],&c.q[first..],r.activity,r.flight,r.mask,&dirty);
     for &q in t{b.x(q);}if matches!(close,Close::Inplace){b.cswap(r.activity,t[128],r.flight);}
     b.play(&guard,true);}
 b.end()
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
        .chain([r.activity,r.flight,r.mask]).filter(|q|super::super::c659::retained(*q)).all(|q|ports.insert(q)));
    let dirty=c.bank(&[c.q[127]]);let add=matches!(op,Op::Add);let complement=matches!(op,Op::Divide);
    let fp3=fp3_on(c,prefix)&&fault==Fault::None&&matches!(op,Op::Divide|Op::Add);
    let wf=wf_selected(c,gate,false)&&!prefix&&fault==Fault::None;
    let guarded=wf&&!add&&wf_guarded(false);
    let held=wf&&!guarded&&matches!(gate,Gate::Bottom(_))&&std::env::var("C658_WP1_WF_HELDBOT").as_deref()==Ok("1");
    let terms=if held{vec![vec![(c.size.y[5],false)]]}else if wf{c.gate_terms(gate)}else{vec![]};
    let prep=if held{super::super::bottom_comparator::held_prep_record3(b,c,j,&dirty)}else{vec![]};
    let narrow=if fp3&&complement&&matches!(gate,Gate::Top(_)){fp3_top_narrow(b,c,j,&dirty)}else{vec![]};
    let fp3_prep=if fp3&&complement&&matches!(gate,Gate::Bottom(_)){
        super::super::bottom_comparator::fp3_prep_record3(b,c,j,&dirty)
    }else{vec![]};
    b.begin();let guard=if fp3||add||wf&&!guarded {vec![]}else{witness(b,c,gate,&dirty)};
    b.play(&guard,false);b.play(&prep,false);
    b.play(&narrow,false);
    if complement {for &q in t {b.x(q);}}
    if fp3{if add{k5_records::form_p3_add_ct(b,t,c.q,&c.size.y,r.activity,r.flight,14,&dirty);}
        else if matches!(gate,Gate::Top(_)){
            k5_records::form_p3_div(b,t,c.q,&c.size.y,r.activity,r.flight,14,&dirty,&[],
                |b,ctl,target|k5_records::wf_xor_terms(b,&[vec![(c.q[127],false)]],target,ctl,&dirty));
        }else{
            k5_records::form_p3_div(b,t,c.q,&c.size.y,r.activity,r.flight,14,&dirty,&fp3_prep,
                |b,ctl,target|super::super::bottom_comparator::fp3_xor_gate3_multi(b,c,j,ctl,target,&dirty));
        }}
    else if prefix {k5_records::form_p(b,t,c.q,&c.size.y,&c.size.sum,r.activity,r.flight,r.mask,14,op,&dirty,fault);}
    else if guarded{k5_records::form_n_wf_guarded(b,&t[first..],&c.q[first..],r.activity,r.flight,&c.size.sum,op,&dirty);}
    else if wf&&wf_borrowed(){let host=borrow_host(c,t);let d:Vec<_>=dirty.iter().copied().filter(|q|*q!=host).collect();
        k5_records::form_n_wf_borrowed(b,&t[first..],&c.q[first..],r.activity,r.flight,&c.size.sum,&terms,op,host,&d);}
    else if wf{k5_records::form_n_wf(b,&t[first..],&c.q[first..],r.activity,r.flight,&c.size.sum,&terms,op,&dirty,fault);}
    else {k5_records::form_n(b,&t[first..],&c.q[first..],r.activity,r.flight,r.mask,&c.size.sum,op,&dirty,fault);}
    if complement {for &q in t {b.x(q);}}
    if fp3{
        if let Close::EraseInplace(slot)=close{b.cx(r.flight,slot);}
        if matches!(close,Close::Inplace|Close::EraseInplace(_)){
            b.cx(r.flight,t[128]);
            if matches!(gate,Gate::Top(_)){
                k5_records::wf_xor_terms(b,&[vec![(c.q[127],false)]],r.flight,
                    &[(r.activity,false),(t[128],false)],&dirty);
            }else{
                b.play(&fp3_prep,false);
                super::super::bottom_comparator::fp3_xor_gate3_multi(b,c,j,
                    &[(r.activity,false),(t[128],false)],r.flight,&dirty);
                b.play(&fp3_prep,true);
            }
            b.cx(r.flight,t[128]);
        }
    }else if wf&&!guarded{match close{
        Close::None=>{},
        Close::Inplace=>wf_close_inplace(b,c,t[128],&terms,&dirty),
        Close::EraseInplace(slot)=>{b.cx(r.flight,slot);wf_close_inplace(b,c,t[128],&terms,&dirty);},
        Close::Store(top)=>{
            if matches!(top,VTop::Frame(0)){for term in &terms{for l in cover(&c.size.sum,0,32-c.qb){
                let mut both=term.clone();both.extend(l);k5_records::wf_xor_terms(b,&[both],t[128],&[(r.activity,false)],&dirty);
            }}}else{k5_records::wf_xor_terms(b,&terms,t[128],&[(r.activity,false)],&dirty);}
            wf_close_inplace(b,c,t[128],&terms,&dirty);
        },
    }}else{
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
    }
    b.play(&narrow,true);b.play(&prep,true);b.play(&guard,true);b.end()
}

#[cfg(test)]
pub(crate) fn r14_fixture_twin(b:&mut B,c:&Context<'_>,t:&[QubitId],k:usize)->Vec<G>{
    twin(&Arithmetic::hr(HrSite::PayloadTick),b,c,t,Gate::Natural(k),Op::Divide,
        Close::None,HrSite::PayloadTick)
}

#[cfg(test)]
pub(crate) fn r14_fixture_record(b:&mut B,c:&Context<'_>,t:&[QubitId],gate:Gate,
    ht:bool,source:Source,kind:usize,close_kind:usize)->Vec<G>{
    let op=match kind{0=>Op::Divide,1=>Op::Add,2=>Op::VBit(match gate{
        Gate::Top(j)=>VTop::Frame(j),Gate::Bottom(_)=>VTop::Zero,_=>panic!("gate")}),
        _=>panic!("kind")};
    let close=match close_kind{0=>Close::None,1=>Close::Inplace,
        2=>Close::EraseInplace(super::super::k5_ph_ports::park(c,match gate{
            Gate::Top(j)|Gate::Bottom(j)=>j,_=>panic!("gate")})),
        3=>Close::Store(match op{Op::VBit(v)=>v,_=>panic!("store")}),_=>panic!("close")};
    record(&Arithmetic::controller(ht,source),b,c,t,gate,op,close,Fault::None)
}

#[cfg(test)]
pub(crate) fn diagnostic(b:&mut B,c:&Context<'_>,t:&[QubitId],ht:bool,source:Source,kind:usize,fault_id:usize)->Vec<G>{
 let fault=match fault_id{0=>Fault::None,1=>Fault::RootOnQ127,2=>Fault::MissingParityConjugation,3=>Fault::DroppedS2,_=>panic!("fault id")};
 let(op,gate)=match kind{0=>(Op::Divide,Gate::Bottom(0)),1=>(Op::VBit(VTop::Zero),Gate::Bottom(0)),2=>(Op::Add,Gate::Bottom(0)),_=>panic!("kind")};
 record(&Arithmetic::controller(ht,source),b,c,t,gate,op,Close::None,fault)
}
