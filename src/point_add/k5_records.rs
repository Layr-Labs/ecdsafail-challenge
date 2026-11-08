//! Carry-free record bodies only. PH/controller-cycle integration is separate.
//! Source lineage: middle.md Forms N/P, retaining the original witness/close ABI.
use super::*;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum Fault { None, RootOnQ127, MissingParityConjugation, DroppedS2 }

impl D {
    /// Diagnostic caller, explicit arithmetic/source/frame/carry dimensions.
    /// No production call site or environment knob selects this constructor.
    #[cfg(test)]
    pub(super) fn k5_records(ht:bool,source:SourcePolicy,c:&Cross<'_>,gate:Gate)->Self {
        assert!(matches!(source,SourcePolicy::Parked|SourcePolicy::EmptyQ),"K5_SELECTOR_SOURCE");
        let hi=match gate {Gate::Top(j)=>{assert!(j<15);c.y_bounds.1.min(128-j)},Gate::Bottom(j)=>{assert!(j<15);c.y_bounds.1},Gate::Natural(_)=>panic!("K5_SELECTOR_NATURAL")};
        let payload_open=source==SourcePolicy::EmptyQ&&hi>=115;
        let body=if source==SourcePolicy::Parked&&hi>=115{ArithmeticBody::K5FormP}else{ArithmeticBody::K5FormN};
        Self{ht,payload_open,contract:ArithmeticContract {
            body,caller:ArithmeticCaller::K5RecordsDiagnostic,carry:CarrySource::None,
            source,frame:ArithmeticFrame::Controller129Record,
        }}
    }
}

fn split_terms(sum:&[QubitId],low:bool)->Vec<Vec<(QubitId,bool)>> {
    assert_eq!(sum.len(),5);
    if low {cover(sum,0,2)} else {cover(sum,2,32)}
}

/// Form N on the same pre-complemented coordinates as the parent ladder.
/// m=0 globally; q[n-1]=1 on narrowed activity. Add requires e=>A&Gate.
pub(super) fn form_n(b:&mut B,t:&[QubitId],q:&[QubitId],a:QubitId,e:QubitId,m:QubitId,
    sum:&[QubitId],op:Op,d:&[QubitId],fault:Fault) {
    let n=q.len();assert!(n>=2);assert_eq!(t.len(),n+1);
    assert!(matches!(fault,Fault::None|Fault::DroppedS2));
    let add=matches!(op,Op::Add);let split=matches!(op,Op::VBit(VTop::Frame(0)));
    for i in 1..n {b.cx(q[i],t[i]);}
    for i in (1..n-1).rev() {if fault!=Fault::DroppedS2||i!=n-2 {b.cx(q[i],q[i+1]);}}
    for i in 0..n-1 {b.ccx(q[i],t[i],q[i+1]);}
    b.ccx(q[n-1],t[n-1],m);
    if add {lit(b,&[(e,false),(m,true)],t[n],d);}
    else {
        if split {
            let terms=split_terms(sum,true);
            xor_terms(b,&terms,e,&[(a,false)],d);
            xor_terms(b,&terms,e,&[(a,false),(t[n],false),(m,true)],d);
        } else {b.cx(a,e);lit(b,&[(a,false),(t[n],false),(m,true)],e,d);}
        lit(b,&[(a,false),(e,false),(m,true)],t[n],d);
        if split {xor_terms(b,&split_terms(sum,false),e,&[(a,false),(m,false)],d);}
    }
    b.ccx(q[n-1],t[n-1],m);
    if add {b.cx(e,m);} else {b.ccx(a,e,m);}
    for i in (1..n).rev() {b.ccx(m,q[i],t[i]);b.ccx(q[i-1],t[i-1],q[i]);}
    b.ccx(m,q[0],t[0]);
    if add {b.cx(e,m);} else {b.ccx(a,e,m);}
    for i in 1..n-1 {b.cx(q[i],q[i+1]);}
    for i in 1..n {b.cx(q[i],t[i]);}
}



/// Merge metadata cover terms with extra literals. A repeated literal is
/// kept once; a contradictory intersection contributes no XOR term.
pub(super) fn wf_xor_terms(b:&mut B,terms:&[Vec<(QubitId,bool)>],target:QubitId,
    extra:&[(QubitId,bool)],d:&[QubitId]){
    for term in terms{
        let mut all:Vec<(QubitId,bool)>=vec![];let mut contradiction=false;
        for &(q,neg) in term.iter().chain(extra){
            if let Some((_,old))=all.iter().find(|x|x.0==q){
                if *old!=neg{contradiction=true;break;}
            }else{all.push((q,neg));}
        }
        if !contradiction{lit(b,&all,target,d);}
    }
}

/// WF / WF-ADD body, on the parent's complemented target coordinate.
/// Exact against form_n on the inherited e=>A&Gate entry support.
pub(super) fn form_n_wf(b:&mut B,t:&[QubitId],q:&[QubitId],a:QubitId,e:QubitId,
    sum:&[QubitId],gate_terms:&[Vec<(QubitId,bool)>],op:Op,d:&[QubitId],fault:Fault){
    let n=q.len();assert!(n>=2&&t.len()==n+1&&fault==Fault::None);
    let add=matches!(op,Op::Add);let split=matches!(op,Op::VBit(VTop::Frame(0)));
    for i in 1..n{b.cx(q[i],t[i]);}
    for i in (1..n-1).rev(){b.cx(q[i],q[i+1]);}
    for i in 0..n-1{b.ccx(q[i],t[i],q[i+1]);}
    let cc=[(q[n-1],false),(t[n-1],false)];
    if add{
        b.cx(e,t[n]);lit(b,&[(e,false),cc[0],cc[1]],t[n],d);
    }else{
        let l=if split{split_terms(sum,true)}else{vec![vec![]]};
        for gate in gate_terms{for term in &l{
            let mut both=gate.clone();both.extend_from_slice(term);
            wf_xor_terms(b,&[both.clone()],e,&[(a,false),(t[n],true)],d);
            wf_xor_terms(b,&[both],e,&[(a,false),(t[n],false),cc[0],cc[1]],d);
        }}
        b.cx(e,t[n]);lit(b,&[(e,false),cc[0],cc[1]],t[n],d);
        if split{for gate in gate_terms{for term in split_terms(sum,false){
            let mut both=gate.clone();both.extend(term);
            wf_xor_terms(b,&[both],e,&[(a,false),cc[0],cc[1]],d);
        }}}
    }
    for i in (1..n).rev(){b.ccx(e,q[i],t[i]);b.ccx(q[i-1],t[i-1],q[i]);}
    b.ccx(e,q[0],t[0]);
    for i in 1..n-1{b.cx(q[i],q[i+1]);}
    for i in 1..n{b.cx(q[i],t[i]);}
}
/// Exact borrowed-bit implementation of the gate-dependent WF decision.
/// The two passes cancel an arbitrary initial value of `host`. Neither pass
/// reads `e`, and the data controls are unchanged until both passes finish.
pub(super) fn form_n_wf_borrowed(b:&mut B,t:&[QubitId],q:&[QubitId],a:QubitId,e:QubitId,
    sum:&[QubitId],gate_terms:&[Vec<(QubitId,bool)>],op:Op,host:QubitId,d:&[QubitId]){
    let n=q.len();assert!(n>=2&&t.len()==n+1);
    let add=matches!(op,Op::Add);let split=matches!(op,Op::VBit(VTop::Frame(0)));
    for i in 1..n{b.cx(q[i],t[i]);}
    for i in (1..n-1).rev(){b.cx(q[i],q[i+1]);}
    for i in 0..n-1{b.ccx(q[i],t[i],q[i+1]);}
    let cc=[(q[n-1],false),(t[n-1],false)];
    if add{
        b.cx(e,t[n]);lit(b,&[(e,false),cc[0],cc[1]],t[n],d);
    }else{
        let low=if split{split_terms(sum,true)}else{vec![vec![]]};
        let apply=|b:&mut B|{
            for term in &low{
                let mut condition=term.clone();condition.push((host,false));
                wf_xor_terms(b,&[condition.clone()],e,&[(a,false),(t[n],true)],d);
                wf_xor_terms(b,&[condition],e,&[(a,false),(t[n],false),cc[0],cc[1]],d);
            }
        };
        wf_xor_terms(b,gate_terms,host,&[],d);apply(b);
        wf_xor_terms(b,gate_terms,host,&[],d);apply(b);
        b.cx(e,t[n]);lit(b,&[(e,false),cc[0],cc[1]],t[n],d);
        if split{
            let apply_high=|b:&mut B|for term in split_terms(sum,false){
                let mut condition=term;condition.push((host,false));
                wf_xor_terms(b,&[condition],e,&[(a,false),cc[0],cc[1]],d);
            };
            wf_xor_terms(b,gate_terms,host,&[],d);apply_high(b);
            wf_xor_terms(b,gate_terms,host,&[],d);apply_high(b);
        }
    }
    for i in (1..n).rev(){b.ccx(e,q[i],t[i]);b.ccx(q[i-1],t[i-1],q[i]);}
    b.ccx(e,q[0],t[0]);
    for i in 1..n-1{b.cx(q[i],q[i+1]);}
    for i in 1..n{b.cx(q[i],t[i]);}
}
/// Witness-preserving two-lane Form N. The caller's guard encodes active
/// gate shots as (a,e)=(1,0), skipped shots as (0,1), and inactive shots
/// as (0,0). Every read of e is conjoined with a, so the skipped witness
/// remains inert and the metadata gate is decoded only by the outer guard.
pub(super) fn form_n_wf_guarded(b:&mut B,t:&[QubitId],q:&[QubitId],a:QubitId,e:QubitId,
    sum:&[QubitId],op:Op,d:&[QubitId]){
    let n=q.len();assert!(n>=2&&t.len()==n+1&&!matches!(op,Op::Add));
    let split=matches!(op,Op::VBit(VTop::Frame(0)));
    for i in 1..n{b.cx(q[i],t[i]);}
    for i in (1..n-1).rev(){b.cx(q[i],q[i+1]);}
    for i in 0..n-1{b.ccx(q[i],t[i],q[i+1]);}
    let cc=[(q[n-1],false),(t[n-1],false)];
    let low=if split{split_terms(sum,true)}else{vec![vec![]]};
    for term in &low{
        wf_xor_terms(b,&[term.clone()],e,&[(a,false),(t[n],true)],d);
        wf_xor_terms(b,&[term.clone()],e,&[(a,false),(t[n],false),cc[0],cc[1]],d);
    }
    b.ccx(a,e,t[n]);lit(b,&[(a,false),(e,false),cc[0],cc[1]],t[n],d);
    if split{for term in split_terms(sum,false){
        wf_xor_terms(b,&[term],e,&[(a,false),cc[0],cc[1]],d);
    }}
    for i in (1..n).rev(){lit(b,&[(a,false),(e,false),(q[i],false)],t[i],d);b.ccx(q[i-1],t[i-1],q[i]);}
    lit(b,&[(a,false),(e,false),(q[0],false)],t[0],d);
    for i in 1..n-1{b.cx(q[i],q[i+1]);}
    for i in 1..n{b.cx(q[i],t[i]);}
}
/// For the real 14-cell prefix retain the exact parity14 recipe/cursor.
/// Reduced-width tests use an explicit XOR of the identical decoder leaves;
/// this is a reversible parity on arbitrary metadata, not a one-hot shortcut.
pub(super) fn parity(b:&mut B,p:&mut Prefix<'_>,out:QubitId,cells:usize) {
    assert!((1..=14).contains(&cells));
    if cells==14 {assert_eq!(p.cur,Some(2));parity14(b,p,out);}
    else {
        for i in (0..cells).rev() {p.goto(b,15-i);p.xor_eq(b,out);}
        p.goto(b,16-cells);
    }
}

fn sweep(b:&mut B,t:&[QubitId],q:&[QubitId],meta:&[QubitId],a:QubitId,e:QubitId,m:QubitId,
    cells:usize,add:bool,down:bool,d:&[QubitId],fault:Fault) {
    let correct_root=if add {a}else{e};
    let root=if fault==Fault::RootOnQ127 {q[q.len()-1]}else{correct_root};
    let parity_lane=if add {m}else{a};let write=if add {e}else{m};
    let conjugate=!add&&fault!=Fault::MissingParityConjugation;
    if conjugate {b.x(parity_lane);}
    let mut p=Prefix{e:meta,root,cur:None};
    // Divide/VBit enter deliberately omits the parent's root X. Do not emit
    // a compensating X pair: raw source counts must expose the actual form.
    if add {p.enter(b,d);} else {
        lit(b,&[(meta[4],false),(meta[5],false),(meta[6],false)],root,d);
        for &q in &meta[4..7] {b.x(q);}
    }
    p.goto(b,16-cells);parity(b,&mut p,parity_lane,cells);
    for i in (0..cells).rev() {
        p.goto(b,15-i);
        if down {
            lit(b,&[(parity_lane,false),(q[i],false),(t[i],false)],q[i+1],d);
            lit(b,&[(write,false),(parity_lane,false),(q[i],false)],t[i],d);
        } else {b.ccx(parity_lane,q[i],q[i+1]);}
        p.xor_eq(b,parity_lane);
    }
    for i in 0..cells {
        p.goto(b,15-i);p.xor_eq(b,parity_lane);
        if down {b.ccx(parity_lane,q[i],q[i+1]);}
        else {lit(b,&[(parity_lane,false),(q[i],false),(t[i],false)],q[i+1],d);}
    }
    parity(b,&mut p,parity_lane,cells);
    if add {p.leave(b,d);} else {
        if let Some(v)=p.cur {for i in (0..3).rev() {p.cell(b,i,v);}}
        for &q in &meta[4..7] {b.x(q);}
        lit(b,&[(meta[4],false),(meta[5],false),(meta[6],false)],root,d);
    }
    if conjugate {b.x(parity_lane);}
}

/// FP3's role-parametric prefix sweep. The original `sweep` above is kept
/// intact for gate-off source identity.
fn sweep_fp3(b:&mut B,t:&[QubitId],q:&[QubitId],meta:&[QubitId],
    root:QubitId,pl:QubitId,write:QubitId,conj:bool,add_enter:bool,
    cells:usize,down:bool,d:&[QubitId]){
    if conj{b.x(pl);}
    let mut p=Prefix{e:meta,root,cur:None};
    if add_enter{p.enter(b,d);}else{
        lit(b,&[(meta[4],false),(meta[5],false),(meta[6],false)],root,d);
        for &x in &meta[4..7]{b.x(x);}
    }
    p.goto(b,16-cells);parity(b,&mut p,pl,cells);
    for i in (0..cells).rev(){
        p.goto(b,15-i);
        if down{
            lit(b,&[(pl,false),(q[i],false),(t[i],false)],q[i+1],d);
            lit(b,&[(write,false),(pl,false),(q[i],false)],t[i],d);
        }else{b.ccx(pl,q[i],q[i+1]);}
        p.xor_eq(b,pl);
    }
    for i in 0..cells{
        p.goto(b,15-i);p.xor_eq(b,pl);
        if down{b.ccx(pl,q[i],q[i+1]);}
        else{lit(b,&[(pl,false),(q[i],false),(t[i],false)],q[i+1],d);}
    }
    parity(b,&mut p,pl,cells);
    if add_enter{p.leave(b,d);}else{
        if let Some(v)=p.cur{for i in (0..3).rev(){p.cell(b,i,v);}}
        for &x in &meta[4..7]{b.x(x);}
        lit(b,&[(meta[4],false),(meta[5],false),(meta[6],false)],root,d);
    }
    if conj{b.x(pl);}
}

/// FP3 ADD-CT: q[n-1] is a clean parity lane on A and remains unwritten.
pub(super) fn form_p3_add_ct(b:&mut B,t:&[QubitId],q:&[QubitId],meta:&[QubitId],
    a:QubitId,e:QubitId,cells:usize,d:&[QubitId]){
    let n=q.len();assert!(n>=3&&cells<=n-2&&t.len()==n+1&&meta.len()==7);
    let(top,s,y)=(q[n-1],q[n-2],t[n-1]);
    for i in 0..n{b.cx(q[i],t[i]);}
    lit(b,&[(e,false),(y,false),(s,false)],t[n],d);
    for i in (cells..n-2).rev(){b.cx(q[i],q[i+1]);}
    sweep_fp3(b,t,q,meta,a,top,e,true,true,cells,false,d);
    for i in cells..n-2{b.ccx(q[i],t[i],q[i+1]);}
    lit(b,&[(e,false),(y,false),(s,false),(t[n-2],false)],t[n],d);
    lit(b,&[(e,false),(y,true)],t[n],d);
    lit(b,&[(e,false),(s,false),(t[n-2],false)],y,d);
    b.cx(e,y);
    for i in (cells+1..n-1).rev(){b.ccx(e,q[i],t[i]);b.ccx(q[i-1],t[i-1],q[i]);}
    b.ccx(e,q[cells],t[cells]);
    sweep_fp3(b,t,q,meta,a,top,e,true,true,cells,true,d);
    for i in cells..n-2{b.cx(q[i],q[i+1]);}
    b.ccx(e,s,y);
    for i in 0..n{b.cx(q[i],t[i]);}
}

/// FP3 DIV-2P compare pass followed by ADD-CT. `gate_xor` implements
/// extra_controls & G -> e; `prep` is played only around gate groups.
pub(super) fn form_p3_div<F>(b:&mut B,t:&[QubitId],q:&[QubitId],meta:&[QubitId],
    a:QubitId,e:QubitId,cells:usize,d:&[QubitId],prep:&[G],mut gate_xor:F)
where F:FnMut(&mut B,&[(QubitId,bool)],QubitId){
    let n=q.len();assert!(n>=3&&cells<=n-2&&t.len()==n+1&&meta.len()==7);
    let(s,y,tau)=(q[n-2],t[n-1],t[n]);
    let pre={b.begin();for i in 0..n{b.cx(q[i],t[i]);}b.end()};
    b.play(&pre,false);
    b.play(prep,false);
    gate_xor(b,&[(a,false),(tau,false),(y,false),(s,false)],e);
    b.play(prep,true);
    let links={b.begin();for i in (cells..n-2).rev(){b.cx(q[i],q[i+1]);}b.end()};
    b.play(&links,false);
    let sweep={b.begin();sweep_fp3(b,t,q,meta,q[n-1],a,e,true,true,cells,false,d);b.end()};
    b.play(&sweep,false);
    let s3={b.begin();for i in cells..n-2{b.ccx(q[i],t[i],q[i+1]);}b.end()};
    b.play(&s3,false);
    b.play(prep,false);
    gate_xor(b,&[(a,false)],e);
    gate_xor(b,&[(a,false),(tau,false),(y,true)],e);
    gate_xor(b,&[(a,false),(tau,false),(y,false),(s,false),(t[n-2],false)],e);
    b.play(prep,true);
    b.play(&s3,true);b.play(&sweep,true);b.play(&links,true);b.play(&pre,true);
    form_p3_add_ct(b,t,q,meta,a,e,cells,d);
}

/// Form P keeps e untouched until END for Divide/VBit. Its forward contract
/// is e=0 on narrowed activity; skipped forward witnesses have A'=0,e'=1.
/// The inverse is always replayed on the complete own-forward image.
pub(super) fn form_p(b:&mut B,t:&[QubitId],q:&[QubitId],meta:&[QubitId],sum:&[QubitId],
    a:QubitId,e:QubitId,m:QubitId,cells:usize,op:Op,d:&[QubitId],fault:Fault) {
    let n=q.len();assert!(n>=2&&cells>0&&cells<n&&cells<=14);assert_eq!(t.len(),n+1);assert_eq!(meta.len(),7);
    let add=matches!(op,Op::Add);let split=matches!(op,Op::VBit(VTop::Frame(0)));
    for i in 0..n {b.cx(q[i],t[i]);}
    for i in (cells..n-1).rev() {if fault!=Fault::DroppedS2||i!=n-2 {b.cx(q[i],q[i+1]);}}
    sweep(b,t,q,meta,a,e,m,cells,add,false,d,fault);
    for i in cells..n-1 {b.ccx(q[i],t[i],q[i+1]);}
    if add {
        b.ccx(q[n-1],t[n-1],m);lit(b,&[(e,false),(m,true)],t[n],d);b.ccx(q[n-1],t[n-1],m);
    } else {
        if split {
            let terms=split_terms(sum,true);
            xor_terms(b,&terms,m,&[(a,false)],d);
            xor_terms(b,&terms,m,&[(a,false),(t[n],false)],d);
            xor_terms(b,&terms,m,&[(a,false),(t[n],false),(q[n-1],false),(t[n-1],false)],d);
        } else {
            b.cx(a,m);b.ccx(a,t[n],m);
            lit(b,&[(a,false),(t[n],false),(q[n-1],false),(t[n-1],false)],m,d);
        }
        b.cx(m,t[n]);lit(b,&[(m,false),(q[n-1],false),(t[n-1],false)],t[n],d);
        if split {xor_terms(b,&split_terms(sum,false),m,&[(a,false),(q[n-1],false),(t[n-1],false)],d);}
    }
    let write=if add {e}else{m};
    for i in (cells+1..n).rev() {b.ccx(write,q[i],t[i]);b.ccx(q[i-1],t[i-1],q[i]);}
    b.ccx(write,q[cells],t[cells]);
    sweep(b,t,q,meta,a,e,m,cells,add,true,d,fault);
    if !add {b.cx(m,e);b.ccx(a,e,m);}
    for i in cells..n-1 {b.cx(q[i],q[i+1]);}
    for i in 0..n {b.cx(q[i],t[i]);}
}

pub(super) fn record(dmode:&D,b:&mut B,c:&Cross<'_>,t:&[QubitId],gate:Gate,op:Op,close:Close,fault:Fault)->Vec<G> {
    assert_eq!(dmode.contract.caller,ArithmeticCaller::K5RecordsDiagnostic,"K5_SELECTOR_CALLER");
    assert_eq!(dmode.contract.frame,ArithmeticFrame::Controller129Record,"K5_SELECTOR_FRAME");
    assert_eq!(dmode.contract.carry,CarrySource::None,"K5_SELECTOR_CARRY");
    assert!(matches!(dmode.contract.source,SourcePolicy::Parked|SourcePolicy::EmptyQ),"K5_SELECTOR_SOURCE");
    assert_eq!((c.q.len(),c.size.y.len(),c.size.sum.len(),t.len()),(128,7,5,129));assert_eq!(c.qb,30);
    assert!(1<=c.y_bounds.0&&c.y_bounds.0<=c.y_bounds.1&&c.y_bounds.1<=128);
    let r=c.roles;let mut physical=BTreeSet::new();
    assert_eq!(c.ring.len(),257);
    assert!(c.ring.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
        .chain([c.phase,r.activity,r.flight,r.mask,r.x128]).all(|q|physical.insert(q)),"K5_SELECTOR_PORTS");
    let j=match gate {Gate::Top(j)|Gate::Bottom(j)=>{assert!(j<15,"K5_SELECTOR_INDEX");j},Gate::Natural(_)=>panic!("K5_SELECTOR_NATURAL")};
    match (op,close) {
        (Op::Add,Close::None)=>assert!(dmode.ht,"K5_SELECTOR_ADD_HR"),
        (Op::Divide,Close::None|Close::Inplace)=>{},
        (Op::Divide,Close::EraseInplace(slot))=>{
            assert_eq!(dmode.contract.source,SourcePolicy::Parked,"K5_SELECTOR_ERASE_POLICY");assert_eq!(slot,super::super::normalized_cross_frame::park(c,j),"K5_SELECTOR_ERASE_SLOT");
        },
        (Op::VBit(top),Close::None)|(Op::VBit(top),Close::Store(_))=>{
            match (gate,top) { (Gate::Top(g),VTop::Frame(v))=>assert_eq!(g,v,"K5_SELECTOR_VFRAME"),(Gate::Bottom(_),VTop::Zero)=>{},_=>panic!("K5_SELECTOR_VFRAME") }
            if let Close::Store(other)=close {assert!(matches!((top,other),(VTop::Zero,VTop::Zero))||matches!((top,other),(VTop::Frame(a),VTop::Frame(z)) if a==z));}
        },_=>panic!("K5_SELECTOR_CLOSE"),
    }
    if let Gate::Top(j)=gate {if c.y_bounds.0>128-j {return vec![];}}
    let hi=if let Gate::Top(j)=gate {c.y_bounds.1.min(128-j)}else{c.y_bounds.1};
    assert_eq!(dmode.payload_open,dmode.contract.source==SourcePolicy::EmptyQ&&hi>=115,"K5_SELECTOR_LEGACY_POLICY");
    let prefix=hi>=115&&!dmode.payload_open;
    assert_eq!(dmode.contract.body,if prefix {ArithmeticBody::K5FormP}else{ArithmeticBody::K5FormN},"K5_SELECTOR_BODY");
    let first=if prefix {14}else{128-hi};assert!(first<=126);
    let mut ports=BTreeSet::new();
    assert!(t.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
        .chain([r.activity,r.flight,r.mask]).all(|q|ports.insert(q)));
    let dirty=bank(c);let add=matches!(op,Op::Add);let complement=matches!(op,Op::Divide);
    b.begin();let guard=if add {vec![]}else{witness(b,c,gate,&dirty)};b.play(&guard,false);
    if complement {for &q in t {b.x(q);}}
    if prefix {form_p(b,t,c.q,&c.size.y,&c.size.sum,r.activity,r.flight,r.mask,14,op,&dirty,fault);}
    else {form_n(b,&t[first..],&c.q[first..],r.activity,r.flight,r.mask,&c.size.sum,op,&dirty,fault);}
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
