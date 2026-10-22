//! Complete-Y arithmetic without a stored boundary mask.
//! The activity/flight witness replaces A by A & Gate while preserving the
//! excluded activity in e. All lower writes retain A explicitly.
use super::builder::{B,G};
use super::cross_three::{Cross,Gate,VTop};
use super::three_control::{literal,range,xor_terms};
use crate::circuit::QubitId;
#[derive(Clone,Copy)] enum Op{Divide,Add,VBit(VTop)}
pub(crate) struct D{pub ht:bool,pub payload_open:bool}
fn query(b:&mut B,c:&Cross<'_>,y:usize,top:Option<bool>,extra:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    let(lo,hi)=match top{Some(true)=>(32-c.qb,32),Some(false)=>(0,32-c.qb),None=>(0,32)};
    for s in range(&c.size.sum,lo,hi){for mut t in c.size.y_terms(y){t.extend_from_slice(&s);t.extend_from_slice(extra);literal(b,&t,target,dirty);}}
}
impl D{
    fn record(&self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,op:Op)->Vec<G>{
        let lo=c.y_bounds.0;let mut hi=c.y_bounds.1.min(target.len()-1);
        if let Gate::Top(j)=gate{hi=hi.min(128-j);}if lo>hi{return vec![];}
        let t=&target[..hi+1];let s=&c.q[..(hi+1).min(128)];let r=c.roles;
        let carry=if self.payload_open{r.work}else{c.phase};let dirty=c.bank(&[]);
        let guard=super::three_control::rec(b,|b|if !matches!(op,Op::Add){
            let terms=c.gate_terms(gate);
            for(control,target)in[(r.activity,r.flight),(r.flight,r.activity)]{
                b.cx(control,target);xor_terms(b,&terms,&[(control,false)],target,&dirty);
            }
        });
        b.begin();b.play(&guard,false);
        if !self.payload_open&&self.ht{b.cx(r.activity,c.phase);}
        if matches!(op,Op::Divide){for &q in t{b.x(q);}}
        for i in 0..s.len(){let x=if i==0{carry}else{s[i-1]};
            b.cx(s[i],t[i]);b.cx(s[i],x);b.ccx(x,t[i],s[i]);}
        for i in (0..t.len()).rev(){let x=if i==0{carry}else{s[i-1]};
            if i<s.len(){b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);}
            if i<hi{
                b.cx(s[i],x);
                if matches!(op,Op::Add){
                    xor_terms(b,&range(&c.size.y,i,128),&[(r.activity,false),(r.flight,false),(x,false)],t[i],&dirty);
                }else{literal(b,&[(r.activity,false),(r.flight,false),(x,false)],t[i],&dirty);}
                b.cx(s[i],x);
            }
            if matches!(op,Op::Add){
                if (lo..=hi).contains(&i){query(b,c,i,None,&[(r.activity,false),(r.flight,false),(x,false)],t[i],&dirty);}
                continue;
            }
            let split=matches!(op,Op::VBit(VTop::Frame(0)));
            for leading in [true,false]{if leading&&!split{continue;}
                let y=if leading{i+1}else{i};if !(lo..=hi).contains(&y){continue;}
                let top=if split{Some(leading)}else{None};
                if leading{
                    query(b,c,y,top,&[(r.activity,false),(t[i],true),(x,true)],r.flight,&dirty);
                    query(b,c,y,top,&[(r.activity,false),(r.flight,false)],t[i],&dirty);
                }else{
                    query(b,c,y,top,&[(r.activity,false)],r.flight,&dirty);
                    query(b,c,y,top,&[(r.activity,false),(t[i],false),(x,false)],r.flight,&dirty);
                    query(b,c,y,top,&[(r.activity,false),(r.flight,false),(x,false)],t[i],&dirty);
                }
            }
        }
        if matches!(op,Op::Divide){for &q in t{b.x(q);}}
        if !self.payload_open&&self.ht{b.cx(r.activity,c.phase);}
        b.play(&guard,true);b.end()
    }
    pub(crate) fn divide(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,inverse:bool){let a=self.record(b,c,t,g,Op::Divide);b.play(&a,inverse);}
    pub(crate) fn add(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate){let a=self.record(b,c,t,g,Op::Add);b.play(&a,false);}
    pub(crate) fn vbit(&mut self,b:&mut B,c:&Cross<'_>,t:&[QubitId],g:Gate,top:VTop){let a=self.record(b,c,t,g,Op::VBit(top));b.play(&a,false);}
}
