//! Guarded low3 normal-domain adapter. Explicit short-tail endpoints excluded.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
#[path="q793_t10_low_v2.rs"]mod plan;
#[path="metadata_phase115_programs.rs"]mod phases;
#[path="metadata_arithmetic5_programs.rs"]mod arithmetic;
type Terms<'a>=Vec<Vec<(&'a QReg,bool)>>;
fn szero<'a>(rank:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,j:usize,shift:usize,c1:bool)->Terms<'a>{
    if j%2!=shift{return Vec::new();}let c0=(j>>1)^(j&1);
    if c1&&c0!=1{return Vec::new();}
    phases::S_ZERO[0].iter().map(|&(m,v)|{let mut cs=vec![(g,true)];if!c1{cs.push((&c[0],c0!=0));}cs.extend(sm.iter().map(|q|(q,false)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()
}
fn c1<'a>(rank:&'a[QReg],c:&'a[QReg])->Terms<'a>{phases::C_EQUAL[0].iter().map(|&(m,v)|{let mut cs:Vec<_>=c.iter().enumerate().map(|(i,q)|(q,i==0)).collect();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()}
fn a252<'a>(rank:&'a[QReg],a:&'a[QReg])->Terms<'a>{arithmetic::A_EQUAL[3].iter().map(|&(m,v)|{let mut cs:Vec<_>=a.iter().enumerate().map(|(i,q)|(q,60>>i&1!=0)).collect();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()}
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]){super::q794_t10_quotient::gate(circ,cs,target,dirty);}

fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,t:&[QReg],b:&[QReg],h:Option<&QReg>,carry:&QReg,p:&QReg,dirty:&[QReg],j:usize,last:bool,sub:bool){
    let zero=szero(rank,c,sm,g,j,0,last);let one=szero(rank,c,sm,g,j,1,last);let mut other=vec![vec![(g,true)]];other.extend(zero.clone());other.extend(one.clone());
    let c_one=if last{Vec::new()}else{c1(rank,c)};let a_edge=if last{Vec::new()}else{a252(rank,a)};
    for(shift,bases)in[(0,zero),(1,one),(2,other)]{
        if bases.is_empty(){continue;}
        let l=plan::Layout::new(3,shift);let mut ops=Vec::new();if sub{plan::low_sub(&mut ops,l);}else{plan::low_borrow(&mut ops,l);}
        for op in ops{
            let target=match op.target{3..=5=>&b[op.target-3],12=>carry,_=>panic!("unexpected normal low target")};
            let mut literals=Vec::new();let mut h_term=false;let mut v2_term=false;
            for(id,value)in op.controls{if id==l.guard{assert!(value);continue;}
                let q=match id{0..=2=>&t[id],3..=5=>&b[id-3],7=>&b[257],8=>{v2_term=true;&b[256-shift]},9=>&b[258],11=>{h_term=true;if last{continue;}h.expect("remaining quotient route required")},13=>p,_=>panic!("unexpected normal low control {id}")};
                // A positive h factor vanishes identically for C=1.
                if id==11&&last{unreachable!();}literals.push((q,value));
            }
            if h_term&&last{continue;}
            for base in &bases{
                let mut cs=base.clone();cs.extend(literals.iter().copied());gate(circ,&cs,target,dirty);
                // In the general branch h has no semantic digit for C1;
                // this cancellation also prevents reading its dirty carry host.
                if h_term{for cond in &c_one{let mut q=cs.clone();q.extend(cond.iter().copied());gate(circ,&q,target,dirty);}}
                // In S1,A252,C!=1 the physical v2 rail holds second cargo.
                // Its logical value is the known-zero second-cargo base.
                if shift==1&&v2_term&&!last{for edge in &a_edge{
                    let mut q=cs.clone();q.extend(edge.iter().copied());gate(circ,&q,target,dirty);
                    for cond in &c_one{let mut z=q.clone();z.extend(cond.iter().copied());gate(circ,&z,target,dirty);}
                }}
            }
        }
    }
}
pub(super) fn borrow(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,t:&[QReg],b:&[QReg],carry:&QReg,p:&QReg,dirty:&[QReg],j:usize,last:bool){
    let owned=circ.b.next_qubit;
    if last||j%2!=0{emit(circ,rank,a,c,sm,g,t,b,None,carry,p,dirty,j,last,false);}
    else{let(h,route)=super::q793_t10_quotient_normal::remaining(circ,rank,a,c,t,dirty);emit(circ,rank,a,c,sm,g,t,b,Some(h),carry,p,dirty,j,last,false);circ.b.ops.extend(route.into_iter().rev());}
    assert_eq!(circ.b.next_qubit,owned);
}
pub(super) fn sub(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,t:&[QReg],b:&[QReg],carry:&QReg,p:&QReg,dirty:&[QReg],j:usize,last:bool){emit(circ,rank,a,c,sm,g,t,b,None,carry,p,dirty,j,last,true);}
