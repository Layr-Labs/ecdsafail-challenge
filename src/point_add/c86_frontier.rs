//! Exact all-input signed-permutation rewrites. No measurement/classical operations.
//! Frozen catalog: C86-catalog.py exhaustively enumerates <=3 gates, <=1 nonlinear.
use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT,NO_QUBIT};
use std::collections::HashMap;
#[derive(Clone,Copy)] struct Gate { k: K, a:usize,b:usize,t:usize }
fn alphabet(n:usize)->Vec<Gate>{
    let mut a=vec![Gate{k:K::Neg,a:0,b:0,t:0}];
    for k in [K::X,K::Z]{for t in 0..n{a.push(Gate{k,a:0,b:0,t});}}
    for k in [K::CX,K::CZ,K::Swap]{for b in 0..n{for t in 0..n{if b!=t&&(k==K::CX||b<t){a.push(Gate{k,a:0,b,t});}}}}
    for x in 0..n{for b in x+1..n{for t in 0..n{if t!=x&&t!=b{a.push(Gate{k:K::CCX,a:x,b,t});}}}}
    for x in 0..n{for b in x+1..n{for t in b+1..n{a.push(Gate{k:K::CCZ,a:x,b,t});}}} a
}
fn identity(n:usize)->[u16;5]{let mut v=[0;5];for b in 0..n{for x in 0..1<<n{v[b]|=(((x>>b)&1)as u16)<<x;}}v}
fn step(v:&mut [u16;5],g:Gate,n:usize){let m=if n==4{u16::MAX}else{255};match g.k{
    K::Neg=>v[n]^=m,K::X=>v[g.t]^=m,K::Z=>v[n]^=v[g.t],K::CX=>v[g.t]^=v[g.b],
    K::CZ=>v[n]^=v[g.b]&v[g.t],K::Swap=>v.swap(g.b,g.t),K::CCX=>v[g.t]^=v[g.a]&v[g.b],
    K::CCZ=>v[n]^=v[g.a]&v[g.b]&v[g.t],_=>unreachable!()}}
fn sig(v:&[u16;5])->u128{v.iter().enumerate().map(|(i,&x)|(x as u128)<<(16*i)).sum()}
#[derive(Clone,Copy)]struct Word{n:usize,w:[u8;3],cost:usize}
fn catalog(data:&[u8],n:usize)->HashMap<u128,Word>{
    let count=u32::from_le_bytes(data[..4].try_into().unwrap())as usize;assert_eq!(data.len(),4+21*count);
    let alpha=alphabet(n);let mut out=HashMap::new();
    for r in data[4..].chunks_exact(21){let key=u128::from_le_bytes(r[..16].try_into().unwrap());let z=r[16]as usize;
        let w=Word{n:z,w:r[17..20].try_into().unwrap(),cost:r[20]as usize};assert!(z<=3);
        let mut v=identity(n);for &i in &w.w[..z]{step(&mut v,alpha[i as usize],n);}assert_eq!(sig(&v),key,"corrupt catalog");
        assert!(out.insert(key,w).is_none());
    } out
}
fn nonlinear(k:K)->bool{matches!(k,K::CCX|K::CCZ)}
fn pure(o:&Op)->bool{o.c_condition==NO_BIT&&matches!(o.kind,K::Neg|K::X|K::Z|K::CX|K::CZ|K::Swap|K::CCX|K::CCZ)}
fn local(o:&Op,ws:&[QubitId])->Gate{let ix=|q|ws.iter().position(|&x|x==q).unwrap();
    Gate{k:o.kind,a:if o.q_control2!=NO_QUBIT{ix(o.q_control2)}else{0},b:if o.q_control1!=NO_QUBIT{ix(o.q_control1)}else{0},t:if o.q_target!=NO_QUBIT{ix(o.q_target)}else{0}}}
fn materialize(g:Gate,ws:&[QubitId])->Op{let mut o=Op::empty();o.kind=g.k;
    if g.k!=K::Neg{o.q_target=ws[g.t];}if matches!(g.k,K::CX|K::CZ|K::Swap|K::CCX|K::CCZ){o.q_control1=ws[g.b];}
    if nonlinear(g.k){o.q_control2=ws[g.a];}o.validate();o}
fn scalar(word:&[Op],ws:&[QubitId],mut x:usize)->(usize,bool){let mut p=false;
    for o in word{let g=local(o,ws);let b=|q:usize|(x>>q)&1;match g.k{
        K::Neg=>p=!p,K::X=>x^=1<<g.t,K::Z=>p^=b(g.t)!=0,K::CX=>x^=b(g.b)<<g.t,
        K::CZ=>p^=(b(g.b)&b(g.t))!=0,K::Swap=>{if b(g.b)!=b(g.t){x^=(1<<g.b)|(1<<g.t);}},
        K::CCX=>x^=(b(g.a)&b(g.b))<<g.t,K::CCZ=>p^=(b(g.a)&b(g.b)&b(g.t))!=0,_=>unreachable!()}}
    (x,p)
}
pub(crate) fn apply(ops:Vec<Op>)->Vec<Op>{
    let c3=catalog(include_bytes!("c86_catalog3.bin"),3);let c4=catalog(include_bytes!("c86_catalog4.bin"),4);
    let a3=alphabet(3);let a4=alphabet(4);let before=ops.iter().filter(|o|nonlinear(o.kind)).count();
    let mut out:Vec<Op>=Vec::with_capacity(ops.len());let mut depth=0usize;let mut run=0usize;let mut hits=0usize;let mut windows=0usize;
    for o in ops{if o.kind==K::PushCondition{depth+=1;}if o.kind==K::PopCondition{depth=depth.checked_sub(1).unwrap();}
        let ok=depth==0&&pure(&o);out.push(o);if !ok{run=0;continue;}run+=1;
        loop{let mut changed=false;
            for len in (2..=7.min(run)).rev(){let start=out.len()-len;let win=&out[start..];
                let cost=win.iter().filter(|o|nonlinear(o.kind)).count();if cost<2{continue;}
                let mut ws=Vec::with_capacity(4);for q in win.iter().flat_map(|x|[x.q_control2,x.q_control1,x.q_target]){if q!=NO_QUBIT&&!ws.contains(&q){ws.push(q);}}
                let n=ws.len();if n!=3&&n!=4{continue;}windows+=1;
                let mut v=identity(n);for x in win{step(&mut v,local(x,&ws),n);}let cat=if n==3{&c3}else{&c4};
                if let Some(w)=cat.get(&sig(&v)){if w.cost>=cost{continue;}let alpha=if n==3{&a3}else{&a4};
                    let rep:Vec<Op>=w.w[..w.n].iter().map(|&i|materialize(alpha[i as usize],&ws)).collect();
                    // Independent scalar checker at every application: all outputs AND phase.
                    for x in 0..1<<n{assert_eq!(scalar(win,&ws,x),scalar(&rep,&ws,x),"C86 signed permutation mismatch");}
                    out.truncate(start);out.extend(rep);run=run-len+w.n;hits+=1;changed=true;break;
                }
            }if !changed{break;}
        }
    }
    let after=out.iter().filter(|o|nonlinear(o.kind)).count();eprintln!("C86_FRONTIER windows={windows} hits={hits} nonlinear_before={before} nonlinear_after={after} delta={}",after as i64-before as i64);out
}
