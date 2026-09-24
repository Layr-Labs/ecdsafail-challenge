//! One T-only H for the exact nine A253/254 geometries. Original rank29
//! lends mask=rank1(0), carry=rank3 XOR g(0); A8 uses rank0/rank2(1,1).
//! Both rank loans return before any rank-dependent cleanup. SM3 holds only
//! the three specified W2[255] phase passengers; SM0..2 park the low chart.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
const GEOMETRY:[(usize,usize,usize);9]=[(253,1,0),(253,1,1),(253,1,2),(253,2,0),(253,2,1),(253,3,0),(254,1,0),(254,1,1),(254,2,0)];
fn admitted(j:usize,cv:usize,s:usize)->bool{(j&1)+2*((j>>1)^(j&1)^(cv&1))==s}
fn gate(c:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,d:&[QReg]){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v)in cs{if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}else{unique.push((q,v));}}
    assert!(!unique.iter().any(|(q,_)|q.id()==out.id()));
    super::length_recompute::mixed_mcx(c,&unique,out,d);
}
fn guard(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg],j:usize){
    let ts=super::q792_fold20_rank_r01::triples();let rank=ts.iter().position(|&v|v==[3,0,0]).unwrap();let(lo,hi)=c.q797_a_support.unwrap_or((0,256));
    for(av,cv,s)in GEOMETRY{if av<lo||av>=hi||!admitted(j,cv,s){continue;}let code=super::q792_fold20_rank_r01::encode(rank,av&63,cv,0,&ts);let mut cs=vec![(p1,true),(p2,false)];cs.extend(m.iter().enumerate().map(|(i,q)|(q,code>>i&1!=0)));gate(c,&cs,g,d);}
}
fn geometry<'a>(a:&'a[QReg],cl:&'a[QReg],g:&'a QReg,av:usize,cv:usize)->Vec<(&'a QReg,bool)>{vec![(g,true),(&a[0],av==253),(&cl[0],cv&1!=0),(&cl[1],cv&2!=0)]}
fn swap(c:&mut Circuit,cs:&[(&QReg,bool)],left:&QReg,right:&QReg,d:&[QReg]){c.cx(right,left);let mut controls=cs.to_vec();controls.push((left,true));gate(c,&controls,right,d);c.cx(right,left);}
fn normalize(c:&mut Circuit,a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,w2:&[QReg],d:&[QReg],j:usize){
    for(av,cv,s)in GEOMETRY{if !admitted(j,cv,s)||!(cv==1||av==254&&cv==2){continue;}swap(c,&geometry(a,cl,g,av,cv),&sm[3],&w2[255],d);}
}
fn pop(c:&mut Circuit,a:&[QReg],cl:&[QReg],g:&QReg,p:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg],j:usize){
    for(av,cv,s)in GEOMETRY{if !admitted(j,cv,s){continue;}let geo=geometry(a,cl,g,av,cv);
        if cv==1{gate(c,&geo,p,d);if av==254{let mut even=geo.clone();even.push((&w1[0],false));gate(c,&even,&w2[2-s],d);}continue;}
        let endpoint=av+cv==256;let slot=&w2[if endpoint{1}else{2-s}];let mut even=geo.clone();even.push((&w1[0],false));swap(c,&even,p,slot,d);
        let mut odd=geo;odd.push((&w1[0],true));
        if endpoint||s==1{odd.push((&w2[0],false));gate(c,&odd,p,d);continue;}
        // Only A253/C2/S0 remains. Logical q1=1 and q2=0 replace the
        // independent phase/global passengers at W1[255]/W1[254].
        let inputs=[&w1[1],&w1[2],&w2[0],&w2[1],&w2[2],&w2[258],&w2[257]];
        let mut anf:Vec<_>=(0..128usize).map(|x|{let t=1+2*(x&3);let b=x>>2&7;let v=x>>5&3;v!=0&&(((71-b*v)*t+256-2*v)&7)>=v}).collect();
        for bit in 0..7{for value in 0..128{if value>>bit&1!=0{anf[value]^=anf[value^(1<<bit)];}}}
        for(term,on)in anf.into_iter().enumerate(){if on{let mut cs=odd.clone();cs.extend((0..7).filter(|&i|term>>i&1!=0).map(|i|(inputs[i],true)));gate(c,&cs,p,d);}}
    }
}
#[derive(Clone,Copy)]enum Input<'a>{Zero,One,Wire(&'a QReg)}
fn unpack(c:&mut Circuit,a:&[QReg],cl:&[QReg],sm:&[QReg],g:&QReg,p:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg],j:usize,inverse:bool){
    use Input::{Zero,One,Wire};let at=c.b.ops.len();
    for(av,cv,s)in GEOMETRY{if !admitted(j,cv,s){continue;}let mut base=geometry(a,cl,g,av,cv);base.push((&w1[0],false));
        let r:[&QReg;3]=std::array::from_fn(|k|&w2[(259+k-s)%259]);let m=av+cv;
        let vv=if m==256||s==2||m==255&&s==1{[One,Zero,Zero]}
            else if av==254&&cv==1{[Wire(&w2[258]),One,Zero]}
            else if m==255{[Wire(&w2[258]),Wire(&w2[257]),Zero]}
            else{std::array::from_fn(|k|Wire(&w2[258-s-k]))};
        let inputs=[Wire(&w1[1]),Wire(&w1[2]),if m==256{Zero}else{Wire(r[0])},if m==256{Zero}else{Wire(r[1])},Zero,vv[0],vv[1],vv[2],Wire(p),if cv==1{Zero}else if cv==2{One}else{Wire(&w2[2])},Zero];
        for out in 0..3-s{
            let mut anf:Vec<_>=(0..2048usize).map(|x|{let t=2*(x&3);let r=x>>2&7;let v=x>>5&7;let q=x>>8&7;(v.wrapping_mul(7usize.wrapping_sub(t*r)).wrapping_sub((q<<s)*t)>>(out+s))&1!=0}).collect();
            for bit in 0..11{for value in 0..2048{if value>>bit&1!=0{anf[value]^=anf[value^(1<<bit)];}}}
            for(term,on)in anf.into_iter().enumerate(){if !on{continue;}let mut cs=base.clone();let mut possible=true;
                for i in 0..11{if term>>i&1==0{continue;}match inputs[i]{Zero=>{possible=false;break;},One=>{},Wire(q)=>cs.push((q,true))}}
                if possible{gate(c,&cs,&sm[out],d);}
            }
        }
        for out in 0..3-s{swap(c,&base,&sm[out],r[s+out],d);}
    }
    if inverse{c.b.ops[at..].reverse();}
}
pub(super)fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],n:usize,j:usize){emit_with_loan(c,m,p1,p2,w1,w2,h,n,j,false);}
pub(super)fn emit_with_loan(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],_n:usize,j:usize,held:bool){
    assert_eq!(m.len(),20);assert_eq!(h.len(),23);assert!(j<4);if c.q797_a_support.is_some_and(|(lo,hi)|lo>=255||hi<=253){return;}let owned=c.b.next_qubit;let g=&h[0];let d=&h[1..];
    let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}
    guard(c,m,p1,p2,g,d,j);super::q792_unfold_lease_r01::emit(c,m,p2,g,d,false);
    let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p2)).map(QReg::borrowed_alias).collect();let a=&m[4..10];let cl=&m[10..16];let sm=&m[16..20];
    let at=c.b.ops.len();normalize(c,a,cl,sm,g,w2,d,j);let normalization=c.b.ops[at..].to_vec();
    c.cx(g,p1);pop(c,a,cl,g,p1,w1,w2,d,j);unpack(c,a,cl,sm,g,p1,w1,w2,d,j,false);
    let upper:Vec<_>=a.iter().chain([&rank[0],&rank[2]]).map(QReg::borrowed_alias).collect();c.cx(g,&rank[3]);
    super::q792_t_only_apex_h_r01::emit(c,&w1[..256],&w2[..256],&upper,p1,g,&rank[1],&rank[3],d);
    c.cx(g,&rank[3]);unpack(c,a,cl,sm,g,p1,w1,w2,d,j,true);c.cx(g,p1);c.b.ops.extend(normalization.into_iter().rev());
    super::q792_unfold_lease_r01::emit(c,m,p2,g,d,true);guard(c,m,p1,p2,g,d,j);if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}assert_eq!(c.b.next_qubit,owned);
}
#[path="q792_t_only_apex_check_r05.rs"]mod check;
pub fn run(){check::run();}
