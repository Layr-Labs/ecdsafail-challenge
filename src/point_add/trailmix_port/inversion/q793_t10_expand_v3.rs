//! Funded one-rail mod8 -> mod4 T10 expansion, valid under held S<=2 guard.
//! SM3 supplies the original zero rail; SM1/SM2 hold M255/M256 flags.
//! Both flags and the borrowed rail are restored by the surrounding adapter.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
#[path="metadata_phase115_programs.rs"] mod phase;
#[path="metadata_arithmetic5_programs.rs"] mod arith;
type Term<'a>=Vec<(&'a QReg,bool)>;
type Poly<'a>=Vec<Term<'a>>;
fn norm<'a>(cs:Term<'a>)->Option<Term<'a>>{let mut out:Term<'a>=Vec::new();for(q,v)in cs{if let Some(&(_,old))=out.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return None;}}else{out.push((q,v));}}out.sort_by_key(|x|x.0.id());Some(out)}
fn tidy<'a>(p:Poly<'a>)->Poly<'a>{let mut map=std::collections::BTreeMap::new();for t in p{if let Some(t)=norm(t){let key:Vec<_>=t.iter().map(|&(q,b)|(q.id(),b)).collect();if map.remove(&key).is_none(){map.insert(key,t);}}}map.into_values().collect()}
fn mul<'a>(p:&Poly<'a>,q:&Poly<'a>)->Poly<'a>{tidy(p.iter().flat_map(|a|q.iter().map(move|b|{let mut c=a.clone();c.extend(b);c})).collect())}
fn xor<'a>(mut p:Poly<'a>,q:Poly<'a>)->Poly<'a>{p.extend(q);tidy(p)}
fn wire(q:&QReg)->Poly<'_>{vec![vec![(q,true)]]}
fn one<'a>()->Poly<'a>{vec![vec![]]}
fn replace<'a>(p:Poly<'a>,cond:Poly<'a>,value:bool)->Poly<'a>{let d=if value{xor(p.clone(),one())}else{p.clone()};xor(p,mul(&cond,&d))}
pub(super) fn aeq<'a>(rank:&'a[QReg],a:&'a[QReg],value:usize)->Poly<'a>{arith::A_EQUAL[value/64].iter().map(|&(m,v)|{let mut cs:Term<'a>=a.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()}
pub(super) fn ceq<'a>(rank:&'a[QReg],c:&'a[QReg],value:usize)->Poly<'a>{phase::C_EQUAL[value/64].iter().map(|&(m,v)|{let mut cs:Term<'a>=c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()}
fn gates(circ:&mut Circuit,p:Poly<'_>,target:&QReg,dirty:&[QReg]){for cs in tidy(p){super::q794_t10_quotient::gate(circ,&cs,target,dirty);}}
fn anf(circ:&mut Circuit,vars:&[Poly<'_>],f:impl Fn(usize)->bool,base:&Poly<'_>,target:&QReg,dirty:&[QReg]){let mut values:Vec<_>=(0..1usize<<vars.len()).map(f).collect();for b in 0..vars.len(){for m in 0..values.len(){if m>>b&1!=0{values[m]^=values[m^(1<<b)];}}}let mut out=Vec::new();for(m,on)in values.into_iter().enumerate(){if on{let mut p=base.clone();for(i,v)in vars.iter().enumerate(){if m>>i&1!=0{p=mul(&p,v);}}out.extend(p);}}gates(circ,out,target,dirty);}
fn swap(circ:&mut Circuit,cond:Poly<'_>,x:&QReg,y:&QReg,dirty:&[QReg]){circ.cx(y,x);gates(circ,mul(&cond,&wire(x)),y,dirty);circ.cx(y,x);}

/// Exact metadata sum flags. Caller starts both flag rails zero on g.
pub(super) fn flags(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,m255:&QReg,m256:&QReg,dirty:&[QReg]){
    super::q794_t10_quotient::endpoint(circ,rank,a,c,&[(g,true)],m256,dirty);
    // Low A+C=63 has no discarded carry: the maximum low sum is126.
    super::metadata_arithmetic5_encoded::add(circ,a,c,None,false);
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut truth:Vec<_>=triples.iter().map(|t|t[0]+t[1]==3).collect();for b in 0..5{for m in 0..32{if m>>b&1!=0{truth[m]^=truth[m^(1<<b)];}}}
    for(m,on)in truth.into_iter().enumerate(){if on{let mut cs=vec![(g,true)];cs.extend(c.iter().map(|q|(q,true)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)));super::q794_t10_quotient::gate(circ,&cs,m255,dirty);}}
    super::metadata_arithmetic5_encoded::add(circ,a,c,None,true);
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,inverse:bool){
    assert!(helpers.len()>=22);let start=circ.b.ops.len();let h=&sm[3];let q=&helpers[..3];let dirty=&helpers[3..];
    let cc:Vec<_>=(0..=3).map(|i|ceq(rank,c,i)).collect();let aa0=aeq(rank,a,0);let aa1=aeq(rank,a,1);
    let spec3=mul(&aeq(rank,a,253),&cc[1]);let spec2=mul(&aeq(rank,a,254),&cc[1]);let spec1=mul(&aeq(rank,a,254),&cc[2]);
    let specs=xor(xor(spec3.clone(),spec2.clone()),spec1.clone());
    swap(circ,mul(&wire(g),&specs),h,&w2[255],dirty);
    // Keep all three source digits in explicit dirty shuttles while the
    // codec reads low t. Restoration reverses the exact route/exchange.
    for k in 0..3{super::q793_t10_routes_v3::digit(circ,rank,a,c,w1,&q[k],dirty,1-k as isize);}
    let tt=[wire(&w1[0]),replace(wire(&w1[1]),aa0.clone(),false),replace(wire(&w1[2]),xor(aa0,aa1),false)];
    let qq=[replace(wire(&q[0]),cc[1].clone(),true),replace(replace(wire(&q[1]),cc[1].clone(),false),cc[2].clone(),true),replace(replace(wire(&q[2]),xor(cc[1].clone(),cc[2].clone()),false),cc[3].clone(),true)];
    for shift in 0..=2{
        if j&1!=shift&1{continue;}
        let c0=((j>>1)^(j&1))^(shift>>1);let sb=vec![vec![(g,true),(&c[0],c0!=0)]];
        let bb:[Poly<'_>;3]=std::array::from_fn(|k|wire(&w2[(259+k-shift)%259]));let b2=&w2[(261-shift)%259];
        let vv:[Poly<'_>;3]=std::array::from_fn(|k|{
            let index=258-shift-k;let mut v=wire(&w2[index]);
            if index>=3&&index-3<=254{let cond=mul(&aeq(rank,a,index-3),&xor(one(),cc[1].clone()));v=replace(v,cond,false);}
            if index==257{v=replace(v,mul(&aeq(rank,a,254),&cc[1]),true);}v
        });
        for rwidth in [3usize,2,1]{
            if rwidth==2&&shift>1||rwidth==1&&shift!=0{continue;}
            let rb=if rwidth==3{vec![vec![(&sm[1],false),(&sm[2],false)]]}else if rwidth==2{wire(&sm[1])}else{wire(&sm[2])};
            let base=mul(&sb,&rb);let spec=match rwidth{3=>&spec3,2=>&spec2,_=>&spec1};let known=rwidth!=3;
            let normal=mul(&base,&xor(one(),spec.clone()));let even=mul(&normal,&vec![vec![(&w1[0],false)]]);let odd=mul(&normal,&wire(&w1[0]));
            gates(circ,mul(&even,&bb[2]),h,dirty);
            let mut vars=Vec::new();vars.extend(tt.clone());vars.extend(bb.clone());vars.extend(vv.clone());vars.extend(qq.clone());
            anf(circ,&vars,|x|{let t=x&7;let u=x>>3&7;let v=x>>6&7;let qs=x>>9&7;
                if rwidth==3{(t.wrapping_mul(7usize.wrapping_sub(u*v)).wrapping_sub((qs<<shift)*v))>>2&1!=0}
                else if rwidth==2{if t&1==0||v==0||(v<<shift)>=4{return false;}let d=(t.wrapping_mul(7usize.wrapping_sub(u*v)).wrapping_sub(((qs&6)<<shift)*v))&7;d>=v<<shift}
                else{((7usize.wrapping_sub(u)).wrapping_mul(t))>>1&1!=0}
            },&odd,h,dirty);
            let hp=replace(wire(h),spec.clone(),known);let all_even=mul(&base,&vec![vec![(&w1[0],false)]]);
            gates(circ,mul(&all_even,&hp),b2,dirty);
            let q0=if rwidth==3{qq[0].clone()}else if rwidth==2{hp.clone()}else{bb[1].clone()};let q1=if rwidth==1{hp}else{qq[1].clone()};
            let mut vars=Vec::new();vars.extend(tt.clone());vars.push(if rwidth==1{Vec::new()}else{bb[0].clone()});vars.push(if rwidth==1{Vec::new()}else{bb[1].clone()});vars.extend(vv.clone());vars.push(q0);vars.push(q1);
            anf(circ,&vars,|x|{let t=x&7;let r=x>>3&3;let v=x>>5&7;let qs=x>>8&3;(v.wrapping_mul(7usize.wrapping_sub(t*r)).wrapping_sub((qs<<shift)*t))>>2&1!=0},&all_even,b2,dirty);
        }
    }
    for k in(0..3).rev(){super::q793_t10_routes_v3::digit(circ,rank,a,c,w1,&q[k],dirty,1-k as isize);}
    if inverse{circ.b.ops[start..].reverse();}
}
