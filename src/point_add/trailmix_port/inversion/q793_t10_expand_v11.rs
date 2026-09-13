//! V11: apply the existing analytic A support to codec metadata cofactors.
//! Semantic q0/q1 or short-t1/t2 readouts use temporarily clean phase bits.
//! SM0 is the actual quotient-address carry and conditional-clean MCX scratch.
//! Exact rank cofactors restricted by held high-S=0 guard.
//! Share each complete metadata factor across its data ANF by F C F C.
//! C1/C>=2 static cofactors and SM0-funded conditional-clean lowering.
//! Consumed C1 q0 is0 in the post-arithmetic codec,1 before.
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
// Exact XOR cubes on the13 physical rank codes having high S=0.
// Outside that domain the external held guard is0. Independent Dijkstra
// truth audit is t10-resume/rank-small-r01.result.json.
fn aeq_small<'a>(rank:&'a[QReg],a:&'a[QReg],value:usize)->Poly<'a>{
    let terms:&[(usize,usize)]=match value/64{0=>&[(28,12),(16,0)],3=>&[(25,25)],_=>return aeq(rank,a,value)};
    terms.iter().map(|&(m,v)|{let mut cs:Term<'a>=a.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()
}
// The caller already supplies the analytic whole-cycle A interval used
// by the handoff and arithmetic routes. It is not fitted to test samples.
// Outside the interval A=value is impossible whenever the held g is1.
fn aeq_supported<'a>(circ:&Circuit,rank:&'a[QReg],a:&'a[QReg],value:usize)->Poly<'a>{
    if circ.q797_a_support.is_some_and(|(lo,hi)|!(lo..hi).contains(&value)){Vec::new()}else{aeq_small(rank,a,value)}
}
fn ceq_small<'a>(rank:&'a[QReg],c:&'a[QReg],value:usize)->Poly<'a>{
    assert!(value<64);[(13usize,4usize),(3,1),(8,0)].iter().map(|&(m,v)|{let mut cs:Term<'a>=c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));cs}).collect()
}
fn conditional_cost(others:usize)->usize{match others{0=>0,1=>1,2=>4,n=>2*n}}
fn data_cost(n:usize)->usize{if n<2{0}else{2*n-3}}
fn gates(circ:&mut Circuit,p:Poly<'_>,target:&QReg,dirty:&[QReg],g:&QReg,scratch:&QReg,metadata:&[u32]){
    let mut groups=std::collections::BTreeMap::new();
    for cs in tidy(p){let(mut meta,mut data)=(Vec::new(),Vec::new());for(q,v)in cs{if metadata.contains(&q.id()){meta.push((q,v));}else{data.push((q,v));}}
        let key:Vec<_>=meta.iter().map(|&(q,v)|(q.id(),v)).collect();let entry=groups.entry(key).or_insert((meta,Vec::new()));entry.1.push(data);
    }
    for(_, (meta,data))in groups{let data=tidy(data);let mut others=Vec::new();let mut has_g=false;for&(q,v)in &meta{if q.id()==g.id(){assert!(v);has_g=true;}else{others.push((q,v));}}assert!(has_g);
        let plain:usize=data.iter().map(|d|conditional_cost(others.len()+d.len())).sum();let factored=2*conditional_cost(others.len())+2*data.iter().map(|d|data_cost(1+d.len())).sum::<usize>();
        if factored<plain{
            let d=&dirty[0];
            // F is metadata-only and contains g. C is a pure target-XOR
            // data oracle, restoring all controls and scratch even off g.
            // On g=1 SM0 is clean. On g=0 F=0, so the two equal C extensions
            // cancel exactly regardless of the initial d and SM0 values.
            for _ in 0..2{
                super::conditional_mcx::guarded(circ,g,&others,d,scratch,false,&dirty[1]);
                for term in &data{let mut cs=vec![(d,true)];cs.extend(term);super::paired_clean_mcx::toggle(circ,&cs,target,scratch);}
            }
        }else{for term in data{let mut cs=others.clone();cs.extend(term);super::conditional_mcx::guarded(circ,g,&cs,target,scratch,false,&dirty[0]);}}
    }
}
fn anf(circ:&mut Circuit,vars:&[Poly<'_>],f:impl Fn(usize)->bool,base:&Poly<'_>,target:&QReg,dirty:&[QReg],g:&QReg,scratch:&QReg,metadata:&[u32]){let mut values:Vec<_>=(0..1usize<<vars.len()).map(f).collect();for b in 0..vars.len(){for m in 0..values.len(){if m>>b&1!=0{values[m]^=values[m^(1<<b)];}}}let mut out=Vec::new();for(m,on)in values.into_iter().enumerate(){if on{let mut p=base.clone();for(i,v)in vars.iter().enumerate(){if m>>i&1!=0{p=mul(&p,v);}}out.extend(p);}}gates(circ,out,target,dirty,g,scratch,metadata);}
fn swap(circ:&mut Circuit,cond:Poly<'_>,x:&QReg,y:&QReg,dirty:&[QReg],g:&QReg,scratch:&QReg,metadata:&[u32]){circ.cx(y,x);gates(circ,mul(&cond,&wire(x)),y,dirty,g,scratch,metadata);circ.cx(y,x);}

// The M255/M256 endpoint machinery (both flag rails and the rwidth 2/1
// chart polynomials they gate) is emitted only where the analytic A support
// admits an endpoint coefficient. Blocks whose support excludes A=252..254
// cannot reach either endpoint, so the flags stay at their zero preparation
// and every gate conditioned on them is skipped. Support-gated, no algebra.
fn endpoints_excluded(circ:&Circuit)->bool{circ.q797_a_support.is_some_and(|(lo,hi)|(252..=254).all(|v|!(lo..hi).contains(&v)))}
/// Exact metadata sum flags. Caller starts both flag rails zero on g.
pub(super) fn flags(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,m255:&QReg,m256:&QReg,dirty:&[QReg]){
    if endpoints_excluded(circ){return;}
    super::q794_t10_quotient::endpoint(circ,rank,a,c,&[(g,true)],m256,dirty);
    // Low A+C=63 has no discarded carry: the maximum low sum is126.
    super::metadata_arithmetic5_encoded::add(circ,a,c,None,false);
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut truth:Vec<_>=triples.iter().map(|t|t[0]+t[1]==3).collect();for b in 0..5{for m in 0..32{if m>>b&1!=0{truth[m]^=truth[m^(1<<b)];}}}
    for(m,on)in truth.into_iter().enumerate(){if on{let mut cs=vec![(g,true)];cs.extend(c.iter().map(|q|(q,true)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)));super::q794_t10_quotient::gate(circ,&cs,m255,dirty);}}
    super::metadata_arithmetic5_encoded::add(circ,a,c,None,true);
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,inverse:bool,last:bool){
    assert!(helpers.len()>=22);let start=circ.b.ops.len();let h=&sm[3];let q=&helpers[..3];let dirty=&helpers[3..];let scratch=&sm[0];let metadata:Vec<_>=rank.iter().chain(a).chain(c).chain(&sm[1..3]).chain(std::iter::once(g)).map(QReg::id).collect();
    let cc:Vec<_>=(0..=3).map(|i|if last{if i==1{one()}else{Vec::new()}}else if i<=1{Vec::new()}else{ceq_small(rank,c,i)}).collect();let aa0=aeq_supported(circ,rank,a,0);let aa1=aeq_supported(circ,rank,a,1);
    let spec3=mul(&aeq_supported(circ,rank,a,253),&cc[1]);let spec2=mul(&aeq_supported(circ,rank,a,254),&cc[1]);let spec1=mul(&aeq_supported(circ,rank,a,254),&cc[2]);
    let specs=xor(xor(spec3.clone(),spec2.clone()),spec1.clone());
    swap(circ,mul(&wire(g),&specs),h,&w2[255],dirty,g,scratch,&metadata);
    // Phase10 is held in g. On g, P1=1 and P2=0; restoring this
    // preparation before arithmetic permits two clean semantic readouts.
    let readout_start=circ.b.ops.len();circ.cx(g,p1);
    if last{
        gates(circ,mul(&wire(g),&replace(wire(&w1[1]),aa0.clone(),false)),p1,dirty,g,scratch,&metadata);
        gates(circ,mul(&wire(g),&replace(wire(&w1[2]),xor(aa0.clone(),aa1.clone()),false)),p2,dirty,g,scratch,&metadata);
    }else{
        // q0 is present only when M<=254. For M255/M256 it is packed in
        // the low chart and the polynomial uses that existing chart bit.
        let q0cond=vec![vec![(g,true),(&sm[1],false),(&sm[2],false)]];
        super::q793_t10_routes_v10::digit_xor(circ,rank,a,c,w1,p1,dirty,1,&q0cond,g,scratch);
        // The physical C2 q1 head is a cargo host. Materialize its logical
        // constant once, before ANF synthesis, rather than in every monomial.
        let q1cond=mul(&vec![vec![(g,true),(&sm[2],false)]],&xor(one(),cc[2].clone()));
        super::q793_t10_routes_v10::digit_xor(circ,rank,a,c,w1,p2,dirty,0,&q1cond,g,scratch);
        gates(circ,mul(&wire(g),&cc[2]),p2,dirty,g,scratch,&metadata);
        // S1 never uses q2 modulo8. Even clocks still need the dirty q2
        // shuttle for S0; S2 cofactors erase it inside the polynomial.
        if j&1==0{let cs=vec![(g,true),(&sm[2],false)];super::q793_t10_routes_v10::digit(circ,rank,a,c,w1,&q[2],dirty,-1,&cs,g,scratch);}
    }
    let readouts=circ.b.ops[readout_start..].to_vec();let poly_start=circ.b.ops.len();
    let tt=if last{[wire(&w1[0]),wire(p1),wire(p2)]}else{[wire(&w1[0]),replace(wire(&w1[1]),aa0.clone(),false),replace(wire(&w1[2]),xor(aa0,aa1),false)]};
    let qq=if last{[if inverse{Vec::new()}else{one()},Vec::new(),Vec::new()]}else{[wire(p1),wire(p2),if j&1==1{Vec::new()}else{replace(replace(wire(&q[2]),cc[2].clone(),false),cc[3].clone(),true)}]};
    for shift in 0..=2{
        if j&1!=shift&1{continue;}
        let c0=((j>>1)^(j&1))^(shift>>1);let sb=vec![vec![(g,true),(&c[0],c0!=0)]];
        let bb:[Poly<'_>;3]=std::array::from_fn(|k|wire(&w2[(259+k-shift)%259]));let b2=&w2[(261-shift)%259];
        let vv:[Poly<'_>;3]=std::array::from_fn(|k|{
            let index=258-shift-k;let mut v=wire(&w2[index]);
            if index>=3&&index-3<=254{let cond=mul(&aeq_supported(circ,rank,a,index-3),&xor(one(),cc[1].clone()));v=replace(v,cond,false);}
            if index==257{v=replace(v,mul(&aeq_supported(circ,rank,a,254),&cc[1]),true);}v
        });
        for rwidth in [3usize,2,1]{
            if rwidth==2&&shift>1||rwidth==1&&shift!=0{continue;}
            if rwidth<3&&endpoints_excluded(circ){continue;}
            let rb=if rwidth==3{vec![vec![(&sm[1],false),(&sm[2],false)]]}else if rwidth==2{wire(&sm[1])}else{wire(&sm[2])};
            let base=mul(&sb,&rb);let spec=match rwidth{3=>&spec3,2=>&spec2,_=>&spec1};let known=rwidth==1||(rwidth==2&&!inverse);
            let normal=mul(&base,&xor(one(),spec.clone()));let even=mul(&normal,&vec![vec![(&w1[0],false)]]);let odd=mul(&normal,&wire(&w1[0]));
            gates(circ,mul(&even,&bb[2]),h,dirty,g,scratch,&metadata);
            let mut vars=Vec::new();vars.extend(tt.clone());vars.extend(bb.clone());vars.extend(vv.clone());vars.extend(qq.clone());
            anf(circ,&vars,|x|{let t=x&7;let u=x>>3&7;let v=x>>6&7;let qs=x>>9&7;
                if rwidth==3{(t.wrapping_mul(7usize.wrapping_sub(u*v)).wrapping_sub((qs<<shift)*v))>>2&1!=0}
                else if rwidth==2{if t&1==0||v==0||(v<<shift)>=4{return false;}let d=(t.wrapping_mul(7usize.wrapping_sub(u*v)).wrapping_sub(((qs&6)<<shift)*v))&7;d>=v<<shift}
                else{((7usize.wrapping_sub(u)).wrapping_mul(t))>>1&1!=0}
            },&odd,h,dirty,g,scratch,&metadata);
            let hp=replace(wire(h),spec.clone(),known);let all_even=mul(&base,&vec![vec![(&w1[0],false)]]);
            gates(circ,mul(&all_even,&hp),b2,dirty,g,scratch,&metadata);
            let q0=if rwidth==3{qq[0].clone()}else if rwidth==2{hp.clone()}else{bb[1].clone()};let q1=if rwidth==1{hp}else{qq[1].clone()};
            let mut vars=Vec::new();vars.extend(tt.clone());vars.push(if rwidth==1{Vec::new()}else{bb[0].clone()});vars.push(if rwidth==1{Vec::new()}else{bb[1].clone()});vars.extend(vv.clone());vars.push(q0);vars.push(q1);
            anf(circ,&vars,|x|{let t=x&7;let r=x>>3&3;let v=x>>5&7;let qs=x>>8&3;(v.wrapping_mul(7usize.wrapping_sub(t*r)).wrapping_sub((qs<<shift)*t))>>2&1!=0},&all_even,b2,dirty,g,scratch,&metadata);
        }
    }
    let poly_end=circ.b.ops.len();
    circ.b.ops.extend(readouts.into_iter().rev());
    if std::env::var("Q793_T10_COST").ok().as_deref()==Some("1"){for(label,l,r)in[("cargo+qborrow",start,poly_start),("poly",poly_start,poly_end),("qreturn",poly_end,circ.b.ops.len())]{let ops=&circ.b.ops[l..r];let t=ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();eprintln!("Q793_T10_V11_CODEC last={last} inverse={inverse} part={label} ops={} T={t}",ops.len());}}
    if inverse{circ.b.ops[start..].reverse();}
}
