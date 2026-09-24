//! R06 shares each short-domain selector across all possible small A values.
//! Existing analytic A support prunes only guarded data-address trees.
//! The active phase bit still supplies the r04 paired-route scratch.
//! Three-hole Sign erasure with one funded mask and no clean carry.
//! The full boundary wrapper is native-qualified separately from whole steps.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v) in cs{assert_ne!(q.id(),out.id());if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}else{unique.push((q,v));}}
    mixed_mcx(circ,&unique,out,dirty);
}
fn swap(circ:&mut Circuit,cs:&[(&QReg,bool)],l:&QReg,r:&QReg,dirty:&[QReg]){assert_ne!(l.id(),r.id());circ.cx(r,l);let mut c=cs.to_vec();c.push((l,true));gate(circ,&c,r,dirty);circ.cx(r,l);}
fn rank_terms(rank:&[QReg],f:impl Fn([usize;3])->bool)->Vec<Vec<(&QReg,bool)>>{
    let values:Vec<_>=triples().into_iter().map(f).collect();let truth=values.iter().enumerate().fold(0u32,|v,(r,&on)|v|((on as u32)<<r));
    // Exact disjoint covers of all 32 rank codes, independently enumerated
    // in sign-resume/rank_covers_r05.py. These need no care-domain premise.
    let cubes:&[(usize,usize)]=match truth{
        0xb4d22911=>&[(23,0),(15,4),(31,11),(15,13),(31,17),(30,22),(31,26),(31,28),(31,31)], // S_high0
        0x20802001=>&[(31,0),(15,13),(31,23)], // C_high0 AND S_high0
        0x6381e00f=>&[(28,0),(29,13),(15,14),(23,16),(31,23),(27,25)], // C_high0
        _=>panic!("unproved Sign r05 rank predicate {truth:08x}"),
    };
    for(r,&expected)in values.iter().enumerate(){let hits=cubes.iter().filter(|&&(m,v)|r&m==v).count();assert!(hits<=1);assert_eq!(hits==1,expected);}
    cubes.iter().map(|&(m,v)|(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect()).collect()
}
fn simplify_terms(terms:Vec<Vec<(&QReg,bool)>>)->Vec<Vec<(&QReg,bool)>>{
    use std::collections::BTreeMap;
    let mut cubes:BTreeMap<Vec<(usize,bool)>,Vec<(&QReg,bool)>>=BTreeMap::new();
    for term in terms{
        let mut unique:BTreeMap<usize,(&QReg,bool)>=BTreeMap::new();let mut valid=true;
        for (q,v) in term{if let Some(&(_,old))=unique.get(&(q.id()as usize)){if old!=v{valid=false;break;}}else{unique.insert(q.id()as usize,(q,v));}}
        if !valid{continue;}let key:Vec<_>=unique.iter().map(|(&id,&(_,v))|(id,v)).collect();
        if cubes.remove(&key).is_none(){cubes.insert(key,unique.into_values().collect());}
    }
    // Every term is a pure XOR into one target. Exact cube cancellation
    // and X*y XOR X*!y = X happen before any dirty-MCX lowering.
    let mut queue:Vec<_>=cubes.keys().cloned().collect();
    while let Some(key)=queue.pop(){if !cubes.contains_key(&key){continue;}
        for i in 0..key.len(){let mut partner=key.clone();partner[i].1^=true;
            if cubes.contains_key(&partner){let mut term=cubes.remove(&key).unwrap();cubes.remove(&partner);let mut common=key.clone();common.remove(i);term.remove(i);
                if cubes.remove(&common).is_none(){cubes.insert(common.clone(),term);queue.push(common);}break;
            }
        }
    }
    cubes.into_values().collect()
}
fn emit_terms_with_scratch(circ:&mut Circuit,terms:Vec<Vec<(&QReg,bool)>>,out:&QReg,dirty:&[QReg],scratch:Option<&QReg>){
    for term in simplify_terms(terms){
        if let Some(scratch)=scratch{super::paired_clean_mcx::toggle(circ,&term,out,scratch);}else{gate(circ,&term,out,dirty);}
    }
}
fn emit_terms(circ:&mut Circuit,terms:Vec<Vec<(&QReg,bool)>>,out:&QReg,dirty:&[QReg]){emit_terms_with_scratch(circ,terms,out,dirty,None);}

fn mcx_cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
/// Exact dirty echo for a simplified XOR bank with a five-bit rank factor.
/// The input truth table is evaluated on all rank codes and the direct path
/// wins ties, so this is independent of the EEA chart's reachable subset.
fn emit_rank_terms(circ:&mut Circuit,terms:Vec<Vec<(&QReg,bool)>>,rank:&[QReg],out:&QReg,dirty:&[QReg]){
    let terms=simplify_terms(terms);
    if !super::metadata_muxlease::active("Q793_RANK_ECHO_SIGN")||dirty.len()<2{for term in terms{gate(circ,&term,out,dirty);}return;}
    let rank_pos=|q:&QReg|rank.iter().position(|r|r.id()==q.id());
    struct Group<'a>{key:Vec<(&'a QReg,bool)>,truth:Vec<bool>,direct:usize,terms:Vec<Vec<(&'a QReg,bool)>>}
    let mut groups:Vec<Group>=Vec::new();
    for term in terms{
        let mut key:Vec<_>=term.iter().copied().filter(|(q,_)|rank_pos(q).is_none()).collect();key.sort_by_key(|(q,_)|q.id());
        let lits:Vec<_>=term.iter().filter_map(|&(q,v)|rank_pos(q).map(|i|(i,v))).collect();
        let at=match groups.iter().position(|g|g.key.len()==key.len()&&g.key.iter().zip(&key).all(|(a,b)|a.0.id()==b.0.id()&&a.1==b.1)){Some(i)=>i,None=>{groups.push(Group{key,truth:vec![false;32],direct:0,terms:Vec::new()});groups.len()-1}};
        for code in 0..32{if lits.iter().all(|&(i,v)|(code>>i&1!=0)==v){groups[at].truth[code]^=true;}}
        groups[at].direct+=mcx_cost(term.len());groups[at].terms.push(term);
    }
    let d=&dirty[0];let rest=&dirty[1..];
    for group in groups{
        if group.truth.iter().all(|&v|!v){continue;}
        let (polarity,monomials)=super::metadata_muxlease::swap_terms(group.truth,5);
        let echo=2*monomials.iter().map(|m|mcx_cost(m.count_ones()as usize)).sum::<usize>()+2*mcx_cost(group.key.len()+1);
        if group.direct<=echo{for term in group.terms{gate(circ,&term,out,dirty);}continue;}
        for &(q,_) in &group.key{assert_ne!(q.id(),d.id(),"Sign rank echo scratch aliases shared controls");}
        let compute=|circ:&mut Circuit|{for i in 0..5{if polarity>>i&1!=0{circ.x(&rank[i]);}}for &m in &monomials{let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)).collect();match cs.len(){0=>circ.x(d),1=>circ.cx(cs[0].0,d),_=>mixed_mcx(circ,&cs,d,rest)}}for i in (0..5).rev(){if polarity>>i&1!=0{circ.x(&rank[i]);}}};
        let consume=|circ:&mut Circuit|{let mut cs=vec![(d,true)];cs.extend_from_slice(&group.key);mixed_mcx(circ,&cs,out,rest);};
        consume(circ);compute(circ);consume(circ);compute(circ);
    }
}

fn truth_terms<'a>(inputs:&[&'a QReg],extra:&[(&'a QReg,bool)],f:impl Fn(usize)->bool)->Vec<Vec<(&'a QReg,bool)>>{
    use std::collections::BTreeMap;
    let mut fixed=BTreeMap::new();for &(q,v)in extra{if let Some(old)=fixed.insert(q.id(),v){if old!=v{return Vec::new();}}}
    let mut free:Vec<&QReg>=Vec::new();let mut codes=Vec::new();
    for &q in inputs{if let Some(&value)=fixed.get(&q.id()){codes.push((None,value));}else{let i=free.iter().position(|x|x.id()==q.id()).unwrap_or_else(||{free.push(q);free.len()-1});codes.push((Some(i),false));}}
    assert!(free.len()<=12);let n=1<<free.len();let mut anf:Vec<_>=(0..n).map(|z|{let code=codes.iter().enumerate().fold(0,|v,(i,(k,b))|v|((if let Some(k)=k{z>>k&1}else{*b as usize})<<i));f(code)}).collect();
    for bit in 0..free.len(){for m in 0..n{if m>>bit&1!=0{anf[m]^=anf[m^(1<<bit)];}}}
    anf.into_iter().enumerate().filter(|&(_,on)|on).map(|(m,_)|{let mut cs=extra.to_vec();cs.extend(free.iter().enumerate().filter(|&(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));cs}).collect()
}

// Pure data truth tables are synthesized after physical alias substitution.
// kind0=ordinary; kind1=small-S chart correction; kinds2/3/4=C1/C2/C3
// v normalization corrections. Metadata is factored into a dirty selector,
// rather than multiplied into every data monomial.
fn low_data_indexed<'a>(w1:&'a[QReg],w2:&'a[QReg],j:usize,width:usize,a_fixed:Option<usize>,kind:usize,a_dynamic:Option<&'a[QReg]>)->Vec<Vec<(&'a QReg,bool)>>{
    assert!((1..=3).contains(&width));let shift=(4-j)%4;
    let abits=if width==1{1}else{2};let a_at=if kind==0{6}else{11};
    let tval=|z:usize|{let av=a_fixed.or_else(||a_dynamic.map(|_|(z>>a_at)&((1<<abits)-1)));if let Some(a)=av{(z&((1<<a)-1))|(1<<a)}else{z&7}};
    let mut ordinary=vec![&w1[0],&w1[1],&w1[2],&w2[0],&w2[1],&w2[2]];if let Some(a)=a_dynamic{ordinary.extend(a[..abits].iter());}
    if kind==0{return truth_terms(&ordinary,&[],|z|tval(z)>(z>>3&((1<<width)-1)));}
    if shift==3{return Vec::new();}
    let mut inputs=vec![&w1[0],&w1[1],&w1[2],&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259],&w2[257-shift],&w2[256-shift],&w2[0],&w2[1],&w2[2]];if let Some(a)=a_dynamic{inputs.extend(a[..abits].iter());}
    let corrected=|z:usize,short_c:usize|{
        let t=tval(z);let b=z>>3&7;let mut v1=z>>6&1;let mut v2=z>>7&1;
        if short_c==1{v1=0;v2=0;}else if short_c==2{v1=1;v2=0;}else if short_c==3{v2=1;}
        let u=if t&1!=0{b}else{1|((1^v1^((t>>1&1)&(b&1)))<<1)|((1^v2^((t>>2&1)&(b&1))^((t>>1&1)&(b>>1&1)))<<2)};
        let raw=z>>8&7;let mut rhs=0;for i in 0..width{rhs|=if i+shift<3{(u>>(i+shift)&1)<<i}else{(raw>>i&1)<<i};}t>rhs
    };
    truth_terms(&inputs,&[],|z|if kind==1{corrected(z,0)^(tval(z)>(z>>8&((1<<width)-1)))}else{corrected(z,0)^corrected(z,kind-1)})
}
fn low_data<'a>(w1:&'a[QReg],w2:&'a[QReg],j:usize,width:usize,a_fixed:Option<usize>,kind:usize)->Vec<Vec<(&'a QReg,bool)>>{low_data_indexed(w1,w2,j,width,a_fixed,kind,None)}
fn selected(circ:&mut Circuit,rank:&[QReg],selectors:Vec<Vec<(&QReg,bool)>>,data:Vec<Vec<(&QReg,bool)>>,out:&QReg,dirty:&[QReg]){
    if selectors.is_empty()||data.is_empty(){return;}
    if data.len()==1&&data[0].is_empty(){emit_rank_terms(circ,selectors,rank,out,dirty);return;}
    let flag=&dirty[0];let tail=&dirty[1..];let controlled:Vec<_>=data.into_iter().map(|mut term|{term.push((flag,true));term}).collect();
    // F C F C: F toggles an arbitrary dirty flag by the metadata selector;
    // C toggles out by flag*data. Their commutator is selector*data, and
    // every flag/lender restores. Metadata is paid only twice per oracle.
    for _ in 0..2{emit_rank_terms(circ,selectors.clone(),rank,flag,tail);emit_terms(circ,controlled.clone(),out,tail);}
}
// Called only inside the core's U / guarded-center / U^-1. Scratch is
// X(P1): zero on the active phase. Off phase, every paired MCX remains a
// pure target-XOR extension and restores scratch/controls; no exact
// off-domain oracle is required because U^-1 is the literal inverse.
fn selected_clean(circ:&mut Circuit,selectors:Vec<Vec<(&QReg,bool)>>,data:Vec<Vec<(&QReg,bool)>>,out:&QReg,dirty:&[QReg],scratch:&QReg){
    if selectors.is_empty()||data.is_empty(){return;}
    if data.len()==1&&data[0].is_empty(){emit_terms_with_scratch(circ,selectors,out,dirty,Some(scratch));return;}
    let flag=&dirty[0];let tail=&dirty[1..];let controlled:Vec<_>=data.into_iter().map(|mut term|{term.push((flag,true));term}).collect();
    for _ in 0..2{emit_terms_with_scratch(circ,selectors.clone(),flag,tail,Some(scratch));emit_terms_with_scratch(circ,controlled.clone(),out,tail,Some(scratch));}
}
fn low(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],w1:&[QReg],w2:&[QReg],out:&QReg,dirty:&[QReg],j:usize,scratch:&QReg){
    emit_terms_with_scratch(circ,low_data(w1,w2,j,3,None,0),out,dirty,Some(scratch));let shift=(4-j)%4;
    if shift==3{return;}
    for kind in 1..=4{
        let selectors:Vec<_>=rank_terms(rank,|t|t[2]==0&&(kind==1||t[1]==0)).into_iter().map(|mut term|{term.extend(sm.iter().map(|q|(q,false)));if kind>1{term.extend(c.iter().enumerate().map(|(i,q)|(q,(kind-1+shift)>>i&1!=0)));}term}).collect();
        selected_clean(circ,selectors,low_data(w1,w2,j,3,None,kind),out,dirty,scratch);
    }
}
fn short_compare(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    // A+C+S<=257 on the active chart. Thus C+S=257-k, k<=3,
    // implies A<=k and high A=0. A0/A1 are ordinary DATA controls;
    // no six-bit A equality needs to be recomputed per metadata leaf.
    let lower=circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0);
    if lower>3{return;}
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let ts=triples();let shift=(4-j)%4;
    for k in lower..=3{let value=257-k;
        let mut base=Vec::new();let mut small=Vec::new();
        for (r,t) in ts.iter().enumerate(){if t[0]!=0{continue;}for carry in 0..=1{if t[1]+t[2]+carry!=value/64{continue;}
            let mut term=vec![(g,true),(cache,carry!=0)];term.extend(rank.iter().enumerate().map(|(i,q)|(q,r>>i&1!=0)));term.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));
            base.push(term.clone());if t[2]==0&&shift<3{term.extend(sm.iter().map(|q|(q,false)));small.push(term);}
        }}
        let ordinary=if k==0{vec![Vec::new()]}else{low_data_indexed(w1,w2,j,k,None,0,Some(a))};
        selected(circ,rank,base,ordinary,sign,dirty);
        // Short C+S>=254 gives C>=252 on small S. All low-v inputs
        // are genuine data, so the generic correction is sufficient.
        if k>0{selected(circ,rank,small,low_data_indexed(w1,w2,j,k,None,1,Some(a)),sign,dirty);}
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}

fn short_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg],j:usize){
    // F C F C pays for an initially dirty high-group flag. Also bypass
    // C1/S0 (sum1): u=p, t<p/2, so its Sign is already zero.
    let scratch=&dirty[0];let tail=&dirty[1..];
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,tail,j,false);
    for (h,values) in [(0usize,vec![1usize]),(3,vec![254usize,255]),(4,vec![256,257])]{
        let max_sum=257-circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0);let values:Vec<_>=values.into_iter().filter(|&v|v<=max_sum).collect();if values.is_empty(){continue;}
        for _ in 0..2{
            super::metadata_phase115_phased::sum_flag_raw(circ,rank,c,sm,g,scratch,tail,j,h);
            for &value in &values{let mut cs=vec![(g,true),(scratch,true)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));gate(circ,&cs,out,tail);}
        }
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,tail,j,true);
}

// Exact high-address Fredkin on g=1. Every use belongs to a complete
// route / g-guarded center / literal-unroute region. X(g) supplies zero
// scratch on that domain and is restored before any center observes g.
fn route_swap(circ:&mut Circuit,controls:&[&QReg],truth:Vec<bool>,left:&QReg,right:&QReg,g:&QReg){
    let(polarity,terms)=super::metadata_muxlease::swap_terms(truth,controls.len());
    for(i,q)in controls.iter().enumerate(){if polarity>>i&1!=0{circ.x(q);}}
    circ.cx(right,left);circ.x(g);
    for m in terms{let mut cs=vec![(left,true)];cs.extend((0..controls.len()).filter(|&i|m>>i&1!=0).map(|i|(controls[i],true)));super::paired_clean_mcx::toggle(circ,&cs,right,g);}
    circ.x(g);circ.cx(right,left);
    for(i,q)in controls.iter().enumerate().rev(){if polarity>>i&1!=0{circ.x(q);}}
}
fn route_predicate(circ:&mut Circuit,rank:&[QReg],axis:usize,bit:usize,left:&QReg,right:&QReg,g:&QReg){
    let truth=triples().into_iter().map(|t|t[axis]>>bit&1!=0).collect();route_swap(circ,&rank.iter().collect::<Vec<_>>(),truth,left,right,g);
}
fn gather_a<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&'a[QReg],offset:usize,max:usize,dirty:&[QReg],g:&QReg)->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let support=circ.q797_a_support.unwrap_or((0,256));let mut nodes:Vec<_>=(0..256).map(|v|if v<=max&&(support.0..support.1).contains(&v){Some(&w1[v+offset])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{if level<6{circ.cswap(&a[level],l,r);}else{route_predicate(circ,rank,0,level-6,l,r,g);}Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
fn gather_span<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],cache:&QReg,word:&'a[QReg],base:usize,min:usize,max:usize,dirty:&[QReg],g:&QReg)->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let max=max.min(257-circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0));assert!(min<=max);let mut nodes=vec![None;512];for value in min..=max{nodes[value]=Some(&word[base-value]);}let ts=triples();
    for level in 0..9{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{let controls:Vec<_>=rank.iter().chain(std::iter::once(cache)).collect();let truth:Vec<_>=(0..64).map(|z|((ts[z&31][1]+ts[z&31][2]+(z>>5))>>(level-6))&1!=0).collect();route_swap(circ,&controls,truth,l,r,g);}Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
fn gather_sum<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],cache:&QReg,word:&'a[QReg],base:usize,min:usize,dirty:&[QReg],g:&QReg)->(&'a QReg,Vec<crate::circuit::Op>){gather_span(circ,rank,c,cache,word,base,min,257,dirty,g)}

fn cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    // Move the SECOND passenger first. At A254 and C+S3 its relocated
    // W2[255] host is precisely the destination of the first handoff.
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let(l,lop)=gather_a(circ,rank,a,w1,2,253,dirty,g);let(r,rop)=gather_sum(circ,rank,c,cache,w2,257,1,dirty,g);
    swap(circ,&[(g,true)],l,r,dirty);
    let mut a254=vec![(g,true)];a254.extend(rank.iter().enumerate().map(|(i,q)|(q,29>>i&1!=0)));a254.extend(a.iter().enumerate().map(|(i,q)|(q,254>>i&1!=0)));swap(circ,&a254,l,r,dirty);
    circ.b.ops.extend(rop.into_iter().rev());circ.b.ops.extend(lop.into_iter().rev());
    for sum in [1usize,3]{let mut cs=a254.clone();cs.extend(c.iter().enumerate().map(|(i,q)|(q,sum>>i&1!=0)));cs.extend(sm.iter().map(|q|(q,false)));swap(circ,&cs,&w2[255],&w2[257-sum],dirty);}
    let(l,lop)=gather_a(circ,rank,a,w1,1,254,dirty,g);let(r,rop)=gather_sum(circ,rank,c,cache,w2,258,1,dirty,g);circ.cswap(g,l,r);circ.b.ops.extend(rop.into_iter().rev());circ.b.ops.extend(lop.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}
fn c12_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg]){for cv in 1usize..=2{let terms=rank_terms(rank,|t|t[1]==0).into_iter().map(|mut cs|{cs.push((g,true));cs.extend(c.iter().enumerate().map(|(i,q)|(q,cv>>i&1!=0)));cs}).collect();emit_rank_terms(circ,terms,rank,out,dirty);}}
/// Hold the common exact C-high-zero chart across the C1/C2 mask-loan body.
///
/// The two C rectangles are disjoint and share H(rank)=[C_high=0].  With an
/// arbitrary lender d, C toggles `out` by d*g*(C=1 xor C=2) and D toggles d
/// by H.  `C D C U C D C` therefore implements the original pair around U
/// while restoring d.  The body receives lenders excluding d.
fn c12_hold_around<F>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg],body:F)
where F:FnOnce(&mut Circuit,&[QReg]){
    if !super::metadata_muxlease::active("Q793_SIGN_C12_HOLD")||dirty.len()<3{
        c12_flag(circ,rank,c,g,out,dirty);body(circ,dirty);c12_flag(circ,rank,c,g,out,dirty);return;
    }
    let truth:Vec<_>=triples().into_iter().map(|t|t[1]==0).collect();
    let(polarity,monomials)=super::metadata_muxlease::swap_terms(truth,5);
    let rank_cost:usize=monomials.iter().map(|m|mcx_cost(m.count_ones()as usize)).sum();
    let consume_cost=mcx_cost(8); // d, g, and the six exact C literals
    let direct:usize=rank_terms(rank,|t|t[1]==0).iter().map(|term|mcx_cost(7+term.len())).sum();
    let restored_pair=4*direct.min(2*rank_cost+2*consume_cost);
    let held=2*rank_cost+8*consume_cost;
    if held>=restored_pair{
        c12_flag(circ,rank,c,g,out,dirty);body(circ,dirty);c12_flag(circ,rank,c,g,out,dirty);return;
    }
    let d=&dirty[0];let rest=&dirty[1..];
    let compute=|circ:&mut Circuit|{
        for i in 0..5{if polarity>>i&1!=0{circ.x(&rank[i]);}}
        for &m in &monomials{let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)).collect();match cs.len(){0=>circ.x(d),1=>circ.cx(cs[0].0,d),_=>mixed_mcx(circ,&cs,d,rest)}}
        for i in (0..5).rev(){if polarity>>i&1!=0{circ.x(&rank[i]);}}
    };
    let consume=|circ:&mut Circuit|{for cv in 1usize..=2{let mut cs=vec![(d,true),(g,true)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,cv>>i&1!=0)));mixed_mcx(circ,&cs,out,rest);}};
    consume(circ);compute(circ);consume(circ);body(circ,rest);consume(circ);compute(circ);consume(circ);
}
fn mask_loan(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,w1:&[QReg],dirty:&[QReg]){
    c12_hold_around(circ,rank,c,g,cache,dirty,|circ,lenders|{
        let start=circ.b.ops.len();let max_c=257-circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0);let mut nodes:Vec<_>=(0..256).map(|v|if v>=3&&v<=max_c{Some(&w1[258-v])}else{None}).collect();
        for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{route_predicate(circ,rank,1,level-6,l,r,g);}Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
        let route=circ.b.ops[start..].to_vec();swap(circ,&[(g,true),(cache,false)],nodes[0].unwrap(),mask,lenders);circ.b.ops.extend(route.into_iter().rev());swap(circ,&[(g,true),(cache,true)],&w1[255],mask,lenders);
    });
}
fn top_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,w1:&[QReg],dirty:&[QReg],j:usize){
    // C+S1/2 imply k256/255. Both true top bits are zero because A<=254.
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);let(q,route)=gather_sum(circ,rank,c,cache,w1,257,3,dirty,g);
    // Pruned leaves are arbitrary off their supported sum. Explicitly
    // cancel sum1/2 so the fallback cannot read a data or passenger bit.
    circ.ccx(g,q,mask);
    for sum in 1usize..=2{let terms=rank_terms(rank,|t|t[1]+t[2]==0).into_iter().map(|mut cs|{cs.extend([(g,true),(cache,false),(q,true)]);cs.extend(c.iter().enumerate().map(|(i,x)|(x,sum>>i&1!=0)));cs}).collect();emit_rank_terms(circ,terms,rank,mask,dirty);}
    circ.b.ops.extend(route.into_iter().rev());super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}

fn core(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,top:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);let start=circ.b.ops.len();
    for i in 3..256{circ.cx(&w1[i],&w2[i]);}
    for i in (4..256).rev(){circ.cx(&w1[i-1],&w1[i]);}
    // At the small-S v1/v2 readers, undo D=target XOR original_source.
    // The neighboring-XOR source frame reconstructs original t_i by the
    // prefix XOR source[3..=i]. These v positions are always >=k, outside
    // the comparison's causal prefix, so they can stay normalized until
    // the exact inverse. No additional output or clean rail is needed.
    let shift=(4-j)%4;
    if shift<3{for pos in [257-shift,256-shift]{if pos<256{for i in 3..=pos{circ.cx(&w1[i],&w2[pos]);}}}}
    circ.x(g);low(circ,rank,c,sm,w1,w2,&w1[3],dirty,j,g);circ.x(g);
    // x_i=t_i XOR B_i; D_i=t_i XOR u_i. Adjacent-XOR preparation gives
    // x_(i+1)=t_(i+1) XOR B_i XOR x_i*D_i with one negative-control CCX.
    for i in 3..255{circ.x(&w2[i]);circ.ccx(&w1[i],&w2[i],&w1[i+1]);circ.x(&w2[i]);}
    let compute=circ.b.ops[start..].to_vec();
    // The active general domain has 2<=C+S<=253 (k>=4); all other
    // reachable branches were parked. Cache is the prepared addition carry.
    let(s,sop)=gather_span(circ,rank,c,cache,w1,256,2,253,dirty,g);
    let(d,dop)=gather_span(circ,rank,c,cache,w2,256,2,253,dirty,g);
    gate(circ,&[(g,true),(top,false),(s,true),(d,false)],sign,dirty);
    circ.b.ops.extend(dop.into_iter().rev());circ.b.ops.extend(sop.into_iter().rev());
    circ.b.ops.extend(compute.into_iter().rev());
    let(s,sop)=gather_span(circ,rank,c,cache,w1,256,2,253,dirty,g);
    gate(circ,&[(g,true),(top,false),(s,true)],sign,dirty);circ.b.ops.extend(sop.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,_n:usize){
    assert!(helpers.len()>=22);let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    let mut last=start;let mut stage=|circ:&Circuit,name:&str|{if std::env::var_os("Q793_SIGN_CENSUS").is_some(){let ops=&circ.b.ops[last..];eprintln!("Q793_SIGN_R06_STAGE j={j} stage={name} ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count());last=circ.b.ops.len();}};
    super::q798_sign_erase::code(circ,p1,p2,sign,helpers,false);
    short_compare(circ,rank,a,c,sm,p1,p2,sign,w1,w2,helpers,j);stage(circ,"short");
    short_flag(circ,rank,c,sm,p1,p2,helpers,j);super::q795_t11::park_c1(circ,p1,p2,sign,helpers);stage(circ,"bypass");
    let movestart=circ.b.ops.len();
    // Internal S0 is just before the exit's final right rotation: A254's
    // second passenger is still W2[256]. S>0 boundary callers use W2[255].
    if j==0{let mut cs=vec![(p1,true)];cs.extend(rank.iter().enumerate().map(|(i,q)|(q,29>>i&1!=0)));cs.extend(a.iter().enumerate().map(|(i,q)|(q,254>>i&1!=0)));cs.extend(sm.iter().map(|q|(q,false)));swap(circ,&cs,&w2[255],&w2[256],helpers);}
    cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);let moves=circ.b.ops[movestart..].to_vec();stage(circ,"cargo");
    let mask=&helpers[0];let dirty=&helpers[1..];let ls=circ.b.ops.len();mask_loan(circ,rank,c,p1,p2,mask,w1,dirty);let loan=circ.b.ops[ls..].to_vec();stage(circ,"mask");
    let ts=circ.b.ops.len();top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);let top=circ.b.ops[ts..].to_vec();stage(circ,"top");
    circ.cswap(p1,p2,mask);circ.ccx(p1,p2,sign);
    // Mask is now a funded zero cache; P2 retains the fixed top branch.
    // Keeping that branch explicit avoids sharing the short-domain park.
    core(circ,rank,c,sm,p1,mask,p2,sign,w1,w2,dirty,j);stage(circ,"core");
    circ.cswap(p1,p2,mask);circ.b.ops.extend(top.into_iter().rev());circ.b.ops.extend(loan.into_iter().rev());circ.b.ops.extend(moves.into_iter().rev());
    super::q795_t11::park_c1(circ,p1,p2,sign,helpers);short_flag(circ,rank,c,sm,p1,p2,helpers,j);super::q798_sign_erase::code(circ,p1,p2,sign,helpers,true);stage(circ,"return");
    assert_eq!(circ.b.next_qubit,owned);for op in &circ.b.ops[start..]{for h in [256,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Sign touched omitted source{h}");}}
}

#[path="q793_sign_dynamic_r05_check.rs"]
pub mod verification;
