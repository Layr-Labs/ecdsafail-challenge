//! Own Sign general body with no P2 consumers; P2 can fund unfolded rank.
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
    let terms=simplify_terms(terms);let terms=if scratch.is_some()&&super::q792_esop_r01::active(){super::q792_poly_r01::terms(terms,0)}else{terms};if let Some(s)=scratch{if super::q792_bank_factor_r01::emit(circ,&terms,out,dirty,s){return;}}
    for term in terms{
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
    let d=&dirty[0];let rest=&dirty[1..];let word:Vec<_>=rank.iter().collect();
    for group in groups{
        if group.truth.iter().all(|&v|!v){continue;}
        // Both are exact XOR oracles on every rank code. Compare actual
        // emitted operation counts, including negative-control frames.
        let at=circ.b.ops.len();
        super::q792_fold20_r01::table(circ,&word,group.truth.clone(),&group.key,out,dirty);
        let direct=circ.b.ops.split_off(at);
        let mut cs=group.key.clone();cs.push((d,true));
        for _ in 0..2{
            mixed_mcx(circ,&cs,out,rest);
            super::q792_fold20_r01::table(circ,&word,group.truth.clone(),&[],d,rest);
        }
        if circ.b.ops.len()-at>=direct.len(){circ.b.ops.truncate(at);circ.b.ops.extend(direct);}
    }
}

fn truth_terms<'a>(inputs:&[&'a QReg],extra:&[(&'a QReg,bool)],f:impl Fn(usize)->bool)->Vec<Vec<(&'a QReg,bool)>>{
    use std::collections::BTreeMap;
    let mut fixed=BTreeMap::new();for &(q,v)in extra{if let Some(old)=fixed.insert(q.id(),v){if old!=v{return Vec::new();}}}
    let mut free:Vec<&QReg>=Vec::new();let mut codes=Vec::new();
    for &q in inputs{if let Some(&value)=fixed.get(&q.id()){codes.push((None,value));}else{let i=free.iter().position(|x|x.id()==q.id()).unwrap_or_else(||{free.push(q);free.len()-1});codes.push((Some(i),false));}}
    assert!(free.len()<=12);let n=1<<free.len();let mut anf:Vec<_>=(0..n).map(|z|{let code=codes.iter().enumerate().fold(0,|v,(i,(k,b))|v|((if let Some(k)=k{z>>k&1}else{*b as usize})<<i));f(code)}).collect();
    super::q792_poly_r01::plan(anf,extra.len()+1).into_iter().map(|(m,v)|{let mut cs=extra.to_vec();cs.extend(free.iter().enumerate().filter(|&(i,_)|m>>i&1!=0).map(|(i,q)|(*q,v>>i&1!=0)));cs}).collect()
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
// The top-mask is conditionally zero under the unchanged core center
// g=1 && !mask. Each complete F-C-F bank restores it for every input;
// arbitrary inactive U extensions close through the full literal Uinverse.
// This removes one whole data bank rather than treating a selector as free.
fn selected_conditional_mask(circ:&mut Circuit,selectors:Vec<Vec<(&QReg,bool)>>,data:Vec<Vec<(&QReg,bool)>>,out:&QReg,dirty:&[QReg],scratch:&QReg,mask:&QReg){
    if selectors.is_empty()||data.is_empty(){return;}
    if data.len()==1&&data[0].is_empty(){selected_clean(circ,selectors,data,out,dirty,scratch);return;}
    assert_ne!(mask.id(),out.id());assert_ne!(mask.id(),scratch.id());
    assert!(dirty.iter().all(|q|q.id()!=mask.id()));
    assert!(selectors.iter().flatten().all(|(q,_)|q.id()!=mask.id()&&q.id()!=out.id()&&q.id()!=scratch.id()));
    assert!(data.iter().flatten().all(|(q,_)|q.id()!=mask.id()&&q.id()!=out.id()&&q.id()!=scratch.id()));
    let at=circ.b.ops.len();
    selected_clean(circ,selectors.clone(),data.clone(),out,dirty,scratch);
    let old=circ.b.ops.split_off(at);
    let controlled:Vec<_>=data.into_iter().map(|mut term|{term.push((mask,true));term}).collect();
    emit_terms_with_scratch(circ,selectors.clone(),mask,dirty,Some(scratch));
    emit_terms_with_scratch(circ,controlled,out,dirty,Some(scratch));
    emit_terms_with_scratch(circ,selectors,mask,dirty,Some(scratch));
    let count=|ops:&[crate::circuit::Op]|ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();
    let old_t=count(&old);let clean_t=count(&circ.b.ops[at..]);let clean=clean_t<old_t;
    if !clean{circ.b.ops.truncate(at);circ.b.ops.extend(old);}
    eprintln!("FOLD20_SIGN_LOW_CONDITIONAL_MASK_SELECT old_T={old_t} clean_T={clean_t} clean={clean}");
}
// Hold only H=C_high0&&S_high0 in the incoming conditional top-mask.
// Inverted phase scratch is0 only under the unchanged g1&&!top center.
// Each exact SM0/C class loans C5=0 only while its classflag is1; the
// conditional MCX restores every port even for the inactive U extension.
// Literal three-bit specialization of the restored V2 comparator in
// q792_r01_sumchart_r01.rs, inherited from Khattar/Gidney (Vandaele Fig.5).
// It toggles an arbitrary target by a>b and returns both operands exactly.
fn greater_three(circ:&mut Circuit,a:&[QReg],b:&[QReg],out:&QReg){
    assert_eq!(a.len(),3);assert_eq!(b.len(),3);
    let mut ids:Vec<_>=a.iter().chain(b.iter()).map(|q|q.id()).collect();ids.push(out.id());ids.sort();ids.dedup();assert_eq!(ids.len(),7);
    for q in b{circ.x(q);}
    for i in 1..3{circ.cx(&a[i],&b[i]);}circ.cx(&a[2],out);circ.cx(&a[1],&a[2]);
    for i in 0..2{circ.ccx(&a[i],&b[i],&a[i+1]);}circ.ccx(&a[2],&b[2],out);
    for i in (0..2).rev(){circ.ccx(&a[i],&b[i],&a[i+1]);}circ.cx(&a[1],&a[2]);
    for i in (1..3).rev(){circ.cx(&a[i],&b[i]);}for q in b.iter().rev(){circ.x(q);}
}
// One complete rank echo computes [S_high0]*[SM0]*!t0 into MASK.
// Inverted phase supplies scratch0 only at the fixed g1&&!top centers.
// For arbitrary phase/MASK, the same echo remains a pure target-XOR
// header which returns every rank/control/flag/lender; no clean allocation.
fn small_s_header(circ:&mut Circuit,rank:&[QReg],sm:&[QReg],t0:&QReg,mask:&QReg,dirty:&[QReg],scratch:&QReg){
    assert_eq!(rank.len(),5);assert_eq!(sm.len(),4);assert!(!dirty.is_empty());
    let flag=&dirty[0];let rest=&dirty[1..];
    let data:Vec<_>=std::iter::once((flag,true)).chain(sm.iter().map(|q|(q,false))).chain(std::iter::once((t0,false))).collect();
    for _ in 0..2{
        for i in 0..5{if 21>>i&1!=0{circ.x(&rank[i]);}}
        for monomial in [1usize,2,3,4,8,9,10,18,20,25,28,31]{let cs:Vec<_>=(0..5).filter(|&i|monomial>>i&1!=0).map(|i|(&rank[i],true)).collect();gate(circ,&cs,flag,rest);}
        for i in (0..5).rev(){if 21>>i&1!=0{circ.x(&rank[i]);}}
        super::paired_clean_mcx::toggle(circ,&data,mask,scratch);
    }
}
// Replace only ordinary+generic S0 banks. All C1/C2/C3 CommonH banks
// still run after this entire header/data frame returns. MASK is0 only
// at the unchanged core center; every other extension closes inside U/Ui.
fn low_seed_frame(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],w1:&[QReg],w2:&[QReg],out:&QReg,dirty:&[QReg],j:usize,scratch:&QReg,mask:&QReg){
    let at=circ.b.ops.len();let shift=(4-j)%4;
    emit_terms_with_scratch(circ,low_data(w1,w2,j,3,None,0),out,dirty,Some(scratch));
    if shift==3{return;}
    let small_s:Vec<_>=rank_terms(rank,|t|t[2]==0).into_iter().map(|mut term|{term.extend(sm.iter().map(|q|(q,false)));term}).collect();
    selected_conditional_mask(circ,small_s,low_data(w1,w2,j,3,None,1),out,dirty,scratch,mask);
    if shift>1{return;}
    let old=circ.b.ops.split_off(at);
    let hs=circ.b.ops.len();small_s_header(circ,rank,sm,&w1[0],mask,dirty,scratch);let header=circ.b.ops[hs..].to_vec();
    let v1=&w2[257-shift];let v2=&w2[256-shift];let b0=&w2[(259-shift)%259];let b1=&w2[(260-shift)%259];
    let ns=circ.b.ops.len();
    circ.x(v2);circ.ccx(&w1[2],b0,v2);circ.ccx(&w1[1],b1,v2);
    if shift==0{circ.x(v1);circ.ccx(&w1[1],b0,v1);}
    let normalize=circ.b.ops[ns..].to_vec();let rs=circ.b.ops.len();
    if shift==0{circ.cswap(mask,&w2[1],v1);circ.cswap(mask,&w2[2],v2);}else{circ.cswap(mask,&w2[1],v2);}
    let route=circ.b.ops[rs..].to_vec();
    // Header1 implies t0=0: rhs0 cannot affect strict greater. Keeping
    // its original bit avoids overwriting a spectator or borrowing zero.
    greater_three(circ,&w1[..3],&w2[..3],out);
    circ.b.ops.extend(route.into_iter().rev());circ.b.ops.extend(normalize.into_iter().rev());circ.b.ops.extend(header.into_iter().rev());
    let count=|ops:&[crate::circuit::Op]|ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();
    let old_t=count(&old);let frame_t=count(&circ.b.ops[at..]);let frame=frame_t<old_t;
    if !frame{circ.b.ops.truncate(at);circ.b.ops.extend(old);}
    eprintln!("FOLD20_SIGN_LOW_DATA_FRAME_SELECT old_T={old_t} frame_T={frame_t} frame={frame}");
    let _=c;
}

fn low(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],w1:&[QReg],w2:&[QReg],out:&QReg,dirty:&[QReg],j:usize,scratch:&QReg,mask:&QReg){
    low_seed_frame(circ,rank,c,sm,w1,w2,out,dirty,j,scratch,mask);let shift=(4-j)%4;
    if shift==3{return;}
    let at=circ.b.ops.len();
    for kind in 2..=4{
        let selectors:Vec<_>=rank_terms(rank,|t|t[2]==0&&t[1]==0).into_iter().map(|mut term|{term.extend(sm.iter().map(|q|(q,false)));term.extend(c.iter().enumerate().map(|(i,q)|(q,(kind-1+shift)>>i&1!=0)));term}).collect();
        selected_conditional_mask(circ,selectors,low_data(w1,w2,j,3,None,kind),out,dirty,scratch,mask);
    }
    let old=circ.b.ops.split_off(at);
    let plans:Vec<_>=(2..=4).map(|kind|{let terms=simplify_terms(low_data(w1,w2,j,3,None,kind));if super::q792_esop_r01::active(){super::q792_poly_r01::terms(terms,0)}else{terms}}).collect();
    if plans.iter().all(|p|p.is_empty()){assert!(old.is_empty());return;}
    assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(!dirty.is_empty());
    assert!(dirty.iter().all(|q|q.id()!=mask.id()&&q.id()!=scratch.id()&&q.id()!=out.id()&&q.id()!=c[5].id()));
    let high=rank_terms(rank,|t|t[1]==0&&t[2]==0);
    emit_terms_with_scratch(circ,high.clone(),mask,dirty,Some(scratch));
    for (i,data) in plans.into_iter().enumerate(){
        if data.is_empty(){continue;}
        let value=i+1+shift;assert!(value<=6);
        let mut class:Vec<_>=sm.iter().map(|q|(q,false)).collect();class.extend(c.iter().enumerate().map(|(bit,q)|(q,value>>bit&1!=0)));
        gate(circ,&class,scratch,dirty);
        for mut term in data{
            assert!(term.iter().all(|(q,_)|q.id()!=out.id()&&q.id()!=scratch.id()&&q.id()!=mask.id()&&q.id()!=c[5].id()&&q.id()!=dirty[0].id()));
            term.push((mask,true));
            super::conditional_mcx::guarded(circ,scratch,&term,out,&c[5],false,&dirty[0]);
        }
        gate(circ,&class,scratch,dirty);
    }
    emit_terms_with_scratch(circ,high,mask,dirty,Some(scratch));
    let count=|ops:&[crate::circuit::Op]|ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();
    let old_t=count(&old);let cache_t=count(&circ.b.ops[at..]);let cache=cache_t<old_t;
    if !cache{circ.b.ops.truncate(at);circ.b.ops.extend(old);}
    eprintln!("FOLD20_SIGN_LOW_COMMON_H_SELECT old_T={old_t} cache_T={cache_t} cache={cache}");
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
    if super::q792_esop_r01::active(){circ.cx(right,left);circ.x(g);super::q792_esop_r01::paired(circ,controls,truth,&[(left,true)],right,g);circ.x(g);circ.cx(right,left);return;}
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
// Exact XOR output: prepared C_low < virtual S_low. Inputs and lenders
// are restored; the output may start arbitrary, and no phase guard is read.
fn span_carry(circ:&mut Circuit,c:&[QReg],sm:&[QReg],out:&QReg,_dirty:&[QReg],j:usize){
    assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(j<4);
    // Exact seeded V2 comparator, specialized from the inherited Vandaele
    // Fig. 5 comparator in arith/khattar_gidney.rs. Virtual S has four
    // quantum high bits and two classical low bits. The low borrow XORs
    // SM[0] inside the carry ladder, then literally restores it.
    // Every C/SM/output input is admitted; no helper or phase guard is read.
    let low=(4-j)%4;
    for q in &c[2..]{circ.x(q);}
    for i in 0..4{circ.cx(&sm[i],&c[i+2]);}
    circ.cx(&sm[3],out);
    for i in (1..4).rev(){circ.cx(&sm[i-1],&sm[i]);}
    let seed=|circ:&mut Circuit,inverse:bool|{match low{
        0=>{},
        1=>{circ.x(&c[0]);circ.x(&c[1]);circ.ccx(&c[0],&c[1],&sm[0]);circ.x(&c[1]);circ.x(&c[0]);},
        2=>{circ.x(&c[1]);circ.cx(&c[1],&sm[0]);circ.x(&c[1]);},
        3=>{if !inverse{circ.x(&sm[0]);}circ.ccx(&c[0],&c[1],&sm[0]);if inverse{circ.x(&sm[0]);}},
        _=>unreachable!(),
    }};
    seed(circ,false);
    for i in 0..3{circ.ccx(&sm[i],&c[i+2],&sm[i+1]);}
    circ.ccx(&sm[3],&c[5],out);
    for i in (0..3).rev(){circ.ccx(&sm[i],&c[i+2],&sm[i+1]);}
    seed(circ,true);
    for i in 1..4{circ.cx(&sm[i-1],&sm[i]);}
    for i in (0..4).rev(){circ.cx(&sm[i],&c[i+2]);}
    for q in c[2..].iter().rev(){circ.x(q);}
}
// Ported from welttowelt's public A11 source, commit
// d46df612a4932d1cfc00ba62c32a6056691df83c. The existing A support and
// A+C+S boundary imply C+S >= 256-A_hi.
fn sum_low_cut(circ:&Circuit)->usize{256usize.saturating_sub(circ.q797_a_support.map_or(256,|(_,hi)|hi))}
fn gather_span<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],word:&'a[QReg],base:usize,min:usize,max:usize,dirty:&[QReg],g:&QReg,j:usize)->(&'a QReg,Vec<crate::circuit::Op>){
    assert!(dirty.len()>=19);let start=circ.b.ops.len();let max=max.min(253).min(257-circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0));let min=min.max(2).max(sum_low_cut(circ)).min(max);assert!(min<=max);
    // Complete every unsupported address with a distinct physical data rail.
    // A full XOR permutation permits arbitrary dirty high-address lenders.
    let mut bank=vec![None;256];let mut used=std::collections::BTreeSet::new();
    for value in min..=max{let at=base-value;assert!(at<word.len());bank[value]=Some(&word[at]);assert!(used.insert(at));}
    let free:Vec<_>=(0..word.len()).filter(|v|!used.contains(v)).collect();let mut free=free.into_iter();for leaf in &mut bank{if leaf.is_none(){*leaf=Some(&word[free.next().unwrap()]);}}
    let mut roots:Vec<_>=bank.into_iter().map(Option::unwrap).collect();for level in 0..6{let mut next=Vec::new();for pair in roots.chunks_exact(2){circ.cswap(&c[level],pair[0],pair[1]);next.push(pair[0]);}roots=next;}assert_eq!(roots.len(),4);
    // On g=1, X(g) gives zero for the sum carry. Compute it once,
    // rotate all four roots by that carry, restore g, then route by Ch+Sh.
    // Off g the complete route is arbitrary but its literal inverse restores
    // every rail around the independently g-controlled data center.
    circ.x(g);let carry_at=circ.b.ops.len();
    span_carry(circ,c,sm,g,dirty,j);let carry_ops=circ.b.ops[carry_at..].to_vec();
    for i in 0..3{circ.cswap(g,roots[i],roots[i+1]);}
    circ.b.ops.extend(carry_ops.into_iter().rev());circ.x(g);
    let ts=triples();
    for i in [0,2]{route_swap(circ,&rank.iter().collect::<Vec<_>>(),ts.iter().map(|t|(t[1]+t[2])&1!=0).collect(),roots[i],roots[i+1],g);}
    route_swap(circ,&rank.iter().collect::<Vec<_>>(),ts.iter().map(|t|(t[1]+t[2])&2!=0).collect(),roots[0],roots[2],g);
    (roots[0],circ.b.ops[start..].to_vec())
}
// Two output banks use the SAME metadata address. Keep its carry and
// high predicates in the active phase wire while routing both banks;
// restore the phase before the sign consumer, then reverse literally.
fn gather_pair_span<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],words:[&'a[QReg];2],base:usize,min:usize,max:usize,dirty:&[QReg],g:&QReg,j:usize)->([&'a QReg;2],Vec<crate::circuit::Op>){
    assert!(dirty.len()>=19);let start=circ.b.ops.len();let max=max.min(253).min(257-circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0));let min=min.max(2);assert!(min<=max);
    let mut banks=Vec::new();
    for word in words{
        let mut bank=vec![None;256];let mut used=std::collections::BTreeSet::new();
        for value in min..=max{let at=base-value;assert!(at<word.len());bank[value]=Some(&word[at]);assert!(used.insert(at));}
        let free:Vec<_>=(0..word.len()).filter(|v|!used.contains(v)).collect();let mut free=free.into_iter();for leaf in &mut bank{if leaf.is_none(){*leaf=Some(&word[free.next().unwrap()]);}}
        let mut roots:Vec<_>=bank.into_iter().map(Option::unwrap).collect();for level in 0..6{let mut next=Vec::new();for pair in roots.chunks_exact(2){circ.cswap(&c[level],pair[0],pair[1]);next.push(pair[0]);}roots=next;}assert_eq!(roots.len(),4);banks.push(roots);
    }
    circ.x(g);let at=circ.b.ops.len();span_carry(circ,c,sm,g,dirty,j);let carry=circ.b.ops[at..].to_vec();
    for roots in &banks{for i in 0..3{circ.cswap(g,roots[i],roots[i+1]);}}
    circ.b.ops.extend(carry.into_iter().rev());circ.x(g);
    let ts=triples();let input:Vec<_>=rank.iter().collect();
    for bit in 0..2{
        circ.x(g);let at=circ.b.ops.len();super::q792_fold20_r01::table(circ,&input,ts.iter().map(|t|(t[1]+t[2])>>bit&1!=0).collect(),&[],g,dirty);let predicate=circ.b.ops[at..].to_vec();
        for roots in &banks{if bit==0{for i in [0,2]{circ.cswap(g,roots[i],roots[i+1]);}}else{circ.cswap(g,roots[0],roots[2]);}}
        circ.b.ops.extend(predicate.into_iter().rev());circ.x(g);
    }
    ([banks[0][0],banks[1][0]],circ.b.ops[start..].to_vec())
}
fn gather_sum<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],word:&'a[QReg],base:usize,min:usize,dirty:&[QReg],g:&QReg,j:usize)->(&'a QReg,Vec<crate::circuit::Op>){gather_span(circ,rank,c,sm,word,base,min,253,dirty,g,j)}

// Open two disjoint 128-rail W2 banks for adjacent cargo addresses.
// O[b]=W2[257-2b] selects floor(span/2); E[b]=W2[258-2b]
// selects ceil(span/2). On the inherited general span2..253 care the
// roots, ordered by prepared C0, are exactly W2[257-span],W2[258-span].
// Every C/g loan returns before a center; arbitrary off-g routing is
// closed by the complete literal inverse around g-controlled centers.
fn gather_cargo_window<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],word:&'a[QReg],dirty:&[QReg],g:&QReg,j:usize)->([&'a QReg;2],Vec<crate::circuit::Op>){
    assert!(dirty.len()>=19);let start=circ.b.ops.len();
    let mut odd:Vec<_>=(0..128).map(|b|&word[257-2*b]).collect();
    let mut even:Vec<_>=(0..128).map(|b|&word[258-2*b]).collect();
    for level in 1..6{let mut next=Vec::new();for pair in odd.chunks_exact(2){circ.cswap(&c[level],pair[0],pair[1]);next.push(pair[0]);}odd=next;}
    // Paid ceil-low-address frame: X(g) is zero exactly on the active
    // guard. Paired MCX restores scratch/controls on every extension;
    // its captured inverse returns C before any high-address predicate.
    let increment_at=circ.b.ops.len();circ.x(g);
    for k in (1..6).rev(){let cs:Vec<_>=c[..k].iter().map(|q|(q,true)).collect();super::paired_clean_mcx::toggle(circ,&cs,&c[k],g);}
    circ.x(g);let increment=circ.b.ops[increment_at..].to_vec();
    for level in 1..6{let mut next=Vec::new();for pair in even.chunks_exact(2){circ.cswap(&c[level],pair[0],pair[1]);next.push(pair[0]);}even=next;}
    circ.b.ops.extend(increment.into_iter().rev());assert_eq!(odd.len(),4);assert_eq!(even.len(),4);
    // Carry and C==63 are disjoint for every prepared-C/virtual-S pair.
    // Thus O uses carry, while E uses carry XOR C==63 for its +C0
    // block overflow. Compute/return the original carry only once.
    circ.x(g);let carry_at=circ.b.ops.len();span_carry(circ,c,sm,g,dirty,j);let carry=circ.b.ops[carry_at..].to_vec();
    for i in 0..3{circ.cswap(g,odd[i],odd[i+1]);}
    let overflow_at=circ.b.ops.len();let cs:Vec<_>=c.iter().map(|q|(q,true)).collect();gate(circ,&cs,g,dirty);let overflow=circ.b.ops[overflow_at..].to_vec();
    for i in 0..3{circ.cswap(g,even[i],even[i+1]);}
    circ.b.ops.extend(overflow.into_iter().rev());circ.b.ops.extend(carry.into_iter().rev());circ.x(g);
    // The two banks share the paid Ch+Sh high predicates. g is returned
    // after each chart and before either cargo consumer observes it.
    let ts=triples();let input:Vec<_>=rank.iter().collect();
    for bit in 0..2{
        circ.x(g);let at=circ.b.ops.len();super::q792_fold20_r01::table(circ,&input,ts.iter().map(|t|(t[1]+t[2])>>bit&1!=0).collect(),&[],g,dirty);let predicate=circ.b.ops[at..].to_vec();
        for roots in [&odd,&even]{if bit==0{for i in [0,2]{circ.cswap(g,roots[i],roots[i+1]);}}else{circ.cswap(g,roots[0],roots[2]);}}
        circ.b.ops.extend(predicate.into_iter().rev());circ.x(g);
    }
    circ.cswap(&c[0],odd[0],even[0]);
    ([odd[0],even[0]],circ.b.ops[start..].to_vec())
}

// Fully paid adjacent W1 window. O[b]=W1[2b+1] selects ceil(A/2),
// E[b]=W1[2b] selects floor(A/2)+1. All banks use only ports0..255.
// At A254 the first root is the arbitrary W1[0] dummy, exactly canceled
// by the unchanged two first-passenger swaps; second root is W1[255].
fn gather_a_cargo_window<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&'a[QReg],dirty:&[QReg],g:&QReg)->([&'a QReg;2],Vec<crate::circuit::Op>){
    assert!(dirty.len()>=19);let start=circ.b.ops.len();let mut banks=Vec::new();
    for parity in 0..2{
        let mut roots:Vec<_>=(0..128).map(|b|&word[2*b+usize::from(parity==0)]).collect();
        // O: conditionally increment A1..5 by A0 (ceil). E: increment
        // A1..5 unconditionally (floor+1). Each active-zero phase loan
        // is paid and returns before any high predicate or consumer.
        let at=circ.b.ops.len();circ.x(g);
        for k in (1..6).rev(){let cs:Vec<_>=a[usize::from(parity==1)..k].iter().map(|q|(q,true)).collect();super::paired_clean_mcx::toggle(circ,&cs,&a[k],g);}
        circ.x(g);let increment=circ.b.ops[at..].to_vec();
        for level in 1..6{let mut next=Vec::new();for pair in roots.chunks_exact(2){circ.cswap(&a[level],pair[0],pair[1]);next.push(pair[0]);}roots=next;}
        circ.b.ops.extend(increment.into_iter().rev());assert_eq!(roots.len(),4);
        // The O high carry is A_low63; E carry is A1..5 all one.
        // Compute/return exact flags on every physical A and helper.
        circ.x(g);let at=circ.b.ops.len();let cs:Vec<_>=a[usize::from(parity==1)..].iter().map(|q|(q,true)).collect();gate(circ,&cs,g,dirty);let carry=circ.b.ops[at..].to_vec();
        for i in 0..3{circ.cswap(g,roots[i],roots[i+1]);}
        circ.b.ops.extend(carry.into_iter().rev());circ.x(g);banks.push(roots);
    }
    // Both banks share the complete paid A-high predicates. Restore the
    // phase after every compute/swap/return before either center reads g.
    let ts=triples();let input:Vec<_>=rank.iter().collect();
    for bit in 0..2{
        circ.x(g);let at=circ.b.ops.len();super::q792_fold20_r01::table(circ,&input,ts.iter().map(|t|t[0]>>bit&1!=0).collect(),&[],g,dirty);let predicate=circ.b.ops[at..].to_vec();
        for roots in &banks{if bit==0{for i in [0,2]{circ.cswap(g,roots[i],roots[i+1]);}}else{circ.cswap(g,roots[0],roots[2]);}}
        circ.b.ops.extend(predicate.into_iter().rev());circ.x(g);
    }
    circ.x(&a[0]);circ.cswap(&a[0],banks[0][0],banks[1][0]);circ.x(&a[0]);
    ([banks[0][0],banks[1][0]],circ.b.ops[start..].to_vec())
}

fn cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,dirty,j,false);
    let mut a254=vec![(g,true)];a254.extend(rank.iter().enumerate().map(|(i,q)|(q,29>>i&1!=0)));a254.extend(a.iter().enumerate().map(|(i,q)|(q,254>>i&1!=0)));
    // The first ordinary transfer's net guard is g AND NOT A254.
    // These exact A254 head actions therefore commute with it, even
    // when data rails overlap. Keep their original literal physical
    // swaps before opening the shared window; no head decoder is free.
    for sum in [1usize,3]{let mut cs=a254.clone();cs.extend(c.iter().enumerate().map(|(i,q)|(q,sum>>i&1!=0)));cs.extend(sm.iter().map(|q|(q,false)));swap(circ,&cs,&w2[255],&w2[257-sum],dirty);}
    let([r0,r1],window)=gather_cargo_window(circ,rank,c,sm,w2,dirty,g,j);
    // Move the SECOND passenger first. The public-supported A trees,
    // exact A254 cancellation and first-passenger center are unchanged.
    // Public A-support pruning can make either complete paid architecture
    // cheaper. Price the whole two-center W1 body after actual primitive
    // lowering, choose strictly fewer Toffolis, and keep old on ties.
    // Both bodies return every A/rank/g/helper and are identical on the
    // existing active care; each is identity off g inside the same W2
    // window. This choice never depends on quantum data or a seed.
    let body_at=circ.b.ops.len();
    let(l,lop)=gather_a(circ,rank,a,w1,2,253,dirty,g);
    swap(circ,&[(g,true)],l,r0,dirty);swap(circ,&a254,l,r0,dirty);
    circ.b.ops.extend(lop.into_iter().rev());
    let(l,lop)=gather_a(circ,rank,a,w1,1,254,dirty,g);circ.cswap(g,l,r1);circ.b.ops.extend(lop.into_iter().rev());
    let separate=circ.b.ops.split_off(body_at);
    let([l0,l1],left_window)=gather_a_cargo_window(circ,rank,a,w1,dirty,g);
    swap(circ,&[(g,true)],l0,r0,dirty);swap(circ,&a254,l0,r0,dirty);circ.cswap(g,l1,r1);
    circ.b.ops.extend(left_window.into_iter().rev());
    let count=|ops:&[crate::circuit::Op]|ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();
    let old_t=count(&separate);let joint_t=count(&circ.b.ops[body_at..]);let joint=joint_t<old_t;
    if !joint{circ.b.ops.truncate(body_at);circ.b.ops.extend(separate);}
    let (lo,hi)=circ.q797_a_support.unwrap_or((0,256));eprintln!("FOLD20_SIGN_A_WINDOW_SELECT lo={lo} hi={hi} separate_T={old_t} joint_T={joint_t} joint={joint}");
    circ.b.ops.extend(window.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,dirty,j,true);
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
fn mask_loan(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,_cache:&QReg,mask:&QReg,w1:&[QReg],dirty:&[QReg]){
    let start=circ.b.ops.len();let max_c=257-circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0);let mut nodes:Vec<_>=(0..256).map(|v|if v>=3&&v<=max_c{Some(&w1[258-v])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{route_predicate(circ,rank,1,level-6,l,r,g);}Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
    let route=circ.b.ops[start..].to_vec();let root=nodes[0].unwrap();circ.cswap(g,root,mask);
    // Hold only the exact high-C rank predicate in one arbitrary dirty
    // lender. Both C1/C2 correction swaps use a paid parity frame; no mask
    // or lender is assumed clean. The route inverse does not read d and
    // returns rank/C/g, so the held predicate survives its full extension.
    let d=&dirty[0];let rest=&dirty[1..];
    let consume=|circ:&mut Circuit,q:&QReg|{
        circ.cx(&c[0],&c[1]);
        let mut cs=vec![(d,true),(g,true),(&c[1],true)];cs.extend(c[2..].iter().map(|q|(q,false)));
        swap(circ,&cs,q,mask,rest);
        circ.cx(&c[0],&c[1]);
    };
    consume(circ,root);
    let at=circ.b.ops.len();let inputs:Vec<_>=rank.iter().collect();
    super::q792_fold20_r01::table(circ,&inputs,triples().into_iter().map(|t|t[1]==0).collect(),&[],d,rest);
    let held=circ.b.ops[at..].to_vec();
    consume(circ,root);
    circ.b.ops.extend(route.into_iter().rev());
    consume(circ,&w1[255]);
    circ.b.ops.extend(held.into_iter().rev());
    consume(circ,&w1[255]);
}
/// Existing carry is zero only on the caller's active output care.
/// The upper four bits use the MAJ/UMA ripple identity, with no overflow
/// output. Arbitrary incoming carry gives a different bijective C frame;
/// all SM/carry ports return. The caller pays the same frame inverse after
/// restoring this carry, and disabled consumers close all other inputs.
/// General owns MASK between the full maskloan and its inverse; A-small
/// owns m7 only under its unchanged m7=0 output literal. No clean allocation.
pub(super) fn prepare_sum_conditional(circ:&mut Circuit,c:&[QReg],sm:&[QReg],carry:&QReg,j:usize,inverse:bool){
    assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(j<4);
    let mut ids:Vec<_>=c.iter().chain(sm.iter()).map(|q|q.id()).collect();ids.push(carry.id());ids.sort();ids.dedup();assert_eq!(ids.len(),11,"Sign sum carry aliases an operand");
    let at=circ.b.ops.len();let low=(4-j)%4;
    match low{
        0=>{},
        1=>{circ.ccx(&c[0],&c[1],carry);circ.cx(&c[0],&c[1]);circ.x(&c[0]);},
        2=>{circ.cx(&c[1],carry);circ.x(&c[1]);},
        3=>{circ.cx(&c[0],carry);circ.cx(&c[1],carry);circ.ccx(&c[0],&c[1],carry);circ.x(&c[0]);circ.cx(&c[0],&c[1]);},
        _=>unreachable!(),
    }
    for i in 0..3{let a=&sm[i];let b=&c[i+2];let h=if i==0{carry}else{&sm[i-1]};circ.cx(a,b);circ.cx(a,h);circ.ccx(h,b,a);}
    circ.cx(&sm[3],&c[5]);circ.cx(&sm[2],&c[5]);
    for i in (0..3).rev(){let a=&sm[i];let b=&c[i+2];let h=if i==0{carry}else{&sm[i-1]};circ.ccx(h,b,a);circ.cx(a,h);circ.cx(h,b);}
    match low{
        0=>{},
        1=>{circ.x(&c[0]);circ.x(&c[1]);circ.ccx(&c[0],&c[1],carry);circ.x(&c[1]);circ.x(&c[0]);},
        2=>{circ.cx(&c[1],carry);circ.x(carry);},
        3=>{circ.x(carry);circ.ccx(&c[0],&c[1],carry);},
        _=>unreachable!(),
    }
    if inverse{circ.b.ops[at..].reverse();}
}

fn top_flag_prepared(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,_cache:&QReg,mask:&QReg,w1:&[QReg],dirty:&[QReg],j:usize){
    let(q,route)=gather_sum(circ,rank,c,sm,w1,257,3,dirty,g,j);
    circ.ccx(g,q,mask);
    if j!=1{let terms=rank_terms(rank,|t|t[1]+t[2]==0).into_iter().map(|mut cs|{cs.extend([(g,true),(q,true)]);cs.extend(sm.iter().map(|x|(x,false)));cs.extend(c.iter().enumerate().map(|(i,x)|(x,2usize>>i&1!=0)));cs}).collect();emit_rank_terms(circ,terms,rank,mask,dirty);}
    circ.b.ops.extend(route.into_iter().rev());
}

fn core_prepared(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,top:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    let start=circ.b.ops.len();
    for i in 3..256{circ.cx(&w1[i],&w2[i]);}
    for i in (4..256).rev(){circ.cx(&w1[i-1],&w1[i]);}
    // At the small-S v1/v2 readers, undo D=target XOR original_source.
    // The neighboring-XOR source frame reconstructs original t_i by the
    // prefix XOR source[3..=i]. These v positions are always >=k, outside
    // the comparison's causal prefix, so they can stay normalized until
    // the exact inverse. No additional output or clean rail is needed.
    let shift=(4-j)%4;
    if shift<3{for pos in [257-shift,256-shift]{if pos<256{for i in 3..=pos{circ.cx(&w1[i],&w2[pos]);}}}}
    circ.x(g);low(circ,rank,c,sm,w1,w2,&w1[3],dirty,j,g,top);circ.x(g);
    // x_i=t_i XOR B_i; D_i=t_i XOR u_i. Adjacent-XOR preparation gives
    // x_(i+1)=t_(i+1) XOR B_i XOR x_i*D_i with one negative-control CCX.
    for i in 3..255{circ.x(&w2[i]);circ.ccx(&w1[i],&w2[i],&w1[i+1]);circ.x(&w2[i]);}
    let compute=circ.b.ops[start..].to_vec();
    // The active general domain has 2<=C+S<=253 (k>=4); all other
    // reachable branches were parked. Cache is the prepared addition carry.
    // The existing adjacent-XOR/carry frame already gives
    // x[k+1] = original_t[k+1] XOR original_t[k] XOR x[k]*!physical_D[k].
    // Read that successor instead of gathering both x[k] and D[k]. After
    // the unchanged literal compute inverse, the second successor read
    // supplies original_t[k+1], reproducing the exact old Sign delta.
    // General span2..253 means k+1=4..255; no omitted source rail is used.
    let(s,route)=gather_span(circ,rank,c,sm,w1,257,2,253,dirty,g,j);
    gate(circ,&[(g,true),(top,false),(s,true)],sign,dirty);
    circ.b.ops.extend(route.into_iter().rev());
    circ.b.ops.extend(compute.into_iter().rev());
    let(s,sop)=gather_span(circ,rank,c,sm,w1,257,2,253,dirty,g,j);
    gate(circ,&[(g,true),(top,false),(s,true)],sign,dirty);circ.b.ops.extend(sop.into_iter().rev());
}

pub(super) fn general(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize){
    let begin=circ.b.ops.len();
    let movestart=circ.b.ops.len();
    // Internal S0 is just before the exit's final right rotation: A254's
    // second passenger is still W2[256]. S>0 boundary callers use W2[255].
    if j==0{let mut cs=vec![(p1,true)];cs.extend(rank.iter().enumerate().map(|(i,q)|(q,29>>i&1!=0)));cs.extend(a.iter().enumerate().map(|(i,q)|(q,254>>i&1!=0)));cs.extend(sm.iter().map(|q|(q,false)));swap(circ,&cs,&w2[255],&w2[256],helpers);}
    cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);let moves=circ.b.ops[movestart..].to_vec();;
    let mask=&helpers[0];let dirty=&helpers[1..];let ls=circ.b.ops.len();mask_loan(circ,rank,c,p1,p2,mask,w1,dirty);let loan=circ.b.ops[ls..].to_vec();;
    // MASK is zero after the complete cargo/head and maskloan transfer.
    // Hold this one sum frame through B/O/C/B^-1: B changes MASK, so its
    // literal inverse must restore the carry before the sum frame closes.
    prepare_sum_conditional(circ,c,sm,mask,j,false);
    let ts=circ.b.ops.len();top_flag_prepared(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);let top=circ.b.ops[ts..].to_vec();;
    circ.ccx(p1,mask,sign);
    // Mask is now a funded zero cache; P2 retains the fixed top branch.
    // Keeping that branch explicit avoids sharing the short-domain park.
    core_prepared(circ,rank,c,sm,p1,p2,mask,sign,w1,w2,dirty,j);;
    circ.b.ops.extend(top.into_iter().rev());prepare_sum_conditional(circ,c,sm,mask,j,true);circ.b.ops.extend(loan.into_iter().rev());circ.b.ops.extend(moves.into_iter().rev());
    for op in &circ.b.ops[begin..]{assert!(rank.iter().any(|r|r.id()==p2.id())||[op.q_target.0,op.q_control1.0,op.q_control2.0].iter().all(|&q|q!=p2.id() as u64),"general Sign consumed leased phase");}
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,_n:usize){
    assert!(helpers.len()>=22);let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    let mut last=start;let mut stage=|circ:&Circuit,name:&str|{if std::env::var_os("Q793_SIGN_CENSUS").is_some(){let ops=&circ.b.ops[last..];eprintln!("Q793_SIGN_R06_STAGE j={j} stage={name} ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count());last=circ.b.ops.len();}};
    super::q798_sign_erase::code(circ,p1,p2,sign,helpers,false);
    short_compare(circ,rank,a,c,sm,p1,p2,sign,w1,w2,helpers,j);stage(circ,"short");
    short_flag(circ,rank,c,sm,p1,p2,helpers,j);super::q795_t11::park_c1(circ,p1,p2,sign,helpers);stage(circ,"bypass");
    general(circ,rank,a,c,sm,p1,p2,sign,w1,w2,helpers,j);
    super::q795_t11::park_c1(circ,p1,p2,sign,helpers);short_flag(circ,rank,c,sm,p1,p2,helpers,j);super::q798_sign_erase::code(circ,p1,p2,sign,helpers,true);stage(circ,"return");
    assert_eq!(circ.b.next_qubit,owned);for op in &circ.b.ops[start..]{for h in [256,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Sign touched omitted source{h}");}}
}

#[path="q793_sign_dynamic_r05_check.rs"]
pub mod verification;
