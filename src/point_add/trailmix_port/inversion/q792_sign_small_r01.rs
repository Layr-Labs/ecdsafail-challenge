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
pub(super) fn selected(circ:&mut Circuit,rank:&[QReg],selectors:Vec<Vec<(&QReg,bool)>>,data:Vec<Vec<(&QReg,bool)>>,out:&QReg,dirty:&[QReg]){
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
// A cache port is borrowed by XOR, preserving either incoming value.
// The center queries only residue 1,0,63,62 for k=0,1,2,3. On those
// residues the exact overflow reduces to one small-S predicate or constant.
// Other prepared residues can have any cache extension because the center
// is a target-XOR enabled by the exact endpoint equality, and the literal
// inverse restores the port, every operand and all arbitrary dirty lenders.
pub(super) fn short_carry_port(circ:&mut Circuit,sm:&[QReg],g:&QReg,cache:&QReg,dirty:&[QReg],j:usize,k:usize,inverse:bool){
    assert!(j<4&&k<=3);let low=(4-j)%4;let at=circ.b.ops.len();
    if k<=1{
        if low==0||(low==1&&k==0){
            circ.cx(g,cache);let mut cs=vec![(g,true)];cs.extend(sm.iter().map(|q|(q,false)));gate(circ,&cs,cache,dirty);
        }else{circ.cx(g,cache);}
    }else if low==3&&k==3{
        let mut cs=vec![(g,true)];cs.extend(sm.iter().map(|q|(q,true)));gate(circ,&cs,cache,dirty);
    }
    if inverse{circ.b.ops[at..].reverse();}
}
pub(super) fn short_selectors<'a>(rank:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,cache:&'a QReg,j:usize,k:usize,extra:&'a[QReg],small:bool)->Vec<Vec<(&'a QReg,bool)>>{
    let ts=triples();let value=257-k;let mut terms=Vec::new();
    for(r,t)in ts.iter().enumerate(){if t[0]!=0||(small&&t[2]!=0){continue;}for carry in 0..2{if t[1]+t[2]+carry!=value/64{continue;}
        let mut term=vec![(g,true),(cache,carry!=0)];term.extend(extra.iter().map(|q|(q,false)));term.extend(rank.iter().enumerate().map(|(i,q)|(q,r>>i&1!=0)));term.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));if small{term.extend(sm.iter().map(|q|(q,false)));}terms.push(term);
    }}
    let _=j;terms
}
fn short_compare(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,extra:&[QReg]){
    let lower=circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0);if lower>3{return;}
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,dirty,j,false);let low=(4-j)%4;
    // The two high4 endpoints share one carry-port loan for low=0/2/3.
    // Low=1 has different exact laws at residues1 and0 and pays both loans.
    for (first,last)in [(0usize,1usize),(2,3)]{
        if last<lower{continue;}let begin=first.max(lower);let shared=first==0&&low!=1;
        if shared{short_carry_port(circ,sm,g,cache,dirty,j,first,false);}
        for k in begin..=last{
            if !shared{short_carry_port(circ,sm,g,cache,dirty,j,k,false);}
            let ordinary=if k==0{vec![Vec::new()]}else{low_data_indexed(w1,w2,j,k,None,0,Some(a))};
            selected(circ,rank,short_selectors(rank,c,sm,g,cache,j,k,extra,false),ordinary,sign,dirty);
            if k>0&&low<3{selected(circ,rank,short_selectors(rank,c,sm,g,cache,j,k,extra,true),low_data_indexed(w1,w2,j,k,None,1,Some(a)),sign,dirty);}
            if !shared{short_carry_port(circ,sm,g,cache,dirty,j,k,true);}
        }
        if shared{short_carry_port(circ,sm,g,cache,dirty,j,first,true);}
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,dirty,j,true);
}

pub(super) fn compare(circ:&mut Circuit,m:&[QReg],g:&QReg,cache:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    super::q792_asmall_chart_r01::emit(circ,m,dirty,false);let rank=super::q792_asmall_chart_r01::rank(m);
    short_compare(circ,&rank,&m[4..10],&m[10..16],&m[16..20],g,cache,sign,w1,w2,dirty,j,&m[7..10]);
    super::q792_asmall_chart_r01::emit(circ,m,dirty,true);
}
fn raw_sum1(circ:&mut Circuit,m:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg],j:usize){
    // Raw sum1 is separate; raw S0 is intentional at the exit boundary.
    if j==0||j==3{let cv=usize::from(j==0);super::q792_fold20_predicate_r01::rank_low(circ,m,0x20802001,(63<<6)|(15<<12),cv<<6,&[(g,true)],out,dirty);}
}
pub(super) fn flag_charted(circ:&mut Circuit,m:&[QReg],rank:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg],j:usize){
    // The paid A-small chart supplies all five rank bits and three exact
    // zero-rail controls. Specialize the comparator only at its four
    // observed prepared C residues; every raw/offguard extension agrees.
    let c=&m[10..16];let sm=&m[16..20];let rest=&dirty[1..];let ts=triples();let low=(4-j)%4;
    let max_sum=257-circ.q797_a_support.map(|(lo,_)|lo).unwrap_or(0);let word:Vec<_>=rank.iter().collect();
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,rest,j,false);
    for (h,all)in [(3usize,[254usize,255]),(4,[256usize,257])]{
        let values:Vec<_>=all.into_iter().filter(|&v|v<=max_sum).collect();if values.is_empty(){continue;}
        let mut base=vec![(g,true)];base.extend(m[7..10].iter().map(|q|(q,false)));
        // Both adjacent residues share bits1..5. Retain bit0 only if the
        // public A support removed the other member of this exact pair.
        base.extend((usize::from(values.len()==2)..6).map(|i|(&c[i],values[0]>>i&1!=0)));
        let high=|carry:usize|ts.iter().map(|t|t[0]==0&&t[1]+t[2]+carry==h).collect::<Vec<_>>();
        let carry_base=usize::from(h==4);super::q792_fold20_r01::table(circ,&word,high(carry_base),&base,out,dirty);
        if h==3{
            if low==3&&values.contains(&254){let mut last=base.clone();if values.len()==2{last.push((&c[0],false));}last.extend(sm.iter().map(|q|(q,true)));let delta=ts.iter().map(|t|t[0]==0&&((t[1]+t[2]==h)^(t[1]+t[2]+1==h))).collect();super::q792_fold20_r01::table(circ,&word,delta,&last,out,dirty);}
        }else{
            let zero:Vec<_>=values.iter().copied().filter(|&v|low<=v%64).collect();if !zero.is_empty(){let mut first=base.clone();if zero.len()!=values.len(){first.push((&c[0],zero[0]%2!=0));}first.extend(sm.iter().map(|q|(q,false)));let delta=ts.iter().map(|t|t[0]==0&&((t[1]+t[2]==h)^(t[1]+t[2]+1==h))).collect();super::q792_fold20_r01::table(circ,&word,delta,&first,out,dirty);}
        }
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,rest,j,true);
}

pub(super) fn compare_and_flag(circ:&mut Circuit,m:&[QReg],g:&QReg,cache:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    super::q792_asmall_chart_r01::emit(circ,m,dirty,false);let rank=super::q792_asmall_chart_r01::rank(m);
    short_compare(circ,&rank,&m[4..10],&m[10..16],&m[16..20],g,cache,sign,w1,w2,dirty,j,&m[7..10]);
    // The charted flag body and raw sum1 are target-XOR oracles which restore
    // metadata and lenders. The body never reads `cache`, so they commute.
    flag_charted(circ,m,&rank,g,cache,dirty,j);
    super::q792_asmall_chart_r01::emit(circ,m,dirty,true);raw_sum1(circ,m,g,cache,dirty,j);
}
pub(super) fn flag(circ:&mut Circuit,m:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg],j:usize){
    raw_sum1(circ,m,g,out,dirty,j);
    super::q792_asmall_chart_r01::emit(circ,m,dirty,false);let rank=super::q792_asmall_chart_r01::rank(m);
    flag_charted(circ,m,&rank,g,out,dirty,j);super::q792_asmall_chart_r01::emit(circ,m,dirty,true);
}
