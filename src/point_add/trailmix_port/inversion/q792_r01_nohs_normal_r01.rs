//! Timefix R01: one normal scan including normalized A1/S1 donor geometry.
//! No global padding loan, cargo relocation, endpoint routing, or allocator hook.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_arithmetic5 as arithmetic,metadata_muxlease as mux,length_recompute::mixed_mcx};
#[path="metadata_remainder5_programs.rs"] mod programs;
#[path="metadata_phase115_programs.rs"] mod c_programs;
#[path="q793_r01_numeric_partial.rs"] mod numeric_chart;
#[path="q793_r01_numeric_seed_check.rs"] mod numeric_seed_check;
#[path="q792_r01_joint_window_r01.rs"] mod joint_window;
#[path="q792_r01_seed_parity_r01.rs"] mod seed_parity;
#[path="q792_r01_seed_shared_r01.rs"] mod seed_shared;
#[path="q792_r01_prefix_hold_r01.rs"] mod prefix_hold;

fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v) in cs { assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}
        else{unique.push((q,v));}
    }
    mixed_mcx(circ,&unique,out,dirty);
}
/// On g1, X(g) is a genuine zero scratch. On g0 the primitive remains
/// a pure HA XOR with every control restored; the second identical seed
/// cancels it after the exact carry frame and disabled updates restore data.
fn seed_ha_gate(circ:&mut Circuit,cs:&[(&QReg,bool)],ha:&QReg,g:&QReg){
    assert!(cs.iter().any(|&(q,v)|q.id()==g.id()&&v));
    let controls:Vec<_>=cs.iter().copied().filter(|&(q,_)|q.id()!=g.id()).collect();
    circ.x(g);super::paired_clean_mcx::toggle(circ,&controls,ha,g);circ.x(g);
}
/// The already-produced high-S flag and original C0 literal jointly
/// imply a known rank bit. This uses the same restored-control AND reduction
/// as conditional_mcx, with BOTH guards in the sole exact dirty4 target
/// action. An absent guard therefore disables the center for arbitrary
/// scratch. The rank/SM loans and both existing dirty lenders return before
/// the high-S oracle inverse. Only X/CX/CCX; 12T, no extra clean qubit.
fn two_guard_rank_mask(circ:&mut Circuit,high:&QReg,c0:&QReg,c0_value:bool,sm:&[QReg],low:usize,
                       mask:&QReg,rank_scratch:&QReg,known:bool,dirty:&[QReg]){
    assert_eq!(sm.len(),4);assert!(low<16&&dirty.len()>=2);
    let mut ids:Vec<_>=sm.iter().chain([high,c0,mask,rank_scratch,&dirty[0],&dirty[1]]).map(QReg::id).collect();
    ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
    if !c0_value{circ.x(c0);}
    for(b,q)in sm.iter().enumerate(){if low>>b&1==0{circ.x(q);}}
    if known{circ.x(rank_scratch);}
    circ.ccx(&sm[0],&sm[1],rank_scratch);
    circ.ccx(&sm[2],&sm[3],&sm[1]);circ.x(&sm[1]);
    crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder(circ,
        &[high,c0,rank_scratch,&sm[1]],mask,&[&dirty[0],&dirty[1]]);
    circ.x(&sm[1]);circ.ccx(&sm[2],&sm[3],&sm[1]);
    circ.ccx(&sm[0],&sm[1],rank_scratch);
    if known{circ.x(rank_scratch);}
    for(b,q)in sm.iter().enumerate().rev(){if low>>b&1==0{circ.x(q);}}
    if !c0_value{circ.x(c0);}
}

fn a_flags<'a>(rank:&'a[QReg],a:&'a[QReg],value:usize)->Vec<Vec<(&'a QReg,bool)>>{
    programs::EQUAL[value/64].iter().map(|&(m,v)|a.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0))
        .chain((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0))).collect()).collect()
}
fn c_flags<'a>(rank:&'a[QReg],c:&'a[QReg],value:usize)->Vec<Vec<(&'a QReg,bool)>>{
    c_programs::C_EQUAL[value/64].iter().map(|&(m,v)|
        c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0))
        .chain((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0))).collect()).collect()
}

/// Temporary route only. Low coefficient rails may move, so copy the result
/// into a separate SM loan and undo the entire route before decoding the chart.
fn prefix_xor(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],word:&[QReg],base:&[(&QReg,bool)],out:&QReg,
              offset:usize,needed_c:usize,g:&QReg,carry:&QReg,dirty:&[QReg]){
    assert!((1..=2).contains(&needed_c));
    let(root,route)=super::q793_r01_routes_v1::gather(circ,rank,a,c,word,g,carry,offset);
    arithmetic::add(circ,a,c,None,true); // Read original C and its parity.
    let mut cs=base.to_vec();cs.push((root,true));gate(circ,&cs,out,dirty);
    for absent in 0..needed_c {for flag in c_flags(rank,c,absent){
        let mut ex=cs.clone();ex.extend(flag);gate(circ,&ex,out,dirty);
    }}
    arithmetic::add(circ,a,c,None,false);
    circ.b.ops.extend(route.into_iter().rev());
}

fn borrow_truth(code:usize,shift:usize,a_class:Option<usize>)->bool{
    let mut t=code&7;let mut b=code>>3&7;let mut v=code>>6&7;
    if let Some(a)=a_class{
        if a==0{t=1;b=0;}
        else if a==1{t=(t&1)|2;
            if shift==0{if t&1==0{
                let low_b=b&3;let logical_b=low_b|(v&4);
                v=(v&3)|((1^(low_b>>1&1)^(code>>9&1))<<2);b=logical_b;
            }else{b&=3;}} // u<t=3; physical b2 is the parked HA passenger.
        }
        else if a==2{t=(t&3)|4;} // Logical coefficient head, not its passenger.
        let keep=256usize.saturating_sub(a+shift).min(3);
        v&=(1<<keep)-1; // Beyond this point the physical source can be cargo.
    }
    let q=match shift{0=>((code>>9&1)<<1)|((code>>10&1)<<2),1=>(code>>9&1)<<2,2=>0,_=>unreachable!()};
    let r=if t&1!=0{7usize.wrapping_sub(b*v).wrapping_mul(t).wrapping_sub(q*v)&7}else{b};
    r<((v<<shift)&7)
}
fn terms(shift:usize,class:Option<usize>)->Vec<usize>{
    let mut anf:Vec<_>=(0..2048).map(|c|borrow_truth(c,shift,class)^class.is_some().then(||borrow_truth(c,shift,None)).unwrap_or(false)).collect();
    for bit in 0..11{for m in 0..2048{if m>>bit&1!=0{anf[m]^=anf[m^(1<<bit)];}}}
    anf.into_iter().enumerate().filter_map(|(m,b)|b.then_some(m)).collect()
}
#[path="q792_r01_seed_plan_r01.rs"]mod seed_plan;
fn seed_logic(circ:&mut Circuit,word:&[&QReg],base:&[(&QReg,bool)],ha:&QReg,g:&QReg,shift:usize,ac:Option<usize>){
    static VERIFIED:std::sync::OnceLock<()>=std::sync::OnceLock::new();VERIFIED.get_or_init(||{
        for sh in 0..3{for cls in [None,Some(0),Some(1),Some(2),Some(252),Some(253)]{let(pol,terms)=seed_plan::plan(sh,cls);for x in 0..2048{let expected=borrow_truth(x,sh,cls)^if cls.is_some_and(|a|a>=2){borrow_truth(x,sh,None)}else{false};assert_eq!(terms.iter().fold(false,|v,&m|v^((x^pol)&m==m)),expected);}}}
    });
    let(pol,terms)=seed_plan::plan(shift,ac);for(i,q)in word.iter().enumerate(){if pol>>i&1!=0{circ.x(q);}}
    for &m in terms{let mut cs=base.to_vec();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));seed_ha_gate(circ,&cs,ha,g);}
    for(i,q)in word.iter().enumerate().rev(){if pol>>i&1!=0{circ.x(q);}}
}
fn numeric_seed_enabled(shift:usize)->bool{
    shift<3
}
fn numeric_route<'a>(circ:&mut Circuit,m:&[QReg],word:&'a[QReg],offset:usize)->&'a QReg{
    assert_eq!(m.len(),8);assert!(offset<=1);
    // Transfer of gnuchev Q793 numeric_route support pruning: M=A+C>=A.
    // The complete route is paired with its literal inverse off guard.
    let lo=circ.q797_a_support.map_or(0,|(lo,_)|lo.min(253));
    let mut nodes:Vec<_>=(0..256).map(|v|if(lo..=253).contains(&v){Some(&word[v+offset])}else{None}).collect();
    for bit in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{circ.cswap(&m[bit],left,right);Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}nodes[0].unwrap()
}
/// Numeric A/C are open and original on entry/return. Route W1[M+offset],
/// copy under the seed guard, repair the C-low endpoint aliases, then reverse
/// the entire route literally. The active domain has M<=253; pruned leaves
/// are therefore never consumed, while the unconditional route still cancels
/// for arbitrary off-guard metadata and work data.
fn numeric_prefix_xor(circ:&mut Circuit,aa:&[QReg],cc:&[QReg],word:&[QReg],base:&[(&QReg,bool)],out:&QReg,
                      offset:usize,needed_c:usize,dirty:&[QReg]){
    assert_eq!(aa.len(),8);assert_eq!(cc.len(),8);assert!(offset<=1&&(1..=2).contains(&needed_c));
    let at=circ.b.ops.len();arithmetic::add(circ,aa,cc,None,false);let root=numeric_route(circ,cc,word,offset);arithmetic::add(circ,aa,cc,None,true);
    let route=circ.b.ops[at..].to_vec();let mut cs=base.to_vec();cs.push((root,true));gate(circ,&cs,out,dirty);
    for absent in 0..needed_c{let mut ex=cs.clone();ex.extend(cc.iter().enumerate().map(|(i,q)|(q,absent>>i&1!=0)));gate(circ,&ex,out,dirty);}
    circ.b.ops.extend(route.into_iter().rev());
}
/// A temporary prefix cache may use the SM2 zero supplied by g&mask's
/// actual small-S admission. Arbitrary off-base scratch gives a pure target
/// XOR extension; the identical second prefix removes it after the HA-only
/// seed. Every control and lender returns on each call. This primitive is
/// never used for an unpaired work-data update.
fn prefix_loan_gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,sm2:&QReg){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v) in cs{assert_ne!(q.id(),out.id());assert_ne!(q.id(),sm2.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}
        else{unique.push((q,v));}
    }
    super::paired_clean_mcx::toggle(circ,&unique,out,sm2);
}
fn prefix_high_flag(circ:&mut Circuit,rank:&[QReg],g:&QReg,sm3:&QReg,delta:bool)->Vec<crate::circuit::Op>{
    let at=circ.b.ops.len();let high=[&rank[0],&rank[1],&rank[3],&rank[4]];
    let truth=(0..16).map(|r|{let f0=[0,9,10,15].contains(&r);let f1=[1,6,11].contains(&r);if delta{f0^f1}else{f0}}).collect();
    // On g=1, X(g) is the same genuine zero helper used by the main scan.
    // Off g the flag is a pure target-XOR extension removed literally.
    circ.x(g);super::q792_esop_r01::paired(circ,&high,truth,&[],sm3,g);circ.x(g);
    circ.b.ops[at..].to_vec()
}
/// C enters as M_low except that C0 is temporarily original quotient
/// parity. Original Ah/C_h are not materialized. Under g&mask, Sh=0 and
/// all SM loans start zero; rank[0:2] is M_high and rank[3:5] carries the
/// exact Ah0/Ah3 class predicates. The prefix restores original C_low only
/// while excluding C=0/1, then reverses its entire arithmetic/route frame.
fn major_prefix_xor(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],word:&[QReg],base:&[(&QReg,bool)],out:&QReg,
                    offset:usize,needed_c:usize,c0:bool,g:&QReg){
    assert!(offset<=1&&(1..=2).contains(&needed_c));
    let at=circ.b.ops.len();circ.cx(&a[0],&c[0]); // Original C0 -> M0.
    let mm:Vec<_>=c.iter().chain(rank[..2].iter()).map(QReg::borrowed_alias).collect();
    let root=numeric_route(circ,&mm,word,offset);
    arithmetic::add(circ,a,c,None,true); // Original C_low for paid endpoints.
    let route=circ.b.ops[at..].to_vec();let mut cs=base.to_vec();cs.push((root,true));
    prefix_loan_gate(circ,&cs,out,&sm[2]);
    for absent in 0..needed_c{
        if (absent&1!=0)!=c0{continue;} // The exact base already fixes C0.
        let high=prefix_high_flag(circ,rank,g,&sm[3],false);
        let mut ex=cs.clone();ex.push((&sm[3],true));ex.extend(c.iter().enumerate().map(|(i,q)|(q,absent>>i&1!=0)));
        prefix_loan_gate(circ,&ex,out,&sm[2]);
        circ.b.ops.extend(high.into_iter().rev());
        if absent==1{
            // C=1 has discarded carry exactly when A_low=63. The rank
            // predicate then changes from F0 to F1, paid as F0 XOR F1.
            let high=prefix_high_flag(circ,rank,g,&sm[3],true);
            let mut ex=cs.clone();ex.push((&sm[3],true));ex.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));ex.extend(a.iter().map(|q|(q,true)));
            prefix_loan_gate(circ,&ex,out,&sm[2]);
            circ.b.ops.extend(high.into_iter().rev());
        }
    }
    circ.b.ops.extend(route.into_iter().rev());
}
fn major_or_window_prefix(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],w1:&[QReg],base:&[(&QReg,bool)],out:&QReg,
                          offset:usize,needed:usize,c0:bool,g:&QReg,dirty:&[QReg],window:Option<&[QReg]>){
    if let Some(roots)=window{joint_window::prefix(circ,rank,a,c,sm,&roots[offset],&w1[2],base,out,offset,needed,c0,g,dirty);}
    else{major_prefix_xor(circ,rank,a,c,sm,w1,base,out,offset,needed,c0,g);}
}
fn seed(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,ha:&QReg,
        w1:&[QReg],w2:&[QReg],hs:&QReg,dirty:&[QReg],j:usize,shift:usize){
    seed_impl(circ,rank,a,c,sm,g,mask,ha,w1,w2,hs,dirty,j,shift,false,None);
}
fn seed_impl(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,ha:&QReg,
        w1:&[QReg],w2:&[QReg],hs:&QReg,dirty:&[QReg],j:usize,shift:usize,major:bool,window:Option<&[QReg]>){
    let c0=((j>>1)&1!=0) ^ (shift!=0); // S_old=shift+1, original quotient parity.
    let base=[(g,true),(mask,true),(&c[0],c0)];
    let numeric=numeric_seed_enabled(shift)&&!major;
    let chart_word:Vec<QReg>=rank.iter().chain(std::iter::once(hs)).map(QReg::borrowed_alias).collect();
    let aa:Vec<QReg>=a.iter().chain(if major{rank[3..5].iter()}else{chart_word[..2].iter()}).map(QReg::borrowed_alias).collect();
    let cc:Vec<QReg>=c.iter().chain(chart_word[2..4].iter()).map(QReg::borrowed_alias).collect();
    let converter=if numeric{
        let at=circ.b.ops.len();numeric_chart::emit(circ,&chart_word,dirty);Some(circ.b.ops[at..].to_vec())
    }else{None};
    // g&mask selects encoded S=1/2/3 (logical S_new<=2), hence Sh=0 and
    // every SM bit is zero. In the major path SM2 temporarily funds prefix
    // centers, SM3 funds high-C flags; both return before the A-class cache.
    // The route and source formulas do not interpret S until all loans return.
    // One full operand/endpoint cache frame survives the HA-only seed.
    // Prefix outputs are consumed only by the unchanged g&mask&C0 centers.
    let held_prefix=if major{window.and_then(|roots|prefix_hold::begin(circ,rank,a,c,sm,g,roots,&w1[2],shift,c0))}else{None};
    if held_prefix.is_none(){
    if shift==0{
        if major{
            major_or_window_prefix(circ,rank,a,c,sm,w1,&base,&sm[0],1,1,c0,g,dirty,window);
            major_or_window_prefix(circ,rank,a,c,sm,w1,&base,&sm[1],0,2,c0,g,dirty,window);
        }else if numeric{
            numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[0],1,1,dirty);
            numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[1],0,2,dirty);
        }else{
            prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,g,hs,dirty);
            prefix_xor(circ,rank,a,c,w1,&base,&sm[1],0,2,g,hs,dirty);
        }
    }else if shift==1{if major{major_or_window_prefix(circ,rank,a,c,sm,w1,&base,&sm[0],1,1,c0,g,dirty,window);}else if numeric{numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[0],1,1,dirty);}else{prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,g,hs,dirty);}}
    }
    // The original path materializes literal Ah through partial86. The major
    // path keeps the existing sum chart: on Sh=0, Ah0 iff rank[3:5]=00 and
    // Ah3 iff rank[3:5]=11. Those are exactly the only high-A classes below,
    // with the same two high controls and no additional chart lifetime.
    let word=[&w1[0],&w1[1],&w1[2],&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259],
              &w2[258-shift],&w2[257-shift],&w2[256-shift],&sm[0],&sm[1]];
    // The high-C prefix caches have returned SM3 before this one new loan.
    // It closes at A2, before every later class/prefix/next-seed/carry use.
    let mut shared=if major&&window.is_some()&&seed_shared::has_small(circ){Some(seed_shared::begin(circ,&aa,&sm[3],g))}else{None};
    if major&&window.is_some(){
        if shared.is_some(){seed_parity::emit_cached(circ,&word,&base,ha,&sm[2],g,shift,&sm[3]);}
        else{seed_parity::emit(circ,&aa,&word,&base,ha,&sm[2],g,shift);}
    }else{
    // Cache the disjoint A0/A1 selector on the existing SM2 zero.
    // Emit their direct functions instead of expanding F_class XOR F_generic.
    let small_at=circ.b.ops.len();
    let merge_small=circ.q797_a_support.map_or(true,|(lo,hi)|(lo..hi).contains(&0)&&(lo..hi).contains(&1));
    if merge_small{
        // [A=0] XOR [A=1] = [A>>1=0] in the selected numeric/small-S care.
        // The complete raw extension is paid by this cache's literal inverse.
        let mut cs=base.to_vec();cs.extend(aa.iter().skip(1).map(|q|(q,false)));gate(circ,&cs,&sm[2],dirty);
    }else{
        for ac in 0..2{if circ.q797_a_support.is_some_and(|(lo,hi)|!(lo..hi).contains(&ac)){continue;}let mut cs=base.to_vec();cs.extend(aa.iter().enumerate().map(|(i,q)|(q,ac>>i&1!=0)));gate(circ,&cs,&sm[2],dirty);}
    }
    let small=circ.b.ops[small_at..].to_vec();let mut default_base=base.to_vec();default_base.push((&sm[2],false));seed_logic(circ,&word,&default_base,ha,g,shift,None);circ.b.ops.extend(small.into_iter().rev());
    }
    for a_class in [0,1,2,252,253]{
        if a_class==2{if let Some(ops)=shared.take(){circ.b.ops.extend(ops.into_iter().rev());}}
        // Same analytic endpoint-gating principle as public Q793's codec.
        if circ.q797_a_support.is_some_and(|(lo,hi)|!(lo..hi).contains(&a_class)){continue;}
        if seed_plan::plan(shift,Some(a_class)).1.is_empty(){continue;}
        let at=circ.b.ops.len();
        if a_class<2&&shared.is_some(){
            seed_shared::small_cache(circ,&aa,&sm[3],&sm[2],a_class);
        }else if major&&window.is_some(){
            // Class cache is observed only by the unchanged masked HA center.
            // On every g1, X(g) is a genuine zero: omit mask/C0 from the
            // producer and pay the eight-bit AA test with that returned loan.
            // SM2 starts zero only on g&mask; false mask/C0 centers vanish.
            // Off g this is a pure cache-XOR with all ports restored; the
            // complete HA-only seed extension is paired around returned carry.
            let mut cs=vec![(g,true)];cs.extend(aa.iter().enumerate().map(|(i,q)|(q,a_class>>i&1!=0)));
            seed_ha_gate(circ,&cs,&sm[2],g);
        }else{
            let mut cs=base.to_vec();cs.extend(aa.iter().enumerate().map(|(i,q)|(q,a_class>>i&1!=0)));gate(circ,&cs,&sm[2],dirty);
        }
        let restore=circ.b.ops[at..].to_vec();
        let mut selected=base.to_vec();selected.push((&sm[2],true));
        if major&&window.is_some()&&a_class==1&&shift==0{seed_shared::a1_head(circ,&word,&selected,ha,g);}
        else if major&&window.is_some()&&a_class==2&&shift<2{seed_shared::a2_delta(circ,&word,&selected,ha,g,shift);}
        else{seed_logic(circ,&word,&selected,ha,g,shift,Some(a_class));}
        circ.b.ops.extend(restore.into_iter().rev());
    }
    if let Some(frame)=held_prefix{prefix_hold::close(circ,frame);}else{
    if shift==0{
        if major{
            major_or_window_prefix(circ,rank,a,c,sm,w1,&base,&sm[1],0,2,c0,g,dirty,window);
            major_or_window_prefix(circ,rank,a,c,sm,w1,&base,&sm[0],1,1,c0,g,dirty,window);
        }else if numeric{
            numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[1],0,2,dirty);
            numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[0],1,1,dirty);
        }else{
            prefix_xor(circ,rank,a,c,w1,&base,&sm[1],0,2,g,hs,dirty);
            prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,g,hs,dirty);
        }
    }else if shift==1{if major{major_or_window_prefix(circ,rank,a,c,sm,w1,&base,&sm[0],1,1,c0,g,dirty,window);}else if numeric{numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[0],1,1,dirty);}else{prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,g,hs,dirty);}}
    }
    if let Some(ops)=converter{circ.b.ops.extend(ops.into_iter().rev());}
}

struct Scan<'a>{rank:&'a[QReg],a:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,mask:&'a QReg,hs:&'a QReg,ha:&'a QReg,dirty:&'a[QReg],j:usize,support_end:usize,normalized_sm3:bool,read_quotient:bool,major_consumers:bool,joint_window:bool}
impl Scan<'_>{
    fn lower(&self,circ:&mut Circuit,i:usize){
        if i>255||(i+1)%2!=self.j%2{return;}
        // This variant is called only with g implying original S=1. SM3
        // parks the HA passenger; interpret its logical value as zero.
        if self.normalized_sm3&&((i+1)%256)&32!=0{return;}let value=(i+1)%256;let old_c0=((value>>1)^(self.j>>1))&1!=0;
        circ.cx(&self.a[0],&self.c[0]);circ.x(self.g);let start=circ.b.ops.len();
        let clean=mux::active("Q795_R01_LOWER_CONDITIONAL_SCRATCH");if clean&&old_c0{circ.x(&self.c[0]);}
        for &(m,v)in programs::EQUAL[4+value/64]{let cs:Vec<_>=(0..5).filter(|&b|m>>b&1!=0).map(|b|(&self.rank[b],v>>b&1!=0)).collect();
            if clean{super::paired_clean_mcx::toggle(circ,&cs,self.g,&self.c[0]);}else{gate(circ,&cs,self.g,self.dirty);}}
        if clean&&old_c0{circ.x(&self.c[0]);}let high=circ.b.ops[start..].to_vec();
        let mut cs=vec![(self.g,true),(&self.c[0],old_c0)];cs.extend((0..if self.normalized_sm3{3}else{4}).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));gate(circ,&cs,self.mask,self.dirty);
        circ.b.ops.extend(high.into_iter().rev());circ.x(self.g);circ.cx(&self.a[0],&self.c[0]);
    }
    fn carry(&self,circ:&mut Circuit,s:&QReg,t:&QReg,inverse:bool){
        if !inverse{circ.cx(s,t);circ.cx(self.ha,s);}circ.x(self.g);
        super::paired_clean_mcx::toggle(circ,&[(self.mask,true),(t,true),(s,true)],self.ha,self.g);circ.x(self.g);
        if inverse{circ.cx(self.ha,s);circ.cx(s,t);}
    }
    fn seed_all(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg]){
        arithmetic::add(circ,self.a,self.c,None,true);
        for shift in 0..3{if (shift+1)%2==self.j%2{seed(circ,self.rank,self.a,self.c,self.sm,self.g,self.mask,self.ha,w1,w2,self.hs,self.dirty,self.j,shift);}}
        arithmetic::add(circ,self.a,self.c,None,false);
    }
    fn seed_all_major(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg]){
        circ.cx(&self.a[0],&self.c[0]); // Only the original C0 seed guard is needed.
        for shift in 0..3{if (shift+1)%2==self.j%2{seed_impl(circ,self.rank,self.a,self.c,self.sm,self.g,self.mask,self.ha,w1,w2,self.hs,self.dirty,self.j,shift,true,None);}}
        circ.cx(&self.a[0],&self.c[0]);
    }
    fn seed_all_window(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],roots:&[QReg]){
        circ.cx(&self.a[0],&self.c[0]);
        for shift in 0..3{if (shift+1)%2==self.j%2{seed_impl(circ,self.rank,self.a,self.c,self.sm,self.g,self.mask,self.ha,w1,w2,self.hs,self.dirty,self.j,shift,true,Some(roots));}}
        circ.cx(&self.a[0],&self.c[0]);
    }
    fn low_update_cached(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg,major:bool,window:Option<&[QReg]>){
        assert!(major&&window.is_some());
        if major{circ.cx(&self.a[0],&self.c[0]);}else{arithmetic::add(circ,self.a,self.c,None,true);}
        let chart_word:Vec<QReg>=self.rank.iter().chain(std::iter::once(&self.sm[3])).map(QReg::borrowed_alias).collect();let at=circ.b.ops.len();if !major{numeric_chart::emit(circ,&chart_word,self.dirty);}let chart=circ.b.ops[at..].to_vec();
        let aa:Vec<QReg>=self.a.iter().chain(if major{self.rank[3..5].iter()}else{chart_word[..2].iter()}).map(QReg::borrowed_alias).collect();let cc:Vec<QReg>=self.c.iter().chain(chart_word[2..4].iter()).map(QReg::borrowed_alias).collect();
        let support=circ.q797_a_support.unwrap_or((0,256));
        let aflags=|value:usize|if(support.0..support.1).contains(&value){vec![aa.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect::<Vec<_>>()]}else{Vec::new()};
        // After the full second seed, g&mask implies encoded S1/2/3 and
        // original SM0/1/2=0. Prefix/default/class loans have all returned.
        // Outside both guards these ports may be arbitrary: every DATA or
        // HA-cache center retains exact g&mask and both producers return.
        let allow0=(support.0..support.1).contains(&0);
        let allow1=(support.0..support.1).contains(&1);
        let class0=allow0.then_some(&self.sm[0]);
        let class1=(self.j%2!=0&&(allow0||allow1)).then_some(&self.sm[1]);
        let class_at=circ.b.ops.len();
        if let Some(q)=class0{circ.x(q);for flag in aflags(0){gate(circ,&flag,q,self.dirty);}}
        if let Some(q)=class1{
            circ.x(q);
            if allow0&&allow1{
                let cs:Vec<_>=aa.iter().skip(1).map(|q|(q,false)).collect();gate(circ,&cs,q,self.dirty);
            }else{for ac in 0..2{for flag in aflags(ac){gate(circ,&flag,q,self.dirty);}}}
        }
        let class_ops=circ.b.ops[class_at..].to_vec();
        for shift in 0..3{if (shift+1)%2!=self.j%2{continue;}
            let c0=((self.j>>1)&1!=0)^(shift!=0);
            // decision, coefficient t0 and original C0 remain unchanged
            // through this entire branch, including the paid A1 root frame.
            let branch_at=circ.b.ops.len();
            gate(circ,&[(decision,true),(&w1[0],false),(&self.c[0],c0)],&self.sm[2],self.dirty);
            let branch_ops=circ.b.ops[branch_at..].to_vec();
            let branch_base=[(self.g,true),(self.mask,true),(&self.sm[2],true)];
            let b=[&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259]];
            let v=[&w2[258-shift],&w2[257-shift],&w2[256-shift]];
            let allow_a1=circ.q797_a_support.map_or(true,|(lo,hi)|lo<=1&&1<hi);
            if shift==0&&allow_a1{
                // HS is again zero on g after the literal cache reversal.
                // Cache the A1/S1/t2 decision guard, preserving arbitrary HS
                // off g. The C-only q0 route does not consume this zero loan.
                let start=circ.b.ops.len();
                for flag in aflags(1){let mut cs=branch_base.to_vec();cs.extend(flag);gate(circ,&cs,self.hs,self.dirty);}
                let flag_ops=circ.b.ops[start..].to_vec();let base=[(self.g,true),(self.mask,true),(self.hs,true)];
                // r1 is preserved, r2 ^= decision*(r0 XOR r1 XOR qstored0).
                for q in [b[0],b[1]]{let mut cs=base.to_vec();cs.push((q,true));gate(circ,&cs,v[2],self.dirty);}
                let route_at=circ.b.ops.len();let mm:Vec<_>=self.c.iter().chain(self.rank[..2].iter()).map(QReg::borrowed_alias).collect();
                let root=if let Some(roots)=window{&roots[1]}else if major{
                    // On the active A1 branch, C+2=M+1. Preserve original
                    // C0 in the base while reversing the whole M route.
                    circ.cx(&self.a[0],&self.c[0]);let root=numeric_route(circ,&mm,w1,1);circ.cx(&self.a[0],&self.c[0]);root
                }else{
                    let mut nodes:Vec<_>=(0..256).map(|cv|if cv<=252{Some(&w1[cv+2])}else{None}).collect();for q in &cc{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{circ.cswap(q,l,r);Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),_=>None});}nodes=next;}nodes[0].unwrap()
                };
                let route=circ.b.ops[route_at..].to_vec();let mut cs=base.to_vec();cs.push((root,true));gate(circ,&cs,v[2],self.dirty);
                // Under A1, current C0 is original parity and all remaining
                // literal M bits zero mean M=1, equivalently original C=0.
                cs.extend(if major{mm.iter()}else{cc.iter()}.map(|q|(q,false)));gate(circ,&cs,v[2],self.dirty);circ.b.ops.extend(route.into_iter().rev());
                circ.b.ops.extend(flag_ops.into_iter().rev());
            }
            let mut change=|target:usize,extra:&[(&QReg,bool)]|{
                let mut cs=branch_base.to_vec();
                // One exact held class replaces the original default XOR
                // A0 correction (and the A1 physical-b2 suppression).
                let class=if shift==0&&target==2{class1}else{class0};
                if let Some(q)=class{cs.push((q,true));}
                cs.extend_from_slice(extra);gate(circ,&cs,b[target],self.dirty);
                // Suppress physical v bits that are actually gap/cargo above
                // the proven source width. The semantic high source is zero.
                for ac in [252,253]{let keep=256usize.saturating_sub(ac+shift).min(3);
                    if extra.iter().any(|&(q,_)|(keep..3).any(|i|q.id()==v[i].id())){
                        for flag in aflags(ac){let mut ex=cs.clone();ex.extend(flag);gate(circ,&ex,b[target],self.dirty);}
                    }
                }
            };
            if shift==0{
                change(2,&[(v[2],true)]);change(2,&[(v[1],true),(b[1],false)]);
                change(2,&[(v[0],true),(b[0],false),(b[1],false)]);change(2,&[(v[0],true),(b[0],false),(v[1],true)]);
                change(1,&[(v[1],true)]);change(1,&[(v[0],true),(b[0],false)]);change(0,&[(v[0],true)]);
            }else if shift==1{change(2,&[(v[1],true)]);change(2,&[(v[0],true),(b[1],false)]);change(1,&[(v[0],true)]);}
            else{change(2,&[(v[0],true)]);}
            drop(change);
            circ.b.ops.extend(branch_ops.into_iter().rev());
        }
        // Both conditional class ports return before sumchart/outer input
        // restoration and before the second quotient restores decision.
        circ.b.ops.extend(class_ops.into_iter().rev());
        circ.b.ops.extend(chart.into_iter().rev());
        if major{circ.cx(&self.a[0],&self.c[0]);}else{arithmetic::add(circ,self.a,self.c,None,false);}
    }
    fn low_update(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg,major:bool,window:Option<&[QReg]>){
        if major&&window.is_some(){return self.low_update_cached(circ,w1,w2,decision,major,window);}
        if major{circ.cx(&self.a[0],&self.c[0]);}else{arithmetic::add(circ,self.a,self.c,None,true);}
        let chart_word:Vec<QReg>=self.rank.iter().chain(std::iter::once(&self.sm[3])).map(QReg::borrowed_alias).collect();let at=circ.b.ops.len();if !major{numeric_chart::emit(circ,&chart_word,self.dirty);}let chart=circ.b.ops[at..].to_vec();
        let aa:Vec<QReg>=self.a.iter().chain(if major{self.rank[3..5].iter()}else{chart_word[..2].iter()}).map(QReg::borrowed_alias).collect();let cc:Vec<QReg>=self.c.iter().chain(chart_word[2..4].iter()).map(QReg::borrowed_alias).collect();
        let support=circ.q797_a_support.unwrap_or((0,256));
        let aflags=|value:usize|if(support.0..support.1).contains(&value){vec![aa.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect::<Vec<_>>()]}else{Vec::new()};
        for shift in 0..3{if (shift+1)%2!=self.j%2{continue;}
            let c0=((self.j>>1)&1!=0)^(shift!=0);
            let b=[&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259]];
            let v=[&w2[258-shift],&w2[257-shift],&w2[256-shift]];
            let allow_a1=circ.q797_a_support.map_or(true,|(lo,hi)|lo<=1&&1<hi);
            if shift==0&&allow_a1{
                // HS is again zero on g after the literal cache reversal.
                // Cache the A1/S1/t2 decision guard, preserving arbitrary HS
                // off g. The C-only q0 route does not consume this zero loan.
                let start=circ.b.ops.len();
                for flag in aflags(1){let mut cs=vec![(self.g,true),(self.mask,true),(decision,true),(&w1[0],false),(&self.c[0],c0)];cs.extend(flag);gate(circ,&cs,self.hs,self.dirty);}
                let flag_ops=circ.b.ops[start..].to_vec();let base=[(self.g,true),(self.mask,true),(self.hs,true)];
                // r1 is preserved, r2 ^= decision*(r0 XOR r1 XOR qstored0).
                for q in [b[0],b[1]]{let mut cs=base.to_vec();cs.push((q,true));gate(circ,&cs,v[2],self.dirty);}
                let route_at=circ.b.ops.len();let mm:Vec<_>=self.c.iter().chain(self.rank[..2].iter()).map(QReg::borrowed_alias).collect();
                let root=if let Some(roots)=window{&roots[1]}else if major{
                    // On the active A1 branch, C+2=M+1. Preserve original
                    // C0 in the base while reversing the whole M route.
                    circ.cx(&self.a[0],&self.c[0]);let root=numeric_route(circ,&mm,w1,1);circ.cx(&self.a[0],&self.c[0]);root
                }else{
                    let mut nodes:Vec<_>=(0..256).map(|cv|if cv<=252{Some(&w1[cv+2])}else{None}).collect();for q in &cc{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{circ.cswap(q,l,r);Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),_=>None});}nodes=next;}nodes[0].unwrap()
                };
                let route=circ.b.ops[route_at..].to_vec();let mut cs=base.to_vec();cs.push((root,true));gate(circ,&cs,v[2],self.dirty);
                // Under A1, current C0 is original parity and all remaining
                // literal M bits zero mean M=1, equivalently original C=0.
                cs.extend(if major{mm.iter()}else{cc.iter()}.map(|q|(q,false)));gate(circ,&cs,v[2],self.dirty);circ.b.ops.extend(route.into_iter().rev());
                circ.b.ops.extend(flag_ops.into_iter().rev());
            }
            let mut change=|target:usize,extra:&[(&QReg,bool)]|{
                let base=[(self.g,true),(self.mask,true),(decision,true),(&w1[0],false),(&self.c[0],c0)];
                let mut cs=base.to_vec();cs.extend_from_slice(extra);gate(circ,&cs,b[target],self.dirty);
                // A0 has logical t=1 even when the physical head passenger
                // is zero. Its u chart is immutable under R01.
                for flag in aflags(0){let mut ex=cs.clone();ex.extend(flag);gate(circ,&ex,b[target],self.dirty);}
                // The unified A1/S1/t2 branch stores logical r2 in physical
                // v2 and parks HA's passenger in physical b2. Cancel every
                // general b2 write there; its exact replacement is below.
                if shift==0&&target==2&&allow_a1{for flag in aflags(1){let mut ex=cs.clone();ex.extend(flag);gate(circ,&ex,b[target],self.dirty);}}
                // Suppress physical v bits that are actually gap/cargo above
                // the proven source width. The semantic high source is zero.
                for ac in [252,253]{let keep=256usize.saturating_sub(ac+shift).min(3);
                    if extra.iter().any(|&(q,_)|(keep..3).any(|i|q.id()==v[i].id())){
                        for flag in aflags(ac){let mut ex=cs.clone();ex.extend(flag);gate(circ,&ex,b[target],self.dirty);}
                    }
                }
            };
            if shift==0{
                change(2,&[(v[2],true)]);change(2,&[(v[1],true),(b[1],false)]);
                change(2,&[(v[0],true),(b[0],false),(b[1],false)]);change(2,&[(v[0],true),(b[0],false),(v[1],true)]);
                change(1,&[(v[1],true)]);change(1,&[(v[0],true),(b[0],false)]);change(0,&[(v[0],true)]);
            }else if shift==1{change(2,&[(v[1],true)]);change(2,&[(v[0],true),(b[1],false)]);change(1,&[(v[0],true)]);}
            else{change(2,&[(v[0],true)]);}
        }
        circ.b.ops.extend(chart.into_iter().rev());
        if major{circ.cx(&self.a[0],&self.c[0]);}else{arithmetic::add(circ,self.a,self.c,None,false);}
    }
    // C already holds (A_low+C_low) mod64. Under C=value_low, its
    // discarded carry is exactly A_low>value_low. F is computed into the
    // active g=1 rail as g XOR !F, consumed, and uncomputed immediately.
    // Its arbitrary off-g mask extension is inside a literal U/U^-1 frame.
    fn upper(&self,circ:&mut Circuit,value:usize){
        let ts=triples();let h=value/64;let low=value&63;let rank:Vec<_>=self.rank.iter().collect();let d=&self.dirty[0];let rest=&self.dirty[1..];
        let base:Vec<_>=ts.iter().map(|t|t[0]+t[1]==h).collect();let delta:Vec<_>=ts.iter().map(|t|(t[0]+t[1]==h)^(t[0]+t[1]+1==h)).collect();
        // On incoming g1 the temporary guard is exactly Csum_low==value.
        // Only upper's mask XOR observes this guard; it restores before any
        // arithmetic. Off g this is a reversible mask extension inside U/U^-1.
        let equals:Vec<_>=self.c.iter().enumerate().map(|(i,q)|(q,low>>i&1!=0)).collect();circ.x(self.g);gate(circ,&equals,self.g,self.dirty);
        super::q792_fold20_r01::table(circ,&rank,base,&[(self.g,true)],self.mask,self.dirty);
        for _ in 0..2{super::q792_fold20_r01::table(circ,&rank,delta.clone(),&[],d,rest);for cube in super::length_recompute::above_cubes(6,low){let mut cs=vec![(self.g,true),(d,true)];cs.extend(cube.iter().map(|&(i,b)|(&self.a[i],b)));gate(circ,&cs,self.mask,rest);}}
        gate(circ,&equals,self.g,self.dirty);circ.x(self.g);
    }
    fn lower_major(&self,circ:&mut Circuit,i:usize){
        if i>255||(i+1)%2!=self.j%2{return;}assert!(!self.normalized_sm3);let value=(i+1)%256;let h=value/64;let low=value>>2&15;let old_c0=((value>>1)^(self.j>>1))&1!=0;
        circ.cx(&self.a[0],&self.c[0]);let rank:Vec<_>=self.rank.iter().collect();
        // Restore g before every carry cell. Its active value 1 temporarily
        // funds the single high-S predicate, avoiding its repetition on each
        // low-field cube. Off g this is a pure mask XOR inside literal U/U^-1.
        circ.x(self.g);let at=circ.b.ops.len();
        // The mask center requires original C0=old_c0. Normalize this
        // public literal to a genuine zero only on that consumer branch,
        // and use it for the high-S target-XOR oracle. Restore C0 before
        // the center. On the other branch the center is disabled and the
        // arbitrary-helper extension disappears under the literal inverse.
        // This producer's target-XOR frame is exact on the C0 branch;
        // its arbitrary extension elsewhere is retained and removed literally.
        if old_c0{circ.x(&self.c[0]);}
        super::q792_esop_r01::paired(circ,&rank,(0..32).map(|r|super::q792_r01_sumchart_r01::sh(r)==h).collect(),&[],self.g,&self.c[0]);
        if old_c0{circ.x(&self.c[0]);}
        let high=circ.b.ops[at..].to_vec();
        // Under original g1, a matching C0 makes g exactly Sh==h.
        // That predicate implies rank2=0/1 for h0/1, or rank3=1 for h2/3
        // on EVERY physical rank code. Retain BOTH guards: on C0 mismatch
        // the paired producer can have an arbitrary dirty-helper extension.
        // Original g0 may change the local pure mask extension, which is
        // canceled by the complete recorded carry U/disabled-center/U^-1.
        let(bit,known)=if h<2{(2,h!=0)}else{(3,true)};
        two_guard_rank_mask(circ,self.g,&self.c[0],old_c0,self.sm,low,self.mask,&self.rank[bit],known,self.dirty);
        circ.b.ops.extend(high.into_iter().rev());circ.x(self.g);
        // The only displaced SM0 occurs at M=S=128. All other SM bits
        // are zero on that complete numeric boundary, so only 128/132
        // need the parity correction for physical versus logical SM0.
        if h==2&&low<=1{let base=[(&self.c[0],old_c0),(&self.sm[0],true)];super::q792_fold20_r01::table(circ,&rank,(0..32).map(|r|r==26||r==30).collect(),&base,self.mask,self.dirty);}
        circ.cx(&self.a[0],&self.c[0]);
    }
    fn upper_major(&self,circ:&mut Circuit,value:usize){
        let mut cs:Vec<_>=self.c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect();
        cs.extend(self.rank[..2].iter().enumerate().map(|(i,q)|(q,value>>(i+6)&1!=0)));
        // Public Q793 numeric_fused uses this guard-clean decomposition on
        // literal M. Our sum-major chart exposes the same eight M controls.
        // Active g=1 funds X(g)=0; inactive target-XOR extensions cancel in
        // the recorded U/guarded-center/U^-1 frame. g is restored per call.
        circ.x(self.g);super::paired_clean_mcx::toggle(circ,&cs,self.mask,self.g);circ.x(self.g);
    }
    fn fused(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
        if self.major_consumers{return self.fused_major(circ,w1,w2,decision);}
        let n=self.support_end.min(257);assert!(n>=3);
        let start=circ.b.ops.len();for i in 0..3{self.lower(circ,i);}let low=circ.b.ops[start..].to_vec();
        self.seed_all(circ,w1,w2);
        let at=circ.b.ops.len();super::q792_r01_sumchart_r01::emit(circ,self.rank,self.a,self.c,self.sm,self.g,self.dirty);let chart=circ.b.ops[at..].to_vec();
        // The first seed consumes W1[M], W1[M+1] and coefficient rails
        // W1[0..2], while the quotient SWAP consumes W1[M+2]. The sole
        // overlap M=0 implies A=C=0: its literal A0 seed ignores physical
        // t2 and both C-prefix copies are disabled. Thus the seed commutes
        // with the SWAP, including arbitrary incoming decision. Reuse this
        // already-paid sum chart rather than recomputing rank+carry M.
        if self.read_quotient{super::q793_r01_routes_v1::quotient_major(circ,self.rank,self.c,w1,self.g,decision);}
        let mut updates=Vec::new();
        for i in 3..n{
            let at=circ.b.ops.len();self.lower_major(circ,i);let value=256-i;
            self.upper_major(circ,value);
            updates.push(circ.b.ops[at..].to_vec());self.carry(circ,&w2[258-i],&w1[258-i],false);
        }
        circ.cx(self.g,decision);circ.ccx(self.g,self.ha,decision);
        for i in (3..n).rev(){
            self.carry(circ,&w2[258-i],&w1[258-i],true);circ.cx(self.ha,&w2[258-i]);
            gate(circ,&[(self.g,true),(self.mask,true),(&w2[258-i],true),(decision,true)],&w1[258-i],self.dirty);circ.cx(self.ha,&w2[258-i]);
            circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
        }
        circ.b.ops.extend(chart.into_iter().rev());
        self.seed_all(circ,w1,w2);self.low_update(circ,w1,w2,decision,false,None);
        circ.b.ops.extend(low.into_iter().rev());
    }
    /// A single paid sum-chart lifetime now owns both seed consumers,
    /// both quotient SWAPs and low_update. Initial S-mask construction and
    /// its inverse remain in the original rank chart. Every SM prefix/class
    /// loan returns before another consumer or the chart inverse runs.
    fn fused_major(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
        if self.joint_window{return self.fused_window(circ,w1,w2,decision);}
        assert!(self.read_quotient&&!self.normalized_sm3);
        let n=self.support_end.min(257);assert!(n>=3);
        let start=circ.b.ops.len();for i in 0..3{self.lower(circ,i);}let low=circ.b.ops[start..].to_vec();
        let at=circ.b.ops.len();super::q792_r01_sumchart_r01::emit(circ,self.rank,self.a,self.c,self.sm,self.g,self.dirty);let chart=circ.b.ops[at..].to_vec();
        self.seed_all_major(circ,w1,w2);
        super::q793_r01_routes_v1::quotient_major(circ,self.rank,self.c,w1,self.g,decision);
        let mut updates=Vec::new();
        for i in 3..n{
            let at=circ.b.ops.len();self.lower_major(circ,i);self.upper_major(circ,256-i);
            updates.push(circ.b.ops[at..].to_vec());self.carry(circ,&w2[258-i],&w1[258-i],false);
        }
        circ.cx(self.g,decision);circ.ccx(self.g,self.ha,decision);
        for i in (3..n).rev(){
            self.carry(circ,&w2[258-i],&w1[258-i],true);circ.cx(self.ha,&w2[258-i]);
            gate(circ,&[(self.g,true),(self.mask,true),(&w2[258-i],true),(decision,true)],&w1[258-i],self.dirty);circ.cx(self.ha,&w2[258-i]);
            circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
        }
        self.seed_all_major(circ,w1,w2);self.low_update(circ,w1,w2,decision,true,None);
        // low_update has finished consuming the updated quotient. Only now
        // insert it back and recover decision's arbitrary original data.
        super::q793_r01_routes_v1::quotient_major(circ,self.rank,self.c,w1,self.g,decision);
        circ.b.ops.extend(chart.into_iter().rev());
        circ.b.ops.extend(low.into_iter().rev());
    }
    /// Only the backward, fully returned carry frame observes this loan.
    /// Active mask_i is S-1 <= i < 256-M. For i<63, Sh=0 and rank2=0;
    /// for i>=128, M<128 and literal rank1=0. Both original g and mask
    /// remain in the sole exact dirty center, so arbitrary inactive rank
    /// inputs cannot toggle work. Producer/center/inverse returns per cell.
    fn window_data_update(&self,circ:&mut Circuit,i:usize,source:&QReg,target:&QReg,decision:&QReg){
        let scratch=if i<63{Some(&self.rank[2])}else if i>=128{Some(&self.rank[1])}else{None};
        if let Some(q)=scratch{
            circ.ccx(source,decision,q);
            gate(circ,&[(self.g,true),(self.mask,true),(q,true)],target,self.dirty);
            circ.ccx(source,decision,q);
        }else{
            gate(circ,&[(self.g,true),(self.mask,true),(source,true),(decision,true)],target,self.dirty);
        }
    }
    fn fused_window(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
        assert!(self.read_quotient&&!self.normalized_sm3);
        let n=self.support_end.min(257);assert!(n>=3);
        let start=circ.b.ops.len();for i in 0..3{self.lower(circ,i);}let low=circ.b.ops[start..].to_vec();
        let at=circ.b.ops.len();super::q792_r01_sumchart_r01::emit(circ,self.rank,self.a,self.c,self.sm,self.g,self.dirty);let chart=circ.b.ops[at..].to_vec();
        let m:Vec<_>=self.c.iter().chain(self.rank[..2].iter()).map(QReg::borrowed_alias).collect();
        let (roots,window)=joint_window::route(circ,&m,w1,self.dirty);
        self.seed_all_window(circ,w1,w2,&roots);
        joint_window::quotient(circ,self.rank,self.c,&roots,w1,self.g,decision,self.dirty);
        circ.b.ops.extend(window.into_iter().rev());
        let mut updates=Vec::new();
        for i in 3..n{
            let at=circ.b.ops.len();self.lower_major(circ,i);self.upper_major(circ,256-i);
            updates.push(circ.b.ops[at..].to_vec());self.carry(circ,&w2[258-i],&w1[258-i],false);
        }
        circ.cx(self.g,decision);circ.ccx(self.g,self.ha,decision);
        for i in (3..n).rev(){
            self.carry(circ,&w2[258-i],&w1[258-i],true);circ.cx(self.ha,&w2[258-i]);
            self.window_data_update(circ,i,&w2[258-i],&w1[258-i],decision);circ.cx(self.ha,&w2[258-i]);
            circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
        }
        let (roots,window)=joint_window::route(circ,&m,w1,self.dirty);
        self.seed_all_window(circ,w1,w2,&roots);self.low_update(circ,w1,w2,decision,true,Some(&roots));
        // low_update has finished consuming the updated quotient. Only now
        // insert it back and recover decision's arbitrary original data.
        joint_window::quotient(circ,self.rank,self.c,&roots,w1,self.g,decision,self.dirty);
        circ.b.ops.extend(window.into_iter().rev());
        circ.b.ops.extend(chart.into_iter().rev());
        circ.b.ops.extend(low.into_iter().rev());
    }
}

/// Exact normal core, AFTER physical pre-rotation and quotient-decision loan.
/// Caller must supply g=1 exactly on its intended R01 domain A+C<=253;
/// genuine HA=mask=hs=0 under g; decision=old high residual bit there. All
/// scratch may be dirty off g. Metadata C is ORIGINAL on entry and return.
/// The caller owns zero leases, cargo moves, guard construction and quotient
/// insertion. In particular this function NEVER borrows W1[A+1]/W2[A+1].
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,hs:&QReg,ha:&QReg,
                   decision:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,support_end:usize,normalized_sm3:bool){
    emit_with_quotient(circ,rank,a,c,sm,g,mask,hs,ha,decision,w1,w2,dirty,j,support_end,normalized_sm3,false);
}
/// The folded phaselease caller can defer its first quotient SWAP until
/// the existing sum chart is open. Other adapters retain their original ABI.
pub(super) fn emit_with_quotient(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,hs:&QReg,ha:&QReg,
                   decision:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,support_end:usize,normalized_sm3:bool,read_quotient:bool){
    emit_internal(circ,rank,a,c,sm,g,mask,hs,ha,decision,w1,w2,dirty,j,support_end,normalized_sm3,read_quotient,false,false);
}
pub(super) fn emit_with_sum_consumers(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,hs:&QReg,ha:&QReg,
                   decision:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,support_end:usize){
    emit_internal(circ,rank,a,c,sm,g,mask,hs,ha,decision,w1,w2,dirty,j,support_end,false,true,true,true);
}
fn emit_internal(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,hs:&QReg,ha:&QReg,
                   decision:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,support_end:usize,normalized_sm3:bool,read_quotient:bool,major_consumers:bool,joint_window:bool){
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);
    assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);assert!(dirty.len()>=18);assert!(j<4);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(&w1[..256]).chain(w2).chain(dirty)
        .chain([g,mask,ha,decision]).map(QReg::id).collect();
    ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]),"Q793 normal core alias");
    let start=circ.b.ops.len();let owned=(circ.b.next_qubit,circ.b.active_qubits);
    arithmetic::add(circ,a,c,None,false);
    Scan{rank,a,c,sm,g,mask,hs:&sm[3],ha,dirty,j,support_end,normalized_sm3,read_quotient,major_consumers,joint_window}.fused(circ,w1,w2,decision);
    arithmetic::add(circ,a,c,None,true);
    assert_eq!((circ.b.next_qubit,circ.b.active_qubits),owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Q793 R01 normal touched omitted Work1[{h}]");
    }}
}
pub(crate) fn run_numeric_seed_check(){numeric_seed_check::run();}


pub(crate) fn run_supported_route(){
 use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x19)}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 let mut lanes=0usize;
 for (block,&support)in super::metadata_entry_head5::A_SUPPORTS.iter().enumerate(){for offset in 0..2{
  let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;c.q797_a_support=Some(support);
  let m=c.alloc_qreg_bits("M",8);let w=c.alloc_qreg_bits("bank",259);let owned=c.b.next_qubit;
  let root=numeric_route(&mut c,&m,&w,offset).id()as usize;let ops=c.into_builder().ops;
  for first in(0..256).step_by(64){let mut seed=0x79270151u64^((block as u64)<<32)^first as u64^offset as u64;
   let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();for bit in 0..8{before[m[bit].id()as usize]=(0..64).fold(0,|v,l|v|((((first+l)>>bit&1)as u64)<<l));}
   let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());
   for l in 0..64{let v=first+l;if(support.0.min(253)..=253).contains(&v){assert_eq!(sim.qubits[root]>>l&1,before[w[v+offset].id()as usize]>>l&1,"numeric M route block={block} M={v}");}}
   for q in &m{assert_eq!(sim.qubits[q.id()as usize],before[q.id()as usize]);}assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
  }
 }}
 eprintln!("FOLD20_R01_SUPPORTED_ROUTE_PASS lanes={lanes} blocks=202 offsets=2 all_numeric_M=true inverse=true phase=0");
}
