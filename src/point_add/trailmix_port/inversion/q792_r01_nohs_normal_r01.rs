//! Timefix R01: one normal scan including normalized A1/S1 donor geometry.
//! No global padding loan, cargo relocation, endpoint routing, or allocator hook.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_arithmetic5 as arithmetic,metadata_muxlease as mux,length_recompute::mixed_mcx};
#[path="metadata_remainder5_programs.rs"] mod programs;
#[path="metadata_phase115_programs.rs"] mod c_programs;
#[path="q793_r01_numeric_partial.rs"] mod numeric_chart;
#[path="q793_r01_numeric_seed_check.rs"] mod numeric_seed_check;

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
    let mut nodes:Vec<_>=(0..256).map(|v|if v<=253{Some(&word[v+offset])}else{None}).collect();
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
fn seed(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,ha:&QReg,
        w1:&[QReg],w2:&[QReg],hs:&QReg,dirty:&[QReg],j:usize,shift:usize){
    let c0=((j>>1)&1!=0) ^ (shift!=0); // S_old=shift+1, original quotient parity.
    let base=[(g,true),(mask,true),(&c[0],c0)];
    let numeric=numeric_seed_enabled(shift);
    let chart_word:Vec<QReg>=rank.iter().chain(std::iter::once(hs)).map(QReg::borrowed_alias).collect();
    let aa:Vec<QReg>=a.iter().chain(chart_word[..2].iter()).map(QReg::borrowed_alias).collect();
    let cc:Vec<QReg>=c.iter().chain(chart_word[2..4].iter()).map(QReg::borrowed_alias).collect();
    let converter=if numeric{
        let at=circ.b.ops.len();numeric_chart::emit(circ,&chart_word,dirty);Some(circ.b.ops[at..].to_vec())
    }else{None};
    // g&mask implies true S_new<=2, hence SM0/1/2 are zero. The route
    // and source formulas below do not interpret S until all three restore.
    if shift==0{
        if numeric{
            numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[0],1,1,dirty);
            numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[1],0,2,dirty);
        }else{
            prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,g,hs,dirty);
            prefix_xor(circ,rank,a,c,w1,&base,&sm[1],0,2,g,hs,dirty);
        }
    }else if shift==1{if numeric{numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[0],1,1,dirty);}else{prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,g,hs,dirty);}}
    // The partial86 permutation converts rank5 plus the guard-clean HS rail
    // into literal high A/C/S bits. Keep it open across every shift-0 A-class
    // correction, reducing each rank-minterm family to one eight-bit cube.
    // Its three borrowed work rails may start dirty and are restored by the
    // recorded literal inverse after all dirty-ladder consumers finish.
    let word=[&w1[0],&w1[1],&w1[2],&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259],
              &w2[258-shift],&w2[257-shift],&w2[256-shift],&sm[0],&sm[1]];
    // Cache the disjoint A0/A1 selector on the existing SM2 zero.
    // Emit their direct functions instead of expanding F_class XOR F_generic.
    let small_at=circ.b.ops.len();
    for ac in 0..2{let mut cs=base.to_vec();cs.extend(aa.iter().enumerate().map(|(i,q)|(q,ac>>i&1!=0)));gate(circ,&cs,&sm[2],dirty);}
    let small=circ.b.ops[small_at..].to_vec();let mut default_base=base.to_vec();default_base.push((&sm[2],false));seed_logic(circ,&word,&default_base,ha,g,shift,None);circ.b.ops.extend(small.into_iter().rev());
    for a_class in [0,1,2,252,253]{
        if seed_plan::plan(shift,Some(a_class)).1.is_empty(){continue;}
        let at=circ.b.ops.len();let mut cs=base.to_vec();cs.extend(aa.iter().enumerate().map(|(i,q)|(q,a_class>>i&1!=0)));gate(circ,&cs,&sm[2],dirty);let restore=circ.b.ops[at..].to_vec();
        let mut selected=base.to_vec();selected.push((&sm[2],true));seed_logic(circ,&word,&selected,ha,g,shift,Some(a_class));circ.b.ops.extend(restore.into_iter().rev());
    }
    if shift==0{
        if numeric{
            numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[1],0,2,dirty);
            numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[0],1,1,dirty);
        }else{
            prefix_xor(circ,rank,a,c,w1,&base,&sm[1],0,2,g,hs,dirty);
            prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,g,hs,dirty);
        }
    }else if shift==1{if numeric{numeric_prefix_xor(circ,&aa,&cc,w1,&base,&sm[0],1,1,dirty);}else{prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,g,hs,dirty);}}
    if let Some(ops)=converter{circ.b.ops.extend(ops.into_iter().rev());}
}

struct Scan<'a>{rank:&'a[QReg],a:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,mask:&'a QReg,hs:&'a QReg,ha:&'a QReg,dirty:&'a[QReg],j:usize,support_end:usize,normalized_sm3:bool}
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
    fn low_update(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
        arithmetic::add(circ,self.a,self.c,None,true);
        let chart_word:Vec<QReg>=self.rank.iter().chain(std::iter::once(&self.sm[3])).map(QReg::borrowed_alias).collect();let at=circ.b.ops.len();numeric_chart::emit(circ,&chart_word,self.dirty);let chart=circ.b.ops[at..].to_vec();
        let aa:Vec<QReg>=self.a.iter().chain(chart_word[..2].iter()).map(QReg::borrowed_alias).collect();let cc:Vec<QReg>=self.c.iter().chain(chart_word[2..4].iter()).map(QReg::borrowed_alias).collect();
        let aflags=|value:usize|vec![aa.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect::<Vec<_>>()];
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
                let route_at=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|cv|if cv<=252{Some(&w1[cv+2])}else{None}).collect();for q in &cc{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{circ.cswap(q,l,r);Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),_=>None});}nodes=next;}let route=circ.b.ops[route_at..].to_vec();let mut cs=base.to_vec();cs.push((nodes[0].unwrap(),true));gate(circ,&cs,v[2],self.dirty);cs.extend(cc.iter().map(|q|(q,false)));gate(circ,&cs,v[2],self.dirty);circ.b.ops.extend(route.into_iter().rev());
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
        arithmetic::add(circ,self.a,self.c,None,false);
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
        circ.x(self.g);let at=circ.b.ops.len();super::q792_fold20_r01::table(circ,&rank,(0..32).map(|r|super::q792_r01_sumchart_r01::sh(r)==h).collect(),&[],self.g,self.dirty);let high=circ.b.ops[at..].to_vec();
        let mut cs=vec![(self.g,true),(&self.c[0],old_c0)];cs.extend((0..4).map(|b|(&self.sm[b],low>>b&1!=0)));gate(circ,&cs,self.mask,self.dirty);
        circ.b.ops.extend(high.into_iter().rev());circ.x(self.g);
        // The only displaced SM0 occurs at M=S=128. All other SM bits
        // are zero on that complete numeric boundary, so only 128/132
        // need the parity correction for physical versus logical SM0.
        if h==2&&low<=1{let base=[(&self.c[0],old_c0),(&self.sm[0],true)];super::q792_fold20_r01::table(circ,&rank,(0..32).map(|r|r==26||r==30).collect(),&base,self.mask,self.dirty);}
        circ.cx(&self.a[0],&self.c[0]);
    }
    fn upper_major(&self,circ:&mut Circuit,value:usize){let mut cs:Vec<_>=self.c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect();cs.extend(self.rank[..2].iter().enumerate().map(|(i,q)|(q,value>>(i+6)&1!=0)));gate(circ,&cs,self.mask,self.dirty);}
    fn fused(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
        let n=self.support_end.min(257);assert!(n>=3);
        let start=circ.b.ops.len();for i in 0..3{self.lower(circ,i);}let low=circ.b.ops[start..].to_vec();
        self.seed_all(circ,w1,w2);
        let at=circ.b.ops.len();super::q792_r01_sumchart_r01::emit(circ,self.rank,self.a,self.c,self.sm,self.dirty);let chart=circ.b.ops[at..].to_vec();
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
        self.seed_all(circ,w1,w2);self.low_update(circ,w1,w2,decision);
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
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);
    assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);assert!(dirty.len()>=18);assert!(j<4);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(&w1[..256]).chain(w2).chain(dirty)
        .chain([g,mask,ha,decision]).map(QReg::id).collect();
    ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]),"Q793 normal core alias");
    let start=circ.b.ops.len();let owned=(circ.b.next_qubit,circ.b.active_qubits);
    arithmetic::add(circ,a,c,None,false);
    Scan{rank,a,c,sm,g,mask,hs:&sm[3],ha,dirty,j,support_end,normalized_sm3}.fused(circ,w1,w2,decision);
    arithmetic::add(circ,a,c,None,true);
    assert_eq!((circ.b.next_qubit,circ.b.active_qubits),owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Q793 R01 normal touched omitted Work1[{h}]");
    }}
}
pub(crate) fn run_numeric_seed_check(){numeric_seed_check::run();}
