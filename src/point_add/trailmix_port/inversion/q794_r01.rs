//! Two-hole restoring R01 on the actual rank5 dynamic interval.
//! New candidate, not a whole-Q or cargo-lifecycle certification.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_arithmetic5 as arithmetic,metadata_muxlease as mux,length_recompute::mixed_mcx};
#[path="metadata_remainder5_programs.rs"] mod programs;
#[path="q794_r01_factor.rs"] mod factor;
#[path="q794_r01_numeric.rs"] pub(crate) mod numeric;
fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();for &(q,v)in cs{
        assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}else{unique.push((q,v));}
    }
    if super::q794_r01_odd_cache::mode()!=0&&dirty.len()<unique.len().saturating_sub(2){
        let split=unique.len()/2;assert!(!dirty.is_empty()&&dirty.len()-1>=split.saturating_sub(2)&&dirty.len()-1>=(unique.len()-split+1).saturating_sub(2),"R01 cached branch split-MCX lender shortage: controls={} dirty={}",unique.len(),dirty.len());
    }
    mixed_mcx(circ,&unique,out,dirty);
}
fn borrow_word(circ:&mut Circuit,rank:&[QReg],a:&[QReg],guard:Option<&QReg>,passenger:&QReg,word:&[QReg],dirty:&[QReg]){
    mux::exchange(circ,rank,a,0,guard,passenger,&word[1..257].iter().collect::<Vec<_>>(),dirty,false);
}
fn phase_guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    gate(circ,&[(p1,false),(p2,true)],g,dirty);
    for &(m,v)in programs::EQUAL[3]{let mut cs=vec![(p1,false),(p2,true)];cs.extend(a.iter().map(|q|(q,true)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));gate(circ,&cs,g,dirty);}
}
fn endpoint(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    // A+C=255 has no low carry: A_low XOR C_low=63 and high sum=3.
    for i in 0..6{circ.cx(&a[i],&c[i]);}
    for (r,t)in triples().iter().enumerate(){if t[0]+t[1]!=3{continue;}
        let mut cs=vec![(p1,false),(p2,true)];cs.extend(c.iter().map(|q|(q,true)));cs.extend(rank.iter().enumerate().map(|(i,q)|(q,r>>i&1!=0)));gate(circ,&cs,g,dirty);
    }
    for i in (0..6).rev(){circ.cx(&a[i],&c[i]);}
}

/// Existing C is unprepared on entry and prepared on return. All candidates
/// are actual physical rails2..256. The omitted endpoint has no tree leaf.
/// The caller's normal guard excludes M255; q1 use additionally excludes C0.
fn gather_sum<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],word:&'a[QReg],offset:usize,dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    assert!(offset==1||offset==2);let start=circ.b.ops.len();
    arithmetic::add(circ,a,c,None,false);
    let mut nodes:Vec<_>=(0..256).map(|m|if m<=254&&m+offset>=2{Some(&word[m+offset])}else{None}).collect();
    let d=&dirty[0];let rest=&dirty[1..];
    for level in 0..8{
        if level==6&&mux::active("Q794_R01_SUM_XOR"){
            assert_eq!(nodes.len(),4);let roots:Vec<_>=nodes.iter().map(|q|q.expect("R01 sum four real roots")).collect();
            super::q794_sum_xor::high(circ,rank,a,c,&roots,dirty);
            nodes=vec![Some(roots[0])];break;
        }
        let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{
            if level<6{circ.cswap(&c[level],left,right);}else{
                let bit=level-6;let ts=triples();let ctrls:Vec<_>=rank.iter().chain(std::iter::once(d)).collect();
                let truth:Vec<_>=(0..64).map(|r|((ts[r&31][0]+ts[r&31][1]+(r>>5))>>bit)&1!=0).collect();
                arithmetic::add(circ,a,c,None,true);arithmetic::add(circ,a,c,Some(d),false);
                mux::truth_swap(circ,&ctrls,truth.clone(),left,right,rest);
                arithmetic::add(circ,a,c,None,true);arithmetic::add(circ,a,c,Some(d),false);
                mux::truth_swap(circ,&ctrls,truth,left,right,rest);
                mux::truth_swap(circ,&rank.iter().collect::<Vec<_>>(),ts.iter().map(|t|((t[0]+t[1])>>bit)&1!=0).collect(),left,right,rest);
            }Some(left)
        },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
fn quotient(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,decision:&QReg,w1:&[QReg],dirty:&[QReg]){
    let(root,ops)=gather_sum(circ,rank,a,c,w1,2,dirty);circ.cswap(g,root,decision);circ.b.ops.extend(ops.into_iter().rev());
}
fn flag_terms<'a>(rank:&'a[QReg],a:&'a[QReg],c:&'a[QReg],flag:usize)->Vec<Vec<(&'a QReg,bool)>>{
    if flag==3{return triples().iter().enumerate().filter(|(_,t)|t[1]==0).map(|(r,_)|c.iter().map(|q|(q,false)).chain(rank.iter().enumerate().map(|(i,q)|(q,r>>i&1!=0))).collect()).collect();}
    let av=[0usize,1,254][flag];programs::EQUAL[av/64].iter().map(|&(m,v)|a.iter().enumerate().map(|(i,q)|(q,av>>i&1!=0)).chain((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0))).collect()).collect()
}
fn chart_seed(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,mask:&QReg,ha:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],shift:usize){
    // The parity clock fixes whether an active low boundary can be0 or1.
    // C is temporarily original here. qpre0=0; for shift1 qpre1=0 too.
    let gathered=if shift==0{Some(gather_sum(circ,rank,a,c,w1,1,dirty))}else{None};
    if gathered.is_some(){arithmetic::add(circ,a,c,None,true);}
    let chart=[&w1[0],&w1[1],&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[258-shift],&w2[257-shift]];
    // [six retained low bits, qpre1, A0, A1, A254, C0]. A0 has t=1,u=0;
    // its physical b1 currently contains the old HA passenger. A1 t1 is a
    // phase passenger. At A254/shift1, v=1 and physical v1 is cargo at A+2.
    let mut anf:Vec<bool>=(0..2048).map(|z|{
        let mut t=z&3;let mut b=z>>2&3;let mut v=z>>4&3;let mut q=z>>6&1;
        if z&128!=0{t=1;b=0;}else if z&256!=0{t|=2;}
        if shift==1&&z&512!=0{v&=1;}if z&1024!=0{q=0;}
        let r=if t&1!=0{3usize.wrapping_sub(b*v).wrapping_mul(t).wrapping_sub(if shift==0{2*q*v}else{0})&3}else{b};
        r<((v<<shift)&3)
    }).collect();
    for i in 0..11{for m in 0..2048{if m>>i&1!=0{anf[m]^=anf[m^(1<<i)];}}}
    let flags:Vec<_>=(0..4).map(|f|flag_terms(rank,a,c,f)).collect();
    if mux::active("Q794_R01_SEED_FACTOR") {
        let mut inputs=chart.to_vec();if let Some((q,_))=&gathered{inputs.push(q);}
        factor::emit(circ,&inputs,g,mask,ha,dirty,&flags,&anf,shift);
    } else { for(m,on)in anf.into_iter().enumerate(){if !on||(m&896).count_ones()>1||shift==1&&m&64!=0{continue;}
        let mut base=vec![(g,true),(mask,true)];for i in 0..6{if m>>i&1!=0{base.push((chart[i],true));}}
        if m&64!=0{base.push((gathered.as_ref().unwrap().0,true));}
        let mut terms=vec![base];for f in 0..4{if m>>(7+f)&1!=0{terms=terms.into_iter().flat_map(|old|flags[f].iter().map(move|flag|{let mut cs=old.clone();cs.extend(flag.iter().copied());cs})).collect();}}
        for cs in terms{gate(circ,&cs,ha,dirty);}
    } }
    if let Some((_,ops))=gathered{arithmetic::add(circ,a,c,None,false);circ.b.ops.extend(ops.into_iter().rev());}
}
struct Scan<'a>{rank:&'a[QReg],a:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,mask:&'a QReg,hs:&'a QReg,ha:&'a QReg,dirty:&'a[QReg],cache:Option<&'a QReg>,j:usize,support_end:usize}
impl Scan<'_>{
    fn lower(&self,circ:&mut Circuit,i:usize){
        if i>255||(i+1)%2!=self.j%2{return;}let value=(i+1)%256;let old_c0=((value>>1)^(self.j>>1))&1!=0;
        circ.cx(&self.a[0],&self.c[0]);circ.x(self.g);let start=circ.b.ops.len();
        let clean=mux::active("Q795_R01_LOWER_CONDITIONAL_SCRATCH");if clean&&old_c0{circ.x(&self.c[0]);}
        if clean&&mux::active("Q794_R01_S_AFFINE") {super::q795_r01_s_affine::emit(circ,self.rank,value/64,self.g,&self.c[0]);}
        else {for &(m,v)in programs::EQUAL[4+value/64]{let cs:Vec<_>=(0..5).filter(|&b|m>>b&1!=0).map(|b|(&self.rank[b],v>>b&1!=0)).collect();if clean{super::paired_clean_mcx::toggle(circ,&cs,self.g,&self.c[0]);}else{gate(circ,&cs,self.g,self.dirty);}}}
        if clean&&old_c0{circ.x(&self.c[0]);}let high=circ.b.ops[start..].to_vec();
        let mut cs=vec![(self.g,true),(&self.c[0],old_c0)];cs.extend((0..4).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));gate(circ,&cs,self.mask,self.dirty);
        circ.b.ops.extend(high.into_iter().rev());circ.x(self.g);circ.cx(&self.a[0],&self.c[0]);
    }
    fn carry(&self,circ:&mut Circuit,s:&QReg,t:&QReg,inverse:bool){
        if !inverse{circ.cx(s,t);circ.cx(self.ha,s);}circ.x(self.g);
        super::paired_clean_mcx::toggle(circ,&[(self.mask,true),(t,true),(s,true)],self.ha,self.g);circ.x(self.g);
        if inverse{circ.cx(self.ha,s);circ.cx(s,t);}
    }
    fn even(&self,circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,t0:&QReg){
        let mut base=cs.to_vec();base.push((t0,false));gate(circ,&base,out,self.dirty);
        for flag in flag_terms(self.rank,self.a,self.c,0){let mut ex=base.clone();ex.extend(flag);gate(circ,&ex,out,self.dirty);}
    }
    fn low_update(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg,shift:usize){
        let base=[(self.g,true),(self.mask,true),(decision,true)];
        if shift==0{
            // Borrow into bit1 uses INPUT b0. The low update is therefore
            // ordered high-before-low; qpre is supplied by quotient insertion.
            let mut cs=base.to_vec();cs.push((&w2[257],true));self.even(circ,&cs,&w2[1],&w1[0]);
            let mut cs=base.to_vec();cs.extend([(&w2[258],true),(&w2[0],false)]);self.even(circ,&cs,&w2[1],&w1[0]);
            let mut cs=base.to_vec();cs.push((&w2[258],true));self.even(circ,&cs,&w2[0],&w1[0]);
        }else{let mut cs=base.to_vec();cs.push((&w2[257],true));self.even(circ,&cs,&w2[0],&w1[0]);}
    }
    fn fused(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
        if numeric::selected(circ,self.support_end.min(257),self.j){numeric::fused(self,circ,w1,w2,decision);return;}
        let n=self.support_end.min(257);assert!(n>=2);let shift=if self.j&1!=0{0}else{1};
        let start=circ.b.ops.len();self.lower(circ,0);self.lower(circ,1);let low=circ.b.ops[start..].to_vec();
        arithmetic::add(circ,self.a,self.c,None,true);chart_seed(circ,self.rank,self.a,self.c,self.g,self.mask,self.ha,w1,w2,self.dirty,shift);arithmetic::add(circ,self.a,self.c,None,false);
        if let Some(h)=self.cache{super::q794_r01_odd_cache::loan(circ,self.rank,self.a,self.g,h,w1,self.dirty,true);}
        let mut sgroup=None;let mut group=-1isize;let mut updates=Vec::new();
        for i in 2..n{
            let at=circ.b.ops.len();
            if let Some(h)=self.cache.filter(|_|super::q794_r01_odd_cache::eligible(i,self.j)){super::q794_r01_odd_cache::lower(circ,self.rank,self.a,self.c,self.sm,self.g,self.mask,h,self.dirty,i,self.j,&mut sgroup);}else{self.lower(circ,i);}
            let value=256-i;let h=(value/64)as isize;
            if super::q795_r01_cache_clean::enabled(){super::q795_r01_cache_clean::transition(circ,self.rank,self.a,self.c,self.g,self.hs,&self.dirty[0],&self.dirty[1..],group,h);}else{arithmetic::sum_flag_transition(circ,self.rank,self.a,self.c,self.g,self.hs,&self.dirty[0],&self.dirty[1..],group,h);}group=h;
            let mut cs=vec![(self.hs,true)];cs.extend((0..6).map(|b|(&self.c[b],value>>b&1!=0)));
            circ.x(self.g);super::paired_clean_mcx::toggle(circ,&cs,self.mask,self.g);circ.x(self.g);
            updates.push(circ.b.ops[at..].to_vec());self.carry(circ,&w2[258-i],&w1[258-i],false);
        }
        circ.cx(self.g,decision);circ.ccx(self.g,self.ha,decision);
        for i in (2..n).rev(){
            self.carry(circ,&w2[258-i],&w1[258-i],true);circ.cx(self.ha,&w2[258-i]);
            gate(circ,&[(self.g,true),(self.mask,true),(&w2[258-i],true),(decision,true)],&w1[258-i],self.dirty);circ.cx(self.ha,&w2[258-i]);
            circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
        }
        if let Some(h)=self.cache{super::q794_r01_odd_cache::loan(circ,self.rank,self.a,self.g,h,w1,self.dirty,false);}
        arithmetic::add(circ,self.a,self.c,None,true);chart_seed(circ,self.rank,self.a,self.c,self.g,self.mask,self.ha,w1,w2,self.dirty,shift);
        self.low_update(circ,w1,w2,decision,shift);arithmetic::add(circ,self.a,self.c,None,false);
        circ.b.ops.extend(low.into_iter().rev());
    }
}
/// Entry: reachable decoded-cargo R01 after its pre-rotation, unchanged
/// entry-clock metadata. HA gap W2[A+1] is zero here; cargo is at A+2.
pub(super) fn signless(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,support_end:usize){
    assert!(helpers.len()>=23);let start=circ.b.ops.len();let owned=circ.b.next_qubit;
    let g=&helpers[0];let ha=&helpers[1];let decision=&helpers[2];let dirty=&helpers[3..];
    borrow_word(circ,rank,a,None,g,w1,dirty);phase_guard(circ,rank,a,p1,p2,g,dirty);endpoint(circ,rank,a,c,p1,p2,g,dirty);
    borrow_word(circ,rank,a,Some(g),ha,w2,dirty);circ.cx(g,p2);quotient(circ,rank,a,c,g,decision,w1,dirty);
    arithmetic::add(circ,a,c,None,false);
    let use_cache=!numeric::selected(circ,support_end.min(257),j)&&super::q794_r01_odd_cache::selected(circ,support_end.min(257),j);
    let (cache,scan_dirty)=if use_cache{let(h,rest)=dirty.split_last().unwrap();assert!(rest.len()>=19);(Some(h),rest)}else{(None,dirty)};
    Scan{rank,a,c,sm,g,mask:p1,hs:p2,ha,dirty:scan_dirty,cache,j,support_end}.fused(circ,w1,w2,decision);
    arithmetic::add(circ,a,c,None,true);quotient(circ,rank,a,c,g,decision,w1,dirty);circ.cx(g,p2);borrow_word(circ,rank,a,Some(g),ha,w2,dirty);
    endpoint(circ,rank,a,c,p1,p2,g,dirty);phase_guard(circ,rank,a,p1,p2,g,dirty);
    endpoint(circ,rank,a,c,p1,p2,g,dirty);
    // The width2 endpoint has v=1,r<=1. Even t moves r0 into overflow q0
    // payload b1 and clears b0; odd t already implies q0=1 XOR u0.
    circ.cx(&w2[1],&w2[0]);let base=[(g,true),(&w1[0],false),(&w2[0],true)];gate(circ,&base,&w2[1],dirty);
    for flag in flag_terms(rank,a,c,0){let mut cs=base.to_vec();cs.extend(flag);gate(circ,&cs,&w2[1],dirty);}circ.cx(&w2[1],&w2[0]);
    endpoint(circ,rank,a,c,p1,p2,g,dirty);borrow_word(circ,rank,a,None,g,w1,dirty);
    assert_eq!(circ.b.next_qubit,owned);
    for op in &circ.b.ops[start..]{for h in [257usize,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"R01 touched omitted Work1[{h}]");}}
}
#[path="q794_r01_check.rs"] mod check;
pub fn run(){check::run();}
pub fn run_seed_factor(){factor::run();}
