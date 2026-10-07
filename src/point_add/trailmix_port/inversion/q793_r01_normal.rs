//! Three-hole R01 normal-region arithmetic, with externally funded zero leases.
//! No global padding loan, cargo relocation, endpoint routing, or allocator hook.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_arithmetic5 as arithmetic,metadata_muxlease as mux,length_recompute::mixed_mcx};
#[path="metadata_remainder5_programs.rs"] mod programs;

fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v) in cs { assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}
        else{unique.push((q,v));}
    }
    mixed_mcx(circ,&unique,out,dirty);
}
fn a_flags<'a>(rank:&'a[QReg],a:&'a[QReg],value:usize)->Vec<Vec<(&'a QReg,bool)>>{
    programs::EQUAL[value/64].iter().map(|&(m,v)|a.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0))
        .chain((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0))).collect()).collect()
}
fn c_flags<'a>(rank:&'a[QReg],c:&'a[QReg],value:usize)->Vec<Vec<(&'a QReg,bool)>>{
    triples().iter().enumerate().filter(|(_,t)|t[1]==value/64).map(|(r,_)|
        c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0))
        .chain(rank.iter().enumerate().map(|(i,q)|(q,r>>i&1!=0))).collect()).collect()
}

/// Temporary route only. Low coefficient rails may move, so copy the result
/// into a separate SM loan and undo the entire route before decoding the chart.
fn gather_sum<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],word:&'a[QReg],offset:usize,dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    assert!(offset<=1);let start=circ.b.ops.len();arithmetic::add(circ,a,c,None,false);
    let mut nodes:Vec<_>=(0..256).map(|m|if m<=253{Some(&word[m+offset])}else{None}).collect();
    let d=&dirty[0];let rest=&dirty[1..];
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
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
fn prefix_xor(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],word:&[QReg],base:&[(&QReg,bool)],out:&QReg,
              offset:usize,needed_c:usize,dirty:&[QReg]){
    assert!((1..=2).contains(&needed_c));
    let(root,route)=gather_sum(circ,rank,a,c,word,offset,dirty);
    arithmetic::add(circ,a,c,None,true); // Read original C and its parity.
    let mut cs=base.to_vec();cs.push((root,true));gate(circ,&cs,out,dirty);
    for absent in 0..needed_c {for flag in c_flags(rank,c,absent){
        let mut ex=cs.clone();ex.extend(flag);gate(circ,&ex,out,dirty);
    }}
    arithmetic::add(circ,a,c,None,false);
    circ.b.ops.extend(route.into_iter().rev());
}

fn borrow_truth(code:usize,shift:usize,a_class:Option<usize>)->bool{
    let mut t=code&7;let b=code>>3&7;let mut v=code>>6&7;
    if let Some(a)=a_class{
        assert!(a>=2);
        if a==2{t=(t&3)|4;} // Logical coefficient head, not its passenger.
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
fn seed(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,ha:&QReg,
        w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,shift:usize){
    let c0=((j>>1)&1!=0) ^ (shift!=0); // S_old=shift+1, original quotient parity.
    let base=[(g,true),(mask,true),(&c[0],c0)];
    // g&mask implies true S_new<=2, hence SM0/1/2 are zero. The route
    // and source formulas below do not interpret S until all three restore.
    if shift==0{
        prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,dirty);
        prefix_xor(circ,rank,a,c,w1,&base,&sm[1],0,2,dirty);
    }else if shift==1{prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,dirty);}
    let word=[&w1[0],&w1[1],&w1[2],&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259],
              &w2[258-shift],&w2[257-shift],&w2[256-shift],&sm[0],&sm[1]];
    for m in terms(shift,None){let mut cs=base.to_vec();cs.extend((0..11).filter(|&i|m>>i&1!=0).map(|i|(word[i],true)));gate(circ,&cs,ha,dirty);}
    for a_class in [2,252,253]{
        let correction=terms(shift,Some(a_class));if correction.is_empty(){continue;}
        let start=circ.b.ops.len();
        for flag in a_flags(rank,a,a_class){let mut cs=base.to_vec();cs.extend(flag);gate(circ,&cs,&sm[2],dirty);}
        let restore=circ.b.ops[start..].to_vec();
        // SM2 is known zero only under the external seed guard. Retaining
        // that guard on each action makes arbitrary off-guard SM2 harmless.
        for m in correction{let mut cs=base.to_vec();cs.push((&sm[2],true));
            cs.extend((0..11).filter(|&i|m>>i&1!=0).map(|i|(word[i],true)));gate(circ,&cs,ha,dirty);
        }
        circ.b.ops.extend(restore.into_iter().rev());
    }
    if shift==0{
        prefix_xor(circ,rank,a,c,w1,&base,&sm[1],0,2,dirty);
        prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,dirty);
    }else if shift==1{prefix_xor(circ,rank,a,c,w1,&base,&sm[0],1,1,dirty);}
}

struct Scan<'a>{rank:&'a[QReg],a:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,mask:&'a QReg,hs:&'a QReg,ha:&'a QReg,dirty:&'a[QReg],j:usize,support_end:usize}
impl Scan<'_>{
    fn lower(&self,circ:&mut Circuit,i:usize){
        if i>255||(i+1)%2!=self.j%2{return;}let value=(i+1)%256;let old_c0=((value>>1)^(self.j>>1))&1!=0;
        circ.cx(&self.a[0],&self.c[0]);circ.x(self.g);let start=circ.b.ops.len();
        let clean=mux::active("Q795_R01_LOWER_CONDITIONAL_SCRATCH");if clean&&old_c0{circ.x(&self.c[0]);}
        for &(m,v)in programs::EQUAL[4+value/64]{let cs:Vec<_>=(0..5).filter(|&b|m>>b&1!=0).map(|b|(&self.rank[b],v>>b&1!=0)).collect();
            if clean{super::paired_clean_mcx::toggle(circ,&cs,self.g,&self.c[0]);}else{gate(circ,&cs,self.g,self.dirty);}}
        if clean&&old_c0{circ.x(&self.c[0]);}let high=circ.b.ops[start..].to_vec();
        let mut cs=vec![(self.g,true),(&self.c[0],old_c0)];cs.extend((0..4).map(|b|(&self.sm[b],value>>(b+2)&1!=0)));gate(circ,&cs,self.mask,self.dirty);
        circ.b.ops.extend(high.into_iter().rev());circ.x(self.g);circ.cx(&self.a[0],&self.c[0]);
    }
    fn carry(&self,circ:&mut Circuit,s:&QReg,t:&QReg,inverse:bool){
        if !inverse{circ.cx(s,t);circ.cx(self.ha,s);}circ.x(self.g);
        super::paired_clean_mcx::toggle(circ,&[(self.mask,true),(t,true),(s,true)],self.ha,self.g);circ.x(self.g);
        if inverse{circ.cx(self.ha,s);circ.cx(s,t);}
    }
    fn seed_all(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg]){
        arithmetic::add(circ,self.a,self.c,None,true);
        for shift in 0..3{if (shift+1)%2==self.j%2{seed(circ,self.rank,self.a,self.c,self.sm,self.g,self.mask,self.ha,w1,w2,self.dirty,self.j,shift);}}
        arithmetic::add(circ,self.a,self.c,None,false);
    }
    fn low_update(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
        arithmetic::add(circ,self.a,self.c,None,true);
        for shift in 0..3{if (shift+1)%2!=self.j%2{continue;}
            let c0=((self.j>>1)&1!=0)^(shift!=0);
            let b=[&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259]];
            let v=[&w2[258-shift],&w2[257-shift],&w2[256-shift]];
            let mut change=|target:usize,extra:&[(&QReg,bool)]|{
                let base=[(self.g,true),(self.mask,true),(decision,true),(&w1[0],false),(&self.c[0],c0)];
                let mut cs=base.to_vec();cs.extend_from_slice(extra);gate(circ,&cs,b[target],self.dirty);
                // Suppress physical v bits that are actually gap/cargo above
                // the proven source width. The semantic high source is zero.
                for ac in [252,253]{let keep=256usize.saturating_sub(ac+shift).min(3);
                    if extra.iter().any(|&(q,_)|(keep..3).any(|i|q.id()==v[i].id())){
                        for flag in a_flags(self.rank,self.a,ac){let mut ex=cs.clone();ex.extend(flag);gate(circ,&ex,b[target],self.dirty);}
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
        arithmetic::add(circ,self.a,self.c,None,false);
    }
    fn fused(&self,circ:&mut Circuit,w1:&[QReg],w2:&[QReg],decision:&QReg){
        let n=self.support_end.min(257);assert!(n>=3);
        let start=circ.b.ops.len();for i in 0..3{self.lower(circ,i);}let low=circ.b.ops[start..].to_vec();
        self.seed_all(circ,w1,w2);
        let mut group=-1isize;let mut updates=Vec::new();
        for i in 3..n{
            let at=circ.b.ops.len();self.lower(circ,i);let value=256-i;let h=(value/64)as isize;
            if super::q795_r01_cache_clean::enabled(){super::q795_r01_cache_clean::transition(circ,self.rank,self.a,self.c,self.g,self.hs,&self.dirty[0],&self.dirty[1..],group,h);}
            else{arithmetic::sum_flag_transition(circ,self.rank,self.a,self.c,self.g,self.hs,&self.dirty[0],&self.dirty[1..],group,h);}group=h;
            let mut cs=vec![(self.hs,true)];cs.extend((0..6).map(|b|(&self.c[b],value>>b&1!=0)));
            circ.x(self.g);super::paired_clean_mcx::toggle(circ,&cs,self.mask,self.g);circ.x(self.g);
            updates.push(circ.b.ops[at..].to_vec());self.carry(circ,&w2[258-i],&w1[258-i],false);
        }
        circ.cx(self.g,decision);circ.ccx(self.g,self.ha,decision);
        for i in (3..n).rev(){
            self.carry(circ,&w2[258-i],&w1[258-i],true);circ.cx(self.ha,&w2[258-i]);
            gate(circ,&[(self.g,true),(self.mask,true),(&w2[258-i],true),(decision,true)],&w1[258-i],self.dirty);circ.cx(self.ha,&w2[258-i]);
            circ.b.ops.extend(updates.pop().unwrap().into_iter().rev());
        }
        self.seed_all(circ,w1,w2);self.low_update(circ,w1,w2,decision);
        circ.b.ops.extend(low.into_iter().rev());
    }
}

/// Exact normal core, AFTER physical pre-rotation and quotient-decision loan.
/// Caller must supply g=1 exactly on its intended R01 domain A>=2,A+C<=253;
/// genuine HA=mask=hs=0 under g; decision=old high residual bit there. All
/// scratch may be dirty off g. Metadata C is ORIGINAL on entry and return.
/// The caller owns zero leases, cargo moves, guard construction and quotient
/// insertion. In particular this function NEVER borrows W1[A+1]/W2[A+1].
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,hs:&QReg,ha:&QReg,
                   decision:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,support_end:usize){
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);
    assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);assert!(dirty.len()>=18);assert!(j<4);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(&w1[..256]).chain(w2).chain(dirty)
        .chain([g,mask,hs,ha,decision]).map(QReg::id).collect();
    ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]),"Q793 normal core alias");
    let start=circ.b.ops.len();let owned=(circ.b.next_qubit,circ.b.active_qubits);
    arithmetic::add(circ,a,c,None,false);
    Scan{rank,a,c,sm,g,mask,hs,ha,dirty,j,support_end}.fused(circ,w1,w2,decision);
    arithmetic::add(circ,a,c,None,true);
    assert_eq!((circ.b.next_qubit,circ.b.active_qubits),owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Q793 R01 normal touched omitted Work1[{h}]");
    }}
}
#[path="q793_r01_normal_check.rs"] mod check;
pub fn run(){check::run();}
