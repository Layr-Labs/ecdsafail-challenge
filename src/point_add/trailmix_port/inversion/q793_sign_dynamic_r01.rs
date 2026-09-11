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
    let mut anf:Vec<_>=triples().into_iter().map(f).collect();
    for b in 0..5{for m in 0..32{if m>>b&1!=0{anf[m]^=anf[m^(1<<b)];}}}
    anf.into_iter().enumerate().filter(|&(_,v)|v).map(|(m,_)|(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)).collect()).collect()
}
fn truth(circ:&mut Circuit,inputs:&[&QReg],extra:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],f:impl Fn(usize)->bool){
    assert!(inputs.len()<=12);let n=1<<inputs.len();let mut anf:Vec<_>=(0..n).map(f).collect();
    for b in 0..inputs.len(){for m in 0..n{if m>>b&1!=0{anf[m]^=anf[m^(1<<b)];}}}
    for(m,on)in anf.into_iter().enumerate(){if on{let mut cs=extra.to_vec();cs.extend(inputs.iter().enumerate().filter(|&(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));gate(circ,&cs,out,dirty);}}
}

// C is in the prepared C+S basis. The base reads ordinary shifted u bits;
// only the unique small S for this clock needs the modulo8 replacement.
// a_fixed normalizes every short t cargo without overwriting its host.
fn low(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],w1:&[QReg],w2:&[QReg],out:&QReg,extra:&[(&QReg,bool)],dirty:&[QReg],j:usize,width:usize,a_fixed:Option<usize>){
    assert!((1..=3).contains(&width));
    let tval=|z:usize|if let Some(a)=a_fixed{(z&((1<<a)-1))|(1<<a)}else{z&7};
    let ordinary=[&w1[0],&w1[1],&w1[2],&w2[0],&w2[1],&w2[2]];
    truth(circ,&ordinary,extra,out,dirty,|z|tval(z)>(z>>3&((1<<width)-1)));
    let shift=(4-j)%4;if shift==3{return;}
    let inputs=[&w1[0],&w1[1],&w1[2],&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259],&w2[257-shift],&w2[256-shift],&w2[0],&w2[1],&w2[2]];
    let corrected=|z:usize,short_c:usize|{
        let t=tval(z);let b=z>>3&7;let mut v1=z>>6&1;let mut v2=z>>7&1;
        if short_c==1{v1=0;v2=0;}else if short_c==2{v1=1;v2=0;}else if short_c==3{v2=1;}
        let u=if t&1!=0{b}else{1|((1^v1^((t>>1&1)&(b&1)))<<1)|((1^v2^((t>>2&1)&(b&1))^((t>>1&1)&(b>>1&1)))<<2)};
        let raw=z>>8&7;let mut rhs=0;for i in 0..width{rhs|=if i+shift<3{(u>>(i+shift)&1)<<i}else{(raw>>i&1)<<i};}
        t>rhs
    };
    for short_c in 0..=3{
        for mut term in rank_terms(rank,|t|t[2]==0&&(short_c==0||t[1]==0)){
            term.extend_from_slice(extra);term.extend(sm.iter().map(|q|(q,false)));
            if short_c!=0{term.extend(c.iter().enumerate().map(|(i,q)|(q,(short_c+shift)>>i&1!=0)));}
            truth(circ,&inputs,&term,out,dirty,|z|if short_c==0{corrected(z,0)^(tval(z)>(z>>8&((1<<width)-1)))}else{corrected(z,0)^corrected(z,short_c)});
        }
    }
}

struct Range<'a>{rank:&'a[QReg],c:&'a[QReg],sm:&'a[QReg],g:&'a QReg,cache:&'a QReg,dirty:&'a[QReg],j:usize,group:isize}
impl Range<'_>{
    fn controls(&mut self,circ:&mut Circuit,value:usize)->Vec<(&QReg,bool)>{
        let h=(value/64)as isize;if h!=self.group{super::metadata_phase115_phased::sum_flag_raw_transition(circ,self.rank,self.c,self.sm,self.g,self.cache,self.dirty,self.j,self.group,h);self.group=h;}
        let mut cs=vec![(self.g,true),(self.cache,true)];cs.extend(self.c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));cs
    }
    fn close(&mut self,circ:&mut Circuit){super::metadata_phase115_phased::sum_flag_raw_transition(circ,self.rank,self.c,self.sm,self.g,self.cache,self.dirty,self.j,self.group,-1);self.group=-1;}
}

// k=257-C-S <=3 is handled before any cargo or mask loans. On this domain
// A<=k, so ten exact (k,A) readers normalize t and use at most three u bits.
fn short_compare(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,dirty,j,false);
    let mut range=Range{rank,c,sm,g,cache,dirty,j,group:-1};
    for k in 0..=3{let common=range.controls(circ,257-k);for av in 0..=k{
        for mut cs in rank_terms(rank,|t|t[0]==0){cs.extend_from_slice(&common);cs.extend(a.iter().enumerate().map(|(i,q)|(q,av>>i&1!=0)));
            if k==0{gate(circ,&cs,sign,dirty);}else{low(circ,rank,c,sm,w1,w2,sign,&cs,dirty,j,k,Some(av));}
        }
    }}range.close(circ);super::metadata_phase115_phased::prepare(circ,c,sm,g,None,dirty,j,true);
}
fn short_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg],j:usize){
    // F C F C pays for an initially dirty high-group flag. Also bypass
    // C1/S0 (sum1): u=p, t<p/2, so its Sign is already zero.
    let scratch=&dirty[0];let tail=&dirty[1..];
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,tail,j,false);
    for (h,values) in [(0usize,vec![1usize]),(3,vec![254usize,255]),(4,vec![256,257])]{
        for _ in 0..2{
            super::metadata_phase115_phased::sum_flag_raw(circ,rank,c,sm,g,scratch,tail,j,h);
            for &value in &values{let mut cs=vec![(g,true),(scratch,true)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));gate(circ,&cs,out,tail);}
        }
    }
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,tail,j,true);
}

fn gather_a<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&'a[QReg],offset:usize,max:usize,dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|v|if v<=max{Some(&w1[v+offset])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{if level<6{circ.cswap(&a[level],l,r);}else{super::metadata_muxlease::predicate_swap(circ,rank,0,level-6,l,r,dirty);}Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
fn gather_sum<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],cache:&QReg,word:&'a[QReg],base:usize,min:usize,dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let mut nodes=vec![None;512];for value in min..=257{nodes[value]=Some(&word[base-value]);}let ts=triples();
    for level in 0..9{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{let controls:Vec<_>=rank.iter().chain(std::iter::once(cache)).collect();let truth:Vec<_>=(0..64).map(|z|((ts[z&31][1]+ts[z&31][2]+(z>>5))>>(level-6))&1!=0).collect();super::metadata_muxlease::truth_swap(circ,&controls,truth,l,r,dirty);}Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
fn cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    // Move the SECOND passenger first. At A254 and C+S3 its relocated
    // W2[255] host is precisely the destination of the first handoff.
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let(l,lop)=gather_a(circ,rank,a,w1,2,253,dirty);let(r,rop)=gather_sum(circ,rank,c,cache,w2,257,1,dirty);
    swap(circ,&[(g,true)],l,r,dirty);
    let mut a254=vec![(g,true)];a254.extend(rank.iter().enumerate().map(|(i,q)|(q,29>>i&1!=0)));a254.extend(a.iter().enumerate().map(|(i,q)|(q,254>>i&1!=0)));swap(circ,&a254,l,r,dirty);
    circ.b.ops.extend(rop.into_iter().rev());circ.b.ops.extend(lop.into_iter().rev());
    for sum in [1usize,3]{let mut cs=a254.clone();cs.extend(c.iter().enumerate().map(|(i,q)|(q,sum>>i&1!=0)));cs.extend(sm.iter().map(|q|(q,false)));swap(circ,&cs,&w2[255],&w2[257-sum],dirty);}
    let(l,lop)=gather_a(circ,rank,a,w1,1,254,dirty);let(r,rop)=gather_sum(circ,rank,c,cache,w2,258,1,dirty);circ.cswap(g,l,r);circ.b.ops.extend(rop.into_iter().rev());circ.b.ops.extend(lop.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}
fn c12_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,out:&QReg,dirty:&[QReg]){for cv in 1usize..=2{for mut cs in rank_terms(rank,|t|t[1]==0){cs.push((g,true));cs.extend(c.iter().enumerate().map(|(i,q)|(q,cv>>i&1!=0)));gate(circ,&cs,out,dirty);}}}
fn mask_loan(circ:&mut Circuit,rank:&[QReg],c:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,w1:&[QReg],dirty:&[QReg]){
    c12_flag(circ,rank,c,g,cache,dirty);let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|v|if v>=3{Some(&w1[258-v])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){(Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{super::metadata_muxlease::predicate_swap(circ,rank,1,level-6,l,r,dirty);}Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
    let route=circ.b.ops[start..].to_vec();swap(circ,&[(g,true),(cache,false)],nodes[0].unwrap(),mask,dirty);circ.b.ops.extend(route.into_iter().rev());swap(circ,&[(g,true),(cache,true)],&w1[255],mask,dirty);c12_flag(circ,rank,c,g,cache,dirty);
}
fn top_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,w1:&[QReg],dirty:&[QReg],j:usize){
    // C+S1/2 imply k256/255. Both true top bits are zero because A<=254.
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);let(q,route)=gather_sum(circ,rank,c,cache,w1,257,3,dirty);
    // Pruned leaves are arbitrary off their supported sum. Explicitly
    // cancel sum1/2 so the fallback cannot read a data or passenger bit.
    circ.ccx(g,q,mask);
    for sum in 1usize..=2{for mut cs in rank_terms(rank,|t|t[1]+t[2]==0){cs.extend([(g,true),(cache,false),(q,true)]);cs.extend(c.iter().enumerate().map(|(i,x)|(x,sum>>i&1!=0)));gate(circ,&cs,mask,dirty);}}
    circ.b.ops.extend(route.into_iter().rev());super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}

fn core(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,top:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    super::metadata_phase115_phased::prepare(circ,c,sm,g,None,dirty,j,false);let start=circ.b.ops.len();
    for i in 3..256{circ.cx(&w1[i],&w2[i]);}
    for i in (4..256).rev(){circ.cx(&w1[i-1],&w1[i]);}
    // At the small-S v1/v2 readers, undo D=target XOR original_source.
    // The neighboring-XOR source frame reconstructs original t_i by the
    // prefix XOR source[3..=i]. These v positions are always >=k, outside
    // the comparison's causal prefix, so they can stay normalized until
    // the exact inverse. No additional output or clean rail is needed.
    let shift=(4-j)%4;
    if shift<3{for pos in [257-shift,256-shift]{if pos<256{for i in 3..=pos{circ.cx(&w1[i],&w2[pos]);}}}}
    low(circ,rank,c,sm,w1,w2,&w1[3],&[],dirty,j,3,None);
    // x_i=t_i XOR B_i; D_i=t_i XOR u_i. Adjacent-XOR preparation gives
    // x_(i+1)=t_(i+1) XOR B_i XOR x_i*D_i with one negative-control CCX.
    for i in 3..255{circ.x(&w2[i]);circ.ccx(&w1[i],&w2[i],&w1[i+1]);circ.x(&w2[i]);}
    let compute=circ.b.ops[start..].to_vec();
    let mut range=Range{rank,c,sm,g,cache,dirty,j,group:-1};
    for k in 4..=255{let mut cs=range.controls(circ,257-k);cs.extend([(top,false),(&w1[k-1],true),(&w2[k-1],false)]);gate(circ,&cs,sign,dirty);}
    range.close(circ);circ.b.ops.extend(compute.into_iter().rev());
    for k in 4..=255{let mut cs=range.controls(circ,257-k);cs.extend([(top,false),(&w1[k-1],true)]);gate(circ,&cs,sign,dirty);}
    range.close(circ);super::metadata_phase115_phased::prepare(circ,c,sm,g,None,dirty,j,true);
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,_n:usize){
    assert!(helpers.len()>=22);let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    super::q798_sign_erase::code(circ,p1,p2,sign,helpers,false);
    short_compare(circ,rank,a,c,sm,p1,p2,sign,w1,w2,helpers,j);
    short_flag(circ,rank,c,sm,p1,p2,helpers,j);super::q795_t11::park_c1(circ,p1,p2,sign,helpers);
    let movestart=circ.b.ops.len();
    // Internal S0 is just before the exit's final right rotation: A254's
    // second passenger is still W2[256]. S>0 boundary callers use W2[255].
    if j==0{let mut cs=vec![(p1,true)];cs.extend(rank.iter().enumerate().map(|(i,q)|(q,29>>i&1!=0)));cs.extend(a.iter().enumerate().map(|(i,q)|(q,254>>i&1!=0)));cs.extend(sm.iter().map(|q|(q,false)));swap(circ,&cs,&w2[255],&w2[256],helpers);}
    cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);let moves=circ.b.ops[movestart..].to_vec();
    let mask=&helpers[0];let dirty=&helpers[1..];let ls=circ.b.ops.len();mask_loan(circ,rank,c,p1,p2,mask,w1,dirty);let loan=circ.b.ops[ls..].to_vec();
    let ts=circ.b.ops.len();top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);let top=circ.b.ops[ts..].to_vec();
    circ.cswap(p1,p2,mask);circ.ccx(p1,p2,sign);
    // Mask is now a funded zero cache; P2 retains the fixed top branch.
    // Keeping that branch explicit avoids sharing the short-domain park.
    core(circ,rank,c,sm,p1,mask,p2,sign,w1,w2,dirty,j);
    circ.cswap(p1,p2,mask);circ.b.ops.extend(top.into_iter().rev());circ.b.ops.extend(loan.into_iter().rev());circ.b.ops.extend(moves.into_iter().rev());
    super::q795_t11::park_c1(circ,p1,p2,sign,helpers);short_flag(circ,rank,c,sm,p1,p2,helpers,j);super::q798_sign_erase::code(circ,p1,p2,sign,helpers,true);
    assert_eq!(circ.b.next_qubit,owned);for op in &circ.b.ops[start..]{for h in [256,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"Sign touched omitted source{h}");}}
}

#[path="q793_sign_dynamic_r01_check.rs"]
pub mod verification;
