//! Own two-hole Sign adapter, derived from public Q795's dual-cargo wrapper.
//! Pending native integration; no new owned rails. Do not dispatch by default.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}

fn controlled_swap(circ:&mut Circuit,cs:&[(&QReg,bool)],left:&QReg,right:&QReg,dirty:&[QReg]){
    assert_ne!(left.id(),right.id());
    circ.cx(right,left);let mut c=cs.to_vec();c.push((left,true));
    mixed_mcx(circ,&c,right,dirty);circ.cx(right,left);
}

// Offset2 is selected only in phase11 A<=254. Drop the A255 leaf so that
// even an offguard permutation contains no reference to hole Work1[257].
fn gather_a2<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&'a[QReg],dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();
    let mut nodes:Vec<_>=(0..256).map(|v|if v<=254&&circ.q797_a_support.is_none_or(|(lo,hi)|(lo..hi).contains(&v)){Some(&word[v+2])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{if level<6{circ.cswap(&a[level],l,r);}else{super::metadata_muxlease::predicate_swap(circ,rank,0,level-6,l,r,dirty);}Some(l)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    (nodes[0].expect("nonempty active A support"),circ.b.ops[start..].to_vec())
}

fn gather_top<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],cache:&QReg,word:&'a[QReg],dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let mut nodes=vec![None;512];
    for value in 1..=257{nodes[value]=Some(&word[257-value]);}
    let ts=triples();
    for level in 0..9{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{
            let controls:Vec<_>=rank.iter().chain(std::iter::once(cache)).collect();
            let truth:Vec<_>=(0..64).map(|v|((ts[v&31][1]+ts[v&31][2]+(v>>5))>>(level-6))&1!=0).collect();
            super::metadata_muxlease::truth_swap(circ,&controls,truth,l,r,dirty);
        }Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}

fn move_top_cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    let(left,l)=gather_a2(circ,rank,a,w1,dirty);
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let(right,r)=gather_top(circ,rank,c,cache,w2,dirty);
    circ.cswap(g,left,right);circ.b.ops.extend(r.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
    circ.b.ops.extend(l.into_iter().rev());
}

fn gather_c<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],w1:&'a[QReg],dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|v|if v>=2{Some(&w1[258-v])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{super::metadata_muxlease::predicate_swap(circ,rank,1,level-6,l,r,dirty);}Some(l)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}

// cache is0 under g at this boundary. After BOTH cargo handoffs:
// C1 -> v=1,r=0,u=p,t<p/2, and source255/source256 are both zero.
// Choose255 for S0 to avoid the existing top_flag/topcarry host256;
// the C1/S0 comparator center is separately disabled (result always false).
fn mask_loan(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,w1:&[QReg],dirty:&[QReg],j:usize){
    super::q795_t11::c1_flag(circ,rank,c,g,cache,dirty);
    let(root,ops)=gather_c(circ,rank,c,w1,dirty);
    controlled_swap(circ,&[(g,true),(cache,false)],root,mask,dirty);
    circ.b.ops.extend(ops.into_iter().rev());
    controlled_swap(circ,&[(g,true),(cache,true)],&w1[256],mask,dirty);
    if j==0 {
        // C1 is held independently in cache, so only high-S is needed here.
        let ts=triples();
        for(r,t)in ts.iter().enumerate(){if t[2]!=0{continue;}
            let mut cs=vec![(g,true),(cache,true)];
            cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));
            cs.extend(sm.iter().map(|q|(q,false)));
            controlled_swap(circ,&cs,&w1[256],mask,dirty);
            controlled_swap(circ,&cs,&w1[255],mask,dirty);
        }
    }
    super::q795_t11::c1_flag(circ,rank,c,g,cache,dirty);
}

// Fuse two uses of the same dynamic source[k], k=257-(C+S): copy its
// top flag, then borrow it as a zero carry ONLY on its top-zero branch.
// Mask is zero on g at entry. Cache temporarily carries the prepared
// address, so write the top flag to mask until prepare has been undone.
// The return MUST be the literal inverse of this whole sequence: its
// controlled exchange changes the top bit before the flag is uncomputed.
fn top_flag_and_loan(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,mask:&QReg,carry:&QReg,w1:&[QReg],dirty:&[QReg],j:usize){
    assert!(dirty.iter().all(|q|q.id()!=mask.id()&&q.id()!=carry.id()));
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let(root,gather)=gather_top(circ,rank,c,cache,w1,dirty);
    circ.ccx(g,root,mask);
    controlled_swap(circ,&[(g,true),(mask,false)],root,carry,dirty);
    circ.b.ops.extend(gather.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],j:usize,n:usize){
    assert!(helpers.len()>=22);let owned=circ.b.next_qubit;
    super::q798_sign_erase::code(circ,p1,p2,sign,helpers,false);
    super::q798_handoffs::move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    move_top_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    let mask=&helpers[0];let dirty=&helpers[1..];
    let loan_start=circ.b.ops.len();mask_loan(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
    let loan=circ.b.ops[loan_start..].to_vec();
    let combined=super::metadata_muxlease::active("Q794_SIGN_COMBINED_TOP");
    let top_start=circ.b.ops.len();
    if combined {
        top_flag_and_loan(circ,rank,c,sm,p1,p2,mask,&dirty[0],w1,&dirty[1..],j);
    } else {
        super::q795_t11_top::top_flag(circ,rank,c,sm,p1,p2,mask,w1,dirty,j);
    }
    let top=circ.b.ops[top_start..].to_vec();
    circ.cswap(p1,p2,mask);circ.ccx(p1,p2,sign);
    super::q795_t11::park_c1(circ,p1,p2,sign,helpers);
    super::q794_sign_two_pass::emit(circ,rank,c,sm,p1,p2,mask,sign,w1,w2,dirty,j,n);
    super::q795_t11::park_c1(circ,p1,p2,sign,helpers);circ.cswap(p1,p2,mask);
    circ.b.ops.extend(top.into_iter().rev());
    // The C1/S0 selector is implemented as a product of transpositions;
    // return its loan by LITERAL inverse, not by assuming L is involutory.
    circ.b.ops.extend(loan.into_iter().rev());
    move_top_cargo(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    super::q798_handoffs::move_t11(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,j);
    super::q798_sign_erase::code(circ,p1,p2,sign,helpers,true);
    assert_eq!(circ.b.next_qubit,owned);
}

#[path="q794_sign_check.rs"]
pub mod verification;
