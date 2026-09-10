//! After the cycle word swap, change A_old to A_new using retained C and S0.
//! Guard requires both coefficient lengths to be truthful and inside support.
//! Work1 holds the new coefficient, Work2 the old; prefix length is259-C.
//! All source words, retained C, S and helpers restore. No extra allocation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_Aupdate5_programs.rs"] mod programs;

fn permute(circ:&mut Circuit,rank:&[QReg],guard:&QReg,helpers:&[QReg],inverse:bool) {
    let start=circ.b.ops.len();for &(a,b) in programs::SWAPS {super::metadata_rank5::basis_swap(circ,rank,guard,&[],helpers,a,b);}
    if inverse{circ.b.ops[start..].reverse();}
}
fn permute_for_update(circ:&mut Circuit,rank:&[QReg],guard:&QReg,helpers:&[QReg],inverse:bool) {
    if !super::metadata_muxlease::active("Q795_AUPDATE_PERM_UNGUARDED"){permute(circ,rank,guard,helpers,inverse);return;}
    // These two maps surround guard-rooted length conjugations. On guard0
    // both length maps are identity for arbitrary transformed rank metadata,
    // so this raw permutation and its literal inverse cancel exactly.
    let start=circ.b.ops.len();for &(left,right) in programs::SWAPS{
        let mut value=left;let mut edges=Vec::new();for bit in 0..5{if (left^right)>>bit&1!=0{edges.push((bit,value));value^=1<<bit;}}
        assert_eq!(value,right);let path=edges.clone();edges.extend(path[..path.len()-1].iter().rev().copied());
        for(bit,value)in edges{let cs:Vec<_>=(0..5).filter(|&i|i!=bit).map(|i|(&rank[i],value>>i&1!=0)).collect();mixed_mcx(circ,&cs,&rank[bit],helpers);}
    }
    if inverse{circ.b.ops[start..].reverse();}
}
fn length_xor(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],out:&[&QReg],source:&[QReg],prefix:&[QReg],guard:&QReg,helpers:&[QReg],lo:usize,hi:usize,decode_u:bool) {
    let chart=[&prefix[0],&prefix[1],&prefix[2],&source[0],&source[1],&source[2],&source[258],&source[257],&source[256]];
    // These are arbitrary dirty replacements, not clean allocations. The
    // prefix conjugation restores them; it must not overwrite its chart.
    let protected:Vec<_>=prefix.iter().enumerate().map(|(i,q)|if decode_u&&i<3{helpers[i].borrowed_alias()}else{q.borrowed_alias()}).collect();
    let prefix=&protected;
    let helpers=if decode_u{assert!(helpers.len()>=19);&helpers[3..]}else{helpers};
    let mut boundary:Vec<_>=c.iter().collect();boundary.extend([&rank[0],&rank[1]]);let mask=&rank[4];let scratch=&sm[0];let n=hi-lo;
    let cache_bits=std::env::var("Q795_AUPDATE_PREFIX").ok().map(|v|v.parse::<usize>().unwrap()).unwrap_or(0);assert!(cache_bits==0||(4..=6).contains(&cache_bits));
    let cache_key=std::cell::Cell::new(None);
    let cache_toggle=|circ:&mut Circuit,value:usize|{let cs:Vec<_>=boundary[8-cache_bits..].iter().enumerate().map(|(i,&q)|(q,value>>i&1!=0)).collect();mixed_mcx(circ,&cs,scratch,helpers);};
    let update=|circ:&mut Circuit,i:usize| {
        let value=259-hi+i;if value>255{return;}
        if cache_bits==0{
            let cs:Vec<_>=boundary.iter().enumerate().map(|(b,&q)|(q,value>>b&1!=0)).collect();
            super::conditional_mcx::guarded(circ,guard,&cs,mask,scratch,false,&helpers[0]);
        }else{
            // SM0 was the existing conditional-clean update scratch. Cache
            // the static C-boundary high prefix there through both zero maps.
            // Off guard the conjugation root is zero: arbitrary cache/mask
            // offsets cancel, and the final cache teardown restores SM0.
            let key=value>>(8-cache_bits);if cache_key.get()!=Some(key){
                if let Some(old)=cache_key.get().filter(|&old|super::metadata_muxlease::active("Q795_AUPDATE_PREFIX_TRANSITION")&&(old^key).is_power_of_two()){
                    // Both producers are exact products, including off guard.
                    let omit=(old^key).trailing_zeros()as usize;let cs:Vec<_>=boundary[8-cache_bits..].iter().enumerate().filter(|(i,_)|*i!=omit).map(|(i,&q)|(q,key>>i&1!=0)).collect();mixed_mcx(circ,&cs,scratch,helpers);
                }else{if let Some(old)=cache_key.get(){cache_toggle(circ,old);}cache_toggle(circ,key);}
                cache_key.set(Some(key));
            }
            let cs:Vec<_>=std::iter::once((scratch,true)).chain(boundary[..8-cache_bits].iter().enumerate().map(|(b,&q)|(q,value>>b&1!=0))).collect();
            mixed_mcx(circ,&cs,mask,helpers);
        }
    };
    let cell=|circ:&mut Circuit,i:usize| {
        let parent=if i==0{guard}else{&prefix[i-1]};circ.cx(parent,&prefix[i]);
        if hi-1-i==0&&super::q796_parity::enabled(){mixed_mcx(circ,&[(parent,true),(mask,true)],&prefix[i],helpers);}else if (1..=2).contains(&(hi-1-i))&&decode_u{super::q793_exit_low::xor_u(circ,chart,hi-1-i,&[(parent,true),(mask,true)],&prefix[i],helpers);}else{mixed_mcx(circ,&[(parent,true),(&source[hi-1-i],true),(mask,true)],&prefix[i],helpers);}
    };
    // Selected coefficient top lies in [lo,hi), so C<=258-lo on guard1.
    // Initialize eligibility at the high reverse index; both sweeps restore
    // arbitrary mask offsets on guard0, where the conjugation root is zero.
    let zero_map=|circ:&mut Circuit| {
        circ.x(mask);for i in (1..n).rev(){cell(circ,i);update(circ,i);}cell(circ,0);
        for i in 1..n{update(circ,i);cell(circ,i);}circ.x(mask);
    };
    let writes=|circ:&mut Circuit| {
        for i in 0..n {let value=hi-1-i;let next=if i+1<n{value-1}else{255};let delta=value^next;
            for bit in 0..8 {if delta>>bit&1!=0{circ.cx(&prefix[i],out[bit]);}}
        }
    };
    for bit in 0..8 {if (hi-1)>>bit&1!=0{circ.cx(guard,out[bit]);}}
    writes(circ);zero_map(circ);writes(circ);zero_map(circ);
    if let Some(key)=cache_key.take(){cache_toggle(circ,key);}
}
pub(super) fn update(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],guard:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize,inverse:bool) {
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert!(helpers.len()>=16);assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);assert!(lo<hi&&hi<=256);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(w1).chain(w2).chain(helpers).map(QReg::id).collect();ids.push(guard.id());ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
    let start=circ.b.ops.len();permute_for_update(circ,rank,guard,helpers,false);
    let mut out:Vec<_>=a.iter().collect();out.extend([&rank[2],&rank[3]]);
    length_xor(circ,rank,c,sm,&out,w2,w1,guard,helpers,lo,hi,true);
    length_xor(circ,rank,c,sm,&out,w1,w2,guard,helpers,lo,hi,false);
    permute_for_update(circ,rank,guard,helpers,true);
    if inverse{circ.b.ops[start..].reverse();}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
