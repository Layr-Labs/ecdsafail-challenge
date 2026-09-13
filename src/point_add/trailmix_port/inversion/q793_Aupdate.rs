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
    let affine=std::env::var("Q794_AFFINE_ENDPOINT_EXCHANGE").ok().as_deref()==Some("1");
    let start=circ.b.ops.len();for &(left,right) in programs::SWAPS{
        // Same affine conjugation as the guarded path (see metadata_rank5),
        // with an empty control prefix because this map is already unguarded:
        // on guard0 the surrounding length conjugations are identity, so this
        // permutation and its literal inverse cancel whatever the rank holds.
        if affine {super::metadata_rank5::affine_transposition(circ,rank,&[],helpers,left,right);continue;}
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
                let general=super::metadata_muxlease::active("Q794_AFFINE_PREFIX_TRANSITION");
                if let Some(old)=cache_key.get().filter(|&old|super::metadata_muxlease::active("Q795_AUPDATE_PREFIX_TRANSITION")&&(general||(old^key).is_power_of_two())){
                    // Both producers are exact products, including off guard.
                    //
                    // A transition from `old` to `key` must toggle SM0 on both
                    // prefixes, i.e. produce the indicator of the two-element
                    // set {old,key}. When they differ in one bit that set is a
                    // cube -- drop that control and one product does both. For
                    // a general pair it is not, so conjugate it into one: with
                    // pivot `p` the lowest differing bit, `cx(p,i)` on every
                    // other differing bit `i` maps {old,key} onto a pair that
                    // differs at `p` alone, which IS a cube. One product, then
                    // the frame is undone. CNOT is unscored, so a distance-d
                    // transition costs what distance 1 used to.
                    //
                    // The emitted sequence must be a symmetric function of the
                    // UNORDERED pair, because the reverse sweep replays it with
                    // the roles exchanged. It is: `p` is symmetric, and for
                    // `i` in the frame the literal `key_i ^ key_p` equals
                    // `old_i ^ old_p` (both bits flip, so their XOR is fixed),
                    // while off the frame `key_i == old_i`. Deriving the pivot
                    // or the literals from `key` alone would break the reverse
                    // sweep as off-guard phase garbage, not as a mismatch.
                    let base=8-cache_bits;let d=old^key;let p=d.trailing_zeros()as usize;
                    let others:Vec<usize>=(0..cache_bits).filter(|&i|i!=p&&d>>i&1!=0).collect();
                    for &i in &others {circ.cx(boundary[base+p],boundary[base+i]);}
                    let cs:Vec<_>=(0..cache_bits).filter(|&i|i!=p)
                        .map(|i|(boundary[base+i],(key>>i&1!=0)^(others.contains(&i)&&key>>p&1!=0))).collect();
                    mixed_mcx(circ,&cs,scratch,helpers);
                    for &i in others.iter().rev() {circ.cx(boundary[base+p],boundary[base+i]);}
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

/// Numeric A8/C8 exit chart. The missing fifth rank rail is borrowed from P1,
/// which is zero under the independent exit guard after the caller toggles it.
pub(super) fn update_numeric(circ:&mut Circuit,aa:&[QReg],cc:&[QReg],sm:&[QReg],mask:&QReg,guard:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize){
    assert_eq!(aa.len(),8);assert_eq!(cc.len(),8);let rank:Vec<_>=[&cc[6],&cc[7],&aa[6],&aa[7],mask].into_iter().map(QReg::borrowed_alias).collect();
    let out:Vec<_>=aa.iter().collect();
    length_xor(circ,&rank,&cc[..6],sm,&out,w2,w1,guard,helpers,lo,hi,true);
    length_xor(circ,&rank,&cc[..6],sm,&out,w1,w2,guard,helpers,lo,hi,false);
}
