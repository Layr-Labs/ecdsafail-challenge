//! Rank5 transfer using a temporary four-bit (A_high,S_high) representation.
//! C_high0 frees rank[4] as conditional clean scratch; no extra qubits.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
#[path="metadata_transfer5_compact_programs.rs"] mod programs;

fn permutation(circ:&mut Circuit,word:&[&QReg],guard:&QReg,helpers:&[QReg],swaps:&[(usize,usize)]) {
    permutation_inner(circ,word,guard,helpers,swaps,None);
}
fn permutation_inner(circ:&mut Circuit,word:&[&QReg],guard:&QReg,helpers:&[QReg],swaps:&[(usize,usize)],scratch:Option<&[QReg]>) {
    for &(left,right) in swaps {
        if super::metadata_muxlease::active("Q794_TRANSFER_ACTIVE_AFFINE"){
            super::q794_affine_frames::swap(circ,word,guard,&[],helpers,left,right,scratch);continue;
        }
        assert_ne!(left,right);let mut value=left;let mut edges=Vec::new();
        for bit in 0..word.len(){if (left^right)>>bit&1!=0{edges.push((bit,value));value^=1<<bit;}}
        assert_eq!(value,right);let path=edges.clone();edges.extend(path[..path.len()-1].iter().rev().copied());
        for (bit,value) in edges {
            let mut cs=vec![(guard,true)];cs.extend((0..word.len()).filter(|&i|i!=bit).map(|i|(word[i],value>>i&1!=0)));
            if let Some(s)=scratch{exit_guarded_toggle(circ,guard,&cs[1..],word[bit],s,helpers);}else{mixed_mcx(circ,&cs,word[bit],helpers);}
        }
    }
}
// All four S bits are zero on the independent exit guard before and after
// each rank-permutation edge. The sole target action retains that guard.
fn exit_guarded_toggle(circ:&mut Circuit,guard:&QReg,cs:&[(&QReg,bool)],out:&QReg,scratch:&[QReg],helpers:&[QReg]) {
    assert!(cs.len()>=2);let n=(cs.len()-1).min(scratch.len());assert!(n>0);
    for &(q,v) in cs{if !v{circ.x(q);}}
    circ.ccx(cs[0].0,cs[1].0,&scratch[0]);
    for i in 2..=n{circ.ccx(&scratch[i-2],cs[i].0,&scratch[i-1]);}
    let action:Vec<_>=std::iter::once((guard,true)).chain(std::iter::once((&scratch[n-1],true))).chain(cs[n+1..].iter().map(|&(q,_)|(q,true))).collect();
    mixed_mcx(circ,&action,out,helpers);
    for i in (2..=n).rev(){circ.ccx(&scratch[i-2],cs[i].0,&scratch[i-1]);}
    circ.ccx(cs[0].0,cs[1].0,&scratch[0]);
    for &(q,v) in cs.iter().rev(){if !v{circ.x(q);}}
}
fn clean(circ:&mut Circuit,guard:&QReg,scratch:&QReg,helpers:&[QReg],controls:&[(&QReg,bool)],out:&QReg) {
    let others:Vec<_>=controls.iter().copied().filter(|(q,_)|q.id()!=guard.id()).collect();
    assert!(controls.iter().all(|(q,v)|q.id()!=guard.id()||*v));
    super::conditional_mcx::guarded(circ,guard,&others,out,scratch,false,&helpers[0]);
}
// Pure target-toggle extension for arbitrary scratch, exact conjunction when
// scratch is zero. Every intermediate lender restores, including off guard.
fn exit_clean_toggle(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,scratch:&[QReg]) {
    assert!((2..=5).contains(&cs.len()));assert!(scratch.len()>=cs.len()-2);
    for &(q,v) in cs{if !v{circ.x(q);}}
    if cs.len()==2{circ.ccx(cs[0].0,cs[1].0,out);}else{
        circ.ccx(cs[0].0,cs[1].0,&scratch[0]);
        for i in 2..cs.len()-1{circ.ccx(&scratch[i-2],cs[i].0,&scratch[i-1]);}
        circ.ccx(&scratch[cs.len()-3],cs[cs.len()-1].0,out);
        for i in (2..cs.len()-1).rev(){circ.ccx(&scratch[i-2],cs[i].0,&scratch[i-1]);}
        circ.ccx(cs[0].0,cs[1].0,&scratch[0]);
    }
    for &(q,v) in cs.iter().rev(){if !v{circ.x(q);}}
}
fn length_xor(circ:&mut Circuit,rank:&[QReg],a:&[QReg],source:&[QReg],out:&[&QReg],guard:&QReg,prefix:&[QReg],helpers:&[QReg],exit_cache:Option<(&[QReg],usize)>) {
    let chart=[&source[0],&source[1],&prefix[0],&prefix[1],&prefix[258],&prefix[257]];
    // Protect all four W2 chart inputs from this borrowed dirty prefix.
    assert!(helpers.len()>=20);
    let protected:Vec<_>=prefix.iter().enumerate().map(|(i,q)|match i{0=>helpers[0].borrowed_alias(),1=>helpers[1].borrowed_alias(),257=>helpers[2].borrowed_alias(),258=>helpers[3].borrowed_alias(),_=>q.borrowed_alias()}).collect();
    let prefix=&protected;let helpers=&helpers[4..];
    let mut boundary:Vec<_>=a.iter().collect();boundary.extend([&rank[0],&rank[1]]);let mask=&rank[4];
    let cache_key=std::cell::Cell::new(None);
    let cache_toggle=|circ:&mut Circuit,value:usize|{let(sm,bits)=exit_cache.unwrap();let cs:Vec<_>=boundary[8-bits..].iter().enumerate().map(|(i,&q)|(q,value>>i&1!=0)).collect();exit_clean_toggle(circ,&cs,&sm[0],&sm[1..]);};
    // On guard1 the unused bit starts0. On guard0 it can be arbitrary:
    // the prefix conjugation has root0 and is identity for either mask offset.
    let update=|circ:&mut Circuit,i:usize| {
        if !(2..=257).contains(&i){return;}
        let value=i-2;
        if let Some((sm,bits))=exit_cache{
            let key=value>>(8-bits);if cache_key.get()!=Some(key){if let Some(old)=cache_key.get(){cache_toggle(circ,old);}cache_toggle(circ,key);cache_key.set(Some(key));}
            let controls:Vec<_>=std::iter::once((&sm[0],true)).chain(boundary[..8-bits].iter().enumerate().map(|(b,&q)|(q,value>>b&1!=0))).collect();
            exit_clean_toggle(circ,&controls,mask,&sm[1..]);
        }else{
            let controls:Vec<_>=boundary.iter().enumerate().map(|(b,&q)|(q,value>>b&1!=0)).collect();
            mixed_mcx(circ,&controls,mask,helpers);
        }
    };
    let cell=|circ:&mut Circuit,i:usize| {
        let parent=if i==0{guard}else{&prefix[i-1]};circ.cx(parent,&prefix[i]);
        if i>0 {if i==258&&super::q796_parity::enabled(){mixed_mcx(circ,&[(parent,true),(mask,true)],&prefix[i],helpers);}else if i==257{super::q794_exit_low::xor_r1(circ,chart,&boundary,&[(parent,true),(mask,true)],&prefix[i],helpers);}else{mixed_mcx(circ,&[(parent,true),(&source[i],true),(mask,true)],&prefix[i],helpers);}}
    };
    let zero_map=|circ:&mut Circuit| {
        circ.x(mask);
        for i in (1..259).rev(){cell(circ,i);update(circ,i);}
        cell(circ,0);
        for i in 1..259{update(circ,i);cell(circ,i);}
        circ.x(mask);
    };
    let writes=|circ:&mut Circuit| {
        for i in 0..259{let delta=(259-i)^(258-i);for bit in 0..8{if delta>>bit&1!=0{circ.cx(&prefix[i],out[bit]);}}}
    };
    for bit in 0..8{if 259>>bit&1!=0{circ.cx(guard,out[bit]);}}
    writes(circ);zero_map(circ);writes(circ);zero_map(circ);
    if let Some(key)=cache_key.take(){cache_toggle(circ,key);}
}
fn shift_add(circ:&mut Circuit,rank:&[QReg],sm:&[QReg],word:&[&QReg],guard:&QReg,helpers:&[QReg],j:usize) {
    let start=circ.b.ops.len();let low=(4-j)%4;
    for i in 0..8 {
        if i<2&&low>>i&1==0{continue;}
        for k in (i..8).rev() {
            let mut cs=Vec::new();cs.extend(word[i..k].iter().map(|&q|(q,true)));
            if i>=2 {cs.push((if i<6{&sm[i-2]}else{&rank[i-4]},true));}
            clean(circ,guard,&rank[4],helpers,&cs,word[k]);
        }
    }
    circ.b.ops[start..].reverse();
}
pub(super) fn transfer(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],prefix:&[QReg],helpers:&[QReg],j:usize,inverse:bool) {
    transfer_inner(circ,rank,a,c,sm,p1,p2,guard,source,prefix,helpers,j,inverse,false);
}
/// Exit caller has restored all four S_mid cargo loans and proves S=0.
pub(super) fn transfer_exit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],prefix:&[QReg],helpers:&[QReg]) {
    transfer_inner(circ,rank,a,c,sm,p1,p2,guard,source,prefix,helpers,0,true,true);
}
fn transfer_inner(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],prefix:&[QReg],helpers:&[QReg],j:usize,inverse:bool,is_exit:bool) {
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);assert_eq!(source.len(),259);assert_eq!(prefix.len(),259);assert!(helpers.len()>=16);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(sm).chain(source).chain(prefix).chain(helpers).map(QReg::id).collect();ids.extend([p1.id(),p2.id(),guard.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]));
    let start=circ.b.ops.len();circ.cx(guard,p1);circ.cx(guard,p2);
    let mut word:Vec<_>=c.iter().collect();word.extend([p1,p2]);let mut high:Vec<_>=rank.iter().collect();
    let perm_scratch=if is_exit&&super::metadata_muxlease::active("Q795_EXIT_PERM_CLEAN"){Some(sm)}else{None};
    permutation_inner(circ,&high,guard,helpers,programs::UNPACK_SWAPS,perm_scratch);
    let cache_bits=if is_exit{std::env::var("Q795_EXIT_PREFIX").ok().map(|v|v.parse::<usize>().unwrap()).unwrap_or(0)}else{0};assert!(cache_bits==0||cache_bits==4||cache_bits==5);
    length_xor(circ,rank,a,source,&word,guard,prefix,helpers,if cache_bits==0{None}else{Some((sm,cache_bits))});
    shift_add(circ,rank,sm,&word,guard,helpers,j);
    high.extend([p1,p2]);permutation_inner(circ,&high,guard,helpers,programs::PACK_SWAPS,perm_scratch);
    circ.cx(guard,p2);circ.cx(guard,p1);
    if inverse{circ.b.ops[start..].reverse();}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
