//! Q794 Sign MAJ history with modulo4 virtual-low correction and exact endpoints.
//! Caller must use the OLD top_flag/park frame, NOT the fused top carry loan.
//! On guard: cache=mask=0 and source[k]=0, k=257-C-S in0..=257.
//! Offguard: arbitrary seed, cache, DATA and helpers are restored exactly.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::{mixed_mcx,above_cubes};

fn triples()->Vec<[usize;3]>{super::q794_rank_fold::triples()}
fn high(circ:&mut Circuit,rank:&[QReg],cache:&QReg,c:&[QReg],g:&QReg,root:&QReg,sign:&QReg,helpers:&[QReg],truth:Vec<bool>,cube:&[(usize,bool)]) {
    let(polarity,terms)=super::metadata_muxlease::swap_terms(truth,6);
    let inputs:Vec<_>=rank.iter().chain(std::iter::once(cache)).collect();
    for(i,&q)in inputs.iter().enumerate(){if polarity>>i&1!=0{circ.x(q);}}
    for &(b,v)in cube {if !v{circ.x(&c[b]);}}
    for m in terms {
        let mut cs=vec![(g,true),(root,true)];cs.extend(inputs.iter().enumerate().filter(|&(i,_)|m>>i&1!=0).map(|(_,&q)|(q,true)));cs.extend(cube.iter().map(|&(b,_)|(&c[b],true)));
        mixed_mcx(circ,&cs,sign,helpers);
    }
    for &(b,v)in cube.iter().rev(){if !v{circ.x(&c[b]);}}
    for(i,&q)in inputs.iter().enumerate().rev(){if polarity>>i&1!=0{circ.x(q);}}
}
/// Sign ^= g*root*[prepared C+S >= lower]. No persistent helper or new loan.
fn threshold(circ:&mut Circuit,rank:&[QReg],cache:&QReg,c:&[QReg],g:&QReg,root:&QReg,sign:&QReg,helpers:&[QReg],lower:usize) {
    assert!((1..=257).contains(&lower));let h=lower/64;let lo=lower%64;let ts=triples();
    if lo==0 {
        let truth=(0..64).map(|r|ts[r&31][1]+ts[r&31][2]+(r>>5)>=h).collect();
        high(circ,rank,cache,c,g,root,sign,helpers,truth,&[]);
    }else{
        let greater=(0..64).map(|r|ts[r&31][1]+ts[r&31][2]+(r>>5)>h).collect();
        high(circ,rank,cache,c,g,root,sign,helpers,greater,&[]);
        let equal:Vec<_>=(0..64).map(|r|ts[r&31][1]+ts[r&31][2]+(r>>5)==h).collect();
        for cube in above_cubes(6,lo-1){high(circ,rank,cache,c,g,root,sign,helpers,equal.clone(),&cube);}
    }
}
fn gather<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],cache:&QReg,seed:&'a QReg,source:&'a[QReg],helpers:&[QReg],n:usize)->(&'a QReg,Vec<crate::circuit::Op>) {
    let start=circ.b.ops.len();let lower=258-n;let mut nodes=vec![None;512];
    // Only unique history rails. The final carry source[n-1] is NOT a leaf.
    for v in lower..=257 {nodes[v]=Some(if v==257{seed}else{&source[256-v]});}
    let ts=triples();
    for level in 0..9 {
        let mut next=Vec::new();
        for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
            (Some(left),Some(right))=>{
                if level<6{circ.cswap(&c[level],left,right);}else{
                    let inputs:Vec<_>=rank.iter().chain(std::iter::once(cache)).collect();
                    let truth=(0..64).map(|r|((ts[r&31][1]+ts[r&31][2]+(r>>5)>>(level-6))&1)!=0).collect();
                    if super::metadata_muxlease::active("Q794_SIGN_SUM_MAJ") {super::q794_sign_fold::sum_swaps::swap(circ,rank,cache,level-6,left,right,helpers);}
                    else {super::metadata_muxlease::truth_swap(circ,&inputs,truth,left,right,helpers);}
                }Some(left)
            },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
        });}nodes=next;
    }
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,seed:&QReg,sign:&QReg,source:&[QReg],target:&[QReg],helpers:&[QReg],j:usize,n:usize) {
    assert!((1..=258).contains(&n));assert!(helpers.len()>=17);assert_eq!(rank.len(),5);assert_eq!(c.len(),6);assert_eq!(sm.len(),4);
    let n=n.min(257);assert!(source.len()>=257&&target.len()>=257);
    let mut ids:Vec<_>=rank.iter().chain(c).chain(sm).chain(source.iter().take(257)).chain(target).chain(helpers).map(QReg::id).collect();ids.extend([g.id(),cache.id(),seed.id(),sign.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"MAJ history aliases");
    let start=circ.b.ops.len();for q in &target[..n]{circ.x(q);}
    for i in 0..n {
        let prev=if i==0{seed}else{&source[i-1]};
        circ.cx(&source[i],&target[i]);circ.cx(&source[i],prev);circ.ccx(prev,&target[i],&source[i]);
        if i==1 {virtual_low(circ,rank,c,sm,g,seed,source,target,helpers,j);}
    }
    let maj=circ.b.ops[start..].to_vec();
    // Metadata, guard and Sign are disjoint from MAJ. Prepare/gather excludes
    // the seed and every DATA rail from its arbitrary dirty lender list.
    super::q794_sign_fold::preparation::emit(circ,c,sm,g,Some(cache),helpers,j,false);
    let(root,route)=gather(circ,rank,c,cache,seed,source,helpers,n);let final_carry=&source[n-1];assert_ne!(root.id(),final_carry.id());
    // At k<n, history[k]=carry_k XOR original source[k]=carry_k. At k>=n
    // the unique final carry is correct, even when source[k] is a passenger.
    circ.ccx(g,final_carry,sign);circ.cx(final_carry,root);
    threshold(circ,rank,cache,c,g,root,sign,helpers,258-n);
    // C1/S0 loans a mask passenger into source255, inside k=256. The
    // semantic comparator is false (u=p,v=1,r=0,t<p/2), so cancel BOTH
    // terms of the actual min(k,n) center, not merely the final carry.
    if j==0 {
        for(r,t)in triples().iter().enumerate(){if t[1]!=0||t[2]!=0{continue;}
            let mut cs=vec![(g,true)];cs.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));
            cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend(sm.iter().map(|q|(q,false)));
            let mut final_term=cs.clone();final_term.push((final_carry,true));mixed_mcx(circ,&final_term,sign,helpers);
            if n==257{cs.push((root,true));mixed_mcx(circ,&cs,sign,helpers);}
        }
    }
    circ.cx(final_carry,root);circ.b.ops.extend(route.into_iter().rev());
    super::q794_sign_fold::preparation::emit(circ,c,sm,g,Some(cache),helpers,j,true);
    circ.b.ops.extend(maj.into_iter().rev());
}

// At i1 in the MAJ basis: seed=t0, source0=carry1 XOR t1,
// source1=carry2, target0=NOT(b0) XOR t0, target1=NOT(b1) XOR t1.
// On the even-t0 correction domain carry1=0, so source0 is exactly t1;
// the two complement offsets in target0 XOR target1 cancel. This is the
// upstream virtual-low correction conjugated into the MAJ basis, not a
// materialized residual bit. S0 and C in1..255 imply k>=2, so no mask rail.
fn virtual_low(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,seed:&QReg,source:&[QReg],target:&[QReg],helpers:&[QReg],j:usize){
    if j!=0{return;}
    let ts=triples();
    for cancel_c1 in [false,true]{
        let mut anf:Vec<_>=ts.iter().map(|t|t[2]==0&&(!cancel_c1||t[1]==0)).collect();
        for bit in 0..5{for m in 0..32{if m>>bit&1!=0{anf[m]^=anf[m^(1<<bit)];}}}
        for(m,on)in anf.into_iter().enumerate(){if !on{continue;}
            let mut cs=vec![(g,true),(seed,false),(&source[0],true)];cs.extend(sm.iter().map(|q|(q,false)));
            cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],true)));
            if cancel_c1{
                cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));cs.push((&target[257],true));mixed_mcx(circ,&cs,&source[1],helpers);
            }else{
                circ.cx(&target[1],&target[0]);circ.cx(&target[257],&target[0]);
                cs.push((&target[0],true));mixed_mcx(circ,&cs,&source[1],helpers);
                circ.cx(&target[257],&target[0]);circ.cx(&target[1],&target[0]);
            }
        }
    }
}

#[cfg(any())]
pub mod verification {
    use super::*;use crate::{circuit::OperationType,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
    pub fn run(){
        let ts=triples();let mut widths=vec![1,2,3,64,65,66,128,129,256,257,258];widths.extend(super::super::shared_step::SCHEDULE_SUPPORTS.iter().map(|&(_,t)|(t+1).min(258)));widths.sort_unstable();widths.dedup();
        let(mut total,mut active,mut empty,mut truncated)=(0usize,0usize,0usize,0usize);
        for n in widths {for j in 0..4 {
            let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("maj.rank",5);let c=circ.alloc_qreg_bits("maj.c",6);let sm=circ.alloc_qreg_bits("maj.sm",4);let g=circ.alloc_qreg("maj.g");let cache=circ.alloc_qreg("maj.cache");let seed=circ.alloc_qreg("maj.seed");let sign=circ.alloc_qreg("maj.sign");let source=circ.alloc_qreg_bits("maj.source",259);let target=circ.alloc_qreg_bits("maj.target",259);let help=circ.alloc_qreg_bits("maj.dirty",22);let owned=circ.b.next_qubit;
            emit(&mut circ,&rank,&c,&sm,&g,&cache,&seed,&sign,&source,&target,&help,j,n);let candidate=circ.b.ops.split_off(0);
            super::super::q795_sign_two_pass::emit(&mut circ,&rank,&c,&sm,&g,&cache,&seed,&sign,&source,&target,&help,j,n);let old=circ.b.ops.split_off(0);assert_eq!(owned,circ.b.next_qubit);
            for ops in [&candidate,&old]{for op in ops{let hole=source[258].id()as u64;assert!(op.q_target.0!=hole&&op.q_control1.0!=hole&&op.q_control2.0!=hole);assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}}
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);
            for pattern in 0..2 {for batch in 0..1024 {
                let mut state=0x731aeb9u64^batch as u64^((pattern as u64)<<32);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut state)).collect();let mut expected=before.clone();
                for lane in 0..64 {
                    let x=batch*64+lane;let r=x&31;let cl=x>>5&63;let sl=x>>11&15;let cv=64*ts[r][1]+cl;let sv=64*ts[r][2]+4*sl+(4-j)%4;let on=x>>15&1!=0&&cv>0&&cv<=255&&cv+sv<=257;
                    for w in [&mut before,&mut expected]{for i in 0..5{put(w,&rank[i],lane,r>>i&1!=0);}for i in 0..6{put(w,&c[i],lane,cl>>i&1!=0);}for i in 0..4{put(w,&sm[i],lane,sl>>i&1!=0);}put(w,&g,lane,on);put(w,&sign,lane,pattern!=0);if on{put(w,&cache,lane,false);put(w,&seed,lane,false);put(w,&source[257-cv-sv],lane,false);}}
                    if on {
                        let k=257-cv-sv;let mut greater=false;for i in 0..k.min(n){let a=before[source[i].id()as usize]>>lane&1!=0;let b=before[target[i].id()as usize]>>lane&1!=0;if a!=b{greater=a;}}
                        if greater{expected[sign.id()as usize]^=1u64<<lane;}active+=1;if k==0{empty+=1;}if k>=n{truncated+=1;}
                    }
                }
                sim.qubits.copy_from_slice(&before);sim.apply_iter(old.iter());assert_eq!(sim.qubits,expected,"old MAJ reference n{n} j{j} batch{batch}");assert_eq!(sim.phase,0);
                sim.qubits.copy_from_slice(&before);sim.apply_iter(candidate.iter());assert_eq!(sim.qubits,expected,"new MAJ n{n} j{j} batch{batch}");assert_eq!(sim.phase,0);sim.apply_iter(candidate.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
            }}
            eprintln!("SIGN_MAJ_CASE n={n} j={j} oldT={} newT={} ops={} PASS",old.iter().filter(|o|o.kind==OperationType::CCX).count(),candidate.iter().filter(|o|o.kind==OperationType::CCX).count(),candidate.len());
        }}
        eprintln!("SIGN_MAJ_PASS lanes={total} active={active} empty={empty} truncated={truncated}; actual old/scalar/new match, both Sign inputs, arbitrary offguard DATA/seed/cache/lenders, inverse/phase/noallocation/hole");
    }
}
