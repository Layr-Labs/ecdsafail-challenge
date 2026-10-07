//! Exact folded-control lowering of read-only metadata routing templates.
//! Gather replacements preserve the selected leaf on the caller's domain;
//! surrounding literal inverses restore arbitrary data and all dirty lenders.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{Op,OperationType as K,NO_QUBIT};
#[derive(Clone)]enum Meaning{Gate(Vec<(usize,bool)>,usize),Gather{word:Vec<usize>,offset:usize,root:usize,support:(usize,usize)}}
#[derive(Clone)]struct Macro{ops:Vec<Op>,meaning:Meaning}
thread_local!{static ACTIVE:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};static BANK:std::cell::RefCell<Vec<Macro>>=const{std::cell::RefCell::new(Vec::new())};}
pub(super) fn active()->bool{ACTIVE.with(|x|x.get())}
pub(super) fn begin_gate(c:&Circuit,cs:&[(&QReg,bool)],out:&QReg)->Option<usize>{(active()&&out.id()>=21&&cs.iter().any(|(q,_)|q.id()<21)).then_some(c.b.ops.len())}
pub(super) fn end_gate(c:&Circuit,at:Option<usize>,cs:&[(&QReg,bool)],out:&QReg){if let Some(at)=at{BANK.with(|b|b.borrow_mut().push(Macro{ops:c.b.ops[at..].to_vec(),meaning:Meaning::Gate(cs.iter().map(|(q,v)|(q.id()as usize,*v)).collect(),out.id()as usize)}));}}
pub(super) fn gather(c:&Circuit,ops:&[Op],word:&[QReg],offset:usize,root:&QReg){if active(){BANK.with(|b|b.borrow_mut().push(Macro{ops:ops.to_vec(),meaning:Meaning::Gather{word:word.iter().map(|q|q.id()as usize).collect(),offset,root:root.id()as usize,support:c.q797_a_support.unwrap_or((0,256))}}));}}
fn gate(c:&mut Circuit,q:&[QReg],cs:&[(usize,bool)],target:usize,polarity:usize,pool:&[usize]){
    assert!(target>=21);let mut mask=0usize;let mut value=0usize;let mut external=Vec::new();let mut seen=std::collections::BTreeMap::new();
    for &(id,b)in cs{if let Some(old)=seen.insert(id,b){if old!=b{return;}}if id<21{mask|=1<<id;if b^(polarity>>id&1!=0){value|=1<<id;}}else if !external.iter().any(|(x,_)|*x==id){external.push((id,b));}}
    let d:Vec<_>=pool.iter().copied().filter(|&id|id!=target&&!external.iter().any(|&(x,_)|id==x)).map(|id|q[id-1].borrowed_alias()).collect();let prefix:Vec<_>=external.iter().map(|&(id,b)|(&q[id-1],b)).collect();
    if mask==0{super::length_recompute::mixed_mcx(c,&prefix,&q[target-1],&d);}else{assert!(d.len()>=20,"folded control lender count {}",d.len());super::q792_fold20_predicate_r01::toggle(c,&q[..20],mask,value,&prefix,&q[target-1],&d);}
}
fn gather_lower(c:&mut Circuit,q:&[QReg],word:&[usize],offset:usize,root:usize,support:(usize,usize),pool:&[usize]){
    assert!(word.len()>=256);let mut bank:Vec<Option<usize>>=vec![None;256];let mut used=std::collections::BTreeSet::new();
    for v in 0..256{if v+offset<word.len()&&((support.0..support.1).contains(&v)||v==255)&&!(offset==3&&v==255){let id=word[v+offset];bank[v]=Some(id);assert!(used.insert(id));}}
    let free:Vec<_>=word.iter().copied().filter(|v|!used.contains(v)).collect();let mut free=free.into_iter();for x in &mut bank{if x.is_none(){*x=Some(free.next().unwrap());}}
    let bank:Vec<_>=bank.into_iter().map(|id|&q[id.unwrap()-1]).collect();let d:Vec<_>=pool.iter().map(|&id|q[id-1].borrowed_alias()).collect();let addr=&d[..8];let rest=&d[8..];
    super::q792_fold20_address_r01::translation(c,addr,&bank);super::q792_fold20_address_r01::read_a(c,&q[..20],addr,rest);super::q792_fold20_address_r01::translation(c,addr,&bank);super::q792_fold20_address_r01::read_a(c,&q[..20],addr,rest);
    let root=&q[root-1];if root.id()!=bank[0].id(){c.cx(root,bank[0]);c.cx(bank[0],root);c.cx(root,bank[0]);}
}
fn key(op:&Op)->(u8,u64,u64,u64){(op.kind as u8,op.q_target.0,op.q_control1.0,op.q_control2.0)}
fn lower_legacy(source:&[Op],n:usize,pool:&[usize])->Vec<Op>{
    let macros=BANK.with(|b|b.borrow().clone());let mut index=std::collections::BTreeMap::new();
    for m in macros{if m.ops.is_empty(){continue;}for inverse in [false,true]{let mut m=m.clone();if inverse{m.ops.reverse();}index.entry(key(&m.ops[0])).or_insert_with(Vec::new).push((m,inverse));}}
    for values in index.values_mut(){values.sort_by_key(|(m,_)|std::cmp::Reverse(m.ops.len()));values.dedup_by(|(a,ai),(b,bi)|ai==bi&&a.ops==b.ops);}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let q=c.alloc_qreg_bits("fold20.passive.template",n-1);let mut polarity=0usize;let mut at=0;let mut matched=0;let mut gathers=0;
    while at<source.len(){let op=&source[at];if let Some((m,inverse))=index.get(&key(op)).and_then(|xs|xs.iter().find(|(m,_)|source[at..].starts_with(&m.ops))){
        let start=c.b.ops.len();match &m.meaning{Meaning::Gate(cs,target)=>gate(&mut c,&q,cs,*target,polarity,pool),Meaning::Gather{word,offset,root,support}=>{assert_eq!(polarity,0);gather_lower(&mut c,&q,word,*offset,*root,*support,pool);gathers+=1;}}
        if *inverse{c.b.ops[start..].reverse();}at+=m.ops.len();matched+=1;continue;
    }
    assert!(matches!(op.kind,K::X|K::CX|K::CCX));let target=op.q_target.0 as usize;let controls:Vec<_>=[op.q_control1,op.q_control2].into_iter().filter(|&v|v!=NO_QUBIT).map(|v|(v.0 as usize,true)).collect();
    if target<21{assert!(op.kind==K::X,"passive template changed metadata at {at}: {op:?}");polarity^=1<<target;}
    else{gate(&mut c,&q,&controls,target,polarity,pool);}at+=1;
    }
    assert_eq!(polarity,0);let mut ops=c.into_builder().ops;super::shared_optimize::cancel_nct(&mut ops,2048,8);super::shared_optimize::cancel_nct_live(&mut ops,2048);eprintln!("FOLD20_PASSIVE_LOWER old={} new={} macros={matched} gathers={gathers}",source.len(),ops.len());ops
}
/// Each run consists only of XOR oracles into one common target. It is cut
/// at every other target and gather; no run moves a predicate across a data
/// dependency. Cache is absent from every run control/target and every lender.
fn bank(c:&mut Circuit,q:&[QReg],run:&[(Vec<(usize,bool)>,usize,usize)],pool:&[usize]){
    if run.is_empty(){return;}assert!(run.iter().all(|(cs,target,_)|cs.iter().all(|(id,_)|id!=target)));let at=c.b.ops.len();
    for (cs,target,polarity)in run{gate(c,q,cs,*target,*polarity,pool);}let old=c.b.ops.split_off(at);
    let cache=pool.iter().copied().find(|id|run.iter().all(|(cs,target,_)|id!=target&&cs.iter().all(|(x,_)|id!=x)));
    let Some(cache)=cache else{c.b.ops.extend(old);return;};
    let rest_pool:Vec<_>=pool.iter().copied().filter(|&id|id!=cache).collect();
    let requests:Vec<_>=run.iter().map(|(cs,target,polarity)|{
        let mut mask=0;let mut value=0;let mut ext=Vec::new();let mut seen=std::collections::BTreeMap::new();let mut valid=true;
        for &(id,b)in cs{if let Some(old)=seen.insert(id,b){if old!=b{valid=false;}}if id<21{mask|=1<<id;if b^(*polarity>>id&1!=0){value|=1<<id;}}else if !ext.iter().any(|(x,_)|*x==id){ext.push((id,b));}}
        (mask,value,ext,*target,valid)
    }).collect();
    if requests.iter().filter(|(mask,_,_,_,valid)|*mask!=0&&*valid).count()<2{c.b.ops.extend(old);return;}
    // Exact rank-cube XOR aggregation: same low literals and external
    // controls give one rank truth on ALL 32 codes, including invalid-chart
    // extensions inherited by the original predicate tables.
    let mut groups=std::collections::BTreeMap::<(usize,usize,Vec<(usize,bool)>,usize),u32>::new();
    let mut plain=Vec::new();
    for (mask,value,mut ext,target,valid)in requests{
        if !valid{continue;}ext.sort();if mask==0{plain.push((ext,target));continue;}
        let truth=(0..32).filter(|&r|r&(mask&31)==value&31).fold(0u32,|v,r|v|(1u32<<r));
        *groups.entry((mask>>5,value>>5,ext,target)).or_default()^=truth;
    }
    for (ext,target)in plain{let d:Vec<_>=rest_pool.iter().copied().filter(|&id|id!=target&&ext.iter().all(|&(x,_)|id!=x)).map(|id|q[id-1].borrowed_alias()).collect();let prefix:Vec<_>=ext.iter().map(|&(id,b)|(&q[id-1],b)).collect();super::length_recompute::mixed_mcx(c,&prefix,&q[target-1],&d);}
    let needs_branch=groups.iter().any(|((lm,lv,_,_),&truth)|truth!=0&&super::q792_fold20_predicate_r01::branch_needed(*lm,*lv));
    for reflected in [false,true,true]{if reflected&&!needs_branch{continue;}
        for (&(lm,lv,ref ext,target),&truth)in &groups{
            if truth==0{continue;}let d:Vec<_>=rest_pool.iter().copied().filter(|&id|id!=target&&ext.iter().all(|&(x,_)|id!=x)).map(|id|q[id-1].borrowed_alias()).collect();let prefix:Vec<_>=ext.iter().map(|&(id,b)|(&q[id-1],b)).collect();
            assert!(d.len()>=19);super::q792_fold20_predicate_r01::cached_rank_part(c,&q[..20],truth,lm,lv,&prefix,&q[target-1],&d,&q[cache-1],reflected);
        }
        if reflected{let d:Vec<_>=rest_pool.iter().map(|&id|q[id-1].borrowed_alias()).collect();super::q792_fold20_predicate_r01::cached_branch(c,&q[..20],&q[cache-1],&d);}
    }
    let new=c.b.ops.split_off(at);let cost=|ops:&[Op]|(ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len());
    if cost(&new)<cost(&old){eprintln!("FOLD20_PASSIVE_BANK gates={} cache={cache} old_T={} new_T={} old_N={} new_N={}",run.len(),cost(&old).0,cost(&new).0,old.len(),new.len());c.b.ops.extend(new);}else{c.b.ops.extend(old);}
}
fn lower(source:&[Op],n:usize,pool:&[usize])->Vec<Op>{
    let macros=BANK.with(|b|b.borrow().clone());let mut index=std::collections::BTreeMap::new();
    for m in macros{if m.ops.is_empty(){continue;}for inverse in [false,true]{let mut m=m.clone();if inverse{m.ops.reverse();}index.entry(key(&m.ops[0])).or_insert_with(Vec::new).push((m,inverse));}}
    for values in index.values_mut(){values.sort_by_key(|(m,_)|std::cmp::Reverse(m.ops.len()));values.dedup_by(|(a,ai),(b,bi)|ai==bi&&a.ops==b.ops);}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let q=c.alloc_qreg_bits("fold20.passive.template",n-1);let mut polarity=0;let mut at=0;let mut run=Vec::new();let mut matched=0;let mut gathers=0;
    while at<source.len(){let op=&source[at];if let Some((m,inverse))=index.get(&key(op)).and_then(|xs|xs.iter().find(|(m,_)|source[at..].starts_with(&m.ops))){
        match &m.meaning{Meaning::Gate(cs,target)=>{if run.last().map_or(false,|(_,t,_)|t!=target){bank(&mut c,&q,&run,pool);run.clear();}run.push((cs.clone(),*target,polarity));},Meaning::Gather{word,offset,root,support}=>{bank(&mut c,&q,&run,pool);run.clear();assert_eq!(polarity,0);let start=c.b.ops.len();gather_lower(&mut c,&q,word,*offset,*root,*support,pool);if *inverse{c.b.ops[start..].reverse();}gathers+=1;}}
        at+=m.ops.len();matched+=1;continue;
    }
    assert!(matches!(op.kind,K::X|K::CX|K::CCX));let target=op.q_target.0 as usize;let controls:Vec<_>=[op.q_control1,op.q_control2].into_iter().filter(|&v|v!=NO_QUBIT).map(|v|(v.0 as usize,true)).collect();
    if target<21{assert!(op.kind==K::X,"passive metadata mutation {op:?}");polarity^=1<<target;}
    else{if run.last().map_or(false,|(_,t,_)|*t!=target){bank(&mut c,&q,&run,pool);run.clear();}run.push((controls,target,polarity));}at+=1;
    }
    bank(&mut c,&q,&run,pool);assert_eq!(polarity,0);let mut ops=c.into_builder().ops;super::shared_optimize::cancel_nct(&mut ops,2048,8);super::shared_optimize::cancel_nct_live(&mut ops,2048);eprintln!("FOLD20_PASSIVE_LOWER old={} new={} macros={matched} gathers={gathers}",source.len(),ops.len());ops
}
pub(super) fn emit(circ:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,it:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],j:usize,kind:usize){
    assert_eq!(m.len(),20);assert_eq!(h.len(),23);let mut temp=Circuit::new();temp.b.count_only=false;temp.b.fiat_hash=None;temp.q797_a_support=circ.q797_a_support;
    let rank=temp.alloc_qreg_bits("r",5);let a=temp.alloc_qreg_bits("a",6);let c=temp.alloc_qreg_bits("c",6);let sm=temp.alloc_qreg_bits("sm",4);let p1v=temp.alloc_qreg("p1");let p2v=temp.alloc_qreg("p2");let itv=temp.alloc_qreg("it");let w1v=temp.alloc_qreg_bits("w1",259);let w2v=temp.alloc_qreg_bits("w2",259);let hv=temp.alloc_qreg_bits("h",23);let n=temp.b.next_qubit as usize;
    BANK.with(|b|b.borrow_mut().clear());ACTIVE.with(|x|x.set(true));
    super::q793_step_r03::passive20_template(&mut temp,&rank,&a,&c,&sm,&p1v,&p2v,&itv,&w1v,&w2v,&hv,j,kind);
    ACTIVE.with(|x|x.set(false));let pool:Vec<_>=hv.iter().chain(std::iter::once(&itv)).map(|q|q.id()as usize).collect();let ops=lower(&temp.into_builder().ops,n,&pool);
    let refs:Vec<_>=m.iter().chain([p1,p2,it]).chain(w1).chain(w2).chain(h).collect();assert_eq!(refs.len(),n-1);
    for mut op in ops{for wire in [&mut op.q_target,&mut op.q_control1,&mut op.q_control2]{if *wire!=NO_QUBIT{let id=refs[wire.0 as usize].id();assert_ne!(id,u32::MAX,"passive selected absent rail");wire.0=id as u64;}}circ.b.ops.push(op);}
}

pub(super) mod verification{
    use super::*;
    use crate::sim::Simulator;
    use sha3::{Shake256,digest::{Update,ExtendableOutput,XofReader}};
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn decoded(code:usize)->Option<usize>{
        const LOW:[usize;10]=[0,1,2,4,5,8,13,14,17,23];const EDGE:[usize;10]=[3,6,9,11,15,18,20,24,26,29];const PEAK:[usize;12]=[7,10,12,16,19,21,22,25,27,28,30,31];
        let tag=code&15;let low=code>>4;let a=low&63;let cl=low>>6&63;let sm=low>>12&15;
        let(r,a,cl,sm)=if tag<10{(LOW[tag],a,cl,sm)}else if tag<15{let side=usize::from((a>>4)+(cl>>4)+(sm>>2)>=5);let v=low^if side!=0{65535}else{0};(EDGE[2*(tag-10)+side],v&63,v>>6&63,v>>12&15)}else if a&2!=0{(29,63,cl,sm&3)}else{if a>>2>=12{return None;}(PEAK[a>>2],a&1,cl,sm)};
        Some(r|a<<5|cl<<11|sm<<17)
    }
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn hash(ops:&[Op])->String{let mut h=Shake256::default();for op in ops{h.update(&[op.kind as u8]);for q in [op.q_target,op.q_control1,op.q_control2]{h.update(&q.0.to_le_bytes());}}let mut b=[0u8;32];h.finalize_xof().read(&mut b);b.iter().map(|v|format!("{v:02x}")).collect()}
    pub fn run(){
        let mut seen:Vec<(Vec<Op>,Vec<Op>,Vec<Op>)>=Vec::new();let mut lanes=0u64;let mut valid_lanes=0u64;let mut unique=0;
        for kind in 4..=6{for j in 0..4{
            let mut original=Circuit::new();original.b.count_only=false;original.b.fiat_hash=None;let rank=original.alloc_qreg_bits("rank",5);let a=original.alloc_qreg_bits("A",6);let cl=original.alloc_qreg_bits("C",6);let sm=original.alloc_qreg_bits("SM",4);let p1=original.alloc_qreg("p1");let p2=original.alloc_qreg("p2");let it=original.alloc_qreg("it");let w1=original.alloc_qreg_bits("w1",259);let w2=original.alloc_qreg_bits("w2",259);let h=original.alloc_qreg_bits("h",23);let on=original.b.next_qubit as usize;assert_eq!(on,565);
            BANK.with(|b|b.borrow_mut().clear());ACTIVE.with(|x|x.set(true));super::super::q793_step_r03::passive20_template(&mut original,&rank,&a,&cl,&sm,&p1,&p2,&it,&w1,&w2,&h,j,kind);ACTIVE.with(|x|x.set(false));let source=original.into_builder().ops;let pool:Vec<_>=h.iter().chain(std::iter::once(&it)).map(|q|q.id()as usize).collect();let old=lower_legacy(&source,on,&pool);
            let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("metadata20",20);let p1=c.alloc_qreg("p1");let p2=c.alloc_qreg("p2");let it=c.alloc_qreg("it");let w1=c.alloc_qreg_bits("w1",259);let w2=c.alloc_qreg_bits("w2",259);let h=c.alloc_qreg_bits("h",23);let n=c.b.next_qubit as usize;assert_eq!(n,564);emit(&mut c,&m,&p1,&p2,&it,&w1,&w2,&h,j,kind);assert_eq!(c.b.next_qubit as usize,n);let ops=c.into_builder().ops;
            for op in ops.iter().chain(&old).chain(&source){op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
            let cost=|v:&[Op]|v.iter().filter(|o|o.kind==K::CCX).count();let duplicate=seen.iter().any(|(a,b,d)|*a==ops&&*b==old&&*d==source);
            if !duplicate{unique+=1;seen.push((ops.clone(),old.clone(),source.clone()));
                for first in (0..1usize<<20).step_by(16){
                    let mut seed=0x7921_70ba_5e03u64^first as u64^((kind as u64)<<40)^((j as u64)<<48);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();for bit in 0..20{before[bit]=(0..64).fold(0,|v,l|v|(((first+l/4)>>bit&1)as u64)<<l);}
                    before[p1.id()as usize]=0xaaaa_aaaa_aaaa_aaaa;before[p2.id()as usize]=0xcccc_cccc_cccc_cccc;
                    let mut ob=vec![0u64;on];ob[21..].copy_from_slice(&before[20..]);let mut valid=0u64;for lane in 0..64{if let Some(logical)=decoded(first+lane/4){valid|=1u64<<lane;for bit in 0..21{ob[bit]|=((logical>>bit&1)as u64)<<lane;}}}
                    let mut f=Fixed;let mut sim=Simulator::new(n,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.phase,0);let actual=sim.qubits.clone();sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before,"candidate inverse kind={kind} j={j} first={first}");assert_eq!(sim.phase,0);
                    let mut f=Fixed;let mut legacy=Simulator::new(n,0,&mut f);legacy.qubits.copy_from_slice(&before);legacy.apply_iter(old.iter());assert_eq!(legacy.phase,0);assert_eq!(legacy.qubits,actual,"arbitrary-code extension kind={kind} j={j} first={first}");legacy.apply_iter(old.iter().rev());assert_eq!(legacy.qubits,before);assert_eq!(legacy.phase,0);
                    let mut f=Fixed;let mut reference=Simulator::new(on,0,&mut f);reference.qubits.copy_from_slice(&ob);reference.apply_iter(source.iter());assert_eq!(reference.phase,0);for bit in 0..21{assert_eq!(reference.qubits[bit]&valid,ob[bit]&valid,"metadata changed");}for bit in 20..n{assert_eq!(reference.qubits[bit+1]&valid,actual[bit]&valid,"unfolded oracle kind={kind} j={j} first={first} physical={bit}");}for bit in 0..20{assert_eq!(actual[bit],before[bit]);}
                    lanes+=64;valid_lanes+=valid.count_ones()as u64;
                }
            }
            eprintln!("FOLD20_PASSIVE_NATIVE_CASE kind={kind} j={j} ports={n} max_id=563 T={} N={} old_T={} old_N={} ops_shake256={} duplicate={duplicate}",cost(&ops),ops.len(),cost(&old),old.len(),hash(&ops));
        }}
        eprintln!("FOLD20_PASSIVE_NATIVE_PASS kinds=4,5,6 clocks=4 streams=12 unique_streams={unique} lanes={lanes} decoded_lanes={valid_lanes} metadata_codes=1048576 phase_patterns=4 arbitrary_h0=true arbitrary_cache=true all_ports=564 max_id=563 phase=0 inverse=true invalid_extension_equals_parent=true whole_Q792=false");
    }
}
