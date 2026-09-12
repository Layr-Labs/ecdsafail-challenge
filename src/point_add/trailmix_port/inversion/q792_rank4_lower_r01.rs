//! Exact class-local lowering of a virtual five-bit rank onto four wires.
//! Only rank-only permutations may target virtual rank. The current rank
//! functions are exhaustively tracked on all sixteen physical codes.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{Op,OperationType as K,NO_QUBIT};

#[derive(Clone)]struct Pair {exact:bool,ops:Vec<Op>,controls:Vec<(usize,bool)>,target:usize,scratch:usize,conditional:Option<(usize,bool,usize)>}
thread_local!{static CAPTURE:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};static PAIRS:std::cell::RefCell<Vec<Pair>>=const{std::cell::RefCell::new(Vec::new())};}
pub(super) fn pair_begin(c:&Circuit,cs:&[(&QReg,bool)])->Option<usize>{(CAPTURE.with(|x|x.get())&&cs.len()>=3&&cs.iter().any(|(q,_)|q.id()<5)).then_some(c.b.ops.len())}
pub(super) fn pair_end(c:&Circuit,start:Option<usize>,cs:&[(&QReg,bool)],target:&QReg,scratch:&QReg){
    if let Some(start)=start{let ops=c.b.ops[start..].to_vec();PAIRS.with(|p|{let mut p=p.borrow_mut();if !p.iter().any(|x|x.ops==ops){p.push(Pair{exact:false,ops,controls:cs.iter().map(|(q,b)|(q.id()as usize,*b)).collect(),target:target.id()as usize,scratch:scratch.id()as usize,conditional:None});}});}
}
pub(super) fn conditional_end(c:&Circuit,start:Option<usize>,cs:&[(&QReg,bool)],target:&QReg,scratch:&QReg,g:&QReg,known:bool,d:&QReg){
    if let Some(start)=start{let ops=c.b.ops[start..].to_vec();PAIRS.with(|p|{let mut p=p.borrow_mut();if !p.iter().any(|x|x.ops==ops){p.push(Pair{exact:false,ops,controls:cs.iter().map(|(q,b)|(q.id()as usize,*b)).collect(),target:target.id()as usize,scratch:scratch.id()as usize,conditional:Some((g.id()as usize,known,d.id()as usize))});}});}
}
fn pair_poly(n:usize)->Vec<u64>{
    use std::collections::BTreeSet;fn product(a:&BTreeSet<u64>,b:&BTreeSet<u64>)->BTreeSet<u64>{let mut out=BTreeSet::new();for &x in a{for &y in b{if !out.insert(x|y){out.remove(&(x|y));}}}out}
    fn toggle(a:&mut BTreeSet<u64>,b:BTreeSet<u64>){for m in b{if !a.insert(m){a.remove(&m);}}}
    assert!((3..=31).contains(&n));let mut w:Vec<BTreeSet<u64>>=(0..n+1).map(|i|std::iter::once(1u64<<i).collect()).collect();let mut marked=vec![false;n+1];marked[0]=true;
    loop{let mut choice=None;for t in (0..n+1).rev(){if !marked[t]{continue;}let xs:Vec<_>=(t+1..n+1).filter(|&i|!marked[i]).take(2).collect();if xs.len()==2{choice=Some((xs[0],xs[1],t));break;}}
        let Some((x,y,t))=choice else{break;};let p=product(&w[x],&w[y]);toggle(&mut w[t],p);if t!=0{toggle(&mut w[t],std::iter::once(0).collect());}marked[t]=false;marked[x]=true;marked[y]=true;
    }
    let left:Vec<_>=(0..n+1).filter(|&i|!marked[i]).collect();assert_eq!(left.len(),2);product(&w[left[0]],&w[left[1]]).into_iter().collect()
}
fn lower_pair(c:&mut Circuit,q:&[QReg],p:&Pair,rank:&[usize;16],dirty_ids:&[usize]){
    assert!(p.target>=5);let vars:Vec<_>=std::iter::once((p.scratch,!p.conditional.is_some_and(|(_,known,_)|known))).chain(p.controls.iter().copied()).collect();let mut groups=std::collections::BTreeMap::<Vec<(usize,bool)>,[bool;16]>::new();
    for m in pair_poly(p.controls.len()){
        let mut lits:Vec<_>=vars.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,v)|*v).collect();if let Some((g,_,_))=p.conditional{lits.push((g,true));}let mut prefix:Vec<_>=lits.iter().copied().filter(|(q,_)|*q>=5).collect();prefix.sort_unstable();
        let truth=groups.entry(prefix).or_insert([false;16]);for code in 0..16{truth[code]^=lits.iter().filter(|(q,_)|*q<5).all(|&(q,b)|(rank[code]>>q&1!=0)==b);}
    }
    for (prefix,truth)in groups{let pool:Vec<_>=dirty_ids.iter().copied().filter(|&id|id!=p.target&&!prefix.iter().any(|(v,_)|*v==id)).map(|v|q[v-1].borrowed_alias()).collect();let cs:Vec<_>=prefix.iter().map(|&(id,b)|(&q[id-1],b)).collect();super::q792_fold20_r01::table(c,&q[..4].iter().collect::<Vec<_>>(),truth.to_vec(),&cs,&q[p.target-1],&pool);}
}
pub(super) fn exact_begin(c:&Circuit,cs:&[(&QReg,bool)],out:&QReg)->Option<usize>{(CAPTURE.with(|x|x.get())&&out.id()>=5&&cs.iter().any(|(q,_)|q.id()<5)).then_some(c.b.ops.len())}
pub(super) fn exact_end(c:&Circuit,start:Option<usize>,cs:&[(&QReg,bool)],out:&QReg){if let Some(start)=start{let ops=c.b.ops[start..].to_vec();if !ops.is_empty(){PAIRS.with(|p|p.borrow_mut().push(Pair{exact:true,ops,controls:cs.iter().map(|(q,b)|(q.id()as usize,*b)).collect(),target:out.id()as usize,scratch:usize::MAX,conditional:None}));}}}
fn lower_exact(c:&mut Circuit,q:&[QReg],p:&Pair,rank:&[usize;16],dirty_ids:&[usize]){
 let truth:Vec<_>=rank.iter().map(|&r|p.controls.iter().filter(|(id,_)|*id<5).all(|&(id,b)|(r>>id&1!=0)==b)).collect();let cs:Vec<_>=p.controls.iter().filter(|(id,_)|*id>=5).map(|&(id,b)|(&q[id-1],b)).collect();let pool:Vec<_>=dirty_ids.iter().copied().filter(|&id|id!=p.target&&!p.controls.iter().any(|(v,_)|*v==id)).map(|id|q[id-1].borrowed_alias()).collect();super::q792_fold20_r01::table(c,&q[..4].iter().collect::<Vec<_>>(),truth,&cs,&q[p.target-1],&pool);
}
pub(super) fn chart(class:usize)->[usize;16]{
    if class==3||class==4{let ts=super::q792_fold20_rank_r01::triples();let mut out=[0;16];for (r,t)in ts.iter().enumerate(){if t[if class==3{2}else{1}]==0{out[t[0]+4*t[if class==3{1}else{2}]]=r;}}return out;}

    let ts=super::q792_fold20_rank_r01::triples();let rows:Vec<_>=(0..32).filter(|&r|if class==0{ts[r].iter().sum::<usize>()<=2}else{ts[r].iter().sum::<usize>()==class+2}).collect();
    let kernel=[24usize,16,29][class];let pivot=kernel.trailing_zeros()as usize;let mut out=[rows[0];16];let mut used=[false;16];
    for r in rows{let frame=r^if r>>pivot&1!=0{kernel}else{0};let code=(frame&((1<<pivot)-1))|((frame>>(pivot+1))<<pivot);assert!(!used[code]);used[code]=true;out[code]=r;}out
}

fn lower_clean_pair(c:&mut Circuit,q:&[QReg],p:&Pair,rank:&[usize;16]){
    assert!(p.target>=5&&p.scratch>=5);let truth:Vec<_>=rank.iter().map(|&r|p.controls.iter().filter(|(id,_)|*id<5).all(|&(id,b)|(r>>id&1!=0)==b)).collect();let (pol,terms)=super::metadata_muxlease::swap_terms(truth,4);
    for m in terms{let mut cs:Vec<_>=p.controls.iter().filter(|(id,_)|*id>=5).map(|&(id,b)|(&q[id-1],b)).collect();cs.extend((0..4).filter(|&i|m>>i&1!=0).map(|i|(&q[i],pol>>i&1==0)));
        if let Some((g,known,d))=p.conditional{assert!(g>=5);super::conditional_mcx::guarded(c,&q[g-1],&cs,&q[p.target-1],&q[p.scratch-1],known,&q[d-1]);}else{super::paired_clean_mcx::toggle(c,&cs,&q[p.target-1],&q[p.scratch-1]);}
    }
}
type CleanPending=Option<(usize,usize,std::collections::BTreeMap<Vec<(usize,bool)>,[bool;16]>)>;
fn flush_clean(c:&mut Circuit,q:&[QReg],pending:&mut CleanPending){if let Some((target,scratch,groups))=pending.take(){for(prefix,truth)in groups{let cs:Vec<_>=prefix.iter().map(|&(id,b)|(&q[id-1],b)).collect();super::q792_esop_r01::paired(c,&q[..4].iter().collect::<Vec<_>>(),truth.to_vec(),&cs,&q[target-1],&q[scratch-1]);}}}
fn queue_clean(c:&mut Circuit,q:&[QReg],p:&Pair,rank:&[usize;16],pending:&mut CleanPending){
 assert!(p.conditional.is_none()&&p.scratch>=5&&p.target>=5);if pending.as_ref().is_some_and(|(target,scratch,_)|*target!=p.target||*scratch!=p.scratch){flush_clean(c,q,pending);}let(_,_,groups)=pending.get_or_insert_with(||(p.target,p.scratch,std::collections::BTreeMap::new()));let mut prefix:Vec<_>=p.controls.iter().copied().filter(|(id,_)|*id>=5).collect();prefix.sort_unstable();prefix.dedup();if prefix.windows(2).any(|v|v[0].0==v[1].0&&v[0].1!=v[1].1){return;}let truth=groups.entry(prefix).or_insert([false;16]);for code in 0..16{truth[code]^=p.controls.iter().filter(|(id,_)|*id<5).all(|&(id,b)|(rank[code]>>id&1!=0)==b);}
}
pub(super) fn begin_capture(){CAPTURE.with(|x|x.set(true));PAIRS.with(|p|p.borrow_mut().clear());}
pub(super) fn end_capture(){CAPTURE.with(|x|x.set(false));}
pub(super) fn lower(ops:&[Op],n:usize,dirty_ids:&[usize],class:usize)->Vec<Op>{lower_impl(ops,n,dirty_ids,class,false)}
pub(super) fn lower_clean(ops:&[Op],n:usize,dirty_ids:&[usize],class:usize)->Vec<Op>{lower_impl(ops,n,dirty_ids,class,true)}
type Pending=Option<(usize,std::collections::BTreeMap<Vec<(usize,bool)>,[bool;16]>)>;
fn flush_exact(c:&mut Circuit,q:&[QReg],dirty_ids:&[usize],pending:&mut Pending){if let Some((target,groups))=pending.take(){for(prefix,truth)in groups{let cs:Vec<_>=prefix.iter().map(|&(id,b)|(&q[id-1],b)).collect();let pool:Vec<_>=dirty_ids.iter().copied().filter(|&id|id!=target&&!prefix.iter().any(|(v,_)|*v==id)).map(|id|q[id-1].borrowed_alias()).collect();super::q792_fold20_r01::table(c,&q[..4].iter().collect::<Vec<_>>(),truth.to_vec(),&cs,&q[target-1],&pool);}}}
fn queue_exact(c:&mut Circuit,q:&[QReg],p:&Pair,rank:&[usize;16],dirty_ids:&[usize],pending:&mut Pending){
 if pending.as_ref().is_some_and(|(target,_)|*target!=p.target){flush_exact(c,q,dirty_ids,pending);}let(_,groups)=pending.get_or_insert_with(||(p.target,std::collections::BTreeMap::new()));let mut prefix:Vec<_>=p.controls.iter().copied().filter(|(id,_)|*id>=5).collect();prefix.sort_unstable();prefix.dedup();if prefix.windows(2).any(|v|v[0].0==v[1].0&&v[0].1!=v[1].1){return;}
 let truth=groups.entry(prefix).or_insert([false;16]);for code in 0..16{truth[code]^=p.controls.iter().filter(|(id,_)|*id<5).all(|&(id,b)|(rank[code]>>id&1!=0)==b);}
}
fn lower_impl(ops:&[Op],n:usize,dirty_ids:&[usize],class:usize,clean:bool)->Vec<Op>{
    assert!(dirty_ids.len()>=16);let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let q=c.alloc_qreg_bits("physical.rank4-template",n-1);
    let initial=chart(class);let mut rank=initial;let mut symbolic=0usize;let mut skipped=0usize;let mut macros=0usize;let mut pairs=PAIRS.with(|p|p.borrow().clone());let reversed:Vec<_>=pairs.iter().cloned().map(|mut p|{p.ops.reverse();p}).collect();pairs.extend(reversed);pairs.sort_by_key(|p|std::cmp::Reverse(p.ops.len()));
    let mut pending:Pending=None;let mut clean_pending:CleanPending=None;
    let mut index=std::collections::BTreeMap::new();for p in pairs{index.entry((p.ops[0].kind as u8,p.ops[0].q_target.0,p.ops[0].q_control1.0,p.ops[0].q_control2.0)).or_insert_with(Vec::new).push(p);}
    for (at,op)in ops.iter().enumerate(){
        if at<skipped{continue;}if let Some(p)=index.get(&(op.kind as u8,op.q_target.0,op.q_control1.0,op.q_control2.0)).and_then(|xs|xs.iter().find(|p|ops[at..].starts_with(&p.ops))){if p.exact{flush_clean(&mut c,&q,&mut clean_pending);queue_exact(&mut c,&q,p,&rank,dirty_ids,&mut pending);}else{flush_exact(&mut c,&q,dirty_ids,&mut pending);if clean&&p.conditional.is_none(){queue_clean(&mut c,&q,p,&rank,&mut clean_pending);}else{flush_clean(&mut c,&q,&mut clean_pending);if clean{lower_clean_pair(&mut c,&q,p,&rank);}else{lower_pair(&mut c,&q,p,&rank,dirty_ids);}}}skipped=at+p.ops.len();macros+=1;continue;}
        assert!(matches!(op.kind,K::X|K::CX|K::CCX));let target=op.q_target.0 as usize;let controls:Vec<_>=[op.q_control1,op.q_control2].into_iter().filter(|&v|v!=NO_QUBIT).map(|v|v.0 as usize).collect();
        if target<5{
            assert!(controls.iter().all(|&v|v<5),"external-controlled rank target at {at}: {op:?}");
            for r in &mut rank{if controls.iter().all(|&v|*r>>v&1!=0){*r^=1<<target;}}symbolic+=1;continue;
        }
        flush_exact(&mut c,&q,dirty_ids,&mut pending);flush_clean(&mut c,&q,&mut clean_pending);
        if controls.iter().all(|&v|v>=5){let mut new=*op;for wire in [&mut new.q_target,&mut new.q_control1,&mut new.q_control2]{if *wire!=NO_QUBIT{wire.0-=1;}}c.b.ops.push(new);continue;}
        let truth:Vec<_>=rank.iter().map(|&r|controls.iter().filter(|&&v|v<5).all(|&v|r>>v&1!=0)).collect();let prefix:Vec<_>=controls.iter().filter(|&&v|v>=5).map(|&v|(&q[v-1],true)).collect();
        let pool:Vec<_>=dirty_ids.iter().copied().filter(|&v|v!=target&&!controls.contains(&v)).map(|v|q[v-1].borrowed_alias()).collect();
        assert!(pool.len()>=14);super::q792_fold20_r01::table(&mut c,&q[..4].iter().collect::<Vec<_>>(),truth,&prefix,&q[target-1],&pool);
    }
    flush_exact(&mut c,&q,dirty_ids,&mut pending);flush_clean(&mut c,&q,&mut clean_pending);
    assert_eq!(rank,initial,"template must restore its rank chart");assert_eq!(c.b.next_qubit as usize,n-1);
    let mut out=c.into_builder().ops;super::shared_optimize::cancel_nct(&mut out,2048,8);super::shared_optimize::cancel_nct_live(&mut out,2048);
    eprintln!("RANK4_LOWER class={class} original_ops={} new_ops={} symbolic_rank_gates={symbolic} paired_macros={macros} conditional_clean={clean}",ops.len(),out.len());out
}
fn template(j:usize)->(Vec<Op>,usize,Vec<usize>){
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let r=c.alloc_qreg_bits("r",5);let a=c.alloc_qreg_bits("a",6);let cl=c.alloc_qreg_bits("cl",6);let sm=c.alloc_qreg_bits("sm",4);
    let g=c.alloc_qreg("g");let mask=c.alloc_qreg("mask");let hs=c.alloc_qreg("hs");let ha=c.alloc_qreg("ha");let decision=c.alloc_qreg("decision");let w1=c.alloc_qreg_bits("w1",259);let w2=c.alloc_qreg_bits("w2",259);let d=c.alloc_qreg_bits("dirty",20);let n=c.b.next_qubit;
    CAPTURE.with(|x|x.set(true));PAIRS.with(|p|p.borrow_mut().clear());
    super::q793_r01_normal_timefix_r01::emit(&mut c,&r,&a,&cl,&sm,&g,&mask,&hs,&ha,&decision,&w1,&w2,&d,j,259,false);
    CAPTURE.with(|x|x.set(false));
    let ids=d.iter().map(|q|q.id()as usize).collect();(c.into_builder().ops,n as usize,ids)
}
pub fn run(){
    use crate::sim::Simulator;use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x89)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let old=std::env::var_os("Q793_R01_NUMERIC_SEED");std::env::set_var("Q793_R01_NUMERIC_SEED","0");let mut total=0;
    for j in 0..4{let (source,n,d)=template(j);for class in 0..3{let ops=lower(&source,n,&d,class);let mapping=chart(class);
        eprintln!("RANK4_R01_BUILT j={j} class={class} metadata=20 T={} ops={} original_T={} original_ops={}",ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len(),source.iter().filter(|o|o.kind==K::CCX).count(),source.len());
        for batch in 0..64{let mut seed=0x79214c00u64^batch as u64^((j as u64)<<40)^((class as u64)<<44);let mut before:Vec<_>=(0..n-1).map(|_|rnd(&mut seed)).collect();
            for i in 0..4{before[i]=(0..64).fold(0,|v,l|v|(((l>>i)&1)as u64)<<l);}
            let mut reference=vec![0u64;n];reference[5..].copy_from_slice(&before[4..]);for lane in 0..64{let r=mapping[lane&15];for i in 0..5{reference[i]|=(((r>>i)&1)as u64)<<lane;}}
            let mut f=Fixed;let mut fs=Fixed;let mut a=Simulator::new(n,0,&mut f);let mut b=Simulator::new(n-1,0,&mut fs);a.qubits.copy_from_slice(&reference);b.qubits.copy_from_slice(&before);
            a.apply_iter(source.iter());b.apply_iter(ops.iter());assert_eq!(&a.qubits[..5],&reference[..5]);assert_eq!(&b.qubits[..4],&before[..4]);assert_eq!(&a.qubits[5..],&b.qubits[4..],"rank4 differential j={j} class={class} batch={batch}");assert_eq!(a.phase,0);assert_eq!(b.phase,0);b.apply_iter(ops.iter().rev());assert_eq!(b.qubits,before);assert_eq!(b.phase,0);total+=64;
        }
    }}match old{Some(v)=>std::env::set_var("Q793_R01_NUMERIC_SEED",v),None=>std::env::remove_var("Q793_R01_NUMERIC_SEED")};eprintln!("RANK4_R01_LOWER_NATIVE_PASS lanes={total} classes=3 clocks=4 arbitrary_all_nonrank_data=true inverse=true phase=0 whole_Q792=false");
}

#[path="q792_rank4_clean_check_r01.rs"]mod clean_check;
pub fn run_clean(){clean_check::run();}
