//! Exact low-workspace replacements. No finite-window policy is changed here.
use super::{Builder, compare, modular};
use crate::circuit::{QubitId,BitId};
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

#[derive(Clone,Debug)]
pub(crate) struct Plan { pub sizes: Vec<usize>, pub slow: bool, pub extra2: usize, pub peak: usize }

pub(crate) fn plan(n:usize, room:usize)->Option<Plan> {
    static CACHE:OnceLock<Mutex<HashMap<(usize,usize),Option<Plan>>>>=OnceLock::new();
    let cache=CACHE.get_or_init(||Mutex::new(HashMap::new()));
    if let Some(p)=cache.lock().unwrap().get(&(n,room)){return p.clone();}
    let mut best:Option<Plan>=None;
    let mut offer=|sizes:Vec<usize>,slow:bool,extra2:usize,peak:usize|{
        assert_eq!(sizes.iter().sum::<usize>(),n);assert!(peak<=room);
        let key=(extra2,peak,sizes.len());
        if best.as_ref().is_none_or(|p|key<(p.extra2,p.peak,p.sizes.len())) {best=Some(Plan{sizes,slow,extra2,peak});}
    };
    if room>=n {offer(vec![n],false,0,n);} else {
        for k in 2..=n.min(room) {
            let caps:Vec<_>=(0..k).map(|j|room-j).collect();
            if caps.iter().sum::<usize>()<n {continue;}
            let last=caps[k-1].min(n-k+1);
            let mut sizes=vec![1;k];sizes[k-1]=last;
            let mut left=n-sizes.iter().sum::<usize>();
            for j in 0..k-1{let take=left.min(caps[j]-1);sizes[j]+=take;left-=take;}
            if left>0{continue;}
            let peak=sizes.iter().enumerate().map(|(j,w)|j+w).max().unwrap();
            let extra2=sizes[..k-1].iter().map(|w|w-1).sum();offer(sizes,false,extra2,peak);
        }
        if room>=2 {
            for k in 0..=(n-1).min(room-1) {
                let caps:Vec<_>=(0..k).map(|j|room-j).collect();
                let last=n.saturating_sub(caps.iter().sum()).max(1);
                if last>n-k{continue;}
                let mut sizes=vec![1;k+1];sizes[k]=last;
                let mut left=n-sizes.iter().sum::<usize>();
                for j in 0..k{let take=left.min(caps[j]-1);sizes[j]+=take;left-=take;}
                if left>0{continue;}
                let peak=sizes[..k].iter().enumerate().map(|(j,w)|j+w).chain(std::iter::once(if k==0{2}else{k+1})).max().unwrap();
                let extra2=2*last+sizes[..k].iter().map(|w|w-1).sum::<usize>();offer(sizes,true,extra2,peak);
            }
        }
    }
    cache.lock().unwrap().insert((n,room),best.clone());best
}

fn erase_release(c:&mut Builder,q:QubitId,a:&[QubitId],b:&[QubitId],incoming:Option<QubitId>){
    let m=c.alloc_bit();c.hmr(q,m);c.release_clean(q);
    c.push_condition(m);
    if b.len()>1 {compare::cmp_lt_phase(c,b,a,incoming);} else {
        c.x(b[0]);c.cz(a[0],b[0]);
        if let Some(p)=incoming{c.cz(a[0],p);c.cz(b[0],p);}
        c.x(b[0]);
    }
    c.pop_condition();c.free_bit(m);
}

fn inplace(c:&mut Builder,a:&[QubitId],b:&[QubitId],incoming:Option<QubitId>,out:QubitId){
    let seed=incoming.unwrap_or_else(||c.alloc_qubit());
    for i in 0..a.len(){let p=if i==0{seed}else{a[i-1]};c.cx(a[i],b[i]);c.cx(a[i],p);c.ccx(p,b[i],a[i]);}
    c.cx(a[a.len()-1],out);
    for i in (0..a.len()).rev(){let p=if i==0{seed}else{a[i-1]};c.ccx(p,b[i],a[i]);c.cx(a[i],p);c.cx(p,b[i]);}
    if incoming.is_none(){c.release_clean(seed);}
}

pub(crate) fn add(c:&mut Builder,a:&[QubitId],b:&[QubitId],p:&Plan)->QubitId{
    add_with_carry(c,a,b,None,p)
}

/// Same exact adder with a live, preserved incoming carry. Its wire is part
/// of the caller's base, so the existing workspace plan is unchanged.
pub(crate) fn add_with_carry(c:&mut Builder,a:&[QubitId],b:&[QubitId],initial:Option<QubitId>,p:&Plan)->QubitId{
    let _dirty_trace=super::dirty_boundary_probe::Trace::new(c,"wc_add",b.len());
    eprintln!("DIRTY_PLAN\t{}\t{}\t{}\t{}\t{}\t{}\t{:?}",c.op_count(),b.len(),c.active_qubits(),p.slow as u8,p.extra2,p.peak,p.sizes);
    assert_eq!(a.len(),b.len());assert_eq!(p.sizes.iter().sum::<usize>(),a.len());
    let base=c.active_qubits();let mut at=0;let mut incoming=initial;let mut flags=Vec::new();
    for (j,&w) in p.sizes.iter().enumerate(){
        let out=c.alloc_qubit();let end=at+w;
        if p.slow && j+1==p.sizes.len(){inplace(c,&a[at..end],&b[at..end],incoming,out);}
        else {modular::ripple_add(c,&a[at..end],&b[at..end],incoming,Some(out));}
        if j+1<p.sizes.len(){flags.push((at,end,incoming,out));}
        incoming=Some(out);at=end;
    }
    for (lo,hi,prev,q) in flags.into_iter().rev(){erase_release(c,q,&a[lo..hi],&b[lo..hi],prev);}
    assert_eq!(c.active_qubits(),base+1);incoming.unwrap()
}

pub(crate) fn mapped_peak(n:usize,chunk:usize)->usize{
    let buffer=n.min(chunk);let count=n.div_ceil(chunk);
    (0..count).map(|j|{
        let w=chunk.min(n-j*chunk);
        // j incoming boundaries; nonfinal out and w-1 ladder, or wrapped w-2.
        buffer+j+if j+1<count{w}else{w.saturating_sub(2)}
    }).max().unwrap()
}

pub(crate) fn mapped_extra2(n:usize,chunk:usize)->usize{
    let count=n.div_ceil(chunk);(0..count-1).map(|_|chunk-1).sum()
}

fn copy(c:&mut Builder,map:&[Vec<QubitId>],buf:&[QubitId]){
    for (bits,&q) in map.iter().zip(buf){for &bit in bits{c.cx(bit,q);}}
}

/// b += XOR-mapped source + incoming, modulo 2^n. Source and incoming restored.
pub(crate) fn mapped_add(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId,chunk:usize){
    assert_eq!(map.len(),b.len());let base=c.active_qubits();
    let buffer=c.alloc_qubits(chunk.min(b.len()));let mut stages=Vec::new();
    let mut at=0;let mut prev=Some(incoming);
    while at<b.len(){
        let end=(at+chunk).min(b.len());let src=&map[at..end];let tmp=&buffer[..end-at];
        copy(c,src,tmp);let out=if end<b.len(){Some(c.alloc_qubit())}else{None};
        modular::ripple_add(c,tmp,&b[at..end],prev,out);copy(c,src,tmp);
        if let Some(q)=out{stages.push((at,end,prev,q));}prev=out;at=end;
    }
    for (lo,hi,prev,q) in stages.into_iter().rev(){
        let src=&map[lo..hi];let tmp=&buffer[..hi-lo];copy(c,src,tmp);
        erase_release(c,q,tmp,&b[lo..hi],prev);copy(c,src,tmp);
    }
    for q in buffer{c.release_clean(q);}assert_eq!(c.active_qubits(),base);
}

pub(crate) fn direct_plan(n:usize,room:usize)->Option<Plan>{
    let mut best:Option<Plan>=None;
    for k in 1..=n.min(room+1){
        let mut caps:Vec<_>=(0..k-1).map(|j|room-j).collect();caps.push(room-(k-1)+2);
        if caps.contains(&0)||caps.iter().sum::<usize>()<n{continue;}
        let mut sizes=vec![1;k];sizes[k-1]=caps[k-1].min(n-k+1);
        let mut left=n-sizes.iter().sum::<usize>();
        for j in 0..k-1{let d=left.min(caps[j]-1);sizes[j]+=d;left-=d;}
        if left>0{continue;}
        let extra2=sizes[..k-1].iter().map(|w|w-1).sum();
        let peak=sizes.iter().enumerate().map(|(j,w)|j+if j+1<k{*w}else{w.saturating_sub(2)}).max().unwrap();
        if best.as_ref().is_none_or(|p|(extra2,peak,k)<(p.extra2,p.peak,p.sizes.len())){best=Some(Plan{sizes,slow:false,extra2,peak});}
    }best
}

fn mapped_compare(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId){
    let _dirty_trace=super::dirty_boundary_probe::Trace::new(c,"mapped_compare",b.len());

    use super::pingpong::{fold_step,with_selector_xor};
    let n=b.len();let carries=c.alloc_qubits(n-1);c.x_all(b);
    for i in 0..n-1{let prev=if i==0{incoming}else{carries[i-1]};fold_step(c,b[i],prev,carries[i],&map[i],false);}
    let prev=if n==1{incoming}else{carries[n-2]};
    if map[n-1].is_empty(){c.cz(b[n-1],prev);}else{
        with_selector_xor(c,&map[n-1],prev,|c,s|{c.cz(b[n-1],s);c.cz(b[n-1],prev);c.cz(s,prev);});
    }
    for i in (0..n-1).rev(){let prev=if i==0{incoming}else{carries[i-1]};
        with_selector_xor(c,&map[i],prev,|c,s|{
            c.cx(prev,carries[i]);if s!=prev{c.cx(prev,s);}
            let m=c.alloc_bit();c.hmr(carries[i],m);c.cz_if(s,b[i],m);c.free_bit(m);
            if s!=prev{c.cx(prev,s);}c.cx(prev,b[i]);
        });
    }
    c.free_vec(&carries);c.x_all(b);
}

/// Exact wrapped source-selected add, without materializing a source word.
pub(crate) fn direct_add(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId,p:&Plan){
    assert!(direct_add_phase_transport(c,map,b,incoming,p,false,&[]).is_empty());
}

/// Optionally retain classical measurement outcomes instead of comparing to
/// repair boundary phases. A matching inverse recreates the SAME carries and
/// applies these deferred Z corrections before normal exact cleanup.
pub(crate) fn direct_add_phase_transport(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId,p:&Plan,defer:bool,recover:&[(usize,BitId)])->Vec<(usize,BitId)>{
    if std::env::var_os("FOLD_MAP_TRACE").is_some(){let mut syms=map.iter().flatten().copied().collect::<Vec<_>>();syms.push(incoming);syms.sort_by_key(|q|q.0);syms.dedup();let rows=map.iter().map(|r|r.iter().map(|q|syms.iter().position(|x|x==q).unwrap()).collect::<Vec<_>>()).collect::<Vec<_>>();eprintln!("FOLD_MAP\t{}\t{}\t{}\t{}\t{:?}",c.op_count(),super::pingpong::heo_hooks::cap().saturating_sub(c.active_qubits()as usize),syms.len(),syms.iter().position(|q|*q==incoming).unwrap(),rows);}
    eprintln!("DIRTY_DIRECT_PLAN\t{}\t{}\t{}\t{}\t{}\t{}\t{:?}",c.op_count(),b.len(),c.active_qubits(),p.slow as u8,p.extra2,p.peak,p.sizes);
    let _dirty_trace=super::dirty_boundary_probe::Trace::new(c,"direct_add_phase_transport",b.len());
    let room=super::pingpong::heo_hooks::cap().saturating_sub(c.active_qubits()as usize);
    if !defer && recover.is_empty() && p.peak>room && std::env::var_os("FOLD_PACKED_BOUNDARIES").is_some() {
        if super::fold_template::try_fold(c,map,b,incoming,room){return Vec::new();}
    }

    use super::pingpong::{fold_step,unwind_fold_step};
    assert_eq!(p.sizes.iter().sum::<usize>(),b.len());let base=c.active_qubits();
    let mut at=0;let mut prev=incoming;let mut stages=Vec::new();
    for(j,&w)in p.sizes.iter().enumerate(){let last=j+1==p.sizes.len();let end=at+w;
        let out=if last{None}else{Some(c.alloc_qubit())};
        if !strict_square_chunk(c,map,b,at,w,prev,out){
        let work=c.alloc_qubits(if last{w.saturating_sub(2)}else{w-1});
        for i in 0..work.len(){let carry=if i==0{prev}else{work[i-1]};fold_step(c,b[at+i],carry,work[i],&map[at+i],false);}
        let carry=work.last().copied().unwrap_or(prev);
        if let Some(q)=out{fold_step(c,b[end-1],carry,q,&map[end-1],true);}else if w==1{
            c.cx(prev,b[at]);for &s in &map[at]{c.cx(s,b[at]);}
        }else{
            fold_step(c,b[end-2],carry,b[end-1],&map[end-2],true);
            for &s in &map[end-1]{c.cx(s,b[end-1]);}
        }
        for i in(0..work.len()).rev(){let carry=if i==0{prev}else{work[i-1]};unwind_fold_step(c,b[at+i],carry,work[i],&map[at+i]);}
        c.free_vec(&work);
        }

        if let Some(q)=out{
            for &(boundary,bit)in recover{if boundary==end{c.z_if(q,bit);c.free_bit(bit);}}
            stages.push((at,end,prev,q));prev=q;
        }at=end;
    }
    assert!(recover.iter().all(|(hi,_)|stages.iter().any(|(_,end,_,_)|hi==end)));
    let mut pending=Vec::new();
    for(lo,hi,cin,q)in stages.into_iter().rev(){let m=c.alloc_bit();c.hmr(q,m);c.release_clean(q);
        if defer{pending.push((hi,m));}else{c.push_condition(m);if !super::leapfrog::C35_SQ_FX.with(|x|x.get()){mapped_compare(c,&map[lo..hi],&b[lo..hi],cin);}c.pop_condition();c.free_bit(m);}
    }
    assert_eq!(c.active_qubits(),base);
    pending
}

/// One chunk of the direct ripple, as in [`direct_add_phase_transport`]:
/// carries chained from `prev`; a non-final chunk XORs its carry-out into
/// `out`; the sum bits are finished in `b` and the ladder is unwound.
fn direct_chunk(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],at:usize,w:usize,prev:QubitId,out:Option<QubitId>){
    if strict_square_chunk(c,map,b,at,w,prev,out){return;}

    use super::pingpong::{fold_step,unwind_fold_step};
    let end=at+w;
    let work=c.alloc_qubits(if out.is_none(){w.saturating_sub(2)}else{w-1});
    for i in 0..work.len(){let carry=if i==0{prev}else{work[i-1]};fold_step(c,b[at+i],carry,work[i],&map[at+i],false);}
    let carry=work.last().copied().unwrap_or(prev);
    if let Some(q)=out{fold_step(c,b[end-1],carry,q,&map[end-1],true);}else if w==1{
        c.cx(prev,b[at]);for &s in &map[at]{c.cx(s,b[at]);}
    }else{
        fold_step(c,b[end-2],carry,b[end-1],&map[end-2],true);
        for &s in &map[end-1]{c.cx(s,b[end-1]);}
    }
    for i in(0..work.len()).rev(){let carry=if i==0{prev}else{work[i-1]};unwind_fold_step(c,b[at+i],carry,work[i],&map[at+i]);}
    c.free_vec(&work);
}

/// SQ_HOLD_BOUNDARY forward: the same exact chunked add, but every non-final
/// chunk's carry-out stays live (no hmr, no compare). Returns those wires.
pub(crate) fn direct_add_hold(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId,p:&Plan)->Vec<QubitId>{
    assert_eq!(p.sizes.iter().sum::<usize>(),b.len());let base=c.active_qubits();
    let k=p.sizes.len();let mut held=Vec::new();let mut at=0;let mut prev=incoming;
    for(j,&w)in p.sizes.iter().enumerate(){
        let out=if j+1<k{Some(c.alloc_qubit())}else{None};
        direct_chunk(c,map,b,at,w,prev,out);
        if let Some(q)=out{held.push(q);prev=q;}at+=w;
    }
    assert_eq!(c.active_qubits(),base+held.len() as u32);
    held
}

/// SQ_HOLD_BOUNDARY inverse, called on the complemented accumulator with the
/// forward's plan and map. The complemented add has the same chunk carries as
/// the forward add, so chunk j run with out = held[j] returns it to zero.
/// Chunks run high-to-low so each reads held[j-1] before it is cleared.
pub(crate) fn direct_add_unhold(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId,p:&Plan,held:Vec<QubitId>){
    assert_eq!(p.sizes.iter().sum::<usize>(),b.len());let base=c.active_qubits();
    let k=p.sizes.len();assert_eq!(held.len(),k-1);
    let starts:Vec<usize>=p.sizes.iter().scan(0,|s,&w|{let a=*s;*s+=w;Some(a)}).collect();
    for j in(0..k).rev(){
        let prev=if j==0{incoming}else{held[j-1]};
        let out=if j+1<k{Some(held[j])}else{None};
        direct_chunk(c,map,b,starts[j],p.sizes[j],prev,out);
        if let Some(q)=out{c.release_clean(q);}
    }
    assert_eq!(c.active_qubits()+held.len() as u32,base);
}

pub(crate) fn direct_add_hold_keep(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId,p:&Plan,keep:usize)->(Vec<QubitId>,Vec<QubitId>){
    use super::pingpong::{fold_step,unwind_fold_step};
    assert_eq!(p.sizes.iter().sum::<usize>(),b.len());let base=c.active_qubits();
    let k=p.sizes.len();assert!(k>=2&&keep>=1&&keep<p.sizes[0],"GO-B3: keep must fit chunk 0 carries");
    let w=p.sizes[0];let out=c.alloc_qubit();
    let work=c.alloc_qubits(w-1);
    for i in 0..w-1{let carry=if i==0{incoming}else{work[i-1]};fold_step(c,b[i],carry,work[i],&map[i],false);}
    fold_step(c,b[w-1],work[w-2],out,&map[w-1],true);
    for i in(keep..w-1).rev(){unwind_fold_step(c,b[i],work[i-1],work[i],&map[i]);}
    for i in 0..keep{for &s in &map[i]{c.cx(s,b[i]);}}
    for &q in &work[keep..]{c.free(q);}
    let kept=work[..keep].to_vec();
    let mut held=vec![out];let mut prev=out;let mut at=w;
    for(j,&w)in p.sizes.iter().enumerate().skip(1){
        let o=if j+1<k{Some(c.alloc_qubit())}else{None};
        direct_chunk(c,map,b,at,w,prev,o);
        if let Some(q)=o{held.push(q);prev=q;}at+=w;
    }
    assert_eq!(c.active_qubits(),base+(held.len()+kept.len()) as u32);
    (held,kept)
}

/// GO-B3 inverse of [`direct_add_hold_keep`], on the complemented accumulator.
/// Chunk 0 takes its low carries from `kept` (each bit only gets the carry-in
/// XOR a fold step would apply), then unwinds every carry as usual.
pub(crate) fn direct_add_unhold_keep(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId,p:&Plan,held:Vec<QubitId>,kept:Vec<QubitId>){
    use super::pingpong::{fold_step,unwind_fold_step};
    assert_eq!(p.sizes.iter().sum::<usize>(),b.len());let base=c.active_qubits();
    let k=p.sizes.len();assert_eq!(held.len(),k-1);let keep=kept.len();
    let starts:Vec<usize>=p.sizes.iter().scan(0,|s,&w|{let a=*s;*s+=w;Some(a)}).collect();
    for j in(1..k).rev(){
        let prev=held[j-1];
        let out=if j+1<k{Some(held[j])}else{None};
        direct_chunk(c,map,b,starts[j],p.sizes[j],prev,out);
        if let Some(q)=out{c.release_clean(q);}
    }
    let w=p.sizes[0];let out=held[0];
    let mut work=kept.clone();work.extend(c.alloc_qubits(w-1-keep));
    for i in 0..w-1{let carry=if i==0{incoming}else{work[i-1]};
        if i<keep{c.cx(carry,b[i]);}else{fold_step(c,b[i],carry,work[i],&map[i],false);}}
    fold_step(c,b[w-1],work[w-2],out,&map[w-1],true);
    for i in(0..w-1).rev(){let carry=if i==0{incoming}else{work[i-1]};unwind_fold_step(c,b[i],carry,work[i],&map[i]);}
    c.free_vec(&work);c.release_clean(out);
    assert_eq!(c.active_qubits()+(held.len()+keep) as u32,base);
}

fn strict_square_chunk(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],at:usize,w:usize,prev:QubitId,out:Option<QubitId>)->bool{
    /* Exact plain mapped chunk in any arithmetic phase; outer boundary callbacks stay intact. */let mut target=b[at..at+w].to_vec();let mut rows=map[at..at+w].to_vec();
    if let Some(q)=out{target.push(q);rows.push(Vec::new());}
    super::phase_fit::plain_optional(c,&target,&rows,&vec![false;target.len()],Some(prev),&mut|_,_,_|{})
}

#[cfg(test)]mod direct_transport_tests{
 use super::*;use crate::circuit::{analyze_ops,Op,OperationType};use crate::sim::Simulator;use sha3::{Shake256,digest::{Update,ExtendableOutput,XofReader}};
 struct Words{data:Vec<u8>,pos:usize}impl XofReader for Words{fn read(&mut self,b:&mut[u8]){let end=self.pos+b.len();assert!(end<=self.data.len());b.copy_from_slice(&self.data[self.pos..end]);self.pos=end;}}
 fn draws(ops:&[Op])->usize{ops.iter().filter(|o|matches!(o.kind,OperationType::R|OperationType::Hmr)).count()}
 fn build(n:usize,pattern:usize,mode:usize,adapt:bool)->(Vec<Op>,Vec<QubitId>,Vec<Vec<QubitId>>){
  let mut c=Builder::new();let a=c.alloc_qubits(n);let b=c.alloc_qubits(n);let ci=c.alloc_qubit();let shared=c.alloc_qubit();let guard=c.alloc_bit();assert_eq!(guard.0,0);
  let interface:Vec<_>=a.iter().chain(&b).copied().chain([ci,shared]).collect();c.declare_qubit_register(&interface);
  let rows:Vec<_>=(0..n).map(|i|match pattern{0=>vec![a[i]],1=>if i%2==0{vec![a[i],shared]}else{vec![a[i]]},2=>vec![shared],_=>if i%3==1{vec![]}else{vec![a[i]]}}).collect();
  let w=n/2;let plan=Plan{sizes:vec![w,w],slow:false,extra2:w-1,peak:w};let base=c.active_qubits();
  std::env::set_var("PEBBLE_HARD_CAP",if adapt{(base as usize+w-1).to_string()}else{"1234".into()});
  c.push_condition(guard);let((),peak)=c.r3_peak(|c|match mode{
   3=>{let held=direct_add_hold(c,&rows,&b,ci,&plan);c.x_all(&b);direct_add_unhold(c,&rows,&b,ci,&plan,held);c.x_all(&b);},
   4=>{let(held,kept)=direct_add_hold_keep(c,&rows,&b,ci,&plan,1);c.x_all(&b);direct_add_unhold_keep(c,&rows,&b,ci,&plan,held,kept);c.x_all(&b);},
   _=>{let pending=direct_add_phase_transport(c,&rows,&b,ci,&plan,mode==2||mode==5,&[]);if mode!=0{c.x_all(&b);assert!(direct_add_phase_transport(c,&rows,&b,ci,&plan,false,if mode==2{&pending}else{&[]}).is_empty());c.x_all(&b);}}
  });c.pop_condition();std::env::set_var("PEBBLE_HARD_CAP","1234");
  let wanted=if adapt&&mode!=4{w-1}else{w};assert_eq!(peak,base+wanted as u32,"n={n} pattern={pattern} mode={mode} adapt={adapt}");
  (c.take_ops(),interface,rows)
 }
 fn fixture(n:usize,pattern:usize,mode:usize,guard:u64,probe:Option<usize>){
  let(old,interface,rows)=build(n,pattern,mode,false);let(new,interface2,_)=build(n,pattern,mode,true);assert_eq!(interface,interface2);
  let(nq,nb,_,_)=analyze_ops(old.iter().chain(&new));let starts:Vec<_>=if mode==5{vec![15usize<<n]}else if probe.is_some(){vec![0x36D80]}else{(0..1usize<<(2*n+2)).step_by(64).collect()};
  for start in starts{for ops in[&old,&new]{let nr=draws(ops);let mut bytes=vec![0u8;nr*8];if let Some(p)=probe{for i in 0..nr{let word=if p==usize::MAX||p==i||p==nr{u64::MAX}else{0};bytes[i*8..i*8+8].copy_from_slice(&word.to_le_bytes());}}else{let mut h=Shake256::default();h.update(b"direct-transport-measurements-v1");h.update(&(start as u64).to_le_bytes());h.finalize_xof().read(&mut bytes);}
   let mut rng=Words{data:bytes,pos:0};let mut s=Simulator::new(nq as usize,nb as usize,&mut rng);s.bits[0]=guard;
   for lane in 0..64{for(i,&q)in interface.iter().enumerate(){if(start+lane)>>i&1!=0{s.qubits[q.0 as usize]|=1u64<<lane;}}}let original=s.qubits.clone();s.apply_iter(ops.iter());
   for lane in 0..64{let v=start+lane;let mut av=0usize;for(i,row)in rows.iter().enumerate(){let x=row.iter().fold(0usize,|x,q|x^(v>>interface.iter().position(|r|r==q).unwrap()&1));av|=x<<i;}
    let bv=v>>n&((1<<n)-1);let ci=v>>(2*n)&1;let expected=if mode==0&&guard>>lane&1!=0{(av+bv+ci)&((1<<n)-1)}else{bv};for i in 0..n{assert_eq!(s.qubits[interface[n+i].0 as usize]>>lane&1,(expected>>i&1)as u64,"n={n} pattern={pattern} mode={mode}");}}
   for i in 0..nq as usize{if !interface[n..2*n].iter().any(|q|q.0 as usize==i){assert_eq!(s.qubits[i],original[i]);}}
   if mode==5{assert_ne!(s.phase,0,"deliberate omitted recover must be detected");}else{assert_eq!(s.phase,0,"n={n} pattern={pattern} mode={mode} start={start}");}drop(s);assert_eq!(rng.pos,nr*8);
  }}
 }
 #[test]fn exact_direct_maps_deferred_recovery_and_held_boundaries_with_lower_peak(){
  // One test owns all environment changes; other filters run in separate processes.
  for pattern in 0..4{for mode in 0..4{for guard in[u64::MAX,0xA9563C78F012DE4B]{fixture(8,pattern,mode,guard,None);}}}
  for pattern in 0..4{for mode in 0..5{let old=build(12,pattern,mode,false).0;let new=build(12,pattern,mode,true).0;let nr=draws(&old).max(draws(&new));for probe in 0..nr+2{for guard in[0u64,u64::MAX,0xAA55AA55AA55AA55]{fixture(12,pattern,mode,guard,Some(probe));}}}}
  fixture(8,0,5,u64::MAX,Some(usize::MAX));
 }
}
