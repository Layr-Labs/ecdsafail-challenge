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
    use super::pingpong::{fold_step,unwind_fold_step};
    assert_eq!(p.sizes.iter().sum::<usize>(),b.len());let base=c.active_qubits();
    let mut at=0;let mut prev=incoming;let mut stages=Vec::new();
    for(j,&w)in p.sizes.iter().enumerate(){let last=j+1==p.sizes.len();let end=at+w;
        let out=if last{None}else{Some(c.alloc_qubit())};
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
        if let Some(q)=out{
            for &(boundary,bit)in recover{if boundary==end{c.z_if(q,bit);c.free_bit(bit);}}
            stages.push((at,end,prev,q));prev=q;
        }at=end;
    }
    assert!(recover.iter().all(|(hi,_)|stages.iter().any(|(_,end,_,_)|hi==end)));
    let mut pending=Vec::new();
    for(lo,hi,cin,q)in stages.into_iter().rev(){let m=c.alloc_bit();c.hmr(q,m);c.release_clean(q);
        if defer{pending.push((hi,m));}else{c.push_condition(m);mapped_compare(c,&map[lo..hi],&b[lo..hi],cin);c.pop_condition();c.free_bit(m);}
    }
    assert_eq!(c.active_qubits(),base);
    pending
}
