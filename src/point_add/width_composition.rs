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

/// Plan for a preserved, caller-owned incoming carry, which replaces the
/// zero-initialized carry otherwise needed by a one-block in-place addition.
pub(crate) fn plan_with_carry(n:usize,room:usize)->Option<Plan> {
    if room==1 && n>0 {
        Some(Plan{sizes:vec![n],slow:true,extra2:2*n,peak:1})
    } else {
        plan(n,room)
    }
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
    low_workspace_add(c,a,b,incoming,Some(out),None);
}

/// Ancilla-free wrapped addition. The source MSB serves as a dirty carry;
/// controlled swaps propagate it and the surrounding XOR frames cancel it.
pub(crate) fn add_wrapped(c:&mut Builder,a:&[QubitId],b:&[QubitId]) {
    assert!(!a.is_empty() && a.len()==b.len());
    if a.len()==1 {c.cx(a[0],b[0]);return;}
    let last=a.len()-1;
    let carry=a[last];
    let frame=|c:&mut Builder| {
        for &q in a[..last].iter().chain(b) {c.cx(carry,q);}
    };
    frame(c);
    for i in 0..last {
        c.cx(carry,b[i]);
        super::pingpong::cswap(c,b[i],carry,a[i]);
    }
    c.cx(carry,b[last]);
    for i in (0..last).rev() {
        super::pingpong::cswap(c,b[i],carry,a[i]);
        c.cx(a[i],b[i]);
    }
    frame(c);
}

/// Wrapped MAJ/UMA addition using the live incoming carry, with no new qubits.
pub(crate) fn add_wrapped_with_carry(
    c: &mut Builder, a: &[QubitId], b: &[QubitId], incoming: QubitId,
    deferred: Option<(usize, BitId)>,
) {
    low_workspace_add(c,a,b,Some(incoming),None,deferred);
}

fn low_workspace_add(
    c: &mut Builder, a: &[QubitId], b: &[QubitId], incoming: Option<QubitId>,
    out: Option<QubitId>, mut deferred: Option<(usize, BitId)>,
) {
    assert!(!a.is_empty() && a.len()==b.len());
    let seed=incoming.unwrap_or_else(||c.alloc_qubit());
    let carries = if out.is_some() { a.len() } else { a.len()-1 };
    for i in 0..carries {
        let p=if i==0{seed}else{a[i-1]};
        c.cx(a[i],b[i]);c.cx(a[i],p);c.ccx(p,b[i],a[i]);
        if deferred.as_ref().is_some_and(|(index,_)| *index==i) {
            let (_,bit)=deferred.take().unwrap();
            c.z_if(a[i],bit);c.free_bit(bit);
        }
    }
    if let Some(out)=out {
        c.cx(a[a.len()-1],out);
    } else {
        let last=a.len()-1;
        c.cx(a[last],b[last]);
        c.cx(if last==0{seed}else{a[last-1]},b[last]);
    }
    for i in (0..carries).rev(){let p=if i==0{seed}else{a[i-1]};c.ccx(p,b[i],a[i]);c.cx(a[i],p);c.cx(p,b[i]);}
    if incoming.is_none(){c.release_clean(seed);}
    assert!(deferred.is_none(), "deferred phase did not name a low-workspace carry");
}

pub(crate) fn add(c:&mut Builder,a:&[QubitId],b:&[QubitId],p:&Plan)->QubitId{
    add_with_carry(c,a,b,None,p)
}

/// Same exact adder with a live, preserved incoming carry. Its wire is part
/// of the caller's base, so the existing workspace plan is unchanged.
pub(crate) fn add_with_carry(c:&mut Builder,a:&[QubitId],b:&[QubitId],initial:Option<QubitId>,p:&Plan)->QubitId{
    assert_eq!(a.len(),b.len());assert_eq!(p.sizes.iter().sum::<usize>(),a.len());
    assert!(!(p.slow&&p.peak==1)||initial.is_some(),"one-workspace plan requires a live incoming carry");
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

fn mapped_step(c:&mut Builder,b:QubitId,previous:Option<QubitId>,carry:QubitId,map:&[QubitId],finish:bool) {
    if let Some(previous)=previous {
        super::pingpong::fold_step(c,b,previous,carry,map,finish);
    } else if !map.is_empty() {
        super::pingpong::with_selector_xor(c,map,b,|c,source|{
            c.ccx(source,b,carry);
            if finish {c.cx(source,b);}
        });
    }
}

fn mapped_unwind(c:&mut Builder,b:QubitId,previous:Option<QubitId>,carry:QubitId,map:&[QubitId]) {
    if let Some(previous)=previous {
        super::pingpong::unwind_fold_step(c,b,previous,carry,map);
    } else {
        let measured=c.alloc_bit();c.hmr(carry,measured);
        if !map.is_empty() {
            super::pingpong::with_selector_xor(c,map,b,|c,source|{
                c.cz_if(source,b,measured);c.cx(source,b);
            });
        }
        c.free_bit(measured);
    }
}

fn mapped_compare(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:Option<QubitId>){
    use super::pingpong::with_selector_xor;
    let n=b.len();let carries=c.alloc_qubits(n-1);c.x_all(b);
    for i in 0..n-1{let prev=if i==0{incoming}else{Some(carries[i-1])};mapped_step(c,b[i],prev,carries[i],&map[i],false);}
    let prev=if n==1{incoming}else{Some(carries[n-2])};
    if let Some(prev)=prev {
        if map[n-1].is_empty(){c.cz(b[n-1],prev);}else{
            with_selector_xor(c,&map[n-1],prev,|c,s|{c.cz(b[n-1],s);c.cz(b[n-1],prev);c.cz(s,prev);});
        }
    } else if !map[n-1].is_empty() {
        with_selector_xor(c,&map[n-1],b[n-1],|c,s|c.cz(b[n-1],s));
    }
    for i in (0..n-1).rev(){let prev=if i==0{incoming}else{Some(carries[i-1])};
        if prev.is_none() {
            let m=c.alloc_bit();c.hmr(carries[i],m);
            if !map[i].is_empty(){with_selector_xor(c,&map[i],b[i],|c,s|c.cz_if(s,b[i],m));}
            c.free_bit(m);continue;
        }
        let prev=prev.unwrap();
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

pub(crate) fn direct_add_zero(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],p:&Plan){
    assert!(direct_add_optional_carry(c,map,b,None,p,false,&[]).is_empty());
}

/// Optionally retain classical measurement outcomes instead of comparing to
/// repair boundary phases. A matching inverse recreates the SAME carries and
/// applies these deferred Z corrections before normal exact cleanup.
pub(crate) fn direct_add_phase_transport(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:QubitId,p:&Plan,defer:bool,recover:&[(usize,BitId)])->Vec<(usize,BitId)>{
    direct_add_optional_carry(c,map,b,Some(incoming),p,defer,recover)
}

fn direct_add_optional_carry(c:&mut Builder,map:&[Vec<QubitId>],b:&[QubitId],incoming:Option<QubitId>,p:&Plan,defer:bool,recover:&[(usize,BitId)])->Vec<(usize,BitId)>{
    assert_eq!(p.sizes.iter().sum::<usize>(),b.len());let base=c.active_qubits();
    let mut at=0;let mut prev=incoming;let mut stages=Vec::new();
    for(j,&w)in p.sizes.iter().enumerate(){let last=j+1==p.sizes.len();let end=at+w;
        let out=if last{None}else{Some(c.alloc_qubit())};
        let work=c.alloc_qubits(if last{w.saturating_sub(2)}else{w-1});
        for i in 0..work.len(){let carry=if i==0{prev}else{Some(work[i-1])};mapped_step(c,b[at+i],carry,work[i],&map[at+i],false);}
        let carry=work.last().copied().or(prev);
        if let Some(q)=out{mapped_step(c,b[end-1],carry,q,&map[end-1],true);}else if w==1{
            if let Some(prev)=prev{c.cx(prev,b[at]);}for &s in &map[at]{c.cx(s,b[at]);}
        }else{
            mapped_step(c,b[end-2],carry,b[end-1],&map[end-2],true);
            for &s in &map[end-1]{c.cx(s,b[end-1]);}
        }
        for i in(0..work.len()).rev(){let carry=if i==0{prev}else{Some(work[i-1])};mapped_unwind(c,b[at+i],carry,work[i],&map[at+i]);}
        c.free_vec(&work);
        if let Some(q)=out{
            for &(boundary,bit)in recover{if boundary==end{c.z_if(q,bit);c.free_bit(bit);}}
            stages.push((at,end,prev,q));prev=Some(q);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::{digest::ExtendableOutput, Shake256};

    #[test]
    #[should_panic = "one-workspace plan requires a live incoming carry"]
    fn one_workspace_plan_rejects_a_missing_carry() {
        let mut circ=Builder::new();
        let a=circ.alloc_qubits(3);
        let b=circ.alloc_qubits(3);
        let plan=plan_with_carry(3,1).unwrap();
        add_with_carry(&mut circ,&a,&b,None,&plan);
    }

    #[test]
    fn live_incoming_carry_needs_only_one_workspace_qubit_for_overflow() {
        for width in 1usize..=5 {
            let plan=plan_with_carry(width,1).unwrap();
            assert_eq!(plan.peak,1);
            let mut circ=Builder::new();
            let a=circ.alloc_qubits(width);
            let b=circ.alloc_qubits(width);
            let incoming=circ.alloc_qubit();
            let base=circ.active_qubits();
            let outgoing=add_with_carry(&mut circ,&a,&b,Some(incoming),&plan);
            assert_eq!(circ.active_qubits(),base+1);
            let ops=circ.take_ops();
            let(nq,nb,_,_)=analyze_ops(ops.iter());
            assert_eq!(nq,base as u64+1);
            let mask=(1usize<<width)-1;
            let assignments=1usize<<(2*width+1);
            for start in (0..assignments).step_by(64) {
                let mut rng=Shake256::default().finalize_xof();
                let mut sim=Simulator::new(nq as usize,nb as usize,&mut rng);
                let mut sums=vec![0;width+1];
                for lane in 0..64.min(assignments-start) {
                    let value=start+lane;let x=value&mask;let y=(value>>width)&mask;let cin=value>>(2*width);
                    for bit in 0..width {
                        sim.qubits[a[bit].0 as usize]|=(((x>>bit)&1)as u64)<<lane;
                        sim.qubits[b[bit].0 as usize]|=(((y>>bit)&1)as u64)<<lane;
                    }
                    sim.qubits[incoming.0 as usize]|=(cin as u64)<<lane;
                    let sum=x+y+cin;
                    for bit in 0..=width{sums[bit]|=(((sum>>bit)&1)as u64)<<lane;}
                }
                let mut expected=sim.qubits.clone();
                for bit in 0..width{expected[b[bit].0 as usize]=sums[bit];}
                expected[outgoing.0 as usize]=sums[width];
                sim.apply_iter(ops.iter());
                assert_eq!(sim.qubits,expected,"width={width}");
                assert_eq!(sim.phase,0);
            }
        }
    }

    #[test]
    fn ancilla_free_adder_preserves_source_with_linear_toffoli_cost() {
        for width in 1usize..=7 {
            let mut circ=Builder::new();
            let a=circ.alloc_qubits(width);
            let b=circ.alloc_qubits(width);
            let base=circ.active_qubits();
            add_wrapped(&mut circ,&a,&b);
            assert_eq!(circ.active_qubits(),base);
            let ops=circ.take_ops();
            let(nq,nb,_,_)=analyze_ops(ops.iter());
            assert_eq!(nq,base as u64);
            assert_eq!(ops.iter().filter(|op|op.kind==crate::circuit::OperationType::CCX).count(),2*width-2);
            let mask=(1usize<<width)-1;
            let assignments=1usize<<(2*width);
            for start in (0..assignments).step_by(64) {
                let mut rng=Shake256::default().finalize_xof();
                let mut sim=Simulator::new(nq as usize,nb as usize,&mut rng);
                let mut sums=vec![0;width];
                for lane in 0..64.min(assignments-start) {
                    let value=start+lane;let x=value&mask;let y=value>>width;
                    let sum=(x+y)&mask;
                    for bit in 0..width {
                        sim.qubits[a[bit].0 as usize]|=(((x>>bit)&1)as u64)<<lane;
                        sim.qubits[b[bit].0 as usize]|=(((y>>bit)&1)as u64)<<lane;
                        sums[bit]|=(((sum>>bit)&1)as u64)<<lane;
                    }
                }
                let mut expected=sim.qubits.clone();
                for bit in 0..width{expected[b[bit].0 as usize]=sums[bit];}
                sim.apply_iter(ops.iter());
                assert_eq!(sim.qubits,expected,"width={width}");
                assert_eq!(sim.phase,0);
            }
        }
    }

    #[test]
    fn zero_carry_mapped_addition_needs_no_separate_initial_carry() {
        for width in 1..=7 {
            for room in 0..=width {
                let Some(plan)=direct_plan(width,room) else {continue;};
                for pattern in 0..4 {
                    let mut circ=Builder::new();
                    let selectors=circ.alloc_qubits(3);
                    let b=circ.alloc_qubits(width);
                    let map:Vec<Vec<QubitId>>=(0..width).map(|bit|{
                        let mask=match pattern {0=>0,1=>1,2=>1<<(bit%3),_=>bit%8};
                        selectors.iter().enumerate().filter_map(|(i,&q)|(mask&(1<<i)!=0).then_some(q)).collect()
                    }).collect();
                    let base=circ.active_qubits();
                    direct_add_zero(&mut circ,&map,&b,&plan);
                    assert_eq!(circ.active_qubits(),base);
                    let ops=circ.take_ops();
                    let(nq,nb,_,_)=analyze_ops(ops.iter());
                    assert!(nq.saturating_sub(base as u64)<=room as u64);
                    let limit=1usize<<width;
                    for start in (0..8*limit).step_by(64) {
                        let mut rng=Shake256::default().finalize_xof();
                        let mut sim=Simulator::new((nq as usize).max(base as usize),nb as usize,&mut rng);
                        let mut sums=vec![0;width];
                        for lane in 0..64.min(8*limit-start) {
                            let value=start+lane;let control=value/limit;let old=value%limit;
                            let source:usize=map.iter().enumerate().map(|(bit,terms)|{
                                let set=terms.iter().fold(0usize,|parity,q|parity^((control>>q.0)&1));
                                set<<bit
                            }).sum();
                            let sum=(old+source)&(limit-1);
                            for i in 0..3 {sim.qubits[i]|=(((control>>i)&1)as u64)<<lane;}
                            for i in 0..width {
                                sim.qubits[b[i].0 as usize]|=(((old>>i)&1)as u64)<<lane;
                                sums[i]|=(((sum>>i)&1)as u64)<<lane;
                            }
                        }
                        let mut expected=sim.qubits.clone();
                        for i in 0..width{expected[b[i].0 as usize]=sums[i];}
                        sim.apply_iter(ops.iter());
                        assert_eq!(sim.qubits,expected,"width={width}, room={room}, pattern={pattern}");
                        assert_eq!(sim.phase,0);
                    }
                }
            }
        }
    }

    #[test]
    fn wrapped_add_uses_no_qubits_and_preserves_deferred_carry_phase() {
        for width in 1..=6 {
            for phase_at in (0..width-1).map(Some).chain([None]) {
                let mut circ = Builder::new();
                let a = circ.alloc_qubits(width);
                let b = circ.alloc_qubits(width);
                let incoming = circ.alloc_qubit();
                let deferred = phase_at.map(|index| (index, circ.alloc_bit()));
                let base = circ.active_qubits();
                add_wrapped_with_carry(&mut circ, &a, &b, incoming, deferred);
                assert_eq!(circ.active_qubits(), base);
                let ops = circ.take_ops();
                let (nq, nb, _, _) = analyze_ops(ops.iter());
                assert_eq!(nq, base as u64);
                let mask = (1usize << width) - 1;
                let assignments = 1usize << (2 * width + 1);
                for start in (0..assignments).step_by(64) {
                    let mut rng = Shake256::default().finalize_xof();
                    let mut sim = Simulator::new(nq as usize, (nb as usize).max(1), &mut rng);
                    sim.bits[0] = u64::MAX;
                    let mut sums = vec![0; width];
                    let mut phase = 0;
                    for lane in 0..64.min(assignments-start) {
                        let assignment = start+lane;
                        let x = assignment & mask;
                        let y = (assignment >> width) & mask;
                        let carry = (assignment >> (2*width)) & 1;
                        let sum = x+y+carry;
                        for bit in 0..width {
                            sim.qubits[a[bit].0 as usize] |= (((x>>bit)&1) as u64)<<lane;
                            sim.qubits[b[bit].0 as usize] |= (((y>>bit)&1) as u64)<<lane;
                            sums[bit] |= (((sum>>bit)&1) as u64)<<lane;
                        }
                        sim.qubits[incoming.0 as usize] |= (carry as u64)<<lane;
                        if let Some(index)=phase_at {
                            let low_mask=(1usize<<(index+1))-1;
                            phase |= u64::from((x&low_mask)+(y&low_mask)+carry>low_mask)<<lane;
                        }
                    }
                    let mut expected=sim.qubits.clone();
                    for bit in 0..width {expected[b[bit].0 as usize]=sums[bit];}
                    sim.apply_iter(ops.iter());
                    assert_eq!(sim.qubits,expected,"width={width}, phase={phase_at:?}");
                    assert_eq!(sim.phase,phase,"width={width}, phase={phase_at:?}");
                }
            }
        }
    }
}
