//! Exact phase-pebbled affine addition, with optional paused consumers.
//! At a pause: dropped carry views are None and their target sums are already
//! written; other target bits retain their original values. Consumers must
//! restore every data/carry/source value they touch. Birth hooks may add phase
//! using the true carry value, and must preserve that value.
use super::builder::Builder;
use crate::circuit::QubitId;
use std::collections::BTreeSet;
fn on(c:&mut Builder,row:&[QubitId],one:bool,ci:QubitId)->QubitId{let q=if row.is_empty(){ci}else{let q=row[0];for &r in &row[1..]{c.cx(r,q);}c.cx(ci,q);q};if one{c.x(q);}q}
fn off(c:&mut Builder,row:&[QubitId],one:bool,ci:QubitId){let q=row.first().copied().unwrap_or(ci);if one{c.x(q);}if !row.is_empty(){c.cx(ci,q);for &r in row[1..].iter().rev(){c.cx(r,q);}}}
fn carry(c:&mut Builder,a:QubitId,row:&[QubitId],one:bool,ci:QubitId)->QubitId{c.cx(ci,a);let v=on(c,row,one,ci);let out=c.alloc_qubit();c.ccx(a,v,out);off(c,row,one,ci);c.cx(ci,out);c.cx(ci,a);out}
fn erase(c:&mut Builder,out:QubitId,a:QubitId,row:&[QubitId],one:bool,ci:QubitId){c.cx(ci,out);c.cx(ci,a);let v=on(c,row,one,ci);let bit=c.alloc_bit();c.hmr(out,bit);c.cz_if(a,v,bit);c.free_bit(bit);c.release_clean(out);off(c,row,one,ci);c.cx(ci,a);}
pub(super) fn valid_mode(acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:QubitId,drops:&[usize],paused:bool)->bool{
    let n=acc.len();if n<3||rows.len()!=n||ones.len()!=n{return false;}let m=n-2+usize::from(paused);if drops.len()>m{return false;}let room=m-drops.len();
    for(j,&i)in drops.iter().enumerate(){if i==0||i+1>m||i+1-j>room||j>0&&drops[j-1]+1>=i{return false;}}
    let mut target=BTreeSet::from([cin.0]);if !acc.iter().all(|q|target.insert(q.0)){return false;}
    rows.iter().all(|r|{let mut seen=BTreeSet::new();r.iter().all(|q|!target.contains(&q.0)&&seen.insert(q.0))})
}
pub(super) fn add(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:QubitId,drops:&[usize])->bool{
    run(c,acc,rows,ones,cin,drops,false,&mut|_,_,_|{},None,None)
}
pub(super) fn add_with_hook(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:QubitId,drops:&[usize],hook:&mut dyn FnMut(&mut Builder,usize,QubitId))->bool{
    run(c,acc,rows,ones,cin,drops,false,hook,None,None)
}
pub(super) fn with_pause(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:QubitId,drops:&[usize],hook:&mut dyn FnMut(&mut Builder,usize,QubitId),mid:&mut dyn FnMut(&mut Builder,&[Option<QubitId>]))->bool{
    run(c,acc,rows,ones,cin,drops,true,hook,Some(mid),None)
}
fn run(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:QubitId,drops:&[usize],paused:bool,hook:&mut dyn FnMut(&mut Builder,usize,QubitId),mid:Option<&mut dyn FnMut(&mut Builder,&[Option<QubitId>])>,desired:Option<bool>)->bool{
    if !valid_mode(acc,rows,ones,cin,drops,paused){return false;}let n=acc.len();let m=n-2+usize::from(paused);let mut cc=vec![None;n];cc[0]=Some(cin);
    for i in 0..m{
        let ci=cc[i].unwrap();let q=carry(c,acc[i],&rows[i],ones[i],ci);cc[i+1]=Some(q);hook(c,i+1,q);
        if drops.contains(&i){for &q in &rows[i]{c.cx(q,acc[i]);}if ones[i]{c.x(acc[i]);}c.cx(ci,acc[i]);erase(c,cc[i].take().unwrap(),acc[i-1],&rows[i-1],ones[i-1],cc[i-1].unwrap());}
    }
    if let Some(desired)=desired{known_phase(c,acc,rows,ones,cc[m].unwrap(),desired);}else if let Some(mid)=mid{mid(c,&cc);}else{
        let i=n-2;let ci=cc[i].unwrap();c.cx(ci,acc[i]);let v=on(c,&rows[i],ones[i],ci);c.ccx(acc[i],v,acc[n-1]);off(c,&rows[i],ones[i],ci);c.cx(ci,acc[n-1]);c.cx(ci,acc[i]);
    }
    for i in(0..n).rev(){
        if desired.is_some()&&i==n-1{continue;}
        if drops.contains(&i){continue;}
        for &q in &rows[i]{c.cx(q,acc[i]);}if ones[i]{c.x(acc[i]);}if i!=n-1||paused{c.cx(cc[i].unwrap(),acc[i]);}
        if i>0&&(i<n-1||paused){
            let out=cc[i].unwrap();
            if drops.contains(&(i-1)){
                let bit=c.alloc_bit();c.hmr(out,bit);c.release_clean(out);c.push_condition(bit);c.x(acc[i-1]);
                assert!(super::phase_fusion::pair(c,acc[i-2],acc[i-1],cc[i-2].unwrap(),&rows[i-2],ones[i-2],&rows[i-1],ones[i-1],false));
                c.x(acc[i-1]);c.pop_condition();c.free_bit(bit);
            }else{erase(c,out,acc[i-1],&rows[i-1],ones[i-1],cc[i-1].unwrap());}
        }
    }true
}

#[cfg(test)]mod tests{
    use super::*;use crate::circuit::{analyze_ops,Op,OperationType};use crate::sim::Simulator;use sha3::digest::XofReader;
    struct Words{data:Vec<u8>,pos:usize}impl XofReader for Words{fn read(&mut self,b:&mut[u8]){let end=self.pos+b.len();assert!(end<=self.data.len());b.copy_from_slice(&self.data[self.pos..end]);self.pos=end;}}
    fn rng(words:&[u64])->Words{Words{data:words.iter().flat_map(|w|w.to_le_bytes()).collect(),pos:0}}
    fn draws(ops:&[Op])->usize{ops.iter().filter(|o|matches!(o.kind,OperationType::R|OperationType::Hmr)).count()}
    fn put<R:XofReader>(s:&mut Simulator<'_,R>,q:QubitId,lane:usize,x:usize){if x&1!=0{s.qubits[q.0 as usize]|=1u64<<lane;}}
    fn schedules(n:usize,paused:bool)->Vec<Vec<usize>>{
        let m=n-2+usize::from(paused);let mut result=Vec::new();
        for mask in 1usize..1<<(m-1){let ds:Vec<_>=(1..m).filter(|&i|mask>>(i-1)&1!=0).collect();let room=m-ds.len();if ds.iter().enumerate().all(|(j,&i)|i+1-j<=room&&(j==0||ds[j-1]+1<i)){result.push(ds);}}
        result
    }
    fn fixture(n:usize,pattern:usize,drops:&[usize],paused:bool,inverse:bool,hooked:bool,probe:Option<usize>){
        assert!(!inverse||!paused&&!hooked);let mut c=Builder::new();let source=c.alloc_qubits(n);let target=c.alloc_qubits(n);let ci=c.alloc_qubit();let shared=c.alloc_qubit();
        let interface:Vec<_>=source.iter().chain(target.iter()).copied().chain([ci,shared]).collect();c.declare_qubit_register(&interface);
        let rows:Vec<Vec<QubitId>>=(0..n).map(|i|match pattern{0=>vec![shared],1=>if i%3==0{vec![]}else{vec![source[i],shared]},2=>vec![source[i]],_=>if i==1||i==n-1{vec![]}else{vec![source[i]]}}).collect();
        let ones:Vec<_>=(0..n).map(|i|pattern==2&&i%3==1||pattern==3&&i==1).collect();let m=n-2+usize::from(paused);let active=c.active_qubits();
        let mut execute=|c:&mut Builder|{
            let mut hook=|c:&mut Builder,_i:usize,q:QubitId|{if hooked{c.cz(q,shared);}};
            if paused{
                let mut consumer=|c:&mut Builder,cc:&[Option<QubitId>]|{
                    let flip=|c:&mut Builder|{for i in 0..n{if let Some(q)=cc[i]{for &s in &rows[i]{c.cx(s,target[i]);}if ones[i]{c.x(target[i]);}c.cx(q,target[i]);}}};
                    flip(c);c.cz(target[1],shared);c.cz(target[n-1],target[0]);flip(c);
                };
                assert!(with_pause(c,&target,&rows,&ones,ci,drops,&mut hook,&mut consumer));
            }else{assert!(add_with_hook(c,&target,&rows,&ones,ci,drops,&mut hook));}
        };
        let((),peak)=c.r3_peak(|c|{execute(c);if inverse{c.x_all(&target);execute(c);c.x_all(&target);}});
        assert_eq!(peak,active+(m-drops.len())as u32);let ops=c.take_ops();let(nq,nb,_,_)=analyze_ops(ops.iter());assert_eq!(nq as usize,interface.len()+m-drops.len());
        let copies=if inverse{2}else{1};assert_eq!(ops.iter().filter(|o|o.kind==OperationType::CCX).count(),(n-1)*copies);let nr=draws(&ops);assert_eq!(nr,m*copies);
        let ranks:Vec<_>=drops.iter().map(|&j|if rows[j-1].is_empty()||rows[j].is_empty()||rows[j-1]==rows[j]{1usize}else{2}).collect();assert_eq!(ops.iter().filter(|o|o.kind==OperationType::CCZ).count(),ranks.iter().sum::<usize>()*copies);
        let starts:Vec<_>=if probe.is_some(){vec![0x6F3C0]}else{(0..1usize<<(2*n+2)).step_by(64).collect()};
        for start in starts{
            let words:Vec<_>=(0..nr).map(|j|match probe{Some(p)=>if p==j||p==nr{u64::MAX}else{0},None=>0xD1B54A32D192ED03u64.wrapping_mul((start+j+1)as u64).rotate_left(j as u32)}).collect();let mut random=rng(&words);
            let mut expected_t=(64*(n-1)*copies)as u64;for copy in 0..copies{for(j,&d)in drops.iter().enumerate(){let i=d+1;let ordinal=drops.len()+(m-i)-drops.iter().filter(|&&x|x>i).count();expected_t+=ranks[j]as u64*words[copy*m+ordinal].count_ones()as u64;}}
            let mut s=Simulator::new(nq as usize,nb as usize,&mut random);for lane in 0..64{for(i,&q)in interface.iter().enumerate(){put(&mut s,q,lane,(start+lane)>>i);}}let original=s.qubits.clone();s.apply_iter(ops.iter());let mut expected_phase=0u64;
            for lane in 0..64{let value=start+lane;let mut av=0usize;for(i,row)in rows.iter().enumerate(){let bit=row.iter().fold(usize::from(ones[i]),|x,q|x^(value>>interface.iter().position(|r|r==q).unwrap()&1));av|=bit<<i;}
                let bv=value>>n&((1<<n)-1);let cin=value>>(2*n)&1;let result=(av+bv+cin)&((1<<n)-1);let wanted=if inverse{bv}else{result};
                for i in 0..n{assert_eq!(s.qubits[target[i].0 as usize]>>lane&1,(wanted>>i&1)as u64,"n={n} pattern={pattern} drops={drops:?} paused={paused}");}
                let shared=value>>(2*n+1)&1;let mut phase=0usize;if hooked{for k in 1..=m{let mask=(1<<k)-1;phase^=(((av&mask)+(bv&mask)+cin)>>k)&shared;}}
                if paused{phase^=(result>>1&1)&shared;phase^=(result>>(n-1)&1)&(result&1);}if phase&1!=0{expected_phase|=1u64<<lane;}}
            for i in 0..nq as usize{if !target.iter().any(|q|q.0 as usize==i){assert_eq!(s.qubits[i],original[i]);}}assert_eq!(s.phase,expected_phase);assert_eq!(s.stats.toffoli_gates as u64,expected_t);drop(s);assert_eq!(random.pos,nr*8);
        }
    }
    #[test]fn every_admissible_small_schedule_and_paused_sum_consumer_with_birth_phases(){for n in 5usize..=7{for paused in[false,true]{for drops in schedules(n,paused){for pattern in 0..4{fixture(n,pattern,&drops,paused,false,true,None);}}}}}
    #[test]fn every_rng_coefficient_for_arbitrary_drops_callbacks_and_inverse(){for paused in[false,true]{for inverse in[false,true]{if paused&&inverse{continue;}for hooked in[false,true]{if inverse&&hooked{continue;}let m=7+usize::from(paused);let nr=m*if inverse{2}else{1};for probe in 0..nr+2{for drops in[vec![1],vec![2],vec![1,3],vec![2,4],vec![1,3,5]]{for pattern in 0..4{fixture(9,pattern,&drops,paused,inverse,hooked,Some(probe));}}}}}}}
    #[test]fn invalid_alias_adjacent_or_prefix_overflow_rejects_before_emission(){let mut c=Builder::new();let a=c.alloc_qubits(7);let b=c.alloc_qubits(7);let ci=c.alloc_qubit();let op=c.op_count();let mut rows:Vec<_>=a.iter().map(|&q|vec![q]).collect();assert!(!add(&mut c,&b,&rows,&[false;7],ci,&[1,2]));assert!(!add(&mut c,&b,&rows,&[false;7],ci,&[3,5]));rows[2]=vec![b[1]];assert!(!with_pause(&mut c,&b,&rows,&[false;7],ci,&[1],&mut|_,_,_|{},&mut|_,_|{}));assert_eq!(op,c.op_count());}
}
/// Same measured known-top-output channel as modular::terminal_step_known.
/// The top bit is forced even on inputs that violate its arithmetic promise.
pub(super) fn known_top(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:QubitId,drops:&[usize],desired:bool)->bool{
    known_top_with_hook(c,acc,rows,ones,cin,drops,desired,&mut|_,_,_|{})
}
fn known_phase(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],ci:QubitId,desired:bool){
    let n=acc.len();let bit=c.alloc_bit();c.hmr(acc[n-1],bit);if desired{c.x(acc[n-1]);}
    c.push_condition(bit);
    // desired XOR a_top XOR MAJ(a_pen,b_pen,ci).
    if desired^ones[n-1]{c.cz(ci,ci);c.x(ci);c.cz(ci,ci);c.x(ci);}
    for &q in &rows[n-1]{c.cz(q,q);}
    for &q in &rows[n-2]{c.cz(q,acc[n-2]);c.cz(q,ci);}
    if ones[n-2]{c.cz(acc[n-2],acc[n-2]);c.cz(ci,ci);}
    c.cz(acc[n-2],ci);c.pop_condition();c.free_bit(bit);
}

pub(super) fn known_top_with_hook(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:QubitId,drops:&[usize],desired:bool,hook:&mut dyn FnMut(&mut Builder,usize,QubitId))->bool{
 run(c,acc,rows,ones,cin,drops,false,hook,None,Some(desired))
}
