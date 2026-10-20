//! Exact zero-carry adapter. Complete bit0 with its carry held, then use the
//! tested live-carry primitive above it. The low carry is erased from the
//! completed low sum. No extra CCX or HMR relative to the ordinary adder.
use super::builder::Builder;use crate::circuit::{QubitId,NO_QUBIT};use std::collections::BTreeSet;
pub(super) fn valid(acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],drops:&[usize])->bool{
    if acc.len()<4||rows.len()!=acc.len()||ones.len()!=acc.len()||rows[0].is_empty(){return false;}
    let mut target=BTreeSet::from([NO_QUBIT.0]);if !acc.iter().all(|q|target.insert(q.0)){return false;}
    if !rows.iter().all(|r|{let mut seen=BTreeSet::new();r.iter().all(|q|!target.contains(&q.0)&&seen.insert(q.0))}){return false;}
    // Sentinel used only for admission; no operation is emitted on it.
    super::phase_pebble::valid_mode(&acc[1..],&rows[1..],&ones[1..],NO_QUBIT,drops,false)
}
pub(super) fn add(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],drops:&[usize],hook:&mut dyn FnMut(&mut Builder,usize,QubitId))->bool{
    if !valid(acc,rows,ones,drops){return false;}let row=&rows[0];let q=row[0];for &r in &row[1..]{c.cx(r,q);}if ones[0]{c.x(q);}
    let carry=c.alloc_qubit();c.ccx(q,acc[0],carry);if ones[0]{c.x(q);}for &r in row[1..].iter().rev(){c.cx(r,q);}hook(c,1,carry);
    for &r in row{c.cx(r,acc[0]);}if ones[0]{c.x(acc[0]);}
    assert!(super::phase_pebble::add_with_hook(c,&acc[1..],&rows[1..],&ones[1..],carry,drops,&mut|c,i,q|hook(c,i+1,q)));
    let bit=c.alloc_bit();c.hmr(carry,bit);c.x(acc[0]);for &r in row{c.cz_if(r,acc[0],bit);}if ones[0]{c.z_if(acc[0],bit);}c.x(acc[0]);c.free_bit(bit);c.release_clean(carry);true
}

#[cfg(test)]mod tests{
    use super::*;use crate::circuit::{analyze_ops,Op,OperationType};use crate::sim::Simulator;use sha3::digest::XofReader;
    struct Words{data:Vec<u8>,pos:usize}impl XofReader for Words{fn read(&mut self,b:&mut[u8]){let end=self.pos+b.len();assert!(end<=self.data.len());b.copy_from_slice(&self.data[self.pos..end]);self.pos=end;}}
    fn rng(words:&[u64])->Words{Words{data:words.iter().flat_map(|w|w.to_le_bytes()).collect(),pos:0}}
    fn draws(ops:&[Op])->usize{ops.iter().filter(|o|matches!(o.kind,OperationType::R|OperationType::Hmr)).count()}
    fn put<R:XofReader>(s:&mut Simulator<'_,R>,q:QubitId,lane:usize,x:usize){if x&1!=0{s.qubits[q.0 as usize]|=1u64<<lane;}}
    fn fixture(n:usize,pattern:usize,drops:&[usize],inverse:bool,hooked:bool,guard:u64,probe:Option<usize>){
        let mut c=Builder::new();let source=c.alloc_qubits(n);let target=c.alloc_qubits(n);let shared=c.alloc_qubit();let bit=c.alloc_bit();let interface:Vec<_>=source.iter().chain(target.iter()).copied().chain([shared]).collect();c.declare_qubit_register(&interface);
        let rows:Vec<Vec<QubitId>>=(0..n).map(|i|match pattern{0=>vec![shared],1=>vec![source[i],shared],2=>vec![source[i]],_=>if i==1||i==n-1{vec![]}else{vec![source[i]]}}).collect();
        let ones:Vec<_>=(0..n).map(|i|pattern==2&&i%3==0||pattern==3&&i==1).collect();let mut execute=|c:&mut Builder|{assert!(add(c,&target,&rows,&ones,drops,&mut|c,_,q|if hooked{c.cz(q,shared);}));};
        c.push_condition(bit);let active=c.active_qubits();let((),peak)=c.r3_peak(|c|{execute(c);if inverse{c.x_all(&target);execute(c);c.x_all(&target);}});c.pop_condition();
        assert_eq!(peak,active+(n-2-drops.len())as u32);let ops=c.take_ops();let(nq,nb,_,_)=analyze_ops(ops.iter());assert_eq!(nq as usize,interface.len()+n-2-drops.len());let copies=if inverse{2}else{1};let m=n-3;let nr=draws(&ops);assert_eq!(nr,(n-2)*copies);
        assert_eq!(ops.iter().filter(|o|o.kind==OperationType::CCX).count(),(n-1)*copies);let ranks:Vec<_>=drops.iter().map(|&j|if rows[j].is_empty()||rows[j+1].is_empty()||rows[j]==rows[j+1]{1usize}else{2}).collect();assert_eq!(ops.iter().filter(|o|o.kind==OperationType::CCZ).count(),ranks.iter().sum::<usize>()*copies);
        let starts:Vec<_>=if probe.is_some(){vec![0x97EC0]}else{(0..1usize<<(2*n+1)).step_by(64).collect()};
        for start in starts{let words:Vec<_>=(0..nr).map(|j|match probe{Some(p)=>if p==j||p==nr{u64::MAX}else{0},None=>0x9E3779B97F4A7C15u64.wrapping_mul((start+j+1)as u64).rotate_left(j as u32)}).collect();let mut random=rng(&words);let mut s=Simulator::new(nq as usize,nb as usize,&mut random);s.bits[bit.0 as usize]=guard;
            for lane in 0..64{for(i,&q)in interface.iter().enumerate(){put(&mut s,q,lane,(start+lane)>>i);}}let original=s.qubits.clone();s.apply_iter(ops.iter());let mut expected_phase=0u64;
            for lane in 0..64{let value=start+lane;let mut av=0usize;for(i,row)in rows.iter().enumerate(){let a=row.iter().fold(usize::from(ones[i]),|x,q|x^(value>>interface.iter().position(|r|r==q).unwrap()&1));av|=a<<i;}
                let bv=value>>n&((1<<n)-1);let enabled=guard>>lane&1!=0;let wanted=if inverse||!enabled{bv}else{(av+bv)&((1<<n)-1)};
                for i in 0..n{assert_eq!(s.qubits[target[i].0 as usize]>>lane&1,(wanted>>i&1)as u64,"n={n} pattern={pattern} drops={drops:?}");}
                if hooked&&enabled{let shared=value>>(2*n)&1;let phase=(1..=n-2).fold(0usize,|p,k|{let mask=(1<<k)-1;p^((((av&mask)+(bv&mask))>>k)&shared)});if phase&1!=0{expected_phase|=1u64<<lane;}}
            }
            for i in 0..nq as usize{if !target.iter().any(|q|q.0 as usize==i){assert_eq!(s.qubits[i],original[i]);}}assert_eq!(s.phase,expected_phase);
            let mut expected_t=(n-1)as u64*copies as u64*guard.count_ones()as u64;for copy in 0..copies{for(j,&d)in drops.iter().enumerate(){let i=d+1;let ordinal=drops.len()+m-i-drops.iter().filter(|&&x|x>i).count();expected_t+=ranks[j]as u64*(words[copy*(n-2)+ordinal]&guard).count_ones()as u64;}}
            assert_eq!(s.stats.toffoli_gates as u64,expected_t);drop(s);assert_eq!(random.pos,nr*8);
        }
    }
    #[test]fn full_small_inputs_with_zero_carry_birth_phases_and_mixed_classical_guard(){for n in 6usize..=8{let m=n-3;for mask in 1usize..1<<(m-1){let ds:Vec<_>=(1..m).filter(|&i|mask>>(i-1)&1!=0).collect();let room=m-ds.len();if !ds.iter().enumerate().all(|(j,&i)|i+1-j<=room&&(j==0||ds[j-1]+1<i)){continue;}for pattern in 0..4{fixture(n,pattern,&ds,false,true,0xA5963C78F012DE4B,None);fixture(n,pattern,&ds,false,true,u64::MAX,None);}}}}
    #[test]fn all_measurement_coefficients_inverse_and_false_guard_on_sixty_four_bases(){for inverse in[false,true]{let nr=8*if inverse{2}else{1};for p in 0..nr+2{for guard in[0u64,u64::MAX,0xAA55AA55AA55AA55]{for pattern in 0..4{for drops in[vec![1],vec![2],vec![1,3],vec![2,4],vec![1,3,5]]{fixture(10,pattern,&drops,inverse,!inverse,guard,Some(p));}}}}}}
    #[test]fn aliases_and_unsupported_first_literal_reject_before_emission(){let mut c=Builder::new();let a=c.alloc_qubits(7);let b=c.alloc_qubits(7);let op=c.op_count();let mut rows:Vec<_>=a.iter().map(|&q|vec![q]).collect();rows[0]=Vec::new();assert!(!add(&mut c,&b,&rows,&[false;7],&[1],&mut|_,_,_|{}));rows[0]=vec![a[0]];rows[3]=vec![b[0]];assert!(!add(&mut c,&b,&rows,&[false;7],&[1],&mut|_,_,_|{}));assert_eq!(op,c.op_count());}
}
