//! Recycle cached linear table functions for the entire fold, rather than
//! only after their last upper-lane use. Their ANF monomials remain live;
//! one function lane is a JIT XOR workspace and all others become carries.
//! With borrowed XOR enabled, the first source term supplies that workspace
//! transiently and every cached-function lane becomes a carry lane.
use super::builder::B;
use crate::circuit::QubitId;

/// Candidate dispatch for modp_ft::c58_var_add_lean. Add this module to
/// ftport/mod.rs and call this before constructing the old `freed` list.
/// Site bit 8 keeps it independently switchable from sites 1/2/4.
pub(crate) fn try_add(
    b: &mut B,
    t: &[QubitId],
    add: &[Option<QubitId>],
    pool: &[QubitId],
    recipes: &[(QubitId, Vec<QubitId>)],
) -> bool {
    if !super::l1_fold::enabled_at(8) || b.is_recording() { return false; }
    emit_if_cheaper(b,t,add,pool,recipes)
}

fn emit_if_cheaper(
    b: &mut B,
    t: &[QubitId],
    add: &[Option<QubitId>],
    pool: &[QubitId],
    recipes: &[(QubitId, Vec<QubitId>)],
) -> bool {
    if recipes.len()<2 { return false; }
    let i0=add.iter().position(|a|a.is_some()).unwrap();
    let need=t.len()-1-i0;
    if pool.len()>=need { return false; }
    let gap=need-pool.len();
    let bridge=i0+pool.len();
    let old_freed=recipes.iter().filter(|(q,_)|!add[bridge..].contains(&Some(*q))).take(gap).count();
    let old_loan=gap-old_freed;
    let borrow=super::l1_fold::borrow_xor_enabled();
    let lend=recipes.len()-usize::from(!borrow);
    let new_p=pool.len()+lend;
    if new_p>=need { return false; } // Existing full-pool cases are unchanged.
    let new_loan=need-new_p;
    if new_p<=new_loan || new_loan>=2*old_loan { return false; }
    // add_table's recipes consist only of original variables or retained
    // ANF monomials, never of other cached XOR functions.
    let function_ids: std::collections::BTreeSet<QubitId>=recipes.iter().map(|(q,_)|*q).collect();
    assert_eq!(function_ids.len(),recipes.len());
    assert!(recipes.iter().all(|(q,terms)| !pool.contains(q) && !t.contains(q)
        && terms.iter().all(|s| !function_ids.contains(s) && !pool.contains(s) && !t.contains(s))));
    let sources: Vec<Vec<QubitId>>=add.iter().map(|a| match a {
        None=>Vec::new(),
        Some(q)=>recipes.iter().find(|(f,_)|f==q).map_or_else(||vec![*q],|(_,terms)|terms.clone()),
    }).collect();
    for (q,terms) in recipes { for &s in terms { b.cx(s,*q); } }
    let mut carries=pool.to_vec();
    carries.extend(recipes[..lend].iter().map(|(q,_)|*q));
    let jit=if borrow {None} else {Some(recipes.last().unwrap().0)};
    super::l1_fold::add(b,t,&sources,&carries,jit);
    for (q,terms) in recipes.iter().rev() { for &s in terms { b.cx(s,*q); } }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::XofReader;

    struct Forced(u64);
    impl XofReader for Forced {
        fn read(&mut self,out:&mut[u8]) { assert_eq!(out.len(),8);out.copy_from_slice(&self.0.to_le_bytes()); }
    }

    #[test]
    fn l1_c58_half_forced_exact_counts() {
        let mut shapes=0;
        let lend=if super::super::l1_fold::borrow_xor_enabled(){5}else{4};
        for n in [54usize,57,58,66] {
            for p in [35usize,37,38,42,46,47,50,54,56] {
                if p+lend>=n-1 || p<=n-1-p {continue;}
                let mut b=B::new();
                let t=b.alloc_n(n);
                let vars=b.alloc_n(6);
                let f=b.alloc_n(5);
                let pool=b.alloc_n(p);
                let indices:Vec<Vec<usize>>=vec![vec![0,1],vec![1,2],vec![2,3],vec![0,2,4],vec![0,3,5]];
                let recipes:Vec<_>=f.iter().zip(&indices).map(|(&q,idx)|(q,idx.iter().map(|&i|vars[i]).collect())).collect();
                let fi:Vec<usize>=(0..n).map(|i|if i<32{i%4}else{4}).collect();
                let add:Vec<_>=fi.iter().map(|&i|Some(f[i])).collect();
                assert!(emit_if_cheaper(&mut b,&t,&add,&pool,&recipes));
                let need=n-1;
                let loan=need-p-lend;
                assert_eq!(b.tof,(need+loan)as u64);
                let mask=(1u128<<n)-1;
                for forced in [0u64,u64::MAX,0xaaaa_aaaa_aaaa_aaaa] {
                    for packet in 0..8 {
                        let mut tape=Forced(forced);
                        let mut sim=Simulator::new(b.peak as usize,10_100,&mut tape);
                        let mut tv=Vec::new();let mut av=Vec::new();
                        for shot in 0..64 {
                            let input=shot;
                            let value=match packet {
                                0=>0,
                                1=>mask,
                                2=>(1u128<<(loan+1))-1,
                                3=>(1u128<<(loan+1)),
                                _=>((shot+64*packet)as u128).wrapping_mul(0x9e37_79b9_7f4a_7c15_9e37_79b9u128)&mask,
                            };
                            let functions:Vec<usize>=indices.iter().map(|idx|idx.iter().fold(0,|v,&j|v^((input>>j)&1))).collect();
                            let sum:u128=fi.iter().enumerate().map(|(i,&j)|(functions[j]as u128)<<i).sum();
                            tv.push(value);av.push(sum);
                            for(i,&q)in t.iter().enumerate(){sim.qubits[q.0 as usize]|=(((value>>i)&1)as u64)<<shot;}
                            for(i,&q)in vars.iter().enumerate(){sim.qubits[q.0 as usize]|=(((input>>i)&1)as u64)<<shot;}
                            for(i,&q)in f.iter().enumerate(){sim.qubits[q.0 as usize]|=(functions[i]as u64)<<shot;}
                        }
                        let before=sim.qubits.clone();
                        sim.apply_iter(b.ops.iter());
                        for shot in 0..64 {
                            let got=t.iter().enumerate().fold(0u128,|v,(i,q)|v|(((sim.qubits[q.0 as usize]>>shot)&1)as u128)<<i);
                            assert_eq!(got,(tv[shot]+av[shot])&mask,"n{n} p{p} packet{packet} forced{forced:x} shot{shot}");
                        }
                        assert_eq!(sim.phase,0,"n{n} p{p} packet{packet} forced{forced:x} phase");
                        for q in n..sim.qubits.len(){assert_eq!(sim.qubits[q],before[q],"n{n} p{p} q{q} scratch/source");}
                        assert_eq!(sim.stats.toffoli_gates,64*need as u64+forced.count_ones()as u64*loan as u64);
                    }
                }
                shapes+=1;
            }
        }
        assert!(shapes>10);
        eprintln!("L1_C58_HALF shapes={shapes} each=64 source assignments x 8 target packets x 3 forced masks");
    }
}
