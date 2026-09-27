//! Experimental finite-map variant. It creates a new precision boundary,
//! and its outer B/F comparison debts must be qualified independently.
use super::*;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::analyze_ops;
    use crate::sim::Simulator;
    use sha3::{digest::ExtendableOutput, Shake256};

    #[test]
    fn low_workspace_half_fold_preserves_every_selector_and_dirty_bit() {
        for width in [5usize,8] {
            let minimum=(0..width).find(|&room|super::super::super::width_composition::direct_plan(width,room).is_some()).unwrap();
            for room in [2,minimum+1] {
                let mut circ=Builder::new();
                let upper=circ.alloc_qubits(width);
                let controls=circ.alloc_qubits(3);
                let dirty=circ.alloc_qubits(width-2);
                circ.alloc_qubits(walk_max_qubits()-circ.active_qubits()as usize-room);
                half_fold(&mut circ,&upper,controls[0],controls[1],controls[2],&dirty);
                let ops=circ.take_ops();
                let(nq,nb,_,_)=analyze_ops(ops.iter());
                assert!(nq<=walk_max_qubits()as u64);
                let mask=(1usize<<width)-1;
                for start in (0..8*(mask+1)).step_by(64) {
                    let mut rng=Shake256::default().finalize_xof();
                    let mut sim=Simulator::new(nq as usize,nb as usize,&mut rng);
                    let mut output=vec![0;width];
                    for lane in 0..64 {
                        let value=start+lane;let old=value&mask;let bits=value>>width;
                        let p=bits&1;let s=(bits>>1)&1;let o=(bits>>2)&1;
                        for(q,bit)in controls.iter().zip([p,s,o]){sim.qubits[q.0 as usize]|=(bit as u64)<<lane;}
                        for (bit,q) in dirty.iter().enumerate(){sim.qubits[q.0 as usize]|=(((value.rotate_left(3)>>bit)&1)as u64)<<lane;}
                        let k=s as i64+p as i64*(2*o as i64-1);
                        let correction=(k*4_294_968_273i64-(s^p)as i64)/2;
                        let sum=(old as i64+correction)as usize&mask;
                        for bit in 0..width {
                            sim.qubits[upper[bit].0 as usize]|=(((old>>bit)&1)as u64)<<lane;
                            output[bit]|=(((sum>>bit)&1)as u64)<<lane;
                        }
                    }
                    let mut expected=sim.qubits.clone();
                    for bit in 0..width{expected[upper[bit].0 as usize]=output[bit];}
                    sim.apply_iter(ops.iter());
                    assert_eq!(sim.qubits,expected,"width={width}, room={room}");
                    assert_eq!(sim.phase,0);
                }
            }
        }
    }
}

pub(super) fn initial_carry(c:&mut Builder,a:QubitId,p:QubitId,s:QubitId)->QubitId {
    c.cx(s,a);c.x(a);let q=and_clean(c,p,a);c.x(a);c.cx(s,a);c.cx(a,q);q
}
pub(super) fn erase_initial(c:&mut Builder,q:QubitId,a:QubitId,p:QubitId,s:QubitId) {
    let m=c.alloc_bit();c.hmr(q,m);
    c.z_if(a,m);c.z_if(p,m);c.cz_if(p,a,m);c.cz_if(p,s,m);
    c.free_bit(m);c.free(q);
}

/// Direct selector-mapped wrapped addition with initial carry exactly zero.
/// This is the same ripple as direct_add, with its first carry specialized.
pub(super) fn mapped_zero(c:&mut Builder,acc:&[QubitId],map:&[Vec<QubitId>]) {
    let n=acc.len();assert!(n>=3);assert_eq!(map.len(),n);
    assert!(!map[0].is_empty());
    let room=walk_max_qubits().saturating_sub(c.active_qubits()as usize);
    if n-2>room {
        let plan=super::super::width_composition::direct_plan(n,room).unwrap_or_else(|| {
            panic!("prebias fold of {n} bits needs more than {room} scratch qubits (live={})",c.active_qubits())
        });
        super::super::width_composition::direct_add_zero(c,map,acc,&plan);
        return;
    }
    let carries=c.alloc_qubits(n-2);
    with_selector_xor(c,&map[0],acc[0],|c,src|c.ccx(src,acc[0],carries[0]));
    for i in 1..n-2 {fold_step(c,acc[i],carries[i-1],carries[i],&map[i],false);}
    fold_step(c,acc[n-2],carries[n-3],acc[n-1],&map[n-2],true);
    for &s in &map[n-1]{c.cx(s,acc[n-1]);}
    for i in (1..n-2).rev(){unwind_fold_step(c,acc[i],carries[i-1],carries[i],&map[i]);}
    with_selector_xor(c,&map[0],acc[0],|c,src| {
        let m=c.alloc_bit();c.hmr(carries[0],m);c.cz_if(src,acc[0],m);c.free_bit(m);c.cx(src,acc[0]);
    });
    c.free_vec(&carries);
}

/// Add J=(k*f-g)/2 to the upper word, k=s+p*(2o-1), g=s XOR p.
/// Original p,s,o survive; two selector ANDs replace the old three.
pub(super) fn half_fold(c:&mut Builder,upper:&[QubitId],p:QubitId,s:QubitId,o:QubitId,dirty:&[QubitId]) {
    #[cfg(test)]
    let _measurement=super::super::measurement::replay::part(super::super::measurement::replay::Part::Fold);
    c.cx(s,o);c.x(o);let q=and_clean(c,p,o);c.x(o);c.cx(s,o);
    let room=walk_max_qubits().saturating_sub(c.active_qubits()as usize);
    if super::super::width_composition::direct_plan(upper.len(),room.saturating_sub(1)).is_none() {
        let plan=super::super::width_composition::direct_plan(upper.len(),room);
            // J = (p XOR s)*(f-1)/2 + (2s-1)*q*f: only q needs an AND.
            let map=|constant:U256,control| (0..upper.len()).map(|bit|if constant.bit(bit){vec![control]}else{Vec::new()}).collect::<Vec<_>>();
            c.cx(s,p);
            if let Some(plan)=&plan {
                super::super::width_composition::direct_add_zero(c,&map((f()-U256::from(1))>>1usize,p),upper,plan);
            } else {
                super::super::const_arith::controlled_const_dirty(c,upper,(f()-U256::from(1))>>1usize,p,dirty,false);
            }
            c.x(s);c.cx_all(s,upper);c.x(s);
            if let Some(plan)=&plan {
                super::super::width_composition::direct_add_zero(c,&map(f(),q),upper,plan);
            } else {
                super::super::const_arith::controlled_const_dirty(c,upper,f(),q,dirty,false);
            }
            c.x(s);c.cx_all(s,upper);c.x(s);
            c.cx(s,p);
            c.cx(s,o);c.x(o);and_uncompute(c,q,p,o);c.x(o);c.cx(s,o);
            return;
    }
    c.x(s);let minus=and_clean(c,q,s);c.x(s);
    c.cx(minus,q); // q hosts plus_2f
    c.cx(s,p);c.cx(minus,p); // p hosts plus_f
    let fp=(f()-U256::from(1))>>1usize;
    let fm=U256::ZERO.wrapping_sub((f()+U256::from(1))>>1usize);
    let mut map=Vec::new();
    for i in 0..upper.len(){let mut row=Vec::new();if fp.bit(i){row.push(p);}if f().bit(i){row.push(q);}if fm.bit(i){row.push(minus);}map.push(row);}
    mapped_zero(c,upper,&map);
    c.cx(minus,p);c.cx(s,p);c.cx(minus,q);
    c.x(s);and_uncompute(c,minus,q,s);c.x(s);
    c.cx(s,o);c.x(o);and_uncompute(c,q,p,o);c.x(o);c.cx(s,o);
}

pub(super) fn eligible(c:&Builder,round:usize)->bool {
    composition_bounds(c,round,false).is_some()
        || walk_max_qubits().saturating_sub(c.active_qubits()as usize)>=if small_tail_enabled(){2}else{3}
}

pub(super) fn joint_prebias_div(c:&mut Builder,sign:QubitId,a:&[QubitId],b:&[QubitId],fw:usize,round:usize) {
    assert!(!split_fold()&&env_raw("PP_PIN_REPLAY_LAYOUT").is_none());
    assert_eq!(a.len(),N);assert_eq!(b.len(),N);
    let bounds=composition_bounds(c,round,false);
    #[cfg(test)]
    super::super::measurement::replay::plan(if bounds.is_some(){"joint-prebias"}else{"prebias-composition"},bounds.as_deref().unwrap_or(&[]),0,None);
    if env_flag("PP_COMPOSE_TRACE"){eprintln!("COMPOSE_PREBIAS {} {} {} {} {:?}",round,c.active_qubits(),fw,REPLAY_SIGN_LOANS.with(|s|s.get()),bounds);}
    c.swap(sign,b[0]);c.cx(a[0],sign);c.cx(b[0],sign); // sign=p, b0=s
    c.cx_all(b[0],&b[1..]);
    let initial=initial_carry(c,a[0],sign,b[0]);
    let o=if let Some(bounds)=bounds {
    let mut cin=Some(initial);let mut previous:Option<(QubitId,usize,usize)>=None;
    for (j,&(lo,hi)) in bounds.iter().enumerate(){
        let out=c.alloc_qubit();let at=if j==0{1}else{lo};
        ripple_add(c,&a[at..hi],&b[at..hi],cin,Some(out));
        if j==0 {erase_initial(c,initial,a[0],sign,b[0]);}
        if let Some((carry,plo,phi))=previous {
            let(k,seeded)=boundary_repair_spec(round,false,plo,phi);
            c.record_replay_site('B',round,phi,k);let w=phi-k..phi;
            let full_first=plo==0 && phi==k;
            if full_first {c.cx(b[0],sign);} // parity host temporarily holds g
            let borrow=if full_first {Some(sign)}else{seeded.then(||a[phi-k-1])};
            erase_with_compare(c,carry,&b[w.clone()],&a[w],borrow);c.free(carry);
            if full_first {c.cx(b[0],sign);}
        }
        cin=Some(out);previous=Some((out,lo,hi));
    }
    cin.unwrap()
    } else {
        let room=walk_max_qubits().saturating_sub(c.active_qubits()as usize);
        let plan=super::super::width_composition::plan_with_carry(N-1,room).expect("prebias addition workspace");
        let out=super::super::width_composition::add_with_carry(c,&a[1..],&b[1..],Some(initial),&plan);
        erase_initial(c,initial,a[0],sign,b[0]);out
    };
    half_fold(c,&b[1..fw],sign,b[0],o,&b[fw..]);
    c.swap(sign,b[0]);c.cx(o,b[0]); // original sign restored; b0=p XOR o
    let mut k=flag_compare(round)+usize::from(policy_width(round)>=flag_widen_div());
    let borrow=if env_flag("CMP_SEED_ALL"){k-=1;Some(a[N-k-1])}else{None};
    if borrow.is_none(){k=refined_unseeded_width(k,N,"PP_REFINE_UNSEEDED_F");}
    c.record_replay_site('F',round,N,k);erase_with_compare(c,o,&b[N-k..],&a[N-k..],borrow);c.free(o);
    c.cx_all(sign,b);rotate_down(c,b);
}
