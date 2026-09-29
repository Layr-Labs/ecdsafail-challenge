// Public ecdsa.fail resource research, no real-world key target.
fn high_early_mode()->usize {super::optional_env::<usize>("SQ_HIGH_EARLY_LOAN").unwrap_or(0)}
fn high_early_trace(c:&Builder,x:&[QubitId],r:&K2Retained,event:&str){
    if std::env::var_os("SQ_HIGH_EARLY_TRACE").is_none(){return;}
    let lo=x.len()/2;
    eprintln!("FLAT_BANK\t{event}\t{}\t{}\t{}\t{:?}",x.len(),c.op_count(),c.active_qubits(),r.flat_sum_carries.iter().map(|q|q.0).collect::<Vec<_>>());
    eprintln!("HIGH_EARLY\t{event}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:?}",x.len(),c.op_count(),c.active_qubits(),r.cross[1].0,r.cross[2].0,x[0].0,x[1].0,x[lo].0,x[lo+1].0,r.carry.0,r.held.iter().map(|q|q.0).collect::<Vec<_>>());
}
fn high_early_pair(c:&mut Builder,x:&[QubitId],r:&K2Retained,restore:bool){high_early_pair_reserved(c,x,r,restore,false);}
fn high_early_reserve(c:&mut Builder,r:&K2Retained){let mode=high_early_mode();if mode&1!=0{c.reacquire(r.cross[1]);}if mode&2!=0{c.reacquire(r.cross[2]);}}
fn high_early_pair_reserved(c:&mut Builder,x:&[QubitId],r:&K2Retained,restore:bool,reserved:bool){
    high_early_pair_reserved_skip(c,x,r,restore,reserved,false);
}
fn high_early_pair_reserved_skip(c:&mut Builder,x:&[QubitId],r:&K2Retained,restore:bool,reserved:bool,skip1:bool){
    let mode=high_early_mode();assert!(mode<=3);if mode==0{return;}
    let lo=x.len()/2;let(q,a,t)=(r.cross[1],x[0],x[lo]);
    let l=Cross2Loan{q:r.cross[2],a0:x[0],a1:x[1],t0:x[lo],t1:x[lo+1]};
    assert!(x.len()>=4 && !x.contains(&q) && !x.contains(&l.q));
    if restore {
        if mode&1!=0&&!skip1{if !reserved{c.reacquire(q);}c.x(t);c.ccx(a,t,q);c.x(t);}
        if mode&2!=0{if !reserved{c.reacquire(l.q);}cross2_restore(c,l);}
    }else{
        if mode&1!=0{let m=c.alloc_bit();c.hmr(q,m);c.x(t);c.cz_if(a,t,m);c.x(t);c.free_bit(m);c.release_clean(q);}
        if mode&2!=0{cross2_erase(c,l);c.release_clean(l.q);}
    }
    high_early_trace(c,x,r,if restore{"repaid"}else{"erased"});
}

pub(crate) fn high_probe(){
    use std::io::Write;
    std::fs::create_dir_all("gates").unwrap();
    let held=std::env::var("PROBE_HELD").unwrap_or("0".into())=="1";
    for n in[6usize,8,10]{
        let mut c=Builder::new();let x=c.alloc_qubits(n);let product=c.alloc_qubits(2*n);
        // A small-cap fixture forces the same held-boundary/rehome branch.
        let room=if held{4}else{50};let pad=c.alloc_qubits(super::pingpong::walk_max_qubits()-3*n-room);
        let start=c.op_count();let mut r=tri_square_k2r_flat(&mut c,&x,&product);
        let produced=c.op_count();let cross=r.cross.clone();let carry=r.carry;let held_ids=r.held.clone();
        high_early_pair(&mut c,&x,&r,false);
        let (a,b)=x.split_at(n/2);let mut t=b.to_vec();t.push(carry);if r.flat_sum_carries.is_empty(){restore_square_sum(&mut c,a,&t);}else{super::modular::shared_carry_inverse(&mut c,a,&t,false,std::mem::take(&mut r.flat_sum_carries));}c.release_clean(carry);
        // Actual reuse of the released identities, then full restoration.
        if high_early_mode()!=0{let tmp=c.alloc_qubits(2);c.cx(x[0],tmp[0]);c.ccx(x[0],x[1],tmp[1]);c.ccx(x[0],x[1],tmp[1]);c.cx(x[0],tmp[0]);c.free_vec(&tmp);}
        let cut=c.op_count();let fcost=c.i35_cost();
        c.reacquire(carry);let keep=super::env_flag("SQ_FLAT_SHARED_CARRIES");if keep{high_early_reserve(&mut c,&r);r.flat_sum_carries=super::modular::shared_carry_forward(&mut c,a,&t,false);}else{add_wide(&mut c,a,&t);}high_early_pair_reserved(&mut c,&x,&r,true,keep);
        tri_square_k2r_inv(&mut c,&x,&product,r);let end=c.active_qubits();let total=c.i35_cost();let peak=c.peak_total();let(nq,nb)=c.i13_dims();let ops=c.take_ops();
        let ids=|qs:&[QubitId]|qs.iter().map(|q|q.0.to_string()).collect::<Vec<_>>().join(",");
        let name=format!("n{n}-held{}-mode{}",held as u8,high_early_mode());let mut out=std::io::BufWriter::new(std::fs::File::create(format!("gates/{name}.json")).unwrap());
        writeln!(out,"{{\"n\":{n},\"nq\":{nq},\"nb\":{nb},\"start\":{start},\"produced\":{produced},\"cut\":{cut},\"x\":[{}],\"product\":[{}],\"cross\":[{}],\"carry\":{},\"held\":[{}],\"mode\":{},\"Q\":{peak},\"F\":{fcost},\"I\":{},\"end_live\":{end},\"pad\":{},\"ops\":[",ids(&x),ids(&product),ids(&cross),carry.0,ids(&held_ids),high_early_mode(),total-fcost,pad.len()).unwrap();
        for(i,o)in ops.iter().enumerate(){writeln!(out,"{}[{},{},{},{},{},{},{}]",if i==0{""}else{","},o.kind as u32,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0).unwrap();}writeln!(out,"]}}").unwrap();
        println!("{{\"name\":\"{name}\",\"Q\":{peak},\"F\":{fcost},\"I\":{},\"held\":{}}}",total-fcost,held_ids.len());
    }
}
