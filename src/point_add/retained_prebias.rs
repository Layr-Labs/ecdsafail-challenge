//! Native composition of retained overflow phase repair and prebiased division.
//! Explicitly preserves the prebias map with a separately named finite low cut.
use super::*;

#[derive(Debug)]
struct Plan {bounds:Vec<(usize,usize)>,prefix:usize,bits:usize,saving:f64,exact:bool}
fn plan(c:&Builder,r:usize,fw:usize)->Option<Plan>{
 let base_bits=super::super::optional_env::<usize>("PP_PREBIAS_RETAIN_BITS")?;
 let bits=if env_flag("PP_SPRINT_MIXED") && (370..=402).contains(&r) {29}else{base_bits};
 assert!(bits>=12&&bits<=fw&&fw>=36&&!split_fold());
 let room=walk_max_qubits().saturating_sub(c.active_qubits()as usize);
 let loans=REPLAY_SIGN_LOANS.with(|s|s.get());
 let old_bounds=composition_bounds(c,r,false)?;
 let bounds=retained_rebalance(c,&old_bounds,r,false);
 if bounds.len()<2{return None;}
 let &(lo,hi)=bounds.last()?;let(plo,phi)=bounds[bounds.len()-2];let(k,seed)=boundary_repair_spec(r,false,plo,phi);
 if lo<fw||phi-k-usize::from(seed)<fw{return None;}
 let need=(bits-3).max(fw-34);
 let existing=room as isize-(hi-lo)as isize-3;
 let missing=(need as isize-existing).max(0)as usize;
 let prefix=if missing==0{0}else{missing+1};if prefix+1>=hi-lo{return None;}
 let mut fk=flag_compare(r)+usize::from(policy_width(r)>=flag_widen_div());
 if env_flag("CMP_SEED_ALL"){fk-=1;}else{fk=refined_unseeded_width(fk,N,"PP_REFINE_UNSEEDED_F");}
 let saving=(fk-1)as f64/2.0-missing as f64/2.0-(bits as f64-33.0);
 if saving<=0.0{return None;}
 // Bound released carry wires, retaining the original outer B comparisons.
 let limit=super::super::optional_env::<usize>("PP_RETAIN_EXACT_EXTRA_DIV").unwrap_or(0);
 let exact_missing=((fw-3) as isize-existing).max(0) as usize;
 let exact_prefix=if exact_missing==0{0}else{exact_missing+1};
 let exact=env_flag("PP_RETAIN_EXACT_DIV") && exact_missing<=limit && exact_prefix+1<hi-lo;
 let prefix=if exact{exact_prefix}else{prefix};
 let saving=if exact{saving-(exact_missing-missing) as f64/2.0-1.0}else{saving};
 Some(Plan{bounds,prefix,bits,saving,exact})
}

/// J0=488*plus+977*twice-489*minus; high word adds k.
fn split_half(c:&mut Builder,b:&[QubitId],p:QubitId,s:QubitId,o:QubitId,bits:usize){
 c.cx(s,o);c.x(o);let q=and_clean(c,p,o);c.x(o);c.cx(s,o);
 c.x(s);let minus=and_clean(c,q,s);c.x(s);
 c.cx(minus,q);c.cx(s,p);c.cx(minus,p);
 let small=U256::from(977);let fp=(small-U256::from(1))>>1usize;
 let fm=U256::ZERO.wrapping_sub((small+U256::from(1))>>1usize);
 let mut map=Vec::new();
 for i in 0..bits-1{let mut row=Vec::new();if fp.bit(i){row.push(p);}if small.bit(i){row.push(q);}if fm.bit(i){row.push(minus);}map.push(row);}
 joint_prebias::mapped_zero(c,&b[1..bits],&map);
 let mut high=Vec::new();for i in 0..b.len()-32{let mut row=vec![minus];if i==0{row.push(p);}if i==1{row.push(q);}high.push(row);}
 joint_prebias::mapped_zero(c,&b[32..],&high);
 c.cx(minus,p);c.cx(s,p);c.cx(minus,q);
 c.x(s);and_uncompute(c,minus,q,s);c.x(s);
 c.cx(s,o);c.x(o);and_uncompute(c,q,p,o);c.x(o);c.cx(s,o);
}

pub(super)fn try_replay(c:&mut Builder,sign:QubitId,a:&[QubitId],b:&[QubitId],fw:usize,r:usize)->bool{
 let Some(p)=plan(c,r,fw)else{return false;};
 eprintln!("RETAINED_PREBIAS {} {} {} {} {} {}",r,c.active_qubits(),fw,p.bits,p.prefix,p.saving);
 if env_flag("PP_COMPOSE_TRACE"){eprintln!("COMPOSE_RETAIN {} {} {} {} {} {:?}",r,c.active_qubits(),fw,p.bits,REPLAY_SIGN_LOANS.with(|s|s.get()),p.bounds);}
 if p.exact {eprintln!("EXACT_RETAINED_FOLD div {} {}",r,fw);}
 c.swap(sign,b[0]);c.cx(a[0],sign);c.cx(b[0],sign);c.cx_all(b[0],&b[1..]);
 let initial=joint_prebias::initial_carry(c,a[0],sign,b[0]);
 let mut cin=Some(initial);let mut previous=None;
 for(j,&(lo,hi))in p.bounds.iter().enumerate(){
  let out=c.alloc_qubit();let at=if j==0{1}else{lo};
  if hi==N{
   let split=lo+p.prefix;
   let mid=if p.prefix==0{cin}else{let m=c.alloc_qubit();ripple_add(c,&a[lo..split],&b[lo..split],cin,Some(m));Some(m)};
   super::super::modular::ripple_add_consume(c,&a[split..hi],&b[split..hi],mid,out,|c,o,aa,bb,cc|{
    if p.exact {joint_prebias::half_fold(c,&b[1..fw],sign,b[0],o);}else{split_half(c,&b[..fw],sign,b[0],o,p.bits);}
    c.swap(sign,b[0]);c.cx(o,b[0]);
    super::super::modular::erase_overflow_from_frame(c,o,aa,bb,cc);
   });
   if p.prefix>0{let m=mid.unwrap();erase_with_compare(c,m,&b[lo..split],&a[lo..split],cin);c.free(m);}
  }else{ripple_add(c,&a[at..hi],&b[at..hi],cin,Some(out));}
  if j==0{joint_prebias::erase_initial(c,initial,a[0],sign,b[0]);}
  if let Some((carry,plo,phi))=previous{
   let(k,seed)=boundary_repair_spec(r,false,plo,phi);c.record_replay_site('B',r,phi,k);
   let full=plo==0&&phi==k;
   if full{c.cx(b[0],sign);}
   erase_with_compare(c,carry,&b[phi-k..phi],&a[phi-k..phi],if full{Some(sign)}else{seed.then(||a[phi-k-1])});c.free(carry);
   if full{c.cx(b[0],sign);}
  }
  cin=Some(out);previous=Some((out,lo,hi));
 }
 c.cx_all(sign,b);rotate_down(c,b);true
}

