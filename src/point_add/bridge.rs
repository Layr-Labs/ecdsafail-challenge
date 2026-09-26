//! A bounded number of Cuccaro carry stages inside a measured ripple.
//! Each in-place stage trades one extra CCX for one fewer owned carry wire.
use super::Builder;
use crate::circuit::QubitId;
pub(crate) fn add(c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:Option<QubitId>,cout:Option<QubitId>,bridges:usize){
    run(c,a,b,cin,cout,bridges,|_,_,_,_,_|{});
}
pub(crate) fn run(c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:Option<QubitId>,cout:Option<QubitId>,bridges:usize,
    consume:impl FnOnce(&mut Builder,Option<QubitId>,QubitId,QubitId,Option<QubitId>)){
    let n=b.len();let owned=if cout.is_some(){n-1}else{n-2};let k=bridges+1;
    if super::env_flag("I50_SPLIT_BRIDGE") && bridges>0 && bridges<owned
        && k<=owned-bridges && n-k>=3 {
        assert_eq!(a.len(),n);assert!(a.iter().all(|q|!b.contains(q)));
        assert!(cin.is_none_or(|q|!a.contains(&q)&&!b.contains(&q)));
        assert!(cout.is_none_or(|q|!a.contains(&q)&&!b.contains(&q)&&Some(q)!=cin));
        let boundary=c.alloc_qubit();
        // The low sum finishes before the high carry ladder is allocated.
        // This also supports the useful two-bit low chunk for bridges=1.
        super::modular::ripple_add_proved(c,&a[..k],&b[..k],cin,Some(boundary),
            super::modular::Carry0::Full,super::modular::Carry1::Full,None,None,None,None);
        raw_run(c,&a[k..],&b[k..],Some(boundary),cout,0,consume);
        // Carry = borrow(completed low sum - original source - carry-in).
        // Exact full-k-bit phase repair; no approximate comparator is used.
        super::compare::erase_with_compare(c,boundary,&b[..k],&a[..k],cin);
        c.free(boundary);
    } else {raw_run(c,a,b,cin,cout,bridges,consume);}
}
fn raw_run(c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:Option<QubitId>,cout:Option<QubitId>,bridges:usize,
    consume:impl FnOnce(&mut Builder,Option<QubitId>,QubitId,QubitId,Option<QubitId>)){
    let n=b.len();assert_eq!(a.len(),n);assert!(n>=3);
    assert!(a.iter().all(|q|!b.contains(q)));assert!(cin.is_none_or(|q|!a.contains(&q)&&!b.contains(&q)));
    assert!(cout.is_none_or(|q|!a.contains(&q)&&!b.contains(&q)&&Some(q)!=cin));
    let owned=if cout.is_some(){n-1}else{n-2};assert!(bridges<owned);
    let first=owned-bridges;
    let is_bridge=|i:usize|i>=first&&i<owned;
    let mut carries:Vec<_>=(0..owned).map(|i|if is_bridge(i){a[i]}else{c.alloc_qubit()}).collect();carries.extend(cout);
    let previous=|i:usize|if i==0{cin}else{Some(carries[i-1])};
    for i in 0..carries.len(){let p=previous(i);
        if is_bridge(i){let p=p.unwrap();c.cx(a[i],b[i]);c.cx(a[i],p);c.ccx(b[i],p,a[i]);}
        else{if let Some(p)=p{c.cx(p,a[i]);c.cx(p,b[i]);}c.ccx(a[i],b[i],carries[i]);if let Some(p)=p{c.cx(p,carries[i]);}}
    }
    if cout.is_some(){if let Some(p)=previous(n-1){c.cx(p,a[n-1]);}c.cx(a[n-1],b[n-1]);}
    else{let i=n-2;let p=previous(i);if let Some(p)=p{c.cx(p,a[i]);c.cx(p,b[i]);}
        c.ccx(a[i],b[i],b[n-1]);if let Some(p)=p{c.cx(p,b[n-1]);}c.cx(a[n-1],b[n-1]);
        if let Some(p)=p{c.cx(p,a[i]);}c.cx(a[i],b[i]);
    }
    consume(c,cout,a[n-1],b[n-1],if cout.is_some(){previous(n-1)}else{None});
    for i in(0..owned).rev(){let p=previous(i);
        if is_bridge(i){let p=p.unwrap();c.ccx(b[i],p,a[i]);c.cx(a[i],p);c.cx(p,b[i]);}
        else{if let Some(p)=p{c.cx(p,carries[i]);}let m=c.alloc_bit();c.hmr(carries[i],m);c.cz_if(a[i],b[i],m);c.free_bit(m);c.free(carries[i]);
            if let Some(p)=p{c.cx(p,a[i]);}c.cx(a[i],b[i]);}
    }
}

thread_local!{static CURRENT:std::cell::Cell<Option<usize>>=const{std::cell::Cell::new(None)};}
pub(crate) fn budget()->usize{CURRENT.with(|v|v.get()).unwrap_or_else(||super::optional_env::<usize>("I35_BUDGET").unwrap_or(0))}
pub(crate) struct Scope(Option<usize>);
impl Drop for Scope{fn drop(&mut self){CURRENT.with(|v|v.set(self.0));}}
pub(crate) fn enter(round:usize,multiply:bool)->Scope{
    static PROFILE:std::sync::OnceLock<std::collections::BTreeMap<(usize,bool),usize>>=std::sync::OnceLock::new();
    let profile=PROFILE.get_or_init(||{
        let mut p=std::collections::BTreeMap::new();
        if let Some(s)=super::env_raw("I35_PROFILE"){for item in s.split(',').filter(|s|!s.is_empty()){
            let v:Vec<usize>=item.split(':').map(|x|x.parse().unwrap()).collect();assert_eq!(v.len(),3);assert!(v[1]<=1&&v[2]<=32);
            assert!(p.insert((v[0],v[1]!=0),v[2]).is_none());
        }}p
    });
    let b=profile.get(&(round,multiply)).copied().unwrap_or_else(||super::optional_env::<usize>("I35_BUDGET").unwrap_or(0));
    Scope(CURRENT.with(|v|v.replace(Some(b))))
}
