use super::super::Row;
use super::config;
const N:u16=u16::MAX;

pub fn b(mut src:Vec<Row>)->Vec<Row>{
    for r in &mut src[230500001-215192049..258008000-215192049]{
        let nq=super::arity(r[0]);for v in &mut r[1..1+nq]{if *v==136{*v=450;}}
    }
    src
}

pub fn bp(src:Vec<Row>)->Vec<Row>{
    let lo=1257301220-1242367771; let hi=1286607360-1242367771;
    let mut a=src[lo..hi].to_vec();
    let mut hits=Vec::new();
    for (i,r) in a.iter_mut().enumerate(){
        if r[0]==13&&((r[1]==166&&matches!(r[2],23|24))||(r[2]==166&&matches!(r[1],23|24))){hits.push(i);}
        for x in r.iter_mut(){if *x==248{*x=450;}}
    }
    assert_eq!(hits.len(),2*config::KEEP.len());let mut flags=vec![0;a.len()];
    for (p,&keep) in hits.chunks_exact(2).zip(config::KEEP){
        let (first,second)=(p[0],p[1]);let gap=second-first;
        assert_eq!(a[first],a[second]);
        let f=if keep==1{1}else{2};
        flags[first]=f;flags[second]=f;
        if gap>1 && second+gap<=a.len() && a[first+1..second].iter().all(|r|r[0]==13) &&
          a[first+1..second].iter().eq(a[second+1..second+gap].iter().rev()){
            flags[first..second+gap].fill(f);
        }
    }
    let mut out=Vec::with_capacity(119390274);out.extend_from_slice(&src[..lo]);
    let guard=a.iter().find(|r|r[0]==15).unwrap()[1];
    out.extend(a.iter().zip(&flags).filter(|(_,f)|**f!=2).map(|(r,_)|*r));
    out.push([8,450,166,N]);
    out.extend(a.iter().zip(&flags).rev().filter(|(_,f)|**f==0).map(|(&r,_)|match r[0]{
        15=>{assert_eq!(r[1],guard);[16,N,N,N]},16=>[15,guard,N,N],_=>r}));
    out.extend(a.iter().zip(&flags).filter(|(_,f)|**f!=1).map(|(r,_)|*r));
    out.push([8,450,166,N]);out.extend_from_slice(&src[hi..]);
    let mut last=0; let mut write=0;
    for &(a,b) in config::BP_CUTS{
        out.copy_within(last..a,write);write+=a-last;last=b;
    }
    out.copy_within(last..,write);out.truncate(write+out.len()-last);out
}

