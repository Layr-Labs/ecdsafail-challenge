//! Closed quantum-only deferral in the F pressure windows (zd-F/defer.cpp).
use super::Row;
use std::collections::BTreeSet;
const N:u16=u16::MAX;
type Poly=BTreeSet<Vec<u16>>;

fn normalize(t:&mut Vec<u16>) {t.sort_unstable();t.dedup();}
fn toggle(poly:&mut Poly,mut term:Vec<u16>) {
    normalize(&mut term);
    if !poly.remove(&term) {poly.insert(term);}
}
fn xor(out:&mut Vec<Row>,mut term:Vec<u16>,target:u16,guard:u16) {
    normalize(&mut term);
    assert!(!term.contains(&target));
    if term.len()<2 {
        out.push(if term.is_empty(){[6,target,guard,N]}else{[8,term[0],target,guard]});
        return;
    }
    if guard!=N {out.push([15,guard,N,N]);}
    if term.len()==2 {out.push([13,term[0],term[1],target]);} else {
        let n=term.len();
        let dirt:Vec<_>=(450..).filter(|x|*x!=target&&!term.contains(x)).take(n-2).collect();
        for _ in 0..2 {
            out.push([13,term[n-1],dirt[n-3],target]);
            for j in (2..n-1).rev(){out.push([13,term[j],dirt[j-2],dirt[j-1]]);}
            out.push([13,term[0],term[1],dirt[0]]);
            for j in 2..n-1 {out.push([13,term[j],dirt[j-2],dirt[j-1]]);}
        }
    }
    if guard!=N {out.push([16,N,N,N]);}
}
fn phase(out:&mut Vec<Row>,mut term:Vec<u16>,guard:u16) {
    normalize(&mut term);
    match term.as_slice() {
        []=>for _ in 0..2 {out.extend([[6,450,N,N],[7,450,guard,N]]);},
        &[a]=>out.push([7,a,guard,N]),
        &[a,b]=>out.push([9,a,b,guard]),
        _=>{
            let dirty=(468..).find(|v|!term.contains(v)).unwrap();
            let last=term.pop().unwrap();
            for _ in 0..2 {xor(out,term.clone(),dirty,N);out.push([9,dirty,last,guard]);}
        }
    }
}

fn defer(rows:&[Row],host:u16)->Vec<Row> {
    let mut out=Vec::with_capacity(rows.len());
    let mut poly=Poly::new();
    let (mut start,mut commit,mut i)=(0,0,0);
    let flush=|p:&mut Poly,o:&mut Vec<Row>,start,commit,end|{
        if !p.is_empty() {o.truncate(commit);o.extend_from_slice(&rows[start..end]);p.clear();}
    };
    while i<rows.len() {
        let r=rows[i];let [k,a,b,c]=r;
        if poly.is_empty(){start=i;commit=out.len();}
        let target=match k{6=>a,8=>b,13=>c,_=>N};
        let guard=match k{6|7=>b,8|9=>c,_=>N};
        let read=match k{7|8=>a==host,9|13=>a==host||b==host,14=>r[1..].contains(&host),_=>false};
        if target==host && guard==N {
            let mut term=Vec::new();if k>=8 {term.push(a);}if k==13{term.push(b);}
            toggle(&mut poly,term);
            if poly.len()>5 {flush(&mut poly,&mut out,start,commit,i+1);}
        } else if poly.is_empty(){out.push(r);}
        else if matches!(k,10|11|15|16) || k==12 && a!=host && poly.iter().any(|t|t.contains(&a)) {
            flush(&mut poly,&mut out,start,commit,i);out.push(r);
        } else if k==12 && a==host {
            if b==N {flush(&mut poly,&mut out,start,commit,i);out.push(r);} else {
                out.push(r);
                if let Some(&[9,x,y,bit])=rows.get(i+1) {
                    if bit==b && x!=host && y!=host {toggle(&mut poly,vec![x,y]);i+=1;}
                }
                for t in &poly {phase(&mut out,t.clone(),b);}
                poly.clear();
            }
        } else if target!=N && poly.iter().any(|t|t.contains(&target)) {
            if read || guard!=N {flush(&mut poly,&mut out,start,commit,i);} else {
                let mut next=poly.clone();let mut ok=true;
                for t in &poly {
                    if !t.contains(&target){continue;}
                    let mut term:Vec<_>=t.iter().copied().filter(|&q|q!=target).collect();
                    if k>=8 {term.push(a);}if k==13{term.push(b);}
                    if term.len()>4 {ok=false;break;}
                    toggle(&mut next,term);
                }
                if ok && next.len()<=5 {poly=next;}else{flush(&mut poly,&mut out,start,commit,i);}
            }
            out.push(r);
        }else{
            out.push(r);
            if read {
                let n=super::qubits(k);
                for t in &poly {
                    let mut term=t.clone();
                    term.extend(r[1..1+n].iter().filter(|&&q|q!=host&&q!=target));
                    if target==N {phase(&mut out,term,guard);}else{xor(&mut out,term,target,guard);}
                }
            }
        }
        i+=1;
    }
    flush(&mut poly,&mut out,start,commit,i);
    out
}

pub(super) fn apply(input:Vec<Row>,windows:&[u8],hosts:&[u16],expected:usize)->Vec<Row>{
    let mut out=Vec::with_capacity(expected);
    let bytes=super::lzma::decode(windows).unwrap();
    let mut at=0;
    for r in bytes.chunks_exact(8){
        let a=u32::from_le_bytes(r[..4].try_into().unwrap()) as usize;
        let b=u32::from_le_bytes(r[4..].try_into().unwrap()) as usize;
        out.extend_from_slice(&input[at..a]);
        let mut g=input[a..b].to_vec();
        for &host in hosts {g=defer(&g,host);}
        out.extend(g);at=b;
    }
    out.extend_from_slice(&input[at..]);
    assert_eq!(out.len(),expected);
    out
}

