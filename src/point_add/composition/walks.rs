use super::super::{post_pass, Row, NONE};
use super::{config, cap, columns};
use std::collections::HashMap;
const N:u16=NONE;

fn mapped(mut r:Row, map:&[u16])->Row {
    let n=super::arity(r[0]);
    for q in &mut r[1..1+n] { *q=map[*q as usize]; }
    r
}

// Same eight-lane protected set and last-writer/last-reader test as compact.cpp.
fn compact(code:&[u32], c:usize)->Vec<u32> {
    let mut reads=vec![Vec::<usize>::new();631];
    let mut writes=reads.clone();
    let mut recent=HashMap::<u32,usize>::new();
    let mut slots=Vec::<u32>::with_capacity(code.len());
    let last=|v:&mut Vec<usize>,s:&[u32]| {
        while v.last().is_some_and(|&i|s[i]==u32::MAX){v.pop();}
        v.last().copied()
    };
    for &w in code {
        let a=(w>>20) as usize; let b=((w>>10)&1023) as usize; let t=(w&1023) as usize;
        if let Some(&i)=recent.get(&w) {
            let protected=[256-c,257-c,256+c,384,385,386,630,257].contains(&t);
            if slots[i]!=u32::MAX && (!protected || i+1==slots.len()) &&
                last(&mut reads[t],&slots)<Some(i) &&
                [a,b].into_iter().all(|q|q==1023 || last(&mut writes[q],&slots)<=Some(i)) {
                slots[i]=u32::MAX;
                continue;
            }
        }
        let i=slots.len(); writes[t].push(i);
        for q in [a,b] {if q!=1023 {reads[q].push(i);}}
        recent.insert(w,i);slots.push(w);
    }
    slots.retain(|&w|w!=u32::MAX);slots
}

pub fn upper(raw:&[Row],which:usize)->Vec<Row>{
    let tag=which*2;
    let anchor=[498,504][which];
    let switches=config::SWITCHES[which];
    let wires=config::WIRES[tag];
    let mut hole=anchor;
    let mut at=0;
    let mut si=0;
    let mut out=Vec::with_capacity(config::UPPER_LEN[which]);
    let mut emit=|mut r:Row|{
        if si<switches.len() && at==switches[si].0{
            let new=switches[si].1;
            if hole!=anchor && new!=anchor{
                out.extend([[8,hole,new,N],[8,new,hole,N]]);
            }
            hole=new;si+=1;
        }
        let k=super::arity(r[0]);
        for q in &mut r[1..1+k] {assert_ne!(*q,hole);if *q==anchor{*q=hole;}}
        out.push(r);at+=1;
    };
    for &r in config::PRE[tag]{emit(r);}
    let mut ports=columns::Ports::handover();
    for c in 65..=127{
        let m=ports.canonical_map();
        let mut words=Vec::new();
        columns::canonical_column(c,|w|{
            let tr=|q:u32|if q==1023{q}else{m[q as usize] as u32};
            words.push(tr(w>>20)<<20 | tr(w>>10&1023)<<10 | tr(w&1023));
        });
        let mut start=0;
        for &end in config::MARKS[c-65]{
            for w in compact(&words[start..end],c){
                let a=(w>>20) as usize;let b=((w>>10)&1023) as usize;
                let t=wires[(w&1023) as usize];
                let r=if a!=1023{[13,wires[a],wires[b],t]}else if b!=1023{[8,wires[b],t,N]}else{[6,t,N,N]};
                emit(r);
            }
            start=end;
        }
        assert_eq!(start,words.len());ports.advance();
    }
    for &r in config::POST[tag]{emit(r);}
    for (i,&r) in raw.iter().enumerate(){
        if i>=config::FCORE[which] || matches!(r[0],15|16){emit(r);}
    }
    assert_eq!(si,switches.len());out
}

pub fn adjoint(raw:&[Row],forward:&[Row],which:usize)->Vec<Row>{
    let tag=which*2+1;
    let mut out=Vec::with_capacity(forward.len()+65536);
    out.extend_from_slice(&raw[..381]);out.extend_from_slice(config::PRE[tag]);
    for &r in forward[..config::FCORE[which]].iter().rev(){
        if !matches!(r[0],15|16){out.push(mapped(r,config::WIRES[tag]));}
    }
    out.extend_from_slice(config::POST[tag]);
    for &r in &raw[381..]{
        match r[0]{3|4|5|15|16=>out.push(r),12=>out.push([12,config::CLEAN[which],r[2],r[3]]),_=>()}
    }
    for &(a,b) in config::FIX[which]{out.extend([[8,a,b,N],[8,b,a,N],[8,a,b,N]]);}
    out
}

pub fn front(which:usize,capped:bool)->Vec<Row>{
    let mut body=cap::generate(which,capped);
    let len=body.len();
    let n=super::super::peephole(&mut body,len);
    let n=super::super::neg_controls(&mut body,n);
    let n=super::super::peephole(&mut body,n); body.truncate(n);
    if capped{
        use post_pass::Step::*;
        let mut out=Vec::with_capacity(n);
        for chunk in body.chunks(4_000_000){
            out.extend(post_pass::run_chunk(post_pass::cap_rgp(chunk.to_vec()),&[Schn,Swp,Gm,Q23,Gm2,Q23b]));
        }
        body=out;
    }
    let mut out=Vec::with_capacity(body.len()+4096);
    let helper=[596,604][which];
    let pair=[[12,helper,65534,N],[4,65534,N,N]];
    if !capped{
        if which==0{for _ in 0..126{out.extend(pair);}}
        else{
            out.extend([[16,N,N,N],[3,768,N,N],[15,768,N,N],[8,507,614,N],[8,614,507,N],[16,N,N,N],[3,768,N,N],[15,768,N,N]]);
            out.extend(pair);out.extend(pair);
        }
    }
    for r in body{out.push(mapped(r,config::CAP_MAP[which]));}
    if !capped && which==0{out.extend(pair);out.extend(pair);}
    out.extend_from_slice(config::CAP_POST[which*2+usize::from(capped)]);
    out
}
