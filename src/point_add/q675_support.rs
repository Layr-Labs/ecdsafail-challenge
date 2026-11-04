//! Source-bound N258 routing and five-slot handoff primitives.
use super::{builder::{B,G},frogdrop_col::{rec,Fd,ColScr}};
use crate::circuit::QubitId;
include!("q675_hr_route.rs");
include!("q675_ht_route.rs");
fn transpose_gap(b:&mut B,sy:&[QubitId],gap:&[QubitId],size:u8,a:u8,z:u8,guards:&[QubitId],dirty:&[QubitId]){
    assert!(a<32&&z<32&&a!=z);
    let mut path=vec![a];let mut cur=a;
    for bit in 0..5{if (a^z)>>bit&1!=0{cur^=1<<bit;path.push(cur);}}
    assert_eq!(cur,z);
    let step=|b:&mut B,u:u8,v:u8|{
        let bit=(u^v).trailing_zeros()as usize;
        let mut ctl:Vec<_>=(0..7).map(|i|(sy[i],size>>i&1==0)).collect();
        ctl.extend(guards.iter().map(|&q|(q,true)));
        ctl.extend((0..5).filter(|&i|i!=bit).map(|i|(gap[i],u>>i&1==0)));
        super::mask::mc_xor(b,&ctl,gap[bit],&[],dirty);
    };
    for pair in path.windows(2){step(b,pair[0],pair[1]);}
    for i in(1..path.len()-1).rev(){step(b,path[i-1],path[i]);}
}
pub(crate) fn route_ht3(b:&mut B,fam:usize,sy:&[QubitId],gap:&[QubitId],owners:&[QubitId;4],guards:&[QubitId],dirty:&[QubitId]){
    for &(f,size,op,o,a,z,m,v) in HT3_TERMS {
        if f as usize!=fam{continue;}
        if op==4{transpose_gap(b,sy,gap,size,a,z,guards,dirty);continue;}
        let mut ctl:Vec<_>=(0..7).map(|i|(sy[i],size>>i&1==0)).collect();
        ctl.extend(guards.iter().map(|&q|(q,true)));
        for i in 0..5{if m>>i&1!=0{ctl.push((gap[i],v>>i&1==0));}}
        match op {
            0=>super::mid2::mc_swap(b,&ctl,owners[o as usize],gap[a as usize],&[],dirty),
            1=>{ctl.push((owners[o as usize],false));super::mask::mc_xor(b,&ctl,gap[a as usize],&[],dirty);},
            2=>{ctl.push((owners[o as usize],false));super::mid2::mc_swap(b,&ctl,gap[a as usize],gap[z as usize],&[],dirty);},
            3=>super::mask::mc_xor(b,&ctl,owners[o as usize],&[],dirty),
            _=>unreachable!(),
        }
    }
}
pub(crate) fn route_hr3(b:&mut B,fam:usize,sy:&[QubitId],gap:&[QubitId],owners:&[QubitId;4],guards:&[QubitId],dirty:&[QubitId]){
    for &(f,size,op,o,a,z,m,v) in HR3_TERMS {
        if f as usize!=fam {continue;}
        let mut ctl:Vec<_>=(0..7).map(|i|(sy[i],size>>i&1==0)).collect();
        ctl.extend(guards.iter().map(|&q|(q,true)));
        for i in 0..5 {if m>>i&1!=0 {ctl.push((gap[i],v>>i&1==0));}}
        match op {
            0=>super::mid2::mc_swap(b,&ctl,owners[o as usize],gap[a as usize],&[],dirty),
            1=>{ctl.push((owners[o as usize],false));super::mask::mc_xor(b,&ctl,gap[a as usize],&[],dirty);},
            2=>{ctl.push((owners[o as usize],false));super::mid2::mc_swap(b,&ctl,gap[a as usize],gap[z as usize],&[],dirty);},
            3=>super::mask::mc_xor(b,&ctl,owners[o as usize],&[],dirty),
            _=>unreachable!(),
        }
    }
}
pub(crate) const ROUTES:&[(i8,u8,u8,u8,u8,u8)]=&[(2,121,2,4,0,0),(3,121,2,4,0,0),(1,122,3,4,0,0),(2,122,3,4,0,0),(3,122,3,4,0,0),(3,122,2,1,12,12),(0,123,3,4,0,0),(1,123,3,4,0,0),(2,123,3,4,0,0),(3,123,3,4,0,0),(4,123,3,4,0,0),(4,123,2,2,8,8),(1,124,3,4,0,0),(2,124,3,4,0,0),(2,124,2,3,4,4),(2,124,2,1,12,8),(3,124,3,4,0,0),(3,124,2,1,8,8),(3,124,1,2,8,8),(0,125,2,3,0,0),(0,125,3,4,0,0),(1,125,2,3,0,0),(1,125,3,4,0,0),(2,125,2,3,0,0),(2,125,3,4,0,0),(3,125,2,3,0,0),(3,125,3,4,0,0),(-1,126,3,3,0,0),(0,126,2,3,0,0),(0,126,3,4,0,0),(1,126,3,3,0,0),(1,126,2,4,0,0),(2,126,3,3,0,0),(2,126,2,4,0,0),(3,126,3,3,0,0),(3,126,2,4,0,0),(4,126,3,3,0,0),(4,126,2,4,0,0),(4,126,1,1,4,4),(-1,127,2,2,0,0),(-1,127,3,3,0,0),(0,127,1,2,0,0),(0,127,2,3,0,0),(0,127,3,4,0,0),(1,127,2,2,0,0),(1,127,3,3,0,0),(1,127,1,4,0,0),(2,127,2,2,0,0),(2,127,3,3,0,0),(2,127,1,4,0,0),(3,127,2,2,0,0),(3,127,3,3,0,0),(3,127,1,4,0,0),(4,127,2,2,0,0),(4,127,3,3,0,0),(-1,128,1,1,0,0),(-1,128,2,2,0,0),(-1,128,3,3,0,0),(0,128,0,1,0,0),(0,128,1,2,0,0),(0,128,2,3,0,0),(0,128,3,4,0,0),(1,128,1,1,0,0),(1,128,2,2,0,0),(1,128,3,3,0,0),(1,128,0,4,0,0),(2,128,1,1,0,0),(2,128,2,2,0,0),(2,128,3,3,0,0),(3,128,1,1,0,0),(3,128,2,2,0,0),(3,128,3,3,0,0),(4,128,1,1,0,0),(4,128,2,2,0,0),(4,128,3,3,0,0)];
pub(crate) fn route(b:&mut B,fam:i8,sy:&[QubitId],gap:&[QubitId],owners:&[QubitId],guards:&[QubitId],dirty:&[QubitId],omit_fourth:bool){
 for &(f,size,o,t,m,v) in ROUTES {
  if f!=fam || (omit_fourth&&o==3){continue;}
  assert_eq!(m&(1<<t),0);
  let mut ctl:Vec<_>=(0..7).map(|i|(sy[i],(size>>i)&1==0)).collect();
  ctl.extend(guards.iter().map(|&q|(q,true)));
  for i in 0..5 {if m>>i&1!=0 {ctl.push((gap[i],v>>i&1==0));}}
  super::mid2::mc_swap(b,&ctl,owners[o as usize],gap[t as usize],&[],dirty);
 }
}
pub(crate) const CUTS:[[usize;6];128]=[[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,3,8,13,18,23],[0,2,7,12,17,22],[0,5,10,15,20,20],[0,3,8,13,18,18],[0,2,6,11,16,16],[0,1,5,9,14,14],[0,2,4,6,8,12],[0,1,3,6,10,10],[0,2,4,6,8,8],[0,1,2,3,4,6],[0,1,2,3,4,4],[0,1,2,2,2,2]];
pub(crate) fn park(b:&mut B,fd:&Fd,sc:&ColScr,fam:usize){super::q675_lookup::park(b,fd,sc,fam,false);}
pub(crate) fn park_literal(b:&mut B,fd:&Fd,sc:&ColScr,fam:usize){
    assert!(fam<5);assert_eq!(fd.sx.len(),8);assert_eq!(fd.sy.len(),8);
    for sy in 1..=128 {
        let len=CUTS[sy-1][fam+1]-CUTS[sy-1][fam];assert!(len<=5&&sy+len<=129);
        let mut ctl:Vec<_>=(0..8).map(|i|(fd.sy[i],sy>>i&1==0)).collect();ctl.push((sc.g,false));
        for i in 0..len {let target=if sy+i<128{fd.q[sy+i]}else{sc.bq};
            assert!(!ctl.iter().any(|(q,_)|*q==target||*q==fd.sx[1+i]));
            assert!(!sc.dirty.contains(&target)&&!sc.dirty.contains(&fd.sx[1+i]));
            super::mid2::mc_swap(b,&ctl,fd.sx[1+i],target,&[],&sc.dirty);
        }
    }
}
#[allow(clippy::too_many_arguments)]
pub(crate) fn parked_forms(b:&mut B,prot:&[G],sg:&[G],u:&[G],fv:&[G],fr:&[G],vh1:Option<QubitId>,
    sy:&[QubitId],gap:&[QubitId],owners:[QubitId;4],sw:Option<QubitId>,
    old:(&[G],QubitId,QubitId,QubitId),dirty:&[QubitId],hr3:bool,ht3:bool)->Vec<Vec<G>>{
    assert!(!(hr3&&ht3));
    (0..if hr3||ht3 {3}else{5}).map(|family|{
        let mut guards=vec![old.1];if let Some(q)=sw{guards.push(q);}
        let route=rec(b,|b|if hr3 {route_hr3(b,family,sy,gap,&owners,&guards,dirty)}
                         else if ht3{route_ht3(b,family,sy,gap,&owners,&guards,dirty)}
                         else {route(b,family as i8,sy,gap,&owners,&guards,dirty,false)});
        let inv=rec(b,|b|b.play(old.0,true));
        let inactive=|b:&mut B,r:&[G]|{
            if let Some(q)=sw{
                b.cx(old.1,old.2);b.cx(q,old.2);b.ccx(old.1,q,old.2);
                b.play_ctrl_full(r,old.2,old.3);
                b.ccx(old.1,q,old.2);b.cx(q,old.2);b.cx(old.1,old.2);
            }else{b.play_ctrl_full(r,old.1,old.2);}
        };
        rec(b,|b|{
            b.play(prot,false);b.play(sg,false);b.play(&route,false);inactive(b,old.0);b.play(u,false);
            if let Some(q)=vh1{b.x(q);}b.play(fv,false);b.play(fr,true);if let Some(q)=vh1{b.x(q);}
            b.play(u,true);inactive(b,&inv);b.play(&route,true);b.play(sg,false);b.play(prot,true);
        })
    }).collect()
}

#[cfg(test)]
mod b9b_hr3_route_tests {
    use super::*;
    use super::super::tests_frogdrop::run;
    use crate::circuit::OperationType;

    fn model(fam:usize,sy:usize,mut x:u16,active:bool)->u16 {
        if !active{return x;}
        for &(f,size,op,owner,a,z,mask,ones) in HR3_TERMS {
            if f as usize!=fam || (sy&127)!=(size as usize&127) || (x as u8&mask)!=ones {continue;}
            let ob=5+owner as usize;
            match op {
                0=>{let aa=a as usize;if (x>>ob^x>>aa)&1!=0{x^=(1<<ob)|(1<<aa);}},
                1=>{if x>>ob&1!=0{x^=1<<a;}},
                2=>{let aa=a as usize;let zz=z as usize;if x>>ob&1!=0 && (x>>aa^x>>zz)&1!=0{x^=(1<<aa)|(1<<zz);}},
                3=>x^=1<<ob,
                _=>unreachable!(),
            }
        }
        x
    }

    fn model_ht(fam:usize,sy:usize,mut x:u16,active:bool)->u16 {
        if !active{return x;}
        for &(f,size,op,owner,a,z,mask,ones) in HT3_TERMS {
            if f as usize!=fam || (sy&127)!=(size as usize&127){continue;}
            if op==4{let g=x&31;if g==a as u16{x=(x&!31)|z as u16;}else if g==z as u16{x=(x&!31)|a as u16;}continue;}
            if (x as u8&mask)!=ones{continue;}
            let ob=5+owner as usize;
            match op {
                0=>{let aa=a as usize;if (x>>ob^x>>aa)&1!=0{x^=(1<<ob)|(1<<aa);}},
                1=>{if x>>ob&1!=0{x^=1<<a;}},
                2=>{let aa=a as usize;let zz=z as usize;if x>>ob&1!=0&&(x>>aa^x>>zz)&1!=0{x^=(1<<aa)|(1<<zz);}},
                3=>x^=1<<ob,
                _=>unreachable!(),
            }
        }
        x
    }

    #[test]
    fn b9b_hr3_route_all_wire(){
        let cases:Vec<(usize,usize,usize,usize)>=include_str!("b9b_hr_route_cases.tsv").lines().map(|line|{
            let v:Vec<_>=line.split_whitespace().map(|x|x.parse::<usize>().unwrap()).collect();
            (v[0],v[1],v[2],v[3])
        }).collect();
        assert_eq!(cases.len(),9779);
        let mut total=0usize;
        for fam in 0..3 {
            let(mut b,fd,pool,dirty)=super::super::q675_layout_tests::ports(258);
            let sc=super::super::frogdrop_col::ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
            let gap=&sc.sz[..5];let owners=[sc.bq,fd.q[127],fd.q[126],fd.q[125]];
            let guards=[fd.ph,sc.sw];
            b.begin();route_hr3(&mut b,fam,&fd.sy[..7],gap,&owners,&guards,&dirty);
            let r=b.end();b.play(&r,false);let forward=b.ops.len();b.play(&r,true);
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let selected:Vec<_>=cases.iter().filter(|c|c.0==fam).collect();
            for chunk in selected.chunks(64){for tape in 0..3{for mode in 0..3{
                let mut input=vec![0u64;b.width()as usize];let valid=if chunk.len()==64{u64::MAX}else{(1u64<<chunk.len())-1};
                for(lane,&&(_,sy,g,owner))in chunk.iter().enumerate(){
                    for i in 0..8{if sy>>i&1!=0{input[fd.sy[i].0 as usize]|=1<<lane;}}
                    for i in 0..5{if g>>i&1!=0{input[gap[i].0 as usize]|=1<<lane;}}
                    for i in 0..4{if owner>>i&1!=0{input[owners[i].0 as usize]|=1<<lane;}}
                }
                for(i,&q)in dirty.iter().enumerate(){input[q.0 as usize]=match tape{0=>0,1=>u64::MAX,_=>0x9e3779b97f4a7c15u64.rotate_left((i*7)as u32)};}
                input[guards[0].0 as usize]=if mode==1{u64::MAX}else{!valid};
                input[guards[1].0 as usize]=if mode==2{u64::MAX}else{0};
                let mut want=input.clone();
                for(lane,&&(_,sy,g,owner))in chunk.iter().enumerate(){
                    let active=mode==0;let z=model(fam,sy,(g|(owner<<5))as u16,active);
                    if active{assert_eq!(z>>5,0,"fam={fam} sy={sy} g={g} owner={owner}");}
                    for(i,&q)in gap.iter().chain(owners.iter()).enumerate(){
                        want[q.0 as usize]=(want[q.0 as usize]&!(1<<lane))|((((z>>i)&1)as u64)<<lane);
                    }
                }
                let result=run(&b.ops[..forward],b.width()as usize,&|q|*q=input.clone());
                assert_eq!(result.q,want,"forward fam={fam} tape={tape} mode={mode}");assert_eq!(result.phase,0);
                let back=run(&b.ops,b.width()as usize,&|q|*q=input.clone());
                assert_eq!(back.q,input,"inverse fam={fam} tape={tape} mode={mode}");assert_eq!(back.phase,0);
                total+=chunk.len();
            }}}
        }
        eprintln!("B9B_HR3_ROUTE_PASS cases={total} public_owner_cases={} dirty=3 guards=3 inverse=true phase=0",cases.len());
    }

    #[test]
    fn b9b_ht3_route_all_wire(){
        let cases:Vec<(usize,usize,usize,usize)>=include_str!("b9b_ht_route_cases.tsv").lines().map(|line|{
            let v:Vec<_>=line.split_whitespace().map(|x|x.parse::<usize>().unwrap()).collect();
            (v[0],v[1],v[2],v[3])
        }).collect();
        assert_eq!(cases.len(),9990);
        let mut total=0usize;
        for fam in 0..3 {
            let(mut b,fd,pool,dirty)=super::super::q675_layout_tests::ports(258);
            let sc=super::super::frogdrop_col::ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
            let gap=&sc.sz[..5];let owners=[sc.bq,fd.q[127],fd.q[126],fd.q[125]];let guards=[fd.ph,sc.sw];
            b.begin();route_ht3(&mut b,fam,&fd.sy[..7],gap,&owners,&guards,&dirty);
            let r=b.end();b.play(&r,false);let forward=b.ops.len();b.play(&r,true);
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let selected:Vec<_>=cases.iter().filter(|c|c.0==fam).collect();
            for chunk in selected.chunks(64){for tape in 0..3{for mode in 0..3{
                let mut input=vec![0u64;b.width()as usize];let valid=if chunk.len()==64{u64::MAX}else{(1u64<<chunk.len())-1};
                for(lane,&&(_,sy,g,owner))in chunk.iter().enumerate(){
                    for i in 0..8{if sy>>i&1!=0{input[fd.sy[i].0 as usize]|=1<<lane;}}
                    for i in 0..5{if g>>i&1!=0{input[gap[i].0 as usize]|=1<<lane;}}
                    for i in 0..4{if owner>>i&1!=0{input[owners[i].0 as usize]|=1<<lane;}}
                }
                for(i,&q)in dirty.iter().enumerate(){input[q.0 as usize]=match tape{0=>0,1=>u64::MAX,_=>0x243f6a8885a308d3u64.rotate_left((i*11)as u32)};}
                input[guards[0].0 as usize]=if mode==1{u64::MAX}else{!valid};
                input[guards[1].0 as usize]=if mode==2{u64::MAX}else{0};
                let mut want=input.clone();
                for(lane,&&(_,sy,g,owner))in chunk.iter().enumerate(){
                    let active=mode==0;let z=model_ht(fam,sy,(g|(owner<<5))as u16,active);
                    if active{assert_eq!(z>>5,0,"fam={fam} sy={sy} g={g} owner={owner}");}
                    for(i,&q)in gap.iter().chain(owners.iter()).enumerate(){
                        want[q.0 as usize]=(want[q.0 as usize]&!(1<<lane))|((((z>>i)&1)as u64)<<lane);
                    }
                }
                let result=run(&b.ops[..forward],b.width()as usize,&|q|*q=input.clone());
                assert_eq!(result.q,want,"forward fam={fam} tape={tape} mode={mode}");assert_eq!(result.phase,0);
                let back=run(&b.ops,b.width()as usize,&|q|*q=input.clone());
                assert_eq!(back.q,input,"inverse fam={fam} tape={tape} mode={mode}");assert_eq!(back.phase,0);
                total+=chunk.len();
            }}}
        }
        eprintln!("B9B_HT3_ROUTE_PASS cases={total} public_owner_cases={} dirty=3 guards=3 inverse=true phase=0",cases.len());
    }

    #[test]
    fn b9b_o5_final_routes_all_wire(){
        let cases:Vec<(bool,usize,usize,usize)>=include_str!("b9b_o5_route_cases.tsv").lines().map(|line|{
            let v:Vec<_>=line.split_whitespace().collect();assert_eq!(v.len(),4);
            (v[0]=="HT",v[1].parse().unwrap(),v[2].parse().unwrap(),v[3].parse().unwrap())
        }).collect();
        assert_eq!(cases.len(),23864);
        let mut total=0usize;
        for ht in [false,true]{for fam in 0..3{
            let(mut b,fd,pool,dirty)=super::super::q675_layout_tests::ports(258);
            let sc=super::super::frogdrop_col::ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
            let gap=&sc.sz[..5];let owners=[sc.bq,fd.q[127],fd.q[126],fd.q[125]];let guards=[fd.ph,sc.sw];
            b.begin();if ht{route_ht3(&mut b,fam,&fd.sy[..7],gap,&owners,&guards,&dirty);}
                      else{route_hr3(&mut b,fam,&fd.sy[..7],gap,&owners,&guards,&dirty);}
            let route=b.end();b.play(&route,false);let forward=b.ops.len();b.play(&route,true);
            assert!(b.ops.iter().all(|op|matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX)));
            let selected:Vec<_>=cases.iter().filter(|c|c.0==ht&&c.1==fam).collect();
            for chunk in selected.chunks(64){for tape in 0..3{for mode in 0..4{
                let mut input=vec![0u64;b.width()as usize];
                let valid=if chunk.len()==64{u64::MAX}else{(1u64<<chunk.len())-1};
                for(lane,&&(_,_,sy,x))in chunk.iter().enumerate(){
                    for i in 0..8{if sy>>i&1!=0{input[fd.sy[i].0 as usize]|=1<<lane;}}
                    for i in 0..5{if x>>i&1!=0{input[gap[i].0 as usize]|=1<<lane;}}
                    for i in 0..4{if x>>(5+i)&1!=0{input[owners[i].0 as usize]|=1<<lane;}}
                }
                for(i,&q)in dirty.iter().enumerate(){input[q.0 as usize]=match tape{
                    0=>0,1=>u64::MAX,_=>0x9e3779b97f4a7c15u64.rotate_left((i*11)as u32)};}
                input[guards[0].0 as usize]=if mode==1||mode==3{u64::MAX}else{!valid};
                input[guards[1].0 as usize]=if mode==2||mode==3{u64::MAX}else{0};
                let mut want=input.clone();
                for(lane,&&(_,_,sy,x))in chunk.iter().enumerate(){
                    let active=mode==0;
                    let z=if ht{model_ht(fam,sy,x as u16,active)}else{model(fam,sy,x as u16,active)};
                    if active{assert_eq!(z>>5,0,"kind={} fam={fam} sy={sy} input={x}",if ht{"HT"}else{"HR"});}
                    for(i,&q)in gap.iter().chain(owners.iter()).enumerate(){
                        want[q.0 as usize]=(want[q.0 as usize]&!(1<<lane))|((((z>>i)&1)as u64)<<lane);
                    }
                }
                let got=run(&b.ops[..forward],b.width()as usize,&|q|*q=input.clone());
                assert_eq!(got.q,want,"route kind={} fam={fam} tape={tape} mode={mode}",if ht{"HT"}else{"HR"});
                assert_eq!(got.phase,0);
                let back=run(&b.ops,b.width()as usize,&|q|*q=input.clone());
                assert_eq!(back.q,input);assert_eq!(back.phase,0);
                total+=chunk.len();
            }}}
        }}
        eprintln!("B9B_O5_FINAL_ROUTES_PASS inputs={} lane_cases={total} dirty=3 guards=4 inverse=true phase=0",cases.len());
    }
}
