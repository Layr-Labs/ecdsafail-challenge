//! Active C/S counters controlled directly by phase bits, skipping rawA255.
//! Already-terminal inputs have phase00; active rawA<=254.
//! No separate aggregate guard or borrowed work-word zero is allocated.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_rank5,length_recompute::mixed_mcx};
use crate::circuit::OperationType;
use crate::sim::Simulator;
use sha3::digest::XofReader;
use std::collections::BTreeMap;
#[path="metadata_remainder5_programs.rs"] mod programs;
fn triples()->Vec<[usize;3]> {(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn implicit_ls1(phase:usize,j:usize,c:usize)->usize {let base=if phase<=1{j}else{(4-j)%4};((base>>1)^if [1,2].contains(&phase){c&1}else{0})&1}
fn small(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],p1:&QReg,p2:&QReg,extras:&[(&QReg,bool)],helpers:&[QReg],phase:usize,subtract:bool) {
    for k in 0..word.len() {let i=if subtract{k}else{word.len()-1-k};
        let mut cs=vec![(p1,true),(p2,phase%2!=0)];cs.extend_from_slice(extras);cs.extend(word[..i].iter().map(|q|(q,true)));
        mixed_mcx(circ,&cs,&word[i],helpers);
        if phase!=0{continue;}
        // Only phase00 can be already terminal; cancel at Ahigh3/Alow63.
        cs.extend(a.iter().map(|q|(q,true)));
        for &(m,v) in programs::EQUAL[3] {
            let mut term=cs.clone();term.extend((0..5).filter(|&b|m>>b&1!=0).map(|b|(&rank[b],v>>b&1!=0)));
            mixed_mcx(circ,&term,&word[i],helpers);
        }
    }
}
fn high(circ:&mut Circuit,rank:&[QReg],a:&[QReg],p1:&QReg,p2:&QReg,extras:&[(&QReg,bool)],helpers:&[QReg],phase:usize,axis:usize,reverse:bool) {
    assert!(axis==1||axis==2);let ts=triples();let mut groups:BTreeMap<Vec<usize>,Vec<(usize,usize)>>=BTreeMap::new();
    for (r,t) in ts.iter().enumerate(){groups.entry(t.iter().enumerate().filter(|(i,_)|*i!=axis).map(|(_,v)|*v).collect()).or_default().push((t[axis],r));}
    let rows:Vec<_>=groups.values_mut().map(|row|{row.sort();row.iter().map(|p|p.1).collect::<Vec<_>>()}).collect();
    let flag=&helpers[0];let dirty=&helpers[1..];
    let mut controls=vec![(p1,true),(p2,phase%2!=0)];controls.extend_from_slice(extras);
    let start=circ.b.ops.len();
    // A row rotation is R1 R0, where Rk maps index i to k-i (mod row length).
    // Each Rk is an involution, so dirty-flag echo applies it under the full
    // carry/phase predicate while only one flag controls its rank gates.
    for offset in 0..2 {
        let reflect=|circ:&mut Circuit| {for row in &rows {for i in 0..row.len() {
            let other=(offset+row.len()-i)%row.len();if i>=other{continue;}
            metadata_rank5::basis_swap(circ,rank,flag,&[],dirty,row[i],row[other]);
            if phase==0&&ts[row[0]][0]==3 {
                let terminal:Vec<_>=a.iter().map(|q|(q,true)).collect();
                metadata_rank5::basis_swap(circ,rank,flag,&terminal,dirty,row[i],row[other]);
            }
        }}};
        reflect(circ);mixed_mcx(circ,&controls,flag,dirty);
        reflect(circ);mixed_mcx(circ,&controls,flag,dirty);
    }
    if reverse{circ.b.ops[start..].reverse();}
}
fn phase_body(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,helpers:&[QReg],phase:usize,j:usize) {
    if phase==0||phase==3 {
        let sub=phase==3;let low=2*implicit_ls1(phase,j,0)+(j&1);let carry=if sub {low==0}else{low==3};
        if carry {let extras:Vec<_>=sm.iter().map(|q|(q,!sub)).collect();high(circ,rank,a,p1,p2,&extras,helpers,phase,2,sub);small(circ,rank,a,sm,p1,p2,&[],helpers,phase,sub);}
        return;
    }
    let sub_s=phase==1;let carry_s=if sub_s {j%2==0}else{j%2!=0};let needed_c0=(usize::from(!sub_s)^implicit_ls1(phase,j,0))!=0;
    let mut s_extras:Vec<_>=sm.iter().map(|q|(q,!sub_s)).collect();s_extras.push((&c[0],needed_c0));let c_extras:Vec<_>=c.iter().map(|q|(q,phase==1)).collect();
    if sub_s {
        if carry_s {high(circ,rank,a,p1,p2,&s_extras,helpers,phase,2,true);}
        high(circ,rank,a,p1,p2,&c_extras,helpers,phase,1,false);
    } else {
        high(circ,rank,a,p1,p2,&c_extras,helpers,phase,1,true);
        if carry_s {high(circ,rank,a,p1,p2,&s_extras,helpers,phase,2,false);}
    }
    // Simultaneous modulo256 wrap: repair only the two affected row endpoints.
    if (phase==1&&j==2)||(phase==2&&j==1) {
        let mut both=c_extras.clone();both.extend(sm.iter().map(|q|(q,phase==2)));
        let (left,right)=if phase==1 {(1,3)}else{(4,11)};
        both.push((p2,phase%2!=0));metadata_rank5::basis_swap(circ,rank,p1,&both,helpers,left,right);
    }
    if carry_s {small(circ,rank,a,sm,p1,p2,&[(&c[0],needed_c0)],helpers,phase,sub_s);}
    small(circ,rank,a,c,p1,p2,&[],helpers,phase,phase==2);
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,helpers:&[QReg],j:usize) {
    assert!(j<4&&helpers.len()>=23);let start=circ.b.ops.len();
    for phase in 0..4 {if phase<2{circ.x(p1);}phase_body(circ,rank,a,c,sm,p1,p2,helpers,phase,j);if phase<2{circ.x(p1);}}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,256,8);super::shared_optimize::cancel_nct_live(&mut tail,256);circ.b.ops.extend(tail);
}
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let bit=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!bit)|if v{bit}else{0};}
pub fn run() {
    let ts=triples();let mut index=[usize::MAX;64];for(i,t)in ts.iter().enumerate(){index[16*t[0]+4*t[1]+t[2]]=i;}
    let mut total=0;let mut terminal=0;
    for j in 0..4 {
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let helpers=circ.alloc_qreg_bits("dirty",24);let owned=circ.b.next_qubit;
        emit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&helpers,j);assert_eq!(circ.b.next_qubit,owned);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,OperationType::X|OperationType::CX|OperationType::CCX));}
        eprintln!("CODEC_PHASE_COUNTER5_BUILT j={j} T={} ops={} metadata=21 phase=2 borrowed=24",b.ops.iter().filter(|o|o.kind==OperationType::CCX).count(),b.ops.len());
        let mut cases=Vec::new();
        for phase in 0..4 {for (r,&[ah,ch,sh]) in ts.iter().enumerate(){for al in 0..64 {for cl in 0..64 {for sl in 0..16 {
            let av=64*ah+al;let cv=64*ch+cl;let sv=64*sh+4*sl+2*implicit_ls1(phase,j,cv)+(j&1);
            let cn=if phase==1{(cv+1)&255}else if phase==2{(cv+255)&255}else{cv};let sn=if [0,2].contains(&phase){(sv+1)&255}else{(sv+255)&255};
            let is_terminal=av==255;
            if is_terminal&&phase!=0{continue;}
            if !is_terminal&&(av+cv+sv>257||av+cn+sn>257){continue;}
            let rr=if is_terminal{r}else{index[16*ah+4*(cn>>6)+(sn>>6)]};assert_ne!(rr,usize::MAX);
            cases.push((phase,r,rr,al,cl,sl,if is_terminal{cv}else{cn},if is_terminal{sv}else{sn},is_terminal));
        }}}}}
        for batch in 0..cases.len().div_ceil(64){
            let mut seed=0x2179e4bc98356dafu64^batch as u64^((j as u64)<<35);let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64 {let (phase,r,rr,al,cl,sl,cn,sn,is_terminal)=cases[(batch*64+lane)%cases.len()];
                for i in 0..5{put(&mut before,&rank[i],lane,r>>i&1!=0);put(&mut after,&rank[i],lane,rr>>i&1!=0);}
                for i in 0..6{put(&mut before,&c[i],lane,cl>>i&1!=0);put(&mut after,&c[i],lane,cn>>i&1!=0);for w in [&mut before,&mut after]{put(w,&a[i],lane,al>>i&1!=0);}}
                for i in 0..4{put(&mut before,&sm[i],lane,sl>>i&1!=0);put(&mut after,&sm[i],lane,sn>>(i+2)&1!=0);}
                for w in [&mut before,&mut after]{put(w,&p1,lane,phase&2!=0);put(w,&p2,lane,phase&1!=0);}terminal+=usize::from(is_terminal);
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,after,"phase counter j={j} batch={batch}");assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
        eprintln!("CODEC_PHASE_COUNTER5_CASE j={j} records={} PASS",cases.len());
    }
    eprintln!("CODEC_PHASE_COUNTER5_PASS lanes={total} terminal_lanes={terminal}; all low A and four phases, actual phase controls, no aggregate guard, dirty and phase restored; full Q799 missing");
}
