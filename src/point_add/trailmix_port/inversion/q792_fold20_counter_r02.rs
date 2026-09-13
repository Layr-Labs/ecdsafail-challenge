//! Direct twenty-wire C/S counter composition. Own component, not wholeQ792.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="q792_fold20_counter_plan_r02.rs"]mod plan;
fn exchange(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],x:usize,y:usize,free:usize){
    let delta=x^y;let fixed=((1usize<<20)-1)^free;let pivot=(delta&fixed).trailing_zeros()as usize;assert!(pivot<20);
    let base=if x>>pivot&1==0{x}else{y};
    for i in 0..20{if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
    let mut cs=prefix.to_vec();cs.extend((0..20).filter(|&i|i!=pivot&&fixed>>i&1!=0).map(|i|(&m[i],base>>i&1!=0)));mixed_mcx(c,&cs,&m[pivot],dirty);
    for i in (0..20).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
}
// Equal affine transpositions on disjoint coarse-code cylinders commute.
// Share their linear conjugation and synthesize the exact union predicate.
fn exchange_group(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],group:&[(usize,usize,usize)]){
    if group.len()==1{let(x,y,free)=group[0];exchange(c,m,prefix,dirty,x,y,free);return;}
    let(x,y,free)=group[0];let fixed=((1usize<<20)-1)^free;let delta=x^y;let pivot=(delta&fixed).trailing_zeros()as usize;let mut bases=Vec::new();
    for &(x,y,f)in group{assert_eq!(f,free);assert_eq!(x^y,delta);let base=if x>>pivot&1==0{x}else{y};assert!(!bases.iter().any(|b|b&fixed==base&fixed));bases.push(base);}
    let varying=bases.iter().fold(0usize,|v,b|v|(b^bases[0]))&fixed;let positions:Vec<_>=(0..20).filter(|&i|varying>>i&1!=0).collect();
    if positions.len()>6{for &(x,y,f)in group{exchange(c,m,prefix,dirty,x,y,f);}return;}
    let mut truth=vec![false;1<<positions.len()];for b in &bases{let code=positions.iter().enumerate().fold(0usize,|v,(i,p)|v|((b>>p&1)<<i));assert!(!truth[code]);truth[code]=true;}
    for i in 0..20{if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
    let mut cs=prefix.to_vec();cs.extend((0..20).filter(|&i|i!=pivot&&(fixed^varying)>>i&1!=0).map(|i|(&m[i],bases[0]>>i&1!=0)));
    super::q792_fold20_r01::table(c,&positions.iter().map(|&i|&m[i]).collect::<Vec<_>>(),truth,&cs,&m[pivot],dirty);
    for i in (0..20).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(&m[pivot],&m[i]);}}
}
fn branch(c:&mut Circuit,m:&[QReg],target:usize,forced:usize,d:&QReg,dirty:&[QReg]){
    let positions=[8usize,9,14,15,18,19];let live:Vec<_>=positions.iter().copied().filter(|&p|p!=target).collect();
    let mut truth=Vec::new();for code in 0..1usize<<live.len(){let mut value=0usize;for (i,&p)in positions.iter().enumerate(){let bit=if p==target{forced}else{code>>live.iter().position(|&x|x==p).unwrap()&1};value|=bit<<i;}truth.push((value&3)+(value>>2&3)+(value>>4&3)>=5);}
    super::q792_fold20_r01::table(c,&live.iter().map(|&p|&m[p]).collect::<Vec<_>>(),truth,&[],d,dirty);
}
fn atomic(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],field:usize,bit:usize,c0:Option<usize>){
    let offset=if field==0{10}else{16};let target=offset+bit;let mut base=prefix.to_vec();base.extend((0..bit).map(|i|(&m[offset+i],false)));if let Some(v)=c0{base.push((&m[10],v!=0));}
    mixed_mcx(c,&base,&m[target],dirty);
    let mut terminal=base.clone();terminal.extend(m[..4].iter().map(|q|(q,true)));terminal.push((&m[5],true));mixed_mcx(c,&terminal,&m[target],dirty);
    if bit==0&&c0.is_none(){return;}
    let d=&dirty[0];let rest=&dirty[1..];let tag:Vec<_>=m[..4].iter().collect();
    // The normal branch uses the maximum target cofactor, the reflected
    // branch the minimum. Admitted flips have both endpoints in the same
    // half. False carry cases remain false even beside the unused gap.
    for reflected in [false,true]{
        let mut controls=prefix.to_vec();controls.push((d,true));controls.extend((0..bit).map(|i|(&m[offset+i],reflected)));if let Some(v)=c0{controls.push((&m[10],(v!=0)^reflected));}
        let consume=|c:&mut Circuit|super::q792_fold20_r01::table(c,&tag,(0..16).map(|t|(10..15).contains(&t)).collect(),&controls,&m[target],rest);
        consume(c);branch(c,m,target,usize::from(!reflected),d,rest);consume(c);branch(c,m,target,usize::from(!reflected),d,rest);
    }
}
fn word(c:&mut Circuit,m:&[QReg],prefix:&[(&QReg,bool)],dirty:&[QReg],field:usize,c0:Option<usize>,subtract:bool){
    let at=c.b.ops.len();let n=if field==0{6}else{4};
    for bit in 0..n{atomic(c,m,prefix,dirty,field,bit,c0);}
    let hi=if field==0{0}else{1+c0.map(|x|x+1).unwrap_or(0)};
    let high=plan::HIGHS[hi];let mut start=0;while start<high.len(){let mut end=start+1;while end<high.len()&&high[end].2==high[start].2&&(high[end].0^high[end].1)==(high[start].0^high[start].1){end+=1;}exchange_group(c,m,prefix,dirty,&high[start..end]);start=end;}
    if subtract{c.b.ops[at..].reverse();}
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,dirty:&[QReg],j:usize){
    assert_eq!(m.len(),20);assert!(dirty.len()>=20&&j<4);let n=c.b.next_qubit;let at=c.b.ops.len();
    if j==3{word(c,m,&[(p1,false),(p2,false)],dirty,1,None,false);}
    if j%2==0{word(c,m,&[(p1,false),(p2,true)],dirty,1,Some(j/2),true);}
    word(c,m,&[(p1,false),(p2,true)],dirty,0,None,false);
    word(c,m,&[(p1,true),(p2,false)],dirty,0,None,true);
    if j%2==1{word(c,m,&[(p1,true),(p2,false)],dirty,1,Some(usize::from(j==1)),false);}
    if j==0{word(c,m,&[(p1,true),(p2,true)],dirty,1,None,true);}
    // Simultaneous modulo wraps cannot be decomposed through the simplex:
    // phase10 at j1: (C,S)=(0,255)->(255,0); phase01 at j2 is inverse.
    // Endpoint admissibility gives A<=2. Repair this COMPLETE scalar domain,
    // independent of EEA input points, test vectors and schedule sampling.
    if j==1||j==2{
        use crate::circuit::{OperationType as K,NO_QUBIT};
        use super::q792_fold20_rank_r01 as codec;
        let ts=codec::triples();let phase=if j==1{2}else{1};
        let (old_c,old_s,new_c,new_s)=if j==1{(0,255,255,0)}else{(255,0,0,255)};
        for a in 0..=2{
            let old_r=ts.iter().position(|t|*t==[0,old_c>>6,old_s>>6]).unwrap();
            let new_r=ts.iter().position(|t|*t==[0,new_c>>6,new_s>>6]).unwrap();
            let before=codec::encode(old_r,a,old_c&63,old_s>>2&15,&ts);
            let expected=codec::encode(new_r,a,new_c&63,new_s>>2&15,&ts);
            let mut bits=vec![false;n as usize];for i in 0..20{bits[m[i].id()as usize]=before>>i&1!=0;}
            bits[p1.id()as usize]=phase&2!=0;bits[p2.id()as usize]=phase&1!=0;
            for op in &c.b.ops[at..]{let target=op.q_target.0 as usize;assert_ne!(op.q_target,NO_QUBIT);match op.kind{K::X=>bits[target]^=true,K::CX=>bits[target]^=bits[op.q_control1.0 as usize],K::CCX=>bits[target]^=bits[op.q_control1.0 as usize]&bits[op.q_control2.0 as usize],_=>panic!("counter primitive type")}}
            assert!(dirty.iter().all(|q|!bits[q.id()as usize]));assert_eq!(bits[p1.id()as usize],phase&2!=0);assert_eq!(bits[p2.id()as usize],phase&1!=0);
            let got=(0..20).fold(0usize,|v,i|v|usize::from(bits[m[i].id()as usize])<<i);
            if got!=expected{exchange(c,m,&[(p1,phase&2!=0),(p2,phase&1!=0)],dirty,got,expected,0);}
        }
    }
    assert_eq!(n,c.b.next_qubit);
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    use super::q792_fold20_rank_r01 as codec;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let ts=codec::triples();let mut total=0u64;let mut active=0u64;
    for j in 0..4{
        let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;
        let m=circ.alloc_qreg_bits("fold20.metadata",20);let p1=circ.alloc_qreg("phase1");let p2=circ.alloc_qreg("phase2");let dirty=circ.alloc_qreg_bits("arbitrary_lenders",20);let n=circ.b.next_qubit;
        emit(&mut circ,&m,&p1,&p2,&dirty,j);let ops=circ.into_builder().ops;for op in &ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        eprintln!("FOLD20_COUNTER_R02_BUILT j={j} metadata=20 scratch_allocated=0 ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
        for phase in 0..4{
            let mut cases=Vec::new();
            for code in 0..1usize<<20{
                if let Some((r,a,cl,sm))=codec::decode(code,&ts){
                    let av=64*ts[r][0]+a;let cv=64*ts[r][1]+cl;
                    let base=if phase<2{j}else{(4-j)%4};let s1=(base/2)^if [1,2].contains(&phase){cv&1}else{0};
                    let sv=64*ts[r][2]+4*sm+2*s1+(j&1);
                    let cn=if phase==1{(cv+1)&255}else if phase==2{(cv+255)&255}else{cv};
                    let sn=if phase==0||phase==2{(sv+1)&255}else{(sv+255)&255};
                    if av+cv+sv>257||av+cn+sn>257{continue;}
                    let nr=ts.iter().position(|t|*t==[av>>6,cn>>6,sn>>6]).unwrap();
                    let next=codec::encode(nr,a,cn&63,sn>>2&15,&ts);
                    assert_eq!(codec::encode(r,a,cl,sm,&ts),code);cases.push((code,next));
                }
            }
            for pattern in 0..2{for first in (0..cases.len()).step_by(64){
                let mut seed=0x7925_c7af_9971u64^(first as u64)^((phase as u64)<<40)^((j as u64)<<44)^((pattern as u64)<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
                for w in [&mut before,&mut after]{w[p1.id()as usize]=if phase&2!=0{u64::MAX}else{0};w[p2.id()as usize]=if phase&1!=0{u64::MAX}else{0};}
                for lane in 0..64{let(code,next)=cases[(first+lane)%cases.len()];for bit in 0..20{for(w,value)in[(&mut before,code),(&mut after,next)]{let mask=1u64<<lane;w[m[bit].id()as usize]=(w[m[bit].id()as usize]&!mask)|(((value>>bit&1)as u64)<<lane);}}}
                let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());
                if sim.qubits!=after{let differences=sim.qubits.iter().zip(&after).fold(0u64,|mask,(x,y)|mask|(x^y));let lane=differences.trailing_zeros()as usize;let (input,expected)=cases[(first+lane)%cases.len()];let got=(0..20).fold(0usize,|v,i|v|(((sim.qubits[m[i].id()as usize]>>lane)&1)as usize)<<i);panic!("counter j={j} phase={phase} input={input} expected={expected} got={got} decoded={:?} expected_decoded={:?} actual_decoded={:?}",codec::decode(input,&ts),codec::decode(expected,&ts),codec::decode(got,&ts));}
                assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;active+=64;
            }}
            eprintln!("FOLD20_COUNTER_R02_CLASS_PASS j={j} phase={phase} cases={}",cases.len());
        }
    }
    eprintln!("FOLD20_COUNTER_R02_NATIVE_PASS metadata=20 lanes={total} active={active} scratch_allocated=0 whole_Q792=false");
}
