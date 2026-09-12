//! Three twenty-wire charts with a four-bit local high-rank code.
//! They expose literal A6/C6/SM4, so body-local arithmetic may leave the
//! global simplex while preserving its high-rank class.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="q792_class_chart_plan_r02.rs"]mod plan;
fn project(r:usize,class:usize)->usize{let k=[24usize,16,29][class];let p=k.trailing_zeros()as usize;let f=r^if r>>p&1!=0{k}else{0};(f&((1<<p)-1))|((f>>(p+1))<<p)}
fn trans(c:&mut Circuit,m:&[QReg],d:&[QReg],x:usize,y:usize,free:usize){
    if x==y{return;}let delta=x^y;let fixed=((1<<m.len())-1)^free;let p=(delta&fixed).trailing_zeros()as usize;assert!(p<m.len());let base=if x>>p&1==0{x}else{y};
    for i in 0..m.len(){if i!=p&&delta>>i&1!=0{c.cx(&m[p],&m[i]);}}
    let cs:Vec<_>=(0..m.len()).filter(|&i|i!=p&&fixed>>i&1!=0).map(|i|(&m[i],base>>i&1!=0)).collect();mixed_mcx(c,&cs,&m[p],d);
    for i in (0..m.len()).rev(){if i!=p&&delta>>i&1!=0{c.cx(&m[p],&m[i]);}}
}
fn small(c:&mut Circuit,m:&[QReg],d:&[QReg],pairs:&[(usize,usize)]){
    let mut perm:Vec<_>=(0..16).collect();let mut assigned=[false;16];let mut used=[false;16];for &(x,y)in pairs{assert!(!assigned[x]&&!used[y]);assigned[x]=true;used[y]=true;perm[x]=y;}
    for x in 0..16{if assigned[x]&&!used[x]{let mut y=x;while assigned[y]{y=perm[y];}perm[y]=x;assigned[y]=true;used[x]=true;}}
    let mut seen=[false;16];for root in 0..16{if seen[root]{continue;}seen[root]=true;let mut y=perm[root];while y!=root{assert!(!seen[y]);seen[y]=true;trans(c,&m[..4],d,root,y,0);y=perm[y];}}
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],d:&[QReg],class:usize,inverse:bool){
    assert_eq!(m.len(),20);assert!(d.len()>=16);let at=c.b.ops.len();let ts=super::q792_fold20_rank_r01::triples();
    if class==1{assert!(plan::TAILS.is_empty());for &(x,y,free)in plan::SWAPS{trans(c,m,d,x,y,free);}}
    else{
        if class==2{for i in 0..4{c.cx(&m[i],&m[6+i]);c.cx(&m[6+i],&m[i]);c.cx(&m[i],&m[6+i]);c.x(&m[6+i]);}}
        let rows:Vec<_>=(0..32).filter(|&r|if class==0{ts[r].iter().sum::<usize>()<=2}else{ts[r].iter().sum::<usize>()==4}).collect();
        small(c,m,d,&rows.iter().enumerate().map(|(i,&r)|(i,project(r,class))).collect::<Vec<_>>());
    }
    if inverse{c.b.ops[at..].reverse();}
}
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x32)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let ts=super::q792_fold20_rank_r01::triples();let low:Vec<_>=(0..32).filter(|&r|ts[r].iter().sum::<usize>()<=2).collect();let edge:Vec<_>=(0..32).filter(|&r|ts[r].iter().sum::<usize>()==3).collect();let peak:Vec<_>=(0..32).filter(|&r|ts[r].iter().sum::<usize>()==4).collect();let mut total=0;let mut active=0;
    for class in 0..3{
        let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let d=c.alloc_qreg_bits("d",20);let n=c.b.next_qubit;emit(&mut c,&m,&d,class,false);assert_eq!(c.b.next_qubit,n);let ops=c.into_builder().ops;
        eprintln!("FOLD20_CLASS_BUILT class={class} ops={} T={}",ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
        for first in (0..1usize<<20).step_by(64){let mut seed=0x792c1a55u64^first as u64^((class as u64)<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();for bit in 0..20{before[bit]=(0..64).fold(0,|v,l|v|(((first+l)>>bit&1)as u64)<<l);}let mut after=before.clone();let mut care=0u64;
            for lane in 0..64{let code=first+lane;let tag=code&15;let mut raw=code>>4;let r=match class{0=>{if tag>=10{continue;}low[tag]},1=>{if !(10..15).contains(&tag){continue;}let side=usize::from(((raw&63)>>4)+((raw>>6&63)>>4)+((raw>>12&15)>>2)>=5);if side!=0{raw^=65535;}edge[2*(tag-10)+side]},_=>{if tag!=15||raw&2!=0||(raw&63)>>2>=12{continue;}let r=peak[(raw&63)>>2];raw&=!62;r}};
                let next=project(r,class)|(raw<<4);care|=1u64<<lane;active+=1;for bit in 0..20{let mask=1u64<<lane;after[bit]=(after[bit]&!mask)|(((next>>bit&1)as u64)<<lane);}
            }
            let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());for bit in 0..20{assert_eq!((sim.qubits[bit]^after[bit])&care,0,"class={class} first={first} bit={bit}");}assert_eq!(&sim.qubits[20..],&before[20..]);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }
    }eprintln!("FOLD20_CLASS_NATIVE_PASS lanes={total} active={active} rank4_literal_low16=true inverse_all_physical_codes=true phase=0");
}
