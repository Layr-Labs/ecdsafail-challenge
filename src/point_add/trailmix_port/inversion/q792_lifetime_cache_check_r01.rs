use super::*;
use crate::{circuit::{Op,OperationType as K},sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x35)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(words:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;words[q.id()as usize]=(words[q.id()as usize]&!b)|(u64::from(v)<<l);}
struct Case{word:usize,a:usize,active:bool}
fn verify(ops:&[Op],marks:&[(usize,usize)],word:&[&QReg],g:&QReg,mask:&QReg,zero:&[&QReg],out:&QReg,n:usize,cases:&[Case])->usize{
    let mut lanes=0;
    for batch in cases.chunks(64){
        let mut seed=0x79211feu64^lanes as u64;let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();let mut active=0;
        for l in 0..64{let x=&batch[l%batch.len()];for(i,&q)in word.iter().enumerate(){put(&mut before,q,l,x.word>>i&1!=0);}put(&mut before,g,l,x.active);if x.active{active|=1u64<<l;for &q in zero{put(&mut before,q,l,false);}}}
        let mut expected_mask=before[mask.id()as usize];let mut f=Fixed;let mut sim=Simulator::new(n,0,&mut f);sim.qubits.copy_from_slice(&before);let mut at=0;
        for &(end,value)in marks{
            sim.apply_iter(ops[at..end].iter());at=end;
            for l in 0..64{let x=&batch[l%batch.len()];if x.active&&x.a==value{expected_mask^=1u64<<l;}}
            assert_eq!((sim.qubits[mask.id()as usize]^expected_mask)&active,0,"cached equality value={value}");assert_eq!(sim.qubits[g.id()as usize],before[g.id()as usize]);assert_eq!(sim.phase,0);
        }
        sim.apply_iter(ops[at..].iter());let mut center=ops[0];center.kind=K::CCX;center.q_control1.0=g.id()as u64;center.q_control2.0=mask.id()as u64;center.q_target.0=out.id()as u64;
        let expected_out=before[out.id()as usize]^(sim.qubits[g.id()as usize]&sim.qubits[mask.id()as usize]);
        sim.apply_iter(std::iter::once(&center));sim.apply_iter(ops.iter().rev());
        let mut expected=before.clone();expected[out.id()as usize]=expected_out;
        assert_eq!(sim.qubits,expected,"full cache U/guarded center/U inverse arbitrary off-guard values");assert_eq!(sim.phase,0);
        lanes+=64;
    }lanes
}
pub(super) fn run(){
    let mut general_lanes=0;let mut c1_lanes=0;let mut general_plans=0;let mut c1_plans=0;
    let ts=super::super::q792_fold20_rank_r01::triples();let mut next=[0usize,16,24,28];let mut map=Vec::new();
    for t in &ts{if t.iter().sum::<usize>()==4&&(t[1]==0||t[2]==0){continue;}let code=next[t[0]];next[t[0]]+=1;map.push((*t,code));}
    for &(lo,hi,end,fixed,value,wire,_)in GENERAL{
        let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;c.q797_a_support=Some((lo,hi));
        let rank=c.alloc_qreg_bits("rank",5);let a=c.alloc_qreg_bits("a",6);let g=c.alloc_qreg("g");let mask=c.alloc_qreg("mask");let out=c.alloc_qreg("external");let n=c.b.next_qubit as usize;
        let mut cache=General::begin(&mut c,&rank,&a,&g,&mask,end).unwrap();let mut marks=Vec::new();
        for i in 1..end{cache.equality(&mut c,i-1);marks.push((c.b.ops.len(),i-1));}cache.finish(&mut c);assert_eq!(c.b.next_qubit as usize,n);
        let ops=c.into_builder().ops;assert!(ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)));
        let mut cases=Vec::new();for av in lo..hi.min(252){for &(t,code)in &map{
            if t[0]==av/64&&av+(2usize.max(t[1]*64))+(3usize.max(t[2]*64))<=256{
                let w=code|((av&63)<<5);assert_eq!(w&fixed,value);assert_eq!(w>>wire&1,value>>wire&1);cases.push(Case{word:w,a:av,active:true});
            }
        }}for w in 0..2048{cases.push(Case{word:w,a:0,active:false});}
        let word:Vec<_>=rank.iter().chain(&a).collect();general_lanes+=verify(&ops,&marks,&word,&g,&mask,&[],&out,n,&cases);general_plans+=1;
    }
    for &(lo,hi,end,_,_)in C1{
        let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;c.q797_a_support=Some((lo,hi));
        let rank=c.alloc_qreg_bits("numeric.high",2);let a=c.alloc_qreg_bits("a",6);let g=c.alloc_qreg("g");let mask=c.alloc_qreg("mask");let high=c.alloc_qreg("high");let one=c.alloc_qreg("C4");let two=c.alloc_qreg("C5");let out=c.alloc_qreg("external");let n=c.b.next_qubit as usize;
        let mut cache=super::C1Cache::new(&c,&a,&high,&one,&two,&g,&mask,end).unwrap();let mut marks=Vec::new();let mut group=None;
        for i in 1..end{let v=i-1;if (lo..hi).contains(&v){let h=v/64;let use_high=lo/64!=(hi-1)/64;
            if use_high&&group!=Some(h){cache.clear(&mut c);for old in group.into_iter().chain(std::iter::once(h)){let cs:Vec<_>=rank.iter().enumerate().map(|(b,q)|(q,old>>b&1!=0)).collect();paired(&mut c,&cs,&high,&g);}group=Some(h);}
            cache.equality(&mut c,v,use_high);
        }marks.push((c.b.ops.len(),v));}
        assert_eq!(c.b.next_qubit as usize,n);let ops=c.into_builder().ops;let word:Vec<_>=rank.iter().chain(&a).collect();let mut cases=Vec::new();
        for av in lo..hi{cases.push(Case{word:(av>>6)|((av&63)<<2),a:av,active:true});}for w in 0..256{cases.push(Case{word:w,a:0,active:false});}
        c1_lanes+=verify(&ops,&marks,&word,&g,&mask,&[&high,&one,&two],&out,n,&cases);c1_plans+=1;
    }
    eprintln!("LIFETIME_CACHE_PASS general_plans={general_plans} general_lanes={general_lanes} c1_plans={c1_plans} c1_lanes={c1_lanes} every_boundary=true arbitrary_off_guard=true phase=0 inverse=true no_extra_qubits=true");
}
