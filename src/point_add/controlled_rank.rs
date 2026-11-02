//! Schaltwaerkli: exact synthesis of controlled linear involutions.
//! Matrices act on column vectors; their rows are bit-packed GF(2) forms.
use crate::circuit::{Op, OperationType as K, QubitId as Q, NO_BIT};
use std::collections::BTreeMap;
use std::io::Write;
const SPAN:usize=4096;
const WIRES:usize=64;
type Mat=Vec<u64>;
fn id(n:usize)->Mat {(0..n).map(|i|1u64<<i).collect()}
fn mul(a:&Mat,b:&Mat)->Mat {a.iter().map(|&row|{
    let mut s=0;let mut m=row;while m!=0{let k=m.trailing_zeros()as usize;m&=m-1;s^=b[k];}s
}).collect()}
fn inv(a:&Mat)->Mat {
    let n=a.len();let(mut x,mut y)=(a.clone(),id(n));
    for j in 0..n{let p=(j..n).find(|&i|x[i]&(1<<j)!=0).expect("singular free map");x.swap(j,p);y.swap(j,p);
        for i in 0..n{if i!=j && x[i]&(1<<j)!=0{x[i]^=x[j];y[i]^=y[j];}}
    }assert_eq!(x,id(n));y
}
fn rank(a:&Mat)->usize {
    let mut x=a.clone();let mut r=0;
    for j in 0..a.len(){if let Some(p)=(r..a.len()).find(|&i|x[i]&(1<<j)!=0){x.swap(r,p);
        for i in r+1..a.len(){if x[i]&(1<<j)!=0{x[i]^=x[r];}}r+=1;}}
    r
}
fn column(a:&Mat,j:usize)->u64 {a.iter().enumerate().fold(0,|v,(i,r)|v|(((r>>j)&1)<<i))}
// Return independent original image columns U and coordinate row forms V.
fn factor(nmat:&Mat)->(Vec<u64>,Vec<u64>){
    let n=nmat.len();let mut e=vec![0u64;n];let mut tags=vec![0u64;n];let mut u=vec![];
    for j in 0..n {let original=column(nmat,j);let(mut x,mut tag)=(original,0);
        for p in 0..n{if x&(1<<p)==0{continue;}if e[p]!=0{x^=e[p];tag^=tags[p];}
            else{let k=u.len();u.push(original);e[p]=x;tags[p]=tag^(1<<k);break;}}
    }
    let mut v=vec![0u64;u.len()];
    for j in 0..n {let(mut x,mut tag)=(column(nmat,j),0);
        for p in 0..n{if x&(1<<p)!=0{assert_ne!(e[p],0);x^=e[p];tag^=tags[p];}}
        assert_eq!(x,0);for k in 0..u.len(){if tag&(1<<k)!=0{v[k]|=1<<j;}}
    }
    let rebuilt:Mat=(0..n).map(|i|(0..u.len()).fold(0,|s,k|s^if u[k]&(1<<i)!=0{v[k]}else{0})).collect();
    assert_eq!(&rebuilt,nmat);assert_eq!(u.len(),rank(nmat));(u,v)
}
fn gate(k:K,a:u64,b:u64,t:u64)->Op {
    let mut o=Op::empty();o.kind=k;o.q_target=Q(t);o.q_control1=Q(a);
    if k==K::CCX{o.q_control2=Q(b);}o.validate();o
}
#[derive(Clone,Debug)]
struct Block{end:usize,c:u64,wires:Vec<u64>,ccx:usize}
fn extend(ops:&[Op],start:usize,c:u64)->Block {
    let mut wires:Vec<u64>=vec![];let mut end=start;let mut ccx=0;
    while end<ops.len() && end-start<SPAN {
        let o=ops[end];if o.c_condition!=NO_BIT{break;}
        let pair=match o.kind{
            K::CCX if o.q_control1.0==c=>[o.q_control2.0,o.q_target.0],
            K::CCX if o.q_control2.0==c=>[o.q_control1.0,o.q_target.0],
            K::CX|K::Swap if o.q_control1.0!=c && o.q_target.0!=c=>[o.q_control1.0,o.q_target.0],
            _=>break,
        };
        let extra=pair.iter().filter(|q|!wires.contains(*q)).count();if wires.len()+extra>WIRES{break;}
        for q in pair{if !wires.contains(&q){wires.push(q);}}
        if o.kind==K::CCX{ccx+=1;}end+=1;
    }
    wires.sort();Block{end,c,wires,ccx}
}
fn matrices(ops:&[Op],b:&Block)->(Mat,Mat){
    let n=b.wires.len();let(mut f0,mut f1)=(id(n),id(n));
    for o in ops{
        let t=b.wires.binary_search(&o.q_target.0).unwrap();
        let a=if o.kind==K::CCX && o.q_control1.0==b.c{o.q_control2.0}else{o.q_control1.0};
        let a=b.wires.binary_search(&a).unwrap();
        match o.kind{
            K::CCX=>f1[t]^=f1[a],
            K::CX=>{f0[t]^=f0[a];f1[t]^=f1[a];},
            K::Swap=>{f0.swap(t,a);f1.swap(t,a);},
            _=>unreachable!(),
        }
    }(f0,f1)
}
fn transvection(c:u64,wires:&[u64],u:u64,v:u64)->Vec<Op>{
    assert_ne!(u,0);assert_ne!(v,0);assert_eq!((u&v).count_ones()%2,0);
    let p=u.trailing_zeros()as usize;let mut basis=vec![];
    for j in 0..wires.len(){if j!=p && u&(1<<j)!=0{basis.push(gate(K::CX,wires[p],0,wires[j]));}}
    // E maps u to e_p. v*E has zero coefficient at p by v(u)=0.
    let vp=v&!(1<<p);assert_ne!(vp,0);let q=vp.trailing_zeros()as usize;
    for j in 0..wires.len(){if j!=q && vp&(1<<j)!=0{basis.push(gate(K::CX,wires[j],0,wires[q]));}}
    let mut out=basis.clone();out.push(gate(K::CCX,c,wires[q],wires[p]));out.extend(basis.into_iter().rev());out
}
fn synth(ops:&[Op],b:&Block,nmat:&Mat)->Vec<Op>{
    let(u,v)=factor(nmat);for a in &u{for z in &v{assert_eq!((a&z).count_ones()%2,0);}}
    let mut out:Vec<Op>=ops.iter().filter(|o|o.kind!=K::CCX).copied().collect();
    for(&a,&z)in u.iter().zip(&v){out.extend(transvection(b.c,&b.wires,a,z));}
    assert_eq!(matrices(&out,b),matrices(ops,b));out
}

pub(crate) fn run(ops:Vec<Op>)->Vec<Op>{
    let mut out=Vec::with_capacity(ops.len());let mut i=0;let mut depth=0usize;
    let mut stats:BTreeMap<&str,usize>=BTreeMap::new();let mut saved=0;
    let mut cert=std::env::var("RANK_CERT").ok().map(|p|std::io::BufWriter::new(std::fs::File::create(p).unwrap()));
    if let Some(f)=cert.as_mut(){writeln!(f,"start\tend\tcontrol\twires\tccx\trank\tinvolution\taccepted\tout_start\tout_end").unwrap();}
    while i<ops.len(){
        let o=ops[i];if depth==0 && o.kind==K::CCX && o.c_condition==NO_BIT{
            let a=extend(&ops,i,o.q_control1.0);let b=extend(&ops,i,o.q_control2.0);
            let score=|x:&Block|(x.ccx,x.end,u64::MAX-x.c);let b=if score(&a)>=score(&b){a}else{b};
            assert!(b.end>i);*stats.entry("blocks").or_default()+=1;*stats.entry("block_ccx").or_default()+=b.ccx;
            if b.ccx==1{*stats.entry("singleton").or_default()+=1;out.extend_from_slice(&ops[i..b.end]);i=b.end;continue;}
            let(f0,f1)=matrices(&ops[i..b.end],&b);let a=mul(&f1,&inv(&f0));let nmat:Mat=a.iter().enumerate().map(|(j,&r)|r^(1<<j)).collect();
            let r=rank(&nmat);assert!(r<=b.ccx);let invol=mul(&nmat,&nmat).iter().all(|&x|x==0);
            *stats.entry("multi_blocks").or_default()+=1;*stats.entry("optimistic_saving_ceiling").or_default()+=b.ccx-r;
            *stats.entry(if invol{"involution_blocks"}else{"noninvolution_blocks"}).or_default()+=1;
            let accepted=invol && r<b.ccx;let os=out.len();
            if accepted{out.extend(synth(&ops[i..b.end],&b,&nmat));saved+=b.ccx-r;
                *stats.entry("accepted").or_default()+=1;*stats.entry("old_ccx").or_default()+=b.ccx;*stats.entry("new_ccx").or_default()+=r;
            }else{out.extend_from_slice(&ops[i..b.end]);}
            if let Some(f)=cert.as_mut(){let w=b.wires.iter().map(|q|q.to_string()).collect::<Vec<_>>().join(",");
                writeln!(f,"{i}\t{}\t{}\t{w}\t{}\t{r}\t{}\t{}\t{os}\t{}",b.end,b.c,b.ccx,invol as u8,accepted as u8,out.len()).unwrap();}
            i=b.end;continue;
        }
        match o.kind{K::PushCondition=>depth+=1,K::PopCondition=>depth=depth.checked_sub(1).unwrap(),_=>{}}
        out.push(o);i+=1;
    }
    assert_eq!(depth,0);let before=ops.iter().filter(|o|o.kind==K::CCX).count();let after=out.iter().filter(|o|o.kind==K::CCX).count();assert_eq!(before-after,saved);
    let barrier=|o:&&Op|!matches!(o.kind,K::CX|K::Swap|K::CCX);assert!(ops.iter().filter(barrier).eq(out.iter().filter(barrier)));
    for(k,v)in stats{eprintln!("RANK_CENSUS {k}={v}");}
    eprintln!("RANK_RESULT saved={saved} original_ops={} final_ops={}",ops.len(),out.len());out
}

#[cfg(test)]
mod tests{
    use super::*;use crate::{sim::Simulator,circuit::BitId};
    struct Forced{word:u64,reads:usize}
    impl sha3::digest::XofReader for Forced{fn read(&mut self,x:&mut[u8]){assert_eq!(x.len(),8);x.copy_from_slice(&self.word.to_le_bytes());self.reads+=1;}}
    fn native(ops:&[Op],n:usize,start:usize,word:u64)->(Vec<u64>,Vec<u64>,u64,usize,u64){
        let mut rng=Forced{word,reads:0};let mut s=Simulator::new(n,2,&mut rng);
        for q in 0..n{s.qubits[q]=(0..64).fold(0,|x,j|x|(((((start+j)>>q)&1)as u64)<<j));}
        s.bits[0]=word;s.bits[1]=!word;s.phase=0xaaaaaaaaaaaaaaaa;s.apply_iter(ops.iter());
        let x=(s.qubits.clone(),s.bits.clone(),s.phase,s.stats.toffoli_gates);drop(s);(x.0,x.1,x.2,rng.reads,x.3)
    }
    fn compare(a:&[Op],b:&[Op],n:usize,save:usize)->usize{
        let mut count=0;for word in [0,u64::MAX,0xa55a0ff033cc9696]{for start in(0..1usize<<n).step_by(64){
            let x=native(a,n,start,word);let y=native(b,n,start,word);
            assert_eq!((&x.0,&x.1,x.2,x.3),(&y.0,&y.1,y.2,y.3));assert_eq!(x.4-y.4,64*save as u64);count+=64;
        }}count
    }
    fn cc(a:u64,t:u64)->Op{gate(K::CCX,0,a,t)}
    #[test]
    fn controlled_rank_exhaustive_small_networks(){
        let gs:Vec<Op>=(1..4).flat_map(|a|(1..4).filter(move|&t|t!=a).map(move|t|cc(a,t))).collect();
        let mut comparisons=0;let mut accepted=0;let mut noninvolution=0;
        for code in 0..6usize.pow(5){let mut x=code;let mut s=vec![];for _ in 0..5{s.push(gs[x%6]);x/=6;}
            let b=Block{end:s.len(),c:0,wires:vec![1,2,3],ccx:5};let(f0,f1)=matrices(&s,&b);let a=mul(&f1,&inv(&f0));
            let nmat:Mat=a.iter().enumerate().map(|(j,&v)|v^(1<<j)).collect();
            if mul(&nmat,&nmat).iter().all(|&x|x==0){let out=synth(&s,&b,&nmat);comparisons+=compare(&s,&out,4,5-rank(&nmat));accepted+=1;}else{noninvolution+=1;}
        }assert!(accepted>0 && noninvolution>0);eprintln!("RANK_TEST exhaustive_cases={comparisons} involutions={accepted} noninvolutions={noninvolution}");
    }
    #[test]
    fn controlled_rank_noncommuting_conjugate_and_interface(){
        let core=vec![cc(1,2),cc(2,3),cc(1,2),cc(2,3)];
        // The commutator of these transvections is one distant transvection.
        let out=run(core.clone());assert_eq!(out.iter().filter(|o|o.kind==K::CCX).count(),1);
        let mut a=core;let mut b=out;
        let mut phase=Op::empty();phase.kind=K::CZ;phase.q_control1=Q(3);phase.q_target=Q(4);
        let mut h=Op::empty();h.kind=K::Hmr;h.q_target=Q(4);h.c_target=BitId(1);
        let mut x=Op::empty();x.kind=K::X;x.q_target=Q(5);x.c_condition=BitId(1);
        for o in [phase,h,x]{o.validate();a.push(o);b.push(o);}let cases=compare(&a,&b,6,3);
        let b0=Block{end:4,c:0,wires:vec![1,2,3,4,5,6,7],ccx:4};
        let e=vec![gate(K::CX,1,0,4),gate(K::CX,3,0,6),gate(K::Swap,2,0,7)];
        let mut a=e.clone();a.extend([cc(1,2),cc(2,3),cc(1,2),cc(2,3)]);a.extend(e.into_iter().rev());
        let(f0,f1)=matrices(&a,&b0);let z=mul(&f1,&inv(&f0));let nm:Mat=z.iter().enumerate().map(|(j,&x)|x^(1<<j)).collect();
        let b=synth(&a,&b0,&nm);let cases=cases+compare(&a,&b,8,3);eprintln!("RANK_TEST interface_cases={cases}");
    }
    #[test]
    fn controlled_rank_barriers_and_noninvolutions(){
        let s=vec![cc(1,2),cc(2,3)];assert_eq!(run(s.clone()),s);
        let mut h=Op::empty();h.kind=K::Hmr;h.q_target=Q(4);h.c_target=BitId(1);
        let mut push=Op::empty();push.kind=K::PushCondition;push.c_condition=BitId(0);
        let mut pop=Op::empty();pop.kind=K::PopCondition;
        let mut conditional=cc(1,2);conditional.c_condition=BitId(1);
        let mut x=Op::empty();x.kind=K::X;x.q_target=Q(0);
        for barrier in [h,x,gate(K::CX,1,0,0),conditional]{let s=vec![cc(1,2),barrier,cc(1,2)];assert_eq!(run(s.clone()),s);}
        let s=vec![push,cc(1,2),cc(1,2),pop];assert_eq!(run(s.clone()),s);
        // A write to one possible control is legal when the other is immutable.
        let s=vec![cc(1,2),gate(K::CX,4,0,0),cc(1,2)];let out=run(s.clone());
        assert_eq!(out.iter().filter(|o|o.kind==K::CCX).count(),1);
        let cases=compare(&s,&out,5,1);
        eprintln!("RANK_TEST barrier_fixtures=6 alternate_control_cases={cases}");
    }
    #[test]
    fn controlled_rank_basis_mutation_detected(){
        let good=transvection(0,&[1,2,3],0b111,0b011);assert!(good.len()>1);
        let mut bad=good.clone();bad.remove(0);
        let mut phase=Op::empty();phase.kind=K::CZ;phase.q_control1=Q(1);phase.q_target=Q(4);
        let mut a=good;a.push(phase);bad.push(phase);
        let x=native(&a,5,0,0);let y=native(&bad,5,0,0);let mut diff=0;for(a,b)in x.0.iter().zip(&y.0){diff|=a^b;}
        assert_ne!(diff,0);assert_ne!(x.2^y.2,0);eprintln!("RANK_TEST mutation_value={} mutation_phase={}",diff.count_ones(),(x.2^y.2).count_ones());
    }
}
