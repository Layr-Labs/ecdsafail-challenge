//! New normal-domain dynamic T10 test against an independent scalar ADD/pop.
//! Rows explicitly restricted to A2..252,C>=1,A+C<=254 on both guard values.
//! No claim for missing short-tail endpoints or the whole Q793 lifecycle.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
    fn get(w:&[u64],q:&QReg,l:usize)->bool{w[q.id()as usize]>>l&1!=0}
    fn bit(r:&[u8],i:usize)->bool{r[i/8]>>(i%8)&1!=0}
    fn bits(r:&[u8],i:usize,n:usize)->usize{(0..n).map(|k|(bit(r,i+k)as usize)<<k).sum()}
    std::env::set_var("Q796_PARITY","1");std::env::set_var("Q795_PHASE_LOAN","1");
    let data=std::fs::read(std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").expect("explicit immutable step capsule")).unwrap();assert_eq!(&data[..8],b"R5FSTEP1");
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut total=0usize;let mut active=0usize;let mut c1_count=0usize;let mut endpoint=0usize;let mut extreme=0usize;let mut weighted_t=0usize;let mut weighted_ops=0usize;
    for block in 0..26{for j in 0..4{
        if std::env::var("Q796_ONLY_BLOCK").ok().is_some_and(|v|v.parse::<usize>().unwrap()!=block){continue;}
        if std::env::var("Q796_ONLY_CLOCK").ok().is_some_and(|v|v.parse::<usize>().unwrap()!=j){continue;}
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let _it=circ.alloc_qreg("it");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("borrowed",23);assert_eq!(circ.b.next_qubit,565);
        let n=super::shared_step::SCHEDULE_SUPPORTS[block].1;circ.q797_a_support=Some(super::metadata_entry_head5::A_SUPPORTS[block]);
        super::q793_t10_normal_v2::emit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&w1,&w2,&helpers,n,j);assert_eq!(circ.b.next_qubit,565);let b=circ.into_builder();
        for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for i in [256,257,258]{let q=w1[i].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"T10 touches omitted W1[{i}]");}}
        let t=b.ops.iter().filter(|o|o.kind==K::CCX).count();let weight=if block==25{4}else{16};weighted_t+=weight*t;weighted_ops+=weight*b.ops.len();
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|r|{let time=u16::from_le_bytes(r[..2].try_into().unwrap())as usize;let x=&r[2..70];let rk=bits(x,0,5);let av=64*ts[rk][0]+bits(x,5,6);let cv=64*ts[rk][1]+bits(x,11,6);(time-1)/64==block&&(time-1)%4==j&&(2..=252).contains(&av)&&cv>=1&&av+cv<=254}).collect();if rows.is_empty(){continue;}
        let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);
        for pattern in 0..6{for batch in 0..rows.len().div_ceil(64){
            let mut seed=0x794c105ba328761fu64^(block as u64).rotate_left(43)^((j as u64)<<32)^batch as u64^((pattern as u64)<<24);
            let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{
                let r=&rows[(batch*64+lane)%rows.len()][2..70];
                for i in 0..542{let old=if i<23{i}else{i+1};let mask=1u64<<lane;before[i]=(before[i]&!mask)|if bit(r,old){mask}else{0};}
                for i in 0..565{let mask=1u64<<lane;after[i]=(after[i]&!mask)|(before[i]&mask);}
                let rk=bits(r,0,5);let av=64*ts[rk][0]+bits(r,5,6);let cv=64*ts[rk][1]+bits(r,11,6);let on=bit(r,21)&&!bit(r,22);
                if !on{for w in [&mut before,&mut after]{for h in [256,257,258]{put(w,&w1[h],lane,false);}}continue;}
                let sv=64*ts[rk][2]+4*bits(r,17,4)+(j&1)+2*((j>>1)^(j&1)^(cv&1));
                let width=av+2;assert!(width<=n);let popped=if cv==0{257}else{av+cv+1};assert!(popped<=257);
                let q=get(&before,&w1[popped],lane);put(&mut after,&w1[popped],lane,false);
                let mut carry=false;if q{for i in 0..width{
                    let x=get(&before,&w1[i],lane);let y=get(&before,&w2[i],lane);put(&mut after,&w2[i],lane,x^y^carry);carry=(x&&y)||((x^y)&&carry);
                }}assert!(!carry,"scalar overflow block{block} j{j} A{av} C{cv}");
                let is_endpoint=popped==257;let is_extreme=av==254&&cv==1;
                let first=if pattern<4{pattern&1!=0}else{rnd(&mut seed)&1!=0};let second=if pattern<4{pattern&2!=0}else{rnd(&mut seed)&1!=0};
                for (w,output)in [(&mut before,false),(&mut after,true)]{
                    let even=!get(w,&w1[0],lane);let b0=(259-sv%259)%259;let b1=(260-sv%259)%259;
                    if even{
                        if is_endpoint{assert_eq!(sv,0);put(w,&w2[b0],lane,false);put(w,&w2[b1],lane,!output&&q);}
                        else{for k in 0..3{let rk=get(w,&w1[258-k],lane);put(w,&w2[(259-sv%259+k)%259],lane,rk);}}
                    }else if is_endpoint{assert_eq!(sv,0);assert_eq!(!get(w,&w2[0],lane),!output&&q,"odd endpoint q payload");}
                    // Boundary cargo chart supplied by root's independently
                    // tested cargo-only pilot; neither slot is treated clean.
                    let first_site=if is_extreme{&w2[257]}else{&w1[if cv==1{av+3}else{av+2}]};
                    let second_site=if cv==1{&w1[av+2]}else{&w2[av+3]};
                    assert_ne!(first_site.id(),second_site.id());
                    if !is_extreme{assert_eq!(get(w,first_site,lane),cv!=1,"first cargo logical base");}
                    // At C1 the scalar oracle popped this known-one last
                    // digit, but its arbitrary passenger is retained by the
                    // physical specialized route on both sides.
                    assert_eq!(get(w,second_site,lane),cv==1&&!output,"second cargo logical base");
                    put(w,first_site,lane,first);put(w,second_site,lane,second);
                    for h in [256,257,258]{put(w,&w1[h],lane,false);}
                }
                active+=1;if cv==1{c1_count+=1;}if is_endpoint{endpoint+=1;}if is_extreme{extreme+=1;}
            }
            sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("Q793 normal T10 block{block} j{j} pattern{pattern} batch{batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("Q793_T10_NORMAL_V2_BLOCK block={block} j={j} ops={} T={t} PASS",b.ops.len());
    }}
    eprintln!("Q793_T10_NORMAL_V2_PASS lanes={total} active={active} C1={c1_count} M256={endpoint} C1A254={extreme} weighted_forward_ops={weighted_ops} weighted_forward_T={weighted_t}; normal-domain-new-adapter/all4passengerpairs+2random/hole256+257+258/dirty/phase/literalinverse; excludes-active-endpoints; NOT fullstep or wholeQ793");
}
