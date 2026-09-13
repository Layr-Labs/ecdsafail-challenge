//! New complete T10 physical test, scalar ADD/pop oracle and packed low3 chart.
//! Every saved geometry, all phase guards, both arbitrary phase passengers.
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
    let mut total=0usize;let mut active=0usize;let mut c1_count=0usize;let mut terminal=0usize;let mut c256=0usize;let mut m255=0usize;let mut m256=0usize;let mut short=0usize;let mut extreme=0usize;let mut weighted_t=0usize;let mut weighted_ops=0usize;
    for block in 0..1{for j in 0..4{
        if std::env::var("Q796_ONLY_BLOCK").ok().is_some_and(|v|v.parse::<usize>().unwrap()!=block){continue;}
        if std::env::var("Q796_ONLY_CLOCK").ok().is_some_and(|v|v.parse::<usize>().unwrap()!=j){continue;}
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let _it=circ.alloc_qreg("it");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("borrowed",23);assert_eq!(circ.b.next_qubit,565);
        let n=259;circ.q797_a_support=Some((0,256));
        super::q792_t10_nop2_r01::emit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&w1,&w2,&helpers,n,j);assert_eq!(circ.b.next_qubit,565);let b=circ.into_builder();
        for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for i in [256,257,258]{let q=w1[i].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"T10 touches omitted W1[{i}]");}}
        let t=b.ops.iter().filter(|o|o.kind==K::CCX).count();let weight=if block==25{4}else{16};weighted_t+=weight*t;weighted_ops+=weight*b.ops.len();
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|r|{let time=u16::from_le_bytes(r[..2].try_into().unwrap())as usize;(time-1)%4==j}).collect();if rows.is_empty(){continue;}
        let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);
        for pattern in 0..6{for batch in 0..rows.len().div_ceil(64){
            let mut seed=0x793c105ba328761fu64^(block as u64).rotate_left(43)^((j as u64)<<32)^batch as u64^((pattern as u64)<<24);
            let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{
                let r=&rows[(batch*64+lane)%rows.len()][2..70];
                for i in 0..542{let old=if i<23{i}else{i+1};let mask=1u64<<lane;before[i]=(before[i]&!mask)|if bit(r,old){mask}else{0};}
                for i in 0..565{let mask=1u64<<lane;after[i]=(after[i]&!mask)|(before[i]&mask);}
                let rk=bits(r,0,5);let av=64*ts[rk][0]+bits(r,5,6);let cv=64*ts[rk][1]+bits(r,11,6);let ph1=bit(r,21)as usize;let ph2=bit(r,22)as usize;let phase=2*ph1+ph2;let on=phase==2;
                let mut sv=64*ts[rk][2]+4*bits(r,17,4)+(j&1)+2*((j>>1)^(ph1&(j&1))^((ph1^ph2)&(cv&1)));
                let tag=phase==3&&bit(r,23)&&av==0&&cv==1&&sv==0;if tag{sv=256;}
                if on{
                    let semantic_c=if cv==0{assert_eq!(av,0);assert_eq!(sv,0);c256+=1;256}else{cv};
                    assert!(av<=254);let width=av+2;assert!(width<=n);let popped=av+semantic_c+1;assert!(popped<=257);let q=get(&before,&w1[popped],lane);put(&mut after,&w1[popped],lane,false);
                    let mut carry=false;if q{for i in 0..width{let x=get(&before,&w1[i],lane);let y=get(&before,&w2[i],lane);put(&mut after,&w2[i],lane,x^y^carry);carry=(x&&y)||((x^y)&&carry);}}
                    assert!(!carry,"scalar overflow block{block} j{j} A{av} C{cv}");active+=1;if cv==1{c1_count+=1;}if av+semantic_c==255{m255+=1;}if av+semantic_c==256{m256+=1;}if av<2{short+=1;}if av>=253{extreme+=1;}
                }
                if av==255{terminal+=1;}
                let first=if pattern<4{pattern&1!=0}else{rnd(&mut seed)&1!=0};let second=if pattern<4{pattern&2!=0}else{rnd(&mut seed)&1!=0};
                for(w,output)in[(&mut before,false),(&mut after,true)]{
                    if !get(w,&w1[0],lane){let packed=(get(w,&w1[258],lane)as usize)+2*(get(w,&w1[257],lane)as usize)+4*(get(w,&w1[256],lane)as usize);for k in 0..3{put(w,&w2[(259+k-sv%259)%259],lane,packed>>k&1!=0);}}
                    let(first_site,first_base)=if phase<2{(&w1[av],true)}else if phase==2&&cv==1&&av==254{(&w2[257],true)}else if phase==2&&cv==1{(&w1[av+3],false)}else if phase==2{(&w1[av+2],true)}else{(&w2[259-cv-sv],true)};
                    let(second_site,second_base)=match phase{0=>(&w2[av+2],false),1=>(&w2[av+1],false),2 if cv==1=>(&w1[av+2],!output),2=>(&w2[av+3],false),_=>(&w1[av+if tag{3}else{2}],false)};
                    // The full packed-Q793 boundary chart replaces only these
                    // metadata-defined absent cargo sites, with logical0.
                    let(first_site,first_base)=if phase==2&&(cv==1&&av==253||cv==2&&av==254){(&w2[255],false)}else{(first_site,first_base)};
                    let(second_site,second_base)=if phase==2&&cv==1&&av==254||phase==3&&av==254{(&w2[255],false)}else{(second_site,second_base)};
                    assert_ne!(first_site.id(),second_site.id());assert_eq!(get(w,first_site,lane),first_base,"first host A{av} C{cv} S{sv} phase{phase} output{output}");assert_eq!(get(w,second_site,lane),second_base,"second host A{av} C{cv} S{sv} phase{phase} output{output}");
                    put(w,first_site,lane,first);put(w,second_site,lane,second);for h in[256,257,258]{put(w,&w1[h],lane,false);}
                }
            }
            sim.qubits.copy_from_slice(&before);sim.phase=0x937c1546a123b9ff;sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("Q793 full T10 V13 block{block} j{j} pattern{pattern} batch{batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0x937c1546a123b9ff);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0x937c1546a123b9ff);total+=64;
        }}
        eprintln!("Q792_T10_NOP2_BLOCK block={block} j={j} ops={} T={t} PASS",b.ops.len());
    }}
    eprintln!("Q792_T10_NOP2_PASS lanes={total} active={active} C1={c1_count} M255={m255} M256={m256} shortA={short} A253+={extreme} terminal={terminal} C256={c256} weighted_forward_ops={weighted_ops} weighted_forward_T={weighted_t}; all saved geometries/all4passengerpairs+2random/packed3holes/dirty/phase/literalinverse; NOT fullstep or wholeQ793");
}
