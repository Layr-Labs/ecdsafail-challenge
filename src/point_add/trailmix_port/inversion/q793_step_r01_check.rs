//! Complete new three-hole/mod8 transition versus independent scalar records.
use crate::point_add::trailmix_port::circuit::Circuit;
pub fn run(){
    std::env::set_var("Q796_PARITY","1");
    std::env::set_var("Q795_PHASE_LOAN","1");
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],i:usize,l:usize,v:bool){let b=1u64<<l;w[i]=(w[i]&!b)|if v{b}else{0};}
    fn bits(r:&[u8],first:usize,n:usize)->usize{(0..n).map(|i|(((r[(first+i)/8]>>((first+i)%8))&1)as usize)<<i).sum()}
    let data=std::fs::read(std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").unwrap()).unwrap();assert_eq!(&data[..8],b"R5FSTEP1");
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut lanes=0;let mut weighted_ops=0usize;let mut weighted_t=0usize;
    for block in 0..26{for j in 0..4{
        if std::env::var("Q796_ONLY_BLOCK").ok().is_some_and(|x|x.parse::<usize>().unwrap()!=block){continue;}
        if std::env::var("Q796_ONLY_CLOCK").ok().is_some_and(|x|x.parse::<usize>().unwrap()!=j){continue;}
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("borrowed_phase");let it=circ.alloc_qreg("it");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("other_borrowed",23);
        super::q793_step_r01::step(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&it,&w1,&w2,&helpers,j,block);assert_eq!(circ.b.next_qubit,565);let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        for h in [256usize,257,258]{let hole=w1[h].id() as u64;let touches=b.ops.iter().filter(|o|o.q_target.0==hole||o.q_control1.0==hole||o.q_control2.0==hole).count();
        eprintln!("Q796_HOLE block={block} j={j} touches={touches}");
        assert_eq!(touches,0,"Q793 must never address omitted low3 rails");}
        let t=b.ops.iter().filter(|op|op.kind==K::CCX).count();weighted_ops+=b.ops.len()*if block==25{4}else{16};weighted_t+=t*if block==25{4}else{16};
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|r|{let t=u16::from_le_bytes(r[..2].try_into().unwrap())as usize;(t-1)/64==block&&t%4==j}).collect();
        for pattern in 0..6 {for batch in 0..rows.len().div_ceil(64){
            let mut seed=0x797575ef1234u64^batch as u64^((pattern as u64)<<32);let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{let row=rows[(batch*64+lane)%rows.len()];let cargo=if pattern<4{pattern&1!=0}else{rnd(&mut seed)&1!=0};
                let second=if pattern<4{pattern&2!=0}else{rnd(&mut seed)&1!=0};
                for (w,r,clock)in[(&mut before,&row[2..70],(j+3)%4),(&mut after,&row[70..138],j)]{
                    let rk=bits(r,0,5);let av=64*ts[rk][0]+bits(r,5,6);let cv=64*ts[rk][1]+bits(r,11,6);let phase=bits(r,21,2);let p1=phase&1;let p2=phase>>1;let sv=64*ts[rk][2]+4*bits(r,17,4)+(clock&1)+2*((clock/2)^(p1&(clock&1))^((p1^p2)&(cv&1)));
                    let tag=phase==3&&bits(r,23,1)==1&&av==0&&cv==1&&sv==0;
                    for i in 0..542{let old=if i<23{i}else{i+1};put(w,i,lane,(bits(r,old,1)!=0) ^ (tag&&i==11));}
                    let t0=bits(r,25,1);let shift=if tag{256}else{sv};
                    if t0==0 {
                        for bit in 0..3 {put(w,283+(259+bit-shift%259)%259,lane,bits(r,25+258-bit,1)!=0);}
                    }
                    // Inert missing rails carry unrelated arbitrary test values.
                    for h in [256,257,258]{put(w,24+h,lane,(batch+lane+pattern)>>(h-256)&1!=0);}
                    let (mut site,mut base)=match phase{
                        0|2=>(24+av,true),1 if cv==1&&av==254=>(283+257,true),1 if cv==1=>(24+av+3,false),1=>(24+av+2,true),3=>(283+259-cv-if tag{256}else{sv},true),_=>unreachable!()
                    };
                    if phase==1&&((cv==1&&av==253)||(cv==2&&av==254)){site=283+255;base=false;}
                    assert!(![280,281,282].contains(&site));
                    assert_eq!((w[site]>>lane)&1!=0,base,"first packed boundary phase={phase} A={av} C={cv} S={sv} j={clock}");
                    put(w,site,lane,cargo);
                    let (mut site2,mut base2)=match phase{0=>(283+av+2,false),2=>(283+av+1,false),1 if cv==1=>(24+av+2,true),1=>(283+av+3,false),3=>(24+av+if tag{3}else{2},false),_=>unreachable!()};
                    if (phase==1&&cv==1&&av==254)||(phase==3&&av==254){site2=283+255;base2=false;}
                    assert!(![280,281,282].contains(&site2));assert_ne!(site,site2);
                    assert_eq!((w[site2]>>lane)&1!=0,base2,"second packed boundary phase={phase} A={av} C={cv} S={sv} j={clock}");
                    put(w,site2,lane,second);
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=after{
                if std::env::var_os("Q795_TRACE").is_some(){
                    let mask=sim.qubits.iter().zip(&after).fold(0u64,|m,(x,y)|m|(x^y));let lane=mask.trailing_zeros();sim.qubits.copy_from_slice(&before);let mut from=0;
                    for(name,to)in super::q793_step_r01::marks(){sim.apply_iter(b.ops[from..to].iter());from=to;let val=|first:usize,n:usize|->usize{(0..n).map(|i|(((sim.qubits[first+i]>>lane)&1)as usize)<<i).sum()};let r=val(0,5);eprintln!("DUAL_TRACE stage={name} ops={to} lane={lane} A={} C={} sm={} phase={} iter={} w1low={} w2low={} sign={}",64*ts[r][0]+val(5,6),64*ts[r][1]+val(11,6),val(17,4),val(21,2),val(23,1),val(24,12),val(283,12),val(542,1));}
                }
                let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("step cargo block={block} j={j} batch={batch} pattern={pattern} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);lanes+=64;
        }}
        eprintln!("Q793_FULL_STEP_BLOCK block={block} j={j} ops={} T={t} physical=565 PASS",b.ops.len());
    }}
    eprintln!("Q793_FULL_STEP_PASS lanes={lanes} forward_ops={weighted_ops} forward_T={weighted_t}; own integrated three-hole/mod8 step; holes256/257/258 absent; NOT whole point-add Q793 or9024");
}


