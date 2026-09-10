//! Exact integer R00 oracle on actual physical cargo and global-loan frames.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
fn bit(r:&[u8],field:usize,i:usize)->bool{i<256&&r[field*32+i/8]>>(i%8)&1!=0}
fn bits(r:&[u8],field:usize)->usize{(0..256).rev().find(|&i|bit(r,field,i)).map(|i|i+1).unwrap_or(0)}
pub fn run(){
    let data=std::fs::read(std::env::var("Q793_R00_PHYSICAL_CAPSULE").expect("explicit physical R00 capsule")).unwrap();assert_eq!(&data[..8],b"Q793R002");
    let count=u32::from_le_bytes(data[8..12].try_into().unwrap())as usize;assert_eq!(data.len(),12+132*count);
    let all=std::env::var("LOWQ_Q793_NATIVE_MODE").ok().as_deref()==Some("r00-physical-r02-all");let blocks=if all{26}else{1};
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut total=0usize;let mut active=0usize;let mut terminal=0usize;let mut a253s1=0usize;
    for block in 0..blocks{for j in 0..4{
        let end=if all{259-super::shared_step::SCHEDULE_SUPPORTS[block].0}else{259};
        let support=if all{super::metadata_entry_head5::A_SUPPORTS[block]}else{(0,256)};
        let rows:Vec<_>=data[12..].chunks_exact(132).filter(|r|r[129]as usize%4==j&&(support.0..support.1).contains(&(r[128]as usize))&&bits(r,2)<=end&&bits(r,3)+r[129]as usize+1<=end).collect();assert!(!rows.is_empty(),"empty R00 physical template block={block} j={j}");
        let mut circ=Circuit::new();if all{circ.q797_a_support=Some(support);}
        let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("dirty",23);let owned=circ.b.next_qubit;
        let mut seed=|cc:&mut Circuit,mask:&QReg,carry:&QReg,helpers:&[QReg],clock:usize|{super::q793_r00_seed_dynamic_r02::emit(cc,&rank,&a,&w1,&w2,mask,carry,helpers,clock);};
        super::q793_r00::phase00_with_support(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&w1,&w2,&dirty,j,end,&mut seed);assert_eq!(circ.b.next_qubit,owned);let builder=circ.into_builder();
        for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for h in [256,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"physical R00 touched hole{h}");}}
        eprintln!("Q793_R00_PHYSICAL_R02_BUILT block={block} j={j} end={end} rows={} ops={} T={}",rows.len(),builder.ops.len(),builder.ops.iter().filter(|o|o.kind==K::CCX).count());
        // Eight independent first/second/global-loan passengers, both Sign
        // accumulators, and three off phases with arbitrary cache data.
        for pattern in 0..19{for batch in 0..rows.len().div_ceil(63){
            let mut rng=0x793002551u64^(block as u64)<<56^(j as u64)<<48^(pattern as u64)<<32^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut after=before.clone();
            for lane in 0..64{
                if lane==63{
                    // Already terminal has no pre-rotation. It borrows the
                    // global Sign host W2[258] and keeps second W2[257].
                    let history=(block*23+batch+pattern)%149;
                    for w in [&mut before,&mut after]{
                        for i in 0..5{put(w,&rank[i],lane,29>>i&1!=0);}for i in 0..6{put(w,&a[i],lane,true);put(w,&c[i],lane,history>>i&1!=0);}
                        for i in 0..4{put(w,&sm[i],lane,i<2&&history>>(6+i)&1!=0);}put(w,&p1,lane,false);put(w,&p2,lane,false);put(w,&sign,lane,pattern&8!=0);
                        for i in 0..256{let one=if i<64{0xffff_fffe_ffff_fc2fu64>>i&1!=0}else{true};put(w,&w1[i],lane,one);}
                        for q in &w2{put(w,q,lane,false);}put(w,&w1[255],lane,pattern&1!=0);put(w,&w2[257],lane,pattern&2!=0);put(w,&w2[258],lane,pattern&4!=0);
                    }terminal+=1;continue;
                }
                let r=rows[(batch*63+lane)%rows.len()];let av=r[128]as usize;let sv=r[129]as usize;let shift=sv+1;let phase=if pattern<16{0}else{pattern-15};let rk=ts.iter().position(|&t|t==[av/64,0,sv/64]).unwrap();
                for w in [&mut before,&mut after]{
                    for i in 0..5{put(w,&rank[i],lane,rk>>i&1!=0);}for i in 0..6{put(w,&a[i],lane,av>>i&1!=0);if phase==0{put(w,&c[i],lane,false);}}
                    for i in 0..4{put(w,&sm[i],lane,sv>>(i+2)&1!=0);}put(w,&p1,lane,phase&2!=0);put(w,&p2,lane,phase&1!=0);put(w,&sign,lane,pattern&8!=0);
                    for i in 0..256{put(w,&w1[i],lane,(i<=av&&bit(r,0,i))||(i>av&&bit(r,2,258-i)));}
                    for i in 0..259{let raw=(i+shift)%259;put(w,&w2[i],lane,(raw<=av&&bit(r,1,raw))||(raw>av&&bit(r,3,258-raw)));}
                    if !bit(r,0,0){for i in 0..3{put(w,&w2[(259+i-shift)%259],lane,bit(r,2,i));}}
                    put(w,&w1[av],lane,pattern&1!=0);put(w,&w2[av+1],lane,pattern&2!=0);put(w,&w1[av+1],lane,pattern&4!=0);
                }
                if phase==0{if r[130]!=0{after[sign.id()as usize]^=1u64<<lane;}active+=1;if av==253&&sv==1{a253s1+=1;}}
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());
            if sim.qubits!=after{let bad:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();let lanes:u64=sim.qubits.iter().zip(&after).map(|(x,y)|x^y).fold(0,|x,y|x|y);let cases:Vec<_>=(0..63).filter(|&l|lanes>>l&1!=0).map(|l|{let r=rows[(batch*63+l)%rows.len()];(l,r[128],r[129],r[130])}).collect();panic!("physical R00 r02 block={block} j={j} pattern={pattern} batch={batch} diffs={bad:?} cases={cases:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }}
    eprintln!("Q793_R00_PHYSICAL_R02_PASS lanes={total} active={active} terminal={terminal} A253_S1={a253s1} scalar_rows={count} templates={}; actual first/second/global-loan passengers, all8 cargo patterns and both Sign accumulators, three off phases, physical pre-rotation and terminal lifetime, exact integer r<v<<(S+1), all-wire/phase/literal-inverse restoration; no whole-step claim",blocks*4);
}
