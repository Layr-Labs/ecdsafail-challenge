//! Independent dynamic-width scalar expectations for our two-hole R00.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
/// Production R00 integration, not merely the Boolean decoder: check every
/// coefficient endpoint, four entry clocks, smallest and large intervals,
/// logical A0/A1 cargo, arbitrary helpers, phase bypass, and both holes.
pub fn run() {
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let b=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!b)|if v{b}else{0};}
    std::env::set_var("Q796_PARITY","1");std::env::set_var("Q794_MOD4","1");
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut total=0;
    let all_templates=std::env::var("LOWQ_Q794_NATIVE_MODE").ok().as_deref()==Some("r00-all");
    let blocks=if all_templates{26}else{1};
    for block in 0..blocks {for j in 0..4{
        let support_end=if all_templates{259-super::shared_step::SCHEDULE_SUPPORTS[block].0}else{259};
        let min_a=257usize.saturating_sub(support_end);
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("borrowed",23);let owned=circ.b.next_qubit;
        super::q794_r00::phase00_with_support(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&w1,&w2,&dirty,j,support_end);
        assert_eq!(circ.b.next_qubit,owned);let builder=circ.into_builder();
        for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for h in [257,258]{let hole=w1[h].id()as u64;assert!(op.q_target.0!=hole&&op.q_control1.0!=hole&&op.q_control2.0!=hole,"R00 touched hole{h}");}}
        eprintln!("Q794_R00_BUILT block={block} j={j} support_end={support_end} ops={} T={}",builder.ops.len(),builder.ops.iter().filter(|o|o.kind==K::CCX).count());
        for pattern in 0..8{for batch in 0..4{
            let mut seed=0x795006aed374b109u64^(j as u64)<<48^(pattern as u64)<<32^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{
                let av=min_a+(64*batch+lane)%(256-min_a);let valid=av<255&&av+j<=255;
                let sv=if valid{j+4*if pattern<2{0}else{(pattern*37+av)%((255-av-j)/4+1)}}else{j};
                let r=triples.iter().position(|&x|x==[av/64,0,sv/64]).unwrap();
                // The inherited terminal code A255 is phase00, not an
                // arbitrary phase bypass. Its special P1 toggle assumes it.
                let phase=if av==255||valid&&pattern<6{0}else{1+(pattern+lane)%3};
                for w in [&mut before,&mut after]{
                    for i in 0..5{put(w,&rank[i],lane,r>>i&1!=0);}
                    for i in 0..6{put(w,&a[i],lane,av>>i&1!=0);if phase==0{put(w,&c[i],lane,false);}}
                    for i in 0..4{put(w,&sm[i],lane,sv>>(i+2)&1!=0);}
                    put(w,&p1,lane,phase&2!=0);put(w,&p2,lane,phase&1!=0);
                }
                if phase==0&&valid{
                    let t=if av==0{1}else{((before[w1[0].id()as usize]>>lane&1)as usize)|if av==1{2}else{((before[w1[1].id()as usize]>>lane&1)as usize)<<1}};
                    let shift=sv+1;let bp0=(259-shift)%259;let bp1=(260-shift)%259;
                    let b=((before[w2[bp0].id()as usize]>>lane&1)as usize)|(((before[w2[bp1].id()as usize]>>lane&1)as usize)<<1);
                    let v=((before[w2[258-shift].id()as usize]>>lane&1)as usize)|if shift<258{((before[w2[257-shift].id()as usize]>>lane&1)as usize)<<1}else{0};
                    let rr=if t&1!=0{3usize.wrapping_sub(b*v).wrapping_mul(t)&3}else{b};
                    let mut less=false;
                    for i in shift..257-av{
                        let x=before[w2[258-i].id()as usize]>>lane&1!=0;
                        let y=if i==1{rr&2!=0}else{before[w1[258-i].id()as usize]>>lane&1!=0};
                        if x!=y{less=x;}
                    }
                    if less{after[sign.id()as usize]^=1u64<<lane;}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("R00 mod4 j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
    }}
    eprintln!("Q794_R00_PASS lanes={total} templates={} helpers=23; production R00 dynamic endpoints, two omitted lanes, direct low carry; existing C5 scratch, A0/A1 head cargo, literal inverse and dirty restoration; full step not yet validated",4*blocks);
}

