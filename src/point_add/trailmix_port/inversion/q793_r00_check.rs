//! The native oracle checks the stated physical-reader contract, not the
//! global arithmetic origin of arbitrary upper-limb samples. A254 short-v
//! bounds are mathematical: t>=2^254 and t*r+u*v=p imply r<4; R00 has
//! v*2^S<=r, so S0 gives v<4 and S1 gives v=1. A0 has t=1 and 0<=u<t,
//! hence u=0. Short t leading bits follow exact bit_length(t)=A+1.
//! Independent dynamic-width scalar expectations for our three-hole R00.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
/// Production R00 integration, not merely the Boolean decoder: check every
/// coefficient endpoint, four entry clocks, smallest and large intervals,
/// logical A0/A1/A2 cargo, arbitrary helpers, phase bypass, and both holes.
pub fn run() {
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,lane:usize,v:bool){let b=1u64<<lane;let x=&mut w[q.id()as usize];*x=(*x&!b)|if v{b}else{0};}
    std::env::set_var("Q796_PARITY","1");std::env::set_var("Q794_MOD4","1"); // Existing helper configuration only; no old comparator executes.
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut total=0;
    let all_templates=std::env::var("LOWQ_Q793_NATIVE_MODE").ok().as_deref()==Some("r00-all");
    let mbu_check=std::env::var("Q793_MBU_COMPONENT").ok().as_deref()==Some("1");
    let blocks=if all_templates{26}else{1};
    for block in 0..blocks {for j in 0..4{
        let support_end=if all_templates{259-super::shared_step::SCHEDULE_SUPPORTS[block].0}else{259};
        let min_a=257usize.saturating_sub(support_end);
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let sign=circ.alloc_qreg("sign");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("borrowed",23);let owned=circ.b.next_qubit;
        let mut seed=|cc:&mut Circuit,mask:&QReg,carry:&QReg,helpers:&[QReg],clock:usize| {
            if mbu_check{super::q793_r00_seed_dynamic_r02::emit(cc,&rank,&a,&w1,&w2,mask,carry,helpers,clock);}else{super::q793_r00_seed_dynamic::emit(cc,&rank,&a,&w1,&w2,mask,carry,helpers,clock);}
        };
        super::q793_r00::phase00_with_support(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&sign,&w1,&w2,&dirty,j,support_end,&mut seed);
        assert_eq!(circ.b.next_qubit,owned);let builder=circ.into_builder();
        for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for h in [256,257,258]{let hole=w1[h].id()as u64;assert!(op.q_target.0!=hole&&op.q_control1.0!=hole&&op.q_control2.0!=hole,"R00 touched hole{h}");}}
        let producer=if mbu_check{let mut pre=Circuit::new();pre.b.next_qubit=owned;pre.ccx(&p1,&p2,&sign);let mut ops=pre.into_builder().ops;ops.extend(builder.ops.iter().copied());Some(ops)}else{None};
        eprintln!("Q793_R00_BUILT block={block} j={j} support_end={support_end} ops={} T={}",builder.ops.len(),builder.ops.iter().filter(|o|o.kind==K::CCX).count());
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
                    for i in 0..6{put(w,&a[i],lane,av>>i&1!=0);if phase==0&&av!=255{put(w,&c[i],lane,false);}}
                    for i in 0..4{put(w,&sm[i],lane,sv>>(i+2)&1!=0);}
                    put(w,&p1,lane,phase&2!=0);put(w,&p2,lane,phase&1!=0);
                }
                if phase==0&&valid{
                    let shift=sv+1;
                    let mut rr=0usize;
                    if shift<=2 {
                        // Scalar oracle reconstructs semantic low data before
                        // direct interval comparison. It does not call the
                        // emitter's truth table or ANF helper.
                        let raw=|q:&QReg|((before[q.id()as usize]>>lane)&1)as usize;
                        let t=match av{0=>1,1=>raw(&w1[0])|2,2=>raw(&w1[0])|(raw(&w1[1])<<1)|4,
                            _=>raw(&w1[0])|(raw(&w1[1])<<1)|(raw(&w1[2])<<2)};
                        let b=if av==0{0}else{(0..3).map(|k|raw(&w2[(259+k-shift)%259])<<k).sum()};
                        let mut v:usize=(0..3).map(|k|raw(&w2[258-shift-k])<<k).sum();
                        if av==254 {v&=if shift==1{3}else{1};}
                        rr=if t&1!=0 {
                            let inverse=(0..8).find(|x|x*t%8==1).unwrap();
                            (71usize-b*v)*inverse&7
                        }else{b};
                    }
                    let mut less=false;
                    for i in shift..257-av{
                        let x=before[w2[258-i].id()as usize]>>lane&1!=0;
                        let y=if i<3{rr>>i&1!=0}else{before[w1[258-i].id()as usize]>>lane&1!=0};
                        if x!=y{less=x;}
                    }
                    if less{after[sign.id()as usize]^=1u64<<lane;}
                }
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();if mbu_check{assert!(diffs.iter().all(|(i,_)|*i==sign.id()as usize),"MBU producer changed a non-Sign wire j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}else{panic!("R00 mod8 j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}}
            assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
            if let Some(producer)=&producer{let mut clean=before.clone();clean[sign.id()as usize]=0;let mut g=Fixed;let mut produced=Simulator::new(owned as usize,0,&mut g);produced.qubits.copy_from_slice(&clean);produced.apply_iter(producer.iter());super::q793_mbu::check_producer(&produced.qubits,producer,crate::circuit::QubitId(sign.id()as u64));}
        }}
    }}
    eprintln!("Q793_R00_PASS lanes={total} templates={} helpers=23 mbu_both_outcomes={mbu_check}; production R00 dynamic endpoints, three omitted lanes, direct low carry; existing C5 scratch, A0/A1/A2 head cargo and A254 short-v, literal inverse and dirty restoration; full step not yet validated",4*blocks);
}
