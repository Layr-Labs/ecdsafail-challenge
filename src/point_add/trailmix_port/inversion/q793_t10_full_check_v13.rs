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
    for block in 0..26{for j in 0..4{
        if std::env::var("Q796_ONLY_BLOCK").ok().is_some_and(|v|v.parse::<usize>().unwrap()!=block){continue;}
        if std::env::var("Q796_ONLY_CLOCK").ok().is_some_and(|v|v.parse::<usize>().unwrap()!=j){continue;}
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let _it=circ.alloc_qreg("it");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("borrowed",23);assert_eq!(circ.b.next_qubit,565);
        let n=super::shared_step::SCHEDULE_SUPPORTS[block].1;circ.q797_a_support=Some(super::metadata_entry_head5::A_SUPPORTS[block]);
        super::q793_t10_full_v13::emit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&w1,&w2,&helpers,n,j);assert_eq!(circ.b.next_qubit,565);let b=circ.into_builder();
        for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for i in [256,257,258]{let q=w1[i].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"T10 touches omitted W1[{i}]");}}
        let t=b.ops.iter().filter(|o|o.kind==K::CCX).count();let weight=if block==25{4}else{16};weighted_t+=weight*t;weighted_ops+=weight*b.ops.len();
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|r|{let time=u16::from_le_bytes(r[..2].try_into().unwrap())as usize;(time-1)/64==block&&(time-1)%4==j}).collect();if rows.is_empty(){continue;}
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
        eprintln!("Q793_T10_FULL_V13_BLOCK block={block} j={j} ops={} T={t} PASS",b.ops.len());
    }}
    eprintln!("Q793_T10_FULL_V13_PASS lanes={total} active={active} C1={c1_count} M255={m255} M256={m256} shortA={short} A253+={extreme} terminal={terminal} C256={c256} weighted_forward_ops={weighted_ops} weighted_forward_T={weighted_t}; all saved geometries/all4passengerpairs+2random/packed3holes/dirty/phase/literalinverse; NOT fullstep or wholeQ793");
}

/// W47 capsule-free differential fixture: q793_t10_full_v13::emit with the
/// W47 lever flags (Q793_A17_V12/Q793_A9A_V12/Q793_A19_SM0) OFF versus ON,
/// driven by identical synthetic 64-lane vectors. OFF is the W46 bitstream,
/// so bitwise equality of final states is the native exactness proof for the
/// lever; the ON circuit must also invert to its input. Every lane enters
/// with the borrowed rails (sm[0..4], iteration, helpers) at zero, exactly as
/// the surrounding adapter prepares them, so the circuit's own guard computes
/// g from contract-consistent metadata and on-g lanes satisfy the v12
/// carry=0-on-g preparation (this is also the A19-sm0 prefix entry value).
/// The fixture runs the whole emit (expand -> pop_and_mask -> add_and_clear
/// -> mask_return -> expand), so an sm[0] restore failure anywhere in the
/// chain shows up as an on-g output diff.
/// Modes a17/stack additionally constrain each lane's (A,C) so the tree
/// address A+C stays inside the block's analytic consumer window (the only
/// domain where on-g states live); mode sm0 needs no constraint because the
/// level-2 refactor is an exact identity on every input given sm[0]=0.
pub fn run_w47_differential(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],i:usize,l:usize,v:bool){let b=1u64<<l;w[i]=(w[i]&!b)|if v{b}else{0};}
    let lever=std::env::var("W47_DIFF_LEVER").unwrap_or_else(|_|"stack".to_string());
    let all=["Q793_A17_V12","Q793_A9A_V12","Q793_A19_SM0"];
    let lever_flags:&[&str]=match lever.as_str(){"sm0"=>&all[2..3],"a17"=>&all[0..2],"stack"=>&all[..],_=>panic!("W47_DIFF_LEVER must be sm0|a17|stack")};
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut lanes_total=0usize;
    for block in 0..super::shared_step::SCHEDULE_BLOCKS{
        if std::env::var("Q796_ONLY_BLOCK").ok().is_some_and(|x|x.parse::<usize>().unwrap()!=block){continue;}
        let (lo,hi)=super::metadata_entry_head5::A_SUPPORTS[block];let n=super::shared_step::SCHEDULE_SUPPORTS[block].1;
        for j in 0..4{
            if std::env::var("Q796_ONLY_CLOCK").ok().is_some_and(|x|x.parse::<usize>().unwrap()!=j){continue;}
            let build=|on:bool|{
                for f in all{std::env::set_var(f,if lever_flags.contains(&f)&&on{"1"}else{"0"});}
                let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
                let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let _it=circ.alloc_qreg("it");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let helpers=circ.alloc_qreg_bits("borrowed",23);
                circ.q797_a_support=Some((lo,hi));
                super::q793_t10_full_v13::emit(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&w1,&w2,&helpers,n,j);
                circ.into_builder()
            };
            let off=build(false);let on=build(true);
            for op in &on.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
            let off_t=off.ops.iter().filter(|o|o.kind==K::CCX).count();let on_t=on.ops.iter().filter(|o|o.kind==K::CCX).count();
            for pattern in 0..2u64{
                let mut seed=0x4776a5d3u64^(block as u64).rotate_left(17)^((j as u64)<<40)^(pattern<<56);
                let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();
                for lane in 0..64{
                    // Contract-consistent synthesis: borrowed rails (sm flags/carry,
                    // helpers, iteration) enter the emit at zero, exactly as the
                    // surrounding adapter prepares them; then g is the circuit's
                    // own guard function of the metadata, so on-g lanes satisfy
                    // the v12 carry=0-on-g preparation by construction.
                    for r in [17usize,18,19,20,23]{put(&mut before,r,lane,false);}
                    for r in 542..565{put(&mut before,r,lane,false);}
                    if lever!="sm0"{
                        // Keep every lane's tree address A+C (mod 256) inside the
                        // analytic window [max(1,A_lo), min(2*A_hi-7,255)].
                        let mcap=(2*hi).saturating_sub(7).min(255);
                        let amax=(hi-1).min(mcap);
                        let av=lo+(rnd(&mut seed)as usize)%(amax+1-lo);
                        let cmax=mcap.saturating_sub(av).min(63);
                        let cv=(rnd(&mut seed)as usize)%(cmax+1);
                        let rk=ts.iter().position(|t|t[0]==av/64&&t[1]==cv/64).unwrap_or(0);
                        for b in 0..5{put(&mut before,b,lane,rk>>b&1!=0);}
                        for b in 0..6{put(&mut before,5+b,lane,(av%64)>>b&1!=0);}
                        for b in 0..6{put(&mut before,11+b,lane,(cv%64)>>b&1!=0);}
                    }
                }
                let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);
                sim.qubits.copy_from_slice(&before);sim.apply_iter(off.ops.iter());let out_off=sim.qubits.clone();
                sim.qubits.copy_from_slice(&before);sim.apply_iter(on.ops.iter());let out_on=sim.qubits.clone();
                if out_off!=out_on{
                    if std::env::var_os("W47_TRACE").is_some(){
                        let dump=|b:&crate::point_add::B,path:String|{use std::io::Write;let mut f=std::fs::File::create(path).unwrap();for o in &b.ops{writeln!(f,"{} {} {} {}",o.kind as u32,o.q_control1.0,o.q_control2.0,o.q_target.0).unwrap();}};
                        dump(&off,format!("/tmp/w47-trace-off-b{block}-j{j}.txt"));dump(&on,format!("/tmp/w47-trace-on-b{block}-j{j}.txt"));
                        let mut f2=std::fs::File::create(format!("/tmp/w47-trace-before-b{block}-j{j}.txt")).unwrap();use std::io::Write;for (i,w) in before.iter().enumerate(){writeln!(f2,"{i} {w:016x}").unwrap();}
                    }
                    let mask:Vec<u64>=out_off.iter().zip(&out_on).map(|(x,y)|x^y).collect();
                    let lane=(0..64).find(|l|mask.iter().any(|w|w>>l&1!=0)).unwrap();
                    let rails:Vec<usize>=mask.iter().enumerate().filter(|&(_,w)|w>>lane&1!=0).map(|(i,_)|i).collect();
                    let get=|w:&[u64],i:usize,l:usize|w[i]>>l&1!=0;
                    let meta:Vec<usize>=(0..23).map(|i|if get(&before,i,lane){1<<0}else{0}).collect();
                    eprintln!("W47_DIFF_FAIL lane={lane} diverging_rails={rails:?} meta01={meta:?}");
                    let av:usize=(5..11).map(|b|if get(&before,b,lane){1<<(b-5)}else{0}).sum();let cv:usize=(11..17).map(|b|if get(&before,b,lane){1<<(b-11)}else{0}).sum();let rk:usize=(0..5).map(|b|if get(&before,b,lane){1<<b}else{0}).sum();
                    eprintln!("W47_DIFF_FAIL lane={lane} rk={rk} av_low={av} cv={cv} sm={}{}{}{} p1={} p2={} g={}",get(&before,17,lane)as usize,get(&before,18,lane)as usize,get(&before,19,lane)as usize,get(&before,20,lane)as usize,get(&before,21,lane)as usize,get(&before,22,lane)as usize,get(&before,542,lane)as usize);
                    panic!("W47 {lever} differential block={block} j={j} pattern={pattern}");
                }
                sim.apply_iter(on.ops.iter().rev());assert_eq!(sim.qubits,before,"W47 {lever} inverse block={block} j={j} pattern={pattern}");
                lanes_total+=64;
            }
            eprintln!("Q793_W47_DIFF block={block} j={j} lever={lever} off_T={off_t} on_T={on_t} PASS");
        }
    }
    eprintln!("Q793_W47_DIFF_PASS lever={lever} lanes={lanes_total}; off=W46 bitstream, on=lever, identical final states + literal inverse; borrowed rails (sm/it/helpers) enter at zero per the surrounding-adapter contract, so on-g lanes satisfy the carry=0-on-g preparation");
}

/// W47 A17 exchanges-level differential: q793_t10_routes_v12::exchanges with
/// the A17+A9a window flags OFF versus ON, driven by synthetic 64-lane
/// vectors whose tree address A+C is placed directly inside the block's
/// analytic consumer window [max(1,A_lo), min(2*A_hi-7,hi_shipped)] (plus the
/// s=0 / s>=hi_ship holes that no build ships). The emit-level differential
/// cannot bind the tree-time address (the emit's guard/codec prefix rewrites
/// the metadata rails en route to the tree), so this fixture drives the tree
/// at the level of the packet's exactness argument: dropped leaves sit off
/// the live address, where the recorded route and its literal inverse cancel.
/// carry enters at zero (the v12 carry=0-on-g contract); g/p/mask/endpoint/
/// source/dirty data are fully random, so armed in-window lanes and every
/// unarmed lane must agree bitwise, and the ON circuit must invert to its
/// input. Synthetic empty-window supports additionally check the rail trap
/// on unarmed lanes (it never fires on A_SUPPORTS: 0/202 both variants).
pub fn run_w47_exchanges_diff(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],i:usize,l:usize,v:bool){let b=1u64<<l;w[i]=(w[i]&!b)|if v{b}else{0};}
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let mut lanes_total=0usize;
    let mut cases:Vec<(usize,usize)>=super::metadata_entry_head5::A_SUPPORTS.to_vec();
    cases.extend_from_slice(&[(0,3),(255,256)]); // synthetic empty-window rail-trap cases
    for (case,(lo,hi)) in cases.into_iter().enumerate(){
        let block=case; if std::env::var("Q796_ONLY_BLOCK").ok().is_some_and(|x|x.parse::<usize>().unwrap()!=block){continue;}
        for endpoint_on in [false,true]{
            let hi_ship=if endpoint_on{256}else{254};
            let floor=lo.max(1).min(255);let cap=(2*hi).saturating_sub(7).min(hi_ship);
            let build=|on:bool|{
                std::env::set_var("Q793_A17_V12",if on{"1"}else{"0"});std::env::set_var("Q793_A9A_V12",if on{"1"}else{"0"});std::env::set_var("Q793_A19_SM0","0");
                let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let _sm=circ.alloc_qreg_bits("sm",4);
                let g=circ.alloc_qreg("g");let p=circ.alloc_qreg("p");let mask=circ.alloc_qreg("mask");let endpoint=circ.alloc_qreg("endpoint");let carry=circ.alloc_qreg("carry");
                let source=circ.alloc_qreg_bits("source",258);let dirty=circ.alloc_qreg_bits("dirty",16);
                circ.q797_a_support=Some((lo,hi));
                if endpoint_on{super::q793_t10_routes_v12::exchanges(&mut circ,&rank,&a,&c,&g,&[&p,&mask],&source,&dirty,&carry,Some(&endpoint));}
                else{super::q793_t10_routes_v12::exchanges(&mut circ,&rank,&a,&c,&g,&[&mask],&source,&dirty,&carry,None);}
                circ.into_builder()
            };
            let off=build(false);let on=build(true);
            for op in &on.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
            let off_t=off.ops.iter().filter(|o|o.kind==K::CCX).count();let on_t=on.ops.iter().filter(|o|o.kind==K::CCX).count();
            for pattern in 0..2u64{
                let mut seed=0x1726a5d3u64^(block as u64).rotate_left(19)^((endpoint_on as u64)<<40)^(pattern<<56);
                let mut before:Vec<_>=(0..300).map(|_|rnd(&mut seed)).collect();
                for lane in 0..64{
                    put(&mut before,25,lane,false); // carry=0 on g (v12 contract)
                    // Armed lanes (g=1) take only addresses whose leaf is kept:
                    // s=0 propagates to the leftmost kept leaf in both builds,
                    // which is source[2] exactly when floor==1 or the rail trap
                    // shipped a lone leaf; in-window s is [floor, min(cap,
                    // hi_ship-1)] (leaves above hi_ship-1 ship in neither
                    // build). Unarmed lanes take anything: route and its
                    // literal inverse cancel exactly in both builds.
                    let armed=before[21]>>lane&1!=0;
                    let dcap=cap.min(hi_ship-1);
                    let s=if !armed&&rnd(&mut seed)%2==0{(rnd(&mut seed)as usize)%256}
                        else if floor>cap{0}
                        else if floor==1&&rnd(&mut seed)%4==0{0}
                        else{floor+rnd(&mut seed)as usize%(dcap+1-floor)};
                    let avmax=s.min(195);let avmin=s.saturating_sub(195);let av=avmin+rnd(&mut seed)as usize%(avmax+1-avmin);let cv=s-av;
                    let rk=ts.iter().position(|t|t[0]==av/64&&t[1]==cv/64).unwrap_or(0);
                    for b in 0..5{put(&mut before,b,lane,rk>>b&1!=0);}
                    for b in 0..6{put(&mut before,5+b,lane,(av%64)>>b&1!=0);}
                    for b in 0..6{put(&mut before,11+b,lane,(cv%64)>>b&1!=0);}
                }
                let mut f=Fixed;let mut sim=Simulator::new(300,0,&mut f);
                sim.qubits.copy_from_slice(&before);sim.apply_iter(off.ops.iter());let out_off=sim.qubits.clone();
                sim.qubits.copy_from_slice(&before);sim.apply_iter(on.ops.iter());let out_on=sim.qubits.clone();
                assert_eq!(out_off,out_on,"W47 exchanges differential case={block} endpoint={endpoint_on} pattern={pattern}");
                sim.apply_iter(on.ops.iter().rev());assert_eq!(sim.qubits,before,"W47 exchanges inverse case={block} endpoint={endpoint_on} pattern={pattern}");
                lanes_total+=64;
            }
            eprintln!("Q793_W47_XDIFF case={block} support=({lo},{hi}) endpoint={endpoint_on} off_T={off_t} on_T={on_t} PASS");
        }
    }
    eprintln!("Q793_W47_XDIFF_PASS lanes={lanes_total}; off=unbounded W46 tree, on=A17+A9a window, identical final states + literal inverse; addresses driven in-window; carry=0 on g");
}
