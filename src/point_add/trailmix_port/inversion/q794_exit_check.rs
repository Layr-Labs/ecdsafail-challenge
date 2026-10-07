//! New dual-cargo, two-hole exit only. Never invokes the public implementation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn active() {
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn bit(r:&[u8],i:usize)->bool{r[i/8]>>(i%8)&1!=0}
    fn bits(r:&[u8],i:usize,n:usize)->usize{(0..n).map(|k|(bit(r,i+k)as usize)<<k).sum()}
    fn put(w:&mut[u64],i:usize,lane:usize,v:bool){let b=1u64<<lane;w[i]=(w[i]&!b)|if v{b}else{0};}
    std::env::set_var("Q795_PHASE_LOAN","1");std::env::set_var("Q796_PARITY","1");std::env::set_var("Q794_MOD4","1");
    let data=std::fs::read(std::env::var("LOWQ_EXIT_BOUNDARY_CAPSULE").expect("explicit immutable exit capsule")).unwrap();
    assert_eq!(&data[..8],b"R5EXIT01");
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let rows:Vec<_>=data[12..].chunks_exact(136).filter(|r|bits(r,21,2)==3&&!bit(r,23)&&bits(r,17,4)==0&&triples[bits(r,0,5)][2]==0).collect();
    assert!(!rows.is_empty());
    let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
    let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let it=circ.alloc_qreg("iteration");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("borrowed",23);
    crate::point_add::trailmix_port::inversion::q794_metadata_exit::exit_phase_cargo(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&it,&w1,&w2,&dirty,0,256);
    assert_eq!(circ.b.next_qubit,565);let builder=circ.into_builder();
    for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for i in [257,258]{let hole=w1[i].id()as u64;assert!(op.q_target.0!=hole&&op.q_control1.0!=hole&&op.q_control2.0!=hole,"exit emitted omitted lane{i}");}}
    eprintln!("Q794_DUAL_EXIT_BUILT ops={} T={}",builder.ops.len(),builder.ops.iter().filter(|o|o.kind==K::CCX).count());
    let mut total=0;let mut first=0;let mut small=0;let mut terminal=0;
    for pattern in 0..6{for batch in 0..rows.len().div_ceil(64){
        let mut seed=0x17953b5e728da401u64^batch as u64^((pattern as u64)<<32);
        let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
        for lane in 0..64{let row=rows[(batch*64+lane)%rows.len()];let cargo=if pattern<4{pattern&1!=0}else{rnd(&mut seed)&1!=0};let second=if pattern<4{pattern&2!=0}else{rnd(&mut seed)&1!=0};
            for (w,r,output) in [(&mut before,&row[..68],false),(&mut after,&row[68..],true)]{
                for i in 0..542{put(w,i,lane,bit(r,if i<23{i}else{i+1}));}
                let av=64*triples[bits(r,0,5)][0]+bits(r,5,6);
                let cv=64*triples[bits(r,0,5)][1]+bits(r,11,6);
                if !output&&av==0{first+=1;assert!(!bit(r,27));}
                if output{assert!(av>=1);if av==1{small+=1;}if av==255{terminal+=1;}}
                if !bit(r,25){assert!(bit(r,284));put(w,283,lane,bit(r,283));put(w,284,lane,bit(r,282));}
                put(w,281,lane,false);put(w,282,lane,false);
                let site=if output{24+av}else{283+259-cv};
                assert!(bit(r,site+1));put(w,site,lane,cargo);
                let second_site=if output{283+av+2}else{24+av+2};
                assert!(!bit(r,second_site+1),"second cargo slot not zero A={av} output={output}");
                assert_ne!(site,second_site);assert!(![281,282].contains(&second_site));
                put(w,second_site,lane,second);
            }
        }
        let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());
        if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("mod4exit pattern={pattern} batch={batch} diffs={diffs:?}");}
        assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}
    eprintln!("Q794_DUAL_EXIT_PASS lanes={total} scalar_rows={} first_exit_lanes={first} newA1_lanes={small} newA255_lanes={terminal}; actual new dual-cargo exit/length path; all4 passenger pairs plus random;, both omitted lanes untouched, literal inverse and all dirty helpers restored; full step and whole Q not yet verified",rows.len());
}

fn offguard() {
    use crate::{circuit::OperationType as K,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn bit(r:&[u8],i:usize)->bool{r[i/8]>>(i%8)&1!=0}
    fn bits(r:&[u8],i:usize,n:usize)->usize{(0..n).map(|k|(bit(r,i+k)as usize)<<k).sum()}
    fn put(w:&mut[u64],i:usize,lane:usize,v:bool){let b=1u64<<lane;w[i]=(w[i]&!b)|if v{b}else{0};}
    fn set(w:&mut[u64],q:&QReg,lane:usize,v:bool){put(w,q.id()as usize,lane,v);}
    std::env::set_var("Q795_PHASE_LOAN","1");std::env::set_var("Q796_PARITY","1");std::env::set_var("Q794_MOD4","1");
    let data=std::fs::read(std::env::var("LOWQ_EXIT_BOUNDARY_CAPSULE").expect("explicit immutable exit capsule")).unwrap();
    assert_eq!(&data[..8],b"R5EXIT01");
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let rows:Vec<_>=data[12..].chunks_exact(136).filter(|r|!(bits(r,21,2)==3&&!bit(r,23)&&bits(r,17,4)==0&&ts[bits(r,0,5)][2]==0)).collect();
    assert!(!rows.is_empty());
    let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
    let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let it=circ.alloc_qreg("iteration");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("borrowed",23);
    crate::point_add::trailmix_port::inversion::q794_metadata_exit::exit_phase_cargo(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&it,&w1,&w2,&dirty,0,256);
    assert_eq!(circ.b.next_qubit,565);let b=circ.into_builder();
    for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for i in [257,258]{let q=w1[i].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q);}}
    eprintln!("Q794_DUAL_EXIT_OFFGUARD_BUILT ops={} T={}",b.ops.len(),b.ops.iter().filter(|o|o.kind==K::CCX).count());
    let mut total=0usize;let mut births=0usize;
    for source in 0..3 {
        let count=match source{0=>rows.len(),1=>32*64*4,_=>149};
        for pattern in 0..4 {for batch in 0..count.div_ceil(64) {
            let mut seed=0x7950ff6a2bd492e1u64^batch as u64^((pattern as u64)<<32)^((source as u64)<<40);
            let mut before:Vec<_>=(0..565).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64 {
                let k=(batch*64+lane)%count;
                let av;
                if source==0 {
                    let r=&rows[k][..68];
                    // Only metadata and phase are copied. All words, iteration,
                    // cargo and external lenders remain independent arbitrary data.
                    for i in 0..23{put(&mut before,i,lane,bit(r,i));}
                    av=64*ts[bits(r,0,5)][0]+bits(r,5,6);
                    // The original capsule keeps the trueS256 Sign discriminator.
                    // The production signless chart stores this birth as C0.
                    if bits(r,21,2)==3&&bit(r,23)&&bits(r,17,4)==0&&ts[bits(r,0,5)][2]==0 {
                        assert_eq!(av,0);assert_eq!(bits(r,0,5),0);assert_eq!(bits(r,11,6),1);
                        set(&mut before,&c[0],lane,false);births+=1;
                    }
                } else if source==1 {
                    let rk=k&31;let al=k>>5&63;let phase=k>>11;
                    for i in 0..5{set(&mut before,&rank[i],lane,rk>>i&1!=0);}
                    for i in 0..6{set(&mut before,&a[i],lane,al>>i&1!=0);}
                    set(&mut before,&p1,lane,phase>>1!=0);set(&mut before,&p2,lane,phase&1!=0);
                    if phase==3{set(&mut before,&sm[0],lane,true);}
                    av=64*ts[rk][0]+al;
                } else {
                    av=255;
                    for i in 0..5{set(&mut before,&rank[i],lane,29>>i&1!=0);}
                    for q in &a{set(&mut before,q,lane,true);}
                    for i in 0..6{set(&mut before,&c[i],lane,k>>i&1!=0);}
                    for i in 0..4{set(&mut before,&sm[i],lane,k>>(i+6)&1!=0);}
                    set(&mut before,&p1,lane,false);set(&mut before,&p2,lane,false);
                }
                // This is the sole global data promise required off guard.
                set(&mut before,&w1[av+1],lane,false);
            }
            let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            if sim.qubits!=before{let diffs:Vec<_>=sim.qubits.iter().zip(&before).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("C06 offguard source={source} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        eprintln!("Q794_DUAL_EXIT_OFFGUARD_SOURCE source={source} cases={count} PASS");
    }
    eprintln!("Q794_DUAL_EXIT_OFFGUARD_PASS lanes={total} scalar_offguard_rows={} birth_lanes={births}; arbitrary whole words and all dirty helpers, every rank/A/disabled-phase combination, all149 terminal histories, exact phase and inverse, omitted lanes untouched",rows.len());
}


pub fn run(){if std::env::var("LOWQ_Q794_NATIVE_MODE").ok().as_deref()==Some("dual-exit-offguard"){offguard();}else{active();}}

