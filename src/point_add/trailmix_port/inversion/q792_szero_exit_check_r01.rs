//! New dual-cargo, three-hole exit against pinned independent scalar records.
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
    let mut circ=Circuit::new();circ.b.count_only=false;circ.b.fiat_hash=None;let m=circ.alloc_qreg_bits("fold20",20);
    let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let it=circ.alloc_qreg("iteration");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("borrowed",23);
    super::emit(&mut circ,&m,&p1,&p2,&it,&w1,&w2,&dirty,0,256);
    assert_eq!(circ.b.next_qubit,564);let builder=circ.into_builder();
    for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));for i in [256,257,258]{let hole=w1[i].id()as u64;assert!(op.q_target.0!=hole&&op.q_control1.0!=hole&&op.q_control2.0!=hole,"exit emitted omitted lane{i}");}}
    eprintln!("FOLD20_SZERO_EXIT_BUILT ops={} T={}",builder.ops.len(),builder.ops.iter().filter(|o|o.kind==K::CCX).count());
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
                if !bit(r,25){assert!(bit(r,284));for k in 0..3{put(w,283+k,lane,bit(r,283-k));}}
                for h in [280,281,282]{put(w,h,lane,false);}
                let site=if output{24+av}else{283+259-cv};
                assert!(bit(r,site+1));put(w,site,lane,cargo);
                let second_site=if output{283+av+2}else if av==254{283+256}else{24+av+2};
                assert!(!bit(r,second_site+1),"second cargo slot not zero A={av} output={output}");
                assert_ne!(site,second_site);assert!(![280,281,282].contains(&second_site));
                put(w,second_site,lane,second);
            }
        }
        let pack=|old:Vec<u64>|{
            let mut out=vec![0u64;564];for i in 20..564{out[i]=old[i+1];}
            for lane in 0..64{let value=|start:usize,n:usize|->usize{(0..n).map(|k|(((old[start+k]>>lane)&1)as usize)<<k).sum()};
                let rk=value(0,5);let al=value(5,6);let cl=value(11,6);let sm=value(17,4);let av=64*triples[rk][0]+al;
                let code=if av==255{assert_eq!((rk,cl,sm),(29,0,0));47}else{super::super::q792_fold20_rank_r01::encode(rk,al,cl,sm,&triples)};
                for bit in 0..20{out[bit]|=(((code>>bit)&1)as u64)<<lane;}
            }out
        };
        let before=pack(before);let after=pack(after);
        let mut f=Fixed;let mut sim=Simulator::new(564,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());
        if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("mod4exit pattern={pattern} batch={batch} diffs={diffs:?}");}
        assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}
    eprintln!("FOLD20_SZERO_EXIT_NATIVE_PASS lanes={total} scalar_rows={} first_exit_lanes={first} newA1_lanes={small} newA255_lanes={terminal}; own20metadata complete exit/length path; all4 passenger pairs plus random; three omitted lanes untouched, literal inverse and all dirty helpers restored; metadata20, zero allocated scratch; full step and whole Q not yet verified",rows.len());
}

fn offguard(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x79)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let m=c.alloc_qreg_bits("m",20);let p1=c.alloc_qreg("p1");let p2=c.alloc_qreg("p2");let it=c.alloc_qreg("it");let w1=c.alloc_qreg_bits("w1",259);let w2=c.alloc_qreg_bits("w2",259);let d=c.alloc_qreg_bits("dirty",23);let n=c.b.next_qubit;
    super::emit(&mut c,&m,&p1,&p2,&it,&w1,&w2,&d,0,256);assert_eq!(n,564);let ops=c.into_builder().ops;let ts=super::super::q792_fold20_rank_r01::triples();
    let mut cases=Vec::new();for code in 0..1<<20{if let Some((r,a,cl,sm))=super::super::q792_fold20_rank_r01::decode(code,&ts){
        if super::super::q792_fold20_rank_r01::encode(r,a,cl,sm,&ts)!=code{continue;}
        let av=64*ts[r][0]+a;let szero=ts[r][2]==0&&sm==0;let birth=r==0&&a==0&&cl==0&&sm==0;
        for phase in 0..4{if phase!=3||!szero||birth{cases.push((code,av,phase));}}
    }}for h in 0..256{cases.push((47|((h&63)<<10)|((h>>6)<<16),255,0));}
    eprintln!("FOLD20_EXIT_OFFGUARD_BUILT cases={} ops={} T={}",cases.len(),ops.len(),ops.iter().filter(|o|o.kind==K::CCX).count());
    let mut total=0;for pattern in 0..2{for batch in 0..cases.len().div_ceil(64){let mut seed=0x792e00ffu64^batch as u64^(pattern<<32);let mut before:Vec<_>=(0..n).map(|_|rnd(&mut seed)).collect();
        for lane in 0..64{let(code,a,phase)=cases[(batch*64+lane)%cases.len()];let mut put=|q:&QReg,v:bool|{let mask=1u64<<lane;let at=q.id()as usize;before[at]=(before[at]&!mask)|if v{mask}else{0};};
            for bit in 0..20{put(&m[bit],code>>bit&1!=0);}put(&p1,phase>>1&1!=0);put(&p2,phase&1!=0);put(if a==255{&w2[258]}else{&w1[a+1]},false);
        }
        let mut f=Fixed;let mut sim=Simulator::new(n as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,before,"exit offguard batch={batch} pattern={pattern}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
    }}eprintln!("FOLD20_EXIT_OFFGUARD_NATIVE_PASS lanes={total} admitted_phase_codes={} terminal_histories=256 arbitrary_data=true inverse=true phase=0",cases.len());
}
pub fn run(){if std::env::var("LOWQ_Q793_NATIVE_MODE").ok().as_deref()==Some("fold20-szero-exit-offguard"){offguard();}else{active();}}
