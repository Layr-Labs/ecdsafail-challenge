//! Candidate-only actual R01 adapters. Reads scalar records, never executes
//! the public donor or trusts its intermediate quantum arithmetic.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::{circuit::OperationType as K,sim::Simulator};
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
fn val(w:&[u64],q:&QReg,l:usize)->bool{w[q.id()as usize]>>l&1!=0}
fn bits(r:&[u8],first:usize,n:usize)->usize{(0..n).map(|i|(((r[(first+i)/8]>>((first+i)%8))&1)as usize)<<i).sum()}
fn set(w:&mut[u64],qs:&[QReg],l:usize,v:usize){for(i,q)in qs.iter().enumerate(){put(w,q,l,v>>i&1!=0);}}
pub(super) fn run(){
    let data=std::fs::read(std::env::var("LOWQ_METADATA_FULL_STEP_CAPSULE").unwrap()).unwrap();assert_eq!(&data[..8],b"R5FSTEP1");
    let ts=super::triples();let mut total=0;let mut endpoint=0;let mut a0=0;let mut a1=0;let mut cargo_v1=0;let mut off=0;let mut results=Vec::new();
    for j in 0..4{
        if std::env::var("Q796_ONLY_CLOCK").ok().is_some_and(|v|v.parse::<usize>().unwrap()!=j){continue;}
        let mut circ=Circuit::new();let rank=circ.alloc_qreg_bits("rank",5);let a=circ.alloc_qreg_bits("a",6);let c=circ.alloc_qreg_bits("c",6);let sm=circ.alloc_qreg_bits("sm",4);
        let p1=circ.alloc_qreg("p1");let p2=circ.alloc_qreg("p2");let w1=circ.alloc_qreg_bits("w1",259);let w2=circ.alloc_qreg_bits("w2",259);let dirty=circ.alloc_qreg_bits("borrowed",23);let owned=circ.b.next_qubit;
        super::signless(&mut circ,&rank,&a,&c,&sm,&p1,&p2,&w1,&w2,&dirty,j,259);assert_eq!(circ.b.next_qubit,owned);
        let builder=circ.into_builder();for op in &builder.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        let nt=builder.ops.iter().filter(|op|op.kind==K::CCX).count();eprintln!("Q793_DYNAMIC_TIMEFIX_R01_BUILT j={j} ops={} T={nt} interfaceQ={owned}",builder.ops.len());
        let rows:Vec<_>=data[12..].chunks_exact(138).filter(|row|{let step=u16::from_le_bytes(row[..2].try_into().unwrap())as usize;((step+3)&3)==j&&bits(&row[2..70],21,2)==2}).collect();
        let mut active_here=0;
        for pattern in 0..4{for batch in 0..rows.len().div_ceil(64){
            let mut seed=0x79401a70e15u64^((j as u64)<<48)^((pattern as u64)<<40)^batch as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{
                let row=rows[(batch*64+lane)%rows.len()];let r=&row[2..70];let rk=bits(r,0,5);let av=64*ts[rk][0]+bits(r,5,6);let cv=64*ts[rk][1]+bits(r,11,6);
                let raw_s=64*ts[rk][2]+4*bits(r,17,4)+(j&1)+2*((j>>1)^(cv&1));let sv=if raw_s==0{256}else{raw_s};let shift=sv-1;let sum=av+cv;
                assert!(av<255&&sum+sv<=256);let t0=bits(r,25,1)!=0;
                set(&mut before,&rank,lane,rk);set(&mut before,&a,lane,av&63);set(&mut before,&c,lane,cv&63);set(&mut before,&sm,lane,bits(r,17,4));put(&mut before,&p1,lane,false);put(&mut before,&p2,lane,true);
                for i in 0..259{put(&mut before,&w1[i],lane,bits(r,25+i,1)!=0);put(&mut before,&w2[i],lane,bits(r,284+i,1)!=0);}
                // Encode low residual in the retained coefficient chart BEFORE
                // moving its word. Coefficient heads and both passengers stay
                // independent; no arithmetic reference reads their values.
                if !t0{for bit in 0..3{put(&mut before,&w2[(259+bit-sv%259)%259],lane,bits(r,25+258-bit,1)!=0);}}
                assert_eq!(bits(r,25+av,1),1);assert_eq!(bits(r,284+av+1,1),0);
                put(&mut before,&w1[av],lane,pattern&1!=0);put(&mut before,&w2[av+1],lane,pattern&2!=0);
                // Literal physical pre-rotation for phase01: old index i ->i+1.
                let rotated:Vec<_>=(0..259).map(|i|val(&before,&w2[(i+258)%259],lane)).collect();for i in 0..259{put(&mut before,&w2[i],lane,rotated[i]);}
                assert!(!val(&before,&w1[av+1],lane));
                if av==1&&sv==1{assert_eq!(bits(r,17,4),0);}else{assert!(!val(&before,&w2[av+1],lane));}
                // Holes are deliberately arbitrary and must stay untouched.
                put(&mut before,&w1[256],lane,rnd(&mut seed)&1!=0);put(&mut before,&w1[257],lane,rnd(&mut seed)&1!=0);put(&mut before,&w1[258],lane,rnd(&mut seed)&1!=0);
                for i in 0..owned as usize{after[i]=(after[i]&!(1u64<<lane))|(before[i]&(1u64<<lane));}
                let n=256-sum;assert!(n>=1);let mut x=vec![false;n];let mut y=vec![false;n];
                for i in 0..n{x[i]=i>=shift&&val(&before,&w2[258-i],lane);y[i]=bits(r,25+258-i,1)!=0;}
                let ge=(0..n).rev().find(|&i|x[i]!=y[i]).map(|i|y[i]).unwrap_or(true);let q=(bits(r,25+sum+2,1)!=0)^ge;
                let mut out=y.clone();if q{let mut borrow=false;for i in 0..n{out[i]=y[i]^x[i]^borrow;borrow=(!y[i]&&(x[i]||borrow))||(x[i]&&borrow);}}
                for i in 3..n{put(&mut after,&w1[258-i],lane,out[i]);}
                if sum<=253{put(&mut after,&w1[sum+2],lane,q);}
                if !t0{for bit in 0..3{let v=if bit<n{out[bit]}else if bit==n{q}else{bits(r,25+258-bit,1)!=0};
                    put(&mut after,&w2[(259+bit-shift)%259],lane,v);}}
                endpoint+=usize::from(sum>=254);
                a0+=usize::from(av==0);a1+=usize::from(av==1);cargo_v1+=usize::from(av==254&&shift==1);active_here+=1;
            }
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());
            if sim.qubits!=after{let diffs:Vec<_>=sim.qubits.iter().zip(&after).enumerate().filter(|(_, (x,y))|x!=y).map(|(i,(x,y))|(i,format!("{:016x}",x^y))).collect();panic!("Q793_DYNAMIC_TIMEFIX_R01 active j={j} pattern={pattern} batch={batch} diffs={diffs:?}");}
            assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);total+=64;
        }}
        // All off-phase rank/low-A patterns. Only the documented global gap
        // is normalized; all caches, work bits and remaining lenders are dirty.
        for phase in [0usize,1,3]{for batch in 0..32{
            let mut seed=0x79401ffu64^((j as u64)<<40)^((phase as u64)<<32)^batch as u64;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64{let rk=batch;let av=64*ts[rk][0]+lane;set(&mut before,&rank,lane,rk);set(&mut before,&a,lane,lane);put(&mut before,&p1,lane,phase&1!=0);put(&mut before,&p2,lane,phase&2!=0);if av<255{put(&mut before,&w1[av+1],lane,false);}else{put(&mut before,&w2[258],lane,false);}}
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(builder.ops.iter());assert_eq!(sim.qubits,before,"offphase j={j} phase={phase} rank={batch}");assert_eq!(sim.phase,0);sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);off+=64;
        }}
        // The complete A255 phase01 extension is identity as well. These
        // states are outside nonterminal R01, but must not borrow a hole or
        // mistake the terminal zero host for an arithmetic input.
        for rk in [29usize,30,31]{for smv in 0..16{
            let mut seed=0x79325501u64^((j as u64)<<40)^((rk as u64)<<16)^smv as u64;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();
            for lane in 0..64{set(&mut before,&rank,lane,rk);set(&mut before,&a,lane,63);set(&mut before,&c,lane,lane);
                set(&mut before,&sm,lane,smv);put(&mut before,&p1,lane,false);put(&mut before,&p2,lane,true);put(&mut before,&w2[258],lane,false);}
            let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);
            sim.apply_iter(builder.ops.iter());assert_eq!(sim.qubits,before,"A255 phase01 identity j={j} rank={rk} SM={smv}");assert_eq!(sim.phase,0);
            sim.apply_iter(builder.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);off+=64;
        }}
        results.push(format!("{{\"clock\":{j},\"active_lanes\":{active_here},\"ops\":{},\"T\":{nt},\"extra_allocations\":0}}",builder.ops.len()));
        eprintln!("Q793_DYNAMIC_TIMEFIX_R01_CLOCK_PASS j={j} active={active_here}");
    }
    println!("{{\"kind\":\"candidate actual dynamic three-hole dual-cargo R01\",\"active_lanes\":{total},\"offguard_lanes\":{off},\"A0\":{a0},\"A1\":{a1},\"A254_S1_v1_cargo\":{cargo_v1},\"overflow_endpoint\":{endpoint},\"results\":[{}],\"whole_q793_proven\":false}}",results.join(","));
    eprintln!("Q793_DYNAMIC_TIMEFIX_R01_PASS active={total} offguard={off}; actual rank5 ranges, A0/A1, two independent cargo bits, q1/q2 gather, three physical holes, packed width2/1 endpoints, normalized b2 HA restored, literal inverse/allphase; no whole-circuit claim");
}
