//! Fixed-width even-t/S0 mod4 T10 gate proof, not a scheduled T10 adapter.
//!
//! Inverse input chart has virtual q0=0, t0=0, u0=v0=1 and
//! u1=1 XOR v1 XOR(t1*b0). Physical target0/1 contain b0=r0,b1=r1.
//! Only target bits2..k carry ordinary u bits. The arbitrary decision p
//! becomes q=p XOR[u>=t], and semantic u becomes u-q*t mod2^(k+1).
//! Both b bits remain unchanged; the output quotient chart supplies u1.
//! Source[k]=0 only on guard funds the arbitrary carry-helper passenger.
//! No new clean or dirty rail is allocated. Odd-t/S>0 are NOT handled here.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn cell(circ:&mut Circuit,s:&QReg,t:&QReg,carry:&QReg,g:&QReg,dirty:&[QReg],active:bool,inverse:bool) {
    if !inverse{circ.cx(s,t);circ.cx(carry,s);}
    if active{mixed_mcx(circ,&[(g,true),(t,true),(s,true)],carry,dirty);}
    if inverse{circ.cx(carry,s);circ.cx(s,t);}
}

pub(super) fn emit_inverse(circ:&mut Circuit,source:&[QReg],target:&[QReg],v1:&QReg,g:&QReg,decision:&QReg,carry:&QReg,dirty:&[QReg]) {
    assert_eq!(source.len(),target.len());assert!(source.len()>=3);assert!(dirty.len()>=4);
    let mut ids:Vec<_>=source.iter().chain(target).chain(dirty).map(QReg::id).collect();
    ids.extend([v1.id(),g.id(),decision.id(),carry.id()]);ids.sort_unstable();
    assert!(ids.windows(2).all(|p|p[0]!=p[1]),"fixed T10 chart/lender alias");
    let owned=circ.b.next_qubit;let k=source.len()-1;
    circ.cswap(g,&source[k],carry);
    // Borrow after both omitted low arithmetic bits: t1*(v1 XOR b0).
    mixed_mcx(circ,&[(g,true),(&source[1],true),(v1,true)],carry,dirty);
    mixed_mcx(circ,&[(g,true),(&source[1],true),(&target[0],true)],carry,dirty);
    for i in 2..=k{cell(circ,&source[i],&target[i],carry,g,dirty,i<k,false);}
    // Preserve the donor's full high-input threshold map, including the
    // arbitrary incoming decision and the arbitrary source-top passenger.
    circ.cx(g,decision);
    mixed_mcx(circ,&[(g,true),(carry,true),(&source[k],true)],decision,dirty);
    mixed_mcx(circ,&[(g,true),(carry,true),(&target[k],true)],decision,dirty);
    mixed_mcx(circ,&[(g,true),(decision,true),(carry,true)],&target[k],dirty);
    for i in (2..=k).rev(){
        cell(circ,&source[i],&target[i],carry,g,dirty,i<k,true);
        circ.cx(carry,&source[i]);
        if i<k{mixed_mcx(circ,&[(g,true),(&source[i],true),(decision,true)],&target[i],dirty);}
        circ.cx(carry,&source[i]);
    }
    mixed_mcx(circ,&[(g,true),(&source[1],true),(&target[0],true)],carry,dirty);
    mixed_mcx(circ,&[(g,true),(&source[1],true),(v1,true)],carry,dirty);
    circ.cswap(g,&source[k],carry);
    assert_eq!(circ.b.next_qubit,owned);
}

pub fn run(){
    use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
    struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
    fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
    fn put(w:&mut[u64],q:&QReg,l:usize,v:bool){let b=1u64<<l;w[q.id()as usize]=(w[q.id()as usize]&!b)|if v{b}else{0};}
    fn get(w:&[u64],q:&QReg,l:usize)->bool{w[q.id()as usize]>>l&1!=0}
    fn greater_equal(x:&[bool],y:&[bool])->bool{for(&a,&b)in x.iter().zip(y).rev(){if a!=b{return a;}}true}
    fn sub(x:&[bool],y:&[bool])->Vec<bool>{let mut borrow=false;x.iter().zip(y).map(|(&a,&b)|{let out=a^b^borrow;borrow=(!a&&(b||borrow))||(b&&borrow);out}).collect()}
    let mut total=0usize;let mut off_total=0usize;let mut big_total=0usize;
    for k in [2usize,3,4,5,6,7,256]{
        let mut circ=Circuit::new();let source=circ.alloc_qreg_bits("low.t",k+1);let target=circ.alloc_qreg_bits("low.bu",k+1);
        let v1=circ.alloc_qreg("low.v1");let g=circ.alloc_qreg("low.guard");let decision=circ.alloc_qreg("low.decision");let carry=circ.alloc_qreg("low.carry_guest");let dirty=circ.alloc_qreg_bits("low.dirty",4);let owned=circ.b.next_qubit;
        emit_inverse(&mut circ,&source,&target,&v1,&g,&decision,&carry,&dirty);assert_eq!(circ.b.next_qubit,owned);
        let b=circ.into_builder();for op in &b.ops{op.validate();assert!(matches!(op.kind,K::X|K::CX|K::CCX));}
        let ccx=b.ops.iter().filter(|op|op.kind==K::CCX).count();
        let mut fixed=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut fixed);
        let cases=if k==256{4096}else{((1usize<<(k-1))-1)*(1usize<<k)*16};
        let patterns=if k==256{1}else{16};let mut active_count=0usize;
        for pattern in 0..patterns{for batch in 0..cases.div_ceil(64){
            let mut seed=0x794f105ed842913au64^(k as u64).rotate_left(39)^batch as u64^((pattern as u64)<<24);
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();let mut after=before.clone();
            for lane in 0..64{
                let mut z=(batch*64+lane)%cases;
                let (x,y,b0,b1,q,guest)=if k==256{
                    let mut x:Vec<_>=(0..=k).map(|_|rnd(&mut seed)&1!=0).collect();x[0]=false;x[k]=false;
                    let mut y:Vec<_>=(0..=k).map(|_|rnd(&mut seed)&1!=0).collect();y[0]=true;
                    // Include exact threshold neighbors and no-high-carry corners.
                    match (batch*64+lane)%8{
                        0=>{x.fill(false);x[1]=true;y.fill(false);y[0]=true;},
                        1=>{x.fill(true);x[0]=false;x[k]=false;y=x.clone();y[0]=true;},
                        2=>{y=x.clone();y[0]=true;},
                        3=>{y=x.clone();let one:Vec<_>=(0..=k).map(|i|i==0).collect();y=sub(&y,&one);},
                        _=>{},
                    }
                    (x,y,rnd(&mut seed)&1!=0,rnd(&mut seed)&1!=0,rnd(&mut seed)&1!=0,rnd(&mut seed)&1!=0)
                }else{
                    let guest=z&1!=0;z>>=1;let q=z&1!=0;z>>=1;let b1=z&1!=0;z>>=1;let b0=z&1!=0;z>>=1;
                    let y=2*(z&((1usize<<k)-1))+1;z>>=k;let x=2*(z+1);
                    ((0..=k).map(|i|x>>i&1!=0).collect(),(0..=k).map(|i|y>>i&1!=0).collect(),b0,b1,q,guest)
                };
                assert!(!x[0]&&!x[k]&&y[0]);
                let v=true^y[1]^(x[1]&b0);let qout=q^greater_equal(&y,&x);let yout=if qout{sub(&y,&x)}else{y.clone()};
                for w in [&mut before,&mut after]{
                    for i in 0..=k{put(w,&source[i],lane,x[i]);put(w,&target[i],lane,if i==0{b0}else if i==1{b1}else{y[i]});}
                    put(w,&v1,lane,v);put(w,&g,lane,true);put(w,&decision,lane,q);put(w,&carry,lane,guest);
                    if k!=256{for(i,h)in dirty.iter().enumerate(){put(w,h,lane,pattern>>i&1!=0);}}
                }
                for i in 2..=k{put(&mut after,&target[i],lane,yout[i]);}put(&mut after,&decision,lane,qout);
                // The output chart's virtual q0 reconstructs the missing u1.
                assert_eq!(true^v^(x[1]&b0)^(qout&x[1]),yout[1]);
            }
            sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());
            assert_eq!(sim.qubits,after,"T10 mod4 active k{k} pattern{pattern} batch{batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
            // The same literal inverse is the forward T10 on the output chart.
            sim.qubits.copy_from_slice(&after);sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);
            active_count+=64;
        }}
        for batch in 0..16{
            let mut seed=0x0ff794ceda348517u64^(k as u64).rotate_left(35)^batch;
            let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();before[g.id()as usize]=0;
            // No on-guard chart/source-top promise is imposed off guard.
            sim.qubits.copy_from_slice(&before);sim.apply_iter(b.ops.iter());assert_eq!(sim.qubits,before,"T10 offguard k{k} batch{batch}");assert_eq!(sim.phase,0);
            sim.apply_iter(b.ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);off_total+=64;
        }
        // No helper contains a hidden result; all four dirty patterns were
        // exhaustive at small widths, arbitrary independently at width256.
        assert!(get(&sim.qubits,&g,0)==false);
        total+=active_count;if k==256{big_total=active_count;}
        eprintln!("Q794_T10_FUSED_LOW_CASE k={k} active_lanes={active_count} offguard_lanes=1024 ops={} T={ccx} allocated_delta=0 component_wires={owned}",b.ops.len());
    }
    eprintln!("Q794_T10_FUSED_LOW_PASS active_lanes={total} offguard_lanes={off_total} width256_lanes={big_total}; even-t/S0 virtualq0=0 inverse and literal forward, arbitrary decisions/source-top passenger, exhaustive4dirtybits at widths2..7, whole state/phase/restoration; NOT odd-t/S1+ scheduled adapter or whole Q794");
}
