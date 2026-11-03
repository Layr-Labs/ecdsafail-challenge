//! Isolated price/identity probe, not a production inverse-double cell.
//! Parent modp_ft includes this file under cfg(test).  It prices the five-AND
//! encoder plus the proposed fused fold with the actual scratch reservation.
use super::*;
use crate::circuit::{analyze_ops, OperationType as K, NO_BIT};
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Fixed(u8);
impl XofReader for Fixed { fn read(&mut self, out: &mut [u8]) { out.fill(self.0); } }

fn cost(ops: &[crate::circuit::Op]) -> f64 {
    let (mut d, mut t) = (0i32, 0.0);
    for o in ops { match o.kind {
        K::PushCondition => d += 1, K::PopCondition => d -= 1,
        K::CCX | K::CCZ => t += 2f64.powi(-d) * if o.c_condition == NO_BIT {1.0} else {0.5},
        _ => {}
    }}
    t
}

// Inputs k1,b1,s1,k2,b2,s2; outputs j1,n,p,u,jhigh.  p is rewritten
// last to jlow.  j = p - n - u is in {-1,0,1} on every input.
fn encode(b: &mut B, v: &[QubitId], a: &[QubitId], erase: bool) {
    let (k1,b1,s1,k2,b2,s2) = (v[0],v[1],v[2],v[3],v[4],v[5]);
    let (j1,n,p,u,jh) = (a[0],a[1],a[2],a[3],a[4]);
    let j1_gate = |b: &mut B, erase: bool| {
        b.cx(s1,b1);
        if erase {b.and_u(k1,b1,j1);} else {b.and_c(k1,b1,j1);}
        b.cx(s1,b1);
    };
    let p_gate = |b: &mut B, erase: bool| {
        b.cx(k2,b2); b.cx(k2,j1);
        if erase {b.cx(k2,p);b.and_u(b2,j1,p);}
        else {b.and_c(b2,j1,p);b.cx(k2,p);}
        b.cx(k2,j1); b.cx(k2,b2);
    };
    let high_gate = |b: &mut B, erase: bool| {
        b.x(p); b.cx(p,n); b.cx(p,u);
        if erase {b.cx(p,jh);b.and_u(n,u,jh);}
        else {b.and_c(n,u,jh);b.cx(p,jh);}
        b.cx(p,u); b.cx(p,n); b.x(p);
    };
    if !erase {
        j1_gate(b,false); b.and_c(j1,s1,n); p_gate(b,false);
        b.and_c(k2,s2,u); high_gate(b,false); b.cx(n,p); b.cx(u,p);
    } else {
        b.cx(u,p); b.cx(n,p); high_gate(b,true); b.and_u(k2,s2,u);
        p_gate(b,true); b.and_u(j1,s1,n); j1_gate(b,true);
    }
}

#[test]
fn l1_inverse_fused_table_price() {
    for room in [56usize,46] { for width in [57usize,58] { for jit in [true,false] { for completed in [false,true] {
        let mut b=B::new();
        let v=b.alloc_n(6); let target=b.alloc_n(width); let bank=b.alloc_n(room);
        // One bank lane holds second carry k2 in a real cell. The next five
        // hold this encoder. k1 occupies Ms.k, outside the bank.
        let a=&bank[1..6]; let pool=&bank[6..];
        encode(&mut b,&v,a,false);
        let t0=cost(&b.ops);
        let mask=(1u128<<width)-1;
        // Only [0,1,2,3,5,6,7,12,13,14] are reachable from the six encoder
        // input bits. Completing the other six entries in the span of
        // monomials [1,2,4,8,3,5,9,10] uses four ANDs instead of eleven.
        // Exhaustive input-tuple checks below bind this support, not a census.
        const COMPLETED: [i128;16]=[0,-1073742068,-2147484136,-3221226204,
            -15,3221226205,2147484137,1073742069,
            4294968286,7516194538,6442452406,-5368709966,
            -4294968273,-5368710341,-6442452409,7516193123];
        let val=|x:usize| -> u128 {
            if completed {return COMPLETED[x].rem_euclid(1i128<<width) as u128;}
            let low=(x&3) as i128;
            let j=((x>>2)&1) as i128-2*((x>>3)&1) as i128;
            (j*C as i128-low*((C-1)/4) as i128).rem_euclid(1i128<<width) as u128
        };
        let vars=[v[1],v[4],a[2],a[4]];
        let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if jit {add_table_jit(&mut b,pool,&target,&vars,&val);}
            else {add_table(&mut b,pool,&target,&vars,&val,false);}
        }));
        if result.is_err() {
            eprintln!("L1_INV_TABLE room={room} width={width} jit={jit} completed={completed} available={} FIT=false",pool.len());
            continue;
        }
        let table=cost(&b.ops)-t0;
        encode(&mut b,&v,a,true);
        let total=cost(&b.ops);
        let (nq,nb,_,_)=analyze_ops(b.ops.iter());
        for tape in [0u8,255,85,170] {
            let mut rng=Fixed(tape);let mut sim=Simulator::new(nq as usize,nb as usize,&mut rng);
            for x in 0..64usize {
                for i in 0..6 {if x>>i&1!=0 {sim.qubits[v[i].0 as usize]|=1<<x;}}
                let z=((x as u128+1)*0x19e3779b97f4a7c1u128)&mask;
                for i in 0..width {if z>>i&1!=0 {sim.qubits[target[i].0 as usize]|=1<<x;}}
            }
            let init=sim.qubits.clone();sim.apply_iter(b.ops.iter());
            for x in 0..64usize {
                let (k1,b1,s1,k2,b2,s2)=((x&1)as i128,((x>>1)&1)as i128,((x>>2)&1)as i128,
                    ((x>>3)&1)as i128,((x>>4)&1)as i128,((x>>5)&1)as i128);
                let h1=b1^k1;let h2=b2^k2^(k1&(b1^s1));
                let d=(1-2*s1)*k1-h1+2*(1-2*s2)*k2-2*h2;
                assert_eq!((d+b1+2*b2)%4,0);
                let delta=(d*C as i128+b1+2*b2)/4;
                let z=((x as u128+1)*0x19e3779b97f4a7c1u128)&mask;
                let got=target.iter().enumerate().fold(0u128,|r,(i,q)|r|(((sim.qubits[q.0 as usize]>>x)&1)as u128)<<i);
                assert_eq!(got,((z as i128+delta).rem_euclid(1i128<<width))as u128,
                    "room={room} width={width} jit={jit} completed={completed} tape={tape} x={x}");
            }
            for &q in &v {assert_eq!(sim.qubits[q.0 as usize],init[q.0 as usize]);}
            for &q in &bank {assert_eq!(sim.qubits[q.0 as usize],0);}
            assert_eq!(sim.phase,0,"room={room} width={width} jit={jit} completed={completed} tape={tape}");
        }
        eprintln!("L1_INV_TABLE room={room} width={width} jit={jit} completed={completed} available={} encoder={t0:.1} table={table:.1} total={total:.1} cases=256 all_wire_phase=PASS",pool.len());
    }}}}
}
