use super::builder::B;
#[test]
fn c43_native_census() {
    super::frogstrip::SEC.with(|s|*s.borrow_mut()=Some(Default::default()));
    let mut b=B::new();super::pointadd_lilypad::point_add(&mut b);
    let (q,c,_,_)=crate::circuit::analyze_ops(b.ops.iter());
    eprintln!("C43_NATIVE Q={q} C={c} ops={} nativeT={} condT={} allocatorQ={}",b.ops.len(),b.tof,b.tof_cond,b.peak);
    let m=super::frogstrip::SEC.with(|s|s.borrow_mut().take().unwrap());
    for (name,(cost,n)) in m {eprintln!("C43_SEC {name} {cost:.3} {n}");}
}

#[test]
fn c43_mask_tree_contract() {
    use crate::circuit::{analyze_ops,OperationType as K};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Fixed(u8);impl XofReader for Fixed {fn read(&mut self,o:&mut[u8]){o.fill(self.0);}}
    for pooln in 2..=8 {for inverse in [false,true] {
        let mut b=B::new();let q=b.alloc_n(12);let bs=b.alloc_n(12);let g=b.alloc_n(4);
        let e=b.alloc();let f=b.alloc();let pool=b.alloc_n(pooln);
        b.begin();super::lilypad::finish_mask(&mut b,&q,&bs,&g,e,&[f],&pool,None);
        let r=b.end();let cost=b.measure(&r,inverse);b.play(&r,inverse);
        let(nq,nb,_,_)=analyze_ops(b.ops.iter());
        eprintln!("C43_MASK pool={pooln} inv={inverse} expectedT={cost} HMR={}",b.ops.iter().filter(|o|o.kind==K::Hmr).count());
        for payload in 0..16 {for fi in [false,true] {for byte in [0,255,170,85] {for guard in 0..4 {
            let mut tape=Fixed(byte);let mut s=Simulator::new(nq as usize,(nb as usize).max(2),&mut tape);
            for k in 0..4 {s.qubits[g[k].0 as usize]=(0..64).filter(|v|v>>k&1!=0).map(|v|1u64<<v).sum();}
            s.qubits[e.0 as usize]=0xffffffff00000000;
            for k in 0..12 {
                s.qubits[q[k].0 as usize]=0xa5e79c2d7b6108f3u64.rotate_left((k*5+payload)as u32);
                s.qubits[bs[k].0 as usize]=match payload {0..=11=>if k==payload{u64::MAX}else{0},12=>0,13=>u64::MAX,_=>0xd5a3f78c21b94e06u64.rotate_left((k*3+payload)as u32)};
            }
            if fi{s.qubits[f.0 as usize]=u64::MAX;}
            let initial=s.qubits.clone();let mut want=initial.clone();
            let (a,z)=match guard {0=>(u64::MAX,u64::MAX),1=>(0,u64::MAX),2=>(u64::MAX,u64::MAX),_=>(0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc)};
            let active=a&z;s.bits[0]=a;s.bits[1]=z;
            let toggle=|w:&mut Vec<u64>,l:usize| {
                let mut eq=initial[e.0 as usize]&active;for k in 0..4 {let v=initial[g[k].0 as usize];eq&=if l>>k&1!=0{v}else{!v};}w[f.0 as usize]^=eq;
            };
            let consume=|w:&mut Vec<u64>,l:usize| {if l+2<12 {w[q[l].0 as usize]^=active&w[f.0 as usize]&initial[bs[l+2].0 as usize];}};
            if inverse {
                for l in (0..11).rev(){consume(&mut want,l);toggle(&mut want,l);}
                want[f.0 as usize]^=active&initial[e.0 as usize];
                want[q[11].0 as usize]^=active&initial[e.0 as usize]&initial[bs[1].0 as usize];
                want[q[10].0 as usize]^=active&initial[e.0 as usize];
            }else{
                want[q[10].0 as usize]^=active&initial[e.0 as usize];
                want[q[11].0 as usize]^=active&initial[e.0 as usize]&initial[bs[1].0 as usize];
                want[f.0 as usize]^=active&initial[e.0 as usize];
                for l in 0..11 {toggle(&mut want,l);consume(&mut want,l);}
            }
            let mut ops=Vec::new();
            if guard!=0 {
                use crate::circuit::{Op,BitId};
                ops.push(Op{kind:K::PushCondition,c_condition:BitId(0),..Op::empty()});
                ops.push(Op{kind:K::PushCondition,c_condition:BitId(1),..Op::empty()});
                ops.push(Op{kind:K::BitInvert,c_target:BitId(0),..Op::empty()});
            }
            ops.extend(b.ops.iter().copied());
            if guard!=0 {for _ in 0..2 {ops.push(crate::circuit::Op{kind:K::PopCondition,..crate::circuit::Op::empty()});}}
            s.apply_iter(ops.iter());assert_eq!(s.qubits,want,"pool{pooln} inverse{inverse} payload{payload} f{fi} HMR{byte}");assert_eq!(s.phase,0);
        }}}}
    }}
}
