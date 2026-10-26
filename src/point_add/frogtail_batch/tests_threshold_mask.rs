use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Fixed;
impl XofReader for Fixed {fn read(&mut self,b:&mut[u8]){b.fill(0xa5);}}
fn put(bits:&mut[u64],qs:&[QubitId],shot:usize,value:u64){for(k,q)in qs.iter().enumerate(){if value>>k&1!=0{bits[q.0 as usize]|=1u64<<shot;}}}
fn get(bits:&[u64],qs:&[QubitId],shot:usize)->u64{qs.iter().enumerate().map(|(k,q)|((bits[q.0 as usize]>>shot)&1)<<k).sum()}

#[test]
fn threshold_mask_exact_channel() {
    assert!(std::env::var_os("LILYPAD_THRESHOLD_MASK").is_none(),"test compares the original branch with the new helper");
    for qb in 2usize..=16 {
        let mut b=B::new();let q=b.alloc_n(qb);let v=b.alloc_n(qb);let g=b.alloc_n(4);let e=b.alloc();let dirty=b.alloc_n(4);
        b.begin();finish_mask_no_tmp(&mut b,&q,&v,&g,e,&dirty);let old=b.end();
        b.begin();finish_mask_threshold(&mut b,&q,&v,&g,e,&dirty);let new=b.end();
        b.play(&old,false);let m0=b.ops.len();b.play(&new,false);let m1=b.ops.len();b.play(&new,true);
        assert!(b.ops.iter().all(|o|o.kind!=crate::circuit::OperationType::Hmr));
        let old_t=b.measure(&old,false);let new_t=b.measure(&new,false);
        eprintln!("THRESHOLD_MASK qb={qb} old_T={old_t} new_T={new_t} delta_T={} Q={}",new_t-old_t,b.peak);
        let mask=(1u64<<qb)-1;
        let words:Vec<u64>=if qb<=12 {(0..=mask).collect()}else{
            let mut vv=vec![0,mask];vv.extend((0..qb).map(|k|1<<k));
            vv.extend((0..256u64).map(|k|k.wrapping_mul(0x453e65d)^k.rotate_left(7)).map(|v|v&mask));vv
        };
        let cases:Vec<_>=words.iter().flat_map(|&vv|(0u64..32).map(move|flags|(vv,flags))).collect();
        for(batch,chunk)in cases.chunks(64).enumerate(){
            let mut fa=Fixed;let mut fc=Fixed;
            let mut a=Simulator::new(b.width()as usize,1,&mut fa);let mut c=Simulator::new(b.width()as usize,1,&mut fc);
            let mut qvals=vec![];
            for(shot,&(vv,flags))in chunk.iter().enumerate(){
                let qv=((batch as u64*0x3b+shot as u64*0x71)^vv.rotate_left(3))&mask;qvals.push(qv);
                put(&mut a.qubits,&q,shot,qv);put(&mut a.qubits,&v,shot,vv);put(&mut a.qubits,&g,shot,flags&15);
                put(&mut a.qubits,&[e],shot,flags>>4);put(&mut a.qubits,&dirty,shot,(batch as u64*7+shot as u64*11)&15);
            }
            c.qubits.clone_from(&a.qubits);let initial=a.qubits.clone();
            a.apply_iter(b.ops[..m0].iter());c.apply_iter(b.ops[m0..m1].iter());
            assert_eq!(a.phase,0);assert_eq!(c.phase,0);assert_eq!(a.qubits,c.qubits,"qb={qb} batch={batch}");
            for(shot,&(vv,flags))in chunk.iter().enumerate(){
                let gv=flags&15;let ev=flags>>4;let mut expect=qvals[shot];
                expect^=ev<<(qb-2);expect^=(ev&((vv>>1)&1))<<(qb-1);
                for l in 0..qb-2 {expect^=(ev&((vv>>(l+2))&1)&u64::from(gv>l as u64))<<l;}
                assert_eq!(get(&c.qubits,&q,shot),expect);
            }
            for &id in v.iter().chain(&g).chain([&e]).chain(&dirty){assert_eq!(c.qubits[id.0 as usize],initial[id.0 as usize]);}
            c.apply_iter(b.ops[m1..].iter());assert_eq!(c.phase,0);assert_eq!(c.qubits,initial);
        }
    }
}
