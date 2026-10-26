use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,x:&mut[u8]){x.fill(0xa5);}}
fn put(x:&mut[u64],q:&[QubitId],s:usize,v:u64){for(k,q)in q.iter().enumerate(){if v>>k&1!=0{x[q.0 as usize]|=1u64<<s;}}}
fn get(x:&[u64],q:&[QubitId],s:usize)->u64{q.iter().enumerate().map(|(k,q)|((x[q.0 as usize]>>s)&1)<<k).sum()}

#[test]
fn nosp_cap_event_lease_exact(){
    assert!(std::env::var_os("LILYPAD_DIRECT_CAP").is_some());
    let mut b=B::new();let h=b.alloc_n(6);let log=b.alloc_n(7);let dirty=b.alloc_n(4);let sigma=b.alloc();let event=b.alloc();
    let w=PWalk{a:vec![],bb:vec![],q:dirty.clone(),h:h.clone(),capq:10,log:log.clone()};
    let sc=PScr{e:event,sg:sigma,d:vec![],tmp:vec![],sp:vec![],pool:vec![]};
    b.begin();cap_logic(&mut b,&w,&sc);let body=b.end();b.play(&body,false);let mid=b.ops.len();b.play(&body,true);
    assert!(b.ops.iter().all(|o|o.kind!=crate::circuit::OperationType::Hmr));
    let mut cases=vec![];
    for hv in 0u64..64{let hs=if hv>=32{hv as i64-64}else{hv as i64};for sg in 0u64..2{
        let ev=sg==1&&hs<=-10;if ev&&hs< -25{continue;}
        for lv in 0u64..128{if ev&&lv>=8{continue;}for dv in 0u64..16{cases.push((hv,sg,lv,dv));}}
    }}
    for chunk in cases.chunks(64){let mut f=Fixed;let mut s=Simulator::new(b.width()as usize,1,&mut f);
        for(shot,&(hv,sg,lv,dv))in chunk.iter().enumerate(){put(&mut s.qubits,&h,shot,hv);put(&mut s.qubits,&log,shot,lv);put(&mut s.qubits,&dirty,shot,dv);put(&mut s.qubits,&[sigma],shot,sg);}
        let initial=s.qubits.clone();s.apply_iter(b.ops[..mid].iter());assert_eq!(s.phase,0);assert_eq!(s.qubits[event.0 as usize],0);
        for(shot,&(hv,sg,lv,dv))in chunk.iter().enumerate(){let hs=if hv>=32{hv as i64-64}else{hv as i64};let ev=sg==1&&hs<=-10;
            assert_eq!(get(&s.qubits,&h,shot),if ev{54}else{hv});
            // low4(-10)=6: the two CNOT repair bits are 1 and2.
            assert_eq!(get(&s.qubits,&log,shot),if ev{((hv&15)^6)|((lv&7)<<4)}else{lv});
            assert_eq!(get(&s.qubits,&dirty,shot),dv);assert_eq!(get(&s.qubits,&[sigma],shot),sg);
        }
        s.apply_iter(b.ops[mid..].iter());assert_eq!(s.phase,0);assert_eq!(s.qubits,initial);
    }
    eprintln!("NO_SP_CAP HB=6 q=10 log=7 event=sc.e cases={} T={} phase=0 eventclean dirtyrestored",cases.len(),b.measure(&body,false));
}
