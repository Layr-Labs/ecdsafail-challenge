//! Source-bound comparison of the active clean-prefix loan and its old dirty implementation.
use super::builder::B;
use crate::circuit::{BitId, Op, OperationType as K, QubitId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Tape { words: Vec<u64>, at: usize }
impl XofReader for Tape {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        out.copy_from_slice(&self.words[self.at].to_le_bytes()); self.at += 1;
    }
}

struct Ports { q: Vec<QubitId>, bs: Vec<QubitId>, g: Vec<QubitId>, e: QubitId,
    f: QubitId, pool: Vec<QubitId>, spare: QubitId }

fn circuit(new: bool, inverse: bool, guarded: bool) -> (Vec<Op>, Ports, usize) {
    let mut b = B::new();
    let p = Ports { q:b.alloc_n(12), bs:b.alloc_n(12), g:b.alloc_n(5), e:b.alloc(),
        f:b.alloc(), pool:b.alloc_n(2), spare:b.alloc() };
    b.begin();
    if new {
        super::lilypad::finish_mask(&mut b,&p.q,&p.bs,&p.g,p.e,&[p.f],&p.pool,None);
    } else {
        // Exact old active branch at source 94623478; no alternate formula used as its oracle.
        b.cx(p.e,p.q[10]); b.ccx(p.e,p.bs[1],p.q[11]);
        b.cx(p.e,p.f);
        for c in 0..3 {
            let high=[(p.e,false),(p.g[2],c&1==0),(p.g[3],c&2==0)];
            b.mbu_compute(p.pool[0],&high,&p.pool[1..2]);
            for l in 4*c..(4*c+4).min(11) {
                let low=[(p.pool[0],false),(p.g[0],l&1==0),(p.g[1],l&2==0)];
                super::mask::mc_xor(&mut b,&low,p.f,&[],&p.q[..1]);
                if l+2<12 { b.ccx(p.f,p.bs[l+2],p.q[l]); }
            }
            b.mbu_erase(p.pool[0],&high,&p.pool[1..2]);
        }
    }
    let r=b.end(); b.play(&r,inverse);
    if guarded {
        let mut ops=vec![Op{kind:K::PushCondition,c_condition:BitId(0),..Op::empty()},
            Op{kind:K::PushCondition,c_condition:BitId(1),..Op::empty()},
            Op{kind:K::BitInvert,c_target:BitId(0),..Op::empty()}];
        ops.extend(b.ops);ops.push(Op{kind:K::PopCondition,..Op::empty()});
        ops.push(Op{kind:K::PopCondition,..Op::empty()}); b.ops=ops;
    }
    let width=b.width() as usize; (b.ops,p,width)
}

fn low_draws(inverse: bool) -> Vec<usize> {
    let mut out=vec![];let mut at=0;
    let groups=if inverse {[3,4,4]}else{[4,4,3]};
    for n in groups { for i in 0..n {out.push(at+1+i);} at+=n+3; }
    assert_eq!(at,20);out
}

fn words(mode: usize) -> Vec<u64> {
    let mut s=0x1234b769faae0795u64;
    (0..20).map(|i| {s^=s<<13;s^=s>>7;s^=s<<17;
        match mode {0=>0,1=>u64::MAX,2=>s,_=>if i==mode-3 {u64::MAX}else{0}} }).collect()
}

fn inputs(p:&Ports,nq:usize,payload:usize,fi:bool)->Vec<u64> {
    let mut q=vec![0;nq];
    for lane in 0..64 {
        for k in 0..5 {if lane>>k&1!=0 {q[p.g[k].0 as usize]|=1<<lane;}}
        if lane&32!=0 {q[p.e.0 as usize]|=1<<lane;}
    }
    for k in 0..12 {
        q[p.q[k].0 as usize]=0xa5e79c2d7b6108f3u64.rotate_left((k*5+payload) as u32);
        q[p.bs[k].0 as usize]=match payload {0..=11=>if k==payload{u64::MAX}else{0},12=>0,
            13=>u64::MAX,_=>0xd5a3f78c21b94e06u64.rotate_left((k*3+payload)as u32)};
    }
    if fi {q[p.f.0 as usize]=u64::MAX;}q
}

fn reference(initial:&[u64],p:&Ports,inverse:bool,active:u64)->Vec<u64> {
    let mut v=initial.to_vec();let e=active & initial[p.e.0 as usize];
    let toggle=|v:&mut Vec<u64>,l:usize| {
        let mut eq=e;
        for k in 0..4 {let x=initial[p.g[k].0 as usize];eq&=if l>>k&1!=0{x}else{!x};}
        v[p.f.0 as usize]^=eq;
    };
    let consume=|v:&mut Vec<u64>,l:usize| {
        if l+2<12 {v[p.q[l].0 as usize]^=active & v[p.f.0 as usize] & initial[p.bs[l+2].0 as usize];}
    };
    if inverse {
        for l in (0..11).rev(){consume(&mut v,l);toggle(&mut v,l);}
        v[p.f.0 as usize]^=e;
        v[p.q[11].0 as usize]^=e & initial[p.bs[1].0 as usize];v[p.q[10].0 as usize]^=e;
    } else {
        v[p.q[10].0 as usize]^=e;v[p.q[11].0 as usize]^=e & initial[p.bs[1].0 as usize];
        v[p.f.0 as usize]^=e;
        for l in 0..11 {toggle(&mut v,l);consume(&mut v,l);}
    }v
}

#[test]
fn mask_pool_loan_contract() {
    let mut checked=0usize;let mut phase_negative=0u64;let mut dirty_negative=0u64;
    for inverse in [false,true] {
      let low=low_draws(inverse);
      for guard in 0..4 {
        let (old,p,nq)=circuit(false,inverse,guard!=0);
        let (new,_,_)=circuit(true,inverse,guard!=0);
        assert_eq!(old.iter().filter(|o|o.kind==K::Hmr).count(),9);
        assert_eq!(new.iter().filter(|o|o.kind==K::Hmr).count(),20);
        let count=|ops:&[Op]|ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
        assert_eq!(count(&old)-count(&new),22);
        let hmr:Vec<_>=new.iter().enumerate().filter(|(_,o)|o.kind==K::Hmr).map(|(i,_)|i).collect();
        let bad_at=hmr[low[0]];
        assert_eq!(new[bad_at].q_target,p.pool[1]);assert_eq!(new[bad_at+1].kind,K::CZ);
        let mut no_phase=new.clone();no_phase.remove(bad_at+1);
        let mut uncleared=new.clone();uncleared[bad_at].q_target=p.spare;
        for payload in 0..16 {for fi in [false,true] {for mode in 0..23 {
          let nw=words(mode);let ow:Vec<_>=nw.iter().enumerate().filter(|(i,_)|!low.contains(i)).map(|(_,x)|*x).collect();
          let bits=match guard {0=>vec![0x1f09d3b6ee0101a9,u64::MAX],1=>vec![0,u64::MAX],
              2=>vec![u64::MAX,u64::MAX],_=>vec![0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc]};
          let initial=inputs(&p,nq,payload,fi);
          let run=|ops:&[Op],ws:Vec<u64>| {
              let mut tape=Tape{words:ws,at:0};
              let mut sim=Simulator::new(nq,2,&mut tape);
              sim.qubits=initial.clone();sim.bits=bits.clone();sim.apply_iter(ops.iter());
              let result=(sim.qubits,sim.bits,sim.phase);(result,tape.at)
          };
          let ((oq,oc,op),oa)=run(&old,ow);let ((nqv,nc,np),na)=run(&new,nw.clone());
          let active=if guard==0{u64::MAX}else{bits[0]&bits[1]};
          assert_eq!(nqv,reference(&initial,&p,inverse,active),"independent Boolean mask");
          assert_eq!(oq,nqv,"quantum inv{inverse} guard{guard} payload{payload} mode{mode}");
          assert_eq!(oc,nc,"outgoing receipts inv{inverse} guard{guard} mode{mode}");
          assert_eq!(op,np);assert_eq!(np,0);assert_eq!((oa,na),(9,20));
          assert_eq!(nqv[p.pool[0].0 as usize],0);assert_eq!(nqv[p.pool[1].0 as usize],0);
          assert_eq!(nqv[p.spare.0 as usize],0);checked+=64;
          if mode==1 {
              let ((bq,_,bp),_)=run(&no_phase,nw.clone());assert_eq!(bq,nqv);
              phase_negative+=(bp^np).count_ones() as u64;
              let ((bq,_,bp),_)=run(&uncleared,nw);
              let mut differences=bp^np;for (a,b)in bq.iter().zip(&nqv){differences|=a^b;}
              dirty_negative+=differences.count_ones() as u64;
          }
        }}}
      }
    }
    assert!(phase_negative>0);assert!(dirty_negative>0);
    eprintln!("MASK_POOL_LOAN cases={checked} phase_only_negative={phase_negative} uncleared_negative={dirty_negative} directions=2 guards=4 outcomes=23 q/c/phase/scratch PASS");
}

#[test]
fn mask_pool_loan_alias_rejected() {
    let mut b=B::new();let q=b.alloc_n(12);let bs=b.alloc_n(12);let g=b.alloc_n(5);
    let e=b.alloc();let f=b.alloc();let hi=b.alloc();
    for loan in [f,hi,e,g[0],q[0],bs[0]] {
        let rejected=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            super::lilypad::finish_mask(&mut b,&q,&bs,&g,e,&[f],&[hi,loan],None)));
        assert!(rejected.is_err());
    }
}

#[test]
#[ignore]
fn mask_pool_loan_native_stream() {
    use std::io::Write;
    let mut b=B::new();super::pointadd_lilypad::point_add(&mut b);
    let (q,c,_,_)=crate::circuit::analyze_ops(b.ops.iter());
    let mut hash=<sha3::Sha3_256 as sha3::Digest>::new();
    let path=std::env::var("MASK_POOL_NATIVE_PATH").expect("fresh native output path");
    let f=std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
    let mut w=std::io::BufWriter::new(f);w.write_all(b"QECCOPSZ").unwrap();
    w.write_all(&(b.ops.len() as u64).to_le_bytes()).unwrap();
    let mut z=zstd::stream::write::Encoder::new(w,3).unwrap();
    for op in &b.ops {let fields=[op.kind as u64,op.q_control2.0,op.q_control1.0,op.q_target.0,
        op.c_target.0,op.c_condition.0,op.r_target.0];
        for v in fields {let bytes=v.to_le_bytes();sha3::Digest::update(&mut hash,bytes);z.write_all(&bytes).unwrap();}}
    z.finish().unwrap().flush().unwrap();
    let raw=sha3::Digest::finalize(hash);
    let static_t=b.ops.iter().filter(|o|matches!(o.kind,K::CCX|K::CCZ)).count();
    eprintln!("MASK_POOL_NATIVE ops={} Q={q} C={c} allocator_peak={} staticT={static_t} builder_condT={} model={} raw56sha3={raw:x}",
        b.ops.len(),b.peak,b.tof_cond,b.tof as f64-b.tof_cond as f64/2.0);
}
