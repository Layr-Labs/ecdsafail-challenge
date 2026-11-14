use super::builder::B;
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Fixed(u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) {
        out.fill(self.0);
    }
}

#[test]
fn average_carry_erase_forced_measurements() {
    for n in [2usize, 4, 8, 32] {
        let mut b = B::new();
        let a = b.alloc_n(n);
        let t = b.alloc_n(n);
        let ctl = b.alloc();
        let flag = b.alloc();
        let pool = b.alloc_n(n);
        b.begin();
        b.carry_erase(&a, &t, ctl, flag, &pool);
        let r = b.end();
        b.play(&r, false);
        let split = b.ops.len();
        b.play(&r, true);
        for byte in [0u8, 255, 170] {
            let mut xof = Fixed(byte);
            let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
            let mask = (1u64 << n) - 1;
            for shot in 0..64 {
                let aa = if shot % 3 == 0 {
                    mask
                } else {
                    ((shot * 17) as u64) & mask
                };
                let tt = if shot % 5 == 0 {
                    mask
                } else {
                    ((shot * 29) as u64) & mask
                };
                let cc = shot % 2 == 0;
                for (i, q) in a.iter().enumerate() {
                    sim.qubits[q.0 as usize] |= ((aa >> i) & 1) << shot;
                }
                for (i, q) in t.iter().enumerate() {
                    sim.qubits[q.0 as usize] |= ((tt >> i) & 1) << shot;
                }
                if cc {
                    sim.qubits[ctl.0 as usize] |= 1 << shot;
                }
                if cc && aa + tt > mask {
                    sim.qubits[flag.0 as usize] |= 1 << shot;
                }
            }
            let initial = sim.qubits.clone();
            sim.apply_iter(b.ops[..split].iter());
            assert_eq!(sim.qubits[flag.0 as usize], 0);
            assert_eq!(sim.phase, 0, "n={n} outcome={byte}");
            for q in &pool {
                assert_eq!(sim.qubits[q.0 as usize], 0);
            }
            let active = (byte.count_ones() * 8) as u64;
            assert_eq!(
                sim.stats.toffoli_gates,
                n as u64 * active,
                "conditional execution count"
            );
            sim.apply_iter(b.ops[split..].iter());
            assert_eq!(sim.qubits, initial, "n={n} outcome={byte} reverse");
            assert_eq!(sim.phase, 0);
        }
    }
}

#[test]
fn c42_var_recycled_exhaustive() {
    use super::modp_ft::var_add_pool;
    for n in [5usize,8,10] {for sparse in [false,true] {
        let p=n/2+1;let mut b=B::new();let a=b.alloc_n(n);let t=b.alloc_n(n);let pool=b.alloc_n(p);
        let add=(0..n).map(|i|if sparse && i%3==1 {None} else {Some(a[i])}).collect::<Vec<_>>();
        b.begin();var_add_pool(&mut b,&t,&add,&pool);let r=b.end();b.play(&r,false);let mid=b.ops.len();b.play(&r,true);
        let (_,nb,_,_)=crate::circuit::analyze_ops(b.ops.iter());let mask=(1u64<<n)-1;
        for byte in [0u8,255,170] {for av in 0..1u64<<n {for batch in 0..(1u64<<n).div_ceil(64) {
            let mut xof=Fixed(byte);let mut sim=Simulator::new(b.width() as usize,nb as usize,&mut xof);
            for shot in 0..64 {for i in 0..n {
                sim.qubits[a[i].0 as usize]|=((av>>i)&1)<<shot;
                sim.qubits[t[i].0 as usize]|=(((batch*64+shot as u64)>>i)&1)<<shot;
            }}
            let initial=sim.qubits.clone();sim.apply_iter(b.ops[..mid].iter());assert_eq!(sim.phase,0);
            let aa=(0..n).filter(|&i|add[i].is_some()).fold(0,|x,i|x|(av&(1<<i)));
            for q in &pool {assert_eq!(sim.qubits[q.0 as usize],0);}
            for shot in 0..64 {let mut out=0;for i in 0..n {out|=((sim.qubits[t[i].0 as usize]>>shot)&1)<<i;}
                assert_eq!(out,((batch*64+shot as u64)+aa)&mask);
            }
            sim.apply_iter(b.ops[mid..].iter());assert_eq!(sim.qubits,initial);assert_eq!(sim.phase,0);
        }}}
        eprintln!("C42 recycled exhaustive n={n} sparse={sparse} pool={p} passed all inputs");
    }}
}

#[test]
fn c42_classical_add_exhaustive() {
    use crate::circuit::analyze_ops;
    use super::modp_ft::classical_add_flag;
    for n in 2..=6 {
        let mut b=B::new();let t=b.alloc_n(n);let y=b.declare_bits(2,n);
        let k=b.alloc();let pool=b.alloc_n(n);
        classical_add_flag(&mut b,&t,&y,k,&pool);
        let (_,nb,_,_)=analyze_ops(b.ops.iter());let mask=(1u64<<n)-1;
        assert_eq!(b.tof,n as u64-1);
        for byte in [0u8,255,170] {for a in 0..1u64<<n {for batch in 0..(1u64<<n).div_ceil(64) {
            let mut xof=Fixed(byte);let mut sim=Simulator::new(b.width() as usize,nb as usize,&mut xof);
            let initial=(0..64).map(|j|(batch*64+j)&mask).collect::<Vec<_>>();
            for shot in 0..64 {for i in 0..n {
                sim.qubits[t[i].0 as usize]|=((initial[shot]>>i)&1)<<shot;
                sim.bits[y[i].0 as usize]|=((a>>i)&1)<<shot;
            }}
            sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0,"n={n} a={a} byte={byte}");
            for q in &pool {assert_eq!(sim.qubits[q.0 as usize],0);}
            for shot in 0..64 {let mut out=0;for i in 0..n {out|=((sim.qubits[t[i].0 as usize]>>shot)&1)<<i;}
                assert_eq!(out,(initial[shot]+a)&mask);assert_eq!((sim.qubits[k.0 as usize]>>shot)&1,(initial[shot]+a)>>n);
            }
        }}}
    }
}

#[test]
fn c42_compare_unconditional() {
    use super::builder::ONE;
    for n in [1usize,2,4,8,32] {for incoming in [false,true] {
        let mut b=B::new();let a=b.alloc_n(n);let t=b.alloc_n(n);let ci=b.alloc();let flag=b.alloc();let pool=b.alloc_n(n);
        b.begin();b.carry_erase_cin(&a,&t,ONE,flag,&pool,incoming.then_some(ci));let r=b.end();b.play(&r,false);let mid=b.ops.len();b.play(&r,true);
        let (_,nb,_,_)=crate::circuit::analyze_ops(b.ops.iter());let mask=(1u64<<n)-1;
        for byte in [0u8,255,170] {
            let mut xof=Fixed(byte);let mut sim=Simulator::new(b.width() as usize,nb as usize,&mut xof);
            for shot in 0..64 {let av=if shot%3==0 {mask} else {(shot as u64*17)&mask};let tv=if shot%5==0 {mask} else {(shot as u64*29)&mask};
                for i in 0..n {sim.qubits[a[i].0 as usize]|=((av>>i)&1)<<shot;sim.qubits[t[i].0 as usize]|=((tv>>i)&1)<<shot;}
                let c=(shot%2) as u64;sim.qubits[ci.0 as usize]|=c<<shot;
                if av+tv+if incoming {c} else {0}>mask {sim.qubits[flag.0 as usize]|=1<<shot;}
            }
            let initial=sim.qubits.clone();sim.apply_iter(b.ops[..mid].iter());assert_eq!(sim.phase,0);assert_eq!(sim.qubits[flag.0 as usize],0);
            for q in &pool {assert_eq!(sim.qubits[q.0 as usize],0);}
            assert_eq!(sim.stats.toffoli_gates,(n as u64-1)*(byte.count_ones()*8) as u64);
            sim.apply_iter(b.ops[mid..].iter());assert_eq!(sim.qubits,initial);assert_eq!(sim.phase,0);
        }
    }}
}
