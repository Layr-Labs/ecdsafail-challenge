//! Integration tests included as a child of modp_ft: these call the three
//! actual rewrite sites, rather than the new helper directly. Set
//! WL_L1_FOLD_HALF=1 externally to exercise the candidate. Each test must
//! fail under WL_L1_FOLD_HALF=1 L1_FOLD_BREAK=1.

use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;
use std::collections::BTreeSet;

struct Forced(u64);
impl XofReader for Forced {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        out.copy_from_slice(&self.0.to_le_bytes());
    }
}

fn mask(n: usize) -> u128 { (1u128 << n) - 1 }

fn vals(n: usize, seed: u64) -> Vec<u128> {
    let mut x = seed;
    let mut next = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    (0..64).map(|i| match i {
        0 => 0,
        1 => mask(n),
        2 => 1,
        3 => mask(n) - 1,
        4 => (1u128 << (n - 1)) - 1,
        5 => 1u128 << (n - 1),
        6 => 0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaau128 & mask(n),
        7 => 0x5555_5555_5555_5555_5555_5555_5555_5555u128 & mask(n),
        _ => ((next() as u128) | ((next() as u128) << 64)) & mask(n),
    }).collect()
}

fn read(qs: &[u64], reg: &[QubitId], shot: usize) -> u128 {
    reg.iter().enumerate().fold(0, |v,(i,q)| v | (((qs[q.0 as usize] >> shot) & 1) as u128) << i)
}

fn run(
    tag: &str,
    b: &B,
    target: &[QubitId],
    sources: &[Vec<QubitId>],
    addend: impl Fn(&[u128]) -> u128,
    unconditional_t: usize,
    conditional_t: usize,
) {
    let tv = vals(target.len(), 0x1327_2468_ace0_579b);
    let sv: Vec<Vec<u128>> = sources.iter().enumerate().map(|(i,s)| vals(s.len(), 0xcafe_0123_abcd_6789 ^ (i as u64 + 1) * 0x10001)).collect();
    let target_ids: BTreeSet<usize> = target.iter().map(|q| q.0 as usize).collect();
    for outcome in [0u64, u64::MAX, 0xaaaa_aaaa_aaaa_aaaa] {
        let mut random = Forced(outcome);
        let mut sim = Simulator::new(b.peak as usize, 10_100, &mut random);
        for shot in 0..64 {
            for (i,q) in target.iter().enumerate() {
                sim.qubits[q.0 as usize] |= (((tv[shot] >> i) & 1) as u64) << shot;
            }
            for (reg,values) in sources.iter().zip(&sv) {
                for (i,q) in reg.iter().enumerate() {
                    sim.qubits[q.0 as usize] |= (((values[shot] >> i) & 1) as u64) << shot;
                }
            }
        }
        let before = sim.qubits.clone();
        sim.apply_iter(b.ops.iter());
        for shot in 0..64 {
            let input: Vec<u128> = sv.iter().map(|v|v[shot]).collect();
            let want = tv[shot].wrapping_add(addend(&input)) & mask(target.len());
            assert_eq!(read(&sim.qubits,target,shot), want, "{tag} outcome={outcome:016x} shot={shot} value");
        }
        assert_eq!(sim.phase, 0, "{tag} outcome={outcome:016x} phase");
        for q in 0..sim.qubits.len() {
            if !target_ids.contains(&q) {
                assert_eq!(sim.qubits[q], before[q], "{tag} outcome={outcome:016x} operand/scratch q{q}");
            }
        }
        assert_eq!(sim.stats.toffoli_gates,
            64 * unconditional_t as u64 + outcome.count_ones() as u64 * conditional_t as u64,
            "{tag} outcome={outcome:016x} executed Toffoli");
    }
    assert_eq!(b.tof, (unconditional_t + conditional_t) as u64, "{tag} emitted Toffoli");
}

fn costs(main: usize, loan: usize, first_copy: bool) -> (usize, usize) {
    let reduction = usize::from(first_copy);
    if super::super::l1_fold::enabled() {
        (main - reduction, loan - reduction)
    } else {
        (main + loan - 2 * reduction, 0)
    }
}

#[test]
fn l1_fold_site_const_forced() {
    let mut shapes = 0;
    for n in [54,58,66] {
        for p in [35usize,38,42,46,50,54,56] {
            for k in [C, C-1, 1, 0xaaaa_5555_0000_0001] {
                let i0 = k.trailing_zeros() as usize;
                let need = n - 1 - i0;
                if p >= need || p <= need - p { continue; }
                for constant_one in [false,true] {
                    let mut b = B::new();
                    let t = b.alloc_n(n);
                    let h = if constant_one { ONE } else { b.alloc() };
                    let pool = b.alloc_n(p);
                    const_add_recycled(&mut b,&t,h,k,&pool);
                    let (main,conditional) = costs(need,need-p,constant_one);
                    let source = if constant_one { vec![] } else { vec![vec![h]] };
                    let tag = format!("const n={n} pool={p} k={k:x} ONE={constant_one}");
                    run(&tag,&b,&t,&source,|s| if constant_one { k as u128 } else { s[0] * k as u128 },main,conditional);
                    shapes += 1;
                }
            }
        }
    }
    assert!(shapes > 100);
    eprintln!("L1_SITE_CONST shapes={shapes} each=64 inputs x 3 forced masks enabled={}",super::super::l1_fold::enabled());
}

#[test]
fn l1_fold_site_var_forced() {
    let mut shapes = 0;
    for n in [54,58,66] {
        for p in [35usize,38,42,46,50,54,56] {
            for sparse in [false,true] {
                let i0 = if sparse { 2 } else { 0 };
                let need = n - 1 - i0;
                if p >= need || p <= need - p { continue; }
                let mut b = B::new();
                let t = b.alloc_n(n);
                let y = b.alloc_n(n);
                let pool = b.alloc_n(p);
                let add: Vec<Option<QubitId>> = (0..n).map(|i| {
                    if sparse {
                        if i < 2 || i % 5 == 0 { None } else { Some(y[(i - 2) % 3]) }
                    } else { Some(y[i]) }
                }).collect();
                var_add_recycled(&mut b,&t,&add,&pool);
                let (main,conditional) = costs(need,need-p,false);
                let tag = format!("var n={n} pool={p} sparse={sparse}");
                run(&tag,&b,&t,&[y.clone()],|s| {
                    if !sparse { s[0] } else {
                        (0..n).filter(|&i|i>=2 && i%5!=0).map(|i| ((s[0] >> ((i-2)%3)) & 1) << i).sum()
                    }
                },main,conditional);
                shapes += 1;
            }
        }
    }
    assert!(shapes > 20);
    eprintln!("L1_SITE_VAR shapes={shapes} each=64 inputs x 3 forced masks enabled={}",super::super::l1_fold::enabled());
}

// Independent accounting of the table's Boolean source basis. This is
// deliberately separate from the arithmetic output reference in `run`.
fn monomial_count(n: usize, nv: usize, table: &dyn Fn(usize)->u128) -> (usize,usize) {
    let mut need = BTreeSet::new();
    let mut first = None;
    for bit in 0..n {
        let mut truth: Vec<bool> = (0..1<<nv).map(|a| ((table(a)>>bit)&1)!=0).collect();
        for variable in 0..nv {
            for assignment in 0..1<<nv {
                if assignment&(1<<variable)!=0 { truth[assignment] ^= truth[assignment^(1<<variable)]; }
            }
        }
        if truth.iter().any(|x|*x) && first.is_none() { first=Some(bit); }
        for (assignment,present) in truth.into_iter().enumerate() {
            if present && assignment.count_ones()>=2 { need.insert(assignment); }
        }
    }
    let mut pending: Vec<usize> = need.iter().copied().collect();
    while let Some(m) = pending.pop() {
        let top=1usize<<(usize::BITS-1-m.leading_zeros());
        let parent=m^top;
        if parent.count_ones()>=2 && need.insert(parent) { pending.push(parent); }
    }
    (need.len(),first.unwrap())
}

#[test]
fn l1_fold_site_jit_forced() {
    let mut shapes=0;
    for n in [54,58,66] {
        // The actual four-variable signed double-fold table.
        let table = |a: usize| -> u128 {
            let d = if a>=10 { a as i128 - 16 } else { a as i128 };
            ((C as i128*d-(a as i128&1))/2).rem_euclid(1i128<<n) as u128
        };
        let (monomials,i0)=monomial_count(n,4,&table);
        let need=n-1-i0;
        for p in [35usize,38,42,46,50,54,56] {
            let Some(effective)=p.checked_sub(monomials+1) else {continue;};
            if effective>=need || effective<=need-effective {continue;}
            let mut b=B::new();
            let t=b.alloc_n(n);
            let vars=b.alloc_n(4);
            let pool=b.alloc_n(p);
            add_table_jit(&mut b,&pool,&t,&vars,&table);
            let loan = need-effective;
            let (main,mut conditional)=costs(need,loan,false);
            if super::super::l1_fold::enabled_at(4) && super::super::l1_fold::borrow_xor_enabled() && loan > 1 {
                conditional -= 1;
            }
            let tag=format!("jit n={n} pool={p} effective={effective} monomials={monomials}");
            run(&tag,&b,&t,&[vars],|s|table(s[0] as usize),main+monomials,conditional);
            shapes+=1;
        }
    }
    assert!(shapes>=6);
    eprintln!("L1_SITE_JIT shapes={shapes} each=64 inputs x 3 forced masks enabled={}",super::super::l1_fold::enabled());
}
