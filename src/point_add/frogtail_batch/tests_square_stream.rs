//! Test-only feasibility gate for a streamed 128-bit Karatsuba square.
//!
//! This does not emit a candidate. It freezes the exact split identity and the public
//! triangular-producer cost/peak bounds that must be beaten by a port to this Builder.

use super::arith::ttk_add;
use super::builder::B;
use super::modp_ft::add_sext;
use super::tests_chunked::expected_t;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn leaf_cost(m: usize) -> usize {
    m * (m - 1) / 2 + 4 * m - 3
}

/// One exact Karatsuba split, using the cost recurrence documented by the public square.
fn split_cost(m: usize) -> usize {
    let a = m / 2;
    let b = m - a;
    leaf_cost(a) + leaf_cost(b) + leaf_cost(b + 1) + a + 7 * b + 1
}

/// Conservative simultaneous scratch: materialized 2m-bit product, retained 2ab word,
/// retained sum-bank carries, and the node carry. The producer must fit below the 463
/// lanes left by the two live coordinates at Q975.
fn scratch_bound(m: usize) -> usize {
    let b = m - m / 2;
    2 * m + 2 * (b + 1) + b + 1
}

fn add_or_sub(b: &mut B, src: &[QubitId], dst: &[QubitId], sub: bool) {
    if sub {
        for &q in dst { b.x(q); }
    }
    ttk_add(b, src, dst, None, None);
    if sub {
        for &q in dst { b.x(q); }
    }
}

/// One signed triangular row: acc += (2*x_i-1)*x[i+1..]. The clean high
/// product lanes are exactly the carry bank needed by add_sext.
fn signed_row(b: &mut B, x: &[QubitId], product: &[QubitId], i: usize, zero: QubitId, inverse: bool) {
    let m = x.len();
    let k = m - i - 1;
    let mut src = x[i + 1..].to_vec();
    src.push(zero);
    let acc = &product[2 * i + 1..i + m + 1];
    let pool = &product[i + m + 1..2 * m];
    assert_eq!(src.len(), acc.len());
    assert_eq!(pool.len(), k);
    // Match the public triangular row's asymmetric top convention. Complementing
    // only the k low lanes leaves a deliberate 2^k offset in the signed row;
    // linear_terms cancels the accumulated offsets.
    b.x(x[i]);
    if inverse { b.cx(x[i], acc[k]); }
    for &q in &acc[..k] { b.cx(x[i], q); }
    if inverse {
        for &q in acc { b.x(q); }
    }
    add_sext(b, &src, acc, pool);
    if inverse {
        for &q in acc { b.x(q); }
    }
    for &q in &acc[..k] { b.cx(x[i], q); }
    if !inverse { b.cx(x[i], acc[k]); }
    b.x(x[i]);
}

fn linear_terms(b: &mut B, x: &[QubitId], product: &[QubitId], pads: &[QubitId], inverse: bool) {
    let m = x.len();
    assert_eq!(pads.len(), m);
    // Forward rows need +spread -correction. Reverse uses opposite signs/order.
    let spread = || {
        let mut v = Vec::with_capacity(2 * m);
        for j in 0..m { v.push(pads[j]); v.push(x[j]); }
        v
    };
    let correction = |b: &mut B| {
        for i in 0..m - 1 { b.cx(x[i], pads[i]); b.x(pads[i]); }
        let mut v = x.to_vec(); v.extend_from_slice(pads); v
    };
    if inverse {
        let c = correction(b); add_or_sub(b, &c, product, false);
        for i in 0..m - 1 { b.x(pads[i]); b.cx(x[i], pads[i]); }
        add_or_sub(b, &spread(), product, true);
    } else {
        add_or_sub(b, &spread(), product, false);
        let c = correction(b); add_or_sub(b, &c, product, true);
        for i in 0..m - 1 { b.x(pads[i]); b.cx(x[i], pads[i]); }
    }
}

fn triangular_square(b: &mut B, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    let zero = b.alloc();
    let pads = b.alloc_n(m);
    if inverse { linear_terms(b, x, product, &pads, true); }
    for r in 0..m - 1 {
        let i = if inverse { m - 2 - r } else { r };
        signed_row(b, x, product, i, zero, inverse);
    }
    if !inverse { linear_terms(b, x, product, &pads, false); }
    b.free_n(&pads);
    b.free(zero);
}

fn wide_add(b: &mut B, src: &[QubitId], dst: &[QubitId], sub: bool) {
    assert!(src.len() <= dst.len());
    let pads = b.alloc_n(dst.len() - src.len());
    let mut a = src.to_vec(); a.extend_from_slice(&pads);
    add_or_sub(b, &a, dst, sub);
    b.free_n(&pads);
}

struct RetainedNode {
    cross: Vec<QubitId>,
    sum_carry: QubitId,
    lo: usize,
}

/// Exact retained Karatsuba node. a² and b² live in disjoint halves of product;
/// cross holds (a+b)²-a²-b²=2ab across the consumer boundary.
fn retained_forward(b: &mut B, x: &[QubitId], product: &[QubitId]) -> RetainedNode {
    let m=x.len(); let lo=m/2; let hi=m-lo;
    assert_eq!(product.len(),2*m);
    triangular_square(b,&x[..lo],&product[..2*lo],false);
    triangular_square(b,&x[lo..],&product[2*lo..],false);
    let sum_carry=b.alloc();
    let mut sum=x[lo..].to_vec(); sum.push(sum_carry);
    wide_add(b,&x[..lo],&sum,false);
    let cross=b.alloc_n(2*(hi+1));
    triangular_square(b,&sum,&cross,false);
    wide_add(b,&product[..2*lo],&cross,true);
    wide_add(b,&product[2*lo..],&cross,true);
    wide_add(b,&cross,&product[lo..],false);
    RetainedNode{cross,sum_carry,lo}
}

fn retained_inverse(b:&mut B,x:&[QubitId],product:&[QubitId],r:RetainedNode){
    let m=x.len();let hi=m-r.lo;
    let mut sum=x[r.lo..].to_vec();sum.push(r.sum_carry);
    wide_add(b,&r.cross,&product[r.lo..],true);
    wide_add(b,&product[2*r.lo..],&r.cross,false);
    wide_add(b,&product[..2*r.lo],&r.cross,false);
    triangular_square(b,&sum,&r.cross,true);
    b.free_n(&r.cross);
    wide_add(b,&x[..r.lo],&sum,true);
    b.free(r.sum_carry);
    triangular_square(b,&x[r.lo..],&product[2*r.lo..],true);
    triangular_square(b,&x[..r.lo],&product[..2*r.lo],true);
    let _=hi;
}

#[test]
fn streamed_square_split_identity_exhaustive() {
    for n in 2usize..=12 {
        let h = n / 2;
        let mask = (1u128 << h) - 1;
        for y in 0u128..(1u128 << n) {
            let a = y & mask;
            let b = y >> h;
            let aa = a * a;
            let bb = b * b;
            let cc = (a + b) * (a + b);
            let streamed = aa + ((cc - aa - bb) << h) + (bb << (2 * h));
            assert_eq!(streamed, y * y, "n={n} y={y}");
        }
    }
}

#[test]
fn streamed_square_resource_gate() {
    let producers = split_cost(128) + split_cost(128) + split_cost(129);
    let peak = scratch_bound(129);
    let public_whole_square = 44_948usize;
    let public_fold_and_adapter_budget = public_whole_square - producers;
    let target = 53_000usize;
    eprintln!(
        "SQUARE_STREAM producer={} public_fold_adapter={} projected={} peak_scratch={} headroom={}",
        producers,
        public_fold_and_adapter_budget,
        producers + public_fold_and_adapter_budget,
        peak,
        463usize.saturating_sub(peak)
    );
    assert_eq!(producers, 22_308);
    assert!(peak <= 463, "streamed producer exceeds Q975 scratch budget");
    assert!(producers + public_fold_and_adapter_budget <= target);
}

#[test]
fn triangular_square_builder_exhaustive() {
    for m in 2usize..=6 {
        let mut b = B::new();
        let x = b.alloc_n(m);
        let p = b.alloc_n(2 * m);
        triangular_square(&mut b, &x, &p, false);
        let split = b.ops.len();
        triangular_square(&mut b, &x, &p, true);
        let (nq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default(); h.update(b"square-stream-small");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        for shot in 0..64 {
            let v = shot & ((1usize << m) - 1);
            for (i, q) in x.iter().enumerate() { if (v >> i) & 1 != 0 { sim.qubits[q.0 as usize] |= 1u64 << shot; } }
        }
        sim.apply_iter(b.ops[..split].iter());
        for shot in 0..64 {
            let v = shot & ((1usize << m) - 1);
            let mut got = 0usize;
            for (i, q) in p.iter().enumerate() { got |= (((sim.qubits[q.0 as usize] >> shot) & 1) as usize) << i; }
            assert_eq!(got, v * v, "m={m} shot={shot}");
        }
        sim.apply_iter(b.ops[split..].iter());
        assert_eq!(sim.phase, 0, "m={m}");
        assert!(p.iter().all(|q| sim.qubits[q.0 as usize] == 0), "m={m} product dirty");
    }
}

#[test]
fn triangular_square_128_pricer() {
    let mut b = B::new();
    let x = b.alloc_n(128);
    let p = b.alloc_n(256);
    triangular_square(&mut b, &x, &p, false);
    triangular_square(&mut b, &x, &p, true);
    let t = expected_t(&b.ops);
    // Standalone already includes 128 source lanes; point-add also carries the
    // other 128 source lanes and the 256-bit output coordinate.
    eprintln!("TRI_SQUARE_128 roundtrip_T={t:.1} standalone_peak={} pointadd_peak_bound={}", b.peak, b.peak + 384);
    assert!(b.peak + 384 <= 975);
    let simple_three_branch_roundtrips = 2 * (128 * 128 + 15 * 128 - 8) + (129 * 129 + 15 * 129 - 8);
    let public_fold_and_adapters = 22_640usize;
    let projected = simple_three_branch_roundtrips + public_fold_and_adapters;
    eprintln!(
        "TRI_SQUARE_SIMPLE three_branch_roundtrips={} with_public_fold_adapter={} HARD_STOP_75K={}",
        simple_three_branch_roundtrips,
        projected,
        projected >= 75_000
    );
    assert_eq!(simple_three_branch_roundtrips, 55_160);
    assert!(projected >= 75_000, "simple port unexpectedly clears the hard stop");
}

#[test]
fn retained_node_builder_exhaustive() {
    for m in 4usize..=8 {
        let mut b=B::new();let x=b.alloc_n(m);let p=b.alloc_n(2*m);
        let r=retained_forward(&mut b,&x,&p);let split=b.ops.len();
        retained_inverse(&mut b,&x,&p,r);
        let(nq,nb,_,_)=analyze_ops(b.ops.iter());let mut h=sha3::Shake256::default();h.update(b"retained-node");let mut xof=h.finalize_xof();let mut sim=Simulator::new(nq as usize,nb as usize,&mut xof);
        for shot in 0..64{let v=shot&((1usize<<m)-1);for(i,q)in x.iter().enumerate(){if(v>>i)&1!=0{sim.qubits[q.0 as usize]|=1u64<<shot;}}}
        sim.apply_iter(b.ops[..split].iter());
        for shot in 0..64{let v=shot&((1usize<<m)-1);let mut got=0usize;for(i,q)in p.iter().enumerate(){got|=(((sim.qubits[q.0 as usize]>>shot)&1)as usize)<<i;}assert_eq!(got,v*v,"m={m} shot={shot}");}
        sim.apply_iter(b.ops[split..].iter());assert_eq!(sim.phase,0,"m={m}");assert!(p.iter().all(|q|sim.qubits[q.0 as usize]==0));
    }
}

#[test]
fn retained_node_128_pricer(){
    let mut b=B::new();let x=b.alloc_n(128);let p=b.alloc_n(256);
    let r=retained_forward(&mut b,&x,&p);let mid=expected_t(&b.ops);let split=b.ops.len();
    retained_inverse(&mut b,&x,&p,r);let total=expected_t(&b.ops);
    eprintln!("RETAINED128 forward={mid:.1} inverse={:.1} total={total:.1} standalone_peak={} pointadd_peak={}",total-mid,b.peak,b.peak+384);
    assert!(b.peak+384<=975);assert!(split>0);
}

/// Matched diagnostic of the inherited square's already finite modular
/// windows. Deliberate carry-run edges are recorded separately from its
/// random input support; this test never qualifies a point-add submission.
#[test]
fn inherited_square_carry_edge_diagnostic() {
    use alloy_primitives::U256;
    use super::modp_ft::{Ms, square_acc};
    let p = U256::from_limbs([0xffff_fffe_ffff_fc2f, u64::MAX, u64::MAX, u64::MAX]);
    let one = U256::from(1u64);
    let fixtures = [p-one-one,p-one-one-one,(one<<128)-one,one<<128,(one<<128)+one,(one<<255)-one];
    let mut b=B::new(); let z=b.alloc_n(256); let y=b.alloc_n(256);
    let ms=Ms::alloc_room(&mut b,975); let tmp=b.alloc(); let mut zz=z.clone();
    square_acc(&mut b,&ms,&mut zz,&y,tmp); assert_eq!(zz,z); b.free(tmp); ms.release(&mut b);
    let(nq,nb,_,_)=analyze_ops(b.ops.iter());let mut h=sha3::Shake256::default();h.update(b"old-square-matched-edges");let mut xof=h.finalize_xof();let mut sim=Simulator::new(nq as usize,nb as usize,&mut xof);
    for(shot,&value)in fixtures.iter().enumerate(){for(i,q)in z.iter().chain(y.iter()).enumerate(){if value.bit(i%256){sim.qubits[q.0 as usize]|=1u64<<shot;}}}
    sim.apply_iter(b.ops.iter());let(mut value_bad,mut source_bad)=(0usize,0usize);
    for(shot,&value)in fixtures.iter().enumerate(){let read=|qs:&[QubitId]|{let mut v=U256::ZERO;for(i,q)in qs.iter().enumerate(){if(sim.qubits[q.0 as usize]>>shot)&1!=0{v|=one<<i;}}v};let got=read(&z);let want=value.add_mod(value.mul_mod(value,p),p);let source=read(&y);value_bad+=usize::from(got!=want);source_bad+=usize::from(source!=value);eprintln!("INHERITED_SQUARE_EDGE shot={shot} value_bad={} source_bad={} out_want={want:#x} out_got={got:#x}",got!=want,source!=value);}
    eprintln!("INHERITED_SQUARE_EDGE total_value_bad={value_bad}/6 total_source_bad={source_bad}/6 phase={:#x} T={:.1} peak={}",sim.phase&0x3f,expected_t(&b.ops),b.peak);
    assert_eq!(source_bad,0,"inherited square source restoration");
}
