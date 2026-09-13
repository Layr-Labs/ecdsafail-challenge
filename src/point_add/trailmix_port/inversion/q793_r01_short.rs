//! Exact finite R01 packed-tail maps when the new decision slot is omitted.
//! Caller supplies logical low X and t parity, not uncorrected cargo rails.
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};
use super::length_recompute::mixed_mcx;

fn unique(b: [&QReg; 3], x: &[&QReg], t0: &QReg, g: &QReg, dirty: &[QReg]) {
    assert!(dirty.len() >= 4);
    let mut ids: Vec<_> = b.into_iter().chain(x.iter().copied()).chain([t0, g]).chain(dirty).map(QReg::id).collect();
    ids.sort_unstable(); assert!(ids.windows(2).all(|w| w[0] != w[1]), "short R01 alias");
}
fn permutation(x: usize) -> [usize; 8] {
    match x {
        0 => [0,1,2,3,4,5,6,7],
        1 => [0,4,2,3,1,5,6,7],
        2 => [0,1,4,5,2,3,6,7],
        3 => [0,1,2,4,5,6,3,7],
        _ => unreachable!(),
    }
}
fn transpose(circ: &mut Circuit, b: [&QReg; 3], base: &[(&QReg,bool)], left: usize, right: usize, dirty: &[QReg]) {
    let mut at = left; let mut path = Vec::new();
    for bit in 0..3 { if (left ^ right) >> bit & 1 != 0 {
        path.push((bit, at)); at ^= 1 << bit;
    }}
    assert_eq!(at, right); assert!(!path.is_empty());
    let mut edges = path.clone(); edges.extend(path[..path.len()-1].iter().rev().copied());
    for (bit, pattern) in edges {
        let mut cs = base.to_vec();
        cs.extend((0..3).filter(|&i| i != bit).map(|i| (b[i], pattern >> i & 1 != 0)));
        mixed_mcx(circ, &cs, b[bit], dirty);
    }
}

/// A+C=254: incoming physical remainder field has width3 and the outgoing
/// field width2. Under g and even t, B=r before and B=(decision<<2)|r_new
/// after. Preconditions: X in1..3, r<2X, decision=[r>=X], r_new=r-decision*X.
/// For odd t the chart holds u and stays unchanged. Every off-guard value is
/// identity. X=0 and invalid r values have a specified reversible extension.
pub(super) fn width_two(circ: &mut Circuit, b: [&QReg; 3], x: [&QReg; 2], t0: &QReg, g: &QReg, dirty: &[QReg]) {
    unique(b, &x, t0, g, dirty);
    let owned = (circ.b.next_qubit, circ.b.active_qubits);
    for value in 1..4 {
        let perm = permutation(value);
        let mut sorted = perm; sorted.sort_unstable(); assert_eq!(sorted, [0,1,2,3,4,5,6,7]);
        let base = [(g,true),(t0,false),(x[0],value & 1 != 0),(x[1],value & 2 != 0)];
        let mut visited = [false; 8];
        for root in 0..8 {
            if visited[root] { continue; }
            visited[root] = true; let mut next = perm[root];
            while next != root {
                assert!(!visited[next]); visited[next] = true;
                // (root,c1),(root,c2),... implements the forward directed cycle.
                transpose(circ, b, &base, root, next, dirty);
                next = perm[next];
            }
        }
    }
    assert_eq!((circ.b.next_qubit, circ.b.active_qubits), owned);
}

/// A+C=255: X=1, r in{0,1}; B=(old_qstored_bit0<<2)|r has b1=0.
/// The outgoing packed tail is (old_qstored_bit0<<2)|(r<<1). The reversible
/// extension is a controlled b0/b1 swap, preserving b2 and arbitrary lenders.
pub(super) fn width_one(circ: &mut Circuit, b: [&QReg; 3], t0: &QReg, g: &QReg, dirty: &[QReg]) {
    unique(b, &[], t0, g, dirty);
    let owned = (circ.b.next_qubit, circ.b.active_qubits);
    circ.cx(b[1], b[0]);
    mixed_mcx(circ, &[(g,true),(t0,false),(b[0],true)], b[1], dirty);
    circ.cx(b[1], b[0]);
    assert_eq!((circ.b.next_qubit, circ.b.active_qubits), owned);
}

pub fn run() {
    use crate::{circuit::OperationType as K, sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed; impl XofReader for Fixed { fn read(&mut self, out: &mut [u8]) { out.fill(0x69); } }
    let mut rows = Vec::new();
    for width in [1,2] {
        let mut circ = Circuit::new(); circ.b.count_only = false; circ.b.fiat_hash = None;
        let b = circ.alloc_qreg_bits("q793.short.B", 3); let x = circ.alloc_qreg_bits("q793.short.X", 2);
        let t = circ.alloc_qreg("q793.short.tparity"); let g = circ.alloc_qreg("q793.short.guard");
        let dirty = circ.alloc_qreg_bits("q793.short.dirty", 4); let owned = circ.b.next_qubit;
        if width == 1 { width_one(&mut circ, [&b[0],&b[1],&b[2]], &t, &g, &dirty); }
        else { width_two(&mut circ, [&b[0],&b[1],&b[2]], [&x[0],&x[1]], &t, &g, &dirty); }
        assert_eq!(circ.b.next_qubit, owned);
        for op in &circ.b.ops { op.validate(); assert!(matches!(op.kind,K::X|K::CX|K::CCX)); }
        let nt = circ.b.ops.iter().filter(|o|o.kind==K::CCX).count();
        let cases = 8*4*2*2*16;
        for first in (0..cases).step_by(64) {
            let mut before = vec![0u64;owned as usize]; let mut expected = before.clone();
            for lane in 0..64 {
                let z = first+lane; let bv = z & 7; let xv = z >> 3 & 3; let tv = z >> 5 & 1; let gv = z >> 6 & 1; let dv = z >> 7 & 15;
                let bn = if gv == 0 || tv != 0 { bv } else if width == 1 { ((bv & 1) << 1) | ((bv >> 1) & 1) | (bv & 4) } else { permutation(xv)[bv] };
                if gv != 0 && tv == 0 {
                    if width == 2 && xv != 0 && bv < 2*xv {
                        let decision = usize::from(bv >= xv);
                        assert_eq!(bn, (decision<<2) | (bv-decision*xv));
                    }
                    if width == 1 && bv & 2 == 0 { assert_eq!(bn, (bv & 4) | ((bv & 1) << 1)); }
                }
                for (words, value) in [(&mut before, bv), (&mut expected, bn)] {
                    for bit in 0..3 { words[b[bit].id() as usize] |= (((value >> bit) & 1) as u64) << lane; }
                    for bit in 0..2 { words[x[bit].id() as usize] |= (((xv >> bit) & 1) as u64) << lane; }
                    words[t.id() as usize] |= (tv as u64) << lane; words[g.id() as usize] |= (gv as u64) << lane;
                    for bit in 0..4 { words[dirty[bit].id() as usize] |= (((dv >> bit) & 1) as u64) << lane; }
                }
            }
            let mut f = Fixed; let mut sim = Simulator::new(owned as usize,0,&mut f);
            sim.qubits.copy_from_slice(&before); sim.apply_iter(circ.b.ops.iter());
            assert_eq!(sim.qubits,expected,"Q793 short width={width} first={first}"); assert_eq!(sim.phase,0);
            sim.apply_iter(circ.b.ops.iter().rev()); assert_eq!(sim.qubits,before); assert_eq!(sim.phase,0);
        }
        rows.push(format!("{{\"low_output_width\":{width},\"lanes\":{cases},\"T\":{nt},\"ops\":{},\"new_allocations\":0}}",circ.b.ops.len()));
    }
    println!("{{\"kind\":\"Q793 short packed-tail R01\",\"all_valid_and_extension_inputs\":true,\"all_dirty_guard_phase_inverse\":true,\"results\":[{}],\"dynamic_metadata_cargo_integrated\":false}}",rows.join(","));
}
