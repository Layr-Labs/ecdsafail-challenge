use super::hold_idle::Plan;
use crate::circuit::{Op, OperationType as K, NO_BIT, NO_QUBIT};
use sha3::{Digest, Sha3_256};
use std::io::Read;
pub(super) fn trailer(ops: &[Op]) -> [Op; 2] {
    assert!(ops.len() >= 2);
    let t = [ops[ops.len() - 2], ops[ops.len() - 1]];
    assert!(
        t[0] == t[1] && matches!(t[0].kind, K::CX | K::X) && t[0].c_condition == NO_BIT,
        "invalid inherited identity tail"
    );
    t
}
pub(super) fn bind(ops: &[Op]) -> ([u8; 32], usize) {
    let (hash, width, _) = bind_layout(ops, &[]);
    (hash, width)
}
fn bind_layout(ops: &[Op], hops: &[(u32, u32, u32)]) -> ([u8; 32], usize, usize) {
    let mut chain = Sha3_256::new();
    chain.update(b"Q659-HOLD-NATIVE-0001");
    chain.update((ops.len() as u64).to_le_bytes());
    let mut maxq = 0;
    let mut buffer = Vec::with_capacity(14 * 16384);
    let (mut hop, mut depth, mut hop_records, mut index) = (0, 0usize, 0usize, 0usize);
    let mut registers = [0usize; 4];
    for chunk in ops.chunks(16384) {
        buffer.clear();
        for g in chunk {
            while hop < hops.len() && hops[hop].0 as usize == index {
                hop_records += 1 + 2 * depth;
                hop += 1;
            }
            match g.kind {
                K::PushCondition => depth += 1,
                K::PopCondition => depth = depth.checked_sub(1).expect("hold stack underflow"),
                K::AppendToRegister => {
                    let r = usize::try_from(g.r_target.0).unwrap();
                    assert!(
                        r < 4
                            && (r < 2) == (g.q_target != NO_QUBIT)
                            && (r >= 2) == (g.c_target != NO_BIT),
                        "unexpected four-register ABI"
                    );
                    registers[r] += 1;
                }
                _ => {}
            }
            index += 1;
            for q in [g.q_target, g.q_control1, g.q_control2] {
                if q != NO_QUBIT {
                    maxq = maxq.max(q.0 as usize + 1);
                }
            }
            let [a, b, t, bt, bc, r] = [
                g.q_control2.0,
                g.q_control1.0,
                g.q_target.0,
                g.c_target.0,
                g.c_condition.0,
                g.r_target.0,
            ]
            .map(|x| x.wrapping_add(1));
            if (a | b | t | bt | bc | r) <= u16::MAX as u64 {
                let mut key = [0u8; 14];
                key[0] = g.kind as u8;
                for (dst, word) in key[2..].chunks_exact_mut(2).zip([a, b, t, bt, bc, r]) {
                    dst.copy_from_slice(&(word as u16).to_le_bytes());
                }
                buffer.extend_from_slice(&key);
            } else {
                buffer.extend_from_slice(&[g.kind as u8, 1]);
                for word in [a, b, t, bt, bc, r] {
                    buffer.extend_from_slice(&word.to_le_bytes());
                }
            }
        }
        chain.update(Sha3_256::digest(&buffer));
    }
    assert_eq!(depth, 0);
    assert_eq!(hop, hops.len());
    assert_eq!(registers, [256; 4]);
    (chain.finalize().into(), maxq, hop_records)
}
fn sites(ops: &[Op], body: usize, plan: &Plan, q: usize) {
    assert_eq!(plan.starts.len(), plan.ends.len());
    for list in [&plan.starts, &plan.ends] {
        assert!(list.windows(2).all(|p| p[0].0 < p[1].0));
        for &(i, w) in list {
            let j = i as usize;
            assert!(j < body && (w as usize) < q);
            let op = ops[j];
            assert!(op.kind == K::CCX && op.c_condition == NO_BIT && op.q_target.0 != w as u64);
        }
    }
    assert!(plan.hops.windows(2).all(|p| p[0].0 <= p[1].0));
    for &(i, f, t) in &plan.hops {
        assert!((i as usize) < body && (f as usize) < q && (t as usize) < q && f != t);
    }
}
pub(super) fn structure(ops: &[Op], body: usize, plan: &Plan, q: usize) -> usize {
    sites(ops, body, plan, q);
    let (mut h, mut depth, mut growth) = (0, 0usize, plan.starts.len() + plan.ends.len());
    for (i, o) in ops[..body].iter().enumerate() {
        while h < plan.hops.len() && plan.hops[h].0 as usize == i {
            growth += 1 + 2 * depth;
            h += 1;
        }
        match o.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => depth = depth.checked_sub(1).unwrap(),
            _ => {}
        }
    }
    assert_eq!(depth, 0);
    assert_eq!(h, plan.hops.len());
    growth
}
pub(super) fn replay(
    ops: Vec<Op>,
    z: &[u8],
    source: [u8; 32],
    expected_table: [u8; 32],
    expected_fingerprint: u64,
) -> Vec<Op> {
    let old_tail = trailer(&ops);
    let body = ops.len() - 2;
    let out = replay_body(ops, z, source, expected_table, expected_fingerprint, body);
    assert_eq!(trailer(&out), old_tail);
    out
}
pub(super) fn replay_body(
    ops: Vec<Op>,
    z: &[u8],
    source: [u8; 32],
    expected_table: [u8; 32],
    expected_fingerprint: u64,
    body: usize,
) -> Vec<Op> {
    assert!(body <= ops.len());
    assert_eq!(
        <[u8; 32]>::from(Sha3_256::digest(z)),
        expected_table,
        "wrong final hold file"
    );
    let mut decoder = zstd::stream::read::Decoder::new(z).unwrap();
    let mut raw = Vec::new();
    decoder.read_to_end(&mut raw).unwrap();
    let (n, fp, plan) = super::hold_table::decode(&raw);
    assert_eq!(n, ops.len());
    assert_eq!(fp, expected_fingerprint);
    drop(raw);
    let (actual, q, hop_records) = bind_layout(&ops, &plan.hops);
    assert_eq!(q, 659);
    assert_eq!(actual, source, "final native circuit changed");
    sites(&ops, body, &plan, q);
    let growth = plan.starts.len() + plan.ends.len() + hop_records;
    assert!(
        growth <= ops.capacity() - n,
        "final hold plan needs additional preallocated headroom"
    );
    let parent_shape = (ops.as_ptr(), ops.capacity());
    let out = super::hold_idle::insert_reloc(ops, &plan);
    assert_eq!(parent_shape, (out.as_ptr(), out.capacity()));
    assert_eq!(out.len(), n + growth);
    eprintln!(
        "Q659_FINAL_HOLDS source={n} saved_fixed={} hops={} operations_added={growth}",
        plan.starts.len(),
        plan.hops.len()
    );
    out
}
