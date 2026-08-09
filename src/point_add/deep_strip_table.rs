//! Identity-keyed deep strip for the q=824 trailmix stream, DELETION column.
//!
//! Port of `apply_deep_strip_identity` (q=1153 lineage, src/point_add/mod.rs:1690-1784)
//! with the key store changed from a generated Rust array to a BINARY SIDE TABLE.
//!
//! WHY A SIDE TABLE. The q=1153 table shipped a few thousand keys as a `const`
//! array. This stream's admissible pool is up to 92.3M keys; as generated Rust
//! that is ~6 GB of source, which does not compile, and as a flat key list it is
//! ~4 GB resident. But the stream has only 297,183 DISTINCT operand tuples across
//! its 192,216,787 CCX/CCZ instances (measured), so the census key (tuple,
//! ordinal) is exactly a (tuple_id, ordinal) pair and the entire admitted set is
//! a per-tuple ordinal BITMAP. That is CONSTANT-SIZE in the number of keys:
//!
//!     header     128 B
//!     directory  297,183 x 56 B = 16,642,248 B   every tuple, kind+operands+occ+bit_off
//!     bitmap     192,216,787 b  = 24,027,099 B   sum(occ) == n_gates
//!     TOTAL                       40,669,475 B  (~38.8 MiB)
//!
//! It is embedded with `include_bytes!` rather than memmapped: `build_circuit`
//! runs under bubblewrap with a read-only root, and no mmap crate can be added
//! (the harness builds `--locked --offline`). The table is therefore part of the
//! binary and the route stays ENV-FREE -- nothing is read from the environment
//! or from the filesystem at build time.
//!
//! THE OCCUPANCY TRIPWIRE IS PRESERVED. The census ordinal is only meaningful if
//! the operand tuple occurs exactly as many times in THIS stream as it did in the
//! censused one. If an unrelated edit adds or removes a gate with the same
//! operands, every later ordinal for that tuple slides and the key silently names
//! a different, LIVE gate -- which deletes load-bearing work and corrupts the
//! circuit (measured consequence in the lineage when this happened for real:
//! 7535/9024 classical mismatches). So each directory entry carries its
//! census-time occupancy, and a tuple whose occupancy has moved is DISCARDED
//! wholesale -- loudly, with its key count reported as stale -- rather than
//! applied. A second, stream-global tripwire is added here: the census's
//! order-sensitive stream fingerprint is recomputed over the live CCX/CCZ
//! subsequence and must match the value baked into the table, which catches
//! reorderings that leave every per-tuple occupancy intact.
//!
//! DELETION COLUMN ONLY. This applies `n_fire == 0` removals. It emits no
//! CX/CZ downgrades; the algebraic downgrade class is a separate column and is
//! deliberately not mixed in here.

use crate::circuit::Op;

static TABLE: &[u8] = include_bytes!("strip_table.bin");

const MAGIC: &[u8; 8] = b"DSKBITM1";
const HDR: usize = 128;
const DIR_REC: usize = 56;
const K_CCX: u8 = 13;
const K_CCZ: u8 = 14;

type Tup = (u8, u64, u64, u64, u64);

#[inline]
fn rd_u32(b: &[u8], o: usize) -> u32 {
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
}

#[inline]
fn rd_u64(b: &[u8], o: usize) -> u64 {
    let mut v = [0u8; 8];
    v.copy_from_slice(&b[o..o + 8]);
    u64::from_le_bytes(v)
}

struct Header {
    n_tuples: usize,
    n_bits: u64,
    n_keys: u64,
    stream_fp: u64,
    n_gates: u64,
}

fn header() -> Header {
    assert!(TABLE.len() >= HDR, "strip table truncated");
    assert_eq!(&TABLE[0..8], MAGIC, "strip table magic mismatch");
    assert_eq!(rd_u32(TABLE, 8), 1, "strip table version");
    let h = Header {
        n_tuples: rd_u64(TABLE, 16) as usize,
        n_bits: rd_u64(TABLE, 24),
        n_keys: rd_u64(TABLE, 32),
        stream_fp: rd_u64(TABLE, 40),
        n_gates: rd_u64(TABLE, 48),
    };
    let want = HDR + h.n_tuples * DIR_REC + ((h.n_bits as usize) + 7) / 8;
    assert_eq!(TABLE.len(), want, "strip table size does not match its header");
    h
}

#[inline]
fn dir_entry(i: usize) -> (Tup, u32, u64) {
    let o = HDR + i * DIR_REC;
    let tup = (
        TABLE[o],
        rd_u64(TABLE, o + 8),
        rd_u64(TABLE, o + 16),
        rd_u64(TABLE, o + 24),
        rd_u64(TABLE, o + 32),
    );
    (tup, rd_u32(TABLE, o + 40), rd_u64(TABLE, o + 48))
}

#[inline]
fn bit(bitmap: &[u8], i: u64) -> bool {
    bitmap[(i >> 3) as usize] & (1u8 << (i & 7)) != 0
}

/// Same order-sensitive FNV the census uses (`stream_fingerprint`), over the
/// operand tuple and per-tuple ordinal of every CCX/CCZ, in stream order.
fn stream_fingerprint(ops: &[Op]) -> u64 {
    use std::collections::HashMap;
    let mut ord: HashMap<Tup, u32> = HashMap::with_capacity(1 << 19);
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for op in ops {
        let kb = op.kind as u8;
        if kb != K_CCX && kb != K_CCZ {
            continue;
        }
        let tup = (
            kb,
            op.q_control2.0,
            op.q_control1.0,
            op.q_target.0,
            op.c_condition.0,
        );
        let e = ord.entry(tup).or_insert(0);
        let o = *e as u64;
        *e += 1;
        for v in [tup.0 as u64, tup.1, tup.2, tup.3, tup.4, o] {
            h ^= v;
            h = h.wrapping_mul(0x0000_0100_0000_01B3);
        }
    }
    h
}

/// Delete every CCX/CCZ instance whose (tuple, ordinal) is admitted in the table.
/// Reversibility and phase are untouched: a gate that never fires on any input
/// contributes identity, so removing it removes no computation. Zero qubits move.
pub(crate) fn apply(ops: Vec<Op>) -> Vec<Op> {
    use std::collections::HashMap;

    let h = header();
    if h.n_keys == 0 {
        eprintln!("[deep-strip-identity] table admits 0 keys; nothing to do");
        return ops;
    }
    let bitmap = &TABLE[HDR + h.n_tuples * DIR_REC..];

    // ---- global tripwire: is this the stream the census was taken on? ------
    let live_fp = stream_fingerprint(&ops);
    if live_fp != h.stream_fp {
        eprintln!(
            "[deep-strip-identity] REFUSING TO APPLY: live stream fingerprint {live_fp:#018x} \
             != census fingerprint {:#018x}. The op stream has changed since the census, so \
             every ordinal in the table addresses a different gate. Re-run the census.",
            h.stream_fp
        );
        return ops;
    }

    // ---- pass 1: occupancy of each operand tuple in THIS stream ------------
    let mut occ: HashMap<Tup, u32> = HashMap::with_capacity(h.n_tuples * 2);
    let mut n_gates: u64 = 0;
    for op in &ops {
        let kb = op.kind as u8;
        if kb == K_CCX || kb == K_CCZ {
            n_gates += 1;
            *occ.entry((
                kb,
                op.q_control2.0,
                op.q_control1.0,
                op.q_target.0,
                op.c_condition.0,
            ))
            .or_insert(0) += 1;
        }
    }

    // ---- occupancy tripwire, per tuple -------------------------------------
    // A tuple whose census-time occupancy no longer matches is dropped whole;
    // its admitted keys are counted as stale, never applied.
    let mut live: HashMap<Tup, u64> = HashMap::with_capacity(h.n_tuples * 2);
    let mut stale: u64 = 0;
    let mut stale_tuples: usize = 0;
    for i in 0..h.n_tuples {
        let (tup, tot, boff) = dir_entry(i);
        let keys_here: u64 = (0..tot as u64).filter(|&o| bit(bitmap, boff + o)).count() as u64;
        if occ.get(&tup).copied() == Some(tot) {
            if keys_here > 0 {
                live.insert(tup, boff);
            }
        } else {
            stale += keys_here;
            if keys_here > 0 {
                stale_tuples += 1;
            }
        }
    }
    if stale > 0 {
        eprintln!(
            "  [deep-strip-identity] WARNING: {stale} keys across {stale_tuples} tuples discarded \
             -- their operand tuple's occupancy changed since the census, so their ordinals no \
             longer address the censused gate. Re-run the census against this op stream."
        );
    }

    // ---- pass 2: apply, assigning ordinals in census stream order ----------
    //
    // IN-PLACE COMPACTION. This column only DELETES, so the survivors are a
    // subsequence and can be slid down inside the SAME allocation with a
    // read/write cursor. Building a second `Vec<Op>` instead holds both at once:
    // Op is 56 bytes and the stream is 441,967,961 ops, so the output vector
    // alone reserves 24,750,205,816 B (~23.05 GiB) and the pair peaks at
    // ~49,500,411,632 B (~46.09 GiB) on a 127,535,148 kB (~121.6 GiB) box now
    // shared by three seats plus the supervisor. A global OOM there kills every
    // seat, not just this one, so a 23 GiB convenience copy is not worth it.
    // Compacting in place holds ONE vector: 24,750,205,816 B (~23.05 GiB) peak.
    //
    // `truncate` is deliberate and `shrink_to_fit` is deliberately NOT called:
    // shrinking reallocates and copies, which would reintroduce the very second
    // buffer this change exists to avoid. The surplus capacity is released when
    // `ops` drops. The resulting op sequence is byte-identical to the copying
    // version, so the Fiat-Shamir seed, correctness and score are unchanged.
    let mut ops = ops;
    let mut ord: HashMap<Tup, u32> = HashMap::with_capacity(h.n_tuples * 2);
    let mut removed: u64 = 0;
    let mut w: usize = 0;
    for r in 0..ops.len() {
        let op = ops[r];
        let kb = op.kind as u8;
        if kb == K_CCX || kb == K_CCZ {
            let tup = (
                kb,
                op.q_control2.0,
                op.q_control1.0,
                op.q_target.0,
                op.c_condition.0,
            );
            let e = ord.entry(tup).or_insert(0);
            let o = *e as u64;
            *e += 1;
            if let Some(&boff) = live.get(&tup) {
                if bit(bitmap, boff + o) {
                    removed += 1;
                    continue; // skip the write: this op is deleted
                }
            }
        }
        ops[w] = op;
        w += 1;
    }
    ops.truncate(w);
    let out = ops;
    eprintln!(
        "[deep-strip-identity] removed {removed} / {} dead; downgraded 0 / 0 to CX/CZ; \
         {stale} stale keys skipped",
        h.n_keys
    );
    eprintln!(
        "[deep-strip-identity] stream toffoli-class {n_gates} (census {}) -> {} after strip; \
         table {} bytes, {} tuples, fp {:#018x}",
        h.n_gates,
        n_gates - removed,
        TABLE.len(),
        h.n_tuples,
        h.stream_fp
    );
    out
}
