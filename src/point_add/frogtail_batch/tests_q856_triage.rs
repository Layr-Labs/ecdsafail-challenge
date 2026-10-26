//! Untrusted diagnostic replay of the frozen trusted packet/corpus.
//! This intentionally duplicates the public trusted run order without sharing
//! or modifying evaluator code, and emits all failure masks for localization.

use crate::circuit::{analyze_ops, OperationType as K, QubitId, QubitOrBit};
use crate::sim::Simulator;
use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
use ruint::aliases::U256;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use super::builder::B;

#[derive(Clone)]
struct Row {
    draw: usize,
    xr: U256,
    yr: U256,
    xa: U256,
    ya: U256,
    xe: U256,
    ye: U256,
    raw: Vec<String>,
}

fn u(s: &str) -> U256 {
    U256::from_str_radix(s.trim_start_matches("0x"), 16).unwrap()
}

fn curve() -> WeierstrassEllipticCurve {
    let h = |s: &str| U256::from_str_radix(s, 16).unwrap();
    WeierstrassEllipticCurve {
        modulus: h("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U256::ZERO,
        b: U256::from(7u64),
        gx: h("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: h("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: h("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    }
}

fn fiat_shamir_seed(ops: &[crate::circuit::Op]) -> sha3::Shake256Reader {
    let mut h = sha3::Shake256::default();
    h.update(b"quantum_ecc-fiat-shamir-v2");
    h.update(&(ops.len() as u64).to_le_bytes());
    for op in ops {
        h.update(&[op.kind as u8]);
        h.update(&op.q_control2.0.to_le_bytes());
        h.update(&op.q_control1.0.to_le_bytes());
        h.update(&op.q_target.0.to_le_bytes());
        h.update(&op.c_target.0.to_le_bytes());
        h.update(&op.c_condition.0.to_le_bytes());
        h.update(&op.r_target.0.to_le_bytes());
    }
    h.finalize_xof()
}

fn indices(batch: usize, mask: u64) -> String {
    (0..64)
        .filter(|bit| mask >> bit & 1 != 0)
        .map(|bit| (batch * 64 + bit).to_string())
        .collect::<Vec<_>>()
        .join(",")
}

struct Fixed(u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) { out.fill(self.0); }
}

fn corpus_rows(path: &str) -> Vec<Row> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .filter(|line| !line.starts_with('#') && !line.starts_with("draw\t") && !line.trim().is_empty())
        .map(|line| {
            let f: Vec<String> = line.split('\t').map(str::to_owned).collect();
            assert_eq!(f.len(), 11);
            Row {
                draw: f[0].parse().unwrap(),
                xr: u(&f[1]), yr: u(&f[2]), xa: u(&f[3]), ya: u(&f[4]),
                xe: u(&f[5]), ye: u(&f[6]), raw: f,
            }
        })
        .collect()
}

#[test]
#[ignore]
fn q856_trusted_failure_inventory() {
    let packet = std::env::var("Q856_TRIAGE_OPS").unwrap_or_else(|_| "ops.bin".into());
    let corpus = std::env::var("Q856_TRIAGE_CORPUS").unwrap_or_else(|_| "Q856_REFERENCE_CORPUS.tsv".into());
    let output = std::env::var("Q856_TRIAGE_OUT").unwrap_or_else(|_| "Q856_TRUSTED_FAILURES.tsv".into());
    let ops = super::packet_io::load(&packet);
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    assert_eq!(ops.len(), 24_079_838);
    assert_eq!(nq, 856);
    assert_eq!(regs.len(), 4);

    let rows = corpus_rows(&corpus);
    assert_eq!(rows.len(), 9024);
    assert!(rows.iter().enumerate().all(|(i, row)| row.draw == i));

    let c = curve();
    let mut xof = fiat_shamir_seed(&ops);
    for row in &rows {
        let mut rb = [[0u8; 32]; 2];
        xof.read(&mut rb[0]);
        xof.read(&mut rb[1]);
        let t = c.mul(c.gx, c.gy, U256::from_le_bytes(rb[0]));
        let a = c.mul(c.gx, c.gy, U256::from_le_bytes(rb[1]));
        assert_eq!(t, (row.xr, row.yr), "scalar/RNG mismatch draw {} target", row.draw);
        assert_eq!(a, (row.xa, row.ya), "scalar/RNG mismatch draw {} addend", row.draw);
        assert_eq!(c.add(t.0, t.1, a.0, a.1), (row.xe, row.ye));
    }

    let logical_events: Vec<_> = ops
        .iter()
        .enumerate()
        .filter(|(_, op)| matches!(op.kind, K::Hmr | K::R))
        .collect();
    let hmr = logical_events.iter().filter(|(_, op)| op.kind == K::Hmr).count();
    let reset = logical_events.len() - hmr;
    let mut eh = sha3::Shake256::default();
    for &(i, op) in &logical_events {
        eh.update(&(i as u64).to_le_bytes());
        eh.update(&[op.kind as u8]);
        eh.update(&op.q_target.0.to_le_bytes());
        eh.update(&op.c_target.0.to_le_bytes());
    }
    let mut er = eh.finalize_xof();
    let mut event_hash = [0u8; 32];
    er.read(&mut event_hash);
    let event_hash = event_hash.iter().map(|b| format!("{b:02x}")).collect::<String>();

    let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
    let mut classical = vec![];
    let mut phase_rows = vec![];
    let mut anc_rows = vec![];
    for batch in 0..rows.len().div_ceil(64) {
        let bs = 64.min(rows.len() - batch * 64);
        let live_mask = if bs == 64 { u64::MAX } else { (1u64 << bs) - 1 };
        sim.clear_for_shot();
        for shot in 0..bs {
            let row = &rows[batch * 64 + shot];
            sim.set_register(&regs[0], row.xr, shot);
            sim.set_register(&regs[1], row.yr, shot);
            sim.set_register(&regs[2], row.xa, shot);
            sim.set_register(&regs[3], row.ya, shot);
        }
        sim.apply_iter(ops.iter());
        for shot in 0..bs {
            let i = batch * 64 + shot;
            let gx = sim.get_register(&regs[0], shot);
            let gy = sim.get_register(&regs[1], shot);
            if gx != rows[i].xe || gy != rows[i].ye {
                classical.push((i, gx, gy));
            }
        }
        let phase = sim.phase & live_mask;
        if phase != 0 {
            phase_rows.push((batch, phase));
        }
        for reg in &regs {
            for qb in reg {
                if let QubitOrBit::Qubit(q) = *qb { *sim.qubit_mut(q) = 0; }
            }
        }
        let mut anc_mask = 0u64;
        let mut first_q = None;
        let mut first_value = 0u64;
        for q in 0..nq {
            let value = sim.qubit(QubitId(q)) & live_mask;
            anc_mask |= value;
            if first_q.is_none() && value != 0 {
                first_q = Some(q);
                first_value = value;
            }
        }
        if anc_mask != 0 {
            anc_rows.push((batch, anc_mask, first_q.unwrap(), first_value));
        }
    }
    assert_eq!(classical.len(), 7);
    assert_eq!(phase_rows.len(), 2);
    assert_eq!(anc_rows.len(), 5);

    let mut out = String::from("kind\tindex_or_batch\tmask\tshots\tq\tvalue\tinput_xR\tinput_yR\tinput_xA\tinput_yA\tgot_x\tgot_y\texp_x\texp_y\n");
    for &(i, gx, gy) in &classical {
        let row = &rows[i];
        out.push_str(&format!(
            "classical\t{i}\t-\t{i}\t-\t-\t{}\t{}\t{}\t{}\t{gx:#x}\t{gy:#x}\t{:#x}\t{:#x}\n",
            row.raw[1], row.raw[2], row.raw[3], row.raw[4], row.xe, row.ye
        ));
    }
    for &(batch, mask) in &phase_rows {
        out.push_str(&format!("phase\t{batch}\t{mask:#018x}\t{}\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\n", indices(batch, mask)));
    }
    for &(batch, mask, q, value) in &anc_rows {
        out.push_str(&format!("ancilla\t{batch}\t{mask:#018x}\t{}\t{q}\t{value:#018x}\t-\t-\t-\t-\t-\t-\t-\t-\n", indices(batch, mask)));
    }
    std::fs::write(&output, out).unwrap();
    eprintln!(
        "Q856_TRIAGE corpus={} scalar_bytes={} batches={} events_per_batch={} hmr={} reset={} event_hash={} cls={:?} phase={:?} anc={:?} meanT={:.3}",
        rows.len(), rows.len() * 64, rows.len().div_ceil(64), logical_events.len(), hmr, reset, event_hash,
        classical.iter().map(|x| x.0).collect::<Vec<_>>(), phase_rows, anc_rows,
        sim.stats.toffoli_gates as f64 / rows.len() as f64,
    );
}

#[test]
#[ignore]
fn q856_raw_failure_witnesses() {
    let corpus = std::env::var("Q856_TRIAGE_CORPUS").unwrap_or_else(|_| "Q856_REFERENCE_CORPUS.tsv".into());
    let wanted = [3611usize, 3640, 3987, 5080, 7415, 8001, 8401];
    let all = corpus_rows(&corpus);
    let rows: Vec<_> = wanted.iter().map(|&i| all[i].clone()).collect();
    let ops = if let Ok(path) = std::env::var("Q856_RAW_OPS") {
        super::packet_io::load(&path)
    } else {
        let mut b = B::new();
        let _ = super::pointadd_lilypad::point_add(&mut b);
        std::mem::take(&mut b.ops)
    };
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let mut reports = vec![];
    for byte in [0u8, 0xff, 0xaa, 0x55, 0x0f, 0xf0, 0x33, 0xcc] {
        let mut fixed = Fixed(byte);
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut fixed);
        for (shot, row) in rows.iter().enumerate() {
            sim.set_register(&regs[0], row.xr, shot);
            sim.set_register(&regs[1], row.yr, shot);
            sim.set_register(&regs[2], row.xa, shot);
            sim.set_register(&regs[3], row.ya, shot);
        }
        sim.apply_iter(ops.iter());
        let mut cls = vec![];
        for (shot, row) in rows.iter().enumerate() {
            if sim.get_register(&regs[0], shot) != row.xe || sim.get_register(&regs[1], shot) != row.ye {
                cls.push(row.draw);
            }
        }
        let phase = sim.phase & ((1u64 << rows.len()) - 1);
        for reg in &regs {
            for qb in reg {
                if let QubitOrBit::Qubit(q) = *qb { *sim.qubit_mut(q) = 0; }
            }
        }
        let mut anc = 0u64;
        let mut first_q = None;
        for q in 0..nq {
            let value = sim.qubit(QubitId(q)) & ((1u64 << rows.len()) - 1);
            anc |= value;
            if first_q.is_none() && value != 0 { first_q = Some((q, value)); }
        }
        reports.push((byte, cls.clone(), phase, anc, first_q));
        eprintln!("Q856_RAW_WITNESS HMR={byte:#04x} cls={cls:?} phase={phase:#04x} anc={anc:#04x} first_q={first_q:?}");
    }
    let tag = std::env::var("Q856_TRIAGE_TAG").unwrap_or_else(|_| "candidate".into());
    let mut out = String::from("tag\thmr\tclassical\tphase_mask\tancilla_mask\tfirst_q\tfirst_value\n");
    for (byte, cls, phase, anc, first) in reports {
        let (q, value) = first.map_or((u64::MAX, 0), |x| x);
        out.push_str(&format!("{tag}\t{byte:#04x}\t{:?}\t{phase:#04x}\t{anc:#04x}\t{q}\t{value:#04x}\n", cls));
    }
    std::fs::write(format!("Q856_RAW_WITNESSES_{tag}.tsv"), out).unwrap();
}

#[test]
#[ignore]
fn q856_write_nonce_packet() {
    let base = std::env::var("Q856_PILOT_BASE").unwrap_or_else(|_| "ops.bin".into());
    let output = std::env::var("Q856_PILOT_PACKET").expect("Q856_PILOT_PACKET");
    let nonce: u64 = std::env::var("Q856_PILOT_NONCE").expect("Q856_PILOT_NONCE").parse().unwrap();
    assert!(nonce < 1u64 << 48);
    let mut ops = super::packet_io::load(&base);
    let tail = ops.len() - 96;
    for bit in 0..48usize {
        let q = QubitId((nonce >> bit) & 1);
        let pair = &mut ops[tail + 2 * bit..tail + 2 * bit + 2];
        assert!(pair.iter().all(|op| op.kind == K::X));
        assert_eq!(pair[0].q_target, pair[1].q_target);
        pair[0].q_target = q;
        pair[1].q_target = q;
    }
    super::packet_io::write(&ops, &output);
    eprintln!("Q856_NONCE_PACKET nonce={nonce} ops={} output={output}", ops.len());
}
