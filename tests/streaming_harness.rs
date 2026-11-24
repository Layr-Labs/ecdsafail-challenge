use quantum_ecc::circuit::{
    analyze_ops, BitId, Op, OperationType, OpsAnalyzer, QubitId, QubitOrBit, RegisterId, NO_BIT,
    NO_QUBIT, NO_REG,
};
use quantum_ecc::eval_stream::{
    compute_wave_plan, fanout_chunks, generate_test_points, pass1_validate_and_hash,
    run_tests_streaming, secp256k1, validate_registers, MAX_SIM_STATE_BYTES, MIN_SIM_STATE_BYTES,
};
use quantum_ecc::ops_io::{
    clean_stale_ops, finalize_build_output, reset_stream_started, take_stream_started,
    tmp_path_for, OpsReader, OpsWriter, DEFAULT_ZSTD_LEVEL, MAGIC, MAX_OPS, OP_BYTES,
};
use quantum_ecc::sim::{SimExecState, Simulator};
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{mpsc, Mutex};
use std::time::Duration;

static STREAM_FLAG_LOCK: Mutex<()> = Mutex::new(());
static TEST_DIR_COUNTER: AtomicU64 = AtomicU64::new(0);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> Self {
        let id = TEST_DIR_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let path = std::env::temp_dir().join(format!("ecdsafail-test-{prefix}-{pid}-{id}"));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("create temp dir");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn encode_op_record(op: &Op) -> [u8; OP_BYTES] {
    let mut rec = [0u8; OP_BYTES];
    rec[0..4].copy_from_slice(&(op.kind as u32).to_le_bytes());
    rec[8..16].copy_from_slice(&op.q_control2.0.to_le_bytes());
    rec[16..24].copy_from_slice(&op.q_control1.0.to_le_bytes());
    rec[24..32].copy_from_slice(&op.q_target.0.to_le_bytes());
    rec[32..40].copy_from_slice(&op.c_target.0.to_le_bytes());
    rec[40..48].copy_from_slice(&op.c_condition.0.to_le_bytes());
    rec[48..56].copy_from_slice(&op.r_target.0.to_le_bytes());
    rec
}

fn write_legacy_ref(ops: &[Op], path: &Path) {
    let mut w = BufWriter::new(File::create(path).expect("create legacy ref"));
    w.write_all(MAGIC).unwrap();
    w.write_all(&(ops.len() as u64).to_le_bytes()).unwrap();
    let mut enc = zstd::stream::write::Encoder::new(w, DEFAULT_ZSTD_LEVEL).unwrap();
    for op in ops {
        enc.write_all(&encode_op_record(op)).unwrap();
    }
    let mut w = enc.finish().unwrap();
    w.flush().unwrap();
}

fn sample_valid_ops(count: usize) -> Vec<Op> {
    let mut ops = Vec::with_capacity(count);
    for i in 0..count {
        let op = match i % 5 {
            0 => {
                let mut o = mk_op(OperationType::X);
                o.q_target = QubitId((i % 16) as u64);
                o
            }
            1 => {
                let mut o = mk_op(OperationType::CX);
                o.q_control1 = QubitId((i % 8) as u64);
                o.q_target = QubitId(8 + (i % 8) as u64);
                o
            }
            2 => {
                let mut o = mk_op(OperationType::CCX);
                o.q_control2 = QubitId(0);
                o.q_control1 = QubitId(1);
                o.q_target = QubitId(2 + (i % 10) as u64);
                o
            }
            3 => {
                let mut o = mk_op(OperationType::Hmr);
                o.q_target = QubitId((i % 16) as u64);
                o.c_target = BitId((i % 8) as u64);
                o
            }
            _ => {
                let mut o = mk_op(OperationType::R);
                o.q_target = QubitId((i % 16) as u64);
                o
            }
        };
        ops.push(op);
    }
    ops
}

fn mk_op(kind: OperationType) -> Op {
    let mut op = Op::empty();
    op.kind = kind;
    op
}

#[test]
fn op_try_validate_accepts_valid_and_rejects_aliasing_and_bad_shape() {
    let mut ccx = mk_op(OperationType::CCX);
    ccx.q_control2 = QubitId(0);
    ccx.q_control1 = QubitId(1);
    ccx.q_target = QubitId(2);
    assert!(ccx.try_validate().is_ok());

    let mut hmr = mk_op(OperationType::Hmr);
    hmr.q_target = QubitId(3);
    hmr.c_target = BitId(1);
    assert!(hmr.try_validate().is_ok());

    let mut r = mk_op(OperationType::R);
    r.q_target = QubitId(4);
    assert!(r.try_validate().is_ok());

    let mut push = mk_op(OperationType::PushCondition);
    push.c_condition = BitId(2);
    assert!(push.try_validate().is_ok());

    let mut append_q = mk_op(OperationType::AppendToRegister);
    append_q.r_target = RegisterId(0);
    append_q.q_target = QubitId(5);
    assert!(append_q.try_validate().is_ok());

    // Aliasing: CCX q1 q1 q2
    let mut aliased = ccx;
    aliased.q_control2 = QubitId(1);
    aliased.q_control1 = QubitId(1);
    assert!(aliased.try_validate().is_err());

    // Missing required operand: CCX with q_control2 == NO_QUBIT
    let mut missing_c2 = ccx;
    missing_c2.q_control2 = NO_QUBIT;
    assert!(missing_c2.try_validate().is_err());

    // Bad shape: PushCondition with c_condition == NO_BIT
    let mut bad_push = mk_op(OperationType::PushCondition);
    bad_push.c_condition = NO_BIT;
    assert!(bad_push.try_validate().is_err());

    // Bad shape: AppendToRegister with both qubit and bit set
    let mut bad_append = append_q;
    bad_append.c_target = BitId(0);
    assert!(bad_append.try_validate().is_err());
}

#[test]
fn ops_analyzer_matches_analyze_ops_and_caps_registers() {
    let mut ops = Vec::new();
    for r in 0..4u64 {
        let mut reg = mk_op(OperationType::Register);
        reg.r_target = RegisterId(r);
        ops.push(reg);
    }
    let mut app0 = mk_op(OperationType::AppendToRegister);
    app0.r_target = RegisterId(0);
    app0.q_target = QubitId(7);
    ops.push(app0);

    let mut app2 = mk_op(OperationType::AppendToRegister);
    app2.r_target = RegisterId(2);
    app2.c_target = BitId(11);
    ops.push(app2);

    let mut ccx = mk_op(OperationType::CCX);
    ccx.q_control2 = QubitId(1);
    ccx.q_control1 = QubitId(2);
    ccx.q_target = QubitId(9);
    ccx.c_condition = BitId(15);
    ops.push(ccx);

    let expected = analyze_ops(ops.iter());
    let mut analyzer = OpsAnalyzer::new();
    for op in &ops {
        analyzer.observe(op).expect("valid op");
    }
    let actual = analyzer.finish();
    assert_eq!(actual, expected);
    assert_eq!(actual.0, 10);
    assert_eq!(actual.1, 16);
    assert_eq!(actual.2, 4);
    assert_eq!(actual.3[0], vec![QubitOrBit::Qubit(QubitId(7))]);
    assert_eq!(actual.3[2], vec![QubitOrBit::Bit(BitId(11))]);

    // OpsAnalyzer rejects r_target >= MAX_REGISTERS
    let mut big_reg = mk_op(OperationType::Register);
    big_reg.r_target = RegisterId(OpsAnalyzer::MAX_REGISTERS);
    let mut capped = OpsAnalyzer::new();
    assert!(capped.observe(&big_reg).is_err());

    // Legacy analyze_ops remains unchanged and accepts r_target = 2000 without panicking
    let mut legacy_reg = mk_op(OperationType::Register);
    legacy_reg.r_target = RegisterId(2000);
    let (_q, _b, num_regs, regs) = analyze_ops(std::iter::once(&legacy_reg));
    assert_eq!(num_regs, 2001);
    assert_eq!(regs.len(), 2001);
    let _ = NO_REG;
}

#[test]
fn apply_chunk_preserves_nested_condition_stack_across_arbitrary_splits() {
    let mut ops = Vec::new();

    let mut push0 = mk_op(OperationType::PushCondition);
    push0.c_condition = BitId(0);
    ops.push(push0);

    let mut x0 = mk_op(OperationType::X);
    x0.q_target = QubitId(0);
    ops.push(x0);

    let mut push1 = mk_op(OperationType::PushCondition);
    push1.c_condition = BitId(1);
    ops.push(push1);

    let mut ccx = mk_op(OperationType::CCX);
    ccx.q_control2 = QubitId(0);
    ccx.q_control1 = QubitId(1);
    ccx.q_target = QubitId(2);
    ccx.c_condition = BitId(2);
    ops.push(ccx);

    let mut push2 = mk_op(OperationType::PushCondition);
    push2.c_condition = BitId(2);
    ops.push(push2);

    let mut hmr = mk_op(OperationType::Hmr);
    hmr.q_target = QubitId(2);
    hmr.c_target = BitId(3);
    ops.push(hmr);

    let mut cz = mk_op(OperationType::CZ);
    cz.q_control1 = QubitId(0);
    cz.q_target = QubitId(1);
    cz.c_condition = BitId(3);
    ops.push(cz);

    let mut swp = mk_op(OperationType::Swap);
    swp.q_control1 = QubitId(1);
    swp.q_target = QubitId(3);
    ops.push(swp);

    let mut r_op = mk_op(OperationType::R);
    r_op.q_target = QubitId(3);
    ops.push(r_op);

    let mut b_inv = mk_op(OperationType::BitInvert);
    b_inv.c_target = BitId(4);
    ops.push(b_inv);

    let mut b_s1 = mk_op(OperationType::BitStore1);
    b_s1.c_target = BitId(5);
    ops.push(b_s1);

    let mut b_s0 = mk_op(OperationType::BitStore0);
    b_s0.c_target = BitId(4);
    ops.push(b_s0);

    let mut neg = mk_op(OperationType::Neg);
    neg.c_condition = BitId(3);
    ops.push(neg);

    ops.push(mk_op(OperationType::PopCondition));

    let mut cx = mk_op(OperationType::CX);
    cx.q_control1 = QubitId(0);
    cx.q_target = QubitId(1);
    ops.push(cx);

    ops.push(mk_op(OperationType::PopCondition));

    let mut z = mk_op(OperationType::Z);
    z.q_target = QubitId(1);
    ops.push(z);

    ops.push(mk_op(OperationType::PopCondition));

    let mut hasher = Shake256::default();
    hasher.update(b"apply-chunk-test-seed");
    let base_xof = hasher.finalize_xof();

    let init_qubits = vec![
        0xF0F0_0F0F_AAAA_5555u64,
        0x3333_CCCC_1234_5678u64,
        0xDEAD_BEEF_CAFE_BABEu64,
        0x0123_4567_89AB_CDEFu64,
    ];
    let init_bits = vec![
        0xFFFF_0000_FFFF_0000u64,
        0x0F0F_F0F0_0F0F_F0F0u64,
        0x5555_5555_AAAA_AAAAu64,
        0,
        0x1111_2222_3333_4444u64,
        0,
    ];

    let mut xof_ref = base_xof.clone();
    let mut sim_ref = Simulator::new(4, 6, &mut xof_ref);
    sim_ref.qubits = init_qubits.clone();
    sim_ref.bits = init_bits.clone();
    sim_ref.apply_iter(ops.iter());

    for chunk_size in [1usize, 2, 3, 7, ops.len()] {
        let mut xof_c = base_xof.clone();
        let mut sim_c = Simulator::new(4, 6, &mut xof_c);
        sim_c.qubits = init_qubits.clone();
        sim_c.bits = init_bits.clone();
        let mut state = SimExecState::new();
        for chunk in ops.chunks(chunk_size) {
            sim_c.apply_chunk(&mut state, chunk.iter());
        }
        assert_eq!(sim_c.qubits, sim_ref.qubits, "chunk_size={chunk_size}");
        assert_eq!(sim_c.bits, sim_ref.bits, "chunk_size={chunk_size}");
        assert_eq!(sim_c.phase, sim_ref.phase, "chunk_size={chunk_size}");
        assert_eq!(sim_c.stats, sim_ref.stats, "chunk_size={chunk_size}");
    }
}

#[test]
fn ops_writer_byte_identical_to_legacy_framing() {
    let dir = TempDir::new("writer-parity");
    let ops = sample_valid_ops(512);
    let legacy_path = dir.path().join("legacy.bin");
    let stream_path = dir.path().join("stream.bin");

    write_legacy_ref(&ops, &legacy_path);

    let mut w = OpsWriter::create(&stream_path).expect("create OpsWriter");
    for op in &ops {
        w.push(op).expect("push op");
    }
    let summary = w.finish().expect("finish OpsWriter");
    assert_eq!(summary.count, ops.len() as u64);

    let legacy_bytes = fs::read(&legacy_path).unwrap();
    let stream_bytes = fs::read(&stream_path).unwrap();
    assert_eq!(stream_bytes, legacy_bytes);
    assert_eq!(summary.on_disk_bytes, stream_bytes.len() as u64);
}

#[test]
fn ops_writer_enforces_max_ops_via_injectable_limit() {
    let dir = TempDir::new("writer-cap");
    let path = dir.path().join("capped.bin");
    let ops = sample_valid_ops(6);

    let mut w = OpsWriter::create_with_max_ops(&path, 5).expect("create capped writer");
    for op in &ops[..5] {
        w.push(op).expect("push within cap");
    }
    assert_eq!(w.count(), 5);
    assert!(w.push(&ops[5]).is_err());
    assert_eq!(w.count(), 5);
    let summary = w.finish().expect("finish after cap hit");
    assert_eq!(summary.count, 5);
}

#[test]
fn ops_writer_drop_without_finish_removes_tmp_and_sets_stream_started_only_for_ops_bin() {
    let _guard = STREAM_FLAG_LOCK.lock().unwrap();
    let dir = TempDir::new("writer-flag");
    let ops = sample_valid_ops(10);

    reset_stream_started();
    let side_path = dir.path().join("side.bin");
    {
        let mut w = OpsWriter::create(&side_path).expect("create side writer");
        for op in &ops {
            w.push(op).unwrap();
        }
    }
    assert!(!side_path.exists());
    assert!(!tmp_path_for(&side_path).exists());
    assert!(!take_stream_started(), "side file must not set STREAM_STARTED");

    let ops_path = dir.path().join("ops.bin");
    {
        let mut w = OpsWriter::create(&ops_path).expect("create ops.bin writer");
        for op in &ops {
            w.push(op).unwrap();
        }
    }
    assert!(!ops_path.exists());
    assert!(!tmp_path_for(&ops_path).exists());
    assert!(take_stream_started(), "ops.bin writer must set STREAM_STARTED");
    assert!(!take_stream_started(), "take_stream_started clears the flag");
}

#[test]
fn ops_reader_roundtrip_and_fd_rewind() {
    let dir = TempDir::new("reader-roundtrip");
    let path = dir.path().join("roundtrip.bin");
    let ops = sample_valid_ops(1000);

    let mut w = OpsWriter::create(&path).unwrap();
    w.extend(ops.iter().copied()).unwrap();
    w.finish().unwrap();

    let mut file_and_digest = None;
    for chunk_size in [1usize, 13, 256, 1000, 10_000] {
        let mut reader = match file_and_digest.take() {
            None => OpsReader::open(&path).expect("open reader"),
            Some((f, _)) => OpsReader::from_file(f).expect("rewind reader"),
        };
        assert_eq!(reader.total_ops(), ops.len() as u64);
        let mut read_back = Vec::new();
        let mut buf = Vec::new();
        loop {
            let n = reader.read_chunk(&mut buf, chunk_size, true).expect("read chunk");
            if n == 0 {
                break;
            }
            read_back.extend_from_slice(&buf);
        }
        assert_eq!(read_back, ops, "chunk_size={chunk_size}");
        let (f, digest) = reader.into_file_and_digest().expect("finalize digest");
        if let Some((_, prev_digest)) = &file_and_digest {
            assert_eq!(&digest, prev_digest);
        }
        file_and_digest = Some((f, digest));
    }

    // Also check exact-match digest across two independent passes and 0-op file
    let (f, d1) = file_and_digest.unwrap();
    let mut r2 = OpsReader::from_file(f).unwrap();
    let mut buf = Vec::new();
    let n = r2.read_chunk(&mut buf, ops.len(), true).unwrap();
    assert_eq!(n, ops.len());
    let (_, d2) = r2.into_file_and_digest().unwrap();
    assert_eq!(d1, d2);

    // 0-op stream
    let empty_path = dir.path().join("empty.bin");
    OpsWriter::create(&empty_path).unwrap().finish().unwrap();
    let mut r_empty = OpsReader::open(&empty_path).unwrap();
    assert_eq!(r_empty.total_ops(), 0);
    assert_eq!(r_empty.read_chunk(&mut buf, 64, true).unwrap(), 0);
    assert!(r_empty.into_file_and_digest().is_ok());
}

#[test]
fn ops_reader_rejects_malformed_inputs() {
    let dir = TempDir::new("reader-malformed");

    // 1. Bad magic
    let bad_magic = dir.path().join("bad_magic.bin");
    fs::write(&bad_magic, b"BADMAGIC\x00\x00\x00\x00\x00\x00\x00\x00").unwrap();
    assert!(OpsReader::open(&bad_magic).is_err());

    // 2. Forged header count = MAX_OPS + 1
    let too_many = dir.path().join("too_many.bin");
    let mut hdr = Vec::new();
    hdr.extend_from_slice(MAGIC);
    hdr.extend_from_slice(&(MAX_OPS + 1).to_le_bytes());
    fs::write(&too_many, &hdr).unwrap();
    assert!(OpsReader::open(&too_many).is_err());

    // Helper to write raw header + zstd-compressed raw records
    let write_raw = |name: &str, claimed_n: u64, raw_recs: &[[u8; OP_BYTES]]| -> PathBuf {
        let p = dir.path().join(name);
        let mut w = BufWriter::new(File::create(&p).unwrap());
        w.write_all(MAGIC).unwrap();
        w.write_all(&claimed_n.to_le_bytes()).unwrap();
        let mut enc = zstd::stream::write::Encoder::new(w, 1).unwrap();
        for r in raw_recs {
            enc.write_all(r).unwrap();
        }
        enc.finish().unwrap().flush().unwrap();
        p
    };

    // 3. Invalid kind (18 and u32::MAX)
    for bad_kind in [18u32, u32::MAX] {
        let mut rec = [0u8; OP_BYTES];
        rec[0..4].copy_from_slice(&bad_kind.to_le_bytes());
        let p = write_raw(&format!("bad_kind_{bad_kind}.bin"), 1, &[rec]);
        let mut r = OpsReader::open(&p).unwrap();
        let mut buf = Vec::new();
        assert!(r.read_chunk(&mut buf, 16, true).is_err());
    }

    // 4. Aliased CCX (q0 q0 q1)
    let mut aliased = mk_op(OperationType::CCX);
    aliased.q_control2 = QubitId(0);
    aliased.q_control1 = QubitId(0);
    aliased.q_target = QubitId(1);
    let p_alias = write_raw("aliased.bin", 1, &[encode_op_record(&aliased)]);
    let mut r = OpsReader::open(&p_alias).unwrap();
    let mut buf = Vec::new();
    assert!(r.read_chunk(&mut buf, 16, true).is_err());

    // 5. Missing required operand: CCX with q_control2 == NO_QUBIT
    let mut missing = mk_op(OperationType::CCX);
    missing.q_control2 = NO_QUBIT;
    missing.q_control1 = QubitId(0);
    missing.q_target = QubitId(1);
    let p_missing = write_raw("missing_op.bin", 1, &[encode_op_record(&missing)]);
    let mut r = OpsReader::open(&p_missing).unwrap();
    assert!(r.read_chunk(&mut buf, 16, true).is_err());

    // 6. Truncated body (header claims 10, body has 5)
    let valid5: Vec<[u8; OP_BYTES]> = sample_valid_ops(5).iter().map(encode_op_record).collect();
    let p_trunc = write_raw("trunc.bin", 10, &valid5);
    let mut r = OpsReader::open(&p_trunc).unwrap();
    assert!(r.read_chunk(&mut buf, 16, true).is_err());

    // 7. Trailing decompressed bytes (header claims 5, body has 6)
    let valid6: Vec<[u8; OP_BYTES]> = sample_valid_ops(6).iter().map(encode_op_record).collect();
    let p_trail = write_raw("trailing.bin", 5, &valid6);
    let mut r = OpsReader::open(&p_trail).unwrap();
    assert!(r.read_chunk(&mut buf, 16, true).is_err());
}

#[test]
fn finalize_build_output_legacy_nonempty() {
    let dir = TempDir::new("finalize-case-a");
    let path = dir.path().join("out.bin");
    let ops = sample_valid_ops(25);
    let summary = finalize_build_output(&ops, &path, false).expect("Case A succeeds");
    assert_eq!(summary.count, 25);
    assert!(path.exists());
    let mut r = OpsReader::open(&path).unwrap();
    let mut buf = Vec::new();
    assert_eq!(r.read_chunk(&mut buf, 64, true).unwrap(), 25);
    assert_eq!(buf, ops);
}

#[test]
fn finalize_build_output_streamed_empty_vec_cleans_leftover_tmp() {
    let dir = TempDir::new("finalize-case-b");
    let path = dir.path().join("out.bin");
    let ops = sample_valid_ops(30);
    let mut w = OpsWriter::create(&path).unwrap();
    w.extend(ops).unwrap();
    w.finish().unwrap();

    // Plant an unexpected leftover tmp file; Case B must clean it.
    let tmp = tmp_path_for(&path);
    fs::write(&tmp, b"stale tmp").unwrap();
    assert!(tmp.exists());

    let summary = finalize_build_output(&[], &path, true).expect("Case B succeeds");
    assert_eq!(summary.count, 30);
    assert!(path.exists());
    assert!(!tmp.exists(), "Case B must clean leftover .bin.tmp");
}

#[test]
fn finalize_build_output_empty_vec_no_stream_writes_zero_ops() {
    let dir = TempDir::new("finalize-case-c-empty");
    let path = dir.path().join("out.bin");
    let summary = finalize_build_output(&[], &path, false).expect("Case C empty succeeds");
    assert_eq!(summary.count, 0);
    assert!(path.exists());
    let r = OpsReader::open(&path).unwrap();
    assert_eq!(r.total_ops(), 0);
}

#[test]
fn finalize_build_output_forgotten_finish_after_drop_fails_loudly() {
    let dir = TempDir::new("finalize-case-c-dropped");
    let path = dir.path().join("out.bin");
    // Simulates OpsWriter dropped without finish(): Drop removed .bin.tmp, stream_started=true.
    let err = finalize_build_output(&[], &path, true).expect_err("must fail loudly");
    assert!(err.contains("finish()"), "unexpected error: {err}");
    assert!(!path.exists());
}

#[test]
fn finalize_build_output_leftover_tmp_fails_loudly() {
    let dir = TempDir::new("finalize-case-c-tmp");
    let path = dir.path().join("out.bin");
    let tmp = tmp_path_for(&path);
    fs::write(&tmp, b"partial").unwrap();
    let err = finalize_build_output(&[], &path, false).expect_err("must fail on leftover tmp");
    assert!(err.contains("finish()"), "unexpected error: {err}");
    assert!(!path.exists());
    assert!(!tmp.exists(), "must clean up leftover tmp on error");
}

#[test]
fn finalize_build_output_conflict_deletes_file_and_errors() {
    let dir = TempDir::new("finalize-case-d");
    let path = dir.path().join("out.bin");
    let ops = sample_valid_ops(12);
    let mut w = OpsWriter::create(&path).unwrap();
    w.extend(ops.iter().copied()).unwrap();
    w.finish().unwrap();

    let err = finalize_build_output(&ops, &path, true).expect_err("Case D conflict must fail");
    assert!(err.contains("both wrote"), "unexpected error: {err}");
    assert!(!path.exists(), "Case D must delete ops file to fail closed");
}

#[test]
fn clean_stale_ops_removes_old_ops_and_tmp() {
    let dir = TempDir::new("clean-stale");
    let path = dir.path().join("out.bin");
    let tmp = tmp_path_for(&path);
    fs::write(&path, b"old ops").unwrap();
    fs::write(&tmp, b"old tmp").unwrap();
    clean_stale_ops(&path).expect("clean stale ops");
    assert!(!path.exists());
    assert!(!tmp.exists());
    // Calling again when neither exists must also succeed.
    clean_stale_ops(&path).expect("clean stale ops idempotent");
}

fn build_synthetic_4reg_circuit() -> Vec<Op> {
    let mut ops = Vec::new();
    for r in 0..4u64 {
        let mut reg = mk_op(OperationType::Register);
        reg.r_target = RegisterId(r);
        ops.push(reg);
    }
    for i in 0..256u64 {
        let mut a0 = mk_op(OperationType::AppendToRegister);
        a0.r_target = RegisterId(0);
        a0.q_target = QubitId(i);
        ops.push(a0);

        let mut a1 = mk_op(OperationType::AppendToRegister);
        a1.r_target = RegisterId(1);
        a1.q_target = QubitId(256 + i);
        ops.push(a1);

        let mut a2 = mk_op(OperationType::AppendToRegister);
        a2.r_target = RegisterId(2);
        a2.c_target = BitId(i);
        ops.push(a2);

        let mut a3 = mk_op(OperationType::AppendToRegister);
        a3.r_target = RegisterId(3);
        a3.c_target = BitId(256 + i);
        ops.push(a3);
    }

    // Add nested conditions, CCX, CX, CZ, X, Z, Hmr, R on ancillas & registers.
    let anc0 = QubitId(512);
    let anc1 = QubitId(513);
    let scratch_b0 = BitId(512);
    let scratch_b1 = BitId(513);

    for step in 0..8u64 {
        let mut p1 = mk_op(OperationType::PushCondition);
        p1.c_condition = BitId(step);
        ops.push(p1);

        let mut x = mk_op(OperationType::X);
        x.q_target = anc0;
        ops.push(x);

        let mut p2 = mk_op(OperationType::PushCondition);
        p2.c_condition = BitId(256 + step);
        ops.push(p2);

        let mut ccx = mk_op(OperationType::CCX);
        ccx.q_control2 = QubitId(step);
        ccx.q_control1 = anc0;
        ccx.q_target = anc1;
        ops.push(ccx);

        let mut cx = mk_op(OperationType::CX);
        cx.q_control1 = anc1;
        cx.q_target = QubitId(256 + step);
        ops.push(cx);

        let mut hmr = mk_op(OperationType::Hmr);
        hmr.q_target = anc1;
        hmr.c_target = scratch_b0;
        ops.push(hmr);

        let mut cz = mk_op(OperationType::CZ);
        cz.q_control1 = QubitId(step);
        cz.q_target = anc0;
        cz.c_condition = scratch_b0;
        ops.push(cz);

        let mut r_op = mk_op(OperationType::R);
        r_op.q_target = anc0;
        ops.push(r_op);

        let mut b_inv = mk_op(OperationType::BitInvert);
        b_inv.c_target = scratch_b1;
        ops.push(b_inv);

        ops.push(mk_op(OperationType::PopCondition));
        ops.push(mk_op(OperationType::PopCondition));
    }

    ops
}

fn ref_fiat_shamir(ops: &[Op]) -> sha3::Shake256Reader {
    let mut hasher = Shake256::default();
    hasher.update(b"quantum_ecc-fiat-shamir-v2");
    hasher.update(&(ops.len() as u64).to_le_bytes());
    for op in ops {
        hasher.update(&[op.kind as u8]);
        hasher.update(&op.q_control2.0.to_le_bytes());
        hasher.update(&op.q_control1.0.to_le_bytes());
        hasher.update(&op.q_target.0.to_le_bytes());
        hasher.update(&op.c_target.0.to_le_bytes());
        hasher.update(&op.c_condition.0.to_le_bytes());
        hasher.update(&op.r_target.0.to_le_bytes());
    }
    hasher.finalize_xof()
}

fn ref_eval_sequential(ops: &[Op], target_shots: usize) -> quantum_ecc::eval_stream::SeedReport {
    let (total_qubits, num_bits, _nr, layout_regs) = analyze_ops(ops.iter());
    let mut xof = ref_fiat_shamir(ops);
    let curve = secp256k1();

    let mut targets = Vec::with_capacity(target_shots);
    let mut offsets = Vec::with_capacity(target_shots);
    let mut expected = Vec::with_capacity(target_shots);
    for _ in 0..target_shots {
        let mut rb = [[0u8; 32]; 2];
        XofReader::read(&mut xof, &mut rb[0]);
        XofReader::read(&mut xof, &mut rb[1]);
        let k1 = alloy_primitives::U256::from_le_bytes(rb[0]);
        let k2 = alloy_primitives::U256::from_le_bytes(rb[1]);
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        if t.0 == o.0
            || (t.0.is_zero() && t.1.is_zero())
            || (o.0.is_zero() && o.1.is_zero())
        {
            continue;
        }
        let e = curve.add(t.0, t.1, o.0, o.1);
        targets.push(t);
        offsets.push(o);
        expected.push(e);
    }
    let n = targets.len();
    let mut sim = Simulator::new(total_qubits as usize, num_bits as usize, &mut xof);
    let mut ok = true;
    let mut fail_reason: Option<String> = None;
    let mut classical_failures = 0usize;
    let mut phase_garbage_batches = 0usize;
    let mut ancilla_garbage_batches = 0usize;

    const BATCH: usize = 64;
    let num_batches = n.div_ceil(BATCH);
    for batch in 0..num_batches {
        let bs = BATCH.min(n - batch * BATCH);
        let cond_mask: u64 = if bs == 64 { u64::MAX } else { (1u64 << bs) - 1 };

        sim.clear_for_shot();
        for shot in 0..bs {
            let i = batch * BATCH + shot;
            sim.set_register(&layout_regs[0], targets[i].0, shot);
            sim.set_register(&layout_regs[1], targets[i].1, shot);
            sim.set_register(&layout_regs[2], offsets[i].0, shot);
            sim.set_register(&layout_regs[3], offsets[i].1, shot);
        }

        sim.apply_iter(ops.iter());

        for shot in 0..bs {
            let i = batch * BATCH + shot;
            let gx = sim.get_register(&layout_regs[0], shot);
            let gy = sim.get_register(&layout_regs[1], shot);
            if gx != expected[i].0 || gy != expected[i].1 {
                classical_failures += 1;
                if fail_reason.is_none() {
                    fail_reason = Some(format!(
                        "CLASSICAL MISMATCH shot {i}: got ({:#x},{:#x}) exp ({:#x},{:#x})",
                        gx, gy, expected[i].0, expected[i].1
                    ));
                }
                ok = false;
            }
        }

        let phase = sim.phase & cond_mask;
        if phase != 0 {
            phase_garbage_batches += 1;
            let msg = format!(
                "PHASE GARBAGE: global_phase = {:#018x} across {} live shots (must be 0)",
                phase, bs
            );
            if fail_reason.is_none() {
                fail_reason = Some(msg);
            }
            ok = false;
        }

        for register in &layout_regs {
            for qb in register {
                if let QubitOrBit::Qubit(q) = *qb {
                    *sim.qubit_mut(q) = 0;
                }
            }
        }
        let mut garbage_q: Option<u64> = None;
        for q in 0..total_qubits {
            let v = sim.qubit(QubitId(q)) & cond_mask;
            if v != 0 {
                garbage_q = Some(q);
                break;
            }
        }
        if let Some(q) = garbage_q {
            ancilla_garbage_batches += 1;
            let v = sim.qubit(QubitId(q)) & cond_mask;
            let msg = format!(
                "ANCILLA GARBAGE: qubit {} = {:#018x} (live shots) at end of forward; \
                 every non-register qubit must be |0⟩ on every live shot",
                q, v
            );
            if fail_reason.is_none() {
                fail_reason = Some(msg);
            }
            ok = false;
        }
    }

    let denom = n.max(1) as f64;
    quantum_ecc::eval_stream::SeedReport {
        ok,
        avg_cliff: sim.stats.clifford_gates as f64 / denom,
        avg_tof: sim.stats.toffoli_gates as f64 / denom,
        tot_tof: sim.stats.toffoli_gates,
        tot_cliff: sim.stats.clifford_gates,
        n_shots: n,
        classical_failures,
        phase_garbage_batches,
        ancilla_garbage_batches,
        fail_reason,
    }
}

#[test]
fn streaming_eval_matches_reference_sequential_eval_bit_for_bit() {
    let dir = TempDir::new("eval-parity");
    let path = dir.path().join("circuit.bin");
    let ops = build_synthetic_4reg_circuit();
    let mut w = OpsWriter::create(&path).unwrap();
    w.extend(ops.iter().copied()).unwrap();
    w.finish().unwrap();

    // 1. Small shot count with tiny chunk_ops & multi-wave fallback
    let target_shots_small = 200;
    let ref_small = ref_eval_sequential(&ops, target_shots_small);
    for (chunk_ops, wave_size, workers) in [(7, 10, 4), (7, 2, 4), (1024, 1, 1), (13, 3, 3)] {
        let (summary, mut xof, file) = pass1_validate_and_hash(&path).expect("pass1");
        validate_registers(&summary.regs).expect("valid regs");
        let points = generate_test_points(&mut xof, target_shots_small, 4);
        let got = run_tests_streaming(file, &summary, &points, &mut xof, chunk_ops, wave_size, workers)
            .expect("pass2");
        assert_eq!(got.ok, ref_small.ok);
        assert_eq!(got.tot_tof, ref_small.tot_tof);
        assert_eq!(got.tot_cliff, ref_small.tot_cliff);
        assert_eq!(got.avg_tof, ref_small.avg_tof);
        assert_eq!(got.avg_cliff, ref_small.avg_cliff);
        assert_eq!(got.n_shots, ref_small.n_shots);
        assert_eq!(got.classical_failures, ref_small.classical_failures);
        assert_eq!(got.phase_garbage_batches, ref_small.phase_garbage_batches);
        assert_eq!(got.ancilla_garbage_batches, ref_small.ancilla_garbage_batches);
        assert_eq!(got.fail_reason, ref_small.fail_reason);
    }

    // 2. Test non-dividing worker counts (31, 8, 140) on 141 synthetic batches
    //    without spending time on 9,024 EC multiplications: clone 1 batch of points 141x.
    let (summary, mut xof_base, _file) = pass1_validate_and_hash(&path).expect("pass1");
    let seed_points = generate_test_points(&mut xof_base, 64, 4);
    let mut targets_141 = Vec::with_capacity(141 * 64);
    let mut offsets_141 = Vec::with_capacity(141 * 64);
    let mut expected_141 = Vec::with_capacity(141 * 64);
    for _ in 0..141 {
        targets_141.extend_from_slice(&seed_points.targets);
        offsets_141.extend_from_slice(&seed_points.offsets);
        expected_141.extend_from_slice(&seed_points.expected);
    }
    let points_141 = quantum_ecc::eval_stream::TestPoints {
        targets: targets_141,
        offsets: offsets_141,
        expected: expected_141,
    };

    let mut xof_ref = xof_base.clone();
    let f_ref = File::open(&path).unwrap();
    let baseline = run_tests_streaming(f_ref, &summary, &points_141, &mut xof_ref, 37, 141, 1)
        .expect("1-worker 141-batch baseline");
    for workers in [8usize, 31, 140] {
        let mut xof_w = xof_base.clone();
        let f_w = File::open(&path).unwrap();
        let got = run_tests_streaming(f_w, &summary, &points_141, &mut xof_w, 37, 141, workers)
            .expect("non-dividing worker run");
        assert_eq!(got.tot_tof, baseline.tot_tof, "workers={workers}");
        assert_eq!(got.tot_cliff, baseline.tot_cliff, "workers={workers}");
        assert_eq!(got.classical_failures, baseline.classical_failures, "workers={workers}");
        assert_eq!(got.phase_garbage_batches, baseline.phase_garbage_batches, "workers={workers}");
        assert_eq!(got.ancilla_garbage_batches, baseline.ancilla_garbage_batches, "workers={workers}");
        assert_eq!(got.fail_reason, baseline.fail_reason, "workers={workers}");
    }
}

#[test]
fn compute_wave_plan_dynamic_budget_and_overflow_guards() {
    // 100M ops x 26M bits => stream_bytes = 5.6 GB, per_sim = ~208 MB => wave_size = 26 (NOT 141!)
    let w_small = compute_wave_plan(
        100_000_000,
        1200,
        26_000_000,
        141,
        MIN_SIM_STATE_BYTES,
        MAX_SIM_STATE_BYTES,
    )
    .expect("valid dynamic wave");
    assert_eq!(w_small, 26);

    // 2B ops x 26M bits => wave_budget = 32 GiB => fits all 141 batches in 1 wave!
    let w_large = compute_wave_plan(
        2_000_000_000,
        1200,
        26_000_000,
        141,
        MIN_SIM_STATE_BYTES,
        MAX_SIM_STATE_BYTES,
    )
    .expect("fits in 1 wave");
    assert_eq!(w_large, 141);

    // Overflow guard: u64::MAX - 2 qubits + 10 bits overflows u64
    assert!(compute_wave_plan(
        100,
        u64::MAX - 2,
        10,
        141,
        MIN_SIM_STATE_BYTES,
        MAX_SIM_STATE_BYTES
    )
    .is_err());

    // Oversized single simulator (> 32 GiB): 5B lanes * 8 = 40 GB > 32 GiB
    assert!(compute_wave_plan(
        100,
        5_000_000_000,
        0,
        141,
        MIN_SIM_STATE_BYTES,
        MAX_SIM_STATE_BYTES
    )
    .is_err());
}

#[test]
fn streaming_eval_rejects_pass2_corrupted_missing_operand_without_panicking() {
    let dir = TempDir::new("eval-pass2-missing-op");
    let valid_path = dir.path().join("valid.bin");
    let ops = build_synthetic_4reg_circuit();
    let mut w = OpsWriter::create(&valid_path).unwrap();
    w.extend(ops.iter().copied()).unwrap();
    w.finish().unwrap();

    let (summary, mut xof, _file) = pass1_validate_and_hash(&valid_path).unwrap();
    let points = generate_test_points(&mut xof, 8, 2);

    // Craft a corrupted file of the same op count containing CCX with q_control2 == NO_QUBIT
    let bad_path = dir.path().join("corrupted.bin");
    let mut bad_ops = ops.clone();
    let mut bad_ccx = mk_op(OperationType::CCX);
    bad_ccx.q_control2 = NO_QUBIT;
    bad_ccx.q_control1 = QubitId(0);
    bad_ccx.q_target = QubitId(1);
    *bad_ops.last_mut().unwrap() = bad_ccx;
    write_legacy_ref(&bad_ops, &bad_path);

    let bad_file = File::open(&bad_path).unwrap();
    let err = run_tests_streaming(bad_file, &summary, &points, &mut xof, 16, 1, 2)
        .expect_err("Pass 2 must reject missing required operand");
    assert!(
        err.contains("q_control2 == NO_QUBIT"),
        "unexpected error: {err}"
    );
}

#[test]
fn streaming_eval_rejects_modified_ops_bin_between_passes() {
    let dir = TempDir::new("eval-digest-mismatch");
    let path1 = dir.path().join("ops1.bin");
    let ops1 = build_synthetic_4reg_circuit();
    let mut w1 = OpsWriter::create(&path1).unwrap();
    w1.extend(ops1.iter().copied()).unwrap();
    w1.finish().unwrap();

    let (summary, mut xof, _file1) = pass1_validate_and_hash(&path1).unwrap();
    let points = generate_test_points(&mut xof, 8, 2);

    // Build a different valid circuit with the exact same op count and qubits/bits
    let path2 = dir.path().join("ops2.bin");
    let mut ops2 = ops1.clone();
    let mut flipped = mk_op(OperationType::X);
    flipped.q_target = QubitId(512);
    // Replace the last op (PopCondition -> wait, keep condition stack balanced: replace an X target)
    let x_pos = ops2
        .iter()
        .position(|o| o.kind == OperationType::X)
        .unwrap();
    flipped.q_target = QubitId(513);
    ops2[x_pos] = flipped;
    let mut w2 = OpsWriter::create(&path2).unwrap();
    w2.extend(ops2.iter().copied()).unwrap();
    w2.finish().unwrap();

    let file2 = File::open(&path2).unwrap();
    let err = run_tests_streaming(file2, &summary, &points, &mut xof, 16, 1, 2)
        .expect_err("Pass 2 must reject file whose compressed bytes changed after Pass 1");
    assert!(
        err.contains("changed between Pass 1 and Pass 2"),
        "unexpected error: {err}"
    );
}

#[test]
fn streaming_eval_does_not_deadlock_on_read_error_or_worker_panic() {
    let dir = TempDir::new("eval-no-deadlock");

    // 1. Mid-stream truncated zstd body in Pass 1 must return Err promptly (no hang)
    let trunc_path = dir.path().join("truncated.bin");
    let ops = sample_valid_ops(2000);
    let mut w = OpsWriter::create(&trunc_path).unwrap();
    w.extend(ops).unwrap();
    w.finish().unwrap();
    let mut bytes = fs::read(&trunc_path).unwrap();
    bytes.truncate(bytes.len() / 2);
    fs::write(&trunc_path, &bytes).unwrap();

    let (tx1, rx1) = mpsc::channel();
    let p1 = trunc_path.clone();
    std::thread::spawn(move || {
        let res = pass1_validate_and_hash(&p1);
        let _ = tx1.send(res.is_err());
    });
    assert!(
        rx1.recv_timeout(Duration::from_secs(5))
            .expect("Pass 1 hung on truncated file"),
        "Pass 1 must return Err"
    );

    // 2. Worker panic in fanout_chunks must return Err promptly (no deadlock!)
    let (tx2, rx2) = mpsc::channel();
    std::thread::spawn(move || {
        let mut items: Vec<usize> = (0..10).collect();
        let mut sent = 0usize;
        let res = fanout_chunks(
            &mut items,
            4,
            16,
            |buf| {
                if sent >= 20 {
                    return Ok(0);
                }
                sent += 1;
                buf.push(mk_op(OperationType::Neg));
                Ok(1)
            },
            |slice, _chunk| {
                if slice.contains(&5) {
                    panic!("intentional test worker panic");
                }
            },
        );
        let _ = tx2.send(res.is_err());
    });
    assert!(
        rx2.recv_timeout(Duration::from_secs(5))
            .expect("fanout_chunks deadlocked after worker panic"),
        "fanout_chunks must return Err on worker panic"
    );
}

#[test]
fn parallel_test_point_generation_matches_sequential_bit_for_bit() {
    let mut h = Shake256::default();
    h.update(b"parallel-points-test");
    let xof_base = h.finalize_xof();

    let mut x1 = xof_base.clone();
    let mut x8 = xof_base.clone();
    let seq = generate_test_points(&mut x1, 256, 1);
    let par = generate_test_points(&mut x8, 256, 8);
    assert_eq!(par.targets, seq.targets);
    assert_eq!(par.offsets, seq.offsets);
    assert_eq!(par.expected, seq.expected);
}
