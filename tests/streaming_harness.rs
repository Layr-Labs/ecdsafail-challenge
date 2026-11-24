use quantum_ecc::circuit::{
    analyze_ops, BitId, Op, OperationType, OpsAnalyzer, QubitId, QubitOrBit, RegisterId, NO_BIT,
    NO_QUBIT, NO_REG,
};
use quantum_ecc::ops_io::{
    clean_stale_ops, finalize_build_output, reset_stream_started, take_stream_started,
    tmp_path_for, OpsReader, OpsWriter, DEFAULT_ZSTD_LEVEL, MAGIC, MAX_OPS, OP_BYTES,
};
use quantum_ecc::sim::{SimExecState, Simulator};
use sha3::{
    digest::{ExtendableOutput, Update},
    Shake256,
};
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

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
