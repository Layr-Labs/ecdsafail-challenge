//! Canonical streaming I/O for the `QECCOPSZ` circuit op format.
//!
//! Format layout:
//!   - 8 bytes: `MAGIC` (`b"QECCOPSZ"`)
//!   - 8 bytes: little-endian `u64` op count `n` (`n <= MAX_OPS`)
//!   - zstd frame of `n` fixed-width 56-byte little-endian op records:
//!       u32 kind (0..=17) | u32 _pad (0)
//!       u64 q_control2, q_control1, q_target, c_target, c_condition, r_target
//!
//! Trusted library code shared by `build_circuit` (streaming write) and
//! `eval_circuit` (bounded streaming decode + SHA3-256 integrity hashing).

use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use sha3::{Digest, Sha3_256};
use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

pub const OPS_PATH: &str = "ops.bin";
pub const MAGIC: &[u8; 8] = b"QECCOPSZ";
pub const OP_BYTES: usize = 56;
pub const DEFAULT_ZSTD_LEVEL: i32 = 3;
pub const ZSTD_WINDOW_LOG_MAX: u32 = 27;
pub const MAX_OPS: u64 = 4_000_000_000;

const IO_BATCH_OPS: usize = 1024;
const WRITER_BUF_BYTES: usize = 256 * 1024;

static STREAM_STARTED: AtomicBool = AtomicBool::new(false);

pub fn reset_stream_started() {
    STREAM_STARTED.store(false, Ordering::SeqCst);
}

pub fn take_stream_started() -> bool {
    STREAM_STARTED.swap(false, Ordering::SeqCst)
}

pub fn zstd_level() -> i32 {
    std::env::var("ZSTD_LEVEL")
        .ok()
        .and_then(|s| s.trim().parse().ok())
        .unwrap_or(DEFAULT_ZSTD_LEVEL)
}

pub fn tmp_path_for(path: &Path) -> PathBuf {
    path.with_extension("bin.tmp")
}

pub fn op_kind_from_u32(v: u32) -> Option<OperationType> {
    Some(match v {
        0 => OperationType::Neg,
        1 => OperationType::Register,
        2 => OperationType::AppendToRegister,
        3 => OperationType::BitInvert,
        4 => OperationType::BitStore0,
        5 => OperationType::BitStore1,
        6 => OperationType::X,
        7 => OperationType::Z,
        8 => OperationType::CX,
        9 => OperationType::CZ,
        10 => OperationType::Swap,
        11 => OperationType::R,
        12 => OperationType::Hmr,
        13 => OperationType::CCX,
        14 => OperationType::CCZ,
        15 => OperationType::PushCondition,
        16 => OperationType::PopCondition,
        17 => OperationType::DebugPrint,
        _ => return None,
    })
}

fn read_u64_le(bytes: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(bytes[off..off + 8].try_into().unwrap())
}

fn read_header_from<R: Read>(r: &mut R, label: &str, max_ops: u64) -> Result<u64, String> {
    let mut header = [0u8; MAGIC.len() + 8];
    r.read_exact(&mut header)
        .map_err(|e| format!("{label}: too short to read header: {e}"))?;
    if &header[..MAGIC.len()] != MAGIC {
        return Err(format!("{label}: bad magic"));
    }
    let n = u64::from_le_bytes(header[MAGIC.len()..].try_into().unwrap());
    if n > max_ops {
        return Err(format!("{label}: op count {n} exceeds cap {max_ops}"));
    }
    Ok(n)
}

pub fn read_header(path: &Path) -> Result<u64, String> {
    let label = path.display().to_string();
    let mut file = File::open(path).map_err(|e| format!("open {label}: {e}"))?;
    read_header_from(&mut file, &label, MAX_OPS)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WriteSummary {
    pub count: u64,
    pub on_disk_bytes: u64,
    pub uncompressed_bytes: u64,
}

impl WriteSummary {
    pub fn from_file_and_count(path: &Path, count: u64) -> Self {
        let on_disk_bytes = fs::metadata(path).map(|m| m.len()).unwrap_or(0);
        let uncompressed_bytes = count
            .saturating_mul(OP_BYTES as u64)
            .saturating_add((MAGIC.len() + 8) as u64);
        Self {
            count,
            on_disk_bytes,
            uncompressed_bytes,
        }
    }
}

/// Streaming writer for `ops.bin`. Writes fixed 56-byte records through zstd
/// into `*.bin.tmp`, backpatches the exact op count in the 16-byte header on
/// `finish()`, and atomically renames to the final path.
pub struct OpsWriter {
    enc: Option<zstd::stream::write::Encoder<'static, BufWriter<File>>>,
    tmp_path: PathBuf,
    final_path: PathBuf,
    count: u64,
    max_ops: u64,
    finished: bool,
}

impl OpsWriter {
    pub fn create_default() -> io::Result<Self> {
        Self::create(OPS_PATH)
    }

    pub fn create(path: impl AsRef<Path>) -> io::Result<Self> {
        Self::create_with_max_ops(path, MAX_OPS)
    }

    pub fn create_with_max_ops(path: impl AsRef<Path>, max_ops: u64) -> io::Result<Self> {
        let final_path = path.as_ref().to_path_buf();
        if final_path.file_name() == Some(OsStr::new(OPS_PATH)) {
            STREAM_STARTED.store(true, Ordering::SeqCst);
        }
        let tmp_path = tmp_path_for(&final_path);
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&tmp_path)?;

        // Write uncompressed header with placeholder count; backpatched on finish().
        file.write_all(MAGIC)?;
        file.write_all(&0u64.to_le_bytes())?;

        let buf_writer = BufWriter::with_capacity(WRITER_BUF_BYTES, file);
        let enc = zstd::stream::write::Encoder::new(buf_writer, zstd_level())?;

        Ok(Self {
            enc: Some(enc),
            tmp_path,
            final_path,
            count: 0,
            max_ops,
            finished: false,
        })
    }

    #[inline]
    pub fn count(&self) -> u64 {
        self.count
    }

    #[inline]
    pub fn push(&mut self, op: &Op) -> io::Result<()> {
        if self.count >= self.max_ops {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("op count exceeds cap {}", self.max_ops),
            ));
        }
        let mut rec = [0u8; OP_BYTES];
        rec[0..4].copy_from_slice(&(op.kind as u32).to_le_bytes());
        rec[8..16].copy_from_slice(&op.q_control2.0.to_le_bytes());
        rec[16..24].copy_from_slice(&op.q_control1.0.to_le_bytes());
        rec[24..32].copy_from_slice(&op.q_target.0.to_le_bytes());
        rec[32..40].copy_from_slice(&op.c_target.0.to_le_bytes());
        rec[40..48].copy_from_slice(&op.c_condition.0.to_le_bytes());
        rec[48..56].copy_from_slice(&op.r_target.0.to_le_bytes());
        self.enc.as_mut().unwrap().write_all(&rec)?;
        self.count += 1;
        Ok(())
    }

    pub fn extend<I: IntoIterator<Item = Op>>(&mut self, ops: I) -> io::Result<()> {
        for op in ops {
            self.push(&op)?;
        }
        Ok(())
    }

    pub fn finish(mut self) -> io::Result<WriteSummary> {
        self.finished = true;
        let mut buf_writer = self.enc.take().unwrap().finish()?;
        buf_writer.flush()?;
        let mut file = buf_writer.into_inner().map_err(|e| e.into_error())?;
        file.seek(SeekFrom::Start(MAGIC.len() as u64))?;
        file.write_all(&self.count.to_le_bytes())?;
        file.flush()?;
        drop(file);
        fs::rename(&self.tmp_path, &self.final_path)?;
        Ok(WriteSummary::from_file_and_count(
            &self.final_path,
            self.count,
        ))
    }
}

impl Drop for OpsWriter {
    fn drop(&mut self) {
        if !self.finished {
            // Release file handle before removing temp file.
            self.enc.take();
            let _ = fs::remove_file(&self.tmp_path);
        }
    }
}

struct HashingReader<R> {
    inner: R,
    hasher: Sha3_256,
}

impl<R> HashingReader<R> {
    fn new(inner: R) -> Self {
        Self {
            inner,
            hasher: Sha3_256::new(),
        }
    }

    fn into_inner_and_digest(self) -> (R, [u8; 32]) {
        let digest: [u8; 32] = self.hasher.finalize().into();
        (self.inner, digest)
    }
}

impl<R: Read> Read for HashingReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.inner.read(buf)?;
        if n > 0 {
            self.hasher.update(&buf[..n]);
        }
        Ok(n)
    }
}

/// Bounded streaming reader for `ops.bin`. Hashes every raw byte read from
/// offset 0 through EOF (header + compressed body) with SHA3-256 so Pass 2
/// can verify the file did not change after Pass 1.
pub struct OpsReader {
    dec: zstd::stream::read::Decoder<'static, BufReader<HashingReader<File>>>,
    label: String,
    total_ops: u64,
    read_ops: u64,
    remaining: u64,
    eof_checked: bool,
    io_buf: Vec<u8>,
}

impl OpsReader {
    pub fn open(path: impl AsRef<Path>) -> Result<Self, String> {
        let p = path.as_ref();
        let label = p.display().to_string();
        let file = File::open(p).map_err(|e| format!("open {label}: {e}"))?;
        Self::from_file_inner(file, label, MAX_OPS)
    }

    pub fn from_file(file: File) -> Result<Self, String> {
        Self::from_file_with_max_ops(file, MAX_OPS)
    }

    pub fn from_file_with_max_ops(file: File, max_ops: u64) -> Result<Self, String> {
        Self::from_file_inner(file, OPS_PATH.to_string(), max_ops)
    }

    fn from_file_inner(mut file: File, label: String, max_ops: u64) -> Result<Self, String> {
        file.seek(SeekFrom::Start(0))
            .map_err(|e| format!("{label}: seek to start: {e}"))?;

        // Wrap BEFORE reading the 16-byte header so the digest covers bytes 0..EOF.
        let mut hr = HashingReader::new(file);
        let n = read_header_from(&mut hr, &label, max_ops)?;

        let mut dec = zstd::stream::read::Decoder::new(hr)
            .map_err(|e| format!("{label}: zstd init: {e}"))?;
        dec.window_log_max(ZSTD_WINDOW_LOG_MAX)
            .map_err(|e| format!("{label}: zstd window cap: {e}"))?;

        Ok(Self {
            dec,
            label,
            total_ops: n,
            read_ops: 0,
            remaining: n,
            eof_checked: false,
            io_buf: vec![0u8; IO_BATCH_OPS * OP_BYTES],
        })
    }

    #[inline]
    pub fn total_ops(&self) -> u64 {
        self.total_ops
    }

    fn check_eof(&mut self) -> Result<(), String> {
        if self.eof_checked {
            return Ok(());
        }
        let mut extra = [0u8; 1];
        match self.dec.read(&mut extra) {
            Ok(0) => {
                self.eof_checked = true;
                Ok(())
            }
            Ok(_) => Err(format!(
                "{}: trailing data after {} ops",
                self.label, self.total_ops
            )),
            Err(e) => Err(format!(
                "{}: error checking for trailing data: {e}",
                self.label
            )),
        }
    }

    pub fn read_chunk(
        &mut self,
        buf: &mut Vec<Op>,
        max_ops: usize,
        validate: bool,
    ) -> Result<usize, String> {
        buf.clear();
        if self.remaining == 0 {
            self.check_eof()?;
            return Ok(0);
        }
        let want = (self.remaining as usize).min(max_ops);
        if want == 0 {
            return Ok(0);
        }
        buf.reserve(want);

        let mut left = want;
        while left > 0 {
            let batch = left.min(IO_BATCH_OPS);
            let byte_len = batch * OP_BYTES;
            let raw = &mut self.io_buf[..byte_len];
            self.dec.read_exact(raw).map_err(|e| {
                format!(
                    "op {}: short read from compressed body: {e}",
                    self.read_ops
                )
            })?;

            for k in 0..batch {
                let off = k * OP_BYTES;
                let rec = &raw[off..off + OP_BYTES];
                let op_idx = self.read_ops;
                let kind_raw = u32::from_le_bytes(rec[0..4].try_into().unwrap());
                let kind = op_kind_from_u32(kind_raw)
                    .ok_or_else(|| format!("op {op_idx}: unknown kind {kind_raw}"))?;
                let op = Op {
                    kind,
                    q_control2: QubitId(read_u64_le(rec, 8)),
                    q_control1: QubitId(read_u64_le(rec, 16)),
                    q_target: QubitId(read_u64_le(rec, 24)),
                    c_target: BitId(read_u64_le(rec, 32)),
                    c_condition: BitId(read_u64_le(rec, 40)),
                    r_target: RegisterId(read_u64_le(rec, 48)),
                };
                if validate {
                    op.try_validate().map_err(|msg| format!("op {op_idx}: {msg}"))?;
                }
                buf.push(op);
                self.read_ops += 1;
            }

            left -= batch;
            self.remaining -= batch as u64;
        }

        if self.remaining == 0 {
            self.check_eof()?;
        }
        Ok(want)
    }

    pub fn into_file_and_digest(mut self) -> Result<(File, [u8; 32]), String> {
        if self.remaining != 0 {
            return Err(format!(
                "{}: stream not fully read ({} ops remaining)",
                self.label, self.remaining
            ));
        }
        self.check_eof()?;
        let hr = self.dec.finish().into_inner();
        Ok(hr.into_inner_and_digest())
    }
}
