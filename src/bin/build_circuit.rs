//! UNTRUSTED stage of the challenge harness.
//!
//! Invokes `point_add::build()` (the contestant's editable code) and
//! writes the resulting op stream to `ops.bin`. Nothing else runs here:
//! no simulation, no scoring, no `score.json`. The trusted `eval_circuit`
//! binary re-reads `ops.bin` from disk in a separate process so contestant
//! code cannot influence the score.
//!
//! Large circuits can avoid materializing a full `Vec<Op>` in memory by
//! streaming directly via `crate::ops_io::OpsWriter::create_default()`,
//! calling `finish()`, and returning `Vec::new()` from `point_add::build()`.

use quantum_ecc::circuit::Op;
use quantum_ecc::ops_io::{
    clean_stale_ops, finalize_build_output, reset_stream_started, take_stream_started, OpsWriter,
    OPS_PATH,
};
use std::path::Path;

// Contestant code is compiled into THIS binary only. It must never be part
// of the shared `quantum_ecc` library: that library is also linked into the
// trusted `eval_circuit`, and an `.init_array`/`__mod_init_func` constructor
// in contestant code would then run before `main` in the scorer process,
// letting it forge `score.json` and exit 0 before any validation runs.
// Including the sources via `#[path]` keeps every existing `crate::point_add`,
// `crate::circuit`, `crate::ops_io`, `crate::sim`,
// `crate::weierstrass_elliptic_curve` path inside `src/point_add/**`
// resolving cleanly, so existing submissions build unchanged.
#[allow(dead_code)]
#[path = "../point_add/mod.rs"]
mod point_add;

// Root bindings backing the `crate::{circuit,ops_io,sim,weierstrass_elliptic_curve}`
// paths used inside `src/point_add/**` (see the note above).
#[allow(unused_imports)]
use quantum_ecc::{circuit, ops_io, sim, weierstrass_elliptic_curve};

// Legacy module-private shims preserved with exact signatures because
// historical submissions in `src/point_add/**` call `crate::zstd_level()`
// and `crate::write_ops(&ops, path)`.
#[allow(dead_code)]
fn zstd_level() -> i32 {
    ops_io::zstd_level()
}

#[allow(dead_code)]
fn write_ops(ops: &[Op], path: &Path) -> std::io::Result<()> {
    let mut writer = OpsWriter::create(path)?;
    for op in ops {
        writer.push(op)?;
    }
    writer.finish()?;
    Ok(())
}

fn main() {
    println!("=== quantum_ecc: build_circuit (untrusted stage) ===\n");
    println!("-- building circuit --");

    let path = Path::new(OPS_PATH);
    if let Err(e) = clean_stale_ops(path) {
        eprintln!("error: failed to clean stale {}: {}", OPS_PATH, e);
        std::process::exit(2);
    }
    reset_stream_started();

    let ops = point_add::build();
    let stream_started = take_stream_started();

    let summary = match finalize_build_output(&ops, path, stream_started) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(2);
        }
    };

    println!("  emitted ops : {}", summary.count);
    println!(
        "  wrote       : {} ({} bytes on disk, {} uncompressed, {:.1}x)",
        OPS_PATH,
        summary.on_disk_bytes,
        summary.uncompressed_bytes,
        summary.uncompressed_bytes as f64 / summary.on_disk_bytes.max(1) as f64,
    );
    println!("\n=== build_circuit OK ===");
}
