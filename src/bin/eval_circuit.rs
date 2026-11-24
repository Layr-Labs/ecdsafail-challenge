//! TRUSTED stage of the challenge harness.
//!
//! Reads the op stream produced by `build_circuit` from `ops.bin`,
//! re-simulates the circuit against the secp256k1 reference adder,
//! enforces the four validity checks (correctness, reversibility, phase,
//! ancilla cleanup), counts gates, writes `score.json`, and appends one
//! row to `results.tsv`.
//!
//! This binary deliberately does NOT import `quantum_ecc::point_add` —
//! contestant code never executes inside the trusted process. `ops.bin`
//! is treated as fully untrusted input and is bounds-checked before use.

use quantum_ecc::eval_stream::{
    compute_wave_plan, generate_test_points, pass1_validate_and_hash, run_tests_streaming,
    validate_registers, CHUNK_OPS, MAX_SIM_STATE_BYTES, MIN_SIM_STATE_BYTES, NUM_TESTS,
};
use quantum_ecc::ops_io::OPS_PATH;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn parse_note() -> String {
    let mut args = std::env::args().skip(1);
    let mut note = String::new();
    while let Some(a) = args.next() {
        if a == "--note" {
            if let Some(v) = args.next() {
                note = v;
            }
        } else if let Some(rest) = a.strip_prefix("--note=") {
            note = rest.to_string();
        }
    }
    note.replace('\t', " ").replace('\n', " ")
}

fn eval_worker_count() -> usize {
    if let Some(n) = std::env::var("EVAL_WORKERS")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&n| n > 0)
    {
        return n;
    }
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .saturating_sub(1)
        .max(1)
}

fn git_commit_short() -> String {
    Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|o| {
            if o.status.success() {
                Some(String::from_utf8_lossy(&o.stdout).trim().to_string())
            } else {
                None
            }
        })
        .unwrap_or_else(|| "nogit".to_string())
}

fn append_results_row(
    correct: &str,
    avg_tof: f64,
    avg_cliff: f64,
    qubits: u64,
    ops_len: u64,
    note: &str,
) {
    let ts = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let commit = git_commit_short();
    let safe_note = note.replace('\t', " ").replace('\n', " ");
    let row = format!(
        "{ts}\t{commit}\t{avg_tof:.3}\t{avg_cliff:.3}\t{qubits}\t{ops_len}\t{correct}\t{safe_note}\n"
    );
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/results.tsv");
    match OpenOptions::new().create(true).append(true).open(path) {
        Ok(mut f) => {
            if let Err(e) = f.write_all(row.as_bytes()) {
                eprintln!("warning: failed to write results.tsv: {e}");
            }
        }
        Err(e) => eprintln!("warning: failed to open results.tsv: {e}"),
    }
}

fn write_score(avg_tof: f64, qubits: u64) {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/score.json");
    let toffoli = avg_tof.round() as u64;
    let score = toffoli.saturating_mul(qubits);
    let body = format!(
        "{{\n  \"score\": {score},\n  \"metrics\": {{\n    \"toffoli\": {toffoli},\n    \"qubits\": {qubits}\n  }}\n}}\n"
    );
    if let Err(e) = std::fs::write(path, body) {
        eprintln!("warning: failed to write score.json: {e}");
    }
}

fn fail_and_exit(reason: &str, note: &str, ops_len: u64, total_qubits: u64) -> ! {
    eprintln!("\n!! eval FAILED: {reason}");
    let fail_note = if note.is_empty() {
        reason.to_string()
    } else {
        format!("{note} | {reason}")
    };
    append_results_row("FAIL", 0.0, 0.0, total_qubits, ops_len, &fail_note);
    std::process::exit(1);
}

fn main() {
    let note = parse_note();
    println!("=== quantum_ecc: eval_circuit (trusted stage) ===\n");

    let (summary, mut xof, file) = match pass1_validate_and_hash(Path::new(OPS_PATH)) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("!! could not load {OPS_PATH}: {e}");
            append_results_row("FAIL", 0.0, 0.0, 0, 0, &format!("{note} | load: {e}"));
            std::process::exit(1);
        }
    };
    println!("  loaded ops  : {}", summary.ops_len);

    if let Err(reason) = validate_registers(&summary.regs) {
        fail_and_exit(&reason, &note, summary.ops_len, summary.total_qubits);
    }

    let wave_size = match compute_wave_plan(
        summary.ops_len,
        summary.total_qubits,
        summary.num_bits,
        NUM_TESTS.div_ceil(64),
        MIN_SIM_STATE_BYTES,
        MAX_SIM_STATE_BYTES,
    ) {
        Ok(w) => w,
        Err(reason) => fail_and_exit(&reason, &note, summary.ops_len, summary.total_qubits),
    };

    println!("  qubits      : {}", summary.total_qubits);
    println!("  bits        : {}", summary.num_bits);

    let all_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);
    let workers = eval_worker_count();

    println!("\n-- correctness tests ({} shots) --", NUM_TESTS);
    let points = generate_test_points(&mut xof, NUM_TESTS, all_threads);
    let r = match run_tests_streaming(
        file,
        &summary,
        &points,
        &mut xof,
        CHUNK_OPS,
        wave_size,
        workers,
    ) {
        Ok(r) => r,
        Err(reason) => fail_and_exit(&reason, &note, summary.ops_len, summary.total_qubits),
    };

    println!("  tested shots            : {}", r.n_shots);
    println!("  classical mismatches    : {}", r.classical_failures);
    println!("  phase-garbage batches   : {}", r.phase_garbage_batches);
    println!("  ancilla-garbage batches : {}", r.ancilla_garbage_batches);
    if !r.ok {
        let reason = r.fail_reason.clone().unwrap_or_else(|| "(no detail)".into());
        println!("\n!! correctness FAILED: {reason}");
        let fail_note = format!("{note} | {reason}");
        append_results_row(
            "FAIL",
            r.avg_tof,
            r.avg_cliff,
            summary.total_qubits,
            summary.ops_len,
            &fail_note,
        );
        std::process::exit(1);
    }
    println!("  all {} shots OK", r.n_shots);

    println!("\n=== circuit metrics (secp256k1, n=256) ===");
    println!("  avg executed Toffoli  : {:.3}", r.avg_tof);
    println!("  avg executed Clifford : {:.3}", r.avg_cliff);
    println!(
        "  total Toffoli (sum)   : {} over {} shots",
        r.tot_tof, r.n_shots
    );
    println!("  total Clifford (sum)  : {}", r.tot_cliff);
    println!("  emitted ops           : {}", summary.ops_len);
    println!("  qubits                : {}", summary.total_qubits);

    append_results_row(
        "OK",
        r.avg_tof,
        r.avg_cliff,
        summary.total_qubits,
        summary.ops_len,
        &note,
    );
    write_score(r.avg_tof, summary.total_qubits);

    println!("\n=== experiment OK ===");
}
