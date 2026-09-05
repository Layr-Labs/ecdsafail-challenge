#!/usr/bin/env python3
"""Portable, source-pinned Q823 paired-Tsub retained-Tadd stream reproduction. Attribution: gpt-5.

Builds real Qiskit circuits and uses the qualified typed paired flatten/pack code.
Fresh output directory only; four workers maximum; 45 steps per shard; each
worker limited to 512 MiB and 180 seconds per shard. No external proof files,
network, benchmark invocation, submission, or authentication are required.
"""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
import gc
import hashlib
import importlib.metadata
import importlib.util
import json
import multiprocessing
import os
from pathlib import Path
import resource
import signal
import struct
import sys
import time

os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SOURCE_PINS = {
    'eea_circuit_s835_exactwidth_dirty12.py': '16e1bf06d353fe95ff8a6aad1d0e977c976b6651d8c90a0d54a3351dff179072',
    'eea_circuit_updated.py': '067d363deeabb6532b52f42eba884b0d184c5b74aa14d2c0d33e5579f668d277',
    'eea_circuit_s835_lowaux.py': 'b5f7aaabff4d86912c4b28cff48c43fac465def7d51ca28eb59e47835b54b70c',
    'active_windows_1616.json': '3e1961f5550249604bf044edb65f1d1bc403ed75bd7178e283685ddb4f3cb880',
    'generate_eea_blob.py': 'a24d42628b411672bc2654a27ef0304017f8e00bc627c130b600c4c01005e512',
    'paired_codec.py': 'd79109b671cddb232fbb48e4a23ff42c44eb830b5b8c45f19eb576d3b0da7f72',
}
VERSIONS = {'dill': '0.4.1', 'numpy': '2.4.6', 'qiskit': '2.1.2', 'rustworkx': '0.18.1',
            'scipy': '1.17.1', 'stevedore': '5.9.1', 'typing_extensions': '4.16.0', 'zstandard': '0.23.0'}
KINDS = {'x': 1, 'cx': 2, 'ccx': 3, 'z': 4, 'cz': 5, 'swap': 6, 'clean_c3x_mbu': 7, 'paired_tsub_compute_v1': 8, 'paired_tsub_uncompute_v1': 9}
ARITIES = {'x': 1, 'cx': 2, 'ccx': 3, 'z': 1, 'cz': 2, 'swap': 2, 'clean_c3x_mbu': 5, 'paired_tsub_compute_v1': 3, 'paired_tsub_uncompute_v1': 3}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def directional_counts(counts):
    c = Counter(counts)
    result = {}
    for direction, compute, erase in (("forward", c["paired_tsub_compute_v1"], c["paired_tsub_uncompute_v1"]),
                                      ("reverse", c["paired_tsub_uncompute_v1"], c["paired_tsub_compute_v1"])):
        m = c["clean_c3x_mbu"]
        result[direction] = dict(ccx=c["ccx"] + compute + 2*m, hmr=m + erase,
                                 cz=c["cz"] + m + erase, ops=sum(c.values()) + 3*m + erase)
    return result


def preflight():
    raw = (HERE / 'source_manifest.json').read_bytes()
    manifest = json.loads(raw)
    need(manifest['schema'] == 'q823-portable-source-reproduction-v1', 'source manifest schema')
    need(manifest['attribution'] == 'gpt-5', 'attribution')
    expected_files = set(SOURCE_PINS) | {'reproduce_q823_idle_mbu.py', 'requirements.txt', 'README-q823-idle-mbu.md', 'UPSTREAM_LICENSE'}
    need(set(manifest['files']) == expected_files, 'source manifest file set')
    for name, row in manifest['files'].items():
        path = HERE / name
        need(path.is_file() and not path.is_symlink(), f'source is not a regular file: {name}')
        data = path.read_bytes()
        need(sha(data) == row['sha256'] and len(data) == row['bytes'], f'source hash or length: {name}')
    for name, expected in SOURCE_PINS.items():
        need(manifest['files'][name]['sha256'] == expected, f'fixed source pin: {name}')
    need({name: importlib.metadata.version(name) for name in VERSIONS} == VERSIONS, 'dependency versions')
    requirements = dict(line.split('==', 1) for line in (HERE / 'requirements.txt').read_text().splitlines())
    need(requirements == VERSIONS, 'requirements do not match runtime pins')
    return sha(raw)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    need(spec is not None and spec.loader is not None, f'cannot load module: {name}')
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def clear_caches(*modules):
    for module in modules:
        for function in vars(module).values():
            clear = getattr(function, 'cache_clear', None)
            if callable(clear):
                clear()
    gc.collect()
    for module in modules:
        for function in vars(module).values():
            info = getattr(function, 'cache_info', None)
            if callable(info):
                need(info().currsize == 0, 'production lru cache did not empty')


def worker(task):
    start, end, output = task
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 512 * 1024**2))
    signal.alarm(180)
    began = time.monotonic()
    manifest_sha = preflight()
    import qiskit
    import zstandard
    need(qiskit.__version__ == '2.1.2' and zstandard.__version__ == '0.23.0', 'loaded dependency versions')
    sys.path.insert(0, str(HERE))
    import eea_circuit_updated as support
    import eea_circuit_s835_lowaux as lowaux
    module = load_module('q823_mbu_generation_source', HERE / 'eea_circuit_s835_exactwidth_dirty12.py')
    flat = load_module('q823_original_production_flatten', HERE / 'paired_codec.py')
    need(flat.KIND == KINDS, 'production record enum')
    path = Path(output) / f'chunk-{start:04d}-{end:04d}.zst'
    total = Counter()
    per_step = []
    digest = hashlib.sha256()
    records = 0
    with path.open('xb') as handle:
        with zstandard.ZstdCompressor(level=12).stream_writer(handle, closefd=False) as stream:
            stream.write(b'P26EEA3\0' + struct.pack('<IIII', 256, 577, start, end))
            for step in range(start, end + 1):
                clear_caches(module, support, lowaux)
                circuit = module.build_step_circuit(256, step, T_max=1616, aux_size=11, measurement_uncompute=False)
                need(circuit.num_qubits == 577 and support.MEASUREMENT_UNCOMPUTE is False, 'production physical ABI')
                counts = Counter()
                step_digest = hashlib.sha256()
                step_records = 0
                for kind, positions in flat.flatten_paired_v1(circuit):
                    need(kind in ARITIES and len(positions) == ARITIES[kind], 'production kind/arity')
                    need(len(set(positions)) == len(positions) and all(0 <= index < 577 for index in positions),
                         'production operand bounds/alias')
                    record = flat.pack_paired_v1(kind, positions)
                    stream.write(record)
                    digest.update(record)
                    step_digest.update(record)
                    counts[kind] += 1
                    step_records += 1
                per_step.append({'step': step, 'counts': dict(counts), 'records': step_records,
                                 'executed_toffoli': directional_counts(counts)['forward']['ccx'],
                                 'directional': directional_counts(counts), 'raw_record_sha256': step_digest.hexdigest()})
                total.update(counts)
                records += step_records
                del circuit
                clear_caches(module, support, lowaux)
    need(preflight() == manifest_sha, 'source manifest changed during generation')
    signal.alarm(0)
    report = {'schema': 'paper2607-paired-portable-stream-v1', 'source_module': 'q823_mbu_generation_source',
              'n': 256, 'qubits': 577, 'aux_size': 11, 'step_start': start, 'step_end': end, 'schedule_end': 1616,
              'measurement_uncompute': False, 'record_bytes': 8, 'records': records, 'counts': dict(total),
              'executed_toffoli': directional_counts(total)['forward']['ccx'], 'directional': directional_counts(total),
              'raw_record_sha256': digest.hexdigest(), 'compressed_bytes': path.stat().st_size,
              'compressed_sha256': sha(path.read_bytes()), 'per_step': per_step,
              'input_manifest_sha256': manifest_sha, 'candidate_source_sha256': SOURCE_PINS['eea_circuit_s835_exactwidth_dirty12.py'],
              'generator_sha256': sha(Path(__file__).read_bytes()), 'cache_cleared_and_empty_each_step': True,
              'elapsed_seconds': time.monotonic() - began, 'maxrss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    with path.with_suffix('.zst.json').open('x') as handle:
        json.dump(report, handle, indent=2, sort_keys=True)
        handle.write('\n')
    del sys.modules['q823_mbu_generation_source']
    del sys.modules['q823_original_production_flatten']
    gc.collect()
    return {'file': path.name, **report}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='fresh output directory; never reused')
    parser.add_argument('--start', type=int, default=1)
    parser.add_argument('--end', type=int, default=1616)
    parser.add_argument('--workers', type=int, default=4)
    args = parser.parse_args()
    need(1 <= args.start <= args.end <= 1616 and 1 <= args.workers <= 4, 'range or worker count')
    manifest_sha = preflight()
    args.output.mkdir()
    intent = {'schema': 'q823-local-generation-intent-v1', 'range': [args.start, args.end],
              'workers': args.workers, 'chunk_steps': 45, 'source_manifest_sha256': manifest_sha,
              'generator_sha256': sha(Path(__file__).read_bytes()), 'dependencies': VERSIONS,
              'started_unix': time.time(), 'publication': False, 'full9024_validation': False}
    with (args.output / 'intent.json').open('x') as handle:
        json.dump(intent, handle, indent=2, sort_keys=True)
        handle.write('\n')
    tasks = [(start, min(start + 44, args.end), str(args.output.resolve())) for start in range(args.start, args.end + 1, 45)]
    reports = []
    try:
        with ProcessPoolExecutor(max_workers=args.workers, mp_context=multiprocessing.get_context('spawn')) as pool:
            futures = [pool.submit(worker, task) for task in tasks]
            for future in as_completed(futures):
                report = future.result()
                reports.append(report)
                print(json.dumps({'completed': report['file'], 'records': report['records'],
                                  'executed_toffoli': report['executed_toffoli']}), flush=True)
        reports.sort(key=lambda row: row['step_start'])
        total = Counter()
        rows = []
        for report in reports:
            total.update(report['counts'])
            rows.extend(report['per_step'])
        need([r['step'] for r in rows] == list(range(args.start, args.end + 1)), 'complete generated step coverage')
        need(preflight() == manifest_sha, 'source manifest changed before completion')
        aggregate = {'schema': 'q823-paired-retained-portable-stream-v1', 'status': 'COMPLETE_GENERATION_UNVALIDATED',
                     'step_start': args.start, 'step_end': args.end, 'schedule_end': 1616, 'qubits': 577, 'owned_qubits': 567,
                     'counts': dict(total), 'records': sum(r['records'] for r in reports),
                     'executed_toffoli': directional_counts(total)['forward']['ccx'], 'directional': directional_counts(total),
                     'input_manifest_sha256': manifest_sha, 'generator_sha256': sha(Path(__file__).read_bytes()),
                     'candidate_source_sha256': SOURCE_PINS['eea_circuit_s835_exactwidth_dirty12.py'],
                     'shards': [{key: r[key] for key in ('file', 'compressed_sha256', 'raw_record_sha256', 'step_start', 'step_end')}
                                for r in reports], 'per_step': rows, 'full9024_validated': False, 'rust_builder_reduction_run': False}
        with (args.output / 'aggregate_manifest.json').open('x') as handle:
            json.dump(aggregate, handle, indent=2, sort_keys=True)
            handle.write('\n')
        print(json.dumps({'status': aggregate['status'], 'aggregate_sha256': sha((args.output / 'aggregate_manifest.json').read_bytes()),
                          'executed_toffoli': aggregate['executed_toffoli']}), flush=True)
    except BaseException as error:
        with (args.output / 'FAILED.json').open('x') as handle:
            json.dump({'status': 'GENERATION_FAILED_OUTPUT_PRESERVED', 'error_type': type(error).__name__}, handle, indent=2)
            handle.write('\n')
        raise


if __name__ == '__main__':
    main()
