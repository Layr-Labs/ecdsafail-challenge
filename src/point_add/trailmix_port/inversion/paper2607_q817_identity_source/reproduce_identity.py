#!/usr/bin/env python3
"""Portable exact Q817 identity records; no historical reducer or model draw."""
from collections import Counter
import argparse
import gc
import hashlib
import json
from pathlib import Path
import struct
import sys
from types import ModuleType

sys.dont_write_bytecode = True

KIND = {'x':1, 'cx':2, 'ccx':3, 'z':4, 'cz':5, 'swap':6, 'clean_c3x_mbu':7}
PINS = {
    'eea_circuit_s835_exactwidth_dirty12.py': 'b7ff97de22b36450d6fee3f267be62a00d8be24f6988849655e1fea04c9374d2',
    'eea_circuit_updated.py': '067d363deeabb6532b52f42eba884b0d184c5b74aa14d2c0d33e5579f668d277',
    'eea_circuit_s835_lowaux.py': 'b5f7aaabff4d86912c4b28cff48c43fac465def7d51ca28eb59e47835b54b70c',
    'active_windows_1616.json': '3e1961f5550249604bf044edb65f1d1bc403ed75bd7178e283685ddb4f3cb880',
}
MAX_STEP = 4*1024**2


def flatten(circuit, qmap=None):
    if qmap is None:
        qmap = {q: i for i, q in enumerate(circuit.qubits)}
    for item in circuit.data:
        op = item.operation
        qargs = [qmap[q] for q in item.qubits]
        name = op.name.lower()
        if name == "clean_c3x_mbu":
            yield name, qargs
            continue
        if item.clbits:
            raise RuntimeError(f"classical operands in unitary stream: {op.name}")
        if name in KIND:
            yield name, qargs
            continue
        definition = op.definition
        if definition is None:
            raise RuntimeError(f"opaque operation {op.name!r}")
        if definition.num_clbits:
            raise RuntimeError(f"dynamic definition in unitary stream: {op.name}")
        child_map = {q: qargs[i] for i, q in enumerate(definition.qubits)}
        yield from flatten(definition, child_map)


def pack_record(name: str, qargs: list[int]) -> bytes:
    if len(qargs) > 5:
        raise RuntimeError(f"primitive {name} has {len(qargs)} operands")
    q = qargs + [0, 0, 0, 0, 0]
    if any(x >= 1024 for x in qargs):
        raise RuntimeError(f"qubit index overflow in {name}: {qargs}")
    word = (KIND[name] | (len(qargs) << 4) | (q[0] << 8) | (q[1] << 18)
            | (q[2] << 28) | (q[3] << 38) | (q[4] << 48))
    return struct.pack("<Q", word)


def clear_caches(*modules):
    rows = []
    for module in modules:
        seen = set()
        for name,value in vars(module).items():
            clear,info = getattr(value,'cache_clear',None),getattr(value,'cache_info',None)
            if not callable(clear) or id(value) in seen: continue
            seen.add(id(value)); before = info().currsize if callable(info) else None
            clear(); after = info().currsize if callable(info) else None
            assert after in (None,0)
            rows.append(dict(module=module.__name__,function=name,before=before,after=after))
    gc.collect()
    assert rows
    return rows


def check_tree(circuit):
    seen = {}
    def visit(qc):
        assert qc.num_clbits == 0 and qc.global_phase == 0
        for item in qc.data:
            op = item.operation
            assert not item.clbits and getattr(op, 'condition', None) is None
            if op.name.lower() in KIND:
                continue
            if id(op) in seen:
                continue
            seen[id(op)] = op
            assert op.definition is not None
            visit(op.definition)
    visit(circuit)


def cache_snapshot(*modules):
    rows = []
    for module in modules:
        seen = set()
        for name, fn in vars(module).items():
            if not callable(getattr(fn, 'cache_clear', None)) or id(fn) in seen:
                continue
            seen.add(id(fn))
            stats = fn.cache_info()
            rows.append(dict(module=module.__name__, function=name, hits=stats.hits,
                             misses=stats.misses, currsize=stats.currsize))
    assert rows
    return rows


def cleared(*modules):
    clear_caches(*modules)
    rows = cache_snapshot(*modules)
    assert all(r['hits'] == r['misses'] == r['currsize'] == 0 for r in rows)
    return rows


def load_source(folder):
    for name, h in PINS.items():
        path = folder/name
        assert path.is_file() and not path.is_symlink()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == h, name
    assert sys.version_info[:3] == (3, 11, 5)
    import qiskit
    assert qiskit.__version__ == '2.1.2'
    sys.path.insert(0, str(folder))
    modules = []
    for filename in ('eea_circuit_updated.py', 'eea_circuit_s835_lowaux.py',
                     'eea_circuit_s835_exactwidth_dirty12.py'):
        name = filename[:-3]
        assert name not in sys.modules, 'source module already loaded'
        module = ModuleType(name)
        module.__file__ = str(folder/filename)
        sys.modules[name] = module
        raw = (folder/filename).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == PINS[filename]
        # Always compile the authenticated source bytes, never load a .pyc cache.
        exec(compile(raw,str(folder/filename),'exec'),module.__dict__)
        modules.append(module)
    return modules[2], modules[0], modules[1]


def run(folder, output, start, end):
    """Raw frames first; compression is a separate byte-only packaging stage."""
    assert __debug__ and type(start) is type(end) is int
    assert 1 <= start <= end <= 1616 and end-start < 45
    assert (start == end and start in (1, 256, 1021, 1616)) or (
        (start-1) % 45 == 0 and end == min(start+44, 1616))
    assert not output.exists() and not output.is_symlink()
    source, support, lowaux = load_source(folder)
    output.mkdir(mode=0o700)
    rows = []
    prefix = hashlib.sha256()
    with (output/'frame.bin').open('xb') as frame:
        frame.write(b'P26EEA2\0'+struct.pack('<4I', 256, 571, start, end))
        for step in range(start, end+1):
            before = cleared(source, support, lowaux)
            circuit = source.build_step_circuit(256, step, T_max=1616, aux_size=5,
                                                measurement_uncompute=False)
            assert circuit.num_qubits == 571 and circuit.num_clbits == 0
            registers = {r.name: [circuit.find_bit(q).index for q in r] for r in circuit.qregs}
            assert registers['Aux'] == list(range(556, 561))
            assert registers['DirtyPassenger'] == list(range(561, 571))
            check_tree(circuit)
            raw = bytearray()
            counts = Counter()
            for name, args in flatten(circuit):
                assert len(raw)+8 <= MAX_STEP
                raw.extend(pack_record(name, args))
                counts[name] += 1
            raw = bytes(raw)
            with (output/f'step-{step:04d}.records.bin').open('xb') as f:
                f.write(raw)
            frame.write(raw)
            prefix.update(raw)
            del circuit
            after = cleared(source, support, lowaux)
            row = dict(step=step, records=len(raw)//8, counts=dict(counts),
                raw_record_sha256=hashlib.sha256(raw).hexdigest(), prefix_raw_sha256=prefix.hexdigest(),
                entry_cache=before, exit_cache=after)
            rows.append(row)
            with (output/f'step-{step:04d}.json').open('x') as f:
                json.dump(row, f, sort_keys=True, indent=2)
                f.write('\n')
    result = dict(schema='q817-portable-identity-reproduction-v1', start=start, end=end,
        source_generator_sha256=PINS['eea_circuit_s835_exactwidth_dirty12.py'],
        n=256, qubits=571, aux_size=5, schedule_end=1616, raw_record_sha256=prefix.hexdigest(),
        per_step=rows, identity_transport=True, historical_reducer_invoked=False,
        canonical_Q=None, canonical_T=None, full9024=False)
    with (output/'receipt.json').open('x') as f:
        json.dump(result, f, sort_keys=True, indent=2)
        f.write('\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start', type=int, required=True)
    parser.add_argument('--end', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(Path(__file__).resolve().parent, args.output, args.start, args.end)
