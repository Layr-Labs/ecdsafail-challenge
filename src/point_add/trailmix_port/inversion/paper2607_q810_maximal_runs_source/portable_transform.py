"""Standalone public maximal-run saved-cache transform. Attribution: gpt-5.

Requires the exact public baseline cache; this is not a point-adder generator.
No network access or private source loader is used.
"""
import argparse
from collections import Counter
import contextlib
import hashlib
import io
import json
from pathlib import Path
import struct

WORD = struct.Struct('<Q')
WITNESS = struct.Struct('<8Q')  # exact native interval/rule/fixed/saving witness
NAMES = {1: 'x', 2: 'cx', 3: 'ccx'}
MAX_FRAME = 128*1024**2
BLOCK = 65536
BASELINE_COMMIT = 'a7f329a7b4ee87b532a5b3eff4c9ca8bf4f4915b'

class Support:
    EXPECTED = {'ccx': 0, 'cx': 0, 'x': 0}
    @staticmethod
    def need(value, message):
        if not value:
            raise ValueError(message)
    @staticmethod
    def safe(path):
        path = Path(path)
        Support.need(path.is_absolute() and path.resolve() == path
                     and path.is_file() and not path.is_symlink(), 'unsafe file')
        return path
    @staticmethod
    def counts(rows):
        return {k: sum(r['counts'][k] for r in rows) for k in Support.EXPECTED}

b = Support

@contextlib.contextmanager
def frame(path, records, start, end, zstd):
    """Bounded reader; consume exact declared body plus EOF (no missing tail)."""
    expected = 24+8*records
    b.need(24 <= expected <= MAX_FRAME, 'frame size bound')
    with b.safe(path).open('rb') as raw:
        params = zstd.get_frame_parameters(raw.read(64))
        b.need(params.content_size == expected and params.window_size <= MAX_FRAME, 'zstd declared size/window')
        raw.seek(0)
        with zstd.ZstdDecompressor(max_window_size=MAX_FRAME).stream_reader(
                raw, read_size=16384, read_across_frames=True, closefd=False) as stream:
            with io.BufferedReader(stream, buffer_size=BLOCK) as buffered:
                header = buffered.read(24)
                b.need(header == b'P26EEA2\0'+struct.pack('<4I', 256, 564, start, end), 'numeric frame header')
                yield buffered, header
                b.need(buffered.read(1) == b'', 'extra numeric frame data')


def unpack(raw):
    b.need(len(raw) == 8, 'truncated record')
    word, = WORD.unpack(raw)
    kind = word & 15
    b.need(kind in NAMES and ((word >> 4) & 15) == kind and word >> (8+10*kind) == 0,
           'nonpositive or malformed primitive')
    operands = tuple((word >> (8+10*i)) & 1023 for i in range(kind))
    b.need(len(set(operands)) == kind and max(operands) < 564, 'aliased/out-of-range operand')
    return kind, operands


def pack(kind, operands):
    return WORD.pack(kind | (kind << 4) | sum(q << (8+10*i) for i, q in enumerate(operands)))


def replacement(kind, fixed, items):
    # Parity is valid because targets and controls remain mutually disjoint.
    odd = [q for q, count in Counter(items).items() if count % 2]
    if not odd:
        return []
    pivot = odd[0]
    if kind == 'control_xor':
        common, target = fixed
        ladder = [(q, pivot) for q in odd[1:]]
        middle = (common, pivot, target)
    else:
        ladder = [(pivot, q) for q in odd[1:]]
        middle = (*fixed, pivot)
    return ladder + [middle] + list(reversed(ladder))


def runs(ops):
    witnesses = []
    i = 0
    while i < len(ops):
        first = ops[i]
        if len(first) != 3:
            i += 1
            continue
        candidates = []
        # Two possible common controls, plus same-controls target fanout.
        for kind, fixed in [('control_xor', (first[0], first[2])),
                            ('control_xor', (first[1], first[2])),
                            ('target_fanout', tuple(sorted(first[:2])))]:
            j = i
            items = []
            while j < len(ops):
                q = ops[j]
                if len(q) != 3:
                    break
                if kind == 'control_xor':
                    common, target = fixed
                    if q[2] != target or common not in q[:2]:
                        break
                    item = q[1] if q[0] == common else q[0]
                else:
                    if tuple(sorted(q[:2])) != fixed:
                        break
                    item = q[2]
                assert item not in fixed
                items.append(item)
                j += 1
            if len(items) > 1:
                after = replacement(kind, fixed, items)
                saved = len(items) - sum(len(q) == 3 for q in after)
                candidates.append((saved, j-i, kind, fixed, items, after))
        if not candidates:
            i += 1
            continue
        saved, length, kind, fixed, items, after = max(candidates, key=lambda v: (v[0], v[1], -len(v[-1])))
        witnesses.append(dict(first=i, end=i+length, kind=kind, fixed=fixed, items=items,
                              ccx_saved=saved, added_cx=sum(len(q)==2 for q in after)))
        i += length
    return witnesses


class Kernel:
    replacement = staticmethod(replacement)
    runs = staticmethod(runs)


class Kernels:
    @staticmethod
    def transform_kernel():
        return Kernel


kernels = Kernels


def transform_step(raw, step, witness_start=0):
    """Bounded glue around the exact root kernels; ORIGINAL records only."""
    b.need(type(step) is int and 1 <= step <= 1616 and type(witness_start) is int
           and witness_start >= 0, 'step/witness scope')
    b.need(raw and len(raw)%8 == 0 and len(raw)//8 <= 196583, 'step byte bound')
    ops = [unpack(raw[i:i+8])[1] for i in range(0,len(raw),8)]
    kernel = kernels.transform_kernel()
    plans = kernel.runs(ops)
    output, witnesses = bytearray(), bytearray()
    rules, lengths = Counter(), Counter()
    cursor = removed = inserted = saved = added = duplicates = empty = 0
    for plan in plans:
        first, end = plan['first'], plan['end']
        b.need(cursor <= first < end <= len(ops) and end-first >= 2, 'original run partition')
        output.extend(raw[8*cursor:8*first])
        start_out = len(output)//8
        replacement = kernel.replacement(plan['kind'],plan['fixed'],plan['items'])
        for operands in replacement:
            record = pack(len(operands),operands)
            unpack(record)  # independently reject malformed emitted shape/aliases
            output.extend(record)
        rule = {'control_xor':1,'target_fanout':2}[plan['kind']]
        end_out = len(output)//8
        ccx_saved = end-first-sum(len(q)==3 for q in replacement)
        cx_added = sum(len(q)==2 for q in replacement)
        b.need(ccx_saved == plan['ccx_saved'] and cx_added == plan['added_cx'], 'kernel delta')
        witnesses.extend(WITNESS.pack(first,end,start_out,end_out,rule,*plan['fixed'],ccx_saved))
        rules[str(rule)] += 1; lengths[str(end-first)] += 1
        removed += end-first; inserted += len(replacement); saved += ccx_saved; added += cx_added
        duplicates += len(set(plan['items'])) != len(plan['items'])
        empty += not replacement
        cursor = end
    output.extend(raw[8*cursor:])
    before = {name:sum(len(op)==kind for op in ops) for kind,name in NAMES.items()}
    counts = Counter(NAMES[unpack(output[i:i+8])[0]] for i in range(0,len(output),8))
    after = {k:counts[k] for k in b.EXPECTED}
    b.need(after == dict(x=before['x'],cx=before['cx']+added,ccx=before['ccx']-saved)
           and len(output)//8 == len(ops)-removed+inserted, 'generic parity count identity')
    b.need(len(witnesses)==64*len(plans) and len(output)<=2*len(raw), 'step output bounds')
    row = dict(step=step,counts=after,records=len(output)//8,executed_toffoli=after['ccx'],
        baseline_counts=before,baseline_records=len(ops),baseline_raw_record_sha256=hashlib.sha256(raw).hexdigest(),
        raw_record_sha256=hashlib.sha256(output).hexdigest(),selected_runs=len(plans),raw_ccx_saved=saved,
        added_cx=added,removed_records=removed,inserted_records=inserted,
        rule_counts={k:rules[k] for k in ('1','2')},run_lengths=dict(sorted(lengths.items(),key=lambda p:int(p[0]))),
        max_run_length=max((int(n) for n in lengths),default=0),duplicate_groups=duplicates,empty_parity_groups=empty,
        witness_record_start=witness_start,witness_record_end=witness_start+len(plans),
        witness_sha256=hashlib.sha256(witnesses).hexdigest())
    return bytes(output),bytes(witnesses),row


def walk(path, meta, zstd, emit=None, emit_witness=None):
    """At most one source step plus its output; exact pinned step boundaries."""
    all_in, all_out, all_witness = (hashlib.sha256() for _ in range(3))
    rows = []
    witness_start = 0
    with frame(path,meta['records'],meta['step_start'],meta['step_end'],zstd) as (stream,header):
        for old in meta['per_step']:
            b.need(type(old['records']) is int and 0 < old['records'] <= 196583,'pinned step record bound')
            raw = stream.read(8*old['records'])
            b.need(len(raw)==8*old['records'],'truncated whole step')
            output,witness,row = transform_step(raw,old['step'],witness_start)
            b.need(row['baseline_counts']==old['counts'],'original step counts')
            all_in.update(raw);all_out.update(output);all_witness.update(witness)
            row.update(baseline_prefix_raw_sha256=all_in.hexdigest(),prefix_raw_record_sha256=all_out.hexdigest(),
                       witness_prefix_sha256=all_witness.hexdigest())
            if emit is not None: emit(output)
            if emit_witness is not None: emit_witness(witness)
            witness_start = row['witness_record_end']
            rows.append(row)
    b.need(all_in.hexdigest()==meta['raw_record_sha256'],'entire original raw hash')
    return dict(header_hex=header.hex(),baseline_raw_record_sha256=all_in.hexdigest(),
        raw_record_sha256=all_out.hexdigest(),witness_sha256=all_witness.hexdigest(),
        records=sum(r['records'] for r in rows),counts=b.counts(rows),selected_runs=witness_start,
        raw_ccx_saved=sum(r['raw_ccx_saved'] for r in rows),added_cx=sum(r['added_cx'] for r in rows),per_step=rows)


class BufferedSink:
    def __init__(self, writer):
        self.writer, self.pending = writer, bytearray()

    def write(self, data):
        self.pending.extend(data)
        if len(self.pending) >= BLOCK:
            self.flush()

    def flush(self):
        if self.pending:
            self.writer.write(self.pending)
            self.pending.clear()


def digest(path):
    h = hashlib.sha256()
    with b.safe(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()

def unique(pairs):
    out = {}
    for k, v in pairs:
        b.need(k not in out, 'duplicate JSON key')
        out[k] = v
    return out

def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True)+'\n').encode()

def load_json(path):
    return json.loads(b.safe(path).read_bytes(), object_pairs_hook=unique)

def write_new(path, raw):
    with path.open('xb') as stream:
        stream.write(raw)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-root', required=True, type=Path)
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--index', type=int)
    args = parser.parse_args()
    b.need(__debug__, 'assertions must remain enabled')
    manifest_path = args.manifest.resolve()
    b.need(digest(manifest_path) == args.manifest_sha256, 'manifest hash')
    manifest = load_json(manifest_path)
    b.need(manifest['schema'] == 'q810-maximal-runs-cache-reproducer-manifest-v1'
           and manifest['baseline_commit'] == BASELINE_COMMIT
           and digest(Path(__file__).resolve()) == manifest['transformer_sha256']
           and len(manifest['shards']) == 36, 'exact source/manifest scope')
    import zstandard as zstd
    b.need(zstd.__version__ == '0.23.0' and zstd.backend == 'cext'
           and zstd.ZSTD_VERSION == (1, 5, 6), 'qualified zstandard0.23/libzstd1.5.6 C extension required')
    baseline = args.baseline_root.resolve()
    output = args.output.absolute()
    b.need(output.parent.resolve() == output.parent and not output.exists()
           and not output.is_symlink() and not output.is_relative_to(baseline), 'fresh output outside baseline')
    selected = range(36) if args.index is None else (args.index,)
    b.need(all(0 <= i < 36 for i in selected), 'index0..35')
    b.need(digest(baseline/'aggregate_manifest.json') == manifest['baseline_aggregate_sha256'], 'baseline aggregate')
    output.mkdir()
    receipts = []
    for i in selected:
        row = manifest['shards'][i]
        first, last = i*45+1, min((i+1)*45, 1616)
        name = f'chunk-{first:04d}-{last:04d}.zst'
        b.need(row['file'] == name, 'fixed shard name')
        path = baseline/name
        b.need(digest(path) == row['baseline_compressed_sha256']
               and digest(baseline/(name+'.json')) == row['baseline_metadata_sha256'], 'baseline shard hashes')
        meta = load_json(baseline/(name+'.json'))
        b.need(meta['step_start'] == first and meta['step_end'] == last, 'baseline step boundaries')
        profile = walk(path, meta, zstd)
        b.need(profile == row['expected_profile'], 'complete derived profile differs')
        target = output/name
        witness_path = output/(name+'.witnesses.bin')
        with target.open('xb') as raw, witness_path.open('xb') as witnesses:
            with zstd.ZstdCompressor(level=19, threads=0, write_checksum=True,
                    write_content_size=True).stream_writer(raw, size=24+8*profile['records'], closefd=False) as writer:
                writer.write(bytes.fromhex(profile['header_hex']))
                sink, wsink = BufferedSink(writer), BufferedSink(witnesses)
                second = walk(path, meta, zstd, sink.write, wsink.write)
                sink.flush(); wsink.flush()
        b.need(second == profile and digest(target) == row['candidate_compressed_sha256']
               and target.stat().st_size == row['candidate_compressed_bytes'], 'complete reproduced frame mismatch')
        b.need(digest(witness_path) == profile['witness_sha256']
               and digest(witness_path) == row['candidate_witness_sha256']
               and witness_path.stat().st_size == row['candidate_witness_bytes'] == 64*profile['selected_runs'],
               'complete witness stream mismatch')
        b.need(digest(path) == row['baseline_compressed_sha256'], 'baseline changed')
        metadata = encoded(row['public_metadata'])
        b.need(hashlib.sha256(metadata).hexdigest() == row['public_metadata_sha256'], 'metadata pin')
        write_new(output/(name+'.json'), metadata)
        receipts.append(dict(file=name, compressed_sha256=digest(target),
            raw_record_sha256=profile['raw_record_sha256'], records=profile['records'], counts=profile['counts'],
            witness_sha256=profile['witness_sha256'], witness_bytes=witness_path.stat().st_size,
            raw_ccx_saved=profile['raw_ccx_saved'], selected_runs=profile['selected_runs']))
    if args.index is None:
        aggregate = encoded(manifest['public_aggregate'])
        b.need(hashlib.sha256(aggregate).hexdigest() == manifest['public_aggregate_sha256'], 'aggregate pin')
        write_new(output/'aggregate_manifest.json', aggregate)
    write_new(output/'reproduction-receipt.json', encoded(dict(
        status='EXACT_SELECTED_CACHE_FRAMES_REPRODUCED_NOT_ARITHMETIC_VALIDATION',
        source_sha256=digest(Path(__file__).resolve()), manifest_sha256=args.manifest_sha256,
        baseline_commit=BASELINE_COMMIT, selected_shards=len(receipts), shards=receipts,
        full9024=False, canonical_Q=None, canonical_T=None, new_model_or_challenge_draw=False)))

if __name__ == '__main__':
    main()
