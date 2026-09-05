"""Standalone public saved-cache transform. Attribution: gpt-5.

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
WITNESS = struct.Struct('<QQQQ')
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


def factor(left, right):
    """Implementation follows native pilot; verifier uses a separate set matcher."""
    if left[0] != 3 or right[0] != 3:
        return None
    p, q = left[1], right[1]
    if len(set(p+q)) != 4:
        return None
    if p[2] == q[2]:
        common = tuple(x for x in p[:2] if x in q[:2])
        if len(common) != 1:
            return None
        a = common[0]
        v = p[1] if p[0] == a else p[0]
        w = q[1] if q[0] == a else q[0]
        return 1, (pack(2, (w, v)), pack(3, (a, v, p[2])), pack(2, (w, v)))
    if (p[0] == q[0] and p[1] == q[1]) or (p[0] == q[1] and p[1] == q[0]):
        return 2, (pack(2, (p[2], q[2])), pack(3, p), pack(2, (p[2], q[2])))
    return None


def walk(path, meta, zstd, emit=None, emit_witness=None):
    """One record lookahead; no matching across steps or newly emitted gates."""
    all_in, all_out, all_witness = (hashlib.sha256() for _ in range(3))
    rows = []
    with frame(path, meta['records'], meta['step_start'], meta['step_end'], zstd) as (stream, header):
        for old in meta['per_step']:
            inp, out, wit = (hashlib.sha256() for _ in range(3))
            before, after, rules = Counter(), Counter(), Counter()
            pending = None
            output_index = 0

            def output(raw):
                nonlocal output_index
                kind = raw[0] & 15
                after[NAMES[kind]] += 1
                output_index += 1
                out.update(raw)
                all_out.update(raw)
                if emit is not None:
                    emit(raw)

            for index in range(old['records']):
                raw = stream.read(8)
                parsed = unpack(raw)
                before[NAMES[parsed[0]]] += 1
                inp.update(raw)
                all_in.update(raw)
                if pending is None:
                    pending = (index, raw, parsed)
                    continue
                match = factor(pending[2], parsed)
                if match is None:
                    output(pending[1])
                    pending = (index, raw, parsed)
                    continue
                rule, replacements = match
                witness = WITNESS.pack(old['step'], pending[0], output_index, rule)
                wit.update(witness)
                all_witness.update(witness)
                if emit_witness is not None:
                    emit_witness(witness)
                rules[str(rule)] += 1
                for replacement in replacements:
                    output(replacement)
                pending = None
            if pending is not None:
                output(pending[1])
            before = {k: before[k] for k in b.EXPECTED}
            after = {k: after[k] for k in b.EXPECTED}
            pairs = sum(rules.values())
            b.need(before == old['counts'] and after == {'x': before['x'],
                   'cx': before['cx']+2*pairs, 'ccx': before['ccx']-pairs}, 'step exact count delta')
            b.need(output_index == old['records']+pairs, 'step record delta')
            rows.append(dict(step=old['step'], counts=after, records=output_index,
                executed_toffoli=after['ccx'], baseline_counts=before, baseline_records=old['records'],
                baseline_raw_record_sha256=inp.hexdigest(), raw_record_sha256=out.hexdigest(),
                matched_pairs=pairs, rule_counts={k: rules[k] for k in ('1', '2')},
                witness_sha256=wit.hexdigest()))
    b.need(all_in.hexdigest() == meta['raw_record_sha256'], 'entire baseline raw hash')
    return dict(header_hex=header.hex(), baseline_raw_record_sha256=all_in.hexdigest(),
        raw_record_sha256=all_out.hexdigest(), witness_sha256=all_witness.hexdigest(),
        records=sum(r['records'] for r in rows), counts=b.counts(rows),
        matched_pairs=sum(r['matched_pairs'] for r in rows), per_step=rows)


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
    b.need(manifest['schema'] == 'q810-adjacent-cache-reproducer-manifest-v1'
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
        with target.open('xb') as raw:
            with zstd.ZstdCompressor(level=19, threads=0, write_checksum=True,
                    write_content_size=True).stream_writer(raw, size=24+8*profile['records'], closefd=False) as writer:
                writer.write(bytes.fromhex(profile['header_hex']))
                sink = BufferedSink(writer)
                second = walk(path, meta, zstd, sink.write)
                sink.flush()
        b.need(second == profile and digest(target) == row['candidate_compressed_sha256']
               and target.stat().st_size == row['candidate_compressed_bytes'], 'complete reproduced frame mismatch')
        b.need(digest(path) == row['baseline_compressed_sha256'], 'baseline changed')
        metadata = encoded(row['public_metadata'])
        b.need(hashlib.sha256(metadata).hexdigest() == row['public_metadata_sha256'], 'metadata pin')
        write_new(output/(name+'.json'), metadata)
        receipts.append(dict(file=name, compressed_sha256=digest(target),
            raw_record_sha256=profile['raw_record_sha256'], records=profile['records'], counts=profile['counts']))
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
