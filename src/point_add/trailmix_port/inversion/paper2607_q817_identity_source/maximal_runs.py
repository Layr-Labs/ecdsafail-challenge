#!/usr/bin/env python3
"""Portable typed Q817 maximal-run postprocessor. Model: gpt-5."""
from collections import Counter
import argparse
import hashlib
import io
import json
from pathlib import Path
import stat
import struct
import sys
from types import SimpleNamespace

sys.dont_write_bytecode=True
WORD=struct.Struct('<Q')
WITNESS=struct.Struct('<8Q')
NAMES={1:'x',2:'cx',3:'ccx',4:'z',5:'cz',6:'swap',7:'clean_c3x_mbu'}
ARITY={1:1,2:2,3:3,4:1,5:2,6:2,7:5}
MAX_STEP_BYTES=4*1024**2
MAX_WITNESS_BYTES=8*1024**2
BLOCK=65536
GENERATOR_SHA='b7ff97de22b36450d6fee3f267be62a00d8be24f6988849655e1fea04c9374d2'

def need(ok,code):
    if not ok:raise ValueError(code)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def encoded(value):return (json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
def read(path,maximum):
    before=path.lstat()
    need(path.resolve()==path and stat.S_ISREG(before.st_mode) and before.st_size<=maximum,'regular bounded input')
    raw=path.read_bytes();after=path.lstat()
    ident=lambda s:(s.st_dev,s.st_ino,s.st_mode,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
    need(ident(before)==ident(after) and len(raw)==before.st_size,'input changed')
    return raw
def unique(rows):
    result={}
    for k,v in rows:need(k not in result,'duplicate JSON key');result[k]=v
    return result
def decode(raw):return json.loads(raw,object_pairs_hook=unique)

# Exact pure kernels and typed glue copied from their disclosed original sources.
# b/kernels are only compatibility namespaces, not imported campaign modules.
b=SimpleNamespace(need=need,MAX_STEP_BYTES=MAX_STEP_BYTES,MAX_WITNESS_BYTES=MAX_WITNESS_BYTES)

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


def unpack(raw):
    b.need(len(raw) == 8, 'truncated record')
    word, = WORD.unpack(raw)
    kind = word & 15
    b.need(kind in NAMES and ((word >> 4) & 15) == ARITY[kind] and word >> (8+10*ARITY[kind]) == 0,
           'unknown or malformed typed primitive')
    operands = tuple((word >> (8+10*i)) & 1023 for i in range(ARITY[kind]))
    b.need(len(set(operands)) == ARITY[kind] and max(operands) < 571, 'aliased/out-of-range operand')
    return kind, operands


def pack(kind, operands):
    b.need(kind in ARITY and len(operands)==ARITY[kind] and all(type(q) is int and 0<=q<571 for q in operands)
           and len(set(operands))==len(operands), 'typed pack operands')
    return WORD.pack(kind | (ARITY[kind] << 4) | sum(q << (8+10*i) for i, q in enumerate(operands)))


def transform_step(raw, step, witness_start=0):
    """Bounded glue around the exact root kernels; ORIGINAL records only."""
    b.need(type(step) is int and 1 <= step <= 1616 and type(witness_start) is int
           and witness_start >= 0, 'step/witness scope')
    b.need(raw and len(raw)%8 == 0 and len(raw) <= b.MAX_STEP_BYTES, 'step byte bound')
    typed = [unpack(raw[i:i+8]) for i in range(0,len(raw),8)]
    # Only explicit kind3 records enter the pure positive kernel. Every other
    # kind is an opaque one-word barrier, including kind7's five-operand MBU.
    ops = [q if kind==3 else () for kind,q in typed]
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
    before_hist = Counter(kind for kind,_ in typed)
    before = {name:before_hist[kind] for kind,name in NAMES.items()}
    counts = Counter(NAMES[unpack(output[i:i+8])[0]] for i in range(0,len(output),8))
    after = {k:counts[k] for k in NAMES.values()}
    b.need(after == dict(before, cx=before['cx']+added, ccx=before['ccx']-saved)
           and len(output)//8 == len(ops)-removed+inserted, 'generic parity count identity')
    b.need(len(witnesses)==64*len(plans) and len(witnesses)<=b.MAX_WITNESS_BYTES
           and len(output)<=2*len(raw) and len(output)<=b.MAX_STEP_BYTES, 'step output bounds')
    row = dict(step=step,counts=after,records=len(output)//8,executed_toffoli=after['ccx']+2*after['clean_c3x_mbu'],
        baseline_counts=before,baseline_records=len(ops),baseline_raw_record_sha256=hashlib.sha256(raw).hexdigest(),
        raw_record_sha256=hashlib.sha256(output).hexdigest(),selected_runs=len(plans),raw_ccx_saved=saved,
        added_cx=added,removed_records=removed,inserted_records=inserted,
        rule_counts={k:rules[k] for k in ('1','2')},run_lengths=dict(sorted(lengths.items(),key=lambda p:int(p[0]))),
        max_run_length=max((int(n) for n in lengths),default=0),duplicate_groups=duplicates,empty_parity_groups=empty,
        witness_record_start=witness_start,witness_record_end=witness_start+len(plans),
        witness_sha256=hashlib.sha256(witnesses).hexdigest())
    return bytes(output),bytes(witnesses),row


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


kernels=SimpleNamespace(transform_kernel=lambda:SimpleNamespace(replacement=replacement,runs=runs))

def check_metadata(meta):
    need(meta['schema']=='q817-maximal-runs-public-chunk-v1','public chunk schema')
    start,end=meta['step_start'],meta['step_end']
    need(type(start) is type(end) is int and 1<=start<=end<=1616
         and (start-1)%45==0 and end==min(start+44,1616),'fixed shard range')
    need(meta['file']==f'chunk-{start:04d}-{end:04d}.zst'
         and meta['n']==256 and meta['qubits']==571 and meta['aux_size']==5
         and meta['record_bytes']==8 and meta['schedule_end']==1616,'fixed source interface')
    need(meta['source_generator_sha256']==GENERATOR_SHA
         and meta['source_postprocessor_sha256']==sha(read(Path(__file__).resolve(),1024**2)),'public source pins')
    need([r['step'] for r in meta['per_step']]==list(range(start,end+1)),'fixed step census')
    return b'P26EEA2\0'+struct.pack('<4I',256,571,start,end)

def walk_identity(identity,meta,emit=None,emit_witness=None):
    all_in,all_out,all_witness=(hashlib.sha256() for _ in range(3))
    rows=[];witness_start=0
    for expected in meta['per_step']:
        step=expected['step']
        raw=read(identity/f'step-{step:04d}.records.bin',MAX_STEP_BYTES)
        output,witness,row=transform_step(raw,step,witness_start)
        need(row['baseline_raw_record_sha256']==expected['baseline_raw_record_sha256']
             and row['baseline_records']==expected['baseline_records']
             and row['baseline_counts']==expected['baseline_counts'],'original identity step source hash/count')
        all_in.update(raw);all_out.update(output);all_witness.update(witness)
        row.update(baseline_prefix_raw_sha256=all_in.hexdigest(),
                   prefix_raw_record_sha256=all_out.hexdigest(),
                   witness_prefix_sha256=all_witness.hexdigest())
        need(row==expected,'exact transformed step and witness metadata')
        if emit is not None:emit(output)
        if emit_witness is not None:emit_witness(witness)
        witness_start=row['witness_record_end'];rows.append(row)
    need(all_in.hexdigest()==meta['baseline_raw_record_sha256']
         and all_out.hexdigest()==meta['raw_record_sha256']
         and all_witness.hexdigest()==meta['witness_sha256'],'whole identity/candidate/witness hashes')
    return dict(per_step=rows,baseline_raw_record_sha256=all_in.hexdigest(),
        raw_record_sha256=all_out.hexdigest(),witness_sha256=all_witness.hexdigest())

def reproduce(identity,metadata,output):
    need(__debug__ and sys.version_info[:2]==(3,11),'Python3.11 with assertions')
    identity=identity.resolve();metadata=metadata.resolve();output=output.absolute()
    need(identity.is_dir() and output.resolve()==output
         and not output.exists() and not output.is_symlink(),'new output directory required')
    raw_meta=read(metadata,4*1024**2);meta=decode(raw_meta);header=check_metadata(meta)
    old=decode(read(identity/'receipt.json',4*1024**2))
    need(old['schema']=='q817-portable-identity-reproduction-v1'
         and old['source_generator_sha256']==GENERATOR_SHA and old['identity_transport'] is True
         and old['start']==meta['step_start'] and old['end']==meta['step_end'],'original identity reproduction receipt')
    # Import only at explicit reproduction; no generator, private settings or draw.
    import zstandard
    need(zstandard.__version__=='0.23.0' and zstandard.backend=='cext'
         and zstandard.ZSTD_VERSION==(1,5,6),'zstandard0.23.0 cext libzstd1.5.6 required')
    first=walk_identity(identity,meta)
    expected_size=24+8*meta['records']
    need(expected_size<=128*1024**2 and meta['records']==sum(r['records'] for r in meta['per_step']),'declared frame records')
    output.mkdir(mode=0o700)
    target=output/meta['file'];witness_path=output/(meta['file']+'.witnesses.bin')
    with target.open('xb') as raw,witness_path.open('xb') as witnesses:
        compressor=zstandard.ZstdCompressor(level=19,threads=0,write_checksum=True,write_content_size=True)
        with compressor.stream_writer(raw,size=expected_size,closefd=False) as compressed:
            compressed.write(header)
            sink,wsink=BufferedSink(compressed),BufferedSink(witnesses)
            second=walk_identity(identity,meta,sink.write,wsink.write)
            sink.flush();wsink.flush()
        need(second==first,'two unchanged input passes')
    actual=read(target,16*1024**2)
    need(sha(actual)==meta['compressed_sha256'] and len(actual)==meta['compressed_bytes'],'exact compressed candidate bytes')
    need(sha(read(witness_path,128*1024**2))==meta['witness_sha256'],'exact witness output')
    need(read(metadata,4*1024**2)==raw_meta,'metadata changed')
    result=dict(schema='q817-portable-maximal-runs-reproduction-v1',
        status='EXACT_SOURCE_BOUND_RAW_AND_COMPRESSED_BYTES_REPRODUCED_NOT_WHOLE_VALIDATED',
        metadata_sha256=sha(raw_meta),source_postprocessor_sha256=meta['source_postprocessor_sha256'],
        source_generator_sha256=GENERATOR_SHA,start=meta['step_start'],end=meta['step_end'],
        file=meta['file'],compressed_sha256=sha(actual),raw_record_sha256=meta['raw_record_sha256'],
        witness_sha256=meta['witness_sha256'],counts=meta['counts'],records=meta['records'],
        nonkind3_opaque_boundaries_preserved=True,original_identity_generator_reexecuted_here=False,
        new_challenge_or_measurement_draw=False,canonical_Q=None,canonical_T=None,full9024=False)
    with (output/'receipt.json').open('xb') as stream:stream.write(encoded(result))
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--identity',type=Path,required=True)
    parser.add_argument('--metadata',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    print(encoded(reproduce(args.identity,args.metadata,args.output)).decode(),end='')
