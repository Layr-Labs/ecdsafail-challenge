//! Assemble assigned cuts in the graded post-relabel coordinate system.
use super::*;
use std::cell::Cell;

thread_local! { pub(super) static LOADER: Cell<usize> = const { Cell::new(usize::MAX) }; }
pub(super) const WIDTH: u16 = 631;
pub(super) const LENGTHS: [usize; 32] = [
    23371274,14,217586643,68156338,17,61903462,139633762,18,115733069,29674,
    257058535,14,37316495,249232523,28246954,953376,438118,14,218258931,65366697,
    18,76908469,29674,244891560,17,110554504,138595757,14,37316618,249234148,16073708,113940,
];
pub(super) const CUTS: &[(usize,usize)] = &[
    (0,1),(2,3),(4,6),(7,10),(11,11),(12,14),(15,17),(18,19),(20,23),(24,26),(27,27),(28,30),(31,31)
];

fn hybrid(mut donor: Vec<Row>, first: usize, scan: usize, trace: &[u8], edit: &[u8]) -> Vec<Row> {
    let mut pack = Pack::parse(&lzma::decode(include_bytes!("data/pack.lzma")).unwrap());
    i1::w4_apply(&mut pack);
    let piece = &pack.scans[scan];
    let mut map = pack.segs[pack.seg_of(piece.out)].map.clone();
    map.resize(647, NONE);
    map[646] = 633;
    let prefix_count = LENGTHS[first..pack.seg_of(piece.out)].iter().sum();
    donor.truncate(prefix_count);
    let expected = u64::from_le_bytes(edit[8..16].try_into().unwrap()) as usize;
    donor.reserve_exact(expected - prefix_count);
    let marks = [match scan {0 => 14400, 3 => 20890, 7 => 20920, _ => unreachable!()}, 24600, 26600];
    let mut pool = scan::Classical::new();
    for (cell, mark) in pool.cl.iter_mut().zip(marks) { cell.next = mark; }
    let native = traceplanes::decode(trace);
    let mut put = |r| donor.push(map_lanes(r,&map));
    LOADER.with(|mode| mode.set(scan));
    vm::TOP_BIT.with(|mode| mode.set(true));
    if scan == 0 {
        borrow_scan::run(&native, piece.bit0, &mut pool, &mut put, KG_ZERO[scan]);
    } else {
        opt_scan::run(&native, piece.bit0, &mut pool, &mut put, KG_ZERO[scan], true);
    }
    vm::TOP_BIT.with(|mode| mode.set(false));
    LOADER.with(|mode| mode.set(usize::MAX));
    b5gen::decode(&donor,edit)
}

fn cx(a:u16,b:u16) -> Row { [8,a,b,NONE] }
fn bprime(donor:&[Row]) -> Vec<Row> {
    let (walk, scan) = donor.split_at(LENGTHS[18]);
    let placed_walk = b5gen::decode(walk,include_bytes!("data/zi/walk18.b5"));
    let placed_scan = b5gen::decode(scan,include_bytes!("data/zi/Bp.b5"));
    let last = &scan[scan.len()-14..];
    assert!(last.iter().all(|r|r[0]==7));
    let joined = [[12,497,65001,NONE],cx(503,497),cx(497,503)].into_iter()
        .chain(placed_walk).chain([cx(498,214),cx(214,498),cx(498,214)])
        .chain(placed_scan).chain(last.iter().copied()).chain([[7,497,65001,NONE]]);
    let mut deletions = include_bytes!("data/zi/Bp-deletions.bin").chunks_exact(4)
        .map(|b| u32::from_le_bytes(b.try_into().unwrap()) as usize).peekable();
    let mut out = Vec::with_capacity(347345657);
    for (i,row) in joined.enumerate() {
        if deletions.next_if_eq(&i).is_none() { out.push(row); }
    }
    assert!(deletions.next().is_none());
    assert_eq!(out.len(),347345657);
    out
}

pub(super) fn emit(first: usize, mut donor: Vec<Row>) -> Vec<Row> {
    match first {
        0 => {
            // The parent never addresses 550. Both workspace cells start clean.
            let mut uses = 0;
            for r in &mut donor {
                let fields = if r[0]==2 {2..3} else {1..1+qubits(r[0])};
                for q in &mut r[fields] {
                    assert_ne!(*q,550);
                    if *q == 631 { *q = 550; uses += 1; }
                }
            }
            assert_eq!(uses,396);
            donor
        }
        2 => hybrid(donor,2,0,include_bytes!("data/zi/B15.trc"), include_bytes!("data/zi/Bhybrid.b5")),
        4 => b5gen::decode(&donor,include_bytes!("data/zi/Dfull.b5")),
        7 => fd::f(&donor),
        11 | 27 => {
            assert_eq!(donor.last().map(|r| (r[0],r[1])),Some((12,498)));
            if first == 27 {
                // The F′ output maps graded 248 to 180 and the virtual high
                // lane to 248. All three gates restore the complete permutation.
                donor.extend([cx(180,248),cx(248,180),cx(180,248)]);
            }
            let src = if first == 11 {180} else {179};
            donor.extend([cx(src,498),cx(498,src)]);
            donor
        }
        12 => hybrid(donor,12,3,include_bytes!("data/zi/I15.trc"),include_bytes!("data/zi/Ihybrid.b5")),
        15 => b5gen::decode(&donor,include_bytes!("data/zi/point15-17.b5")),
        18 => bprime(&donor),
        20 => fd::dp(&donor),
        24 => {
            let base = b5gen::decode(&donor,include_bytes!("data/fprime.b5"));
            drop(donor);
            b5gen::decode(&base,include_bytes!("data/zi/Fp-tuned.b5"))
        }
        28 => hybrid(donor,28,7,include_bytes!("data/zi/Ip15.trc"),include_bytes!("data/zi/Iphybrid.b5")),
        31 => {
            for r in &mut donor {
                let n=qubits(r[0]);
                for lane in &mut r[1..1+n] {
                    assert_ne!(*lane,598,"occupied I-prime exit port in closing segment");
                    if *lane==631 { *lane=598; }
                }
                if r[0]==2 {
                    assert_ne!(r[2],598);
                    if r[2]==631 {r[2]=598;}
                }
            }
            donor
        }
        _ => unreachable!()
    }
}

pub(super) fn fits(r: Row) -> bool {
    r[1..1+qubits(r[0])].iter().all(|&q| q<WIDTH) && (r[0]!=2 || r[2]<WIDTH)
}

// Keep only one decoded cut live while replacing the physical parents.
// Both builders use these same in-memory buffers.
struct PackedRows {
    count: usize,
    blocks: Vec<Vec<u8>>,
}
impl PackedRows {
    fn pack<S:Slot>(rows:&[S]) -> Self {
        let blocks = rows.chunks(1<<20).map(|chunk| {
            let mut bytes = Vec::with_capacity(chunk.len()*8);
            for slot in chunk {
                for word in slot.to_row() { bytes.extend_from_slice(&word.to_le_bytes()); }
            }
            zstd::bulk::compress(&bytes,1).expect("compress rows")
        }).collect();
        Self {count: rows.len(), blocks}
    }
    fn unpack<S:Slot>(self, out:&mut Vec<S>) {
        let start=out.len();
        for block in self.blocks {
            let bytes=zstd::bulk::decompress(&block,8<<20).expect("decompress rows");
            let raw=bytes.chunks_exact(8);
            assert!(raw.remainder().is_empty());
            out.extend(raw.map(|b| S::from_row(std::array::from_fn(|i| u16::from_le_bytes([b[2*i],b[2*i+1]])))));
        }
        assert_eq!(out.len()-start,self.count);
    }
}
pub(super) fn assemble<S: Slot>(mut parent: Vec<S>, n: usize) -> Vec<S> {
    assert_eq!(LENGTHS.iter().sum::<usize>(), n);
    parent.truncate(n);
    let mut inputs=Vec::new();
    for &(first,last) in CUTS.iter().rev() {
        let start=parent.len()-LENGTHS[first..=last].iter().sum::<usize>();
        inputs.push((first,PackedRows::pack(&parent[start..])));
        parent.truncate(start);
        parent.shrink_to_fit();
    }
    drop(parent);
    let mut outputs=Vec::new();
    let mut total=0;
    while let Some((first,input))=inputs.pop() {
        let mut raw=Vec::with_capacity(input.count);
        input.unpack(&mut raw);
        let assigned=emit(first,raw);
        // D's AL1 placement keeps 9 native unconditional SWAP records ([10,a,b,NONE]); the builder's Op conversion and
        // the post passes take no kind 10: lower each one exactly to CX(a,b) CX(b,a) CX(a,b).
        let assigned=if assigned.iter().any(|r|r[0]==10) {
            let mut v=Vec::with_capacity(assigned.len()+64);
            for r in assigned {
                if r[0]==10 { assert_eq!(r[3],NONE,"conditional SWAP"); v.extend([cx(r[1],r[2]),cx(r[2],r[1]),cx(r[1],r[2])]); }
                else { v.push(r); }
            }
            v
        } else { assigned };
        assert!(assigned.iter().copied().all(fits),"width at assigned cut {first}");
        total += assigned.len();
        outputs.push(PackedRows::pack(&assigned));
    }
    let mut out=Vec::with_capacity(total+TAIL);
    for packed in outputs {packed.unpack(&mut out);}
    out.resize(total+TAIL,S::empty());
    out
}
