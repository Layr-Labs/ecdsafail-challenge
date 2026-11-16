//! Raw 95b048 body, rebuilt from the base builder's own stream (the history), GIRS patch blocks (data/patch.girs) and
//! three scans emitted by code from their traces (E0, F18, F'17).
//! Block b is decoded against `base[HIST[b].0 .. HIST[b].0 + HIST[b].1]` (copy tokens address history, then the block's own output).
use super::gir;
use super::post_pass::R8;
use super::Row;

const HIST: [(usize, usize); 16] = [(0, 23371274), (23371274, 308050643), (0, 0), (0, 0), (576918852, 18), (576918870, 400428080), (977346950, 18), (977346968, 311794263), (1289141231, 1391484), (1290532715, 283504659), (0, 0), (2138127630, 16), (2138127646, 234045784), (0, 0), (2372173430, 305402772), (2677576202, 114036)];
/// records of the raw stream without its 96-row tail
pub const BODY_ROWS: usize = 2_413_828_529;
static PATCH: &[u8] = include_bytes!("data/patch.girs");

#[derive(Clone, Copy)]
enum Piece { Patch(usize), E0, F18, Fp17, E1, E5 }
use Piece::*;
/// raw order: patch blocks are numbered in container order
const PLAN: [Piece; 21] = [Patch(0), Patch(1), E0, Patch(2), E1, Patch(3), Patch(4), Patch(5), F18, Patch(6), Patch(7), Patch(8), Patch(9), E5, Patch(10), Patch(11), Patch(12), Fp17, Patch(13), Patch(14), Patch(15)];

fn scan_rows(p: Piece) -> Vec<Row> {
    let (trc, rows): (&[u8], usize) = match p { E0 => (include_bytes!("data/e0.trc.lzma"), 55_234_529), F18 => (include_bytes!("data/f18.trc.lzma"), 276_878_180), Fp17 => (include_bytes!("data/fp17.trc.lzma"), 154_383_757), _ => unreachable!() };
    let tr = super::lzma::decode(trc).expect("scan trace");
    let mut out: Vec<Row> = Vec::with_capacity(rows);
    match p {
        E0 => super::e0::emit(&tr, include_bytes!("e0/scan.map"), 249, &mut out),
        F18 => super::f18::emit(&tr, include_bytes!("f18/map.bin"), 235, &mut out),
        _ => super::fp17::emit(&tr, include_bytes!("fp17/map.bin"), 231, &mut out),
    }
    assert!(out.len() == rows, "scan rows");
    out
}

pub fn raw_body() -> Vec<R8> {
    let base: Vec<Row> = super::build_slots::<Row>(false);
    let g = gir::Girs::open(PATCH);
    assert!(g.blocks.len() == HIST.len());
    let mut body: Vec<R8> = Vec::with_capacity(BODY_ROWS + 96);
    let mut buf: Vec<Row> = Vec::new();
    for p in PLAN.iter() {
        match *p {
            Patch(b) => { let (f, n) = HIST[b]; g.decode_hist(b, &base[f..f + n], &mut buf); body.extend(buf.iter().map(|&r| R8(r))); }
            E1 => { let mut rows: Vec<Row> = Vec::with_capacity(215_702_819); super::e1::emit(&mut rows); body.extend(rows.iter().map(|&r| R8(r))); }
            E5 => { let mut rows: Vec<Row> = Vec::with_capacity(370_484_040); super::e5::emit(&mut rows); body.extend(rows.iter().map(|&r| R8(r))); }
            s => { let rows = scan_rows(s); body.extend(rows.iter().map(|&r| R8(r))); }
        }
    }
    drop(base);
    assert!(body.len() == BODY_ROWS + 96, "raw length");
    body.truncate(BODY_ROWS);
    body
}

/// the body after the builder's three peephole passes (the "common peepholes" of the pipeline)
pub fn prepped_body() -> Vec<R8> {
    let mut body = raw_body();
    let n = body.len();
    let m = super::peephole(&mut body, n);
    let m = super::neg_controls(&mut body, m);
    let m = super::peephole(&mut body, m);
    body.truncate(m);
    body.shrink_to_fit();
    body
}
