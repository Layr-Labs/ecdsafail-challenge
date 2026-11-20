//! Reconstruct the native scan event bytes before invoking the graded expanders.
//! Short events of the same opcode and length are stored in delta-coded columns.
use super::lzma;

fn take<'a>(data: &mut &'a [u8], n: usize) -> &'a [u8] {
    let (out, rest) = data.split_at(n);
    *data = rest;
    out
}
fn word(data: &mut &[u8]) -> usize {
    u32::from_le_bytes(take(data, 4).try_into().unwrap()) as usize
}
fn varint(data: &mut &[u8]) -> usize {
    let mut n = 0;
    for shift in (0..32).step_by(7) {
        let b = take(data, 1)[0];
        n |= ((b & 127) as usize) << shift;
        if b < 128 { return n; }
    }
    panic!("invalid trace length");
}
struct Group {
    op: u8,
    width: usize,
    rows: Vec<u8>,
    position: usize,
}
pub(super) fn decode(blob: &[u8]) -> Vec<u8> {
    let plain = lzma::decode(blob).expect("scan trace columns");
    let mut data = plain.as_slice();
    assert_eq!(take(&mut data, 4), b"TPL1");
    let groups = word(&mut data);
    let events = word(&mut data);
    let n = word(&mut data);
    let mut order = take(&mut data, n);
    let mut table = Vec::with_capacity(groups);
    let mut capacity = events;
    for _ in 0..groups {
        let op = take(&mut data, 1)[0];
        let width = take(&mut data, 1)[0] as usize;
        let len = word(&mut data);
        let src = take(&mut data, len);
        let rows = if width == 129 { src.to_vec() } else {
            let mut rows = vec![0; len];
            if width == 0 { assert_eq!(len, 0); } else {
                assert_eq!(len % width, 0);
                let count = len/width;
                for j in 0..width {
                    let mut value = 0u8;
                    for k in 0..count {
                        value = value.wrapping_add(src[j*count+k]);
                        rows[k*width+j] = value;
                    }
                }
            }
            rows
        };
        capacity += len;
        table.push(Group { op, width, rows, position: 0 });
    }
    assert!(data.is_empty());
    let mut output = Vec::with_capacity(capacity);
    for _ in 0..events {
        let g = &mut table[varint(&mut order)];
        let mut body = &g.rows[g.position..];
        let len = if g.width == 129 { varint(&mut body) } else { g.width };
        output.push(g.op);
        output.extend_from_slice(take(&mut body, len));
        g.position = g.rows.len()-body.len();
    }
    assert!(order.is_empty() && table.iter().all(|g| g.position == g.rows.len()));
    output
}

