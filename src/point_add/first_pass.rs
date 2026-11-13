use std::io::Cursor;

type Row = [u16; 4];
const NONE: u16 = u16::MAX;

struct Table {
    bytes: Vec<u8>,
    pos: usize,
}

impl Table {
    fn decode(data: &[u8]) -> Self {
        Self { bytes: zstd::stream::decode_all(Cursor::new(data)).expect("rewrite table"), pos: 0 }
    }

    fn end(&self) -> bool { self.pos == self.bytes.len() }

    fn byte(&mut self) -> u8 {
        let value = self.bytes[self.pos];
        self.pos += 1;
        value
    }

    fn length(&mut self) -> usize {
        let mut result = 0;
        for shift in (0..=56).step_by(7) {
            let b = self.byte();
            result |= usize::from(b & 127) << shift;
            if b < 128 { return result; }
        }
        panic!("oversized rewrite interval");
    }

    fn wire(&mut self) -> u16 { u16::from_le_bytes([self.byte(), self.byte()]) }
}

pub struct FirstPass {
    mask: Table,
    merges: Table,
    remaining: usize,
    drop: bool,
    kept: usize,
    merge_at: Option<usize>,
    cnot: Row,
    joined: usize,
}

impl FirstPass {
    pub fn new(mask: &[u8], merges: &[u8]) -> Self {
        let mut mask = Table::decode(mask);
        let first = mask.length();
        let mut pass = Self {
            mask, merges: Table::decode(merges), remaining: first, drop: false,
            kept: 0, merge_at: None, cnot: [NONE; 4], joined: 0,
        };
        pass.next_merge();
        pass
    }

    fn next_merge(&mut self) {
        if self.merges.end() {
            self.merge_at = None;
            return;
        }
        let delta = self.merges.length();
        assert!(delta != 0 || self.joined == 0);
        self.merge_at = Some(self.merge_at.unwrap_or(0).checked_add(delta).expect("merge index"));
        let (a, b) = (self.merges.wire(), self.merges.wire());
        assert!(a < 646 && b < 646 && a != b);
        self.cnot = [8, a, b, NONE];
    }

    pub fn push(&mut self, row: Row, emit: &mut impl FnMut(Row)) {
        while self.remaining == 0 {
            self.remaining = self.mask.length();
            self.drop = !self.drop;
        }
        self.remaining -= 1;
        if self.drop { return; }
        if self.merge_at == Some(self.kept) {
            assert_eq!(row[0], 13);
            emit(self.cnot);
            emit(row);
            emit(self.cnot);
            self.joined += 1;
            self.next_merge();
        } else {
            emit(row);
        }
        self.kept += 1;
    }

    pub fn finish(self) -> (usize, usize) {
        assert!(self.remaining == 0 && self.mask.end() && self.merges.end() && self.merge_at.is_none());
        (self.kept, self.joined)
    }
}
