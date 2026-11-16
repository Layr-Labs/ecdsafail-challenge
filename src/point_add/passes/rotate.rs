//! Choose an equivalent cyclic shift of a restored dirty-ancilla ladder.
use super::{Controls, Ladder, Row, NONE};

fn is_involution(row: Row) -> bool {
    let [kind, _, b, c] = row;
    kind == 13 || (kind == 8 && c == NONE) || (kind == 6 && b == NONE)
}

fn push_reduced(output: &mut Vec<Row>, row: Row) {
    if is_involution(row) && output.last() == Some(&row) {
        output.pop();
    } else {
        output.push(row);
    }
}

fn shift_index(half: usize, start: usize, reverse: bool, offset: usize) -> usize {
    if reverse { (start + half - offset % half) % half } else { (start + offset) % half }
}

fn best_shift(half: &[Row], left: &[Row], right: &[Row]) -> (usize, bool) {
    let h = half.len();
    let mut best = (0, false);
    let mut score = 0;
    for reverse in [false, true] {
        for start in 0..h {
            let at = |offset| half[shift_index(h, start, reverse, offset)];
            let mut l = 0usize;
            while l < left.len().min(2*h) && left[left.len()-l-1] == at(l) { l += 1; }
            let mut r = 0usize;
            while r < right.len().min(2*h-l) && right[r] == at(2*h-r-1) { r += 1; }
            if l+r > score {
                best = (start, reverse);
                score = l+r;
            }
        }
    }
    best
}

pub struct Rotation {
    decoder: Ladder,
    block: usize,
    rows: Vec<Row>,
    reduced: Vec<Row>,
    pub recognized: u64,
    pub rotated: u64,
    pub saved: u64,
    pub removed: u64,
}
impl Rotation {
    pub fn new(width: usize, block: usize) -> Self {
        Self { decoder: Ladder::new(width,block), block, rows:Vec::with_capacity(block),
               reduced:Vec::with_capacity(block), recognized:0, rotated:0, saved:0, removed:0 }
    }
    pub fn push(&mut self, row: Row, emit: &mut impl FnMut(Row)) {
        self.rows.push(row);
        if self.rows.len() == self.block { self.finish(emit); }
    }
    pub fn finish(&mut self, emit: &mut impl FnMut(Row)) {
        if self.rows.is_empty() {return;}
        if !self.rows.iter().any(|r|r[0]==13) {
            self.rows.drain(..).for_each(emit);
            return;
        }
        for row in &mut self.rows {
            if row[0] == 13 && row[1] > row[2] {row.swap(1,2);}
        }
        let count = self.rows.iter().filter(|r|r[0]==13).count();
        let atoms = self.decoder.lift(&self.rows);
        for atom in atoms {
            let rows = &self.rows[atom.start..atom.end];
            if let Controls::Ladder { sites, dirty } = &atom.controls {
                // The original recognizer also accepts repeated controls. Keep this pass
                // restricted to the distinct-site ladder covered by the commutation proof.
                let k = sites.len();
                let classical_form = k>=3 && dirty.len()==k-2 && rows.len()==4*(k-2);
                if classical_form {
                    self.recognized+=1;
                    let half = &rows[..rows.len()/2];
                    let (start,rev) = best_shift(half, &self.reduced, &self.rows[atom.end..]);
                    self.rotated += u64::from(start!=0 || rev);
                    for i in 0..rows.len() {
                        let row = half[shift_index(half.len(), start,rev,i)];
                        push_reduced(&mut self.reduced,row);
                    }
                    continue;
                }
            }
            for &row in rows { push_reduced(&mut self.reduced,row); }
        }
        let after=self.reduced.iter().filter(|r|r[0]==13).count();
        self.saved += (count-after) as u64;
        self.removed += (self.rows.len()-self.reduced.len()) as u64;
        self.rows.clear();
        self.reduced.drain(..).for_each(emit);
    }
}
