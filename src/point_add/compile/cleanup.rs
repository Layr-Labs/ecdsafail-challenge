//! Uncompute an AND using X measurement when the target provably holds the
//! product of its two current controls. A fresh value ID denotes an unknown.
pub type Row = [u16; 4];
const EMPTY: u16 = u16::MAX;
const HISTORY: usize = 12;

#[derive(Copy, Clone, Eq, PartialEq)]
struct Term(u64, u64);
const ZERO: Term = Term(0, 0);
const ONE: Term = Term(1, 1);

fn product(a: u64, b: u64) -> Term {
    if a == 0 || b == 0 { return ZERO; }
    if a == b { return Term(1, a); }
    Term(a.min(b), a.max(b))
}

#[derive(Copy, Clone)]
struct Change { term: Term, before: u64 }
#[derive(Copy, Clone)]
struct Wire { value: u64, history: [Change; HISTORY], used: usize }

impl Wire {
    const ZERO: Self = Self { value: 0, history: [Change { term: ZERO, before: 0 }; HISTORY], used: 0 };
}

struct Frame { number: u64, start: usize }
struct Undo { q: u16, mark: u64, prior: Wire }

pub struct Cleanup {
    wires: Vec<Wire>,
    next_id: u64,
    started: bool,
    frames: Vec<Frame>,
    next_frame: u64,
    marks: Vec<u64>,
    undos: Vec<Undo>,
    changed: Vec<u16>,
    scratch: u16,
    pub measurements: u64,
    pub simpler_ccx: u64,
}

impl Cleanup {
    pub fn new(width: usize, scratch: u16) -> Self {
        assert!(scratch < EMPTY);
        Self {
            wires: vec![Wire::ZERO; width], marks: vec![0; width],
            next_id: 2, started: false, next_frame: 0, frames: Vec::new(),
            undos: Vec::new(), changed: Vec::new(), scratch, measurements: 0, simpler_ccx: 0,
        }
    }

    // Within PUSH, reason on the taken branch. Remember its entry state once
    // for each modified wire so POP can also account for the bypassed branch.
    fn remember(&mut self, q: u16) {
        if let Some(frame) = self.frames.last() {
            let i = usize::from(q);
            if self.marks[i] != frame.number {
                self.undos.push(Undo {q, mark: self.marks[i], prior: self.wires[i]});
                self.marks[i] = frame.number;
            }
        }
    }

    fn enter(&mut self) {
        self.next_frame += 1;
        self.frames.push(Frame {number: self.next_frame, start: self.undos.len()});
    }

    fn leave(&mut self) {
        let start = self.frames.pop().expect("unmatched POP").start;
        while self.undos.len() > start {
            let undo = self.undos.pop().unwrap();
            let i = usize::from(undo.q);
            if self.wires[i].value != undo.prior.value { self.changed.push(undo.q); }
            self.wires[i] = undo.prior;
            self.marks[i] = undo.mark;
        }
        // Equal exit/entry values keep their original proof on both branches.
        // Give each remaining wire a fresh name in the enclosing frame.
        while let Some(q) = self.changed.pop() { self.unknown(q); }
    }

    fn unknown(&mut self, q: u16) {
        self.remember(q);
        self.next_id += 1;
        let wire = &mut self.wires[usize::from(q)];
        wire.value = self.next_id;
        wire.used = 0;
    }

    fn zero(&mut self, q: u16) {
        self.remember(q);
        let wire = &mut self.wires[usize::from(q)];
        wire.value = 0;
        wire.used = 0;
    }

    // Return true when undoing a recorded AND on a previously zero wire.
    fn toggle(&mut self, q: u16, term: Term) -> bool {
        if term == ZERO { return false; }
        self.remember(q);
        let wire = &mut self.wires[usize::from(q)];
        if wire.used != 0 && wire.history[wire.used-1].term == term {
            wire.used -= 1;
            wire.value = wire.history[wire.used].before;
            return wire.value == 0 && term.0 > 1;
        }
        let before = wire.value;
        wire.value = if term.0 == 1 && before == 0 {
            term.1
        } else if term.0 == 1 && before == term.1 {
            0
        } else {
            self.next_id += 1;
            self.next_id
        };
        if wire.used == HISTORY { wire.used = 0; }
        wire.history[wire.used] = Change {term, before};
        wire.used += 1;
        false
    }

    pub fn push(&mut self, row: Row, mut emit: impl FnMut(Row)) {
        let [k, a, b, c] = row;
        let scratch = self.scratch;
        let collision = match k {
            18 | 6 | 7 | 12 => b == scratch,
            3..=5 => a == scratch || b == scratch,
            8 | 9 => c == scratch,
            15 => a == scratch,
            _ => false,
        };
        assert!(!collision, "measurement bit already in use");
        if matches!(k, 1 | 2 | 18) {
            assert!(!self.started, "late register declaration");
            if k == 2 { self.unknown(b); }
            emit(row);
            return;
        }
        self.started = true;
        match k {
            15 => self.enter(),
            16 => self.leave(),
            12 => self.zero(a),
            6 | 8 | 13 => {
                let target = match k {6 => a, 8 => b, _ => c};
                let guarded = k == 6 && b != EMPTY || k == 8 && c != EMPTY;
                if guarded {
                    self.unknown(target);
                } else {
                    let x = if k == 6 {1} else {self.wires[usize::from(a)].value};
                    let y = if k == 13 {self.wires[usize::from(b)].value} else {1};
                    let term = product(x, y);
                    let clean_and = self.toggle(target, term);
                    if k == 13 {
                        if term == ZERO {
                            self.simpler_ccx += 1;
                            return;
                        }
                        if term.0 == 1 {
                            self.simpler_ccx += 1;
                            if term == ONE { emit([6, c, EMPTY, EMPTY]); }
                            else { emit([8, if x == 1 {b} else {a}, c, EMPTY]); }
                            return;
                        }
                        if clean_and {
                            self.measurements += 1;
                            emit([12, c, scratch, EMPTY]);
                            emit([9, a, b, scratch]);
                            emit([4, scratch, EMPTY, EMPTY]);
                            return;
                        }
                    }
                }
            }
            3..=5 | 7 | 9 => (), // These gates preserve quantum basis values.
            _ => panic!("unsupported native gate {k}"),
        }
        emit(row);
    }

    pub fn finish(&self) { assert!(self.frames.is_empty() && self.undos.is_empty()); }
}
