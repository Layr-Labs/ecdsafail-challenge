// The original peephole pass is credited in README.md. This wrapper accepts
// native eight-byte records and keeps bounded chunks of the circuit in memory.
#[path="peephole.rs"]
mod peephole;

use std::env;
use std::io::{self, BufReader, BufWriter, Read, Write};
use self::peephole::Rows;

type Row = [u16; 4];
const EMPTY: u16 = u16::MAX;
const WIDTH: usize = 649;
pub const CHUNK: usize = 262_144;

struct Tape {
    rows: Vec<Row>,
    blocks: Vec<[Row; 3]>,
}

impl Rows for Tape {
    fn len(&self) -> usize { self.rows.len() }
    fn get(&self, i: usize) -> Row { self.rows[i] }
    fn set(&mut self, i: usize, row: Row) { self.rows[i] = row; }
    fn expand(&mut self, i: usize, block: [Row; 3]) {
        let j = u32::try_from(self.blocks.len()).unwrap();
        self.rows[i] = [peephole::BLOCK, j as u16, (j >> 16) as u16, EMPTY];
        self.blocks.push(block);
    }
    fn block(&self, i: usize) -> [Row; 3] {
        let r = self.rows[i];
        self.blocks[usize::from(r[1]) + (usize::from(r[2]) << 16)]
    }
}

impl Tape {
    fn flatten(&self) -> Vec<Row> {
        let mut out = Vec::with_capacity(self.rows.len() + self.blocks.len());
        for (i, &r) in self.rows.iter().enumerate() {
            match r[0] {
                peephole::TOMB => (),
                peephole::BLOCK => out.extend(self.block(i)),
                _ => out.push(r),
            }
        }
        out
    }
}

// a*b applied to two independent destinations t,u can be distributed by
// CX(t,u), CCX(a,b,t), CX(t,u). Move the first gate forward only while no
// operation writes either control or reads its target.
fn fanout(tape: &mut Tape) -> usize {
    let mut writes = [0; WIDTH];
    let mut reads = [0; WIDTH];
    let mut pending = vec![0; WIDTH*WIDTH];
    let mut barrier = 0;
    let mut saved = 0;
    for i in 0..tape.len() {
        let r = tape.get(i);
        let now = i + 1;
        match r[0] {
            6 if r[2] == EMPTY => writes[usize::from(r[1])] = now,
            8 if r[3] == EMPTY => {
                reads[usize::from(r[1])] = now;
                writes[usize::from(r[2])] = now;
            }
            13 => {
                let (a,b,u) = (usize::from(r[1]),usize::from(r[2]),usize::from(r[3]));
                let slot = a.min(b)*WIDTH + a.max(b);
                let prior = pending[slot];
                let mut combined = false;
                if prior > barrier && writes[a] <= prior && writes[b] <= prior {
                    let old = tape.get(prior-1);
                    let t = usize::from(old[3]);
                    if old[0] == 13 && t != u && reads[t] <= prior {
                        let cnot = [8, t as u16, u as u16, EMPTY];
                        tape.set(prior-1, [peephole::TOMB,0,EMPTY,EMPTY]);
                        tape.expand(i,[cnot,old,cnot]);
                        writes[t] = now;
                        pending[slot] = 0;
                        saved += 1;
                        combined = true;
                    }
                }
                if !combined { pending[slot] = now; }
                reads[a] = now;
                reads[b] = now;
                writes[u] = now;
            }
            _ => barrier = now,
        }
    }
    saved
}

pub fn stack_after(mut depth: usize, rows: &[Row]) -> usize {
    for r in rows {
        match r[0] {
            15 => depth += 1,
            16 => depth = depth.checked_sub(1).expect("unmatched condition pop"),
            _ => (),
        }
    }
    depth
}

pub fn optimize(data: Vec<Row>, entering: usize, leaving: usize, rounds: usize) -> (Vec<Row>, u64) {
    if !data.iter().any(|r| r[0] == 13) { return (data,0); }
    // A unique artificial bit stands for already captured enclosing masks.
    // It must not occur as a real operand. Permanent context boundaries
    // outside this chunk can therefore only make the optimization conservative.
    let synthetic = 65534;
    assert!(data.iter().all(|r| !r[1..].contains(&synthetic)));
    let mut rows = vec![[15,synthetic,EMPTY,EMPTY]; entering];
    rows.extend(data);
    rows.resize(rows.len()+leaving,[16,EMPTY,EMPTY,EMPTY]);
    let mut merges = 0;
    for _ in 0..rounds {
        let mut tape = Tape{rows,blocks:Vec::new()};
        let fans = fanout(&mut tape);
        merges += fans as u64;
        // Expose real gate dependencies before invoking the independent pass.
        let mut plain = Tape{rows:tape.flatten(),blocks:Vec::new()};
        let stats = peephole::pass(&mut plain);
        rows = plain.flatten();
        if fans == 0 && stats.removed_ccx() == 0 { break; }
    }
    rows.truncate(rows.len()-leaving);
    rows.drain(..entering);
    (rows,merges)
}

#[derive(Default)]
struct Counts { rows: u64, ccx_by_depth: Vec<u64>, depth: usize }
impl Counts {
    fn visit(&mut self, rows: &[Row]) {
        for r in rows {
            self.rows += 1;
            match r[0] {
                15 => self.depth += 1,
                16 => self.depth = self.depth.checked_sub(1).expect("invalid condition"),
                13 => {
                    if self.ccx_by_depth.len() <= self.depth { self.ccx_by_depth.resize(self.depth+1,0); }
                    self.ccx_by_depth[self.depth] += 1;
                }
                _ => (),
            }
        }
    }
}

fn main() -> io::Result<()> {
    let rounds = env::args().nth(1).map(|arg| arg.parse().expect("integer pass count")).unwrap_or(2);
    let chunk = env::args().nth(2).map(|arg| arg.parse().expect("integer chunk size")).unwrap_or(CHUNK);
    assert!(rounds > 0 && chunk > 0 && chunk <= 4_194_304);
    let mut input = BufReader::new(io::stdin().lock());
    let mut output = BufWriter::with_capacity(1<<20,io::stdout().lock());
    let (mut before,mut after) = (Counts::default(),Counts::default());
    let mut fans = 0u64;
    let mut buffer = vec![0u8;8*chunk];
    loop {
        let mut n = 0;
        while n < buffer.len() {
            match input.read(&mut buffer[n..])? { 0 => break, len => n += len }
        }
        if n == 0 { break; }
        assert_eq!(n%8,0,"partial native gate record");
        let rows: Vec<Row> = buffer[..n].chunks_exact(8).map(|r|
            std::array::from_fn(|i| u16::from_le_bytes([r[i*2],r[i*2+1]]))).collect();
        let entering = before.depth;
        let leaving = stack_after(entering,&rows);
        before.visit(&rows);
        let (rewritten,merged) = optimize(rows,entering,leaving,rounds);
        fans += merged;
        after.visit(&rewritten);
        assert_eq!(after.depth,leaving,"condition nesting changed");
        for row in rewritten { for field in row { output.write_all(&field.to_le_bytes())?; } }
    }
    assert_eq!(before.depth,0,"incomplete circuit");
    output.flush()?;
    eprintln!("{{\"inputRecords\":{},\"outputRecords\":{},\"inputCCXByDepth\":{:?},\"outputCCXByDepth\":{:?},\"fanoutMerges\":{}}}",
        before.rows,after.rows,before.ccx_by_depth,after.ccx_by_depth,fans);
    Ok(())
}
