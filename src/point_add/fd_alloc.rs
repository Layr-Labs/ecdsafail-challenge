//! The unannotated AL1 assignment used by the pinned cuts. Both passes use
//! the same structural machine as lanealloc. Only the rewrite stays in memory.
use super::fd_machine::{operands, Frame, Machine, Row, N};
use std::collections::BTreeSet;

const WIDTH: usize = 631;
const WIRES: usize = 640;
const INF: u32 = u32::MAX;

struct Colours {
    loc: [usize; WIRES],
    owner: [usize; WIDTH],
    free: BTreeSet<usize>,
    future: [u32; WIDTH],
    preferred: usize,
}

impl Colours {
    fn best(&self, lane: usize, end: u32) -> usize {
        if lane < self.preferred && self.free.contains(&lane) && self.future[lane] >= end {
            return lane;
        }
        *self.free.iter().max_by_key(|&&c| (self.future[c] >= end,
            c < self.preferred, std::cmp::Reverse(c))).expect("free operand")
    }
    fn claim(&mut self, l: usize, c: usize) {
        assert!(self.free.remove(&c));
        self.loc[l] = c;
        self.owner[c] = l;
    }
    fn release(&mut self, l: usize) {
        let c = self.loc[l];
        self.loc[l] = usize::MAX;
        self.owner[c] = usize::MAX;
        self.free.insert(c);
    }
    fn relocate(&mut self, l: usize, c: usize, m: &Machine, out: &mut impl FnMut(Row)) {
        let old = self.loc[l];
        assert!(m.move_runs_where_live(l));
        out([8,old as u16,c as u16,N]);
        out([8,c as u16,old as u16,N]);
        self.release(l);
        self.claim(l,c);
    }
}

pub(super) fn assign(rows: &mut Vec<Row>, start: usize, frame: &Frame,
                     entry: &[usize], exit: &[usize], peak: usize, moves: usize) {
    let n = rows.len() - start;
    let mut machine = Machine::new(WIRES, frame, true);
    let mut ends: Vec<_> = machine.q.iter().map(|&v| (v != 0).then_some(0)).collect();
    let mut deaths = vec![Vec::new(); WIRES];
    let mut cached = 0;
    const CACHE_LIMIT: usize = 8_000_000;
    for (i,&r) in rows[start..].iter().enumerate() {
        for lane in machine.step(r).lanes {
            if lane == N {continue;}
            let l = lane as usize;
            if machine.q[l] != 0 {
                ends[l].get_or_insert(i as u32);
            } else if ends[l].take().is_some() && cached < CACHE_LIMIT {
                deaths[l].push(i as u32);
                cached += 1;
                if cached == CACHE_LIMIT {deaths = vec![Vec::new(); WIRES];}
            }
        }
    }
    let mut pool = Colours { loc: [usize::MAX; WIRES], owner: [usize::MAX; WIDTH],
        free: (0..WIDTH).collect(), future: [INF; WIDTH], preferred: peak };
    for (l,birth) in ends.iter().enumerate() {
        if let Some(p) = birth {
            pool.future[exit[l]] = *p;
            pool.preferred = pool.preferred.max(exit[l]+1);
            if cached < CACHE_LIMIT {deaths[l].push(n as u32);}
        }
    }
    for &l in &frame.live {
        pool.claim(l,entry[l]);
        pool.preferred = pool.preferred.max(entry[l]+1);
    }
    // Leave exactly the maximum insertion space in front of the reader.
    // Non-move output never expands. This permits a single shared Vec.
    let gap = 2*moves;
    if gap > 0 {
        rows.reserve_exact(gap);
        rows.resize(start+n+gap,[0;4]);
        rows.copy_within(start..start+n,start+gap);
    }
    let mut machine = Machine::new(WIRES, frame, true);
    let mut written = start;
    for i in 0..n {
        let r = rows[start+gap+i];
        let effect = machine.step(r);
        let pos = i as u32;
        let mut put = |r| {rows[written]=r; written+=1;};
        if !effect.noop {
            let mut renamed = false;
            if r[0] == 10 {
                for (a,b) in [(r[1],r[2]),(r[2],r[1])] {
                    let (a,b)=(a as usize,b as usize);
                    let c=pool.loc[a];
                    if c!=usize::MAX && pool.loc[b]==usize::MAX && machine.q[a]==0 {
                        pool.release(a);pool.claim(b,c);renamed=true;break;
                    }
                }
            }
            if !renamed {
                let mut row=r;
                assert_ne!(r[0],2,"bracket contains a register declaration");
                for (j,&l) in operands(&r).iter().enumerate() {
                    let l=l as usize;
                    if pool.loc[l]==usize::MAX {
                        let ds=&deaths[l];
                        let c = if ends[l]==Some(pos) && machine.q[l]!=0 {exit[l]} else {
                            let end=if machine.q[l]==0 {pos+1} else {
                                ds.get(ds.partition_point(|&d|d<=pos)).copied().unwrap_or(INF)
                            };
                            pool.best(l,end)
                        };
                        let other=pool.owner[c];
                        if other!=usize::MAX {
                            let spare=pool.best(other,pos);
                            pool.relocate(other,spare,&machine,&mut put);
                        }
                        pool.claim(l,c);
                    }
                    row[j+1]=pool.loc[l] as u16;
                }
                put(row);
            }
        }
        for &q in operands(&r) {
            let l=q as usize;
            if machine.q[l]==0 && pool.loc[l]!=usize::MAX {pool.release(l);}
        }
        assert!(written<=start+gap+i+1);
    }
    rows.truncate(written);
    loop {
        let mut blocked=None;
        let mut ready=None;
        for (l,&c) in pool.loc.iter().enumerate() {
            if c!=usize::MAX && exit[l]!=c {
                blocked=Some(l);
                if pool.free.contains(&exit[l]) {ready=Some(l);break;}
            }
        }
        let Some(l)=ready.or(blocked) else {break};
        let c=if ready.is_some(){exit[l]}else{pool.best(l,n as u32)};
        pool.relocate(l,c,&machine,&mut |r|rows.push(r));
    }
}
