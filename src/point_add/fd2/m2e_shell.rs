//! M2E_SHELL (ob-shell, q765 pivot): the product stage of fb-m2e's R8-Z0 + DFOLD shell (NOTES/v7/m2_e/full_shell.py,
//! 1,337,787 T/shot simulated at peak 765) in place of P5SHELL, around the base's own walk (F + start765 / tail765 lists,
//! MarkerWalk). The shell is replayed from 5 GLV2 segments recorded gate by gate from the exact Python model
//! (NOTES/v8/pivot/shell/sshell.py + rec_sshell.py; generator gen_rust.py -> m2e_data.rs), cut at the 4 walk points.
//! Lanes: the recording's own lane ids 0..764 ("py lanes") are mapped to physical qubits on first use (fresh |0> lanes)
//! and released when dead at a segment end, so the shell holds at most 765 physical lanes. At a walk point the live
//! registers are moved by SWAP (0 T) onto the lanes the walk reads; after a forward walk the shell's X register follows
//! the walk's inverse lanes and PAR the walk's sign lane.
//! Seam (sshell.py): the walk leaves y = a if PAR else p - a (y < 2^255) and PAR; the shell's segments open with
//! X -> -X under ~PAR, PAR ^= ~X[255] (= 0; exact except a in (2^255 - C, 2^255)) and close with the reverse.
//! GLV2 (.glz) = zstd of b"GLV2" | u32 n_ops | u32 n_lanes | u32 n_bits | u32 n_tof | u32 0 | per op: u8 code (low 5 bits;
//! bit 7 = conditioned) + u32 LE operands + [u32 cond bit]. Codes: 0 X 1 CX 2 CCX 3 Z 4 CZ 5 CCZ 6 SWAP 7 NEG 8 HMR(t,bit)
//! 9 R 10 PUSH(bit) 11 POP 12 BINV(bit) 13 BST0(bit) 14 BST1(bit) (ob-wire's gl/glv2.py). Bits: 0..255 = ox, 256..511 = oy,
//! the rest fresh.
use super::builder::B;
use super::m2e_data::{Pt, Seg};
use super::pointadd_frogdrop::Walk;
use crate::circuit::{BitId, Op, OperationType, QubitId};
use sha3::{Digest, Sha3_256};
use std::collections::HashMap;

/// Switch: false = P5SHELL (the base stream, sha unchanged).
pub const ON: bool = true;
/// M2E_NEGD (ob-shell, op-blead's shot-6611 test): walks 3 / 4 carry ndy = -pdy (P5SHELL's passenger sign): the shell negates D before
/// walk 3, back after it (P5 sees pdy), again before walk 4 and back after (4 x 62 T; recording m2e_data_n, sshell.py NEGD=1).
pub const NEGD: bool = true;
fn tables() -> (&'static [Seg], &'static [Pt], &'static [u16], &'static [u16], u64) {
    if NEGD {
        use super::m2e_data_n as d;
        (&d::SEGS, &d::PTS, d::END_X, d::END_D, d::NBITS)
    } else {
        use super::m2e_data as d;
        (&d::SEGS, &d::PTS, d::END_X, d::END_D, d::NBITS)
    }
}

const NPY: usize = 765;

struct Sh {
    map: Vec<Option<QubitId>>,
    owner: HashMap<u64, usize>,
    ox: Vec<BitId>,
    oy: Vec<BitId>,
    base: u64,
}

impl Sh {
    fn bind(&mut self, k: usize, q: QubitId) {
        assert!(self.map[k].is_none(), "m2e: py lane {k} bound twice");
        assert!(self.owner.insert(q.0, k).is_none(), "m2e: q{} owned twice", q.0);
        self.map[k] = Some(q);
    }
    fn unbind(&mut self, k: usize) -> QubitId {
        let q = self.map[k].take().expect("m2e: unbind of an unbound lane");
        self.owner.remove(&q.0);
        q
    }
    fn lane(&mut self, b: &mut B, k: usize) -> QubitId {
        if let Some(q) = self.map[k] {
            return q;
        }
        let q = b.alloc();
        self.bind(k, q);
        q
    }
    fn bit(&self, k: u32) -> BitId {
        let k = k as u64;
        if k < 256 {
            self.ox[k as usize]
        } else if k < 512 {
            self.oy[k as usize - 256]
        } else {
            BitId(self.base + k - 512)
        }
    }
    /// Move the value of py lane k onto physical lane t (SWAP; a value already on t moves to k's old lane).
    fn place(&mut self, b: &mut B, k: usize, t: QubitId) {
        let cur = self.lane(b, k);
        if cur == t {
            return;
        }
        match self.owner.get(&t.0).copied() {
            Some(j) => {
                b.swap(cur, t);
                self.unbind(k);
                self.unbind(j);
                self.bind(k, t);
                self.bind(j, cur);
            }
            None => {
                b.acquire(t);
                b.swap(cur, t);
                self.unbind(k);
                b.free(cur);
                self.bind(k, t);
            }
        }
    }
}

fn code(c: u8) -> (OperationType, usize, bool) {
    use OperationType::*;
    match c {
        0 => (X, 1, false),
        1 => (CX, 2, false),
        2 => (CCX, 3, false),
        3 => (Z, 1, false),
        4 => (CZ, 2, false),
        5 => (CCZ, 3, false),
        6 => (Swap, 2, false),
        7 => (Neg, 0, false),
        8 => (Hmr, 1, true),
        9 => (R, 1, false),
        10 => (PushCondition, 0, true),
        11 => (PopCondition, 0, false),
        12 => (BitInvert, 0, true),
        13 => (BitStore0, 0, true),
        14 => (BitStore1, 0, true),
        _ => panic!("m2e: bad GLV2 op code {c}"),
    }
}

fn run_seg(b: &mut B, sh: &mut Sh, s: &Seg) {
    let h: String = Sha3_256::digest(s.data).iter().map(|x| format!("{:02x}", x)).collect();
    assert_eq!(h, s.sha3, "m2e: sha3 of segment {} changed", s.name);
    let raw = zstd::stream::decode_all(s.data).expect("m2e: zstd");
    assert!(raw.len() >= 24 && &raw[0..4] == b"GLV2", "m2e: bad magic");
    let r32 = |o: usize| u32::from_le_bytes([raw[o], raw[o + 1], raw[o + 2], raw[o + 3]]);
    let (n, nl, ntof) = (r32(4) as u64, r32(8) as usize, r32(16) as u64);
    assert!(nl <= NPY && n == s.ops && ntof == s.tof, "m2e: segment {} header", s.name);
    let (mut o, mut t) = (24usize, 0u64);
    for _ in 0..n {
        let c = raw[o];
        o += 1;
        let (kind, nq, hb) = code(c & 0x1f);
        let mut q = [QubitId(0); 3];
        for qi in q.iter_mut().take(nq) {
            *qi = sh.lane(b, r32(o) as usize);
            o += 4;
        }
        let mut op = Op::empty();
        op.kind = kind;
        if hb {
            let bb = sh.bit(r32(o));
            o += 4;
            if kind == OperationType::PushCondition {
                op.c_condition = bb;
            } else {
                op.c_target = bb;
            }
        }
        if c & 0x80 != 0 {
            op.c_condition = sh.bit(r32(o));
            o += 4;
        }
        match nq {
            1 => op.q_target = q[0],
            2 => {
                op.q_control1 = q[0];
                op.q_target = q[1];
            }
            3 => {
                op.q_control1 = q[0];
                op.q_control2 = q[1];
                op.q_target = q[2];
                t += 1;
            }
            _ => {}
        }
        b.raw_op(op);
    }
    assert_eq!(o, raw.len(), "m2e: trailing bytes in {}", s.name);
    assert_eq!(t, ntof, "m2e: CCX + CCZ count of {}", s.name);
    let mut keep = vec![false; NPY];
    for &k in s.live_end {
        keep[k as usize] = true;
    }
    for k in 0..NPY {
        if sh.map[k].is_some() && !keep[k] {
            let q = sh.unbind(k);
            b.free(q);
        }
    }
    for &k in s.live_end {
        assert!(sh.map[k as usize].is_some(), "m2e: live lane {k} of {} never touched", s.name);
    }
    eprintln!("m2e: segment {} replayed: {} ops, {} CCX+CCZ, live {} (b.live {})", s.name, n, t, s.live_end.len(), b.live);
}

pub fn point_add(b: &mut B, walk: &mut dyn Walk) -> (Vec<QubitId>, Vec<QubitId>) {
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);
    let (SEGS, PTS, END_X, END_D, NBITS) = tables();
    let base = b.fresh_bits((NBITS - 512) as usize)[0].0;
    let mut sh = Sh { map: vec![None; NPY], owner: HashMap::new(), ox, oy, base };
    // the recording allocates X first (py 0..255), then Y (py 256..511), bit i on the i-th lane
    for i in 0..256 {
        sh.bind(PTS[0].x[i] as usize, x[i]);
        sh.bind(256 + i, y[i]);
    }
    assert!(PTS[0].other.iter().enumerate().all(|(i, &k)| k as usize == 256 + i), "m2e: Y ids");
    run_seg(b, &mut sh, &SEGS[0]);
    // per forward walk: (inverse lanes, sign lane, flip, x lanes freed by the seam)
    let mut open: Vec<(Vec<QubitId>, QubitId, bool, Vec<QubitId>)> = vec![];
    for (k, p) in PTS.iter().enumerate() {
        for i in 0..256 {
            sh.place(b, p.other[i] as usize, y[i]);
        }
        if p.fwd {
            for i in 0..256 {
                sh.place(b, p.x[i] as usize, x[i]);
            }
            assert_eq!(b.live, 512, "m2e: live before forward walk {k}");
            for i in 0..256 {
                sh.unbind(p.x[i] as usize);
            }
            let (inv, (c, flip)) = walk.forward(b, &x, &y);
            assert_eq!(inv.len(), 255);
            for i in 0..255 {
                sh.bind(p.x[i] as usize, inv[i]);
            }
            if !flip {
                b.x(c);
            }
            sh.bind(p.par as usize, c);
            // x lanes the walk left |0> and unowned: one carries the shell's X[255], the rest are released
            let mut extra: Vec<QubitId> = x.iter().copied().filter(|q| !sh.owner.contains_key(&q.0) && !b.is_free(*q)).collect();
            // (the walk may have released the x lane of inv bit 255 itself: then X[255] takes any fresh |0> lane)
            let z = extra.pop().unwrap_or_else(|| b.alloc());
            sh.bind(p.x[255] as usize, z);
            for &q in &extra {
                b.free(q);
            }
            eprintln!("m2e: after forward walk {k}: b.live {} owned {} (x lanes released {})", b.live, sh.owner.len(), extra.len());
            assert_eq!(b.live as usize, sh.owner.len(), "m2e: a lane held outside the shell after forward walk {k}");
            open.push((inv, c, flip, extra));
        } else {
            let (inv, c, flip, extra) = open.pop().expect("m2e: inverse without forward");
            for i in 0..255 {
                sh.place(b, p.x[i] as usize, inv[i]);
            }
            sh.place(b, p.par as usize, c);
            if !flip {
                b.x(c);
            }
            // X[255] is |0>: release it, and give the walk back its zero x lanes
            let z = sh.unbind(p.x[255] as usize);
            b.free(z);
            sh.unbind(p.par as usize);
            for i in 0..255 {
                sh.unbind(p.x[i] as usize);
            }
            for &q in &extra {
                b.acquire(q);
            }
            eprintln!("m2e: before inverse walk {k}: b.live {}", b.live);
            walk.inverse(b, &x, &y);
            assert_eq!(b.live, 512, "m2e: live after inverse walk {k}");
            for i in 0..256 {
                sh.bind(p.x[i] as usize, x[i]);
            }
        }
        run_seg(b, &mut sh, &SEGS[k + 1]);
    }
    for i in 0..256 {
        sh.place(b, END_X[i] as usize, x[i]);
        sh.place(b, END_D[i] as usize, y[i]);
    }
    assert_eq!(b.live, 512, "m2e: live at the end");
    b.flush_dependency();
    (x, y)
}
