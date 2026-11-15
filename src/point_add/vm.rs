//! Gate emitter for the scans: gates go to the output, or into the innermost open capture (a recorded sub-circuit that is
//! replayed forwards or backwards: every gate is its own inverse).  Plus the adder family the scan trace is written in.
use super::Row;
const NONE: u16 = u16::MAX;
/// run-time constant load: one classically conditioned X / CX per lane; ids are bit ids + 2 (1 = no gate, 0 = unconditioned)
pub struct Krt { pub lanes: Vec<u16>, pub ids: Vec<u32>, pub ctl: i32 }
#[derive(Default)]
pub struct Block { g: Vec<u64>, krt: Vec<Krt> }
pub struct Vm<'a> { out: &'a mut dyn FnMut(Row), caps: Vec<Block>, pub next_bit: u32, pub meas: Vec<u16> }
const KRT_TAG: u64 = 1 << 63;
/// lane T (635): a captured CCX that computes an AND into a lane that is 0 (AND_C) or uncomputes one (AND_U); `play` emits the uncomputing
/// direction (forward AND_U, reverse AND_C) as `mz` and the computing direction as a CCX
const AND_C: u64 = 1 << 62;
const AND_U: u64 = 1 << 61;
#[inline] fn pack(a: u16, b: u16, t: u16) -> u64 { ((a as u64) << 32) | ((b as u64) << 16) | t as u64 }
impl<'a> Vm<'a> {
    pub fn new(out: &'a mut dyn FnMut(Row), bit0: u32) -> Vm<'a> { Vm { out, caps: Vec::new(), next_bit: bit0, meas: Vec::new() } }
    #[inline] pub fn rec(&mut self, r: Row) { (self.out)(r); }
    #[inline] pub fn x(&mut self, t: u16) { if let Some(b) = self.caps.last_mut() { b.g.push(pack(NONE, NONE, t)); } else { (self.out)([6, t, NONE, NONE]); } }
    #[inline] pub fn cx(&mut self, c: u16, t: u16) { debug_assert!(c != t); if let Some(b) = self.caps.last_mut() { b.g.push(pack(NONE, c, t)); } else { (self.out)([8, c, t, NONE]); } }
    #[inline] pub fn ccx(&mut self, a: u16, b2: u16, t: u16) { debug_assert!(a != b2 && a != t && b2 != t); if let Some(b) = self.caps.last_mut() { b.g.push(pack(a, b2, t)); } else { (self.out)([13, a, b2, t]); } }
    pub fn krt(&mut self, lanes: &[u16], ids: &[u32], ctl: i32) {
        if let Some(b) = self.caps.last_mut() { b.g.push(KRT_TAG | b.krt.len() as u64); b.krt.push(Krt { lanes: lanes.to_vec(), ids: ids.to_vec(), ctl }); return; }
        for i in 0..lanes.len() { let id = if i < ids.len() { ids[i] } else { 1 }; if id == 1 { continue; } let cb = if id == 0 { NONE } else { (id - 2) as u16 };
            if ctl >= 0 { (self.out)([8, ctl as u16, lanes[i], cb]); } else { (self.out)([6, lanes[i], cb, NONE]); } } }
    pub fn hmr(&mut self, q: u16) { assert!(self.caps.is_empty(), "measurement inside a capture"); let b = self.next_bit as u16; self.next_bit += 1; self.meas.push(b); (self.out)([12, q, b, NONE]); }
    pub fn zif(&mut self, m: usize, q: u16) { assert!(self.caps.is_empty()); let b = self.meas[m]; (self.out)([7, q, b, NONE]); }
    pub fn czif(&mut self, m: usize, a: u16, b: u16) { assert!(self.caps.is_empty()); let bit = self.meas[m]; (self.out)([9, a, b, bit]); }
    pub fn cap_begin(&mut self) { self.caps.push(Block::default()); }
    pub fn cap_end(&mut self) -> Block { self.caps.pop().expect("capture") }
    pub fn capturing(&self) -> bool { !self.caps.is_empty() }
    pub fn play(&mut self, b: &Block, rev: bool) { let n = b.g.len();
        for k in 0..n { let z = b.g[if rev { n - 1 - k } else { k }];
            if z & KRT_TAG != 0 { let e = &b.krt[(z & 0xffff_ffff) as usize]; self.krt(&e.lanes, &e.ids, e.ctl); continue; }
            let (a, c, t) = ((z >> 32) as u16, (z >> 16) as u16, z as u16);
            if z & (AND_C | AND_U) != 0 { if (z & AND_U != 0) != rev { self.ccx_u(a, c, t); } else { self.ccx_c(a, c, t); } continue; }
            if a != NONE { self.ccx(a, c, t); } else if c != NONE { self.cx(c, t); } else { self.x(t); } } }
    // ---- the adder family (Cuccaro ripple): b += a, a restored, c0 clean
    #[inline] fn maj(&mut self, x: u16, y: u16, z: u16) { self.cx(z, y); self.cx(z, x); self.ccx(x, y, z); }
    #[inline] fn maj_inv(&mut self, x: u16, y: u16, z: u16) { self.ccx(x, y, z); self.cx(z, x); self.cx(z, y); }
    #[inline] fn uma(&mut self, x: u16, y: u16, z: u16) { self.ccx(x, y, z); self.cx(z, x); self.cx(x, y); }
    /// controlled UMA (lane T, 635): after CX(z, x) the pair CCX(c, z, y) CCX(c, x, y) adds c (z ^ x ^ z) = c x of the ORIGINAL x to y, so one Toffoli
    /// placed before CX(z, x) replaces the pair: the same unitary with one Toffoli and one record fewer
    #[inline] fn uma_c(&mut self, c: u16, x: u16, y: u16, z: u16) { if UMA_C2 { self.ccx(x, y, z); self.cx(z, y); self.ccx(c, x, y); self.cx(z, x); return; } self.ccx(x, y, z); self.cx(z, x); self.cx(z, y); self.ccx(c, z, y); self.ccx(c, x, y); }
    #[inline] fn uma_inv(&mut self, x: u16, y: u16, z: u16) { self.cx(x, y); self.cx(z, x); self.ccx(x, y, z); }
    #[inline] fn uma_c_inv(&mut self, c: u16, x: u16, y: u16, z: u16) { if UMA_C2 { self.cx(z, x); self.ccx(c, x, y); self.cx(z, y); self.ccx(x, y, z); return; } self.ccx(c, x, y); self.ccx(c, z, y); self.cx(z, y); self.cx(z, x); self.ccx(x, y, z); }
    pub fn xs(&mut self, r: &[u16]) { for &q in r { self.x(q); } }
    pub fn add(&mut self, a: &[u16], b: &[u16], c0: u16, ctrl: i32, cout: i32) { let n = a.len(); assert!(b.len() == n && n > 0, "add widths");
        self.maj(c0, b[0], a[0]); for i in 1..n { self.maj(a[i - 1], b[i], a[i]); }
        if cout >= 0 { if ctrl >= 0 { self.ccx(ctrl as u16, a[n - 1], cout as u16); } else { self.cx(a[n - 1], cout as u16); } }
        for i in (1..n).rev() { if ctrl >= 0 { self.uma_c(ctrl as u16, a[i - 1], b[i], a[i]); } else { self.uma(a[i - 1], b[i], a[i]); } }
        if ctrl >= 0 { self.uma_c(ctrl as u16, c0, b[0], a[0]); } else { self.uma(c0, b[0], a[0]); } }
    pub fn sub(&mut self, a: &[u16], b: &[u16], c0: u16, ctrl: i32, cout: i32) {
        if cout >= 0 { self.xs(b); self.add(a, b, c0, ctrl, cout); self.xs(b); return; }
        let n = a.len(); assert!(b.len() == n && n > 0, "sub widths");
        if ctrl >= 0 { self.uma_c_inv(ctrl as u16, c0, b[0], a[0]); } else { self.uma_inv(c0, b[0], a[0]); }
        for i in 1..n { if ctrl >= 0 { self.uma_c_inv(ctrl as u16, a[i - 1], b[i], a[i]); } else { self.uma_inv(a[i - 1], b[i], a[i]); } }
        for i in (1..n).rev() { self.maj_inv(a[i - 1], b[i], a[i]); } self.maj_inv(c0, b[0], a[0]); }
    pub fn carry(&mut self, a: &[u16], b: &[u16], c0: u16, flag: u16, ctrl: i32) { let n = a.len(); assert!(b.len() == n && n > 0, "carry widths");
        self.maj(c0, b[0], a[0]); for i in 1..n { self.maj(a[i - 1], b[i], a[i]); }
        if ctrl >= 0 { self.ccx(ctrl as u16, a[n - 1], flag); } else { self.cx(a[n - 1], flag); }
        for i in (1..n).rev() { self.maj_inv(a[i - 1], b[i], a[i]); } self.maj_inv(c0, b[0], a[0]); }
    pub fn gt(&mut self, a: &[u16], b: &[u16], c0: u16, flag: u16, ctrl: i32) { let n = a.len(); assert!(b.len() == n, "gt widths");
        self.xs(b); self.maj(c0, b[0], a[0]); for i in 1..n { self.maj(a[i - 1], b[i], a[i]); }
        if ctrl >= 0 { self.ccx(ctrl as u16, a[n - 1], flag); } else { self.cx(a[n - 1], flag); }
        for i in (1..n).rev() { self.maj_inv(a[i - 1], b[i], a[i]); } self.maj_inv(c0, b[0], a[0]); self.xs(b); }
    pub fn swap(&mut self, a: u16, b: u16) { self.cx(a, b); self.cx(b, a); self.cx(a, b); }
    /// lane i -> lane i + 1 (top lane wraps to lane 0)
    pub fn rot1_up(&mut self, reg: &[u16]) { for i in (1..reg.len()).rev() { self.swap(reg[i], reg[i - 1]); } }
    // ---- scan macros
    pub fn fan(&mut self, ctl: u16, r: &[u16]) { for &q in r { self.cx(ctl, q); } }
    /// C += ctl with clean carry lanes
    pub fn cinc_clean(&mut self, ctl: u16, c: &[u16], anc: &[u16]) { let n = c.len(); if n == 0 { return; }
        if n > 1 { self.ccx(ctl, c[0], anc[0]); for i in 1..n - 1 { self.ccx(anc[i - 1], c[i], anc[i]); }
            for i in (1..n).rev() { self.cx(anc[i - 1], c[i]); if i >= 2 { self.ccx(anc[i - 2], c[i - 1], anc[i - 1]); } else { self.ccx(ctl, c[0], anc[0]); } } }
        self.cx(ctl, c[0]); }
    /// target ^= [all controls are 1], with borrowed lanes d (|d| = |ctrl| - 2): Barenco V-chain, run twice
    pub fn mcx(&mut self, ctrl: &[u16], target: u16, d: &[u16]) { let k = ctrl.len();
        match k { 0 => self.x(target), 1 => self.cx(ctrl[0], target), 2 => self.ccx(ctrl[0], ctrl[1], target),
            _ => for _ in 0..2 { self.ccx(ctrl[k - 1], d[k - 3], target); for i in (2..=k - 2).rev() { self.ccx(ctrl[i], d[i - 2], d[i - 1]); } self.ccx(ctrl[0], ctrl[1], d[0]); for i in 2..=k - 2 { self.ccx(ctrl[i], d[i - 2], d[i - 1]); } } } }
    /// target ^= [all controls are 1] with ONE lane z that is 0 on entry (Khattar-Gidney, arXiv 2407.17966v2 sec 5.1-5.2): 2k - 3 Toffoli instead of 4(k - 2).
    /// Lane 0 = z, lanes 1..=k = the controls; a lane is "marked" while it holds a conditionally clean value.  Greedy schedule: the rightmost marked lane t that has two
    /// unmarked lanes x < y to its right gets t ^= x & y (then t ^= 1 unless t is z); x and y become marked.  After k - 2 steps two unmarked lanes remain and their
    /// product is the AND of all controls: one Toffoli onto the target, then the schedule is undone gate by gate.  z and every control return exactly (borrowed, never dirty-assumed);
    /// the target gets the XOR of the AND, nothing else changes.  Only X / CX / CCX.  Wrong (not merely dirty) if z is not 0 on entry.
    pub fn mcx_kg(&mut self, ctrl: &[u16], target: u16, z: u16) { let k = ctrl.len();
        assert!(k >= 3 && z != target && !ctrl.contains(&z) && !ctrl.contains(&target), "mcx_kg lanes");
        let (ops, rest) = kg_schedule(k); let mut ln: Vec<u16> = Vec::with_capacity(k + 1); ln.push(z); ln.extend_from_slice(ctrl);
        // lane T (635): the one step that targets the zero lane z (t == 0) computes x & y into a lane that is 0, and its mirror uncomputes
        // exactly that AND once every other step is undone: ccx_c / ccx_u (measured when emitted; the form already requires z = 0)
        for &(t, x, y) in ops.iter() { if t == 0 && KG_Z_MZ { self.ccx_c(ln[x], ln[y], ln[t]); } else { self.ccx(ln[x], ln[y], ln[t]); } if t != 0 { self.x(ln[t]); } }
        self.ccx(ln[rest.0], ln[rest.1], target);
        for &(t, x, y) in ops.iter().rev() { if t != 0 { self.x(ln[t]); } if t == 0 && KG_Z_MZ { self.ccx_u(ln[x], ln[y], ln[t]); } else { self.ccx(ln[x], ln[y], ln[t]); } } }
    /// target ^= [all controls are 0], one zero lane z (see `mcx_kg`)
    pub fn mcx_neg_kg(&mut self, ctrl: &[u16], target: u16, z: u16) { self.xs(ctrl); self.mcx_kg(ctrl, target, z); self.xs(ctrl); }
    /// target ^= [all controls are 0]
    pub fn mcx_neg(&mut self, ctrl: &[u16], target: u16, d: &[u16]) { self.xs(ctrl); self.mcx(ctrl, target, d); self.xs(ctrl); }
}
/// schedule of `Vm::mcx_kg` for k controls: (t, x, y) steps over lane indices (0 = the zero lane, 1..=k the controls), and the two unmarked lanes left; cached per k
fn kg_schedule(k: usize) -> (std::rc::Rc<Vec<(usize, usize, usize)>>, (usize, usize)) {
    thread_local! { static CACHE: std::cell::RefCell<std::collections::HashMap<usize, (std::rc::Rc<Vec<(usize, usize, usize)>>, (usize, usize))>> = std::cell::RefCell::new(std::collections::HashMap::new()); }
    CACHE.with(|c| c.borrow_mut().entry(k).or_insert_with(|| {
        let mut marked = vec![false; k + 1]; marked[0] = true; let mut ops: Vec<(usize, usize, usize)> = Vec::new();
        loop { let mut pick = usize::MAX;
            for t in (0..=k).rev() { if marked[t] { let c = (t + 1..=k).filter(|&i| !marked[i]).count(); if c >= 2 { pick = t; break; } } }
            if pick == usize::MAX { break; }
            let mut un = (pick + 1..=k).filter(|&i| !marked[i]); let (x, y) = (un.next().unwrap(), un.next().unwrap());
            ops.push((pick, x, y)); marked[pick] = false; marked[x] = true; marked[y] = true; }
        let rest: Vec<usize> = (0..=k).filter(|&i| !marked[i]).collect(); assert!(rest.len() == 2, "mcx_kg schedule");
        (std::rc::Rc::new(ops), (rest[0], rest[1])) }).clone())
}

impl<'a> Vm<'a> {
    fn guarded_xor(&mut self,guard:i32,a:u16,b:u16) {
        if guard<0 {self.cx(a,b);} else {self.ccx(guard as u16,a,b);}
    }
    // TTK 2009 section 2.2 uses A[i]=a[i]^carry[i] and B[i]=a[i]^b[i]
    // at the peak of the carry ladder. Gate only the sum extraction and
    // (optional) carry flag; every other operation is paired with its inverse.
    fn without_carry_wire(&mut self,a:&[u16],b:&[u16],guard:i32,flag:i32,sum:bool) {
        let n=a.len();
        assert!(n>0 && b.len()==n);
        if n==1 {
            if flag>=0 {
                if guard<0 {self.ccx(a[0],b[0],flag as u16);}
                else {
                    let tmp=(0u16..6).find(|x|!a.contains(x) && !b.contains(x) && *x!=guard as u16 && *x!=flag as u16).unwrap();
                    for _ in 0..2 {
                        self.ccx(a[0],b[0],tmp);
                        self.ccx(guard as u16,tmp,flag as u16);
                    }
                }
            }
            if sum {self.guarded_xor(guard,a[0],b[0]);}
            return;
        }
        let top=n-1;
        if flag>=0 {self.guarded_xor(guard,a[top],flag as u16);}
        for i in 1..n {self.cx(a[i],b[i]);}
        for i in (1..top).rev() {self.cx(a[i],a[i+1]);}
        for i in 0..top {self.ccx(a[i],b[i],a[i+1]);}
        if flag>=0 {
            if guard<0 {self.ccx(a[top],b[top],flag as u16);}
            else {
                // Four-gate borrowed-bit C3X, restoring an occupied operand.
                for _ in 0..2 {
                    self.ccx(a[top],b[top],a[0]);
                    self.ccx(guard as u16,a[0],flag as u16);
                }
            }
        }
        for i in (1..n).rev() {
            if sum {self.guarded_xor(guard,a[i],b[i]);}
            self.ccx(a[i-1],b[i-1],a[i]);
        }
        for i in 1..top {self.cx(a[i],a[i+1]);}
        for i in 1..n {self.cx(a[i],b[i]);}
        if sum {self.guarded_xor(guard,a[0],b[0]);}
    }
    pub fn zero_add(&mut self,a:&[u16],b:&[u16],_carry:u16,guard:i32,flag:i32) {
        self.without_carry_wire(a,b,guard,flag,true);
    }
    pub fn zero_carry(&mut self,a:&[u16],b:&[u16],_carry:u16,flag:u16,guard:i32) {
        self.without_carry_wire(a,b,guard,flag as i32,false);
    }
    pub fn zero_gt(&mut self,a:&[u16],b:&[u16],carry:u16,flag:u16,guard:i32) {
        self.xs(b);self.zero_carry(a,b,carry,flag,guard);self.xs(b);
    }
}

impl<'a> Vm<'a> {
    pub fn zero_sub(&mut self,a:&[u16],b:&[u16],c:u16,guard:i32,flag:i32){
        self.cap_begin();self.zero_add(a,b,c,guard,flag);let inv=self.cap_end();self.play(&inv,true);
    }
}

// lane T (635): measurement-based uncomputation
impl<'a> Vm<'a> {
    // ---- measurement-based uncomputation (lane T, 635): 0 Toffoli where a lane provably holds the AND of two others
    /// t ^= a & b where t holds exactly a & b (t was 0 before the Toffoli that computed it, a and b unchanged since): X-basis measurement of t
    /// into the scratch bit MZ_BIT (t becomes 0), then CZ(a, b) conditioned on the outcome cancels the phase kickback a & b & outcome.
    /// t ^= a & b where t is 0 (an AND computed into a clean lane): a CCX, flagged when captured so that a reverse replay measures it
    #[inline] pub fn ccx_c(&mut self, a: u16, b: u16, t: u16) { if let Some(bl) = self.caps.last_mut() { bl.g.push(pack(a, b, t) | AND_C); } else { (self.out)([13, a, b, t]); } }
    /// t ^= a & b where t holds a & b (an AND uncomputed): `mz` when emitted, flagged when captured (a reverse replay computes it with a CCX)
    #[inline] pub fn ccx_u(&mut self, a: u16, b: u16, t: u16) { if let Some(bl) = self.caps.last_mut() { bl.g.push(pack(a, b, t) | AND_U); } else { self.mz(a, b, t); } }
    pub fn mz(&mut self, a: u16, b: u16, t: u16) { assert!(self.caps.is_empty(), "mz inside a capture"); debug_assert!(a != b && a != t && b != t);
        (self.out)([12, t, MZ_BIT, NONE]); (self.out)([9, a, b, MZ_BIT]); }
    /// b += a + c0 (a, c0 restored): the low m = min(|anc|, n - 1) bits with Gidney's temporary-AND carries (arXiv 1709.06648) held in the clean lanes
    /// anc (0 on entry and on exit; carry i + 1 in anc[i]: m Toffoli, uncomputed by measurement), the high n - m bits by the Cuccaro ripple above
    /// with carry-in lane anc[m - 1].  2n - m Toffoli instead of 2n.
    pub fn add_h(&mut self, a: &[u16], b: &[u16], c0: u16, anc: &[u16]) { let n = a.len(); assert!(b.len() == n && n > 0, "add_h widths"); let m = anc.len().min(n - 1);
        if m == 0 { self.add(a, b, c0, -1, -1); return; }
        for i in 0..m { let c = if i == 0 { c0 } else { anc[i - 1] }; self.cx(c, a[i]); self.cx(c, b[i]); self.ccx_c(a[i], b[i], anc[i]); self.cx(c, anc[i]); }
        self.add(&a[m..], &b[m..], anc[m - 1], -1, -1);
        for i in (0..m).rev() { let c = if i == 0 { c0 } else { anc[i - 1] }; self.cx(c, anc[i]); self.ccx_u(a[i], b[i], anc[i]); self.cx(c, a[i]); self.cx(a[i], b[i]); } }
    /// b -= a + c0: the exact inverse of `add_h` (the Toffoli that uncomputed a carry there computes it here and vice versa)
    pub fn sub_h(&mut self, a: &[u16], b: &[u16], c0: u16, anc: &[u16]) { let n = a.len(); assert!(b.len() == n && n > 0, "sub_h widths"); let m = anc.len().min(n - 1);
        if m == 0 { self.sub(a, b, c0, -1, -1); return; }
        for i in 0..m { let c = if i == 0 { c0 } else { anc[i - 1] }; self.cx(a[i], b[i]); self.cx(c, a[i]); self.ccx_c(a[i], b[i], anc[i]); self.cx(c, anc[i]); }
        self.sub(&a[m..], &b[m..], anc[m - 1], -1, -1);
        for i in (0..m).rev() { let c = if i == 0 { c0 } else { anc[i - 1] }; self.cx(c, anc[i]); self.ccx_u(a[i], b[i], anc[i]); self.cx(c, b[i]); self.cx(c, a[i]); } }
    /// flag ^= [ctrl] carry-out of a + b + c0 (all restored): the low m = min(|anc|, n) carries Gidney-style into the clean lanes anc
    /// (computed with ccx_c, uncomputed with ccx_u), the rest by the Cuccaro carry with carry-in lane anc[m - 1]
    pub fn carry_h(&mut self, a: &[u16], b: &[u16], c0: u16, flag: u16, ctrl: i32, anc: &[u16]) { let n = a.len(); assert!(b.len() == n && n > 0, "carry_h widths"); let m = anc.len().min(n);
        if m == 0 { self.carry(a, b, c0, flag, ctrl); return; }
        for i in 0..m { let c = if i == 0 { c0 } else { anc[i - 1] }; self.cx(c, a[i]); self.cx(c, b[i]); self.ccx_c(a[i], b[i], anc[i]); self.cx(c, anc[i]); }
        if m < n { self.carry(&a[m..], &b[m..], anc[m - 1], flag, ctrl); } else if ctrl >= 0 { self.ccx(ctrl as u16, anc[n - 1], flag); } else { self.cx(anc[n - 1], flag); }
        for i in (0..m).rev() { let c = if i == 0 { c0 } else { anc[i - 1] }; self.cx(c, anc[i]); self.ccx_u(a[i], b[i], anc[i]); self.cx(c, b[i]); self.cx(c, a[i]); } }
    /// `gt` with Gidney carries (see `carry_h`)
    pub fn gt_h(&mut self, a: &[u16], b: &[u16], c0: u16, flag: u16, ctrl: i32, anc: &[u16]) { self.xs(b); self.carry_h(a, b, c0, flag, ctrl, anc); self.xs(b); }
    /// b += a + c0 with cout ^= carry-out (no control): Gidney carries on the low m = min(|anc|, n) bits, Cuccaro (with its carry-out) above
    pub fn add_hc(&mut self, a: &[u16], b: &[u16], c0: u16, cout: u16, anc: &[u16]) { let n = a.len(); assert!(b.len() == n && n > 0, "add_hc widths"); let m = anc.len().min(n);
        if m == 0 { self.add(a, b, c0, -1, cout as i32); return; }
        for i in 0..m { let c = if i == 0 { c0 } else { anc[i - 1] }; self.cx(c, a[i]); self.cx(c, b[i]); self.ccx_c(a[i], b[i], anc[i]); self.cx(c, anc[i]); }
        if m < n { self.add(&a[m..], &b[m..], anc[m - 1], -1, cout as i32); } else { self.cx(anc[n - 1], cout); }
        for i in (0..m).rev() { let c = if i == 0 { c0 } else { anc[i - 1] }; self.cx(c, anc[i]); self.ccx_u(a[i], b[i], anc[i]); self.cx(c, a[i]); self.cx(a[i], b[i]); } }
    /// b += [ctl] a (+ c0, which is 0 here), cout ^= [ctl] carry-out: the low m = min(|anc| / 2, n - 1) bits mask a into clean lanes
    /// x_i = ctl & a_i and add them with Gidney carries (2 Toffoli per bit, both uncomputed by measurement), the rest by the controlled
    /// Cuccaro ripple (3 Toffoli per bit) with carry-in lane = the last Gidney carry (0 whenever ctl = 0)
    pub fn add_mc(&mut self, a: &[u16], b: &[u16], c0: u16, ctl: u16, cout: i32, anc: &[u16]) { let n = a.len(); assert!(b.len() == n && n > 1, "add_mc widths"); let m = (anc.len() / 2).min(n - 1);
        if m == 0 { self.add(a, b, c0, ctl as i32, cout); return; }
        let (x, cl) = (&anc[..m], &anc[m..2 * m]);
        for i in 0..m { let c = if i == 0 { c0 } else { cl[i - 1] }; self.ccx_c(ctl, a[i], x[i]); self.cx(c, x[i]); self.cx(c, b[i]); self.ccx_c(x[i], b[i], cl[i]); self.cx(c, cl[i]); }
        self.add(&a[m..], &b[m..], cl[m - 1], ctl as i32, cout);
        for i in (0..m).rev() { let c = if i == 0 { c0 } else { cl[i - 1] }; self.cx(c, cl[i]); self.ccx_u(x[i], b[i], cl[i]); self.cx(c, x[i]); self.cx(x[i], b[i]); self.ccx_u(ctl, a[i], x[i]); } }
    /// `cinc_clean` with the uncomputing Toffoli of each clean carry lane replaced by `mz` (outside captures only)
    pub fn cinc_clean_mz(&mut self, ctl: u16, c: &[u16], anc: &[u16]) { let n = c.len(); if n == 0 { return; } if self.capturing() { self.cinc_clean(ctl, c, anc); return; }
        if n > 1 { self.ccx(ctl, c[0], anc[0]); for i in 1..n - 1 { self.ccx(anc[i - 1], c[i], anc[i]); }
            for i in (1..n).rev() { self.cx(anc[i - 1], c[i]); if i >= 2 { self.mz(anc[i - 2], c[i - 1], anc[i - 1]); } else { self.mz(ctl, c[0], anc[0]); } } }
        self.cx(ctl, c[0]); }
}
/// classical scratch bit of `Vm::mz` (the raw builder output uses bit ids up to 62483; post_pass reserves 65533 / 65534)
pub const MZ_BIT: u16 = 65500;
/// lane T (635) switch: the controlled UMA of the Cuccaro adder with 2 Toffoli instead of 3 (an exact identity)
pub const UMA_C2: bool = true;
/// lane T (635) switch: the Khattar-Gidney hit test uncomputes its zero lane by measurement
pub const KG_Z_MZ: bool = true;
