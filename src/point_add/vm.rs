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
            let (a, c, t) = ((z >> 32) as u16, (z >> 16) as u16, z as u16); if a != NONE { self.ccx(a, c, t); } else if c != NONE { self.cx(c, t); } else { self.x(t); } } }
    // ---- the adder family (Cuccaro ripple): b += a, a restored, c0 clean
    #[inline] fn maj(&mut self, x: u16, y: u16, z: u16) { self.cx(z, y); self.cx(z, x); self.ccx(x, y, z); }
    #[inline] fn maj_inv(&mut self, x: u16, y: u16, z: u16) { self.ccx(x, y, z); self.cx(z, x); self.cx(z, y); }
    #[inline] fn uma(&mut self, x: u16, y: u16, z: u16) { self.ccx(x, y, z); self.cx(z, x); self.cx(x, y); }
    #[inline] fn uma_c(&mut self, c: u16, x: u16, y: u16, z: u16) { self.ccx(x, y, z); self.cx(z, x); self.cx(z, y); self.ccx(c, z, y); self.ccx(c, x, y); }
    #[inline] fn uma_inv(&mut self, x: u16, y: u16, z: u16) { self.cx(x, y); self.cx(z, x); self.ccx(x, y, z); }
    #[inline] fn uma_c_inv(&mut self, c: u16, x: u16, y: u16, z: u16) { self.ccx(c, x, y); self.ccx(c, z, y); self.cx(z, y); self.cx(z, x); self.ccx(x, y, z); }
    pub fn xs(&mut self, r: &[u16]) { for &q in r { self.x(q); } }
    pub fn add(&mut self, a: &[u16], b: &[u16], c0: u16, ctrl: i32, cout: i32) { let n = a.len(); assert!(b.len() == n && n > 0, "add widths");
        let m = if cout < 0 { n - 1 } else { n };
        if m > 0 { self.maj(c0, b[0], a[0]); for i in 1..m { self.maj(a[i - 1], b[i], a[i]); } }
        if cout >= 0 { if ctrl >= 0 { self.ccx(ctrl as u16, a[n - 1], cout as u16); } else { self.cx(a[n - 1], cout as u16); } }
        else { let prev = if n == 1 { c0 } else { a[n - 2] }; if ctrl >= 0 { self.ccx(ctrl as u16, prev, b[n - 1]); self.ccx(ctrl as u16, a[n - 1], b[n - 1]); } else { self.cx(prev, b[n - 1]); self.cx(a[n - 1], b[n - 1]); } }
        for i in (1..m).rev() { if ctrl >= 0 { self.uma_c(ctrl as u16, a[i - 1], b[i], a[i]); } else { self.uma(a[i - 1], b[i], a[i]); } }
        if m > 0 { if ctrl >= 0 { self.uma_c(ctrl as u16, c0, b[0], a[0]); } else { self.uma(c0, b[0], a[0]); } } }
    pub fn sub(&mut self, a: &[u16], b: &[u16], c0: u16, ctrl: i32, cout: i32) {
        if cout >= 0 { self.xs(b); self.add(a, b, c0, ctrl, cout); self.xs(b); return; }
        let n = a.len(); assert!(b.len() == n && n > 0, "sub widths");
        if n > 1 { if ctrl >= 0 { self.uma_c_inv(ctrl as u16, c0, b[0], a[0]); } else { self.uma_inv(c0, b[0], a[0]); }
        for i in 1..n - 1 { if ctrl >= 0 { self.uma_c_inv(ctrl as u16, a[i - 1], b[i], a[i]); } else { self.uma_inv(a[i - 1], b[i], a[i]); } } }
        let prev = if n == 1 { c0 } else { a[n - 2] }; if ctrl >= 0 { self.ccx(ctrl as u16, prev, b[n - 1]); self.ccx(ctrl as u16, a[n - 1], b[n - 1]); } else { self.cx(prev, b[n - 1]); self.cx(a[n - 1], b[n - 1]); }
        if n > 1 { for i in (1..n - 1).rev() { self.maj_inv(a[i - 1], b[i], a[i]); } self.maj_inv(c0, b[0], a[0]); } }
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
        for &(t, x, y) in ops.iter() { self.ccx(ln[x], ln[y], ln[t]); if t != 0 { self.x(ln[t]); } }
        self.ccx(ln[rest.0], ln[rest.1], target);
        for &(t, x, y) in ops.iter().rev() { if t != 0 { self.x(ln[t]); } self.ccx(ln[x], ln[y], ln[t]); } }
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
