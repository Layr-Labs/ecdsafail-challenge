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
const MEASURE: u16 = 65_532;
// Captures occupy under 2^63 entries; tags use two bits below KRT_TAG.
// Each half of a carry pair reverses into its complementary operation.
const CARRY_TAG: u64 = 1 << 62;
const END_TAG: u64 = 1 << 61;
#[inline] fn pack(a: u16, b: u16, t: u16) -> u64 { ((a as u64) << 32) | ((b as u64) << 16) | t as u64 }
impl<'a> Vm<'a> {
    pub fn new(out: &'a mut dyn FnMut(Row), bit0: u32) -> Vm<'a> { Vm { out, caps: Vec::new(), next_bit: bit0, meas: Vec::new() } }
    #[inline] pub fn rec(&mut self, r: Row) { (self.out)(r); }
    #[inline] pub fn x(&mut self, t: u16) { if let Some(b) = self.caps.last_mut() { b.g.push(pack(NONE, NONE, t)); } else { (self.out)([6, t, NONE, NONE]); } }
    #[inline] pub fn cx(&mut self, c: u16, t: u16) { debug_assert!(c != t); if let Some(b) = self.caps.last_mut() { b.g.push(pack(NONE, c, t)); } else { (self.out)([8, c, t, NONE]); } }
    #[inline] pub fn ccx(&mut self, a: u16, b2: u16, t: u16) { debug_assert!(a != b2 && a != t && b2 != t); if let Some(b) = self.caps.last_mut() { b.g.push(pack(a, b2, t)); } else { (self.out)([13, a, b2, t]); } }
    fn carry_and(&mut self, a:u16, b:u16, t:u16, end:bool) {
        if let Some(block)=self.caps.last_mut() {
            block.g.push(CARRY_TAG | if end { END_TAG } else { 0 } | pack(a,b,t));
        } else if end {
            // Fresh target at computation. Its unchanged controls still encode
            // its current value, including any surrounding classical scope.
            (self.out)([251,t,MEASURE,NONE]);
            (self.out)([252,a,b,MEASURE]);
        } else {
            self.ccx(a,b,t);
        }
    }
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
            if z & CARRY_TAG != 0 {
                self.carry_and((z>>32) as u16,(z>>16) as u16,z as u16,((z & END_TAG)!=0)^rev);
                continue;
            }
            let (a, c, t) = ((z >> 32) as u16, (z >> 16) as u16, z as u16); if a != NONE { self.ccx(a, c, t); } else if c != NONE { self.cx(c, t); } else { self.x(t); } } }
    // ---- the adder family (Cuccaro ripple): b += a, a restored, c0 clean
    #[inline] fn maj(&mut self, x: u16, y: u16, z: u16) { self.cx(z, y); self.cx(z, x); self.ccx(x, y, z); }
    #[inline] fn maj_inv(&mut self, x: u16, y: u16, z: u16) { self.ccx(x, y, z); self.cx(z, x); self.cx(z, y); }
    #[inline] fn uma(&mut self, x: u16, y: u16, z: u16) { self.ccx(x, y, z); self.cx(z, x); self.cx(x, y); }
    // Before restoring x, it already contains the XOR of the controls that
    // would correct y after restoration. Apply that correction once.
    #[inline] fn uma_c(&mut self, c: u16, x: u16, y: u16, z: u16) { self.ccx(x, y, z); self.ccx(c, x, y); self.cx(z, x); self.cx(z, y); }
    #[inline] fn uma_inv(&mut self, x: u16, y: u16, z: u16) { self.cx(x, y); self.cx(z, x); self.ccx(x, y, z); }
    #[inline] fn uma_c_inv(&mut self, c: u16, x: u16, y: u16, z: u16) { self.cx(z, y); self.cx(z, x); self.ccx(c, x, y); self.ccx(x, y, z); }
    // The high sum is y ^ [ctrl](x ^ z). Its carry is unused.
    #[inline] fn sum_top(&mut self, x:u16, y:u16, z:u16, ctrl:i32) {
        if ctrl < 0 { self.cx(x,y); self.cx(z,y); }
        else { self.cx(z,x); self.ccx(ctrl as u16,x,y); self.cx(z,x); }
    }
    // maj(x,y,z) = z ^ ((x ^ z) & (y ^ z)). XOR an unguarded
    // carry directly into its destination without building and undoing it.
    #[inline] fn copy_top_carry(&mut self, x:u16, y:u16, z:u16, flag:u16, ctrl:i32) {
        if ctrl < 0 {
            self.cx(z,y); self.cx(z,x);
            self.ccx(x,y,flag); self.cx(z,flag);
            self.cx(z,x); self.cx(z,y);
        } else {
            self.maj(x,y,z); self.ccx(ctrl as u16,z,flag); self.maj_inv(x,y,z);
        }
    }
    pub fn xs(&mut self, r: &[u16]) { for &q in r { self.x(q); } }
    /// Add a zero-extended unsigned payload into b modulo 2^|b|.
    /// The low carry input and zero-suffix lanes must start clean.
    pub fn add_zero_extended(&mut self, a: &[u16], b: &[u16], c0:u16, zero: &[u16]) {
        assert!(!a.is_empty() && a.len() <= b.len());
        if a.len() == b.len() {
            self.add(a, b, c0, -1, -1);
            return;
        }
        let (low, high) = b.split_at(a.len());
        for i in 0..a.len() {
            self.maj(if i == 0 { c0 } else { a[i - 1] }, low[i], a[i]);
        }
        // The most significant payload lane now holds the outgoing carry.
        // Incrementing the zero-extended suffix uses one clean lane per
        // intermediate carry, all returned clean before the lower UMA sweep.
        self.cinc_clean(a[a.len()-1], high, zero);
        for i in (0..a.len()).rev() {
            self.uma(if i == 0 { c0 } else { a[i - 1] }, low[i], a[i]);
        }
    }
    pub fn add(&mut self, a: &[u16], b: &[u16], c0: u16, ctrl: i32, cout: i32) { let n = a.len(); assert!(b.len() == n && n > 0, "add widths");
        let top=n-1;
        for i in 0..top { self.maj(if i==0 {c0} else {a[i-1]},b[i],a[i]); }
        let x=if top==0 {c0} else {a[top-1]};
        if cout < 0 { self.sum_top(x,b[top],a[top],ctrl); }
        else if ctrl < 0 {
            // Share the two parity preparations between carry-out and sum.
            let (y,z,flag)=(b[top],a[top],cout as u16);
            self.cx(z,y); self.cx(z,x); self.ccx(x,y,flag); self.cx(z,flag);
            self.cx(z,x); self.cx(x,y);
        } else {
            self.maj(x,b[top],a[top]); self.ccx(ctrl as u16,a[top],cout as u16);
            self.uma_c(ctrl as u16,x,b[top],a[top]);
        }
        for i in (0..top).rev() {
            let x=if i==0 {c0} else {a[i-1]};
            if ctrl >= 0 {self.uma_c(ctrl as u16,x,b[i],a[i]);} else {self.uma(x,b[i],a[i]);}
        }
    }
    pub fn sub(&mut self, a: &[u16], b: &[u16], c0: u16, ctrl: i32, cout: i32) {
        if cout >= 0 { self.xs(b); self.add(a, b, c0, ctrl, cout); self.xs(b); return; }
        let n = a.len(); assert!(b.len() == n && n > 0, "sub widths");
        let top=n-1;
        for i in 0..top {
            let x=if i==0 {c0} else {a[i-1]};
            if ctrl >= 0 {self.uma_c_inv(ctrl as u16,x,b[i],a[i]);} else {self.uma_inv(x,b[i],a[i]);}
        }
        self.sum_top(if top==0 {c0} else {a[top-1]},b[top],a[top],ctrl);
        for i in (0..top).rev() {self.maj_inv(if i==0 {c0} else {a[i-1]},b[i],a[i]);}
    }
    pub fn carry(&mut self, a: &[u16], b: &[u16], c0: u16, flag: u16, ctrl: i32) { let n = a.len(); assert!(b.len() == n && n > 0, "carry widths");
        let top=n-1;
        for i in 0..top {self.maj(if i==0 {c0} else {a[i-1]},b[i],a[i]);}
        self.copy_top_carry(if top==0 {c0} else {a[top-1]},b[top],a[top],flag,ctrl);
        for i in (0..top).rev() {self.maj_inv(if i==0 {c0} else {a[i-1]},b[i],a[i]);}
    }
    pub fn gt(&mut self, a: &[u16], b: &[u16], c0: u16, flag: u16, ctrl: i32) { let n = a.len(); assert!(b.len() == n, "gt widths");
        self.xs(b); self.carry(a,b,c0,flag,ctrl); self.xs(b); }
    pub fn swap(&mut self, a: u16, b: u16) { self.cx(a, b); self.cx(b, a); self.cx(a, b); }
    /// lane i -> lane i + 1 (top lane wraps to lane 0)
    pub fn rot1_up(&mut self, reg: &[u16]) { for i in (1..reg.len()).rev() { self.swap(reg[i], reg[i - 1]); } }
    // ---- scan macros
    pub fn fan(&mut self, ctl: u16, r: &[u16]) { for &q in r { self.cx(ctl, q); } }
    /// C += ctl with clean carry lanes
    pub fn cinc_clean(&mut self, ctl: u16, c: &[u16], anc: &[u16]) { let n = c.len(); if n == 0 { return; }
        if n > 1 { self.carry_and(ctl,c[0],anc[0],false); for i in 1..n - 1 { self.carry_and(anc[i-1],c[i],anc[i],false); }
            for i in (1..n).rev() { self.cx(anc[i - 1], c[i]); if i >= 2 { self.carry_and(anc[i-2],c[i-1],anc[i-1],true); } else { self.carry_and(ctl,c[0],anc[0],true); } } }
        self.cx(ctl, c[0]); }
    /// target ^= [all controls are 1], with borrowed lanes d (|d| = |ctrl| - 2): Barenco V-chain, run twice
    pub fn mcx(&mut self, ctrl: &[u16], target: u16, d: &[u16]) { let k = ctrl.len();
        match k { 0 => self.x(target), 1 => self.cx(ctrl[0], target), 2 => self.ccx(ctrl[0], ctrl[1], target),
            _ => for _ in 0..2 { self.ccx(ctrl[k - 1], d[k - 3], target); for i in (2..=k - 2).rev() { self.ccx(ctrl[i], d[i - 2], d[i - 1]); } self.ccx(ctrl[0], ctrl[1], d[0]); for i in 2..=k - 2 { self.ccx(ctrl[i], d[i - 2], d[i - 1]); } } } }
    /// target ^= [all controls are 0]
    pub fn mcx_neg(&mut self, ctrl: &[u16], target: u16, d: &[u16]) { self.xs(ctrl); self.mcx(ctrl, target, d); self.xs(ctrl); }
}

// A temporary product becomes an ordinary CCX in the compute direction and
// an HMR plus a conditional CZ in the erase direction. Toggle accepts a live
// destination and uses an ordinary, self-inverse CCX in either direction.
#[derive(Clone, Copy)]
enum ProductUse { Compute, Erase, Toggle }

impl Vm<'_> {
    fn constant_product(&mut self, a: u16, b: u16, out: u16,
                        linear: [Option<u16>; 2], usage: ProductUse) {
        let add_linear = |vm: &mut Self| {
            if linear[0] != linear[1] {
                for &wire in linear.iter().flatten() { vm.cx(wire, out); }
            }
        };
        match usage {
            ProductUse::Compute => { self.carry_and(a, b, out, false); add_linear(self); }
            ProductUse::Erase => { add_linear(self); self.carry_and(a, b, out, true); }
            ProductUse::Toggle => { self.ccx(a, b, out); add_linear(self); }
        }
    }

    /// flag ^= (x >= threshold), for any n-bit x and either initial flag.
    /// work starts and ends clean. Only n-2 of its lanes can be used.
    pub fn constant_ge(&mut self, x: &[u16], threshold: u32, flag: u16, work: &[u16]) {
        let n = x.len();
        assert!((1..32).contains(&n) && threshold > 0 && threshold < 1u32 << n);
        let delta = (1u32 << n) - threshold;
        let lo = delta.trailing_zeros() as usize;
        if lo + 1 == n { self.cx(x[lo], flag); return; }
        assert!(work.len() >= n - lo - 2);
        // Adding delta gives carry x[lo] above its first set bit. Above it
        // the next carry is a AND b for a zero digit and a OR b for a one.
        let step = |vm: &mut Self, i: usize, out: u16, usage| {
            let a = if i == lo + 1 { x[lo] } else { work[i - lo - 2] };
            let b = x[i];
            let linear = if delta & (1 << i) == 0 { [None, None] } else { [Some(a), Some(b)] };
            vm.constant_product(a, b, out, linear, usage);
        };
        for i in lo + 1..n - 1 { step(self, i, work[i - lo - 1], ProductUse::Compute); }
        step(self, n - 1, flag, ProductUse::Toggle);
        for i in (lo + 1..n - 1).rev() { step(self, i, work[i - lo - 1], ProductUse::Erase); }
    }

    /// x += f*value modulo 2^n. x and f can have arbitrary initial values.
    /// p_i is the amount to XOR into x_i. For constant digit k_i,
    /// p_(i+1) = (x_i XOR k_i)*p_i XOR (k_i XOR k_(i+1))*f.
    pub fn add_guarded_constant(&mut self, x: &[u16], f: u16, value: u32, work: &[u16]) {
        let n = x.len();
        assert!((1..32).contains(&n) && value < 1u32 << n);
        if value == 0 { return; }
        let lo = value.trailing_zeros() as usize;
        let source = |i| if i == lo { f } else { work[i - lo - 1] };
        let step = |vm: &mut Self, i: usize, out: u16, usage| {
            let a = source(i);
            let digit = value >> i;
            let linear = [(digit & 1 != 0).then_some(a), ((digit ^ (digit >> 1)) & 1 != 0).then_some(f)];
            vm.constant_product(a, x[i], out, linear, usage);
        };
        if lo + 1 < n {
            assert!(work.len() >= n - lo - 2);
            for i in lo..n - 2 { step(self, i, work[i - lo], ProductUse::Compute); }
            // The last product toggles the live top bit directly.
            step(self, n - 2, x[n - 1], ProductUse::Toggle);
            for i in (lo..n - 2).rev() {
                self.cx(source(i + 1), x[i + 1]);
                step(self, i, work[i - lo], ProductUse::Erase);
            }
        }
        self.cx(f, x[lo]);
    }
}
