//! Counts in the tree's own `counts()` convention (lane A's rtool io.rs `Counts`, unchanged): ops, native CCX+CCZ,
//! expected T with 0.5 per condition level. Logging only.
use crate::circuit::{Op, OperationType};

/// Counts in the tree's own `counts()` convention: (ops, native CCX+CCZ, expected with 0.5 per condition level).
#[derive(Default, Debug, Clone)]
pub struct Counts {
    pub ops: u64,
    pub native: u64,
    pub expected2: u128, // expected * 2^depth-free fixed point: sum of 2^(32 - levels)
    pub depth0_ccx: u64,
    pub kinds: [u64; 18],
    pub nq: u64,
    pub nb: u64,
    pub maxdepth: usize,
    stack: Vec<u32>,
    lvl: u32,
}
impl Counts {
    #[inline]
    pub fn add(&mut self, op: &Op) {
        use OperationType::*;
        self.ops += 1;
        self.kinds[op.kind as usize] += 1;
        match op.kind {
            PushCondition => {
                self.stack.push(self.lvl);
                self.lvl += 1;
                self.maxdepth = self.maxdepth.max(self.stack.len());
            }
            PopCondition => self.lvl = self.stack.pop().expect("balanced"),
            CCX | CCZ => {
                self.native += 1;
                let l = self.lvl + if op.c_condition.0 == u64::MAX { 0 } else { 1 };
                self.expected2 += 1u128 << (32 - l);
                if l == 0 && op.kind == CCX {
                    self.depth0_ccx += 1;
                }
            }
            _ => {}
        }
        if op.kind != Register && op.kind != AppendToRegister && op.kind != DebugPrint {
            for q in [op.q_control2.0, op.q_control1.0, op.q_target.0] {
                if q != u64::MAX {
                    self.nq = self.nq.max(q + 1);
                }
            }
        }
        if op.kind != DebugPrint {
            for b in [op.c_target.0, op.c_condition.0] {
                if b != u64::MAX {
                    self.nb = self.nb.max(b + 1);
                }
            }
        }
    }
    pub fn expected(&self) -> f64 {
        self.expected2 as f64 / (1u64 << 32) as f64
    }
    pub fn line(&self) -> String {
        format!(
            "ops {} native {} expected {:.1} depth0_ccx {} nq {} nb {} maxdepth {} hmr {} swap {} cx {} x {} cz {} ccz {} push {}",
            self.ops, self.native, self.expected(), self.depth0_ccx, self.nq, self.nb, self.maxdepth,
            self.kinds[12], self.kinds[10], self.kinds[8], self.kinds[6], self.kinds[9], self.kinds[14], self.kinds[15]
        )
    }
}

/// The three numbers of the pass log lines (ops, native, expected), cheaper per op than `Counts`.
#[derive(Default, Debug, Clone)]
pub struct Lite {
    pub ops: u64,
    pub native: u64,
    expected2: u128,
    stack: Vec<u32>,
    lvl: u32,
}
impl Lite {
    #[inline]
    pub fn add(&mut self, op: &Op) {
        use OperationType::*;
        self.ops += 1;
        match op.kind {
            PushCondition => {
                self.stack.push(self.lvl);
                self.lvl += 1;
            }
            PopCondition => self.lvl = self.stack.pop().expect("balanced"),
            CCX | CCZ => {
                self.native += 1;
                let l = self.lvl + if op.c_condition.0 == u64::MAX { 0 } else { 1 };
                self.expected2 += 1u128 << (32 - l);
            }
            _ => {}
        }
    }
    pub fn expected(&self) -> f64 {
        self.expected2 as f64 / (1u64 << 32) as f64
    }
}
