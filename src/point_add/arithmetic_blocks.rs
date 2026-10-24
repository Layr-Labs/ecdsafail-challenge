//! Ordered arithmetic programs for the full-width replay boundary.
//!
//! Each backend supplies disjoint data registers and unchanged controls.
//! A kernel must clear its scratch and repair measurement phases before return.
//! `Add` adds the signed source into the target. `Sub` subtracts that source.
//! `Half` and `Double` act modulo the backend's odd field modulus.
//! The source variants use the same modulus. `Swap` exchanges both registers.
//!
//! The parser checks syntax. The fixed evaluator checks the proposed map.
//! In particular, reordered programs remain candidates until validation.
//! Measurement tests follow https://algassert.com/post/1903.
//! Constant carry reconstruction follows the supplied backend and Gidney's
//! https://arxiv.org/abs/2507.23079; this module claims no new adder theorem.
use std::cell::Cell;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation { Swap, Add, Sub, Half, Double, HalfU, DoubleU }

impl Operation {
    pub fn inverse(self) -> Self {
        match self {
            Self::Swap => Self::Swap,
            Self::Add => Self::Sub, Self::Sub => Self::Add,
            Self::Half => Self::Double, Self::Double => Self::Half,
            Self::HalfU => Self::DoubleU, Self::DoubleU => Self::HalfU,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lowering {
    Direct,
    /// Use the sparser signed binary constant, with at most eight terms.
    /// Dense constants use the direct kernel at the same arithmetic width.
    Power2,
}

thread_local! { static LOWERING: Cell<Lowering> = const { Cell::new(Lowering::Direct) }; }

impl Lowering {
    pub fn current() -> Self { LOWERING.with(Cell::get) }

    /// Select one lowering for this instruction and restore the caller's mode.
    pub fn with_scope<T>(self, f: impl FnOnce() -> T) -> T {
        struct Restore(Lowering);
        impl Drop for Restore {
            fn drop(&mut self) { LOWERING.with(|slot| slot.set(self.0)); }
        }
        let old = LOWERING.with(|slot| slot.replace(self));
        let _restore = Restore(old);
        f()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Instruction { pub op: Operation, pub lowering: Lowering }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction { Forward, Inverse }

/// The backend owns data layout, controls, scratch allocation, and phase repair.
pub trait Kernel { fn emit(&mut self, op: Operation, lowering: Lowering); }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program { instructions: Vec<Instruction> }

impl Program {
    /// Parse one to eight comma-separated `OP:LOWERING` instructions.
    pub fn parse(text: &str) -> Result<Self, String> {
        let mut instructions = Vec::new();
        for token in text.split(',') {
            let (op, mode) = token.split_once(':').ok_or("block instruction requires OP:LOWERING")?;
            let op = match op {
                "swap" => Operation::Swap, "add" => Operation::Add,
                "sub" => Operation::Sub, "half" => Operation::Half,
                "double" => Operation::Double, "half_u" => Operation::HalfU,
                "double_u" => Operation::DoubleU,
                _ => return Err(format!("unsupported block operation {op}")),
            };
            let lowering = match mode {
                "direct" => Lowering::Direct, "power2" => Lowering::Power2,
                _ => return Err(format!("unsupported block lowering {mode}")),
            };
            instructions.push(Instruction { op, lowering });
            if instructions.len() > 8 { return Err("block program needs one to eight instructions".into()); }
        }
        Ok(Self { instructions })
    }

    pub fn instructions(&self) -> &[Instruction] { &self.instructions }

    pub fn inverse(&self) -> Self {
        Self { instructions: self.instructions.iter().rev().map(|i|
            Instruction { op: i.op.inverse(), lowering: i.lowering }).collect() }
    }

    pub fn emit<K: Kernel>(&self, kernel: &mut K, direction: Direction) {
        let emit = |kernel: &mut K, i: &Instruction| {
            i.lowering.with_scope(|| kernel.emit(i.op, i.lowering));
        };
        match direction {
            Direction::Forward => for i in &self.instructions { emit(kernel, i); },
            Direction::Inverse => for i in self.instructions.iter().rev() {
                emit(kernel, &Instruction { op: i.op.inverse(), lowering: i.lowering });
            },
        }
    }
}

#[cfg(test)]
#[path = "arithmetic_blocks_tests.rs"]
mod tests;
