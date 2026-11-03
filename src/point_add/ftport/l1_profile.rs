//! Dev-only source scopes for the L1 shell arithmetic. Markers live in the gate IR,
//! never the benchmark operation stream, and reverse with recorded operations.
use crate::circuit::{Op, OperationType as K, NO_BIT};
use std::cell::RefCell;

thread_local! { static CONTEXT: RefCell<Option<String>> = const { RefCell::new(None) }; }

/// Scope only real adapter calls, not the adapter's scratch-size dry runs.
pub(crate) struct Context(Option<String>);
impl Context {
    pub(crate) fn enter(name: String) -> Self {
        Self(CONTEXT.with(|c| c.replace(if std::env::var_os("L1_PROFILE").is_some() {
            Some(name.replace(',', "/"))
        } else { None })))
    }
}
impl Drop for Context {
    fn drop(&mut self) { CONTEXT.with(|c| { c.replace(self.0.take()); }); }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Tag {
    pub name: &'static str,
    pub slot: i32,
    pub width: usize,
    pub pool: usize,
}

struct Frame { id: u64, parent: u64, tag: Tag, reverse: bool, at: usize, depth: u32 }
pub(crate) struct Profile {
    name: String,
    next: u64,
    frames: Vec<Frame>,
    pub muted: bool,
    pub cells: bool,
}
impl Profile {
    pub fn new() -> Option<Self> {
        CONTEXT.with(|c| c.borrow().as_ref().map(|name| Self {
            name: name.clone(), next: 1, frames: Vec::new(), muted: false,
            cells: std::env::var_os("L1_PROFILE_CELLS").is_some(),
        }))
    }
    pub fn begin(&mut self, tag: Tag, reverse: bool, at: usize, depth: u32) {
        if self.muted { return; }
        let parent = self.frames.last().map_or(0, |f| f.id);
        let id = self.next;
        self.next += 1;
        self.frames.push(Frame { id, parent, tag, reverse, at, depth });
    }
    pub fn end(&mut self, tag: Tag, reverse: bool, ops: &[Op]) {
        if self.muted { return; }
        let f = self.frames.pop().expect("L1 profile scope underflow");
        assert_eq!((f.tag.name, f.tag.slot, f.reverse), (tag.name, tag.slot, reverse), "L1 scope mismatch");
        let mut native = 0u64;
        let mut expected = 0.0;
        let mut depth = f.depth as i32;
        for op in &ops[f.at..] {
            match op.kind {
                K::PushCondition => depth += 1,
                K::PopCondition => depth -= 1,
                K::CCX | K::CCZ => {
                    native += 1;
                    expected += 2f64.powi(-depth) * if op.c_condition == NO_BIT { 1.0 } else { 0.5 };
                }
                _ => {}
            }
        }
        // Inclusive scopes: subtract immediate children's costs for an exclusive census.
        eprintln!("L1PROF,{},{},{},{},{},{},{},{},{},{},{:.3}",
            self.name, f.id, f.parent, f.tag.name, f.tag.slot, f.tag.width,
            f.tag.pool, u8::from(f.reverse), ops.len() - f.at, native, expected);
    }
}
