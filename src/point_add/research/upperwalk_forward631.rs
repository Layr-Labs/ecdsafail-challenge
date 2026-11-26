//! Verified code-only forward upper walk; no tape or table assets.
//! Frame/API and exact seam contract: experiments/forward631_opt_20261119/INTEGRATION.txt.
#[path = "upperwalk_forward631_codegen.rs"]
mod codegen;
pub use codegen::{canonical_column, column, forward, prefix, terminal, Cost, Frame, Ports};
