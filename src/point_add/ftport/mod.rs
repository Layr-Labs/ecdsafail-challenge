//! s825 port: the frogtail/Lilypad builder and modp_ft arithmetic (odinfree's 852 tree, b4b51f02), used by the
//! greedyfrog shell through `super::ft_adapter` for its products and square. Only what modp_ft needs is copied.
#![allow(dead_code, unused_imports, unused_variables, unused_mut, unused_assignments)]
pub mod arith;
pub mod builder;
pub mod chunked;
pub mod frogdrop_sched;
pub mod mask;
pub mod modp_ft;

/// Stand-ins for the Lilypad shell constants modp_ft reads: the adapter sets the cap for each call.
pub mod pointadd_lilypad {
    thread_local! {
        pub static CAP: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    }
    /// Lilypad's PEAK0 (only its distance below 867 matters to modp_ft); 852 = the tree this was copied from.
    pub const PEAK0: u64 = 852;
    pub fn peak() -> u64 {
        CAP.with(|c| c.get())
    }
}

/// The native squares need the Leapfrog family's own builder (not ported): calling them is a bug here.
pub mod public_square_port {
    pub fn native_square_ops_at_cap(_cap: usize) -> Vec<crate::circuit::Op> {
        panic!("native square not ported into the greedyfrog tree")
    }
    pub fn native_flat_square_ops_at_cap(_cap: usize) -> Vec<crate::circuit::Op> {
        panic!("native flat square not ported into the greedyfrog tree")
    }
}
