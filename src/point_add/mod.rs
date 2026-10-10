//! Submission: Frogtail with even-tick digit erasure and average-T carry cleanup.
//! The source-pinned circuit is independent of environment selectors.
mod frogtail_batch;
mod public_square_port;

pub fn build() -> Vec<crate::circuit::Op> {
    frogtail_batch::build()
}
