pub type N = ruint::Uint<384, 6>;
pub fn p() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}
