//! Compile-time opt-in. Profiles and the default four-round path stay intact.

const fn is(raw: &str, expected: &[u8]) -> bool {
    let bytes = raw.as_bytes();
    if bytes.len() != expected.len() {
        return false;
    }
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != expected[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub(super) const REQUESTED: usize = match option_env!("HYBRID_CHECKPOINT_ROUNDS") {
    None => 4,
    Some(raw) => {
        if is(raw, b"4") {
            4
        } else if is(raw, b"14") {
            14
        } else {
            panic!("HYBRID_CHECKPOINT_ROUNDS must be4 or14")
        }
    }
};

pub(super) const fn eligible(widths: &[u8], rounds: usize, requested: usize) -> bool {
    if requested != 14 || rounds < 22 || rounds % 4 != 0 || widths.len() != rounds + 1 {
        return false;
    }
    let mut i = rounds - requested;
    while i <= rounds {
        if widths[i] != 4 {
            return false;
        }
        i += 1;
    }
    true
}

pub(super) const fn start(widths: &[u8], rounds: usize, original: usize) -> usize {
    if REQUESTED == 4 {
        return original;
    }
    assert!(
        original + 4 == rounds,
        "original checkpoint geometry changed"
    );
    assert!(
        eligible(widths, rounds, REQUESTED),
        "checkpoint14 requires all15 actual selected boundaries N-14..N to be width4; no width trimming or fallback to another profile"
    );
    rounds - REQUESTED
}
