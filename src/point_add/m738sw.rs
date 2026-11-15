//! Cut switches of the nineteen dead-work cuts (development aid of the port onto the fused-column walk).
//! (W2 = its three probe sites W2a, W2b, W2c.) Names: B1, P1..P7 (payload cuts), W1..W6 (walk cuts), M1, M2, M3A, M4A, M5A (map cuts).
//! `DEFAULT_ON` lists the accepted cuts; the environment variable M738_ON (comma list, or `all`, or `none`) overrides it
//! for development runs only. The official build runs with an empty environment, so it is exactly DEFAULT_ON.
use std::sync::OnceLock;

pub const NAMES: [&str; 21] = ["B1", "P1", "P2", "P3", "P4", "P5", "P6", "P7", "W1", "W2a", "W2b", "W2c", "W3", "W4", "W5", "W6", "M1", "M2", "M3A", "M4A", "M5A"];
/// accepted cuts. Left out on the fused-column walk: W2c (probe lanes below sz.0 - 1 in stage `probe_q`: replay differs on control-OK directed shots 28, 58, 90) and W6 (4,876 emitted, under the 5,000 floor).
pub const DEFAULT_ON: &str = "B1,P1,P2,P3,P4,P5,P6,P7,W1,W2a,W2b,W3,W4,W5,M1,M2,M3A,M4A,M5A";

fn mask() -> u32 {
    static M: OnceLock<u32> = OnceLock::new();
    *M.get_or_init(|| {
        let spec = DEFAULT_ON.to_string();
        let mut m = 0u32;
        for t in spec.split(',').map(|t| t.trim()).filter(|t| !t.is_empty()) {
            if t == "all" { m = (1 << NAMES.len()) - 1; continue; }
            if t == "none" { continue; }
            if t == "W2" { for s in ["W2a", "W2b", "W2c"] { m |= 1 << NAMES.iter().position(|n| *n == s).unwrap(); } continue; }
            match NAMES.iter().position(|n| *n == t) { Some(i) => m |= 1 << i, None => panic!("unknown cut {t}") }
        }
        m
    })
}
pub fn on(name: &str) -> bool {
    NAMES.iter().position(|n| *n == name).map_or(false, |i| mask() >> i & 1 == 1)
}
