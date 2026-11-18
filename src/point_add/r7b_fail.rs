//! fb-r7b failing-walk hook (census only, never part of a graded stream): gate-level bit-sliced run of ONE forward F
//! pass on random inputs. Switched on by the env var R7B_FAIL=1; R7B_WORDS = shots / 64 (default 4096), R7B_SEED,
//! R7B_ECAP (gap cap override, see ecap() in mod.rs). The x values are the ones of r7b_census.rs (xorshift64, lanes
//! 0..511 lane-major), so NOTES/v9/r7_b/gap_census.py hook <seed> <words> <cap> rebuilds them.
//! A shot is BAD when (a) the passenger 256..511 is not restored, or (b) an F lane that ends constant on > 99.9 % of
//! the shots deviates. Prints the bad shot indices. The process exits after the run.
use super::{gl_loader, mac_expand, G, MAC, MACS, NONE};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

pub(super) fn run(gates: &[G], nlab: usize) {
    let nlab_f = nlab;
    let w: usize = std::env::var("R7B_WORDS").ok().and_then(|v| v.parse().ok()).unwrap_or(4096);
    let seed: u64 = std::env::var("R7B_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let macs = MACS.lock().unwrap().clone();
    let mut plain: Vec<G> = Vec::with_capacity(gates.len() * 2);
    for g in gates {
        if g.0 == MAC {
            mac_expand(&macs[g.1 as usize], &mut plain);
        } else {
            plain.push(*g);
        }
    }
    let nccx = plain.iter().filter(|g| g.2 != NONE).count();
    eprintln!("r7b fail: {} gates ({} CCX) after macro expansion, {} labels, {} shots, ecap {}", plain.len(), nccx, nlab, w * 64, 0);
    let mut st = vec![0u64; nlab * w];
    let mut rng = Rng(0x9E3779B97F4A7C15 ^ seed.wrapping_mul(0xD1B54A32D192ED03).wrapping_add(seed << 17));
    for _ in 0..8 {
        rng.next();
    }
    for l in 0..512 {
        for k in 0..w {
            st[l * w + k] = rng.next();
        }
    }
    let pas_in: Vec<u64> = st[256 * w..512 * w].to_vec();
    for g in &plain {
        if g.2 != NONE {
            let (a, b, c) = (gl_loader::lane_of(g.0) as usize, gl_loader::lane_of(g.1) as usize, gl_loader::lane_of(g.2) as usize);
            for k in 0..w {
                let v = st[a * w + k] & st[b * w + k];
                st[c * w + k] ^= v;
            }
        } else if g.1 != NONE {
            let (a, c) = (gl_loader::lane_of(g.0) as usize, gl_loader::lane_of(g.1) as usize);
            for k in 0..w {
                let v = st[a * w + k];
                st[c * w + k] ^= v;
            }
        } else {
            let c = gl_loader::lane_of(g.0) as usize;
            for k in 0..w {
                st[c * w + k] = !st[c * w + k];
            }
        }
    }
    let n = (w * 64) as u64;
    let mut good = vec![u64::MAX; w];
    let mut bad_pas = vec![0u64; w];
    for l in 256..512 {
        for k in 0..w {
            bad_pas[k] |= st[l * w + k] ^ pas_in[(l - 256) * w + k];
        }
    }
    let mut nl = 0usize;
    for l in (0..nlab_f).filter(|l| !(256..512).contains(l)) {
        let ones: u64 = st[l * w..(l + 1) * w].iter().map(|v| v.count_ones() as u64).sum();
        if ones * 1000 < n {
            for k in 0..w {
                good[k] &= !st[l * w + k];
            }
            nl += 1;
        } else if (n - ones) * 1000 < n {
            for k in 0..w {
                good[k] &= st[l * w + k];
            }
            nl += 1;
        }
    }
    let npas: u64 = bad_pas.iter().map(|v| v.count_ones() as u64).sum();
    let nlane: u64 = good.iter().map(|v| v.count_zeros() as u64).sum();
    let mut idx: Vec<String> = vec![];
    for k in 0..w {
        let b = !good[k] | bad_pas[k];
        for j in 0..64 {
            if (b >> j) & 1 == 1 {
                idx.push((k * 64 + j).to_string());
            }
        }
    }
    println!("R7B_FAIL ecap {} seed {} shots {} bad {} (lane {} of {} constant lanes, passenger {})", 0, seed, n, idx.len(), nlane, nl, npas);
    println!("R7B_BADIDX ecap {} seed {} : {}", 0, seed, idx.join(" "));
}
