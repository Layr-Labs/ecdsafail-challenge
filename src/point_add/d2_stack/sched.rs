//! Classical schedules for the D2 stack/park blocks: checkpoints, per-tick N promise windows and detector
//! parameters.  Built from the private classical model's window table (`tools/ckmodel.rs ... noscan`,
//! `*_win.tsv`) with a margin, or directly (selftests).
use super::{DetParams, NWin};

#[derive(Clone, Debug)]
pub struct D2Sched {
    pub a: usize,
    pub ticks: usize,
    /// Checkpoint ticks d_0 < d_1 < ...; preg value i means "detected at d_i" (p_eff = d_i - 1).
    pub cks: Vec<usize>,
    pub push_win: Vec<Option<NWin>>,
    pub pop_win: Vec<Option<NWin>>,
    pub det: Vec<Option<DetParams>>,
    /// Checkpoint ticks run the detector after the push (`push -> detect -> tick_pop`) instead of before it:
    /// the `s` wire is clean during the detector (one wire of room), the detector sees N after the push.
    pub detect_after_push: bool,
    /// Detector parameters for the traversals with the payload half freed (empty: use `det`).
    pub det_high: Vec<Option<DetParams>>,
}

/// The default checkpoint list at R = 395: every 3 ticks over 350..375, every tick over 376..394 (28).
pub fn default_checkpoints() -> Vec<usize> {
    (350..376).step_by(3).chain(376..395).collect()
}

impl D2Sched {
    /// Index of the last checkpoint <= t.
    pub fn last_ck_index(&self, t: usize) -> Option<u64> {
        let n = self.cks.iter().take_while(|&&d| d <= t).count();
        (n > 0).then(|| (n - 1) as u64)
    }
    /// Smallest park-register width that holds every index plus the all-ones sentinel.
    pub fn pbits(&self) -> usize {
        let mut b = 1;
        while (1usize << b) - 1 < self.cks.len() {
            b += 1;
        }
        b
    }

    /// From a `ckmodel` window table.  Columns (t, then lo/hi pairs): Npre, push, tickpop, scan, xbl, ead,
    /// ckNpre, detM.  `margin` widens every N window and the zero-test top.
    pub fn from_model_table(text: &str, a: usize, cks: &[usize], margin: u64, pebbles: usize) -> Self {
        let mut rows: Vec<Vec<Option<(i64, i64)>>> = Vec::new();
        for l in text.lines() {
            if l.starts_with('#') || l.trim().is_empty() {
                continue;
            }
            let fs: Vec<&str> = l.split_whitespace().collect();
            let t: usize = fs[0].parse().unwrap();
            assert_eq!(t, rows.len());
            let mut r = Vec::new();
            for s in 0..8 {
                let (x, y) = (fs[1 + 2 * s], fs[2 + 2 * s]);
                r.push(if x == "-" { None } else { Some((x.parse().unwrap(), y.parse().unwrap())) });
            }
            rows.push(r);
        }
        let ticks = rows.len();
        assert!(cks.windows(2).all(|w| w[0] < w[1]) && *cks.last().unwrap() < ticks);
        let m = margin as i64;
        let widen = |w: (i64, i64)| -> NWin { ((w.0 - m).max(0) as u64, (w.1 + m) as u64) };
        let mut s = D2Sched {
            a,
            ticks,
            cks: cks.to_vec(),
            push_win: vec![None; ticks],
            pop_win: vec![None; ticks],
            det: vec![None; ticks],
            detect_after_push: false,
            det_high: Vec::new(),
        };
        for t in 0..ticks {
            let npre = rows[t][0].unwrap();
            let nf = n_feasible(a, t);
            s.push_win[t] = rows[t][1].map(widen).map(|w| (w.0, w.1.min(nf - 1)));
            if t >= cks[0] {
                // every tick from the first checkpoint runs the pop block; unobserved ticks get the Npre range.
                let pw = widen(rows[t][2].unwrap_or(npre));
                s.pop_win[t] = Some((pw.0.max(1), pw.1.min(nf)));
            }
        }
        for (i, &d) in cks.iter().enumerate() {
            let npre = rows[d][0].unwrap();
            let xbl = rows[d][4].unwrap().1 as usize;
            let mlo = ((npre.0 - m).max(0) + 1) / 2;
            let mhi = (npre.1 + m + 1) / 2;
            s.det[d] = Some(DetParams { index: i as u64, top: xbl + margin as usize, m_lo: mlo as u64, m_hi: mhi as u64, pebbles, late_memb: false, dirty_lv: 0, stride: 0 });
        }
        s
    }

    /// Detector after the push: N grows by at most 1 before the detector, so every M window's top grows by 1
    /// (M = ceil(N/2)). The zero test then stops below the post-push stack bottom (`Ladd(M)` with the new M), which
    /// still covers every rail of a non-overflowing input.
    pub fn with_detect_after_push(mut self) -> Self {
        for d in self.det.iter_mut().flatten() {
            d.m_hi += 1;
            d.late_memb = true;
        }
        self.detect_after_push = true;
        self
    }
}

/// Largest stack count N whose stacks clear the typ wires after tick t (o(t+1) = ((t+2)/2, (t+1)/2)):
/// ceil(N/2) <= A - o_0 and floor(N/2) <= A - o_1.  Larger N is a storage overflow.
pub fn n_feasible(a: usize, t: usize) -> u64 {
    let o0 = (t + 2) / 2;
    let o1 = (t + 1) / 2;
    let mut n = 0u64;
    while ((n + 2) / 2) as usize <= a - o0 && ((n + 1) / 2) as usize <= a - o1 {
        n += 1;
    }
    n
}
