//! Extract an exact commuting island in source order. Each spectator is
//! independently checked against every selected gate preceding it. The
//! selected two-product region is synthesized and its full truth table
//! re-executed before emitting the original spectators and new region.
use super::*;
#[derive(Clone, Copy)]
enum Local {
    Q(Plan),
    C(Two),
}
impl Local {
    fn count(self) -> usize {
        match self {
            Self::Q(p) => p.count,
            Self::C(_) => 2,
        }
    }
}
#[derive(Default, Clone, Copy)]
struct Memo {
    value: [u64; MAX],
    n: u8,
    old: u8,
    sol: Option<Local>,
}
struct Cache {
    m: Vec<Memo>,
    c: Table,
}
impl Cache {
    fn new() -> Self {
        Self {
            m: vec![Memo::default(); 16384],
            c: Table::new(),
        }
    }
    fn best(&mut self, ch: &Chart, old: usize) -> Option<Local> {
        let mut h = (old as u64).wrapping_mul(0x94d049bb133111eb);
        for (i, &v) in ch.value[..ch.n].iter().enumerate() {
            h = h.rotate_left(17)
                ^ v.rotate_left((7 * i) as u32)
                    .wrapping_mul(0x9e3779b97f4a7c15);
        }
        let at = (h ^ (h >> 29)) as usize & (self.m.len() - 1);
        let e = self.m[at];
        if e.n as usize == ch.n && e.old as usize == old && e.value == ch.value {
            return e.sol;
        }
        let sol = if let Some(p) = classify(ch, old) {
            Some(Local::Q(p))
        } else if old > 2 {
            self.c.solve(ch).map(Local::C)
        } else {
            None
        };
        self.m[at] = Memo {
            value: ch.value,
            n: ch.n as u8,
            old: old as u8,
            sol,
        };
        sol
    }
}
struct Foot {
    read: u8,
    write: u8,
}
impl Foot {
    fn flag(ch: &Chart, q: QubitId) -> u8 {
        if q == NO_QUBIT {
            0
        } else {
            ch.wires[..ch.n]
                .iter()
                .position(|&z| z == q)
                .map_or(0, |x| 1 << x)
        }
    }
    fn masks(&self, ch: &Chart, g: Op) -> (u8, u8, u8) {
        (
            Self::flag(ch, g.q_control2),
            Self::flag(ch, g.q_control1),
            Self::flag(ch, g.q_target),
        )
    }
    fn add(&mut self, ch: &Chart, g: Op) {
        let (b, a, t) = self.masks(ch, g);
        match g.kind {
            K::X => self.write |= t,
            K::CX | K::CCX => {
                self.read |= a | b;
                self.write |= t;
            }
            K::Swap => {
                self.read |= a | t;
                self.write |= a | t;
            }
            _ => unreachable!(),
        }
    }
    fn commutes(&self, ch: &Chart, g: Op) -> bool {
        let (b, a, t) = self.masks(ch, g);
        match g.kind {
            K::Neg | K::BitStore0 | K::BitStore1 | K::BitInvert => true,
            K::X | K::CX | K::CCX => (self.read & t) == 0 && self.write & (a | b) == 0,
            K::CZ | K::CCZ | K::Z => self.write & (a | b | t) == 0,
            K::Hmr | K::R | K::Swap => (self.read | self.write) & (a | t) == 0,
            K::PushCondition
            | K::PopCondition
            | K::AppendToRegister
            | K::Register
            | K::DebugPrint => false,
        }
    }
    fn include(&self, ch: &Chart, g: Op) -> bool {
        if g.c_condition != NO_BIT || !matches!(g.kind, K::X | K::CX | K::CCX | K::Swap) {
            return false;
        }
        let (b, a, t) = self.masks(ch, g);
        let count = match g.kind {
            K::X => 1,
            K::CX | K::Swap => 2,
            _ => 3,
        };
        let known = (a | b | t).count_ones() as usize;
        if known == 0 || ch.n + count - known > MAX {
            return false;
        }
        if known < count && self.commutes(ch, g) {
            if g.kind != K::CCX {
                return false;
            }
            if self.write & t == 0 && (a == 0 || b == 0) {
                return false;
            }
        }
        true
    }
}
#[derive(Default, Debug)]
pub(crate) struct Real {
    pub saved: u64,
    pub groups: u64,
    pub quadratic: u64,
    pub cubic: u64,
    pub quadratic_saved: u64,
    pub cubic_saved: u64,
    pub nonadjacent: u64,
    pub skipped_charged: u64,
    pub skipped_measure: u64,
    pub extra: i64,
    pub limited: u64,
}
fn allows(selected: Op, spectator: Op) -> bool {
    // A second check on the actual earlier gates, independent of the compact
    // accumulated footprint used during discovery.
    let s = [selected.q_control1, selected.q_control2, selected.q_target];
    let read = |q: QubitId| {
        q != NO_QUBIT
            && (selected.q_control1 == q
                || selected.q_control2 == q
                || (selected.kind == K::Swap && selected.q_target == q))
    };
    let write = |q: QubitId| {
        q != NO_QUBIT
            && (selected.q_target == q || (selected.kind == K::Swap && selected.q_control1 == q))
    };
    let (a, b, t) = (
        spectator.q_control1,
        spectator.q_control2,
        spectator.q_target,
    );
    match spectator.kind {
        K::Neg | K::BitStore0 | K::BitStore1 | K::BitInvert => true,
        K::X | K::CX | K::CCX => !read(t) && !write(a) && !write(b),
        K::Z | K::CZ | K::CCZ => !write(t) && !write(a) && !write(b),
        K::R | K::Hmr => !s.contains(&t),
        K::Swap => !s.contains(&a) && !s.contains(&t),
        K::PushCondition | K::PopCondition | K::Register | K::AppendToRegister | K::DebugPrint => {
            false
        }
    }
}
fn shrink(
    src: &[Op],
    out: &mut Vec<Op>,
    cache: &mut Cache,
    syn: &mut Synthesis,
    mut credit: usize,
    c: &mut Real,
) {
    let mut i = 0;
    while i < src.len() {
        let head = src[i];
        if head.kind != K::CCX || head.c_condition != NO_BIT {
            out.push(head);
            i += 1;
            continue;
        }
        let mut ch = Chart::new();
        ch.step(head).unwrap();
        let mut foot = Foot { read: 0, write: 0 };
        foot.add(&ch, head);
        let mut charge = 1;
        let mut selected = 1u64;
        let mut best = None;
        let mut score = (0, 0);
        let (mut skipped, mut sm, mut st) = (0, 0, 0);
        for j in i + 1..src.len().min(i + 48) {
            let g = src[j];
            if foot.include(&ch, g) {
                ch.step(g).unwrap();
                foot.add(&ch, g);
                selected |= 1u64 << (j - i);
                if g.kind == K::CCX {
                    charge += 1;
                    if charge >= 3 {
                        if let Some(p) = cache.best(&ch, charge) {
                            let save = charge - p.count();
                            if save >= score.0 {
                                match p {
                                    Local::Q(plan) => syn.realize(&ch, &plan),
                                    Local::C(plan) => syn.cubic_realize(&ch, plan),
                                }
                                let initial = selected.count_ones() as usize;
                                let delta = syn.native.len().saturating_sub(initial);
                                let priority = (save, usize::MAX - delta);
                                if delta <= 32 * save && delta <= credit {
                                    if priority > score {
                                        score = priority;
                                        best = Some((
                                            j,
                                            selected,
                                            save,
                                            matches!(p, Local::Q(_)),
                                            skipped,
                                            sm,
                                            st,
                                        ));
                                        syn.best.clear();
                                        syn.best.extend_from_slice(&syn.native);
                                    }
                                } else {
                                    c.limited += 1;
                                }
                            }
                        }
                    }
                    if charge == 6 {
                        break;
                    }
                }
            } else if foot.commutes(&ch, g) {
                skipped += 1;
                sm += usize::from(matches!(g.kind, K::Hmr | K::R));
                st += usize::from(matches!(g.kind, K::CCX | K::CCZ));
            } else {
                break;
            }
        }
        if let Some((j, selected, save, quad, skips, sm, st)) = best {
            for (k, &g) in src[i..=j].iter().enumerate() {
                if selected >> k & 1 == 0 {
                    let mut prior = selected & ((1u64 << k) - 1);
                    while prior != 0 {
                        let p = prior.trailing_zeros() as usize;
                        prior &= prior - 1;
                        assert!(
                            allows(src[i + p], g),
                            "spectator blocks source-order region movement"
                        );
                    }
                    out.push(g);
                }
            }
            out.extend_from_slice(&syn.best);
            let old = selected.count_ones() as usize;
            credit = credit + old - syn.best.len();
            c.saved += save as u64;
            c.groups += 1;
            c.extra += syn.best.len() as i64 - old as i64;
            c.nonadjacent += u64::from(skips > 0);
            c.skipped_charged += u64::from(st > 0);
            c.skipped_measure += u64::from(sm > 0);
            if quad {
                c.quadratic += 1;
                c.quadratic_saved += save as u64;
            } else {
                c.cubic += 1;
                c.cubic_saved += save as u64;
            }
            i = j + 1;
        } else {
            out.push(head);
            i += 1
        }
    }
}
pub fn apply(ops: &mut Vec<Op>) -> Real {
    let n = ops.len();
    let layout = (ops.as_ptr(), ops.capacity());
    let gap = (ops.capacity() - n)
        .saturating_sub(2)
        .min(n.div_ceil(64))
        .min(1 << 24);
    if gap != 0 {
        ops.resize(n + gap, Op::empty());
        ops.copy_within(0..n, gap);
    }
    let mut src = Vec::with_capacity(16384);
    let mut out = Vec::with_capacity(32768);
    let mut cache = Cache::new();
    let mut syn = Synthesis::new();
    let mut c = Real::default();
    let mut write = 0;
    for start in (0..n).step_by(16384) {
        let end = (start + 16384).min(n);
        src.clear();
        src.extend_from_slice(&ops[gap + start..gap + end]);
        out.clear();
        let room = (1024 + ((gap as u128) * (end as u128) / (n as u128)) as usize).min(gap);
        shrink(
            &src,
            &mut out,
            &mut cache,
            &mut syn,
            start + room - write,
            &mut c,
        );
        assert!(write + out.len() <= end + room);
        ops[write..write + out.len()].copy_from_slice(&out);
        write += out.len();
    }
    ops.truncate(write);
    assert_eq!(layout, (ops.as_ptr(), ops.capacity()));
    c
}
