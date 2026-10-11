//! Exact-header effective threshold channel, bounded research port.
//! The header encodes K modulo64 on a promised public support [lo,hi].
//! No complete packed clock or production width claim follows from this helper.
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;

fn literal(c: &mut Builder, q: Q, positive: bool) {
    if !positive { c.x(q); }
}

struct Tree<'a, F> {
    h: &'a [Q; 6],
    nodes: &'a [Q; 5],
    flag: Q,
    descending: bool,
    body: &'a mut F,
}

impl<F: FnMut(&mut Builder, usize, Q, Q)> Tree<'_, F> {
    fn visit(&mut self, c: &mut Builder, ctrl: Q, ks: &[usize], domain: &[usize], bit: usize, depth: usize) {
        if bit == 0 {
            for &k in ks {
                if domain.len() == 1 {
                    c.cx(ctrl, self.flag);
                } else {
                    literal(c, self.h[0], k & 1 != 0);
                    c.ccx(ctrl, self.h[0], self.flag);
                    literal(c, self.h[0], k & 1 != 0);
                }
                // Header, g, held nodes and flag are controls only. The supplied
                // early-cleared node0 must be restored by every callback.
                (self.body)(c, k, self.flag, self.nodes[0]);
            }
            return;
        }
        let partition = |v: &[usize], pol: bool| -> Vec<usize> {
            v.iter().copied().filter(|k| ((k % 64) >> bit & 1 != 0) == pol).collect()
        };
        let zero = partition(ks, false);
        let one = partition(ks, true);
        let dzero = partition(domain, false);
        let done = partition(domain, true);
        if zero.is_empty() || one.is_empty() {
            let pol = zero.is_empty();
            let (child, dchild, other) = if pol { (&one, &done, &dzero) } else { (&zero, &dzero, &done) };
            if other.is_empty() {
                self.visit(c, ctrl, child, dchild, bit - 1, depth);
                return;
            }
            let q = self.nodes[depth];
            literal(c, self.h[bit], pol);
            c.ccx(ctrl, self.h[bit], q);
            literal(c, self.h[bit], pol);
            self.visit(c, q, child, dchild, bit - 1, depth + 1);
            let m = c.alloc_bit();
            c.hmr(q, m);
            literal(c, self.h[bit], pol);
            c.cz_if(ctrl, self.h[bit], m);
            literal(c, self.h[bit], pol);
            c.free_bit(m);
            return;
        }
        let q = self.nodes[depth];
        let (first, second, dfirst, dsecond) = if self.descending {
            (&one, &zero, &done, &dzero)
        } else { (&zero, &one, &dzero, &done) };
        literal(c, self.h[bit], self.descending);
        c.ccx(ctrl, self.h[bit], q);
        literal(c, self.h[bit], self.descending);
        self.visit(c, q, first, dfirst, bit - 1, depth + 1);
        c.cx(ctrl, q);
        self.visit(c, q, second, dsecond, bit - 1, depth + 1);
        let m = c.alloc_bit();
        c.hmr(q, m);
        literal(c, self.h[bit], !self.descending);
        c.cz_if(ctrl, self.h[bit], m);
        literal(c, self.h[bit], !self.descending);
        c.free_bit(m);
    }
}

/// Callback sees g*[K>k] ascending or g*[K>=k] descending. Five clean
/// node owners and one clean flag are required. Node0 is clean at callbacks;
/// together with one caller carry owner this is seven work wires.
/// All header/g/held-node owners must remain unchanged across callbacks.
#[allow(clippy::too_many_arguments)]
pub fn stream<F: FnMut(&mut Builder, usize, Q, Q)>(
    c: &mut Builder, h: &[Q; 6], nodes: &[Q; 5], flag: Q,
    g: Q, lo: usize, hi: usize, descending: bool, g_positive: bool,
    mut body: F,
) {
    assert!(lo <= hi && hi - lo < 64, "header residues must be unique");
    let mut labels: Vec<usize> = (lo..=hi).collect();
    if descending { labels.reverse(); }
    if !descending {
        c.cx(g, flag);
        if !g_positive { c.x(flag); }
    }
    let mut tree = Tree { h, nodes, flag, descending, body: &mut body };
    let mut begin = 0;
    while begin < labels.len() {
        let group = labels[begin] % 64 >> 4;
        let mut end = begin + 1;
        while end < labels.len() && labels[end] % 64 >> 4 == group { end += 1; }
        let p4 = group & 1 != 0;
        let p5 = group & 2 != 0;
        literal(c, g, g_positive);
        literal(c, h[5], p5);
        c.ccx(g, h[5], nodes[0]);
        literal(c, h[5], p5);
        literal(c, g, g_positive);
        literal(c, h[4], p4);
        c.ccx(nodes[0], h[4], nodes[1]);
        literal(c, h[4], p4);
        let m = c.alloc_bit();
        c.hmr(nodes[0], m);
        literal(c, g, g_positive);
        literal(c, h[5], p5);
        c.cz_if(g, h[5], m);
        literal(c, h[5], p5);
        literal(c, g, g_positive);
        c.free_bit(m);
        let domain: Vec<usize> = labels.iter().copied().filter(|k| k % 64 >> 4 == group).collect();
        tree.visit(c, nodes[1], &labels[begin..end], &domain, 3, 2);
        let m = c.alloc_bit();
        c.hmr(nodes[1], m);
        c.push_condition(m);
        literal(c, g, g_positive);
        literal(c, h[5], p5);
        literal(c, h[4], p4);
        c.ccz(g, h[5], h[4]);
        literal(c, h[4], p4);
        literal(c, h[5], p5);
        literal(c, g, g_positive);
        c.pop_condition();
        c.free_bit(m);
        begin = end;
    }
    if descending {
        c.cx(g, flag);
        if !g_positive { c.x(flag); }
    }
}
