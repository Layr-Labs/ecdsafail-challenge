// Append include!("q659_cross_word_tests.rs"); to the existing passing
// q659_parked_top_tests.rs TEST MODULE. Both belong below
// normalized_cross_arithmetic. All original declaration/guard helpers and
// the independently tested compact 129-cycle implementation are reused.
#[derive(Clone, Copy, Debug)]
struct WordCase {
    top: bool,
    bit: usize,
    ht: bool,
    unparked: bool,
}
impl WordCase {
    fn gate(self) -> Gate {
        if self.top {
            Gate::Top(self.bit)
        } else {
            Gate::Natural(self.bit)
        }
    }
    fn pos(self, i: usize) -> usize {
        if self.top {
            (256 + self.bit + 257 - i) % 257
        } else {
            256 - self.bit - i
        }
    }
    fn pass(self, y: usize, s: usize) -> bool {
        s + self.bit <= 31 && (!self.top || y + self.bit <= 128)
    }
}

// Transparent lower-fourteen prefix. On the normalized A=1 source,
// the data section starts at delta=127-E. Q[0..14] below delta may hold
// arbitrary parked quotients. EQ(E,127-i) toggles the interval membership
// exactly once. This source deliberately favors clarity over cached decoders.
fn explicit_prefix(
    b: &mut B,
    c: &Cross<'_>,
    t: &[QubitId],
    carry: QubitId,
    down: bool,
    d: &[QubitId],
) {
    let r = c.roles;
    let eq = |value: usize| {
        c.size
            .y
            .iter()
            .enumerate()
            .map(|(i, &q)| (q, value >> i & 1 == 0))
            .collect::<Vec<_>>()
    };
    let union = super::cover(&c.size.y, 114, 128);
    if down {
        super::xor_terms(b, &union, r.mask, &[], d);
        b.cswap(r.mask, carry, c.q[13]);
    }
    for step in 0..14 {
        let i = if down { 13 - step } else { step };
        let sel = eq(127 - i);
        let x = if i == 0 { carry } else { c.q[i - 1] };
        let first_swap = |b: &mut B| {
            if i > 0 {
                let previous = c.q[i - 1];
                let mut ct = sel.clone();
                ct.push((previous, false));
                b.cx(carry, previous);
                super::lit(b, &ct, carry, d);
                b.cx(carry, previous);
            }
        };
        if down {
            super::controlled_cell(b, c.q[i], t[i], x, r.mask, true, d);
            super::lower(b, c, c.q[i], t[i], x, false, d);
            first_swap(b);
            super::lit(b, &sel, r.mask, d);
        } else {
            super::lit(b, &sel, r.mask, d);
            first_swap(b);
            super::controlled_cell(b, c.q[i], t[i], x, r.mask, false, d);
        }
    }
    if !down {
        b.cswap(r.mask, carry, c.q[13]);
        super::xor_terms(b, &union, r.mask, &[], d);
    }
}

fn compact_divide_inplace(b: &mut B, c: &Cross<'_>, t: &[QubitId], case: WordCase) -> Vec<G> {
    let gate = case.gate();
    let r = c.roles;
    let hi = if case.top {
        c.y_bounds.1.min(128 - case.bit)
    } else {
        c.y_bounds.1
    };
    let prefix = hi >= 115 && !case.unparked;
    let first = if prefix { 14 } else { 128 - hi };
    let carry = if case.unparked { r.x128 } else { c.phase };
    let d = bank(c);
    let guard = witness(b, c, gate, &d);
    b.begin();
    b.play(&guard, false);
    if case.ht && !case.unparked {
        b.cx(r.activity, c.phase);
    }
    for &v in t {
        b.x(v);
    }
    if prefix {
        explicit_prefix(b, c, t, carry, false, &d);
    }
    for i in first..127 {
        super::cell(
            b,
            c.q[i],
            t[i],
            if i == first { carry } else { c.q[i - 1] },
            false,
        );
    }
    // Logical source[127]=1, so the missing MAJ carry-out is
    // complemented_target[127] OR carry_in. The physical q127 holds E6
    // and is never changed. The returned mask can expose this OR.
    let x = if first == 127 { carry } else { c.q[126] };
    let top = |b: &mut B| {
        b.cx(t[127], r.mask);
        b.cx(x, r.mask);
        b.ccx(t[127], x, r.mask);
    };
    top(b);
    super::normal_decision(b, r.activity, r.flight, t[128], r.mask, &d);
    super::lit(
        b,
        &[(r.activity, false), (r.flight, false), (r.mask, false)],
        t[128],
        &d,
    );
    top(b);
    b.ccx(r.activity, r.flight, r.mask);
    b.cx(r.mask, t[127]);
    b.ccx(r.mask, x, t[127]);
    for i in (first..127).rev() {
        let x = if i == first { carry } else { c.q[i - 1] };
        super::cell(b, c.q[i], t[i], x, true);
        b.cx(c.q[i], x);
        b.ccx(r.mask, x, t[i]);
        b.cx(c.q[i], x);
    }
    b.ccx(r.activity, r.flight, r.mask);
    if prefix {
        explicit_prefix(b, c, t, carry, true, &d);
    }
    for &v in t {
        b.x(v);
    }
    if case.ht && !case.unparked {
        b.cx(r.activity, c.phase);
    }
    b.cswap(r.activity, t[128], r.flight); // complete Close::Inplace.
    b.play(&guard, true);
    b.end()
}

fn compact_unparked_ring_frame(b: &mut B, p: &Circuit) -> Vec<G> {
    b.begin();
    for (k, &e) in p.low.iter().enumerate() {
        b.x(e);
        frogdrop::crot_up(b, e, &p.q[..128], 1 << k);
        frogdrop::crot_up(b, e, &p.ring, 257 - (1 << k));
        b.x(e);
    }
    let hi = p.q[127];
    b.x(hi);
    for i in 0..63 {
        b.cswap(hi, p.q[i], p.q[i + 64]);
    }
    b.cx(hi, p.q[63]);
    frogdrop::crot_up(b, hi, &p.ring, 193);
    b.x(hi);
    b.end()
}

fn word_tapes(p: &Circuit, parent: bool, case: WordCase) -> (Vec<G>, Vec<G>, QubitId, QubitId) {
    // Match the previously validated explicit port allocation, including
    // the input E6 allocated last by the parent control only.
    let mut b = B::new();
    b.alloc_n(p.width);
    let mask = QubitId(p.e.0 + 1);
    let phase = QubitId(p.e.0 + 2);
    let size = SumSize {
        y: [
            p.low[0],
            p.low[1],
            p.low[2],
            p.low[3],
            p.low[4],
            p.low[5],
            p.high.unwrap_or(p.q[127]),
        ],
        sum: p.sum,
    };
    let c = Cross {
        size: &size,
        ring: &p.ring,
        q: &p.q[..128],
        phase,
        roles: Roles {
            activity: p.a,
            flight: p.e,
            mask,
            x128: p.q[128],
        },
        dirty: &[],
        y_bounds: (1, 128),
        qb: 30,
        clean_external: &[],
    };
    let t: Vec<_> = (0..129).map(|i| p.ring[case.pos(i)]).collect();
    let frame = if case.unparked && !case.top {
        if parent {
            super::super::normalized_cross_unparked_frame::record(&mut b, &c)
        } else {
            compact_unparked_ring_frame(&mut b, p)
        }
    } else {
        p.frame.clone()
    };
    let word = if parent {
        let d = super::D {
            ht: case.ht,
            payload_open: case.unparked,
        };
        d.record(
            &mut b,
            &c,
            &t,
            case.gate(),
            super::Op::Divide,
            super::Close::Inplace,
        )
    } else {
        compact_divide_inplace(&mut b, &c, &t, case)
    };
    assert_eq!(b.width() as usize, p.width);
    (frame, word, mask, phase)
}

#[test]
fn q659_cross_complete_divide_inplace() {
    let old = circuit(true);
    let new = circuit(false);
    assert_eq!(old.width, new.width + 1);
    let mut seed = 0x791d12284a62015fu64;
    let cases = [
        WordCase {
            top: false,
            bit: 7,
            ht: false,
            unparked: true,
        },
        WordCase {
            top: true,
            bit: 2,
            ht: false,
            unparked: true,
        },
        WordCase {
            top: true,
            bit: 14,
            ht: false,
            unparked: false,
        },
        WordCase {
            top: true,
            bit: 2,
            ht: false,
            unparked: false,
        },
        WordCase {
            top: true,
            bit: 2,
            ht: true,
            unparked: false,
        },
    ];
    for case in cases {
        let (of, ow, mask, phase) = word_tapes(&old, true, case);
        let (nf, nw, sm, sp) = word_tapes(&new, false, case);
        assert_eq!((mask, phase), (sm, sp));
        let mut accepted = 0;
        let mut skipped = 0;
        let mut disabled = 0;
        let mut quotients = [0usize; 2];
        let mut parked_states = 0;
        let mut prefix_positions = [0usize; 14];
        for batch in 0..64usize {
            let mut raw: Vec<u64> = (0..old.width).map(|_| random(&mut seed)).collect();
            let mut oracle = raw.clone();
            for lane in 0..64usize {
                let key = batch * 64 + lane;
                let y = key / 32 + 1;
                let s = key % 32;
                let delta = 128 - y;
                let active = (batch + lane) % 4 != 0;
                let pass = case.pass(y, s);
                let mut v = (u128::from(random(&mut seed)) << 64) | u128::from(random(&mut seed));
                if y < 128 {
                    v &= (1u128 << y) - 1;
                }
                v |= 1u128 << (y - 1);
                numbers(&old, &mut raw, lane, y, s);
                put(&mut raw, old.a, lane, active);
                put(&mut raw, old.e, lane, false);
                put(&mut raw, mask, lane, false);
                if active {
                    if !case.unparked {
                        put(&mut raw, phase, lane, case.ht);
                    }
                    let mut parked = false;
                    for i in 0..129usize {
                        let on = if i < y {
                            v >> i & 1 != 0
                        } else if !case.unparked && i < y + 15 {
                            random(&mut seed) & 1 != 0
                        } else {
                            false
                        };
                        parked |= i >= y && on;
                        put(&mut raw, old.q[i], lane, on);
                    }
                    parked_states += usize::from(parked && pass);
                    if !case.unparked && pass && delta < 14 {
                        prefix_positions[delta] += 1;
                    }
                } else if case.unparked && !case.top {
                    // In the native Q128-only frame x128 is a returned
                    // helper throughout the payload loop.
                    put(&mut raw, old.q[128], lane, false);
                }
                // Construct a genuine restoring digit in normalized logical
                // coordinates. Normalize a 128-bit positive divisor. D is
                // one of Dv-1, Dv, Dv+1 or 2Dv-1, covering both outcomes,
                // a possible 129th target bit, and the two decision edges.
                let divisor = v << delta;
                let (dividend, carry, rem, quot) = match (batch + lane) % 5 {
                    0 | 1 => (divisor - 1, false, divisor - 1, false),
                    2 => (divisor, false, 0, true),
                    3 => {
                        let (d, h) = divisor.overflowing_add(1);
                        (d, h, 1, true)
                    }
                    _ => {
                        let (d, h) = divisor.overflowing_add(divisor - 1);
                        (d, h, divisor - 1, true)
                    }
                };
                // ring'[pos] came from ring[pos+delta]. We compare the
                // declared arithmetic interface; the surrounding S/top/V
                // epochs are separate controller operations.
                for i in 0..129usize {
                    let q = old.ring[(case.pos(i) + delta) % 257];
                    put(
                        &mut raw,
                        q,
                        lane,
                        if i == 128 {
                            carry
                        } else {
                            dividend >> i & 1 != 0
                        },
                    );
                }
                for wire in 0..raw.len() {
                    let q = QubitId(wire as u64);
                    put(&mut oracle, q, lane, bit(&raw, q, lane));
                }
                if !active {
                    disabled += 1;
                } else if !pass {
                    skipped += 1;
                } else {
                    accepted += 1;
                    quotients[usize::from(quot)] += 1;
                    for i in 0..129usize {
                        let q = old.ring[(case.pos(i) + delta) % 257];
                        put(
                            &mut oracle,
                            q,
                            lane,
                            if i == 128 { quot } else { rem >> i & 1 != 0 },
                        );
                    }
                }
            }
            let mut a = raw.clone();
            let mut c = raw[..new.width].to_vec();
            apply(&of, &mut a, false);
            apply(&nf, &mut c, false);
            apply(&ow, &mut a, false);
            apply(&nw, &mut c, false);
            apply(&of, &mut a, true);
            apply(&nf, &mut c, true);
            assert_eq!(
                a, oracle,
                "parent full-register oracle {case:?} batch={batch}"
            );
            assert_eq!(
                c.as_slice(),
                &a[..new.width],
                "compact full-register oracle {case:?} batch={batch}"
            );
            // Re-run the source/candidate inverse only on their actual
            // output images, including completed in-place quotient deposits.
            apply(&of, &mut a, false);
            apply(&nf, &mut c, false);
            apply(&ow, &mut a, true);
            apply(&nw, &mut c, true);
            apply(&of, &mut a, true);
            apply(&nf, &mut c, true);
            assert_eq!(a, raw);
            assert_eq!(c.as_slice(), &raw[..new.width]);
        }
        assert!(
            accepted > 0 && skipped > 0 && disabled > 0 && quotients[0] > 0 && quotients[1] > 0
        );
        if !case.unparked {
            assert!(parked_states > 0);
        }
        if !case.unparked && case.bit == 2 {
            assert!(prefix_positions[2..].iter().all(|&n| n > 0));
        }
        println!("q659-cross-word {case:?} widths={}/{} frames={}/{} word_ccx={}/{} accepted={accepted} skipped={skipped} disabled={disabled} quotient0={} quotient1={} parked={parked_states} prefix={prefix_positions:?}",old.width,new.width,ccx(&of),ccx(&nf),ccx(&ow),ccx(&nw),quotients[0],quotients[1]);
    }
}
