use super::{Graph, QubitId, Reader, State, NO_BIT, NO_QUBIT};
#[derive(Clone, Copy, Default)]
struct O {
    t: u8,
    cw: usize,
    e: usize,
    nq: usize,
    q: [usize; 3],
    nc: usize,
}
fn read(r: &mut Reader<'_>) -> O {
    let mut o = O::default();
    o.t = r.byte();
    o.cw = r.uvar();
    o.e = r.uvar();
    for _ in 0..o.cw {
        r.uvar();
    }
    if o.t == 11 {
        r.uvar();
    }
    o.nq = r.uvar();
    for i in 0..o.nq {
        let q = r.uvar();
        if i < 3 {
            o.q[i] = q;
        }
    }
    o.nc = r.uvar();
    for _ in 0..o.nc {
        r.uvar();
    }
    o
}
fn plain(o: O, t: u8, nq: usize) -> bool {
    o.t == t && o.cw == 0 && o.e == 1 && o.nq == nq && o.nc == 0
}
fn pair(o: O, a: usize, b: usize, t: usize) -> bool {
    plain(o, 5, 3) && o.q[2] == t && ((o.q[0] == a && o.q[1] == b) || (o.q[0] == b && o.q[1] == a))
}
fn cx(o: O, a: usize, b: usize) -> bool {
    plain(o, 3, 2) && o.q[..2] == [a, b]
}
fn x(o: O, a: usize) -> bool {
    plain(o, 1, 1) && o.q[0] == a
}
pub(super) fn exclusions(g: &Graph<'_>) -> Vec<Vec<(usize, usize)>> {
    let mut out = Vec::new();
    for (id, node) in g.nodes.iter().enumerate() {
        let mut r = Reader {
            data: &g.data[node.start..node.end],
            at: 0,
        };
        r.uvar();
        r.uvar();
        let count = r.uvar();
        let mut ranges: Vec<(usize, usize)> = Vec::new();
        for ix in 0..count {
            let at = r.at;
            let o = read(&mut r);
            let mut end = ix;
            if (id == 2261 && (155419..155438).contains(&ix))
                || (id == 2263 && (10661..10680).contains(&ix))
            {
                end = ix + 1;
            }
            if o.t == 5 {
                if [
                    include_bytes!("prefix_retention_bank531.hir").as_slice(),
                    include_bytes!("prefix_retention_bank540.hir").as_slice(),
                ]
                .iter()
                .any(|b| r.data[at..].starts_with(b))
                {
                    end = ix + 65;
                } else if count - ix >= 7 {
                    let mut p = Reader { data: r.data, at };
                    let mut tags = [0; 7];
                    for t in &mut tags {
                        *t = read(&mut p).t;
                    }
                    if tags == [5, 5, 8, 9, 10, 11, 5] || tags == [5, 5, 5, 8, 9, 10, 11] {
                        end = ix + 7;
                    }
                }
            }
            if end > ix {
                if let Some(last) = ranges.last_mut() {
                    if ix <= last.1 {
                        last.1 = last.1.max(end);
                        continue;
                    }
                }
                ranges.push((ix, end));
            }
        }
        assert_eq!(r.at, r.data.len());
        out.push(ranges);
    }
    out
}
pub(super) fn try_apply(
    s: &mut State,
    r: &mut Reader<'_>,
    node: usize,
    ix: usize,
    count: usize,
    qs: usize,
    qlen: usize,
    boundary: usize,
) -> Option<usize> {
    if count-ix<10||r.data[r.at]!=5||s.family63_locations[node].binary_search(&ix).is_err(){return None;}
    let len=10;let mut rr=Reader{data:r.data,at:r.at};let mut v=[O::default();10];for o in &mut v{*o=read(&mut rr);}if rr.at>boundary{return None;}
    if !plain(v[0],5,3)||!plain(v[1],3,2)||!plain(v[2],3,2)||!plain(v[4],3,2)||!plain(v[5],3,2)||!plain(v[7],3,2)||!plain(v[8],3,2){return None;}
    let [a,b,c]=v[0].q;let d=v[1].q[1];let e=v[2].q[0];let f=v[4].q[1];let g=v[5].q[0];let h=v[7].q[1];let i=v[8].q[0];
    if !cx(v[1],c,d)||!cx(v[2],e,c)||!pair(v[3],c,d,e)||!cx(v[4],e,f)||!cx(v[5],g,e)||!pair(v[6],e,f,g)||!cx(v[7],g,h)||!cx(v[8],i,h)||!pair(v[9],e,f,g){return None;}
    let wires=[a,b,c,d,e,f,g,h,i];let mut mapped=Vec::new();for q in wires{if q>=qlen{return None;}let p=s.qmap[qs+q];if p==QubitId(0)||mapped.contains(&p){return None;}mapped.push(p);}
    let mut replacement = Vec::new();
    let mut emit = |tag: u8, args: &[usize]| {
        let mut op = super::Op::empty();
        match tag {
            1 => {
                op.kind = super::OperationType::X;
                op.q_target = mapped[args[0]];
            }
            3 => {
                op.kind = super::OperationType::CX;
                op.q_control1 = mapped[args[0]];
                op.q_target = mapped[args[1]];
            }
            5 => {
                op.kind = super::OperationType::CCX;
                op.q_control2 = mapped[args[0]];
                op.q_control1 = mapped[args[1]];
                op.q_target = mapped[args[2]];
            }
            _ => unreachable!(),
        }
        op.validate();
        replacement.push(op);
    };
    emit(5,&[0,1,2]);emit(3,&[2,3]);emit(3,&[4,2]);emit(5,&[2,3,4]);emit(3,&[4,5]);emit(3,&[6,4]);emit(3,&[6,7]);emit(3,&[8,7]);emit(5,&[4,5,7]);
    s.flush_raw();
    assert!(s.capture.is_none());
    s.capture = Some(Vec::new());
    let before_residual=s.residual_counts;
    let before_one=s.one_cleanups;
    let before = [
        s.proof.rewrites,
        s.proof.support_dead,
        s.proof.support_x,
        s.proof.support_cx,
    ];
    for o in v.iter().take(len) {
        let mut q = [NO_QUBIT; 3];
        for j in 0..o.nq {
            q[j] = s.qmap[qs + o.q[j]];
        }
        s.emit_leaf(o.t, &q, o.nq, NO_BIT, 0);
    }
    s.flush_raw();
    let captured = s.capture.take().unwrap();
    let count_t = |v: &[super::Op]| {
        v.iter()
            .filter(|o| {
                matches!(
                    o.kind,
                    super::OperationType::CCX | super::OperationType::CCZ
                )
            })
            .count()
    };
    let old_t = count_t(&captured);
    let new_t = count_t(&replacement);
    if new_t < old_t {assert_eq!(s.residual_counts,before_residual);assert_eq!(captured.len(),10);assert_eq!(s.one_cleanups,before_one);assert_eq!([s.proof.rewrites,s.proof.support_dead,s.proof.support_x,s.proof.support_cx],before);
        // Only generated private scratch may occur; every use is preceded by an unconditional write.
        let mut private_written = false;
        for op in &captured {
            assert!(op.c_target == NO_BIT || op.c_target == s.measurement_bit);
            assert!(op.c_condition == NO_BIT || op.c_condition == s.measurement_bit);
            if op.c_condition == s.measurement_bit {
                assert!(private_written);
            }
            if op.c_target == s.measurement_bit {
                assert_eq!(op.kind, super::OperationType::Hmr);
                assert_eq!(op.c_condition, NO_BIT);
                private_written = true;
            }
        }
        s.skipped_one+=s.one_cleanups-before_one;
        s.family63_counts[1] += 1;
        assert_eq!(old_t-new_t,1);
        s.skipped_cleanups += s.proof.rewrites - before[0];
        s.skipped_support[0] += s.proof.support_dead - before[1];
        s.skipped_support[1] += s.proof.support_x - before[2];
        s.skipped_support[2] += s.proof.support_cx - before[3];
        s.selected_delta += replacement.len() as isize - captured.len() as isize;
        s.output_ops -= captured.len();
        for op in &captured {
            s.output_hist[op.kind as usize] -= 1;
        }
        for op in replacement {
            s.write(op);
        }
    } else {
        for op in captured{s.deliver(op);}
    }
    s.family63_counts[0] += 1;
    r.at = rr.at;
    Some(len)
}

pub(super) fn locations()->Vec<Vec<usize>>{let mut v=vec![Vec::new();2270];for l in include_str!("family63_locations.tsv").lines(){let r:Vec<usize>=l.split_whitespace().map(|s|s.parse().unwrap()).collect();v[r[1]].push(r[2]);}v}
#[cfg(test)]include!("family63_tests.rs");
