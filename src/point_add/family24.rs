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
    if count-ix<5||r.data[r.at]!=5||s.family24_locations[node].binary_search(&ix).is_err(){return None;}
    let len=5;let mut rr=Reader{data:r.data,at:r.at};let mut v=[O::default();6];for i in 0..len{v[i]=read(&mut rr);}if rr.at>boundary{return None;}
    if !plain(v[0],5,3)||!plain(v[1],5,3)||!plain(v[2],1,1)||!plain(v[3],1,1){return None;}
    let b=v[2].q[0];let a=if v[0].q[0]==b{v[0].q[1]}else if v[0].q[1]==b{v[0].q[0]}else{return None;};let t=v[0].q[2];let c=if v[1].q[0]==b{v[1].q[1]}else if v[1].q[1]==b{v[1].q[0]}else{return None;};let d=v[1].q[2];if !x(v[3],d)||!pair(v[4],a,d,t){return None;}
    let wires=[a,b,t,c,d];let mut mapped=Vec::new();for q in wires{if q>=qlen{return None;}let p=s.qmap[qs+q];if p==QubitId(0)||mapped.contains(&p){return None;}mapped.push(p);}
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
    emit(5,&[1,3,4]);emit(1,&[4]);emit(3,&[1,4]);emit(5,&[0,4,2]);emit(3,&[1,4]);emit(1,&[1]);
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
    if new_t < old_t {assert_eq!(s.residual_counts,before_residual);assert_eq!(captured.len(),5);assert_eq!(s.one_cleanups,before_one);assert_eq!([s.proof.rewrites,s.proof.support_dead,s.proof.support_x,s.proof.support_cx],before);
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
        s.family24_counts[1] += 1;
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
    s.family24_counts[0] += 1;
    r.at = rr.at;
    Some(len)
}

pub(super) fn locations()->Vec<Vec<usize>>{let mut v=vec![Vec::new();2270];for l in include_str!("family24_locations.tsv").lines(){let r:Vec<usize>=l.split_whitespace().map(|s|s.parse().unwrap()).collect();v[r[1]].push(r[2]);}v}
#[cfg(test)]include!("family24_tests.rs");
#[cfg(test)]#[test]fn family24_tiny(){tests();}
#[cfg(test)]#[test]fn wire_residual_forces_no_gain_family_fallback_into_outer_capture(){
 use super::{Op,OperationType as K,BitId};use crate::sim::Simulator;use sha3::digest::XofReader;
 struct R(u8);impl XofReader for R{fn read(&mut self,b:&mut[u8]){b.fill(self.0);}}
 let data=include_bytes!("family24_fixture.hir");let mut r=Reader{data,at:0};let v:Vec<_>=(0..5).map(|_|read(&mut r)).collect();let b=v[2].q[0];let a=if v[0].q[0]==b{v[0].q[1]}else{v[0].q[0]};let t=v[0].q[2];let c=if v[1].q[0]==b{v[1].q[1]}else{v[1].q[0]};let d=v[1].q[2];let locals=[a,b,t,c,d];
 let build=|enabled,retain|{let mut s=State::new(8,1,&[1,2,4,5,6],&[],retain,0);s.family24_locations=vec![vec![0]];s.qmap=vec![QubitId(0);580];for(j,&q)in locals.iter().enumerate(){s.qmap[q]=QubitId(j as u64+1);}
 let o=s.raw(K::CX);o.q_control1=QubitId(6);o.q_target=QubitId(3);
 for o in v.iter().rev(){let mut q=[NO_QUBIT;3];for j in 0..o.nq{q[j]=s.qmap[o.q[j]];}s.emit_leaf(o.t,&q,o.nq,NO_BIT,0);}
 s.raw(K::X).q_target=QubitId(6);s.raw(K::X).q_target=QubitId(6);s.flush_raw();let before=s.residual_counts;
 s.comparator_capture=Some(Vec::new());if enabled{let mut rr=Reader{data,at:0};assert_eq!(try_apply(&mut s,&mut rr,0,0,5,0,580,usize::MAX),Some(5));}else{for o in &v{let mut q=[NO_QUBIT;3];for j in 0..o.nq{q[j]=s.qmap[o.q[j]];}s.emit_leaf(o.t,&q,o.nq,NO_BIT,0);}s.flush_raw();}
 assert_eq!(s.residual_counts[0]-before[0],1);assert_eq!(s.family24_counts[1],0);let captured=s.comparator_capture.take().unwrap();assert!(captured.iter().any(|o|o.kind==K::Hmr&&o.c_target==s.measurement_bit));for op in captured{s.deliver(op);}
 for _ in 0..2{let o=s.raw(K::CCX);o.q_control1=QubitId(1);o.q_control2=QubitId(2);o.q_target=QubitId(7);}s.flush_raw();s.assert_accounting(s.input_ops,0);s};
 let old=build(false,true);let new=build(true,true);let count=build(true,false);assert_eq!(new.output_hist,old.output_hist);assert_eq!(new.output_hist,count.output_hist);assert_eq!(new.final_private_hmr,count.final_private_hmr);assert_eq!(new.trace,old.trace);assert_eq!(new.proof.diagnostic_fingerprint(),old.proof.diagnostic_fingerprint());
 for mask in 0..32u64{for m in [0,255]{for stale in 0..2u64{let mut ra=R(m);let mut rb=R(m);let mut a=Simulator::new(8,3,&mut ra);let mut b=Simulator::new(8,3,&mut rb);for(j,q)in [1,2,4,5,6].into_iter().enumerate(){a.qubits[q]=(mask>>j)&1;}a.bits[1]=stale;b.qubits=a.qubits.clone();b.bits=a.bits.clone();a.apply_iter(old.out.iter());b.apply_iter(new.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.bits,b.bits);}}}
}
