//! Exact controlled-UMA factoring. The sum update and carry update share
//! ctrl*addend, so materialize that product once in a proven-zero pool wire.
//! All sixteen data assignments and both directions have the same permutation;
//! measurement cleanup corrects the phase of the new product explicitly.
use super::{Graph, OperationType as K, PendingHmr, Reader, State};

#[derive(Clone, Copy, Default)]
struct Leaf { tag: u8, cw: usize, expected: usize, condition: usize,
    child: usize, nq: usize, q: [usize; 3], nc: usize, c: usize }
fn read(r: &mut Reader<'_>) -> Option<Leaf> {
    let mut o = Leaf { tag: r.byte(), ..Leaf::default() };
    o.cw = r.uvar(); o.expected = r.uvar();
    if o.cw > 1 { return None; }
    if o.cw == 1 { o.condition = r.uvar(); }
    if o.tag == 11 { o.child = r.uvar(); }
    o.nq = r.uvar(); if o.nq > 3 { return None; }
    for i in 0..o.nq { o.q[i] = r.uvar(); }
    o.nc = r.uvar(); if o.nc > 1 { return None; }
    if o.nc == 1 { o.c = r.uvar(); }
    Some(o)
}
fn pair(q: [usize;3], a: usize, b: usize) -> bool {
    (q[0] == a && q[1] == b) || (q[0] == b && q[1] == a)
}
fn decode(r: &mut Reader<'_>) -> Option<([usize;5], usize, bool)> {
    let mut v = [Leaf::default();7];
    v[0] = read(r)?; v[1] = read(r)?;
    if v[0].tag != 5 || v[1].tag != 5 { return None; }
    v[2] = read(r)?;
    let inverse = match v[2].tag { 5 => true, 8 => false, _ => return None };
    let tags = if inverse { [5,5,5,8,9,10,11] } else { [5,5,8,9,10,11,5] };
    for i in 3..7 { v[i] = read(r)?; if v[i].tag != tags[i] { return None; } }
    let (g,h,hm,me,re,cz,sum) = if inverse {
        (v[1],v[2],v[3],v[4],v[5],v[6],v[0])
    } else { (v[0],v[1],v[2],v[3],v[4],v[5],v[6]) };
    for o in [g,h,hm,me,re,sum] { if o.cw != 0 || o.expected != 1 { return None; } }
    for o in [g,h,sum] { if o.nq != 3 || o.nc != 0 { return None; } }
    let pool = g.q[2]; let a = sum.q[2];
    let ctrl = if g.q[0] == a { g.q[1] } else if g.q[1] == a { g.q[0] } else { return None; };
    let b = if sum.q[0] == ctrl { sum.q[1] } else if sum.q[1] == ctrl { sum.q[0] } else { return None; };
    let carry = h.q[2];
    if !pair(h.q,b,pool) || hm.nq != 1 || me.nq != 1 || re.nq != 1
        || hm.q[0] != pool || me.q[0] != pool || re.q[0] != pool
        || hm.nc != 0 || me.nc != 1 || re.nc != 0 { return None; }
    // Child zero is checked independently to be precisely an unconditional CZ.
    if cz.child != 0 || cz.nq != 2 || cz.nc != 1 || cz.cw != 1 || cz.expected != 1
        || cz.condition != me.c || cz.c != me.c || !pair(cz.q,ctrl,a) { return None; }
    let wires = [ctrl,a,b,carry,pool];
    for i in 0..5 { for j in i+1..5 { if wires[i] == wires[j] { return None; } } }
    Some((wires,me.c,inverse))
}
pub(super) fn validate_phase_child(graph: &Graph<'_>) {
    let node = graph.nodes[0];
    let mut r = Reader { data: &graph.data[node.start..node.end], at: 0 };
    assert_eq!((r.uvar(),r.uvar(),r.uvar()),(2,1,1));
    let o = read(&mut r).expect("phase child shape");
    assert_eq!((o.tag,o.cw,o.expected,o.nq,o.q,o.nc),(4,0,1,2,[0,1,0],0));
    assert_eq!(r.at,r.data.len());
}
pub(super) fn try_apply(state: &mut State, reader: &mut Reader<'_>, qs: usize, cs: usize) -> bool {
    let mut peek = Reader { data: reader.data, at: reader.at };
    let Some((wires,bit,inverse)) = decode(&mut peek) else { return false; };
    // This pass is called only on 578-qubit/one-bit EEA nodes. Preserve the
    // ordinary decoder's local-wire bounds even when bypassing its leaf loop.
    if bit != 0 || wires.iter().any(|&q| q >= 578) { return false; }
    assert!(matches!(state.pending_hmr, PendingHmr::None));
    state.flush_raw();
    state.shared_hits += 1;
    let [ctrl,a,b,carry,pool] = wires.map(|q| state.qmap[qs+q]);
    if !state.proof.qubit_is_zero(pool.0 as usize) {
        state.shared_unknown_pool += 1;
        return false;
    }
    let bit = state.cmap[cs+bit];
    let op = state.raw(K::CCX); op.q_control2=ctrl; op.q_control1=b; op.q_target=pool;
    if inverse { let op=state.raw(K::CX); op.q_control1=pool; op.q_target=a; }
    let op = state.raw(K::CCX); op.q_control2=a; op.q_control1=pool; op.q_target=carry;
    if !inverse { let op=state.raw(K::CX); op.q_control1=pool; op.q_target=a; }
    let op=state.raw(K::Hmr); op.q_target=pool; op.c_target=bit;
    state.raw(K::PushCondition).c_condition=bit;
    let op=state.raw(K::CZ); op.q_control1=ctrl; op.q_target=b;
    state.raw(K::PopCondition);
    reader.at=peek.at;
    state.shared_rewrites+=1;
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{BitId,Op,QubitId};
    use crate::sim::Simulator;
    use sha3::digest::XofReader;
    struct Outcome(u8);
    impl XofReader for Outcome { fn read(&mut self,b:&mut [u8]) { b.fill(self.0); } }
    fn ccx(a:usize,b:usize,t:usize)->Op {
        let mut o=Op::empty();o.kind=K::CCX;o.q_control2=QubitId(a as u64);
        o.q_control1=QubitId(b as u64);o.q_target=QubitId(t as u64);o
    }
    #[test]
    fn actual_source_cells_all_inputs_phase_conditions_and_dirty_pool() {
        for fixture in [include_bytes!("shared_product_forward.hir").as_slice(),include_bytes!("shared_product_inverse.hir").as_slice()] {
            let mut p=Reader{data:fixture,at:0};let (w,_,inverse)=decode(&mut p).unwrap();
            assert_eq!(p.at,fixture.len());let [ctrl,a,b,c,pool]=w;
            let mut base=vec![ccx(ctrl,a,pool),ccx(b,pool,c),ccx(ctrl,a,pool),ccx(ctrl,b,a)];
            if inverse { base.reverse(); }
            for enclosed in [false,true] {
                let mut state=State::new(578,2,&w[..4],&[1],true,0);
                if enclosed {state.raw(K::PushCondition).c_condition=BitId(1);}
                let mut r=Reader{data:fixture,at:0};assert!(try_apply(&mut state,&mut r,0,0));
                if enclosed {state.raw(K::PopCondition);}
                state.flush_raw();assert_eq!(r.at,fixture.len());assert!(state.proof.balanced());
                for o in &state.out {o.validate();}
                for mask in 0..16 {for active in [0,1] {for m in [0,255] {
                    let mut rng=Outcome(m);let mut sim=Simulator::new(578,4,&mut rng);
                    for i in 0..4 {sim.qubits[w[i]]=(mask>>i)&1;}
                    sim.bits[1]=active;
                    let initial=sim.qubits.clone();sim.apply_iter(state.out.iter());
                    let (got,phase)=(sim.qubits.clone(),sim.phase&1);
                    let mut rng2=Outcome(0);let mut expected=Simulator::new(578,4,&mut rng2);expected.qubits=initial;
                    if !enclosed||active==1 {expected.apply_iter(base.iter());}
                    for (x,y) in got.iter().zip(expected.qubits) {assert_eq!(x&1,y&1);}
                    assert_eq!(phase,0,"inverse={inverse} mask={mask} active={active} m={m}");
                }}}
            }
            let mut dirty=State::new(578,2,&w,&[],true,0);let mut r=Reader{data:fixture,at:0};
            assert!(!try_apply(&mut dirty,&mut r,0,0));assert_eq!(r.at,0);
            assert_eq!(dirty.shared_unknown_pool,1);assert_eq!(dirty.shared_rewrites,0);
            // Wrong phase-product controls must not match the source signature.
            let mut corrupt=fixture.to_vec();corrupt[4]^=1;
            let mut state=State::new(578,2,&w[..4],&[],true,0);
            let mut r=Reader{data:&corrupt,at:0};assert!(!try_apply(&mut state,&mut r,0,0));
        }
    }
    #[test]
    #[ignore="one authorized low-memory source census; never emits a full artifact"]
    fn shared_product_full_source_census() {
        let start=std::time::Instant::now();
        let decoded=zstd::stream::decode_all(super::super::COMPRESSED_HIR).unwrap();
        let graph=super::super::parse_graph(&decoded);validate_phase_child(&graph);
        let qi:Vec<_>=(1..=512).collect();let ci:Vec<_>=(0..512).collect();
        let mut state=State::new(graph.root_qubits,graph.root_bits,&qi,&ci,false,0);
        super::super::expand_node(&graph,&mut state,graph.root,0,graph.root_qubits,0,graph.root_bits);
        state.flush_raw();assert!(state.out.is_empty());assert!(state.proof.balanced());
        assert_eq!(state.predicate_blocks,1284);
        state.assert_accounting(graph.summaries[graph.root].output_ops,0);
        let static_t=state.output_hist[K::CCX as usize]+state.output_hist[K::CCZ as usize]-state.outer_lowered;
        let expected_t=static_t-512*1284/2;
        let report=format!("{{\"status\":\"source census only; unchanged9024 replay pending\",\"hits\":{},\"shared_rewrites\":{},\"unknown_pool\":{},\"clean_and_rewrites\":{},\"predicate_blocks\":{},\"support_dead\":{},\"support_x\":{},\"support_cx\":{},\"prefix_rewrites\":{},\"input_ops\":{},\"output_ops\":{},\"static_toffoli\":{static_t},\"expected_toffoli\":{expected_t},\"ops\":{},\"qubits\":834,\"seconds\":{}}}",state.shared_hits,state.shared_rewrites,state.shared_unknown_pool,state.proof.rewrites,state.predicate_blocks,state.proof.support_dead,state.proof.support_x,state.proof.support_cx,state.prefix_rewrites,state.input_ops,state.output_ops,state.output_ops+4*257-2,start.elapsed().as_secs_f64());
        eprintln!("PREFIX_RETENTION hits={} rewrites={} unknown={}",state.prefix_hits,state.prefix_rewrites,state.prefix_unknown);
        eprintln!("SUPPORT_LOWERING dead={} x={} cx={} input_ops={} output_ops={}",state.proof.support_dead,state.proof.support_x,state.proof.support_cx,state.input_ops,state.output_ops);
        eprintln!("{report}");std::fs::write(std::env::var("SHARED_PRODUCT_REPORT").unwrap(),report).unwrap();
    }
}
