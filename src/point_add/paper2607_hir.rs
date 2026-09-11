use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId, NO_BIT, NO_QUBIT};

const MAGIC: &[u8; 8] = b"P26HIR1\0";
const COMPRESSED_HIR: &[u8] = include_bytes!("paper2607_runtime.hir.zst");

#[path = "predicate_offsets.rs"]
mod predicate_offsets;
#[path = "shared_product.rs"]
mod shared_product;
#[path = "prefix_retention.rs"]
mod prefix_retention;
#[path = "motif.rs"]
mod motif;
#[path="comparator.rs"] mod comparator;
#[path="peephole.rs"] mod peephole;
#[path="stable_lengths.rs"] mod stable_lengths;
#[path="shift_controls.rs"] mod shift_controls;
#[path="metadata_lt8.rs"] mod metadata_lt8;
#[path="commuting_cancel.rs"] mod commuting_cancel;
#[cfg(test)]
#[path="shift_control_tests.rs"] mod shift_control_tests;
#[cfg(test)]
#[path="integrated_833_tests.rs"] mod integrated_833_tests;

#[cfg(test)]
#[path = "cache_extension_tests.rs"]
mod cache_extension_tests;

struct Reader<'a> {
    data: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn byte(&mut self) -> u8 {
        let value = *self.data.get(self.at).expect("truncated paper-2607 HIR");
        self.at += 1;
        value
    }

    fn uvar(&mut self) -> usize {
        let mut value = 0usize;
        let mut shift = 0usize;
        loop {
            let byte = self.byte();
            value |= usize::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return value;
            }
            shift += 7;
            assert!(
                shift < usize::BITS as usize,
                "oversized paper-2607 HIR varint"
            );
        }
    }
}

#[derive(Clone, Copy, Default)]
struct Summary {
    output_ops: usize,
    h: usize,
    measure: usize,
    reset: usize,
    toffoli: usize,
}

impl Summary {
    fn add(&mut self, other: Self) {
        self.output_ops = self.output_ops.checked_add(other.output_ops).unwrap();
        self.h = self.h.checked_add(other.h).unwrap();
        self.measure = self.measure.checked_add(other.measure).unwrap();
        self.reset = self.reset.checked_add(other.reset).unwrap();
        self.toffoli = self.toffoli.checked_add(other.toffoli).unwrap();
    }
}

#[derive(Clone, Copy)]
struct Node {
    start: usize,
    end: usize,
}

struct Graph<'a> {
    data: &'a [u8],
    nodes: Vec<Node>,
    root: usize,
    root_qubits: usize,
    root_bits: usize,
    summaries: Vec<Summary>,
}

fn skip_vector(reader: &mut Reader<'_>) {
    let width = reader.uvar();
    for _ in 0..width {
        reader.uvar();
    }
}

fn condition_overhead(reader: &mut Reader<'_>) -> usize {
    let width = reader.uvar();
    let expected = reader.uvar();
    if width == 0 {
        assert_eq!(expected, 1, "invalid unconditional HIR sentinel");
    } else {
        assert!(
            width < usize::BITS as usize && expected < (1usize << width),
            "invalid paper-2607 HIR condition"
        );
    }
    let zeros = if width == 0 {
        0
    } else {
        width - expected.count_ones() as usize
    };
    for _ in 0..width {
        reader.uvar();
    }
    2 * width + 2 * zeros
}

fn parse_graph(data: &[u8]) -> Graph<'_> {
    assert!(data.len() >= MAGIC.len() && &data[..MAGIC.len()] == MAGIC);
    let mut reader = Reader {
        data,
        at: MAGIC.len(),
    };
    assert_eq!(reader.uvar(), 1, "unsupported paper-2607 HIR version");
    let root = reader.uvar();
    let node_count = reader.uvar();
    assert!(root < node_count);
    let mut nodes = Vec::with_capacity(node_count);
    for _ in 0..node_count {
        let len = reader.uvar();
        let end = reader
            .at
            .checked_add(len)
            .expect("HIR node length overflow");
        assert!(end <= data.len(), "truncated paper-2607 HIR node");
        nodes.push(Node {
            start: reader.at,
            end,
        });
        reader.at = end;
    }
    assert_eq!(reader.at, data.len(), "trailing paper-2607 HIR bytes");

    let mut summaries = Vec::with_capacity(node_count);
    let mut widths = Vec::with_capacity(node_count);
    for (node_id, node) in nodes.iter().copied().enumerate() {
        let mut body = Reader {
            data: &data[node.start..node.end],
            at: 0,
        };
        let num_qubits = body.uvar();
        let num_bits = body.uvar();
        widths.push((num_qubits, num_bits));
        let mut summary = Summary::default();
        let op_count = body.uvar();
        for _ in 0..op_count {
            let tag = body.byte();
            summary.output_ops += condition_overhead(&mut body);
            if tag == 11 {
                let child = body.uvar();
                assert!(child < node_id, "paper-2607 HIR is not child-before-parent");
                summary.add(summaries[child]);
            } else {
                match tag {
                    1..=7 => {
                        summary.output_ops += 1;
                        if matches!(tag, 5 | 6) {
                            summary.toffoli += 1;
                        }
                    }
                    8 => {
                        summary.output_ops += 1;
                        summary.h += 1;
                    }
                    9 => summary.measure += 1,
                    10 => summary.reset += 1,
                    _ => panic!("unknown paper-2607 HIR tag {tag}"),
                }
            }
            skip_vector(&mut body);
            skip_vector(&mut body);
        }
        assert_eq!(
            body.at,
            body.data.len(),
            "trailing bytes in HIR node {node_id}"
        );
        summaries.push(summary);
    }
    let (root_qubits, root_bits) = widths[root];
    let root_summary = summaries[root];
    assert_eq!(root_summary.h, root_summary.measure, "unpaired H/measure");
    assert_eq!(root_summary.h, root_summary.reset, "unpaired H/reset");
    Graph {
        data,
        nodes,
        root,
        root_qubits,
        root_bits,
        summaries,
    }
}

#[derive(Clone, Copy)]
enum PendingHmr {
    None,
    H(QubitId),
    Measure(QubitId, BitId),
}

#[path="family24.rs"]mod family24;
#[path="family36.rs"]mod family36;
#[path="family63.rs"]mod family63;
struct State {
 lengths: stable_lengths::Tracker,
 family63_enabled:bool,family63_locations:Vec<Vec<usize>>,family63_counts:[usize;2],
 family36_enabled:bool,family36_locations:Vec<Vec<usize>>,family36_counts:[usize;2],
 family24_enabled:bool,family24_locations:Vec<Vec<usize>>,family24_counts:[usize;2],
 retention: Retention,
    out: Vec<Op>,
    pending_raw: Option<Op>,
    retain_output: bool,
    proof: super::clean_and::Proof,
    measurement_bit: BitId,
    predicate_bit: BitId,
    predicate_blocks: usize,
    prefix_hits: usize,
    prefix_rewrites: usize,
    prefix_unknown: usize,
    shared_hits: usize,
    shared_rewrites: usize,
    shared_unknown_pool: usize,
    motif_counts: [usize;3],
    capture: Option<Vec<Op>>,
    comparator: comparator::Tracker, comparator_capture:Option<Vec<Op>>, final_private_hmr:usize,final_private_neg:usize,
    residual_enabled:bool,residual_counts:[usize;2],skipped_residual:[usize;2],
    endpoint_blocks:usize,endpoint_outer:usize,endpoint_enabled:bool,
    carry_enabled:bool,carry_entries:usize,carry_zero:usize,carry_selected:usize,carry_delta:isize,
    one_enabled: bool,
    one_allowed: bool,
    one_cleanups: usize,
    skipped_one: usize,
    #[cfg(test)]
    trace: [u64;2],
    selected_counts: [usize;3],
    selected_delta: isize,
    selected_t_saving: usize,
    skipped_cleanups: u64,
    skipped_support: [u64;3],
    motif_enabled: bool,
    motif_family: usize,
    motif_exclusions: Vec<Vec<(usize,usize)>>,
    input_ops: usize,
    output_ops: usize,
    input_hist: [usize; 18],
    output_hist: [usize; 18],
    outer_toggles: usize,
    outer_lowered: usize,
    examples: Vec<(usize, Op)>,
    qmap: Vec<QubitId>,
    cmap: Vec<BitId>,
    pending_hmr: PendingHmr,
}

impl State {
    fn new(
        nq: usize,
        nb: usize,
        qinputs: &[usize],
        cinputs: &[usize],
        retain_output: bool,
        capacity: usize,
    ) -> Self {
        Self {
            lengths: stable_lengths::Tracker::default(),
            family63_enabled:true,family63_locations:family63::locations(),family63_counts:[0;2],
            family36_enabled:true,family36_locations:family36::locations(),family36_counts:[0;2],
            family24_enabled:true,family24_locations:family24::locations(),family24_counts:[0;2],
            retention: Retention::new(),
            out: Vec::with_capacity(if retain_output { capacity } else { 0 }),
            pending_raw: None,
            retain_output,
            proof: super::clean_and::Proof::new(nq, nb + 2, qinputs, cinputs),
            measurement_bit: BitId(nb as u64),
            predicate_bit: BitId(nb as u64 + 1),
            predicate_blocks: 0,
            prefix_hits: 0,
            prefix_rewrites: 0,
            prefix_unknown: 0,
            shared_hits: 0,
            shared_rewrites: 0,
            shared_unknown_pool: 0,
            motif_counts: [0;3],
            capture: None, comparator:comparator::Tracker::new(),comparator_capture:None,final_private_hmr:0,final_private_neg:0,
            residual_enabled:true,residual_counts:[0;2],skipped_residual:[0;2],
            endpoint_blocks:0,endpoint_outer:0,endpoint_enabled:false,carry_enabled:false,carry_entries:0,carry_zero:0,carry_selected:0,carry_delta:0,
            one_enabled: true, one_allowed: true, one_cleanups: 0, skipped_one: 0,
            #[cfg(test)]
            trace: [0xcbf29ce484222325,0x9e3779b97f4a7c15],
            selected_counts: [0;3],
            selected_delta: 0,
            selected_t_saving: 0,
            skipped_cleanups: 0,
            skipped_support: [0;3],
            motif_enabled: false,
            motif_family: 3,
            motif_exclusions: Vec::new(),
            input_ops: 0,
            output_ops: 0,
            input_hist: [0; 18],
            output_hist: [0; 18],
            outer_toggles: 0,
            outer_lowered: 0,
            examples: Vec::new(),
            qmap: (0..nq).map(|q| QubitId(q as u64)).collect(),
            cmap: (0..nb).map(|c| BitId(c as u64)).collect(),
            pending_hmr: PendingHmr::None,
        }
    }
    fn write(&mut self, op: Op) {
        self.output_ops += 1;
        self.output_hist[op.kind as usize] += 1;
        if let Some(buffer)=self.capture.as_mut(){buffer.push(op);return;}
        self.deliver(op);
    }
    fn deliver(&mut self,op:Op){if let Some(v)=self.comparator_capture.as_mut(){v.push(op);}else{if op.kind==OperationType::Hmr&&op.c_target==self.measurement_bit{self.final_private_hmr+=1;}if op.kind==OperationType::Neg&&op.c_condition==self.measurement_bit{self.final_private_neg+=1;}if self.retain_output{self.out.push(op);}}}
    fn flush_raw(&mut self) {
        let Some(op) = self.pending_raw.take() else {
            return;
        };
        #[cfg(test)]
        for x in [op.kind as u64,op.q_control2.0,op.q_control1.0,op.q_target.0,op.c_target.0,op.c_condition.0,op.r_target.0] {
            self.trace[0]=(self.trace[0]^x).wrapping_mul(0x100000001b3);
            self.trace[1]=self.trace[1].rotate_left(17).wrapping_add(x).wrapping_mul(0x9e3779b185ebca87);
        }
        self.input_ops += 1;
        self.input_hist[op.kind as usize] += 1;
        if op.q_target == QubitId(0) {
            assert_eq!(op.kind, OperationType::X, "unexpected outer-control target");
            self.outer_toggles += 1;
        }
        if matches!(op.kind, OperationType::CCX | OperationType::CCZ)
            && (op.q_control1 == QubitId(0) || op.q_control2 == QubitId(0))
        {
            self.outer_lowered += 1;
        }
        self.proof.affine_allowed=self.one_allowed;
        if self.proof.step(&op) {
            if self.examples.len() < 32 {
                self.examples.push((self.input_ops - 1, op));
            }
            for new in super::clean_and::replacement(&op, self.measurement_bit) {
                self.write(new);
            }
        } else if self.one_enabled && self.one_allowed && self.proof.ccx_result_is_one(&op) {
            self.one_cleanups += 1;
            for new in super::clean_and::replacement_to_one(&op,self.measurement_bit) {new.validate();self.write(new);}
        } else if self.residual_enabled && self.proof.residual_action.is_some(){
            let (wire,parity)=self.proof.residual_action.unwrap();self.residual_counts[parity as usize]+=1;
            for new in super::clean_and::replacement_to_wire(&op,self.measurement_bit,QubitId(wire as u64),parity){self.write(new);}
        } else if let Some(lowered) = self.proof.support_lowering.apply(op) {
            self.write(lowered);
        }
    }
    fn assert_accounting(&self, source_ops: usize, declarations: usize) {
        assert_eq!(self.input_ops, source_ops + 3 * self.predicate_blocks - 35 * self.prefix_rewrites - 34 * self.lengths.rewrites);
        let expected = (self.input_ops as isize + self.proof.rewrites as isize - self.proof.support_dead as isize + 3*self.one_cleanups as isize + self.selected_delta+self.comparator.delta+3*self.residual_counts[0] as isize+5*self.residual_counts[1] as isize) as usize;
        assert_eq!(self.output_ops, expected);
        if self.retain_output {
            assert_eq!(self.out.len(), expected + declarations);
        } else {
            assert!(self.out.is_empty());
        }
    }
    fn raw(&mut self, kind: OperationType) -> &mut Op {
        self.flush_raw();
        let mut op = Op::empty();
        op.kind = kind;
        self.pending_raw = Some(op);
        self.pending_raw.as_mut().unwrap()
    }

    fn emit_condition(&mut self, start: usize, width: usize, expected: usize) {
        if width == 0 {
            assert_eq!(expected, 1);
            return;
        }
        for i in 0..width {
            let bit = self.cmap[start + i];
            if (expected >> i) & 1 == 0 {
                self.raw(OperationType::BitInvert).c_target = bit;
            }
            self.raw(OperationType::PushCondition).c_condition = bit;
        }
    }

    fn unemit_condition(&mut self, start: usize, width: usize, expected: usize) {
        for i in (0..width).rev() {
            let bit = self.cmap[start + i];
            self.raw(OperationType::PopCondition);
            if (expected >> i) & 1 == 0 {
                self.raw(OperationType::BitInvert).c_target = bit;
            }
        }
    }

    fn emit_leaf(&mut self, tag: u8, q: &[QubitId; 3], qlen: usize, c: BitId, clen: usize) {
        match tag {
            8 => {
                assert!(matches!(self.pending_hmr, PendingHmr::None));
                assert_eq!(qlen, 1);
                self.pending_hmr = PendingHmr::H(q[0]);
                return;
            }
            9 => {
                let PendingHmr::H(hq) = self.pending_hmr else {
                    panic!("measurement without preceding H")
                };
                assert_eq!(qlen, 1);
                assert_eq!(q[0], hq);
                assert_eq!(clen, 1);
                self.pending_hmr = PendingHmr::Measure(hq, c);
                return;
            }
            10 => {
                let PendingHmr::Measure(hq, bit) = self.pending_hmr else {
                    panic!("reset without preceding H/measurement")
                };
                assert_eq!(qlen, 1);
                assert_eq!(q[0], hq);
                let op = self.raw(OperationType::Hmr);
                op.q_target = hq;
                op.c_target = bit;
                self.pending_hmr = PendingHmr::None;
                return;
            }
            _ => assert!(
                matches!(self.pending_hmr, PendingHmr::None),
                "incomplete HMR"
            ),
        }
        match tag {
            1 | 2 => {
                assert_eq!(qlen, 1);
                self.raw(if tag == 1 {
                    OperationType::X
                } else {
                    OperationType::Z
                })
                .q_target = q[0];
            }
            3 | 4 | 7 => {
                assert_eq!(qlen, 2);
                let kind = match tag {
                    3 => OperationType::CX,
                    4 => OperationType::CZ,
                    _ => OperationType::Swap,
                };
                let op = self.raw(kind);
                op.q_control1 = q[0];
                op.q_target = q[1];
            }
            5 | 6 => {
                assert_eq!(qlen, 3);
                let op = self.raw(if tag == 5 {
                    OperationType::CCX
                } else {
                    OperationType::CCZ
                });
                op.q_control2 = q[0];
                op.q_control1 = q[1];
                op.q_target = q[2];
            }
            _ => panic!("unknown paper-2607 HIR primitive tag {tag}"),
        }
        assert_eq!(clen, 0, "unexpected classical target on unitary primitive");
    }
}

// Luongo et al. arXiv:2407.20167, single-bit measurement uncomputation.
// This is ONLY the final comparator of a forward modular addition. The same
// comparator at the beginning of subtraction computes a flag and is excluded.
fn predicate_cleanup(
    reader: &mut Reader<'_>, state: &mut State, node_id: usize,
    qstart: usize, ctrl: usize,
) -> usize {
    let (left_start, right_start, carry, flag) = match node_id {
        2262 => (512, 256, 768, 769), // forward multiplication
        2265 => (256, 0, 513, 514),   // forward squaring, copied control
        2267 => (257, 1, 513, 514),   // forward runtime-coordinate addition
        _ => panic!("unapproved arithmetic predicate node"),
    };
    predicate_cleanup_n(reader,state,node_id,qstart,ctrl,256)
}
fn predicate_cleanup_n(reader: &mut Reader<'_>, state: &mut State, node_id: usize, qstart: usize, ctrl: usize, n: usize) -> usize {
    assert!((1..=256).contains(&n));
    let (left_start, right_start, carry, flag) = match node_id {
        2262 => (512, 256, 768, 769),
        2265 => (256, 0, 513, 514),
        2267 => (257, 1, 513, 514),
        _ => panic!("unapproved arithmetic predicate node"),
    };
    let mut original: Vec<(u8, Vec<usize>)> = Vec::with_capacity(8 * n + 5);
    let mut add = |tag, wires: &[usize]| original.push((tag, wires.to_vec()));
    for i in 0..n { add(1, &[right_start + i]); }
    add(1, &[carry]);
    for i in 0..n {
        let (a, b, c) = (left_start + i, right_start + i,
            if i == 0 { carry } else { left_start + i - 1 });
        add(3, &[a,b]); add(3, &[a,c]); add(5, &[c,b,a]);
    }
    add(1, &[left_start+n-1]);
    add(5, &[ctrl,left_start+n-1,flag]);
    add(1, &[left_start+n-1]);
    for i in (0..n).rev() {
        let (a, b, c) = (left_start + i, right_start + i,
            if i == 0 { carry } else { left_start + i - 1 });
        add(5, &[c,b,a]); add(3, &[a,c]); add(3, &[a,b]);
    }
    add(1, &[carry]);
    for i in 0..n { add(1, &[right_start+i]); }
    // Validate the entire source block, including unconditionality and wire
    // order, before emitting a single replacement operation. No fuzzy matches.
    for (tag, wires) in &original {
        assert_eq!(reader.byte(), *tag, "predicate source gate mismatch");
        assert_eq!(reader.uvar(), 0, "conditional predicate source");
        assert_eq!(reader.uvar(), 1);
        assert_eq!(reader.uvar(), wires.len());
        for &q in wires { assert_eq!(reader.uvar(), q, "predicate source wire mismatch"); }
        assert_eq!(reader.uvar(), 0);
    }
    state.flush_raw();state.carry_entries+=1;
    let cq=state.qmap[qstart+carry];let aq=state.qmap[qstart+left_start];let bq=state.qmap[qstart+right_start];
    let mut used:Vec<_>=(0..n).flat_map(|i|[state.qmap[qstart+left_start+i].0,state.qmap[qstart+right_start+i].0]).chain([cq.0]).collect();used.sort_unstable();used.dedup();
    let carry_clean=state.proof.qubit_is_zero(cq.0 as usize);if carry_clean{state.carry_zero+=1;}
    let capture_free=state.capture.is_none();
    // n=1 overlaps the five-record MSB endpoint; conservatively leave LSB alone.
    let carry_admit=state.carry_enabled&&n>1&&carry_clean&&used.len()==2*n+1&&![cq,aq,bq].contains(&QubitId(0))&&capture_free;
    let bit = state.predicate_bit;
    let flag_q = state.qmap[qstart+flag];
    let hmr = state.raw(OperationType::Hmr);
    hmr.q_target = flag_q; hmr.c_target = bit;
    state.raw(OperationType::PushCondition).c_condition = bit;
    let endpoint = 4*n;
    let locals = [ctrl, if n==1 {carry} else {left_start+n-2}, right_start+n-1, left_start+n-1];
    let four: Vec<_> = locals.iter().map(|q|state.qmap[qstart+q]).collect();
    let injective = state.endpoint_enabled && capture_free && (0..4).all(|i|(0..i).all(|j|four[i]!=four[j]));
    assert_eq!(&original[endpoint..endpoint+5], &[
        (5,vec![locals[1],locals[2],locals[3]]),(1,vec![locals[3]]),
        (5,vec![ctrl,locals[3],flag]),(1,vec![locals[3]]),(5,vec![locals[1],locals[2],locals[3]])]);
    for (index,(tag, wires)) in original.iter().enumerate() {
        let lsb_boundary=carry_admit&&index==7*n+1;
        if lsb_boundary{state.flush_raw();assert!(state.capture.is_none());state.capture=Some(Vec::new());}
        if injective && index==endpoint {
            state.flush_raw(); assert!(state.capture.is_none());state.capture=Some(Vec::new());
        }
        let is_output = *tag == 5 && wires[2] == flag;
        let len = if is_output { 2 } else { wires.len() };
        let mut mapped = [NO_QUBIT; 3];
        for i in 0..len { mapped[i] = state.qmap[qstart+wires[i]]; }
        // Replacing the sole flag toggle by CZ computes the phase of the
        // predicate without touching the measured/reset flag. The surrounding
        // carry compute/uncompute is executed only for measurement outcome 1.
        state.emit_leaf(if is_output { 4 } else { *tag }, &mapped, len, NO_BIT, 0);
        if lsb_boundary{
            assert_eq!((*tag,wires.as_slice()),(5,[carry,right_start,left_start].as_slice()));state.flush_raw();let old=state.capture.take().unwrap();let mut ccx=Op::empty();ccx.kind=OperationType::CCX;ccx.q_control2=cq;ccx.q_control1=bq;ccx.q_target=aq;let new=carry_replacement(&ccx,state.measurement_bit);
            if old.iter().any(|o|matches!(o.kind,OperationType::CCX|OperationType::CCZ)){state.carry_selected+=1;let delta=new.len()as isize-old.len()as isize;state.carry_delta+=delta;state.selected_delta+=delta;state.output_ops-=old.len();for o in old{state.output_hist[o.kind as usize]-=1;}for o in new{state.write(o);}}else{for o in old{state.deliver(o);}}
        }
        if injective && index==endpoint+4 {
            state.flush_raw();let captured=state.capture.take().unwrap();
            // Unknown measurement condition suppresses support/MBU lowering.
            // Preserve every classical operation; this window contains none.
            assert!(captured.iter().all(|o|o.c_target==NO_BIT && o.c_condition==NO_BIT));
            let mut replacement=Vec::new();
            let mut z=Op::empty();z.kind=OperationType::Z;z.q_target=four[0];replacement.push(z);
            let mut cz=Op::empty();cz.kind=OperationType::CZ;cz.q_control1=four[0];cz.q_target=four[3];replacement.push(cz);
            let mut ccz=Op::empty();ccz.kind=OperationType::CCZ;ccz.q_control2=four[0];ccz.q_control1=four[1];ccz.q_target=four[2];replacement.push(ccz);
            let is_t=|o:&Op|matches!(o.kind,OperationType::CCX|OperationType::CCZ);
            let outer=|o:&Op|is_t(o)&&(o.q_control1==QubitId(0)||o.q_control2==QubitId(0));
            let cost=|v:&[Op]|v.iter().filter(|o|is_t(o)&&!outer(o)).count();
            if cost(&replacement)<cost(&captured) {
                state.endpoint_blocks+=1;state.endpoint_outer+=usize::from(outer(&ccz));
                state.selected_delta+=replacement.len() as isize-captured.len() as isize;
                state.output_ops-=captured.len();for o in &captured {state.output_hist[o.kind as usize]-=1;}
                state.outer_lowered=state.outer_lowered-captured.iter().filter(|o|outer(o)).count()+replacement.iter().filter(|o|outer(o)).count();
                for o in replacement {o.validate();state.write(o);}
            }else {for o in captured{state.deliver(o);}}
        }
    }
    state.raw(OperationType::PopCondition);
    state.predicate_blocks += 1;
    original.len()
}

fn expand_node(
    graph: &Graph<'_>,
    state: &mut State,
    node_id: usize,
    qstart: usize,
    qlen: usize,
    cstart: usize,
    clen: usize,
) {
    let node = graph.nodes[node_id];
    let mut reader = Reader {
        data: &graph.data[node.start..node.end],
        at: 0,
    };
    assert_eq!(reader.uvar(), qlen, "bad HIR qubit map for node {node_id}");
    assert_eq!(reader.uvar(), clen, "bad HIR bit map for node {node_id}");
    let op_count = reader.uvar();
    let cleanups = match node_id {
        2262 => predicate_offsets::NODE_2262,
        2265 => predicate_offsets::NODE_2265,
        2267 => predicate_offsets::NODE_2267,
        _ => &[],
    };
    let mut cleanup_index = 0;
    let mut op_index = 0;
    let mut retention_index=0;let mut retention_active=None;
    let mut length_window = None;
    while op_index < op_count {
        state.retention_boundary(node_id,op_index,reader.at,qstart,cstart,&mut retention_index,&mut retention_active);
        state.flush_raw();
        if node_id==graph.root{state.comparator.root=op_index;}
        if node_id==2262{comparator::boundary(state,&reader,op_index,qstart,cstart);}
        state.one_allowed=!((node_id==2261&&(155419..155438).contains(&op_index))||(node_id==2263&&(10661..10680).contains(&op_index)));
        if let Some(&(offset, ctrl)) = cleanups.get(cleanup_index) {
            assert!(reader.at <= offset, "missed exact predicate boundary");
            if reader.at == offset {
                op_index += predicate_cleanup(&mut reader, state, node_id, qstart, ctrl);
                cleanup_index += 1;
                continue;
            }
        }
        if stable_lengths::try_apply(state, &mut reader, node_id, op_index, op_count,
            qstart, qlen, cstart, clen, &mut length_window)
        { op_index += 36; continue; }
        if qlen == 578 && clen == 1 && op_count - op_index >= 65
            && reader.data[reader.at] == 5
            && prefix_retention::try_apply(state, &mut reader, qstart, cstart)
        { op_index += 65; continue; }
        if qlen == 578 && clen == 1 && op_count - op_index >= 7
            && reader.data[reader.at] == 5
            && shared_product::try_apply(state, &mut reader, qstart, cstart)
        {
            op_index += 7;
            continue;
        }
        if state.motif_enabled {
            let boundary=cleanups.get(cleanup_index).map(|x|x.0).unwrap_or(usize::MAX);
            if let Some(used)=motif::try_apply(state,&mut reader,node_id,op_index,op_count,qstart,qlen,boundary) {
                op_index+=used;continue;
            }
        }
        if state.family24_enabled{let boundary=cleanups.get(cleanup_index).map(|x|x.0).unwrap_or(usize::MAX);if let Some(used)=family24::try_apply(state,&mut reader,node_id,op_index,op_count,qstart,qlen,boundary){op_index+=used;continue;}}
        if state.family36_enabled{let boundary=cleanups.get(cleanup_index).map(|x|x.0).unwrap_or(usize::MAX);if let Some(used)=family36::try_apply(state,&mut reader,node_id,op_index,op_count,qstart,qlen,boundary){op_index+=used;continue;}}
        if state.family63_enabled{let boundary=cleanups.get(cleanup_index).map(|x|x.0).unwrap_or(usize::MAX);if let Some(used)=family63::try_apply(state,&mut reader,node_id,op_index,op_count,qstart,qlen,boundary){op_index+=used;continue;}}
        op_index += 1;
        let tag = reader.byte();
        let condition_width = reader.uvar();
        let expected = reader.uvar();
        if condition_width == 0 {
            assert_eq!(expected, 1);
        } else {
            assert!(condition_width < usize::BITS as usize);
            assert!(expected < (1usize << condition_width));
        }
        let condition_start = state.cmap.len();
        for _ in 0..condition_width {
            let local = reader.uvar();
            assert!(local < clen);
            state.cmap.push(state.cmap[cstart + local]);
        }
        state.emit_condition(condition_start, condition_width, expected);

        if tag == 11 {
            let child = reader.uvar();
            assert!(child < node_id);
            let child_qstart = state.qmap.len();
            let child_qlen = reader.uvar();
            for _ in 0..child_qlen {
                let local = reader.uvar();
                assert!(local < qlen);
                state.qmap.push(state.qmap[qstart + local]);
            }
            let child_cstart = state.cmap.len();
            let child_clen = reader.uvar();
            for _ in 0..child_clen {
                let local = reader.uvar();
                assert!(local < clen);
                state.cmap.push(state.cmap[cstart + local]);
            }
            let previous_direction = state.lengths.direction;
            state.lengths.direction = stable_lengths::child_direction(state, node_id, op_index-1,
                qstart, qlen, cstart, clen, child, child_qstart, child_qlen,
                child_cstart, child_clen, condition_width);
            expand_node(
                graph,
                state,
                child,
                child_qstart,
                child_qlen,
                child_cstart,
                child_clen,
            );
            state.lengths.direction = previous_direction;
            state.qmap.truncate(child_qstart);
            state.cmap.truncate(child_cstart);
        } else {
            let mut qargs = [NO_QUBIT; 3];
            let leaf_qlen = reader.uvar();
            assert!(leaf_qlen <= qargs.len());
            for target in qargs.iter_mut().take(leaf_qlen) {
                let local = reader.uvar();
                assert!(local < qlen);
                *target = state.qmap[qstart + local];
            }
            let leaf_clen = reader.uvar();
            assert!(leaf_clen <= 1);
            let c = if leaf_clen == 1 {
                let local = reader.uvar();
                assert!(local < clen);
                state.cmap[cstart + local]
            } else {
                NO_BIT
            };
            assert!(condition_width == 0 || !matches!(tag, 8 | 9 | 10));
            state.emit_leaf(tag, &qargs, leaf_qlen, c, leaf_clen);
        }

        state.unemit_condition(condition_start, condition_width, expected);
        state.cmap.truncate(condition_start);
    }
    state.retention_boundary(node_id,op_index,reader.at,qstart,cstart,&mut retention_index,&mut retention_active);
    assert!(retention_active.is_none());
    assert_eq!(cleanup_index, cleanups.len(), "missing predicate source block");
    assert_eq!(op_index, op_count);
    assert_eq!(
        reader.at,
        reader.data.len(),
        "trailing bytes in HIR node {node_id}"
    );
}

fn declare_register(out: &mut Vec<Op>, register: u64, qubits: &[QubitId], bits: &[BitId]) {
    for &qubit in qubits {
        let mut op = Op::empty();
        op.kind = OperationType::AppendToRegister;
        op.q_target = qubit;
        op.r_target = RegisterId(register);
        out.push(op);
    }
    for &bit in bits {
        let mut op = Op::empty();
        op.kind = OperationType::AppendToRegister;
        op.c_target = bit;
        op.r_target = RegisterId(register);
        out.push(op);
    }
    let mut op = Op::empty();
    op.kind = OperationType::Register;
    op.r_target = RegisterId(register);
    out.push(op);
}

fn eliminate_constant_outer_control(ops: &mut Vec<Op>, control: QubitId) {
    let mut removed_control_toggles = 0usize;
    let mut lowered_toffolis = 0usize;
    ops.retain_mut(|op| {
        if op.q_target == control {
            match op.kind {
                OperationType::X => {removed_control_toggles += 1;return false;},
                OperationType::Z => {op.kind=OperationType::Neg;op.q_target=NO_QUBIT;},
                _ => panic!("unsupported outer-control target"),
            }
        }
        match op.kind {
            OperationType::CX | OperationType::CZ if op.q_control1 == control => {
                op.kind = if op.kind == OperationType::CX {
                    OperationType::X
                } else {
                    OperationType::Z
                };
                op.q_control1 = NO_QUBIT;
            }
            OperationType::CCX | OperationType::CCZ
                if op.q_control1 == control || op.q_control2 == control =>
            {
                let other = if op.q_control1 == control {
                    op.q_control2
                } else {
                    op.q_control1
                };
                op.kind = if op.kind == OperationType::CCX {
                    OperationType::CX
                } else {
                    OperationType::CZ
                };
                op.q_control2 = NO_QUBIT;
                op.q_control1 = other;
                lowered_toffolis += 1;
            }
            OperationType::Swap if op.q_control1 == control || op.q_target == control => {
                panic!("paper outer control is unexpectedly swapped")
            }
            _ => {
                assert_ne!(
                    op.q_control1, control,
                    "paper outer control has an unsupported control use"
                );
                assert_ne!(
                    op.q_control2, control,
                    "paper outer control has an unsupported control use"
                );
            }
        }
        for qubit in [&mut op.q_control2, &mut op.q_control1, &mut op.q_target] {
            if *qubit != NO_QUBIT {
                assert!(qubit.0 > control.0);
                qubit.0 -= 1;
            }
        }
        true
    });
    assert_eq!(
        removed_control_toggles, 2,
        "paper outer control must be initialized and cleaned exactly once"
    );
    eprintln!("PAPER2607_CONST_CTRL: removed_qubits=1 lowered_toffolis={lowered_toffolis}");
}

fn coalesce_metadata_lifetime(out: &mut [Op]) -> metadata_lt8::Census {
    metadata_lt8::coalesce(out, metadata_lt8::Lease { high: 787, pool: 834 })
        .expect("pre-peephole metadata lease must have no direct or ABI aliases")
}

pub(super) fn build() -> Vec<Op> {
    let original = zstd::stream::decode_all(COMPRESSED_HIR).expect("decode paper-2607 HIR");
    let decoded = shift_controls::replace(&original);
    drop(original);
    let graph = parse_graph(&decoded);
    shared_product::validate_phase_child(&graph);
    comparator::validate_helper(&graph);
    assert_eq!(graph.root_bits % 5, 0);
    let n = graph.root_bits / 5;
    assert!(
        graph.root_qubits > 1 + 3 * n,
        "paper-2607 HIR must include the outer control, X/Y/A, and workspace"
    );
    let declarations = 4 * (n + 1);
    let summary = graph.summaries[graph.root];
    let qinputs: Vec<_> = (1..=2 * n).collect();
    let cinputs: Vec<_> = (0..2 * n).collect();
    let mut state = State::new(
        graph.root_qubits,
        graph.root_bits,
        &qinputs,
        &cinputs,
        true,
        (summary.output_ops + declarations + summary.toffoli).min(405_000_000),
    );
    state.endpoint_enabled=true;state.carry_enabled=true;
    stable_lengths::configure(&mut state, &graph, COMPRESSED_HIR);
    state.motif_enabled = true;
    state.motif_exclusions = motif::exclusions(&graph);
    let tx: Vec<_> = (1..=n).map(|index| QubitId(index as u64)).collect();
    let ty: Vec<_> = (n + 1..=2 * n).map(|index| QubitId(index as u64)).collect();
    let ox: Vec<_> = (0..n).map(|index| BitId(index as u64)).collect();
    let oy: Vec<_> = (n..2 * n).map(|index| BitId(index as u64)).collect();
    declare_register(&mut state.out, 0, &tx, &[]);
    declare_register(&mut state.out, 1, &ty, &[]);
    declare_register(&mut state.out, 2, &[], &ox);
    declare_register(&mut state.out, 3, &[], &oy);
    expand_node(
        &graph,
        &mut state,
        graph.root,
        0,
        graph.root_qubits,
        0,
        graph.root_bits,
    );
    state.flush_raw();
    assert!(matches!(state.pending_hmr, PendingHmr::None));
    assert!(state.proof.balanced());
    assert_eq!(state.predicate_blocks, 1284);
    state.assert_accounting(summary.output_ops, declarations);
    eprintln!("STABLE_LENGTH_ZERO: enabled={} windows={:?} rewrites={} unknown_scratch={} capture_blocked={} boundary_blocked={} alias_blocked={}", state.lengths.enabled, state.lengths.windows, state.lengths.rewrites, state.lengths.unknown_scratch, state.lengths.capture_blocked, state.lengths.boundary_blocked, state.lengths.alias_blocked);
    eprintln!("ONE_RESIDUAL_MBU: semantic_cleanups={} emitted_cleanups={} skipped_by_motif={}",state.one_cleanups,state.one_cleanups-state.skipped_one,state.skipped_one);
    eprintln!("CURRENT_FAMILIES: residual={:?} skipped_residual={:?} family24={:?} family36={:?} family63={:?}",state.residual_counts,state.skipped_residual,state.family24_counts,state.family36_counts,state.family63_counts);
    eprintln!("COMPARATOR_REFINEMENT: eligible={} selected={} saving={} delta={} skipped_private_hmr={} skipped_private_neg={} final_private_hmr={} final_private_neg={}",state.comparator.eligible,state.comparator.selected,state.comparator.saving,state.comparator.delta,state.comparator.skipped_private_hmr,state.comparator.skipped_private_neg,state.final_private_hmr,state.final_private_neg);
    eprintln!("GENERAL_RETENTION: entries={} proven={} selected={} fallback={} removed_ops={}",state.retention.entries,state.retention.proven,state.retention.selected,state.retention.fallback,state.retention.removed_ops);
    eprintln!("MOTIF_REFINEMENT: matched={:?} selected={:?} t_saved={} output_delta={} skipped_cleanups={} skipped_support={:?}",state.motif_counts,state.selected_counts,state.selected_t_saving,state.selected_delta+state.retention.removed_ops as isize,state.skipped_cleanups,state.skipped_support);
    eprintln!("SUPPORT_LOWERING: dead={} x={} cx={}",state.proof.support_dead,state.proof.support_x,state.proof.support_cx);
    eprintln!(
        "CLEAN_AND_MBU: semantic_rewrites={} emitted_rewrites={} extra_bits=1 cache_evictions={} live_collections={}",
        state.proof.rewrites,
        state.proof.rewrites - state.skipped_cleanups,
        state.proof.evictions(), state.proof.collections()
    );
    let conditional_t=512*state.predicate_blocks-state.carry_selected-state.endpoint_blocks-state.endpoint_outer;
    let post_q0=state.output_hist[OperationType::CCX as usize]+state.output_hist[OperationType::CCZ as usize]-state.outer_lowered;
    eprintln!("PREDICATE_MBU: blocks={} conditional_toffoli={} carry={} endpoint={} endpoint_outer={} expected_2T={} extra_bits=1",state.predicate_blocks,conditional_t,state.carry_selected,state.endpoint_blocks,state.endpoint_outer,2*post_q0-conditional_t);
    eprintln!("SHARED_PRODUCT: hits={} rewrites={} unknown_pool={}", state.shared_hits, state.shared_rewrites, state.shared_unknown_pool);
    // Finish semantic expansion/accounting in original logical coordinates.
    // Establish the physical alias BEFORE any final whole-stream peephole.
    assert_eq!((graph.root_qubits, graph.root_bits, n), (835, 1280, 256));
    let lease_report = coalesce_metadata_lifetime(&mut state.out);
    eprintln!("LT8_COALESCE placement=before_final_peephole logical_pair=787/834 {lease_report:?}");
    let peephole_stats = peephole::cancel_identical_pairs(&mut state.out);
    let peephole_2t = 4 * peephole_stats.ccx_uncond_pairs + 2 * peephole_stats.ccx_cond_pairs;
    eprintln!(
        "PEEPHOLE_CANCEL: passes={} removed_ops={} ccx_uncond_pairs={} ccx_cond_pairs={} other_pairs={} expected_2T={}",
        peephole_stats.passes, peephole_stats.removed_ops, peephole_stats.ccx_uncond_pairs,
        peephole_stats.ccx_cond_pairs, peephole_stats.other_pairs,
        2 * post_q0 as u64 - conditional_t as u64 - peephole_2t,
    );
    let outer_eliminated = std::env::var_os("PAPER2607_KEEP_CONTROL").is_none();
    if outer_eliminated {
        eliminate_constant_outer_control(&mut state.out, QubitId(0));
    }
    eprintln!("PREFIX_RETENTION: hits={} rewrites={} unknown={}",state.prefix_hits,state.prefix_rewrites,state.prefix_unknown);
    let root_qubits = graph.root_qubits;
    let root_bits = graph.root_bits;
    let mut out = std::mem::take(&mut state.out);
    // Release graph/proof storage before the optional packed deletion mask.
    drop(state);
    drop(graph);
    drop(decoded);
    if outer_eliminated && std::env::var("PAPER2607_OVERLAP_CANCEL").ok().as_deref() != Some("0") {
        let stats = commuting_cancel::cancel(&mut out);
        eprintln!("OVERLAPPING_CANCEL physical_after_lease=true {stats:?}");
    } else {
        eprintln!("OVERLAPPING_CANCEL skipped outer_eliminated={outer_eliminated}");
    }
    eprintln!(
        "PAPER2607_HIR: n={n} qubits={} bits={} ops={} toffoli={}",
        root_qubits,
        root_bits,
        out.len(),
        summary.toffoli,
    );
    out
}

#[cfg(test)]
#[path = "support_tests.rs"]
mod support_tests;

#[cfg(test)]
mod mbu_tests {
    use super::*;
    #[test]
    fn hir_emission_applies_proved_cleanup() {
        let mut state = State::new(4, 0, &[1, 2], &[], true, 0);
        let q = [QubitId(1), QubitId(2), QubitId(3)];
        state.emit_leaf(5, &q, 3, NO_BIT, 0);
        state.emit_leaf(5, &q, 3, NO_BIT, 0);
        state.flush_raw();
        assert_eq!(
            state
                .out
                .iter()
                .filter(|o| o.kind == OperationType::Hmr)
                .count(),
            1
        );
    }
    #[test]
    fn predicate_emitter_full_width_both_measurements() {
        use crate::sim::Simulator;
        use sha3::digest::XofReader;
        struct Outcome(u8);
        impl XofReader for Outcome { fn read(&mut self, b: &mut [u8]) { b.fill(self.0); } }
        let fixture = include_bytes!("predicate_comparator_test.hir");
        let inputs: Vec<_> = (0..513).collect();
        let mut state = State::new(518, 256, &inputs, &[], true, 0);
        let mut reader = Reader { data: fixture, at: 0 };
        assert_eq!(predicate_cleanup(&mut reader, &mut state, 2267, 0, 0), 2053);
        state.flush_raw();
        assert_eq!(reader.at, fixture.len());
        assert_eq!(state.out.len(), 2056);
        assert!(state.proof.balanced());
        for op in &state.out { op.validate(); }
        // Exercise each bit position as the decisive comparison bit, equality,
        // both control values and both measurement outcomes, using the trusted
        // simulator and the actual 256-bit emitted replacement.
        for decisive in 0..256 {
            for order in 0..3 {
                for ctrl in 0..2 {
                    for outcome in [0, 255] {
                        let mut rng = Outcome(outcome);
                        let mut sim = Simulator::new(518, 258, &mut rng);
                        sim.qubits[0] = ctrl;
                        sim.qubits[1+decisive] = u64::from(order != 2);
                        sim.qubits[257+decisive] = u64::from(order != 0);
                        let mut expected = sim.qubits.clone();
                        sim.qubits[514] = ctrl & u64::from(order == 0);
                        sim.apply_iter(state.out.iter());
                        expected[514] = 0;
                        for (got, want) in sim.qubits.iter().zip(expected) { assert_eq!(got & 1, want); }
                        assert_eq!(sim.phase & 1, 0, "bit={decisive} order={order} ctrl={ctrl} m={outcome}");
                    }
                }
            }
        }
    }
}


#[cfg(test)]
#[path="one_tests.rs"]
mod one_tests;
#[cfg(test)]
#[test]
#[ignore="single authorized count-only candidate census"]
fn one_source_census(){
 let decoded=zstd::stream::decode_all(COMPRESSED_HIR).unwrap();let graph=parse_graph(&decoded);
 shared_product::validate_phase_child(&graph);
 let qi:Vec<_>=(1..=512).collect();let ci:Vec<_>=(0..512).collect();
 let mut state=State::new(graph.root_qubits,graph.root_bits,&qi,&ci,false,0);
 state.motif_enabled=true;state.motif_exclusions=motif::exclusions(&graph);
 expand_node(&graph,&mut state,graph.root,0,graph.root_qubits,0,graph.root_bits);state.flush_raw();
 state.assert_accounting(graph.summaries[graph.root].output_ops,0);assert!(state.proof.balanced());
 let static_t=state.output_hist[OperationType::CCX as usize]+state.output_hist[OperationType::CCZ as usize]-state.outer_lowered;
 println!("one={} skipped_one={} expected_t={} output={} delta={} motif={:?} selected={:?} skipped_cleanups={} trace={:016x}{:016x} fingerprint={}",state.one_cleanups,state.skipped_one,static_t-512*state.predicate_blocks/2,state.output_ops,state.selected_delta,state.motif_counts,state.selected_counts,state.skipped_cleanups,state.trace[0],state.trace[1],state.proof.diagnostic_fingerprint());
 assert_eq!(state.one_cleanups,257245);
 assert_eq!(state.skipped_one,0);
 assert_eq!(static_t,63866766);
 assert_eq!(static_t-512*state.predicate_blocks/2,63538062);
 assert_eq!(state.output_ops,404464825);
 assert_eq!(state.selected_delta,-47903);
 assert_eq!(state.selected_counts,[170,340,11701]);
 assert_eq!(state.motif_counts,[64800,35640,12960]);
 assert_eq!(state.skipped_cleanups,11610);
 assert_eq!(state.outer_lowered,2060);

 assert_eq!(state.input_ops,401952311);
 assert_eq!(state.proof.rewrites,1790307);
 assert_eq!([state.proof.support_dead,state.proof.support_x,state.proof.support_cx],[1625,1415,72669]);
 assert_eq!(state.prefix_rewrites,7421);assert_eq!(state.shared_rewrites,4229758);assert_eq!(state.predicate_blocks,1284);
 assert_eq!(state.trace,[0x5a945678ac79fd0d,0x7af8b3900bbc1cf0]);
 assert!(state.proof.diagnostic_fingerprint().contains("ded6a0ecf7fd66c397794aeb68a2d979059d16a2de7ad347195d165718c19270"));
}

include!("retention.rs");

#[test]
#[ignore="coordinated comparator plus retention count"]
fn comparator_retention_count(){
 let data=zstd::stream::decode_all(COMPRESSED_HIR).unwrap();let g=parse_graph(&data);shared_product::validate_phase_child(&g);comparator::validate_helper(&g);
 let qi:Vec<_>=(1..=512).collect();let ci:Vec<_>=(0..512).collect();let mut s=State::new(g.root_qubits,g.root_bits,&qi,&ci,false,0);s.motif_enabled=true;s.motif_exclusions=motif::exclusions(&g);
 expand_node(&g,&mut s,g.root,0,g.root_qubits,0,g.root_bits);s.flush_raw();s.assert_accounting(g.summaries[g.root].output_ops,0);assert!(s.comparator_capture.is_none());assert!(s.proof.balanced());
 let t=s.output_hist[OperationType::CCX as usize]+s.output_hist[OperationType::CCZ as usize]-s.outer_lowered-512*s.predicate_blocks/2;
 assert_eq!(t,63302322);assert_eq!(s.output_ops,400626103);assert_eq!(s.comparator.selected,1527);assert_eq!(s.comparator.saving,187823);assert_eq!(s.comparator.delta,-3599137);assert_eq!([s.comparator.skipped_private_hmr,s.comparator.skipped_private_neg],[3052,0]);assert_eq!([s.final_private_hmr,s.final_private_neg],[2032890,257245]);
 assert_eq!(s.input_ops,401952311);assert_eq!(s.comparator.eligible,1527);assert_eq!(t+s.comparator.saving,63490145);assert_eq!(s.output_ops as isize-s.comparator.delta,404225240);
 assert_eq!([s.retention.selected,s.retention.proven,s.retention.fallback],[47917,49176,1259]);assert_eq!(s.selected_counts,[170,340,11701]);assert_eq!(s.selected_delta,-287488);
 assert_eq!(s.proof.rewrites,1790307);assert_eq!(s.one_cleanups,257245);assert_eq!(s.skipped_one,0);assert_eq!(s.skipped_cleanups,11610);assert_eq!(s.skipped_support,[0;3]);assert_eq!([s.proof.support_dead,s.proof.support_x,s.proof.support_cx],[1625,1415,72669]);
 assert_eq!(s.final_private_hmr,s.proof.rewrites as usize+s.one_cleanups-s.skipped_cleanups as usize-s.skipped_one-s.comparator.skipped_private_hmr);assert_eq!(s.final_private_neg,s.one_cleanups-s.skipped_one-s.comparator.skipped_private_neg);
 assert_eq!(s.trace,[0x5a945678ac79fd0d,0x7af8b3900bbc1cf0]);assert!(s.proof.diagnostic_fingerprint().contains("ded6a0ecf7fd66c397794aeb68a2d979059d16a2de7ad347195d165718c19270"));
 println!("expectedT={t} output={} comparator_eligible={} selected={} savings={} delta={} skipped_private_hmr={} skipped_private_neg={} final_private_hmr={} final_private_neg={} retention={} semantic_clean={} semantic_one={} skipped_clean={} skipped_one={} trace={:016x}{:016x} fingerprint={}",s.output_ops,s.comparator.eligible,s.comparator.selected,s.comparator.saving,s.comparator.delta,s.comparator.skipped_private_hmr,s.comparator.skipped_private_neg,s.final_private_hmr,s.final_private_neg,s.retention.selected,s.proof.rewrites,s.one_cleanups,s.skipped_cleanups,s.skipped_one,s.trace[0],s.trace[1],s.proof.diagnostic_fingerprint());
}

#[cfg(test)]#[path="wire_tests.rs"]mod wire_tests;
#[test]
#[ignore="new combined residual plus family24 source count requires a slot grant"]
fn residual_family24_count(){
 let data=zstd::stream::decode_all(COMPRESSED_HIR).unwrap();let g=parse_graph(&data);shared_product::validate_phase_child(&g);comparator::validate_helper(&g);let qi:Vec<_>=(1..=512).collect();let ci:Vec<_>=(0..512).collect();let mut s=State::new(g.root_qubits,g.root_bits,&qi,&ci,false,0);s.motif_enabled=true;s.motif_exclusions=motif::exclusions(&g);
 expand_node(&g,&mut s,g.root,0,g.root_qubits,0,g.root_bits);s.flush_raw();s.assert_accounting(g.summaries[g.root].output_ops,0);assert!(s.comparator_capture.is_none());assert!(s.proof.balanced());
 let t=s.output_hist[OperationType::CCX as usize]+s.output_hist[OperationType::CCZ as usize]-s.outer_lowered-512*s.predicate_blocks/2;
 assert_eq!(s.input_ops,401952311);assert_eq!(s.proof.rewrites,1790307);assert_eq!(s.one_cleanups,257245);assert_eq!([s.proof.support_dead,s.proof.support_x,s.proof.support_cx],[1625,1415,72669]);assert_eq!(s.prefix_rewrites,7421);assert_eq!(s.shared_rewrites,4229758);assert_eq!(s.predicate_blocks,1284);
 let residual=s.residual_counts.iter().sum::<usize>();let skipped_residual=s.skipped_residual.iter().sum::<usize>();
 assert_eq!(s.final_private_hmr,s.proof.rewrites as usize+s.one_cleanups+residual-s.skipped_cleanups as usize-s.skipped_one-skipped_residual-s.comparator.skipped_private_hmr);
 assert_eq!(s.final_private_neg,s.one_cleanups+s.residual_counts[1]-s.skipped_one-s.skipped_residual[1]-s.comparator.skipped_private_neg);
 assert_eq!(s.trace,[0x5a945678ac79fd0d,0x7af8b3900bbc1cf0]);assert!(s.proof.diagnostic_fingerprint().contains("ded6a0ecf7fd66c397794aeb68a2d979059d16a2de7ad347195d165718c19270"));
 println!("baselineT=63302322 expectedT={t} net={} output={} residual={:?} skipped_residual={:?} family24={:?} retention=[{},{},{}] comparator=[{},{},{}] comparator_skipped_private=[{},{}] final_private=[{},{}] motif={:?} motif_saving={} skipped_clean={} skipped_one={} skipped_support={:?} delta={} comparator_delta={} trace={:016x}{:016x} fingerprint={}",63302322isize-t as isize,s.output_ops,s.residual_counts,s.skipped_residual,s.family24_counts,s.retention.selected,s.retention.proven,s.retention.fallback,s.comparator.eligible,s.comparator.selected,s.comparator.saving,s.comparator.skipped_private_hmr,s.comparator.skipped_private_neg,s.final_private_hmr,s.final_private_neg,s.selected_counts,s.selected_t_saving,s.skipped_cleanups,s.skipped_one,s.skipped_support,s.selected_delta,s.comparator.delta,s.trace[0],s.trace[1],s.proof.diagnostic_fingerprint());
}

fn carry_replacement(op:&Op,bit:BitId)->Vec<Op>{
 let [h,cz]=super::clean_and::replacement(op,bit);let mut z=Op::empty();z.kind=OperationType::Z;z.q_target=op.q_control2;z.c_condition=bit;let mut neg=Op::empty();neg.kind=OperationType::Neg;neg.c_condition=bit;let mut cx=Op::empty();cx.kind=OperationType::CX;cx.q_control1=op.q_control2;cx.q_target=op.q_target;let mut x=Op::empty();x.kind=OperationType::X;x.q_target=op.q_target;
 let out=vec![h,cz,z,neg,cx,x];for o in &out{o.validate();}out
}

#[cfg(test)]#[path="endpoint_tests.rs"]mod endpoint_tests;
#[cfg(test)]#[path="carry_tests.rs"]mod carry_tests;
#[cfg(test)]#[path="combined_predicate_tests.rs"]mod combined_predicate_tests;

#[test]
#[ignore="predicate composition source count requires a separate slot grant"]
fn combined_predicate_count(){
 let data=zstd::stream::decode_all(COMPRESSED_HIR).unwrap();let g=parse_graph(&data);shared_product::validate_phase_child(&g);comparator::validate_helper(&g);let qi:Vec<_>=(1..=512).collect();let ci:Vec<_>=(0..512).collect();let mut s=State::new(g.root_qubits,g.root_bits,&qi,&ci,false,0);s.endpoint_enabled=true;s.carry_enabled=true;s.motif_enabled=true;s.motif_exclusions=motif::exclusions(&g);
 expand_node(&g,&mut s,g.root,0,g.root_qubits,0,g.root_bits);s.flush_raw();s.assert_accounting(g.summaries[g.root].output_ops,0);assert!(s.capture.is_none()&&s.comparator_capture.is_none());assert!(s.proof.balanced());
 let post_q0=s.output_hist[OperationType::CCX as usize]+s.output_hist[OperationType::CCZ as usize]-s.outer_lowered;
 let conditional_t=512*s.predicate_blocks-s.carry_selected-s.endpoint_blocks-s.endpoint_outer;let expected_2t=2*post_q0-conditional_t;
 assert_eq!(s.input_ops,401952311);assert_eq!(s.proof.rewrites,1790307);assert_eq!(s.one_cleanups,257245);assert_eq!([s.proof.support_dead,s.proof.support_x,s.proof.support_cx],[1625,1415,72669]);
 let residual=s.residual_counts.iter().sum::<usize>();let skipped_residual=s.skipped_residual.iter().sum::<usize>();
 assert_eq!(s.final_private_hmr,s.proof.rewrites as usize+s.one_cleanups+residual+s.carry_selected-s.skipped_cleanups as usize-s.skipped_one-skipped_residual-s.comparator.skipped_private_hmr);
 assert_eq!(s.final_private_neg,s.one_cleanups+s.residual_counts[1]+s.carry_selected-s.skipped_one-s.skipped_residual[1]-s.comparator.skipped_private_neg);
 assert_eq!(s.trace,[0x5a945678ac79fd0d,0x7af8b3900bbc1cf0]);assert!(s.proof.diagnostic_fingerprint().contains("ded6a0ecf7fd66c397794aeb68a2d979059d16a2de7ad347195d165718c19270"));
 println!("baseline_2T=126545706 expected_2T={} net_2T={} post_q0={} conditional_t={} output={} carry=[{},{},{}] endpoint=[{},{}] outer_lowered={} residual={:?} skipped_residual={:?} family24={:?} retention=[{},{},{}] comparator=[{},{},{}] comparator_skipped_private=[{},{}] final_private=[{},{}] delta={} comparator_delta={} trace={:016x}{:016x} fingerprint={}",expected_2t,126545706isize-expected_2t as isize,post_q0,conditional_t,s.output_ops,s.carry_entries,s.carry_zero,s.carry_selected,s.endpoint_blocks,s.endpoint_outer,s.outer_lowered,s.residual_counts,s.skipped_residual,s.family24_counts,s.retention.selected,s.retention.proven,s.retention.fallback,s.comparator.eligible,s.comparator.selected,s.comparator.saving,s.comparator.skipped_private_hmr,s.comparator.skipped_private_neg,s.final_private_hmr,s.final_private_neg,s.selected_delta,s.comparator.delta,s.trace[0],s.trace[1],s.proof.diagnostic_fingerprint());
}

#[test]
#[ignore="joint family36 predicate count requires a separate slot grant"]
fn family36_predicate_count(){
 let data=zstd::stream::decode_all(COMPRESSED_HIR).unwrap();let g=parse_graph(&data);shared_product::validate_phase_child(&g);comparator::validate_helper(&g);let qi:Vec<_>=(1..=512).collect();let ci:Vec<_>=(0..512).collect();let mut s=State::new(g.root_qubits,g.root_bits,&qi,&ci,false,0);s.endpoint_enabled=true;s.carry_enabled=true;s.motif_enabled=true;s.motif_exclusions=motif::exclusions(&g);
 expand_node(&g,&mut s,g.root,0,g.root_qubits,0,g.root_bits);s.flush_raw();s.assert_accounting(g.summaries[g.root].output_ops,0);assert!(s.capture.is_none()&&s.comparator_capture.is_none());assert!(s.proof.balanced());
 let post_q0=s.output_hist[OperationType::CCX as usize]+s.output_hist[OperationType::CCZ as usize]-s.outer_lowered;
 let conditional_t=512*s.predicate_blocks-s.carry_selected-s.endpoint_blocks-s.endpoint_outer;let expected_2t=2*post_q0-conditional_t;
 assert_eq!(s.input_ops,401952311);assert_eq!(s.proof.rewrites,1790307);assert_eq!(s.one_cleanups,257245);assert_eq!([s.proof.support_dead,s.proof.support_x,s.proof.support_cx],[1625,1415,72669]);
 assert_eq!(s.family36_counts[0],115024);assert_eq!(s.family24_counts,[3240,3236]);assert_eq!([s.retention.selected,s.retention.proven,s.retention.fallback],[47917,49176,1259]);
 let residual=s.residual_counts.iter().sum::<usize>();let skipped_residual=s.skipped_residual.iter().sum::<usize>();
 assert_eq!(s.final_private_hmr,s.proof.rewrites as usize+s.one_cleanups+residual+s.carry_selected-s.skipped_cleanups as usize-s.skipped_one-skipped_residual-s.comparator.skipped_private_hmr);
 assert_eq!(s.final_private_neg,s.one_cleanups+s.residual_counts[1]+s.carry_selected-s.skipped_one-s.skipped_residual[1]-s.comparator.skipped_private_neg);
 assert_eq!(s.trace,[0x5a945678ac79fd0d,0x7af8b3900bbc1cf0]);assert!(s.proof.diagnostic_fingerprint().contains("ded6a0ecf7fd66c397794aeb68a2d979059d16a2de7ad347195d165718c19270"));
 println!("family36={:?}",s.family36_counts);
 println!("baseline_2T=126545706 expected_2T={} net_2T={} post_q0={} conditional_t={} output={} carry=[{},{},{}] endpoint=[{},{}] outer_lowered={} residual={:?} skipped_residual={:?} family24={:?} retention=[{},{},{}] comparator=[{},{},{}] comparator_skipped_private=[{},{}] final_private=[{},{}] delta={} comparator_delta={} trace={:016x}{:016x} fingerprint={}",expected_2t,126545706isize-expected_2t as isize,post_q0,conditional_t,s.output_ops,s.carry_entries,s.carry_zero,s.carry_selected,s.endpoint_blocks,s.endpoint_outer,s.outer_lowered,s.residual_counts,s.skipped_residual,s.family24_counts,s.retention.selected,s.retention.proven,s.retention.fallback,s.comparator.eligible,s.comparator.selected,s.comparator.saving,s.comparator.skipped_private_hmr,s.comparator.skipped_private_neg,s.final_private_hmr,s.final_private_neg,s.selected_delta,s.comparator.delta,s.trace[0],s.trace[1],s.proof.diagnostic_fingerprint());
}

#[test]
#[ignore="family63 count requires a separate slot grant"]
fn family63_count(){
 let data=zstd::stream::decode_all(COMPRESSED_HIR).unwrap();let g=parse_graph(&data);shared_product::validate_phase_child(&g);comparator::validate_helper(&g);let qi:Vec<_>=(1..=512).collect();let ci:Vec<_>=(0..512).collect();let mut s=State::new(g.root_qubits,g.root_bits,&qi,&ci,false,0);s.endpoint_enabled=true;s.carry_enabled=true;s.motif_enabled=true;s.motif_exclusions=motif::exclusions(&g);
 expand_node(&g,&mut s,g.root,0,g.root_qubits,0,g.root_bits);s.flush_raw();s.assert_accounting(g.summaries[g.root].output_ops,0);assert!(s.capture.is_none()&&s.comparator_capture.is_none());assert!(s.proof.balanced());
 let post_q0=s.output_hist[OperationType::CCX as usize]+s.output_hist[OperationType::CCZ as usize]-s.outer_lowered;
 let conditional_t=512*s.predicate_blocks-s.carry_selected-s.endpoint_blocks-s.endpoint_outer;let expected_2t=2*post_q0-conditional_t;
 assert_eq!(s.input_ops,401952311);assert_eq!(s.proof.rewrites,1790307);assert_eq!(s.one_cleanups,257245);assert_eq!([s.proof.support_dead,s.proof.support_x,s.proof.support_cx],[1625,1415,72669]);
 assert_eq!(s.prefix_rewrites,7421);assert_eq!(s.shared_rewrites,4229758);assert_eq!(s.predicate_blocks,1284);assert!(s.out.is_empty());
 assert_eq!(expected_2t,126439508);assert_eq!(s.output_ops,400660091);assert_eq!(s.family63_counts,[85864,32388]);assert_eq!(s.family36_counts,[115024,19425]);assert_eq!(conditional_t,654836);
 let residual=s.residual_counts.iter().sum::<usize>();let skipped_residual=s.skipped_residual.iter().sum::<usize>();
 assert_eq!(s.final_private_hmr,s.proof.rewrites as usize+s.one_cleanups+residual+s.carry_selected-s.skipped_cleanups as usize-s.skipped_one-skipped_residual-s.comparator.skipped_private_hmr);
 assert_eq!(s.final_private_neg,s.one_cleanups+s.residual_counts[1]+s.carry_selected-s.skipped_one-s.skipped_residual[1]-s.comparator.skipped_private_neg);
 assert_eq!(s.trace,[0x5a945678ac79fd0d,0x7af8b3900bbc1cf0]);assert_eq!(s.proof.diagnostic_fingerprint(),r#"{"sha3_256":"ded6a0ecf7fd66c397794aeb68a2d979059d16a2de7ad347195d165718c19270","next":363804180,"evictions":143,"entries":148690,"cap":1048576}"#);
 println!("family63={:?} fallback={} output_difference={} delta_difference={} family36={:?} motif={:?} motif_saving={} skipped_clean={} skipped_one={} skipped_support={:?}",s.family63_counts,s.family63_counts[0]-s.family63_counts[1],s.output_ops as isize-400692479,s.selected_delta+299825,s.family36_counts,s.selected_counts,s.selected_t_saving,s.skipped_cleanups,s.skipped_one,s.skipped_support);
 println!("baseline_2T=126504284 expected_2T={} net_2T={} post_q0={} conditional_t={} output={} carry=[{},{},{}] endpoint=[{},{}] outer_lowered={} residual={:?} skipped_residual={:?} family24={:?} retention=[{},{},{}] comparator=[{},{},{}] comparator_skipped_private=[{},{}] final_private=[{},{}] delta={} comparator_delta={} trace={:016x}{:016x} fingerprint={}",expected_2t,126504284isize-expected_2t as isize,post_q0,conditional_t,s.output_ops,s.carry_entries,s.carry_zero,s.carry_selected,s.endpoint_blocks,s.endpoint_outer,s.outer_lowered,s.residual_counts,s.skipped_residual,s.family24_counts,s.retention.selected,s.retention.proven,s.retention.fallback,s.comparator.eligible,s.comparator.selected,s.comparator.saving,s.comparator.skipped_private_hmr,s.comparator.skipped_private_neg,s.final_private_hmr,s.final_private_neg,s.selected_delta,s.comparator.delta,s.trace[0],s.trace[1],s.proof.diagnostic_fingerprint());
}
