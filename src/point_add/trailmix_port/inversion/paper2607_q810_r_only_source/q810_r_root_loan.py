#!/usr/bin/env python3
"""gpt-5: source-only Q810 R root-loan component.

This is not a complete baseline generator. Pass an independently authenticated
portable baseline source/support/mature/R-module/T-sub-module to install().
Only the R emission hook is replaced. T-sub is never wrapped or reassigned.
The unchanged caller must establish the qualified R accumulator/root promise;
the five-gate identity alone does not establish that caller contract.
"""
from collections import Counter
from contextlib import contextmanager
import functools
from types import FunctionType, SimpleNamespace



NAME = 'ROOT_LOAN_C3X_EXACT_V1'
DEFINITION = (('x', (4,)), ('ccx', (1, 2, 4)), ('ccx', (0, 4, 3)),
              ('ccx', (1, 2, 4)), ('x', (4,)))

def make_gate(support):
    reg = support.QuantumRegister(5, 'RootLoan')
    circuit = support.QuantumCircuit(reg, name=NAME)
    for kind, slots in DEFINITION:
        getattr(circuit, kind)(*[reg[i] for i in slots])
    return circuit.to_gate(label=NAME)

def checked_span(item, root, forbidden):
    """Return exact formal roles; never grant a general protected-wire waiver."""
    gate, wires = item.operation, tuple(item.qubits)
    assert gate.name == NAME and gate.num_qubits == 5
    assert not item.clbits and gate.num_clbits == 0
    assert not gate.params and getattr(gate, 'condition', None) is None
    assert len(wires) == len(set(wires)) == 5 and wires[4] == root
    assert set(wires) & forbidden == {root}
    definition = gate.definition
    assert definition is not None and definition.num_qubits == 5
    assert not definition.clbits and not definition.num_clbits
    assert getattr(definition, 'global_phase', 0) == 0
    assert len(definition.data) == 5
    ids = {q: i for i, q in enumerate(definition.qubits)}
    actual = []
    for inner in definition.data:
        op = inner.operation
        assert not inner.clbits and op.num_clbits == 0
        assert op.definition is None and not op.params
        assert getattr(op, 'condition', None) is None
        slots = tuple(ids[q] for q in inner.qubits)
        assert len(set(slots)) == len(slots)
        assert op.num_qubits == len(slots)
        actual.append((op.name, slots))
    assert tuple(actual) == DEFINITION
    return wires

identity = SimpleNamespace(make_gate=make_gate, checked_span=checked_span)

def build(source, support, original, before, after, kwargs):
    assert getattr(original, '_fixed_low0_frame', False)
    assert getattr(original, '_coefficient0_quotient_capture', False)
    assert getattr(original, '_terminal_activation_capture', False)
    frame_literal = original.__globals__['_terminal_literal']
    events = []

    def observe(circuit, controls, target, *, source, low, low_mask, step, remainder, lenders):
        start = len(circuit.data)
        frame_literal(circuit, controls, target, source=source, low=low, low_mask=low_mask, step=step, remainder=remainder, lenders=lenders)
        events.append(dict(start=start, end=len(circuit.data),
                           wires=tuple(controls) + (target,),
                           mask=low_mask, step=step))

    observed = FunctionType(original.__code__,
        dict(original.__globals__, _terminal_literal=observe), original.__name__,
        original.__defaults__, original.__closure__)
    observed.__kwdefaults__ = original.__kwdefaults__
    statistics = observed(source, before, **kwargs)
    root, acc, borrowed = kwargs['low'][0], kwargs['accumulator'], kwargs['dirty'][0]
    lower, upper = kwargs['lower'], kwargs['upper']
    assert len({root, acc, borrowed}) == 3
    matches = {}
    per_position = Counter()
    for index in range(len(events) - 3):
        batch = events[index:index + 4]
        if not all(event['end'] == event['start'] + 1 for event in batch):
            continue
        if any(left['end'] != right['start'] for left, right in zip(batch, batch[1:])):
            continue
        one, two, three, four = [event['wires'] for event in batch]
        if not (len(one) == len(two) == 3 and one == three and two == four):
            continue
        if one[0] != acc or one[2] != borrowed or two[0] != borrowed:
            continue
        carry, target, addend = one[1], two[1], two[2]
        positions = [j for j in range(lower, upper)
            if (addend, target, carry) == (kwargs['work2'][j - 1],
                kwargs['work1'][j - 1], kwargs['work2'][j])]
        assert len(positions) == 1, 'unexpected acc-controlled R C3X arithmetic ABI'
        j, = positions
        wires = (acc, carry, target, addend, root)
        assert len(set(wires)) == 5 and borrowed not in wires
        start, stop = batch[0]['start'], batch[-1]['end']
        assert stop - start == 4 and start not in matches
        expected = [one, two, three, four]
        for item, expected_wires in zip(before.data[start:stop], expected):
            assert item.operation.name == 'ccx' and item.operation.definition is None
            assert not item.clbits and tuple(item.qubits) == expected_wires
        assert len({(event['step'], event['mask']) for event in batch}) == 1
        matches[start] = dict(stop=stop, position=j, wires=wires,
                              logical_low_mask=batch[0]['mask'])
        per_position[j] += 1
    assert per_position == {j: 2 for j in range(lower, upper)}, per_position
    gate = identity.make_gate(support)
    index = 0
    spans = []
    while index < len(before.data):
        if index in matches:
            match = matches[index]
            start = len(after.data)
            after.append(gate, match['wires'])
            identity.checked_span(after.data[-1], root, {root})
            spans.append(dict(original_start=index, original_stop=match['stop'],
                candidate_index=start, source_position=match['position'],
                logical_low_mask=match['logical_low_mask'],
                physical_slots=[after.find_bit(q).index for q in match['wires']]))
            index = match['stop']
        else:
            item = before.data[index]
            assert not item.clbits
            after.append(item.operation, list(item.qubits))
            index += 1
    assert len(spans) == 2 * (upper - lower)
    assert original.__globals__['_terminal_literal'] is frame_literal
    return dict(original_statistics=statistics, span_count=len(spans), spans=spans,
                observer_events=len(events), original_guards_executed_unchanged=True,
                all_endpoint_and_mode_sign_cells_unchanged=True)

r_candidate = SimpleNamespace(build=build)

LAST = {}
_ACTIVE = False

@contextmanager
def install(source, support, mature, rblock, tsub_body, step):
    """Use only the R replacement inside an already-loaded baseline process.

    The owner authenticates the baseline before calling. This API deliberately
    performs no filesystem lookup, old receipt import, implicit source load,
    generation, scheduling, allocation or publication.
    """
    global _ACTIVE
    assert not _ACTIVE and type(step) is int and 1 <= step <= 1616
    original_r = rblock.emit_fused
    original_tsub = tsub_body._EMIT_PREFIX
    original_builder = source.build_step_circuit
    LAST.clear()
    LAST.update(step=step, r=[])

    @functools.wraps(original_r)
    def r(source_arg, circuit, **kwargs):
        assert source_arg is source and kwargs['step'] == step
        assert circuit.num_qubits == 564 and not LAST['r']
        entry = len(circuit.data)
        after = support.QuantumCircuit(*circuit.qregs)
        changes = r_candidate.build(source, support, original_r, circuit, after, kwargs)
        prior_length = len(circuit.data)
        intervals = [(row['original_start'], row['original_stop']) for row in changes['spans']]
        assert all(entry <= a < b <= prior_length for a, b in intervals)

        def relocated(position):
            assert not any(a < position < b for a, b in intervals)
            return position - 3 * sum(b <= position for _, b in intervals)

        # The original capture markers refer to this same circuit. Preserve
        # their meaning after four primitive items become one exact gate item.
        relocated_marks = []
        for mark in mature.terminal.LAST_SPANS:
            if mark['circuit'] == id(circuit) and mark['step'] == step:
                old_position = mark['start']
                mark['start'] = relocated(old_position)
                relocated_marks.append(dict(label=mark['label'], before=old_position, after=mark['start']))
        assert len(after.data) == prior_length - 3 * len(intervals)
        circuit.data[:] = after.data
        LAST['r'].append(dict(entry=entry, exit=len(circuit.data),
            accumulator=circuit.find_bit(kwargs['accumulator']).index,
            root=circuit.find_bit(kwargs['low'][0]).index,
            iteration=circuit.find_bit(kwargs['iteration']).index,
            relocated_capture_marks=relocated_marks, changes=changes))
        return changes['original_statistics']

    _ACTIVE = True
    rblock.emit_fused = r
    try:
        mature.check_r_hooks()
        yield LAST
        assert len(LAST['r']) == 1
        assert source.build_step_circuit is original_builder
        assert rblock.emit_fused is r
        assert tsub_body._EMIT_PREFIX is original_tsub
        for span in mature.LAST_TSUB_SPANS:
            if span['replaced']:
                assert span['all_original_source_callbacks_unchanged'] is True
        mature.check_r_hooks()
    finally:
        rblock.emit_fused = original_r
        _ACTIVE = False
        assert source.build_step_circuit is original_builder
        assert tsub_body._EMIT_PREFIX is original_tsub
        mature.check_r_hooks()
