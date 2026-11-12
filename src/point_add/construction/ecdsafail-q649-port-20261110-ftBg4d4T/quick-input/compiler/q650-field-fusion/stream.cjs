'use strict';

const path = require('path');

// A lower field walk emits reversible gate batches, interspersed with
// measurement, phase and control events. Every such event ends the window.
function fuseStream(emit, sink, engine, record) {
    const none = 1023;
    let output = [];
    function drain() {
        if (output.length) sink('packed', output);
        output = [];
    }
    const fusion = engine((a, b, target) => {
        output.push(record(a, b, target));
        if (output.length === 65536) drain();
    });
    emit((kind, data) => {
        if (kind === 'packed') {
            for (const gate of data) {
                fusion.put(gate >>> 20, (gate >>> 10) & none, gate & none);
            }
        } else if (kind === 'nct') {
            for (const gate of data) {
                const a = gate.length === 1 ? none : gate[0];
                const b = gate.length === 3 ? gate[1] : none;
                fusion.put(a, b, gate[gate.length - 1]);
            }
        } else {
            fusion.flush();
            drain();
            sink(kind, data);
        }
    });
    fusion.flush();
    drain();
    return fusion.stats;
}

function install(agentRoot) {
    const gatePass = require.resolve(path.join(agentRoot, 'q651-gate-reduction/commute.cjs'));
    const base = require(gatePass);
    const {engine} = require(path.join(agentRoot, 'q651-parity-fusion/fusion.cjs'));
    const totals = {calls: 0, pairs: 0, cancelled: 0};
    require.cache[gatePass].exports = {
        ...base,
        optimizeStream(emit, sink, options) {
            const stats = fuseStream(
                visitor => base.optimizeStream(emit, visitor, options),
                sink, engine, base.record
            );
            totals.calls++;
            totals.pairs += stats.pairs;
            totals.cancelled += stats.cancelled;
        }
    };
    return totals;
}

module.exports = {fuseStream, install};
