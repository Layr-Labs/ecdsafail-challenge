'use strict';
// U37 extension, applied once after its U29 overlay, before allocator/S3/sole sink.
exports.upper=s=>require('./i9-upper-u41-esop.cjs').upper(require('./i9-upper-u41-prefix-122.cjs').upper(require('./i9-upper-u41-probes.cjs').upper(s)));
exports.select=w=>w.kind==='signProbe'&&((w.k<=111&&!w.back&&w.args[0]===644)||((w.k===114&&w.args[0]===644)||(w.k>=115&&w.k<=124)))?{evict:643,reason:'U41 fixed-position coefficient/rank code; carry clean at boundaries'}:null;
exports.wholeStageFreed=false;
