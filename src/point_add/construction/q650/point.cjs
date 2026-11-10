'use strict';
// q650 build entry (width 650), from src/point_add/construction:
//   node q650/point.cjs raw trace.u16le ; node q650/point.cjs spans ranges.tsv
// then the exact peephole (2 passes, W=4096) before hashing/packing:
//   cc -O2 -o tpeep research/agents/midpoint-implicit-query-20261109/q650/tools/tpeep.c
//   ./tpeep trace.u16le ranges.tsv t1.u16le r1.tsv 4096 && ./tpeep t1.u16le r1.tsv trace.final.u16le ranges.final.tsv 4096
//   GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.final.u16le ranges.final.tsv rebuilt
//   bash codec/verify.sh trace.final.u16le rebuilt
// The configuration is fixed here (all stage lists in research/.../q650/stages.cjs); development knobs are cleared.
for(const k of ['Q650_GEOM','Q650_TIGHT','Q650_UPPER_APPLY'])delete process.env[k];
process.env.Q650_GEOM='650';
const {GateWriter}=require('../research/agents/midpoint-implicit-query-20261109/q650/point.cjs');
module.exports={GateWriter};
if(require.main===module){const [mode,f]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');console.log(JSON.stringify(new GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));}
