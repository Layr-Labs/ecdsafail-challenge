'use strict';
// Regression entry: the q651 circuit (width 651) with the full q650 upper WIDTH stack (upper never touches logical 651). Usage as q651/point.cjs:
//   node point651s.cjs raw trace.u16le ; node point651s.cjs spans ranges.tsv
// Same fixed configuration as q651/point.cjs, set BEFORE upper651/upper652 are loaded (upper652 reads R35_UBASE at require time).
const here=f=>require('path').join(__dirname,'../../q651',f);
for(const k of ['R35_UPPER','R35_FIELD11','R35_UPATCH','R35_UPPER_GROUPS','R35_UPPER_NARROW','R35_LISTS','G129_MODE','G129_TOP','N653','N653ROOT'])delete process.env[k];
Object.assign(process.env,{R35_WIDTH:'651',R35_FIELD:here('p-field651.js'),R35_REGEN:here('regen/p-regen651.js'),R35_UBASE:here('upper/upper.cjs')});
require('./upper.cjs').install(require('./upper.cjs').WIDTH);
const {GateWriter}=require('../../q651/point.cjs');
module.exports={GateWriter};
if(require.main===module){const [mode,f]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');console.log(JSON.stringify(new GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));}
