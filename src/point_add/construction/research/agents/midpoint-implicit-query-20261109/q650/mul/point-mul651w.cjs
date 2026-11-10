'use strict';
// Regression entry: the 651 circuit (width 651, 651 geometry) with only short.multiply replaced by q650/mul.
// Usage (from src/point_add/construction): node research/agents/midpoint-implicit-query-20261109/q650/mul/point-mul651w.cjs raw|spans FILE
const path=require('path'),here=f=>path.join(__dirname,f),q651=f=>path.join(__dirname,'../../q651',f);
for(const k of ['R35_UPPER','R35_FIELD11','R35_UPATCH','R35_UPPER_GROUPS','R35_UPPER_NARROW','R35_LISTS','G129_MODE','G129_TOP','N653','N653ROOT'])delete process.env[k];
Object.assign(process.env,{Q651_ENV:'keep',R35_WIDTH:'651',R35_FIELD:here('p-field-mul650.js'),R35_REGEN:q651('regen/p-regen651.js'),R35_UBASE:q651('upper/upper.cjs')});
const {GateWriter}=require(q651('point.cjs'));
module.exports={GateWriter};
if(require.main===module){const [mode,f]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');console.log(JSON.stringify(new GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));}
