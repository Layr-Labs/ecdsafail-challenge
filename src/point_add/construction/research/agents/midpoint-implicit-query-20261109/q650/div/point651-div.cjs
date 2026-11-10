'use strict';
// Regression entry: the 651 configuration with the q650 divide field list (width 651, geometry unchanged).
// Usage (from src/point_add/construction): node research/agents/midpoint-implicit-query-20261109/q650/div/point651-div.cjs raw FILE | spans FILE
const path=require('path');const Q=path.join(__dirname,'../../q651');
for(const k of ['R35_UPPER','R35_FIELD11','R35_UPATCH','R35_UPPER_GROUPS','R35_UPPER_NARROW','R35_LISTS','G129_MODE','G129_TOP','N653','N653ROOT'])delete process.env[k];
Object.assign(process.env,{Q651_ENV:'keep',R35_WIDTH:'651',R35_FIELD:path.join(__dirname,'p-field-div.js'),R35_REGEN:path.join(Q,'regen/p-regen651.js'),R35_UBASE:path.join(Q,'upper/upper.cjs')});
const {GateWriter}=require(path.join(Q,'point.cjs'));
module.exports={GateWriter};
if(require.main===module){const [mode,f]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');console.log(JSON.stringify(new GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));}
