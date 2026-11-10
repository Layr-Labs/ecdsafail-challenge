'use strict';
// Convenience entry from the construction directory.
const {GateWriter}=require('../research/agents/midpoint-implicit-query-20261109/q650-joined-probes/point-increment.cjs');
module.exports={GateWriter};
if(require.main===module){const [mode,f]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!f||require('os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');console.log(JSON.stringify(new GateWriter(mode==='raw'?f:null,mode==='spans'?f:undefined).produce(),null,2));}
