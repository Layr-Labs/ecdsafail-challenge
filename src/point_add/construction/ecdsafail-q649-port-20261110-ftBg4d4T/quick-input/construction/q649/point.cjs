'use strict';
const api=require('../research/agents/midpoint-implicit-query-20261109/q651-ten-field/point-i.cjs');
module.exports=api;
if(require.main===module){const [mode,file]=process.argv.slice(2);if(!['raw','spans'].includes(mode)||!file)throw Error('Use raw FILE or spans FILE');console.log(JSON.stringify(new api.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));}
