'use strict';
const path=require('node:path');
const {create650}=require('../research/agents/midpoint-implicit-query-20261109/q650-joined-probes/build650.cjs');
const variant='code-perm-wide-inc-top-host-shared-rotate-history-multiply-physical';
const api=create650(path.join(__dirname,'../donor'),variant);
module.exports=api;
if(require.main===module){
    const [mode,file]=process.argv.slice(2);
    if(!['raw','spans'].includes(mode)||!file||require('node:os').endianness()!=='LE')throw Error('use raw FILE or spans FILE');
    const writer=new api.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined);
    console.log(JSON.stringify(writer.produce(),null,2));
}
