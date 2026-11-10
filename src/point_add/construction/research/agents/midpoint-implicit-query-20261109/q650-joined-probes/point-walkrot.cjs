'use strict';
const path=require('node:path');
require('./field-rotate.cjs').install(path.join(__dirname,'../q651-ten-field'));
const api=require('./point-increment.cjs');module.exports=api;
if(require.main===module){
    const [mode,file]=process.argv.slice(2);
    if(!['raw','spans'].includes(mode)||!file)throw Error('use raw FILE or spans FILE');
    console.log(JSON.stringify(new api.GateWriter(mode==='raw'?file:null,mode==='spans'?file:undefined).produce(),null,2));
}
