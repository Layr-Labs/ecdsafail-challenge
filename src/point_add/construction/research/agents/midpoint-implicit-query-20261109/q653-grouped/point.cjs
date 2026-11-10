'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace}=require('../q653-next/parts.cjs');
const file=path.join(__dirname,'../q653-next/point.cjs');
let source=checkedSource(file,'d850d912b5144bcd47227ff187d4118977dbe23665922a34eecefbe78ff74115');
source=replace(source,"m.field=require('./backend.cjs');","m.field=module.groupedField;");
source=replace(source,"m.upper=require('./upper.cjs').upper;","m.upper=module.centeredUpper;");
const entry=new Module(file,module);
entry.filename=file;
entry.paths=Module._nodeModulePaths(path.dirname(file));
entry.groupedField=require('./backend.cjs');
entry.centeredUpper=require('../q653-centerfix/upper.cjs').upper;
entry._compile(source,file);
module.exports=entry.exports;
if(require.main===module){
    const [mode,destination]=process.argv.slice(2);
    if(!['raw','spans'].includes(mode)||!destination||require('node:os').endianness()!=='LE')
        throw Error('Use raw FILE or spans FILE on a little-endian host');
    const writer=new entry.exports.GateWriter(mode==='raw'?destination:null,mode==='spans'?destination:undefined);
    console.log(JSON.stringify(writer.produce(),null,2));
}
