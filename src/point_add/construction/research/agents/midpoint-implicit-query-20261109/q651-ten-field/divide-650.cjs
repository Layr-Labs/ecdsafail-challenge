'use strict';
// Complete D5 nine-helper divide. Native/physical645 is absent throughout.
// The point integrator may compact its remaining physical650 into the 645 hole.
const fs=require('fs'),path=require('path'),Module=require('module');
const root=process.env.D5_Q651_ROOT||process.env.D3_Q651_ROOT||__dirname;
function build(pub){
 const published=require(path.join(root,'public-backend.cjs'));pub=pub||published;
 const local=published.withDigit(require('./alternating-digit.cjs').alternatingDigit);
 const file=path.join(root,'divide.cjs');let source=fs.readFileSync(file,'utf8');
 const anchor='const divide=Function(';if(source.split(anchor).length!==2)throw Error('D3 divide build anchor');
 source=source.replace(anchor,'d=module.d3patch(d);'+anchor);
 const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));m.d3patch=require('./p-d5.cjs');m._compile(source,file);
 return {...m.exports.build(local),emitMultiplySparse:pub.emitMultiplySparse};
}
module.exports={build,status:'FREED',wholeStageFreed:true};
