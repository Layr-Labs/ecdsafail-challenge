'use strict';
// Integration entry: still TEN physical helpers. Never label this Q650.
// Install beside n651a divide.cjs with p-candidate/p-tail/p-walks and
// alternating-digit.cjs. R38_Q651_ROOT is only a local test override.
const fs=require('fs'),path=require('path'),Module=require('module');
const root=process.env.R38_Q651_ROOT||__dirname;
function build(pub){
 const published=require(path.join(root,'public-backend.cjs'));pub=pub||published;
 const local=published.withDigit(require('./alternating-digit.cjs').alternatingDigit);
 const file=path.join(root,'divide.cjs');let source=fs.readFileSync(file,'utf8');
 const anchor='const divide=Function(';if(source.split(anchor).length!==2)throw Error('R38 divide build anchor');
 source=source.replace(anchor,'d=module.r38patch(d);'+anchor);
 const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));m.r38patch=require('./p-candidate.cjs');m._compile(source,file);
 return {...m.exports.build(local),emitMultiplySparse:pub.emitMultiplySparse};
}
module.exports={build};
