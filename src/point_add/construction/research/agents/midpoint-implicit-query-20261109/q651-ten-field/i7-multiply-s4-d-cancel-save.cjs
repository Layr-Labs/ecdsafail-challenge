'use strict';
// Complete eight-helper D14 divider; native644/645 absent.
const fs=require('fs'),path=require('path'),Module=require('module');
const root=process.env.D14_Q651_ROOT||process.env.D5_Q651_ROOT||process.env.D3_Q651_ROOT||__dirname;
function build(pub){
 const published=require(path.join(root,'public-backend.cjs'));pub=pub||published;
 const raw=published.withDigit(require('./i7-multiply-d14-alternating-digit.cjs').alternatingDigit);
 const local={...raw,emitWalk:require('./i7-multiply-s4-d-walk-emitter.cjs').wrap(raw)};
 const file=path.join(root,'divide.cjs');let source=fs.readFileSync(file,'utf8');
 const anchor='const divide=Function(';if(source.split(anchor).length!==2)throw Error('D10 divide build anchor');
 source=source.replace(anchor,'d=module.d10patch(d);'+anchor);
 const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));
 m.d10patch=s=>require('./i7-multiply-d14-p-d14-all.cjs')(s);m._compile(source,file);
 const base=m.exports.build(local);
 return {...base,emitMultiplySparse:pub.emitMultiplySparse,emitDivideSparse(sink,tap){
  const p=require('./i7-multiply-s4-sink.cjs').wrapSparse(sink,{mode:'commute',window:4096});
  base.emitDivideSparse(p.sink,tap);p.flush();
 }};
}
module.exports={build,status:'FREED native644/645; eight divide helpers',wholeStageFreed:true};
