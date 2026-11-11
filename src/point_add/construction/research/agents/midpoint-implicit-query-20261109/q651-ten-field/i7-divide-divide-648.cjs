'use strict';
// D19: D18 dual relay walks composed with D17 complete count2 transport.
const fs=require('fs'),path=require('path'),Module=require('module');
const root=process.env.D19_Q651_ROOT||process.env.D17_Q651_ROOT||process.env.D16_Q651_ROOT||process.env.D14_Q651_ROOT||process.env.D5_Q651_ROOT||process.env.D3_Q651_ROOT||__dirname;
function build(pub){
 const published=require(path.join(root,'public-backend.cjs'));pub=pub||published;
 const raw=published.withDigit(require('./i7-divide-alternating-digit.cjs').alternatingDigit);
 const local={...raw,emitWalk:require('./i7-divide-walk-emitter.cjs').wrap(raw)};
 const file=path.join(root,'divide.cjs');let source=fs.readFileSync(file,'utf8');
 const anchor='const divide=Function(';if(source.split(anchor).length!==2)throw Error('D10 divide build anchor');
 source=source.replace(anchor,'d=module.d10patch(d);'+anchor);
 const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));
 m.d10patch=s=>{s=require('./i7-divide-p-partial.cjs')(require('./i7-divide-p-d14-all.cjs')(s));for(const f of ['./i7-divide-d17-p-alpha.cjs','./i7-divide-d17-p-middle.cjs','./i7-divide-d17-p-winding.cjs','./i7-divide-d17-p-tail.cjs'])s=require(f)(s);return require('./i7-divide-p-d18-walks.cjs')(s);};m._compile(source,file);
 const base=m.exports.build(local);
 return {...base,emitMultiplySparse:pub.emitMultiplySparse,emitDivideSparse(sink,tap){
  const p=require('./i7-divide-final-sink.cjs').wrapSparse(sink,{mode:'commute',window:4096});
  base.emitDivideSparse((kind,data)=>{const check=q=>{if([643,644,645,648].includes(q))throw Error('D19 forbidden ABI wire '+q);};if(kind==='packed')for(const x of data){check(x>>>20&1023);check(x>>>10&1023);check(x&1023);}else if(kind==='nct')for(const r of data)r.forEach(check);else data.slice(0,-1).forEach(check);p.sink(kind,data);},tap);p.flush();
 }};
}
module.exports={build,status:'FREED native643/644/645; complete seven-helper divide',wholeStageFreed:true,helpers:[640,641,642,646,647,649,650],physicalHelpers:[512,641,642,643,644,645,646],signPassenger:647};
