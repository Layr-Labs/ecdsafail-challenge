'use strict';
// D22 partial: seven-tag multi-relay walks; count0 delayed to alpha121. Seven helpers overall.
const fs=require('fs'),path=require('path'),Module=require('module');
const root=process.env.D20_Q651_ROOT||process.env.D19_Q651_ROOT||process.env.D17_Q651_ROOT||process.env.D16_Q651_ROOT||process.env.D14_Q651_ROOT||process.env.D5_Q651_ROOT||process.env.D3_Q651_ROOT||__dirname;
function build(pub,options={}){
 const published=require(path.join(root,'public-backend.cjs'));pub=pub||published;
 const raw=published.withDigit(require('./i9-divide-alternating-digit.cjs').alternatingDigit);
 const inner=options.inner||require('./i9-divide-inner-d23.cjs');
 const standard=require('./i9-divide-walk-emitter.cjs').wrap(raw);
 const local={...raw,emitWalk(w,L,R,ws,dirty,back,sink){return ws.aux===-1&&!back?inner.emit(raw,w,L,R,ws,dirty,back,sink):standard(w,L,R,ws,dirty,back,sink);}};
 const file=path.join(root,'divide.cjs');let source=fs.readFileSync(file,'utf8');
 const anchor='const divide=Function(';if(source.split(anchor).length!==2)throw Error('D10 divide build anchor');
 source=source.replace(anchor,'d=module.d10patch(d);'+anchor);
 const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));
 m.d10patch=s=>{s=require('./i9-divide-p-partial.cjs')(require('./i9-divide-p-d14-all.cjs')(s));for(const f of ['./i9-divide-d17-p-alpha.cjs','./i9-divide-d17-p-middle.cjs','./i9-divide-d17-p-winding.cjs','./i9-divide-d17-p-tail.cjs'])s=require(f)(s);s=require('./i9-divide-p-d22-alpha-delay.cjs')(require('./i9-divide-p-d21-recovery.cjs')(require('./i9-divide-p-d21-qsplit.cjs')(require('./i9-divide-p-d21-tail-echo.cjs')(require('./i9-divide-p-tail-shared.cjs')(require('./i9-divide-p-prefix.cjs')(require('./i9-divide-p-d18-walks.cjs')(s)))))));s=require('./i9-divide-p-d24-outside.cjs')(s);s=require('./i9-divide-p-d26-parking.cjs')(s);s=require('./i9-divide-p-d26-outer.cjs')(s);if(options.d25){if(typeof options.d25.applySource!=='function')throw Error('D26_D25_INTERFACE');s=options.d25.applySource(s);}if(inner.tags!==7)s=s.replace('new SectorCanonical(n,7)','new SectorCanonical(n,'+inner.tags+')');return s;};m._compile(source,file);
 const base=m.exports.build(local);
 return {...base,emitMultiplySparse:pub.emitMultiplySparse,emitDivideSparse(sink,tap){
  const p=require('./i9-divide-final-sink.cjs').wrapSparse(sink,{mode:'commute',window:4096});
  base.emitDivideSparse((kind,data)=>{const check=q=>{if([643,644,645,648].includes(q))throw Error('D19 forbidden ABI wire '+q);};if(kind==='packed')for(const x of data){check(x>>>20&1023);check(x>>>10&1023);check(x&1023);}else if(kind==='nct')for(const r of data)r.forEach(check);else data.slice(0,-1).forEach(check);p.sink(kind,data);},tap);p.flush();
 }};
}
module.exports={build,status:'OPEN D26: D23 inner and Q126 parking port; count0/count1 boundary host still641 absent D25',wholeStageFreed:false,helpers:[640,641,642,646,647,649,650],physicalHelpers:[512,641,642,643,644,645,646],signPassenger:647};
