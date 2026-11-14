'use strict';
// h1: nasqret's verbatim physical compilers (q651-gate-reduction, q651-upper-reduction,
// q651-parity-fusion, q651-product-cache) with their search bounds exposed, plus a
// whole-tape version of the 76c5c6cc commute filter. Bounds are opportunity limits
// only (block sizes, look-back windows, scan lengths); every rewrite passes the same
// exactness checks. 1af84e41/5c8969de constants: kb128 kw24 ub128 uw32 fl512 fs192
// fm5 cw256 aw16. Typed-array limits: fl*(2*fm+1)+8 < 65536 (fusion Uint16 links),
// cw <= 32767 (cache Int16 indices).
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
const env=(k,d)=>process.env[k]===undefined?d:+process.env[k];
const P={kb:env('H1_KB',4096),kw:env('H1_KW',768),ub:env('H1_UB',4096),uw:env('H1_UW',768),
    gb:env('H1_GB',4096),gw:env('H1_GW',768),fl:env('H1_FL',4096),fs:env('H1_FS',4096),fm:env('H1_FM',6),
    cw:env('H1_CW',16384),aw:env('H1_AW',512)};
if(P.fl*(2*P.fm+1)+8>=65536||P.cw>32767)throw Error('h1 compiler bounds exceed typed-array capacity');
const R=path.join(__dirname,'..');
function load(rel,edits,extra={}){
    const file=path.join(R,rel);let s=fs.readFileSync(file,'utf8');
    for(const [a,b] of edits){if(s.split(a).length!==2)throw Error('h1 param anchor '+rel+' '+a);s=s.replace(a,()=>b);}
    const m=new Module(file,module);m.filename=file;m.paths=Module._nodeModulePaths(path.dirname(file));Object.assign(m,extra);m._compile(s,file);return m.exports;
}
const affine=load('q651-gate-reduction/affine.cjs',[['function reduceAffine(words,window=16){','function reduceAffine(words,window='+P.aw+'){']]);
const commute=load('q651-gate-reduction/commute.cjs',[["const {reduceAffine}=require('./affine.cjs');","const {reduceAffine}=module.h1affine;"]],{h1affine:affine});
const fusion=load('q651-parity-fusion/fusion.cjs',[['const N=1023,LIMIT=512,SCAN=192,MAX_FAN=5;','const N=1023,LIMIT='+P.fl+',SCAN='+P.fs+',MAX_FAN='+P.fm+';']]);
const cache=load('q651-product-cache/cache.cjs',[['const N=1023,WINDOW=256;','const N=1023,WINDOW='+P.cw+';']]);
function filterOn(output,limit,win,names){
    const {optimizeBlock,record,N}=commute,pending=[],raw=output.out.bind(output);
    function flush(){
        if(!pending.length)return;
        const out=[];optimizeBlock(pending,out,win);pending.length=0;
        for(const g of out){const a=g>>>20,b=g>>>10&1023,t=g&1023;if(b===N)raw(N,a,t);else raw(a,b,t);}
    }
    return {flush,put:(a,b,t)=>{pending.push(record(a,b,t));if(pending.length===limit)flush();}};
}
// Same interface as q651-upper-reduction/pass.cjs upperFilter, with bounds ub/uw.
function upperFilter(output){
    const f=filterOn(output,P.ub,P.uw);
    return {out:f.put,flush:f.flush,
        cond(bit,fn){f.flush();return output.cond(bit,()=>{fn();f.flush();});},
        hmr(q){f.flush();return output.hmr(q);},z(q){f.flush();return output.z(q);}};
}
// Whole point tape: every quantum, phase, measurement, classical-control and condition
// boundary flushes the pending NCT block first, exactly like the cache and fusion installs.
function installGlobal(tape){
    const f=filterOn(tape,P.gb,P.gw);
    for(const name of ['hmr','z','cz','classical'])if(tape[name]){
        const g=tape[name].bind(tape);tape[name]=(...args)=>{f.flush();return g(...args);};
    }
    const cond=tape.cond.bind(tape);tape.cond=(bit,fn)=>{f.flush();return cond(bit,()=>{fn();f.flush();});};
    tape.out=f.put;return f.flush;
}
function optimizeStream(emit,sink){return commute.optimizeStream(emit,sink,{block:P.kb,window:P.kw});}
module.exports={P,upperFilter,installGlobal,optimizeStream,cache,fusion};
