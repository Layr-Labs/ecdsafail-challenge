'use strict';

const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const Module=require('node:module');

// For a physical gate whose target is absent from every virtual polynomial,
// the published lowerer emits the original gate and updates no polynomial.
// A cached union avoids constructing a polynomial product on that path.
function install(owner) {
    const id=require.resolve(path.join(owner,'i9-multiply-m9-encoded-lowerer.cjs'));
    let s=fs.readFileSync(id,'utf8');
    const edit=(a,b)=>{assert.equal(s.split(a).length,2,'Q647 lowerer '+a);s=s.replace(a,()=>b);};
    edit('function output(p,z){',`const flags=Array.from({length:1024},(_,q)=>1n<<BigInt(q));
 let watched=0n;const refresh=()=>{watched=0n;for(const u of unions.values())watched|=u;};refresh();
 function output(p,z){`);
    edit('a=map(a);b=map(b);t=map(t);gates++;const cs=',`a=map(a);b=map(b);t=map(t);gates++;
  if(!E.has(t)&&!E.has(a)&&!E.has(b)&&!(watched&flags[t])){emit(a,b,t);emitted++;return;}
  const cs=`);
    edit('unions.set(t,vars(p));','unions.set(t,vars(p));refresh();');
    edit('unions.set(q,vars(next));','unions.set(q,vars(next));refresh();');
    const m=new Module(id,module);m.filename=id;m.paths=Module._nodeModulePaths(owner);m._compile(s,id);
    require.cache[id]=m;
}

module.exports={install};
