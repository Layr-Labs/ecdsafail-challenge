'use strict';
const path = require('node:path');
const Module = require('node:module');
const {checkedSource} = require('../field128-height-experiment/pinned.cjs');
const {replace} = require('../q653-next/parts.cjs');

// All widths in a group use the same physical nonrestoring division.
// The high divisor cells are zero and can hold the overlaid gcd prefix.
function groupWindingHeights(source) {
    const start = source.indexOf('function outerloadJ(');
    const end = source.indexOf('function mulG(', start);
    if (start < 0 || end <= start) throw Error('Missing Q653 winding stage');
    let body = source.slice(start, end);
    body = replace(body,
        "const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],cls=flagHeight(v,t,e,loan),put=g=>sink('nct',g);",
        `const groups={2:2,64:3,96:65,112:97,120:113,124:121,125:125,126:126,127:127,128:128},lo=groups[t];
         if(lo===undefined)continue;
         const m=v.slice(0,t),a=J.slice(0,t),gap=L[n+1-t],put=g=>sink('nct',g);
         const zero=(word,dest)=>mcN(word,word.map(()=>false),dest,loan);
         const cls=lo===t?flagHeight(v,t,e,loan):zero(v.slice(t),e).concat(zero(v.slice(lo-1),e)),park=[];
         if(lo<t)for(let j=lo;j<=t;j++){
             const stash=v[t+j-lo],tail=v.slice(j,t),test=[e,...tail,stash],match=[true,...tail.map(()=>false),true];
             const cell=j===t?gap:u[j];
             if(stash===undefined)throw Error('No divisor padding for packed gcd');
             park.push([cell,stash],...mcN(test,match,cell,loan),[cell,stash]);
         }`);
    body = replace(body, 'put(cls);if(t===2)', 'put(cls);put(park);if(t===2)');
    body = replace(body, 'neg();cond();neg();cond();put([...cls].reverse());',
        'neg();cond();neg();cond();put(park.slice().reverse());put([...cls].reverse());');
    return source.slice(0,start) + body + source.slice(end);
}

const filename=path.join(__dirname,'../q653-next/backend.cjs');
const original=checkedSource(filename,'7672c89cb5628dc9aa613ad3844bca1d5bd78da23a8dec1c075b9e0f6f69c695');
const modified=replace(original,'const divide=Function(','d=module.groupWindingHeights(d);\nconst divide=Function(');
const builder=new Module(filename,module);
builder.filename=filename;
builder.paths=Module._nodeModulePaths(path.dirname(filename));
builder.groupWindingHeights=groupWindingHeights;
builder._compile(modified,filename);
module.exports=builder.exports;
