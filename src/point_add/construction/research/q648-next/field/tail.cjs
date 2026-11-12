'use strict';

const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const fs = require('node:fs');
const Module = require('node:module');
const path = require('node:path');

function replaceOnce(source, before, after) {
    assert.equal(source.split(before).length, 2, before);
    return source.replace(before, after);
}

// Crossing the short prefix supplies one clean low divisor bit per borrowed
// tag. Use a single long suffix as soon as its complete offset fits.
function cover(m,real,depth) {
    const capacity=kind=>2**(real+kind+1);
    const fits=(len,kind)=>len<=capacity(kind);
    const kindAt=base=>Math.max(0,Math.min(depth,base-1));
    const need=len=>Math.max(0,Math.ceil(Math.log2(len))-real-1);
    let tail=0;
    while(tail<m&&!fits(m-tail,kindAt(tail)))++tail;
    const spots=[];
    let base=0;
    while(base<m) {
        const kind=kindAt(base);
        const width=base<tail?Math.min(capacity(kind),tail-base):Math.min(capacity(kind),m-base);
        spots.push({base,width,kind:Math.min(kind,need(width))});
        base+=width;
    }
    return spots;
}

function sourceFor(source) {
    let s=replaceOnce(source, 'const depth=roles.length,low=',
        'const depth=Math.min(roles.length,tuning.depth(this,m,k,realCount)),low=');
    s=replaceOnce(s, 'wide=1<<full.length', 'wide=1<<(realCount+depth+1)');
    const partition=s.match(/  for\(let j=1;j<depth;[^\n]+/);
    assert(partition,'original height partition');
    s=replaceOnce(s,partition[0],`  if(tuning.tail){
      sectors.splice(0,sectors.length,...tuning.cover(m,realCount,depth));
    }else if(tuning.pack){
      for(let base=low;base<m;){
        const kind=Math.min(depth,base-1),width=1<<(realCount+kind+1);
        sectors.push({base,width,kind});base+=width;
      }
    }else{`+partition[0]+'}');
    const head='const rot=(ar,w,ct,dir,base=0)=>{const tg=tag;';
    s=replaceOnce(s,head,`const rotateTag=(ct,tg,j,word,shift,cache)=>{
      const bit=tg[j];
      if(tuning.simple && full.slice(0,Math.min(realCount,2)).includes(bit)){
        this.rot([bit],word,shift);return;
      }
      if(tuning.cache && cache){
        this.op(ct.concat(bit),this.tst);
        this.rot([this.tst],word,shift);
        this.op(ct.concat(bit),this.tst);
        return;
      }
      this.rot(ct.concat(bit),word,shift);
    };
    const rot=(ar,w,ct,dir,base=0)=>{const tg=tag,plain=sector.kind===0,maximum=tuning.shortTags?sector.hi-base:Infinity;`);
    s=replaceOnce(s,'if(s>=w.length)break;one(ar,',
        'if(s>=w.length||s>maximum)break;one(ar,');
    s=replaceOnce(s,'this.rot(ct.concat(tg[j]),w,dir*s)',
        'rotateTag(ct,tg,j,w,dir*s,plain)');
    s=replaceOnce(s,'const norm=(ar,w,ct,base,dual)=>{const tg=tag;',
        'const norm=(ar,w,ct,base,dual)=>{const tg=tag,plain=sector.kind===0,maximum=tuning.shortTags?sector.hi-base:Infinity;');
    s=replaceOnce(s,'if(base)one(ar,()=>this.rot(ct,w,base));','if(base)one(ar,()=>this.rot(tuning.conjugate?[]:ct,w,base));');
    s=replaceOnce(s,'if(s>=w.length)continue;one(ar,','if(s>=w.length||s>maximum)continue;one(ar,');
    s=replaceOnce(s,'this.rot(ct.concat(tg[j]),dual?w.slice(base):w,s)',
        'if(tuning.conjugate)this.rot([tg[j]],dual?w.slice(base):w,s);else rotateTag(ct,tg,j,dual?w.slice(base):w,s,plain||j===tg.length-1)');
    s=replaceOnce(s,'if(i>=base&&i<=hi)this.multag(c,i-base,[],this.tst);',
        `if(i>=base&&i<=hi){const saved=this.tag;
        if(tuning.shortTags)this.tag=tg.slice(0,Math.ceil(Math.log2(hi-base+1)));
        this.multag(c,i-base,[],this.tst);this.tag=saved;}`);
    return s;
}

const installs=new Map();
function install(fieldDir,options={}) {
    const root=path.resolve(fieldDir), id=require.resolve(path.join(root,'relay-source.cjs'));
    const prior=installs.get(id);
    if(prior) {assert.equal(prior,options.key??'normal');return;}
    assert(!require.cache[require.resolve(path.join(root,'walks.cjs'))], 'Install before Q648 field walks');
    const original=fs.readFileSync(id,'utf8');
    assert.equal(crypto.createHash('sha256').update(original).digest('hex'),
        '2ddaa7bcd13c0f2d49f6e6538674c9ff803cf892c3271c5efb50bc8f8654d811');
    const tuning={
        depth:options.depth??(()=>7),simple:options.simple??true,cache:options.cache??true,
        pack:options.pack??true,tail:options.tail??true,shortTags:options.shortTags??true,
        conjugate:options.conjugate??true,cover
    };
    const carrier=new Module(id,module);
    carrier.filename=id; carrier.paths=module.paths;
    Function('module','realCount','tuning',sourceFor(original))(carrier,0,tuning);
    carrier.loaded=true; require.cache[id]=carrier;
    const gradedId=require.resolve(path.join(root,'graded-relay.cjs'));
    const graded=new Module(gradedId,module); graded.filename=gradedId;
    graded.paths=Module._nodeModulePaths(root);
    graded.transform=sourceFor; graded.tuning=tuning;
    const transformed=replaceOnce(fs.readFileSync(gradedId,'utf8'),
        "Function('module','realCount',s)(m,realCount);",
        "Function('module','realCount','tuning',module.transform(s))(m,realCount,module.tuning);");
    graded._compile(transformed,gradedId);graded.loaded=true;require.cache[gradedId]=graded;
    installs.set(id,options.key??'normal');
}

module.exports={install,cover};
