'use strict';

const assert=require('node:assert/strict');
const fs=require('node:fs');
const Module=require('node:module');
const path=require('node:path');

function one(source,from,to) {
    assert.equal(source.split(from).length,2,from);
    return source.replace(from,()=>to);
}

function hosted(source) {
    let s=one(source,'if(s>=w.length)break;one(ar,','if(s>=w.length||s>sector.hi-base)break;one(ar,');
    s=one(s,'if(base)one(ar,()=>this.rot(ct,w,base));','if(base)one(ar,()=>this.rot([],w,base));');
    s=one(s,'if(s>=w.length)continue;one(ar,','if(s>=w.length||s>sector.hi-base)continue;one(ar,');
    s=one(s,'this.rot(ct.concat(tg[j]),base>0?w.slice(base):w,s)',
        'this.rot([tg[j]],base>0?w.slice(base):w,s)');
    s=one(s,'if(i>=base&&i<=hi)this.multag(c,i-base,[],this.tst);',
        `if(i>=base&&i<=hi){const previous=this.tag;this.tag=tg.slice(0,Math.ceil(Math.log2(hi-base+1)));
        this.multag(c,i-base,[],this.tst);this.tag=previous;}`);
    // Each one of the three comparisons restores every operand other than its
    // own dirty predicate. Evaluate the widest comparison least often.
    const prior='const dH=()=>{H();gate();H();gate();};\n const dG=()=>{G();dH();G();dH();};F();dG();F();dG();this.y=old;';
    s=one(s,prior,`const tests=[[F,4*m],[G,m],[H,t]].sort((a,b)=>b[1]-a[1]);
 const middle=()=>{tests[2][0]();gate();tests[2][0]();gate();};
 const inside=()=>{tests[1][0]();middle();tests[1][0]();middle();};
 tests[0][0]();inside();tests[0][0]();inside();this.y=old;`);
    return s;
}

function build(id,source,extras={}) {
    assert(!require.cache[id], 'Install before loading '+id);
    const fresh=new Module(id,module);
    fresh.filename=id;
    fresh.paths=Module._nodeModulePaths(path.dirname(id));
    Object.assign(fresh,extras);
    fresh._compile(source,id);
    fresh.loaded=true;
    return fresh;
}

function install(research,owner) {
    const sixID=require.resolve(path.join(research,'q648-next/field/six.cjs'));
    const six=one(fs.readFileSync(sixID,'utf8'),
        'built._compile(s,innerId);','built._compile(module.hosted(s),innerId);');
    require.cache[sixID]=build(sixID,six,{hosted});
    const outerID=require.resolve(path.join(research,'q648-next/field/outer.cjs'));
    let outer=one(fs.readFileSync(outerID,'utf8'),"'d14-walk-emitter.cjs'","'i9-divide-walk-emitter.cjs'");
    outer=one(outer,"'divide-i.cjs'","'i9-divide-divide-647.cjs'");
    outer=one(outer,'length:115','length:114');
    build(outerID,outer).exports.install(owner);
}

module.exports={install,hosted};
