'use strict';
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const Module=require('node:module');
const family='construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field';

function replace(source,old,next) {
    assert.equal(source.split(old).length,2,old.slice(0,80));
    return source.replace(old,()=>next);
}

// The one-predicate Q647 inner walker stores its equality predicate at r[j]
// and its dirty digit head at r[j+1]. Its one-relay branch decodes one bit.
function hostedCover(m,depth) {
    const cap=kind=>kind<2?2:2**(kind+1);
    const available=base=>base<2?0:base<4?1:Math.min(depth,base-2);
    let tail=0;while(tail<m&&m-tail>cap(available(tail)))++tail;
    const sectors=[];
    for(let base=0;base<m;){
        const kind=available(base),width=Math.min(cap(kind),base<tail?tail-base:m-base);
        let use=kind;
        if(kind>=2){while(use>2&&width<=cap(use-1))--use;}
        sectors.push({base,width,kind:use});base+=width;
    }
    return sectors;
}

function install(fieldDir,pointAddRoot,{inner=true}={}) {
    const root=path.resolve(fieldDir),owner=path.join(path.resolve(pointAddRoot),family);
    assert.equal(require(path.join(owner,'stage-config.json')).width,647);
    // The second real history tag is parked T[1]. Its V=1 bypass can be dirty.
    require('./tail.cjs').install(root,{simple:false});
    const relayFile=require.resolve(path.join(root,'relay-source.cjs')),relay=require(relayFile);
    const stagesFile=require.resolve(path.join(root,'q647/stages.cjs'));
    const stages=require(stagesFile);
    require.cache[stagesFile].exports={...stages,install(point,compiler,options={}){
        return stages.install(point,compiler,{...options,multiplyRelay:true,historyRelay:true});
    }};
    const histID=require.resolve(path.join(owner,'i9-history-p-r647.cjs'));
    const history=require(histID);
    const prior=require(path.join(owner,'i9-history-multi-relay.cjs')).plan.toString();
    let planCount=0,tagCount=0;
    require.cache[histID].exports=history.map(([from,to])=>{
        if(to.includes('const blocks=('+prior+').call(w);')){
            to=replace(to,'const blocks=('+prior+').call(w);',
                'const blocks=require('+JSON.stringify(relayFile)+').plan.call(w);');
            ++planCount;
        }
        if(to.includes('walk.tag=[900,901,902,903,904,651];')){
            to=replace(to,'walk.tag=[900,901,902,903,904,651];',
                'walk.tag=[900,901,902,903,904,905,651];');++tagCount;
        }
        return [from,to];
    });
    assert.equal(planCount,1);assert.equal(tagCount,1);
    const reverseId=require.resolve(path.join(owner,'i9-divide-multi-relay.cjs'));
    const old=require(reverseId);
    require.cache[reverseId].exports={...old,install(w,digit){
        w.tag=Array.from({length:6},(_,i)=>900+i).concat(w.tag.at(-1));
        w.nq=Math.max(910,w.nq);
        return relay.install(w,digit);
    }};
    if(!inner)return;
    const innerId=require.resolve(path.join(owner,'i9-divide-hosted-test.cjs'));
    assert(!require.cache[innerId],'install six-helper inner before divider');
    let s=fs.readFileSync(innerId,'utf8').replaceAll('\r\n','\n');
    const partition=s.match(/  const depth=roles.length,low=2[^\n]+\n  for\(let j=1;j<depth;[^\n]+/);
    assert(partition);
    s=replace(s,partition[0],'  const sectors=module.cover(m,roles.length);');
    s=replace(s,"if(w.tag.length<3||w.tag.length>7)",`const top=w.tag.at(-1);
 w.tag=Array.from({length:6},(_,i)=>900+i).concat(top);w.nq=Math.max(910,w.nq);
 if(w.tag.length<3||w.tag.length>7)`);
    const built=new Module(innerId,module);built.filename=innerId;
    built.paths=Module._nodeModulePaths(owner);built.cover=hostedCover;
    built._compile(s,innerId);built.loaded=true;require.cache[innerId]=built;
}
module.exports={install,hostedCover};
