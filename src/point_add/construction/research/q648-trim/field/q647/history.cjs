'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');
const {planFor}=require('../graded-relay.cjs');

function plan(w,scale,owner) {
    const small=require(path.join(owner,'i9-divide-walk-small.cjs'));
    const first=w.L[w.n+1],second=scale.T[1],top=w.tag.at(-1);
    assert.equal(new Set([first,second,w.fire,w.tst,top]).size,5,'six-helper signed-walk ports');
    const bits=Math.min(7,Math.log2(w.n));
    const virtual=Array.from({length:bits-3},(_,i)=>900+i);
    w.tag=[first,second,...virtual,top];
    const roles=[...virtual].reverse();
    w.d18reduced=false;w.d18digit=require(path.join(owner,'shared-digit.cjs')).sharedDigit;
    w.zeroPair=small.zeroPair;w.d9oldRot=w.rot;w.rot=small.rot2;
    const blocks=planFor(2).call(w);
    for(const block of blocks){
        const fn=block.fn;
        block.fn=()=>{
            fn();
            const physical=q=>{const j=roles.indexOf(q);if(j<0)return q;
                assert(block.ports[j]!=null,'Q647 history virtual tag');return block.ports[j];};
            for(let j=0;j<w.g.length;j++){
                const x=w.g[j],a=physical(x>>>20),b=physical(x>>>10&1023),t=physical(x&1023);
                assert(t!==a&&t!==b&&(a!==b||a===1023));w.g[j]=(a<<20)|(b<<10)|t;
            }
        };
    }
    return blocks;
}

function install(owner) {
    const id=require.resolve(path.join(owner,'i9-history-p-r647.cjs')),old=require(id);
    const site='r43RelayPlan(walk6)',call=`require(${JSON.stringify(__filename)}).plan(walk6,scale,${JSON.stringify(owner)})`;
    let changed=0;
    const edited=old.map(([a,b])=>[a,b.replace(site,()=>{++changed;return call;})]);
    assert.equal(changed,1,'Q647 R6 call');require.cache[id].exports=edited;
}

module.exports={install,plan};
