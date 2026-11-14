'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');
const {planFor}=require('./relay.cjs');

function signed(w,realCount,makePlan,digit,zeroPair,rot) {
    const physical=w.tag.slice(0,realCount),top=w.tag.at(-1);
    const tags=Math.min(7,Math.log2(w.n));
    const virtual=Array.from({length:tags-realCount-1},(_,i)=>900+i);
    w.tag=physical.concat(virtual,top);
    const roles=virtual.slice().reverse();
    w.d18reduced=false;w.d18digit=digit;w.zeroPair=zeroPair;
    w.d9oldRot=w.rot;w.rot=rot;
    const blocks=makePlan.call(w);
    for(const block of blocks) {
        const body=block.fn;
        block.fn=()=>{
            body();
            const physical=q=>{
                const j=roles.indexOf(q);
                if(j<0)return q;
                const host=block.ports[j];
                if(host===null||host===undefined)throw Error('history normalization tag');
                return host;
            };
            for(let j=0;j<w.g.length;j++){
                const g=w.g[j],a=physical(g>>>20),b=physical(g>>>10&1023),t=physical(g&1023);
                if(a===t||b===t||(a===b&&a!==1023))throw Error('history relay alias');
                w.g[j]=(a<<20)|(b<<10)|t;
            }
        };
    }
    return blocks;
}

function install(campaign=path.resolve(__dirname,'../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input')) {
    const owner=path.join(campaign,'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field');
    assert(!require.cache[require.resolve(path.join(owner,'r6-regen649.cjs'))]);
    const src=require.resolve(path.join(owner,'r6-p-r649-final.js')),original=require(src);
    const small=require(path.join(owner,'d14-walk-small.cjs'));
    const digit=require(path.join(owner,'shared-digit.cjs')).sharedDigit;
    const anchor='function emitRegenerateSparse(sink,erase=false){';
    const code=['function r43RelayPlan(w){','const realCount=2;',
        'return ('+signed.toString()+')(w,realCount,'+planFor(2).toString()+',',
        digit.toString()+','+small.zeroPair.toString()+','+small.rot2.toString()+');','}',anchor].join('\n');
    const edits=original.map(([a,b])=>[a,b.includes('function r43RelayPlan(w)')?code:b]);
    assert.equal(edits.filter(([a,b])=>b===code).length,1);
    require.cache[src].exports=edits;
}

module.exports={install};
