'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');
const family='construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field';

// Call in a fresh process, before the Q647 donor loads its point program.
// The configuration here affects the three lower stages only.
function install(pointAddRoot,compilerRoot,{multiplyRelay=false,historyRelay=false,wholeFieldPass=true}={}) {
    const owner=path.join(path.resolve(pointAddRoot),family),compiler=path.resolve(compilerRoot);
    const configFile=path.join(owner,'stage-config.json'),cfg=require(configFile);
    assert.equal(cfg.width,647);
    const point=require.resolve(path.join(owner,'point-i.cjs'));
    assert(!require.cache[point],'install before Q647 point construction');
    process.env.TRACK_I_CONFIG=configFile;
    require('./fast.cjs').install(owner);
    const shared=require(path.join(owner,'shared-digit.cjs')).sharedDigit;
    const m=require.resolve(path.join(owner,'i9-multiply-s4-m-alternating.cjs')),oldM=require(m);
    require.cache[m].exports={...oldM,alternatingDigit:shared};
    // D25 winding encodes Q[0] in a conditional low-bit host. Its donor
    // digit has a gate-level guard on each such operand. Keep that digit
    // and use the shared routine within the Euclidean walks only.
    const d=require.resolve(path.join(owner,'i9-divide-walk-emitter.cjs')),oldD=require(d);
    require.cache[d].exports={...oldD,wrap:pub=>oldD.wrap({...pub,dirtyDigit:shared})};
    if(multiplyRelay)require('./relay.cjs').install(owner);
    if(historyRelay)require('./history.cjs').install(owner);
    require('./index.cjs').install(owner);
    if(!wholeFieldPass)return;
    require(path.join(compiler,'q650-field-fusion/stream.cjs')).install(compiler);
    const {optimizeStream}=require(path.join(compiler,'q651-gate-reduction/commute.cjs'));
    for(const [entry,name] of [[cfg.multiplyModule,'emitMultiplySparse'],[cfg.divideModule,'emitDivideSparse']]){
        const id=require.resolve(path.join(owner,entry)),old=require(id),emit=old[name];
        require.cache[id].exports={...old,[name]:(sink,...args)=>optimizeStream(v=>emit(v,...args),sink)};
    }
    const id=require.resolve(path.join(owner,cfg.historyModule)),h=require(id);
    require.cache[id].exports={...h,emitRegenerateSparse(sink,back=false){
        optimizeStream(v=>h.emitRegenerateSparse(g=>v('packed',g),back),
            (k,g)=>{assert.equal(k,'packed');sink(g);});
    }};
}

module.exports={family,install};
