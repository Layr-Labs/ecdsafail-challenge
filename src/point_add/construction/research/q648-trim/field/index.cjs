'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');
const family='construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field';
const installed=new Map();

function install(pointAddRoot,compilerRoot,selection='all') {
    const root=path.resolve(pointAddRoot),compiler=path.resolve(compilerRoot),owner=path.join(root,family);
    if(installed.has(owner)){
        assert.equal(installed.get(owner),selection);return;
    }
    const configFile=path.join(owner,'stage-config-648.json');
    const config=require(configFile);assert.equal(config.width,648);
    process.env.Q648_PROFILE='648';
    Object.assign(process.env,require(path.join(owner,'q648-pieces.json')).env);
    process.env.TRACK_I_CONFIG=configFile;
    assert(!require.cache[require.resolve(path.join(owner,'point-i.cjs'))], 'Install before constructing the point program');
    require('./fast-window.cjs').install(owner);
    const controls=path.join(compiler,'q650-joined-probes');
    require(path.join(controls,'field-rotate.cjs')).install(owner);
    const shared=require(path.join(owner,'shared-digit.cjs')).sharedDigit;
    for(const name of ['m6-alternating.cjs','d14-alternating-digit.cjs']){
        const k=require.resolve(path.join(owner,name));require(k);
        require.cache[k].exports={alternatingDigit:shared};
    }
    const chosen=new Set(selection==='all'?['multiply','divide','history']:selection.split(','));
    if(chosen.has('power'))require('./power.cjs').install(owner);
    if(chosen.has('lift'))require('./lift.cjs').install(owner);
    if(selection!=='prior')require('./walks.cjs').install(owner,chosen);
    require(path.join(compiler,'q650-field-fusion/stream.cjs')).install(compiler);
    const {optimizeStream}=require(path.join(compiler,'q651-gate-reduction/commute.cjs'));
    for(const [entry,name] of [[config.multiplyModule,'emitMultiplySparse'],[config.divideModule,'emitDivideSparse']]){
        const k=require.resolve(path.join(owner,entry)),o=require(k),fn=o[name];
        require.cache[k].exports={...o,[name]:(sink,...args)=>optimizeStream(visit=>fn(visit,...args),sink)};
    }
    const h=require.resolve(path.join(owner,config.historyModule)),o=require(h);
    require.cache[h].exports={...o,emitRegenerateSparse(sink,erase=false){
        optimizeStream(visit=>o.emitRegenerateSparse(chunk=>visit('packed',chunk),erase),
            (kind,chunk)=>{assert.equal(kind,'packed');sink(chunk);});
    }};
    globalThis.__q650ArithmeticPasses={
        upperFilter:require(path.join(compiler,'q651-upper-reduction/pass.cjs')).upperFilter,
        cache:require(path.join(compiler,'q651-product-cache/cache.cjs')),
        fusion:require(path.join(compiler,'q651-parity-fusion/fusion.cjs'))
    };
    installed.set(owner,selection);
}

module.exports={family,install};
