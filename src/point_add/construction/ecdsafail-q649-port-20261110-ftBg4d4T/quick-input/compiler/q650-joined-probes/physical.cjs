'use strict';
const path=require('node:path');
const {upperFilter}=require('../q651-upper-reduction/pass.cjs');
const {optimizeStream}=require('../q651-gate-reduction/commute.cjs');
const cache=require('../q651-product-cache/cache.cjs'),fusion=require('../q651-parity-fusion/fusion.cjs');
function installStages(q){
    const config=require(path.join(q,'stage-config.json'));
    for(const [moduleName,name] of [[config.multiplyModule,'emitMultiplySparse'],[config.divideModule,'emitDivideSparse']]){
        const p=require.resolve(path.join(q,moduleName)),base=require(p),old=base[name];
        require.cache[p].exports={...base,[name]:(sink,...rest)=>optimizeStream(visitor=>old(visitor,...rest),sink)};
    }
    const p=require.resolve(path.join(q,config.historyModule)),base=require(p),history=base.emitRegenerateSparse;
    require.cache[p].exports={...base,emitRegenerateSparse:(sink,erase=false)=>optimizeStream(
        visitor=>history(gs=>visitor('packed',gs),erase),(kind,gs)=>{if(kind!=='packed')throw Error('history output');sink(gs);})};
    globalThis.__q650ArithmeticPasses={upperFilter,cache,fusion};
}
function patchPhysical(s){
    function replace(a,b){if(s.split(a).length!==2)throw Error('Q650 physical compiler anchor '+a);s=s.replace(a,()=>b);}
    const field='const field=(div)=>bracketMap(tape,m,BigInt(delta),d,y,div,';
    replace(field,'const closeProducts=globalThis.__q650ArithmeticPasses.cache.install(tape,2*m);const closeFusion=globalThis.__q650ArithmeticPasses.fusion.install(tape);'+field);
    const tail='\n stepList(steps,back,fn=>fn(back));\n for(let i=0;i<states.length;i++)';
    replace(tail,tail.replace(';\n',';closeFusion();closeProducts();\n'));
    const wire='this.physical={out:(a,b,t)=>output.out(wire(a),wire(b),wire(t))};';
    replace(wire,'const filter=globalThis.__q650ArithmeticPasses.upperFilter(output);this.endUpper=filter.flush;output=filter;'+wire);
    const middle='const b=l.bank.length,R=D.slice(0,m-b),U=D.slice(m-b),';
    replace(middle,'t.endUpper();'+middle);
    const end='if(t.hist.size)throw Error("unfinished deferred phases");';
    replace(end,end+'t.endUpper();');
    return s;
}
module.exports={installStages,patchPhysical};
