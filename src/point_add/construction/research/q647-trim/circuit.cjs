'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const quick = path.resolve(__dirname,'../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input');
const compiler = path.join(quick,'compiler');
const owner = path.join(__dirname,'donor/construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field');

function circuit() {
    process.env.TRACK_I_CONFIG = path.join(owner,'stage-config.json');
    const cfg = require(process.env.TRACK_I_CONFIG);
    assert.equal(cfg.width,647);
    assert.deepEqual(cfg.helperSites,[512,641,642,643,644,645]);
    assert.equal(cfg.upperSign,646);
    const field=require('../q648-trim/field/q647/stages.cjs');
    field.install(path.join(__dirname,'donor'),compiler,{historyRelay:true});
    const physical = require(path.join(compiler,'q650-joined-probes/physical.cjs'));
    globalThis.__q650ArithmeticPasses={
        upperFilter:require(path.join(compiler,'q651-upper-reduction/pass.cjs')).upperFilter,
        cache:require(path.join(compiler,'q651-product-cache/cache.cjs')),
        fusion:require(path.join(compiler,'q651-parity-fusion/fusion.cjs'))
    };
    const stages = require(path.join(owner,'stage-map.cjs')), initial = stages.upper;
    stages.upper = (raw,config) => {
        let s = require('./upper/integrated.cjs').patch(initial(raw,config),compiler);
        s = require('../q648-trim/alternate/unit/unit.cjs').patch(s);
        s = require('../q648-trim/alternate/square.cjs').patch(s);
        // The six-helper donor instruments the logical-to-physical mapping,
        // including each change of the evicted helper. Keep that hook intact.
        const generic = 'this.physical={out:(a,b,t)=>output.out(wire(a),wire(b),wire(t))};';
        const traced = "this.physical={out:(a,b,t)=>{note('gate',[a,b,t]);output.out(wire(a),wire(b),wire(t));}};";
        function replace(old, repl) {
            assert.equal(s.split(old).length,2,old);
            s=s.replace(old,()=>repl);
        }
        replace(traced,generic);
        s=physical.patchPhysical(s);
        replace(generic,traced);
        replace('this.endUpper=filter.flush;',
            'const finishStage=this.s1Flush,finishFrame=this.u37Flush;'+
            'this.s1Flush=()=>{filter.flush();finishStage();};'+
            'this.u37Flush=()=>{filter.flush();finishFrame();};this.endUpper=this.s1Flush;');
        return s;
    };
    const api = require(path.join(owner,'point-i.cjs'));
    class GateWriter extends api.GateWriter {
        hooks() {
            const hooks = super.hooks(), start = hooks.start;
            hooks.start = (Tape,width,controls) => {
                const tape = start(Tape,width,controls), bit = tape.nextBit++;
                tape.eraseProduct = (a,b,target) => {
                    this.emit(12,target,bit);
                    this.emit(9,a,b,bit);
                    this.emit(4,bit);
                };
                return tape;
            };
            return hooks;
        }
    }
    return {...api,GateWriter};
}
function check(api,direction,count) {
    const bytes=fs.readFileSync(path.join(quick,'fixtures/openssl-384.json'));
    const fixture=JSON.parse(bytes);
    assert(['forward','reverse'].includes(direction) && count>=1 && count<=fixture.length);
    const rows=fixture.slice(0,count).map(p=>Object.fromEntries(Object.entries(p).map(([k,v])=>[k,v && v.map(BigInt)])));
    const checked=api.arithmetic(null).shellWithFieldOracles(256,(1n<<32n)+977n,rows,direction==='reverse',
        {forward:api.forward,regenerate:api.regenerate},api.divide,'random',false);
    assert.equal(checked.width,647);
    for(const name of ['shortForwardOracles','shortInverseOracles','historyOracles']) assert.equal(checked[name],0);
    return {direction,fixtureSha256:crypto.createHash('sha256').update(bytes).digest('hex'),...checked};
}

if(require.main===module) {
    const [action,target,size]=process.argv.slice(2);
    // Published native stages print progress. Keep stdout exclusively for the
    // machine-readable receipt or the little-endian gate stream.
    const report=console.log.bind(console);
    console.log=console.error;
    const api=circuit();
    if(action==='assemble') {
        api.arithmetic(null);
        report(JSON.stringify({width:api.config.width,helpers:api.config.helperSites,sign:api.config.upperSign}));
    } else if(action==='check') report(JSON.stringify(check(api,target,Number(size||32)),null,2));
    else if(action==='stream' && target) {
        assert.equal(require('node:os').endianness(),'LE');
        const writer=new api.GateWriter(null,size);
        writer.file=1;
        fs.writeFileSync(target,JSON.stringify(writer.produce(),null,2)+'\n',{flag:'wx'});
    } else throw Error('Use assemble, check forward|reverse N, or stream RECEIPT [RANGES]');
}
module.exports={circuit,check};
