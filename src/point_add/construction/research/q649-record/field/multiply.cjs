'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');
const {adapt}=require('./relay.cjs');

function walkClass(pub,bits,small) {
    return class extends pub.D2Canonical {
        constructor(n) {
            super(n,Math.min(bits,Math.log2(n)));
            assert(this.tag.length>=3);
        }
        plan() {
            // The caller constructs the published physical map before asking
            // for these blocks. Preserve its real tag positions and top host.
            this.plan=pub.D2Canonical.prototype.plan;
            small.install(this,pub.dirtyDigit,{rot:true,pair:true,select:true});
            adapt(this,pub.dirtyDigit,Math.min(3,this.tag.length-2));
            const blocks=this.plan(),full=this.tag;
            // M6's mapper looks up the penultimate current tag after each
            // block. The relay has already lowered every virtual tag.
            for(const block of blocks){
                const body=block.fn;
                block.fn=()=>{body();this.tag=full;};
            }
            return blocks;
        }
    };
}

function install(campaign=path.resolve(__dirname,'../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input')) {
    const owner=path.join(campaign,'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field');
    assert(!require.cache[require.resolve(path.join(owner,'m6-multiply-649.cjs'))]);
    const wide=require(path.join(campaign,'port/wide-walk.cjs')),previous=wide.installMultiply;
    wide.installMultiply=q=>{
        previous(q);
        const hostFile=require.resolve(path.join(q,'m6-host-walk.cjs'));
        const small=require(path.join(q,'d14-walk-small.cjs'));
        require.cache[hostFile].exports=(pub,bits=5)=>walkClass(pub,bits,small);
    };
}

module.exports={walkClass,install};
