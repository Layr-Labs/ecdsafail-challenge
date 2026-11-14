'use strict';
const path=require('node:path');
const {patch}=require('./upper.cjs');
const root=path.resolve(__dirname,'../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input');
const donor=path.join(root,'construction'),family='research/agents/midpoint-implicit-query-20261109/q651-ten-field';
const variant='arith-code-rotate-digit-codetrans-prefix-crop-host-fast-lease-leaseadd-f1-virtualtop-physical';
function build(change=true,inspect) {
    const api=require(path.join(root,'port/port.cjs')).build(donor,path.join(root,'compiler'),variant);
    const stages=require(path.join(donor,family,'stage-map.cjs')),old=stages.upper;
    stages.upper=(raw,c)=>{
        const baseline=old(raw,c),out=change?patch(baseline):baseline;
        if(inspect)inspect(out,baseline);
        return out;
    };
    return api;
}
function source() {
    let updated,ordinary;
    const api=build(true,(a,b)=>{updated=a;ordinary=b;});
    api.arithmetic(null);
    if(!updated||!ordinary)throw Error('upper source capture');
    return {updated,ordinary};
}
module.exports={build,source,variant,root};
