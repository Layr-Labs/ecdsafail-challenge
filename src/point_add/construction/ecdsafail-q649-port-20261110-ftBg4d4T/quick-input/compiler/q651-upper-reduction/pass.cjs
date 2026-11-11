'use strict';
const {optimizeBlock,record,N}=require('../q651-gate-reduction/commute.cjs');
function upperFilter(output){
    const pending=[],limit=128;
    function flush(){
        if(!pending.length)return;
        const out=[];optimizeBlock(pending,out,32);pending.length=0;
        for(const g of out){
            const a=g>>>20,b=g>>>10&1023,t=g&1023;
            if(b===N)output.out(N,a,t);
            else output.out(a,b,t);
        }
    }
    function out(a,b,t){
        pending.push(record(a,b,t));if(pending.length===limit)flush();
    }
    function cond(bit,fn){
        flush();return output.cond(bit,()=>{fn();flush();});
    }
    function hmr(q){flush();return output.hmr(q);}
    function z(q){flush();return output.z(q);}
    return {out,cond,hmr,z,flush};
}
module.exports={upperFilter};
