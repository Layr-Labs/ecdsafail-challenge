'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');

// The forward R6 park puts quotient bits on T[i] starting at the bit
// length of V. T[1] can carry data only for V=1; then R mod V is zero
// and the signed Euclidean walk is on its bypass input.
function install(owner) {
    const id=require.resolve(path.join(owner,'../q648w/r648-regen.cjs'));
    const old=require(id),moduleId=path.join(owner,'../q648w/walkt1.cjs');
    require.cache[id].exports={...old,walk6KR(w,scale,n){
        const {TstRelayK}=require(moduleId);
        // The extra site is an interior normalization tag. The predicates
        // and the balance comparison have genuine clean sites on V=1.
        const walk=new TstRelayK(n,[647,648,scale.T[1],w.R[n+1]],scale.T[0],{flat:false});
        assert.equal(walk.sign,w.sign);assert.equal(walk.y[0],w.y[0]);
        return walk.plan().map(b=>({...b,fn:()=>{walk.g=w.g;b.fn();}}));
    }};
}

module.exports={install};
