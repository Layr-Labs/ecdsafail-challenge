'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');

function replaceOne(s,old,replacement) {
    assert.equal(s.split(old).length,2,'Q648 power source '+old);
    return s.replace(old,()=>replacement);
}

// For the selected rows, s>i implies the normalized modulus is divisible
// by 2^(r+1). Its top bit is 1 on all inputs. Host the enable there and use
// bit r as the virtual top of the divisor ripple, then as the group bit.
function rewrite(source) {
    const marker='function m6powerSweep0(n,M,X,s,J,e,dirty,i,kappa) {';
    const a=source.indexOf(marker),b=source.indexOf('\n}',a);
    assert(a>=0&&b>a);
    let copied=source.slice(a,b+2);
    copied=replaceOne(copied,marker,'function q648PowerOnTop(n,M,X,s,J,dropped,dirty,i,kappa) {');
    copied=replaceOne(copied,'const groupBit=M[n-1],guard=',
        'const r=J.length,groupBit=M[r],e=M[n-1],guard=');
    copied=replaceOne(copied,'let gates=guard.concat(dirtyDigit(M.slice(J.length),X.slice(J.length-1,-1)',
        'let gates=[[e],[groupBit]].concat(guard,dirtyDigit(M.slice(r+1,-1).concat(groupBit),X.slice(r,-1)');
    copied=replaceOne(copied,'const cs=M.slice(J.length,k);','const cs=M.slice(r+1,k);');
    copied=replaceOne(copied,'return gates.concat(guard.slice().reverse());',
        'return gates.concat(guard.slice().reverse(),[[groupBit],[e]]);');
    return copied+'\n'+replaceOne(source,
        'function m6powerSweep(n,M,X,s,J,e,dirty,i,kappa){const g=',
        'function m6powerSweep(n,M,X,s,J,e,dirty,i,kappa){if(i>=J.length)return q648PowerOnTop(n,M,X,s,J,e,dirty,i,kappa);const g=');
}

function install(owner) {
    const id=require.resolve(path.join(owner,'q648/p648-power.cjs')),old=require(id);
    require.cache[id].exports={...old,f:s=>rewrite(old.f(s))};
}

module.exports={install,rewrite};
