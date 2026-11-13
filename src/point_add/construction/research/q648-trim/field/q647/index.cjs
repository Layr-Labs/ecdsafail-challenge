'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');

function once(s,old,next) {
    assert.equal(s.split(old).length,2,'Q647 source '+old.slice(0,50));
    return s.replace(old,()=>next);
}

// h ^= en * XOR_j (U[j] xor K[j]) * [M[0..j-i) == 0].
// Store suffix parities directly in U, then unwind them in reverse.
function lift(s) {
    const original=`for(let j=i;j<n-1;j++){
    const low=M.slice(0,j-i),neg=[...low];
    if((K>>BigInt(j))&1n)neg.push(U[j]);
    for(const q of neg)this.raw(-1,-1,q);
    this.op([en,...low,U[j]],h);
    for(const q of neg.slice().reverse())this.raw(-1,-1,q);
   }`;
    const replacement=`const polarity=()=>{for(let j=i;j<n-1;j++)if((K>>BigInt(j))&1n)this.raw(-1,-1,U[j]);};
   const link=j=>{const m=M[j-i];this.raw(-1,-1,m);this.raw(m,U[j+1],U[j]);this.raw(-1,-1,m);};
   polarity();for(let j=n-3;j>=i;j--)link(j);
   this.raw(en,U[i],h);
   for(let j=i;j<n-2;j++)link(j);polarity();`;
    return once(s,original,replacement);
}

// The class code leaves the normalized top scalar bit one. The two passes
// put H at the first nonzero scalar position on the head site, then restore
// H. The scalar bits below the permitted interval remain genuine controls.
function power(old) {
    const original=`for(const [c,d,explicit]of classes)for(let v=Math.max(i+1,d);v<128;v++){
   const low=T.slice(d,v),controls=[en,...low,T[v],H[v]],neg=[...low];if(kappa>>BigInt(v-i-1)&1n)neg.push(H[v]);
   if(explicit)cls(c,controls,q,neg);else emit(controls,q,neg);
  }`;
    const replacement=`for(const [c,d,explicit]of classes){
   const a=Math.max(i+1,d),low=T.slice(d,a);
   const flip=()=>{for(let v=a;v<128;v++)if(kappa>>BigInt(v-i-1)&1n)raw([H[v]]);};
   const link=v=>{raw([T[v]]);for(const g of p.fr(T[v],H[v],H[v+1]))raw(g);raw([T[v]]);};
   flip();for(let v=126;v>=a;v--)link(v);
   const controls=[en,...low,H[a]];
   if(explicit)cls(c,controls,q,low);else emit(controls,q,low);
   for(let v=a;v<127;v++)link(v);flip();
  }`;
    const src=once(old.powerFactory.toString(),original,replacement);
    return Function('sourceDouble','return ('+src+');')(old.sourceDouble);
}

// An active class has a known zero prefix of length d in the numeric
// modulus. Its physical code agrees with the numeric word above that cut.
// A restoring digit by 2^d a leaves the d low remainder bits alone and
// restricts to the ordinary digit by a on the higher bits.
function powerDouble(old) {
    const replacement=`for(let j=0;j<128;j++)for(const row of p.fr(en,q,H[j]))raw(row);
   const digit=(d,ctl)=>{for(const row of p.digit(128-d,T.slice(d),H.slice(d),q,ctl,644))raw(row);};
   if(i>=6)digit(7,en);
   else for(const [c,d] of [[1,1],[2,2],[3,7]]){
     if(c===1&&i>=2)continue;
     cls(c,[en],645);digit(d,645);cls(c,[en],645);
   }`;
    const src=once(power(old).toString(),
        'for(const r of sourceDouble(128,T,H,643,644,645,p))lower(r);',replacement);
    return Function('return ('+src+');')();
}

function install(owner) {
    const m=require.resolve(path.join(owner,'i9-multiply-multiply-647.cjs'));
    assert(!require.cache[m],'Install before loading the Q647 multiplier');
    const a=require.resolve(path.join(owner,'i9-multiply-m9-shifted-lift.cjs'));
    const oldLift=require(a);require.cache[a].exports=s=>lift(oldLift(s));
    const b=require.resolve(path.join(owner,'i9-multiply-m9-simple-power.cjs'));
    const oldPower=require(b);require.cache[b].exports={...oldPower,powerFactory:powerDouble(oldPower)};
}

module.exports={install,lift,power,powerDouble};
