'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');

function once(s,old,value) {
    assert.equal(s.split(old).length,2,'Q648 lift source '+old.slice(0,55));
    return s.replace(old,()=>value);
}

function rewrite(s) {
    // Old M[n-1] is the complement of the row's enable. Rotate the low
    // n-1 sites while the old high bit is still available, then use one
    // count-controlled swap to transfer the wrapped bit to its final site.
    const oldRot="if(F.has('rot')){for(let j=1;j<n;j++){this.raw(M[0],-1,M[j]);pe(i,[M[j]],M[0]);this.raw(M[0],-1,M[j]);}}";
    const newRot=`if(F.has('rot')){
      X1(t);
      for(let j=1;j<n-1;j++){
        this.raw(M[0],-1,M[j]);this.raw(t,M[j],M[0]);this.raw(M[0],-1,M[j]);
      }
      X1(t);
      this.raw(M[0],-1,t);pe(i,[t],M[0]);this.raw(M[0],-1,t);
    }`;
    s=once(s,oldRot,newRot);

    // Every enabled high-count lift has a zero at both ends of M. The
    // low site can stand for its zero high digit during the conditional
    // add. The low target digit is unchanged when adding an even number.
    const oldPlus=`const g=plus(M,U,null,b);
   for(const r of g){const cs=r.slice(0,-1),z=r.at(-1);
    if(i>=half-1&&cs.includes(b)){if(F.has('plus'))pe(i,cs,z);else this.rows(MCX([active,...cs],z,y));}
    else this.raw(r.length>1?r[0]:-1,r.length>2?r[1]:-1,z);}`;
    const newPlus=`if(i>=half-1&&F.has('plus')){
      X1(t);
      for(const r of plus(M.slice(1,-1).concat(M[0]),U.slice(1),null,b)){
        const cs=r.slice(0,-1),z=r.at(-1);
        if(cs.includes(b))this.rows(MCX([t,...cs],z,y));
        else this.raw(r.length>1?r[0]:-1,r.length>2?r[1]:-1,z);
      }
      X1(t);
    }else{${oldPlus}}`;
    return once(s,oldPlus,newPlus);
}

function install(owner) {
    const id=require.resolve(path.join(owner,'q648/p648-lift.cjs')),old=require(id);
    require.cache[id].exports={...old,f:s=>rewrite(old.f(s))};
}

module.exports={install,rewrite};
