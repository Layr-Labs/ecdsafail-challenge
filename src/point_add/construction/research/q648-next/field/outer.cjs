'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');

// Canonical restoring digit using one zero bit. The carry chain is the
// production primitive in nov09-joined/field/forward.cjs.
function cleanDigit(w,A,B,h,e,z){
    const n=A.length,k=n-1;
    const x=q=>w.raw(-1,-1,q),cx=(a,b)=>w.raw(a,-1,b),ccx=(a,b,t)=>w.raw(a,b,t);
    for(const b of B)x(b);
    if(n===1){
        ccx(e,A[0],z);ccx(z,B[0],h);x(B[0]);cx(e,h);
        ccx(z,h,B[0]);ccx(e,A[0],z);return;
    }
    for(let i=1;i<n;i++)cx(A[i],B[i]);
    ccx(e,A[k],h);
    for(let i=n-2;i>=1;i--)cx(A[i],A[i+1]);
    for(let i=0;i<n-1;i++)ccx(B[i],A[i],A[i+1]);
    ccx(e,A[k],z);ccx(z,B[k],h);ccx(e,A[k],z);
    cx(e,h);ccx(e,h,z);
    ccx(z,A[k],B[k]);
    for(let i=n-2;i>=0;i--){ccx(B[i],A[i],A[i+1]);ccx(z,A[i],B[i]);}
    ccx(e,h,z);
    for(let i=1;i<n-1;i++)cx(A[i],A[i+1]);
    for(let i=1;i<n;i++)cx(A[i],B[i]);
    for(const b of B)x(b);
}

function install(owner) {
    const file=require.resolve(path.join(owner,'d14-walk-emitter.cjs'));
    assert(!require.cache[require.resolve(path.join(owner,'divide-i.cjs'))]);
    const old=require(file);
    require.cache[file].exports={...old,wrap(pub){
        const base=old.wrap(pub);
        return function(w,L,R,ws,dirty,back,sink){
            if(ws.aux===-1||back||w.constructor.name!=='SectorReduced')
                return base(w,L,R,ws,dirty,back,sink);
            assert.equal(w.n,128);assert.equal(L[0],0);
            const scratch=Array.from({length:115},(_,j)=>3*w.n+6+j);
            const existing=new Set([...L,...R,...ws.tag,ws.sign,ws.fire,ws.tst,ws.aux,...dirty]);
            for(const q of scratch)assert(!existing.has(q),'public zero padding site already used '+q);
            const loans=dirty.slice(),known=w.y.slice(0,scratch.length);
            assert.equal(loans.length,w.y.length);
            for(let i=0;i<scratch.length;i++)loans[i]=scratch[i];
            if(process.env.Q648_FIELD_OUTER_INSPECT==='1'){
                const summary={type:w.constructor.name,L:[L[0],L.at(-1)],R:[R[0],R.at(-1)],ws,loan:[dirty[0],dirty.at(-1)],scratch:[scratch[0],scratch.at(-1)],
                    method:Object.getPrototypeOf(w).constructor.name,restore:w.restore.toString()};
                console.error(JSON.stringify(summary));throw Error('deliberate outer inspection stop');
            }
            const op=w.op;
            w.op=function(c,z){
                const n=c.length;
                if(n<3||n-2>known.length)return op.call(this,c,z);
                const tmp=known.slice(0,n-2);
                assert(!tmp.some(q=>q===z||c.includes(q)));
                this.raw(c[0],c[1],tmp[0]);
                for(let i=1;i<tmp.length;i++)this.raw(tmp[i-1],c[i+1],tmp[i]);
                this.raw(tmp.at(-1),c.at(-1),z);
                for(let i=tmp.length-1;i>=1;i--)this.raw(tmp[i-1],c[i+1],tmp[i]);
                this.raw(c[0],c[1],tmp[0]);
            };
            w.restore=function(c,A,B,ignored,h){
                assert.equal(c.length,1);cleanDigit(this,A,B,h,c[0],known[0]);
            };
            return base(w,L,R,ws,loans,back,sink);
        };
    }};
}
module.exports={install,cleanDigit};
