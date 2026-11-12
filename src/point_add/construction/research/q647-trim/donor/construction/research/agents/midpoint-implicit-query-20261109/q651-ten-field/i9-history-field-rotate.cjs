'use strict';
const {sharedControlledPermutation}=require('./i9-history-s3-shared-controls.cjs');
const seen=new WeakSet();
function dirtyMc(w,cs,t,pool){
    if(cs.length===1){w.raw(cs[0],-1,t);return;}
    if(cs.length===2){w.raw(cs[0],cs[1],t);return;}
    if(cs.length<1||pool.length<cs.length-2)throw Error('field control workspace');
    for(let echo=0;echo<2;echo++){
        if(!echo)w.raw(cs[0],cs[1],pool[0]);
        for(let i=1;i<cs.length-2;i++)w.raw(pool[i-1],cs[i+1],pool[i]);
        w.raw(pool[cs.length-3],cs.at(-1),t);
        for(let i=cs.length-3;i>=1;i--)w.raw(pool[i-1],cs[i+1],pool[i]);
        if(!echo)w.raw(cs[0],cs[1],pool[0]);
    }
}
function adapt(w){
    // Look up the owner of the inherited rotate primitive and patch that
    // private interpreter instance family once. Each independent build has
    // its own derived walk constructors.
    let p=Object.getPrototypeOf(w);
    while(p&&!Object.hasOwn(p,'rot'))p=Object.getPrototypeOf(p);
    if(!p||seen.has(p))return w;
    seen.add(p);
    const original=p.rot;
    p.rot=function(cs,word,shift){
        const n=word.length;if(cs.length<2||n<3)return original.call(this,cs,word,shift);
        const off=(shift%n+n)%n;if(!off)return;
        const origins=word.slice(-off).concat(word.slice(0,-off));
        const self=this,asTape={one:-1,out(a,b,t){if(a===1023)self.raw(b===1023?-1:b,-1,t);else self.raw(a,b===1023?-1:b,t);},
            mc(controls,t,loans){dirtyMc(self,controls,t,loans);},
            loan(used,number){const u=new Set(used),out=[];for(const q of self.y)if(!u.has(q)&&out.length<number)out.push(q);
                if(out.length!==number)throw Error('field permutation loan');return out;}};
        if(!sharedControlledPermutation(asTape,word,origins,cs,false))original.call(this,cs,word,shift);
    };
    return w;
}
function instrument(pub){
    for(const ctor of [pub.D2Canonical,pub.D2Reduced,pub.R35UnitWalk])if(typeof ctor==='function')for(const j of [4,6])adapt(new ctor(128,j));
    return pub;
}
function install(q){
    const path=require('node:path'),pub=require(path.join(q,'public-backend.cjs'));
    const old=pub.withDigit;
    pub.withDigit=fn=>instrument(old(fn));
    instrument(pub);
}
module.exports={adapt,install};
