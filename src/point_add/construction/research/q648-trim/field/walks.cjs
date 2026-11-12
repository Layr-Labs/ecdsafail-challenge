'use strict';

const assert=require('node:assert/strict');
const path=require('node:path');
const graded=require('./graded-relay.cjs');
const original=require('./relay-source.cjs');

function prepare(w,k,digit,small,signed=false) {
    if(signed){
        let proto=Object.getPrototypeOf(w);
        while(proto && !(Object.hasOwn(proto,'plan') && proto.plan.toString().includes('const stride=1<<tag.length')))
            proto=Object.getPrototypeOf(proto);
        assert(proto,'signed core');
        w.plan=proto.plan;
    }
    small.install(w,digit,{rot:true,pair:true,select:true});
    if(k)return graded.adapt(w,digit,k);
    // Both genuine bits are the fire and comparison wires. The original
    // D22 dirty test restores its arbitrary incoming tag on this domain.
    const bits=Math.min(7,Math.log2(w.n)),top=w.tag.at(-1);
    w.tag=Array.from({length:bits-1},(_,i)=>900+i).concat(top);
    w.nq=Math.max(910,w.nq);
    return original.install(w,digit);
}

// The seven-helper direct interface supplies real tags plus a fire wire.
// Spend the last real tag on the comparison and host the other shift bits.
class Direct {
    constructor(pub,small,n,tags,fire,signed) {
        const k=tags.length-1;
        const w=new pub.D2Canonical(n,Math.min(5,Math.log2(n)));
        this.w=prepare(w,k,pub.dirtyDigit,small,signed);
        this.keys=w.tag.slice(0,k);
        this.tag=tags.slice();this.tst=tags.at(-1);this.fire=fire;this.direct=true;
        for(const prop of ['n','L','R','y','sign','nq','nct'])this[prop]=w[prop];
    }
    plan() {
        const w=this.w,top=w.tag.at(-1),map=new Map(this.keys.map((q,i)=>[q,this.tag[i]]));
        map.set(w.tst,this.tst);map.set(w.fire,this.fire);
        return w.plan().map(b=>({...b,fn:()=>{
            w.g=[];b.fn();
            const fix=q=>{
                if(q===top){assert(b.topPort!=null);q=b.topPort;}
                if(q>=900&&q!==1023)throw Error('unresolved direct relay '+q);
                return map.get(q)??q;
            };
            for(let i=0;i<w.g.length;i++){
                const x=w.g[i],a=fix(x>>>20),b=fix((x>>>10)&1023),t=fix(x&1023);
                if(t===a||t===b||(a===b&&a!==1023))throw Error('seven-helper direct alias');
                w.g[i]=(a<<20)|(b<<10)|t;
            }
            this.g=w.g;
        }}));
    }
}

function install(owner,chosen) {
    const small=require(path.join(owner,'d14-walk-small.cjs'));
    const pub=require(path.join(owner,'public-backend.cjs')).withDigit(require(path.join(owner,'shared-digit.cjs')).sharedDigit);
    const filename=require.resolve(path.join(owner,'../q648w/walkt1.cjs')),stock=require(filename);
    if(chosen.has('multiply')||chosen.has('history')){
        class Selected {
            constructor(n,real,fire,opts={}){
                const signed=opts.flat===false;
                if(!chosen.has(signed?'history':'multiply'))return new stock.TstRelayK(n,real,fire,opts);
                const direct=new Direct(pub,small,n,real,fire,signed);
                // The history loader supplies its existing gate array before
                // invoking a block. Append to that array for its native sink.
                if(signed){
                    const plan=direct.plan.bind(direct);
                    direct.plan=()=>plan().map(b=>({...b,fn:()=>{
                        const target=direct.g;b.fn();
                        for(const gate of direct.g)target.push(gate);
                        direct.g=target;
                    }}));
                }
                return direct;
            }
        }
        require.cache[filename].exports={...stock,TstRelayK:Selected};
    }
    if(chosen.has('divide')){
        const id=require.resolve(path.join(owner,'d648-walks.cjs')),old=require(id);
        require.cache[id].exports={...old,wrapEmit(raw,wrapped){
            const fallback=old.wrapEmit(raw,wrapped);
            return function(w,L,R,ws,dirty,back,sink){
                if(ws.aux!==-1)return fallback(w,L,R,ws,dirty,back,sink);
                assert.equal(w.constructor.name,back?'D2ReducedImpl':'D2Canonical');
                const k=Number(back);
                prepare(w,k,raw.dirtyDigit,small);
                const tags=Array(w.tag.length).fill(-1);
                if(k)tags[0]=ws.tag[0];
                const ports={sign:ws.sign,tag:tags,fire:back?ws.tag[1]:ws.fire,
                    tst:back?L[w.n+1]:ws.tag[0],aux:-1};
                return raw.emitWalk(w,L,R,ports,dirty,back,sink);
            };
        }};
    }
}

module.exports={install};
