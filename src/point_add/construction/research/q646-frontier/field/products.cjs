'use strict';

const assert = require('node:assert/strict');
const path = require('node:path');
const NONE = 1023;
const RECORD = 16383;
const code = (a, b, t) => (a << 20) | (b << 10) | t;

// A block comes directly from one reversible walk primitive. Every clean
// quotient-padding loan is zero on entry and restored by that primitive.
// Pick only loans that the original primitive never reads or writes.
function directErasures(rows,bank) {
    const zero=new Set(bank),products=new Map(),writes=new Int32Array(1024).fill(-1);
    const marked=new Uint8Array(rows.length);
    for(let i=0;i<rows.length;i++){
        const g=rows[i],t=g&1023;
        let a=g>>>20,b=g>>>10&1023;
        if(a>b)[a,b]=[b,a];
        const previous=products.get(t);
        if(previous && previous.a===a && previous.b===b && writes[a]<previous.first && writes[b]<previous.first){
            marked[previous.first]=1;marked[i]=2;products.delete(t);zero.add(t);
        }else if(zero.delete(t) && b!==NONE){
            products.set(t,{a,b,first:i});
        }else products.delete(t);
        writes[t]=i;
    }
    return marked;
}

function share(rows, bank, sink, measured = true, direct = false) {
    if (!rows.length) return;
    const busy = new Uint8Array(1024);
    for (const g of rows) {
        busy[g >>> 20] = busy[g >>> 10 & 1023] = busy[g & 1023] = 1;
    }
    const free = bank.filter(q => !busy[q]);
    const shortcuts=direct&&measured&&directErasures(rows,bank);
    if (!free.length && !shortcuts) { sink('packed', rows); return; }
    // Bound temporary state on large blocks. The bank was checked against
    // the entire primitive and every interval releases its borrowed site.
    for (let start=0; start<rows.length; start+=4096) {
        const end = Math.min(start+4096,rows.length);
        const values = new Map(), events = new Array(end-start);
        const written = new Int32Array(1024).fill(-1);
        for (let i=start; i<end; i++) {
            const g=rows[i], t=g&1023;
            let a=g>>>20, b=g>>>10&1023;
            if (a!==NONE && b!==NONE && !(shortcuts&&shortcuts[i])) {
                if (a>b) [a,b]=[b,a];
                const key = a*1024+b;
                let value = values.get(key);
                if (!value || written[a]>=value.first || written[b]>=value.first) {
                    value={a,b,first:i,last:i,count:0,loan:-1};
                    values.set(key,value);
                }
                value.last=i;
                value.count++;
                events[i-start]=value;
            }
            written[t]=i;
        }
        let pending=[];
        const flush=()=>{if (pending.length) {sink('packed',pending);pending=[];}};
        for (let i=start; i<end; i++) {
            const g=rows[i], value=events[i-start];
            if (shortcuts&&shortcuts[i]===2) {
                flush();sink('hmr',[g&1023,RECORD]);sink('cphase',[g>>>20,g>>>10&1023,RECORD]);continue;
            }
            if (!value || value.count<(measured?2:3)) {pending.push(g);continue;}
            if (i===value.first && free.length) {
                value.loan=free.pop();
                pending.push(code(value.a,value.b,value.loan));
            }
            if (value.loan<0) {pending.push(g);continue;}
            pending.push(code(NONE,value.loan,g&1023));
            if (i===value.last) {
                if (measured) {
                    flush();
                    sink('hmr',[value.loan,RECORD]);
                    sink('cphase',[value.a,value.b,RECORD]);
                } else pending.push(code(value.a,value.b,value.loan));
                free.push(value.loan);
            }
        }
        flush();
    }
}

function nativeSource(s) {
    const enter='const measures=[];const C1=-2;';
    const gate='if(kind==="hmr"){measures[id]=tape.hmr(q);return;}';
    assert.equal(s.split(enter).length,2);
    assert.equal(s.split(gate).length,2);
    return s.replace(enter,enter+'let temporaryProduct=-1;').replace(gate,
        `if(id===${RECORD}&&typeof tape.retireFieldProduct==="function"){
            if(kind==="hmr"&&temporaryProduct<0){temporaryProduct=q;return;}
            if(kind!=="cphase"||temporaryProduct<0)throw Error("unmatched field product correction");
            tape.retireFieldProduct(q,map[buf[1]],temporaryProduct);temporaryProduct=-1;return;
        }`+gate);
}

function install(research,{measured=true,preprocess=false,direct=false,frameWindow=4096}={}) {
    const point=process.env.Q647_POINT_ADD || path.join(research,'q647-trim/donor');
    const owner=path.join(point,'construction/research/agents/midpoint-implicit-query-20261109/q651-ten-field');
    const emitter=require.resolve(path.join(owner,'i9-divide-walk-emitter.cjs'));
    const original=require(emitter);
    require.cache[emitter].exports={...original,wrap(pub){
        const walk=original.wrap(pub);
        return function(w,L,R,ws,dirty,back,sink){
            if (back || ws.aux===-1 || w.constructor.name!=='SectorReduced') return walk(...arguments);
            assert.equal(w.n,128);assert.equal(L[0],0);
            const bank=Array.from({length:114},(_,i)=>390+i);
            const occupied=new Set([...L,...R,...ws.tag,ws.sign,ws.fire,ws.tst,ws.aux,...dirty]);
            assert(bank.every(q=>!occupied.has(q)));
            let activeRows;
            const index=preprocess&&require(path.join(owner,'i9-divide-s3-u-peep-index.cjs')).createPeep(
                (a,b,t)=>activeRows.push(code(a,b,t)),{window:4096});
            const frame=preprocess&&require(path.join(owner,'i9-divide-s3-u-peep-frame2.cjs')).createPeep(index.gate,{window:frameWindow});
            return walk(w,L,R,ws,dirty,back,(k,rows)=>{
                assert.equal(k,'packed');
                if (preprocess) {
                    activeRows=[];
                    for(const g of rows)frame.gate(g>>>20,g>>>10&1023,g&1023);
                    frame.flush();index.flush();rows=activeRows;
                }
                share(rows,bank,sink,measured,direct);
            });
        };
    }};
    if (measured) {
        require('./writer.cjs').install(research);
        const stage=require(path.join(owner,'stage-map.cjs')), upper=stage.upper;
        stage.upper=(...args)=>nativeSource(upper(...args));
    }
}
module.exports={share,nativeSource,install,RECORD};
