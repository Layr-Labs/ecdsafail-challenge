'use strict';
const N=1023,LIMIT=512,SCAN=192,MAX_FAN=5;
const packed=(a,b,t)=>a<=b?(a<<20)|(b<<10)|t:(b<<20)|(a<<10)|t;
function engine(emit){
    const words=new Uint32Array(LIMIT*(2*MAX_FAN+1)+8),prev=new Uint16Array(words.length),next=new Uint16Array(words.length);
    const index=new Uint16Array(1<<20),keys=[],stats={pairs:0,cancelled:0};
    let tail=0,head=0,k=0,input=0;
    function insert(left,right,g){
        const node=++k;if(node>=words.length)throw Error('fusion buffer exceeded');
        words[node]=g;prev[node]=left;next[node]=right;
        if(left)next[left]=node;else head=node;
        if(right)prev[right]=node;else tail=node;return node;
    }
    function flush(){
        for(let n=head;n;n=next[n]){const g=words[n],a=g>>>20,b=g>>>10&N;emit(b===N?N:a,b===N?a:b,g&N);}
        for(const key of keys)index[key]=0;keys.length=0;k=head=tail=input=0;
    }
    function toggle(mask,q){const i=mask.indexOf(q);if(i<0)mask.push(q);else mask.splice(i,1);}
    // Compare two evaluations differing by a fixed output mask, conditional
    // on the recurring product a*b being one. Both controls then equal one.
    function transfer(h,a,b,t,back){
        const g=words[h],mask=[back?t:g&N],end=back?h:0;let n=back?tail:next[h],visited=0;
        while(n!==end){
            if(++visited>SCAN)return null;
            const z=words[n],x=z>>>20,y=z>>>10&N,q=z&N;
            if(q===a||q===b)return null;
            if(y===N){
                if(x!==N&&mask.includes(x))toggle(mask,q);
            }else{
                const dx=mask.includes(x),dy=mask.includes(y);
                if(dx||dy){
                    if(dx&&dy || dx&&y!==a&&y!==b || dy&&x!==a&&x!==b)return null;
                    toggle(mask,q);
                }
            }
            if(mask.length>MAX_FAN+2)return null;
            n=back?prev[n]:next[n];
        }
        toggle(mask,back?g&N:t);return mask.length<=MAX_FAN?mask:null;
    }
    function put(aa,bb,t){
        const a=Math.min(aa,bb),b=Math.max(aa,bb),g=packed(a,b,t);
        if(b===N)insert(tail,0,g);
        else{
            const key=a<<10|b,h=index[key];
            let mask=h?transfer(h,a,b,t,false):null,back=false;
            if(h&&(!mask||mask.length>2)){
                const other=transfer(h,a,b,t,true);
                if(other&&(!mask||other.length<mask.length)){mask=other;back=true;}
            }
            if(!mask){if(!h)keys.push(key);index[key]=insert(tail,0,g);}
            else{
                stats.pairs++;if(!mask.length)stats.cancelled++;
                const before=prev[h],after=next[h];
                if(before)next[before]=after;else head=after;
                if(after)prev[after]=before;else tail=before;
                let left=back?before:tail;const right=back?after:0;
                const add=g=>left=insert(left,right,g);
                if(!mask.length)index[key]=0;
                else{
                    const pivot=mask[0];
                    for(let i=1;i<mask.length;i++)add(packed(pivot,N,mask[i]));
                    add(packed(a,b,pivot));index[key]=left;
                    for(let i=mask.length-1;i>=1;i--)add(packed(pivot,N,mask[i]));
                }
            }
        }
        if(++input===LIMIT)flush();
    }
    return {put,flush,stats};
}
function install(tape){
    const e=engine(tape.out.bind(tape));
    for(const name of ['hmr','z','cz','classical'])if(tape[name]){
        const f=tape[name].bind(tape);tape[name]=(...args)=>{e.flush();return f(...args);};
    }
    const cond=tape.cond.bind(tape);tape.cond=(bit,fn)=>{e.flush();return cond(bit,()=>{fn();e.flush();});};
    tape.out=e.put;return e.flush;
}
module.exports={engine,install};
