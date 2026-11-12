'use strict';
const N=1023, WORD=262144, LIMIT=65536;
// A value is an exact Boolean expression, with its complement in bit zero.
// Atom zero denotes false. A fresh atom discards information conservatively.
class Values {
    constructor(width,cleanFrom,limit=LIMIT){
        this.width=width;this.limit=limit;
        this.type=new Uint8Array(LIMIT+32);
        this.left=new Int32Array(LIMIT+32);this.right=new Int32Array(LIMIT+32);
        this.rep=new Int16Array(LIMIT+32).fill(-1);
        this.prev=new Int16Array(width).fill(-1);this.next=new Int16Array(width).fill(-1);
        this.w=new Int32Array(width);this.used=0;
        this.parities=new Map();this.products=new Map();this.stack=[];
        for(let i=0;i<width;i++)this.put(i,i<cleanFrom?this.atom():0,true);
    }
    atom(){const id=++this.used;this.type[id]=0;return id*2;}
    put(w,value,first=false){
        if(!first){
            const old=this.w[w];if(old===value)return;
            const prev=this.prev[w],next=this.next[w];
            if(prev<0)this.rep[old>>>1]=next;else this.next[prev]=next;
            if(next>=0)this.prev[next]=prev;
        }
        this.w[w]=value;
        const head=this.rep[value>>>1];this.prev[w]=-1;this.next[w]=head;
        if(head>=0)this.prev[head]=w;this.rep[value>>>1]=w;
    }
    rebase(){
        const renumber=new Map([[0,0]]);this.used=0;this.parities.clear();this.products.clear();this.rep.fill(-1);
        const fresh=v=>{
            let x=renumber.get(v>>>1);
            if(x===undefined){x=this.atom();renumber.set(v>>>1,x);}
            return x^(v&1);
        };
        for(const prior of this.stack)for(let i=0;i<this.width;i++)prior[i]=fresh(prior[i]);
        for(let i=0;i<this.width;i++)this.put(i,fresh(this.w[i]),true);
    }
    room(){if(this.used>=this.limit)this.rebase();}
    bind(kind,a,b){
        if(a>b)[a,b]=[b,a];
        const table=kind===1?this.parities:this.products,key=a*WORD+b;
        let value=table.get(key);
        if(value===undefined){
            const id=++this.used;value=2*id;this.type[id]=kind;this.left[id]=a;this.right[id]=b;table.set(key,value);
        }
        return value;
    }
    xor(a,b){
        const sign=(a^b)&1;a&=~1;b&=~1;
        if(!a||!b||a===b)return a^b^sign;
        for(let i=0;i<2;i++){
            const v=i?a:b,u=i?b:a,id=v>>>1;
            if(this.type[id]===1){
                if(this.left[id]===u)return this.right[id]^sign;
                if(this.right[id]===u)return this.left[id]^sign;
            }
        }
        return this.bind(1,a,b)^sign;
    }
    and(a,b,distribute=true){
        if(a===0||b===0||(a^b)===1)return 0;
        if(a===1||a===b)return b;
        if(b===1)return a;
        for(let i=0;i<2;i++){
            const v=i?a:b,u=i?b:a,id=v>>>1,kind=this.type[id];
            const l=this.left[id],r=this.right[id];
            if(kind===2){
                if(l===u||r===u)return v&1?this.xor(u,v^1):v;
                if((l^u)===1||(r^u)===1)return v&1?u:0;
            }
            if(kind===1&&distribute&&((l^u)<=1||(r^u)<=1)){
                const product=this.xor(this.and(u,l,false),this.and(u,r,false));
                return v&1?this.xor(product,u):product;
            }
        }
        return this.bind(2,a,b);
    }
    other(value,target){
        const w=this.rep[value>>>1];return w===target?this.next[w]:w;
    }
    // Substitute an already available predicate, or two terms of its XOR.
    // Every replacement only uses controls whose values it preserves.
    gate(a,b,t,emit){
        this.room();
        if(a===N&&b===N){emit(N,N,t);this.put(t,this.w[t]^1);return;}
        if(a===N||b===N){
            const c=a===N?b:a,p=this.w[c];
            if(p===0)return;
            if(p===1)emit(N,N,t);else emit(N,c,t);
            this.put(t,this.xor(this.w[t],p));return;
        }
        const p=this.and(this.w[a],this.w[b]);if(!p)return;
        if(p===1)emit(N,N,t);
        else{
            const w=this.other(p,t),id=p>>>1;
            if(w>=0){emit(N,w,t);if(this.w[w]!==p)emit(N,N,t);}
            else if(this.type[id]===1){
                const l=this.left[id],r=this.right[id],x=this.other(l,t),y=this.other(r,t);
                if(x>=0&&y>=0){
                    emit(N,x,t);emit(N,y,t);
                    if((p^this.w[x]^this.w[y])&1)emit(N,N,t);
                }else emit(a,b,t);
            }else emit(a,b,t);
        }
        this.put(t,this.xor(this.w[t],p));
    }
    unknown(q){this.room();this.put(q,this.atom());}
    push(){this.stack.push(this.w.slice());}
    pop(){
        const old=this.stack.at(-1);
        for(let i=0;i<this.width;i++)if(old[i]!==this.w[i])this.unknown(i);
        this.stack.pop();
    }
}
function install(tape,cleanFrom){
    const v=new Values(tape.n,cleanFrom),out=tape.out.bind(tape),hmr=tape.hmr.bind(tape),
        cond=tape.cond.bind(tape),classic=tape.classical.bind(tape);
    tape.out=(a,b,t)=>v.gate(a,b,t,out);
    tape.hmr=q=>{const result=hmr(q);v.put(q,0);return result;};
    tape.cond=(c,fn)=>cond(c,()=>{v.push();try{return fn();}finally{v.pop();}});
    tape.classical=(key,i,c,t,views)=>{
        if(c!==null&&v.w[c]===0)return;
        classic(key,i,c,t,views);v.unknown(t);
    };
}
module.exports={Values,install};
