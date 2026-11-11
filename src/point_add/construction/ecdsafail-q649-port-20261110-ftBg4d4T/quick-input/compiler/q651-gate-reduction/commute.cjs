'use strict';
const N=1023, BARRIER=0xffffffff;
const {reduceAffine}=require('./affine.cjs');
function record(a,b,t){
    if(a>b)[a,b]=[b,a];
    return (a<<20)|(b<<10)|t;
}
const cnot=(a,t)=>record(a,N,t);
// A gate is self-inverse. Disjoint targets and shared read-only controls commute.
function commutes(g,h){
    const t=g&1023,u=h&1023;
    return t!==(h>>>20)&&t!==((h>>>10)&1023)&&u!==(g>>>20)&&u!==((g>>>10)&1023);
}
function optimizeBlock(input,output,window=24){
    const buf=[];
    for(let j=0;j<input.length;j++){
        const word=input[j],a=word>>>20,b=(word>>>10)&1023,t=word&1023;
        if(word===BARRIER)throw Error('an NCT block cannot contain a barrier');
        const g=record(a,b,t),x=g>>>20,y=(g>>>10)&1023;
        let cancel=-1,fan=-1,cx=0;
        for(let i=buf.length-1,lim=Math.max(0,buf.length-window);i>=lim;i--){
            const prev=buf[i];
            if(prev===g){cancel=i;break;}
            if(!commutes(g,prev))break;
            if(fan>=0 || y===N)continue;
            const u=prev>>>20,v=(prev>>>10)&1023,z=prev&1023;
            if(v===N)continue;
            if(x===u&&y===v){
                fan=i;cx=cnot(z,t);
            }else if(z===t){
                if(x===u){fan=i;cx=cnot(y,v);}
                else if(x===v){fan=i;cx=cnot(y,u);}
                else if(y===u){fan=i;cx=cnot(x,v);}
                else if(y===v){fan=i;cx=cnot(x,u);}
            }
        }
        if(cancel>=0){buf.splice(cancel,1);continue;}
        if(fan>=0){const old=buf[fan];buf.splice(fan,1,cx,old,cx);continue;}
        buf.push(g);
    }
    for(const g of reduceAffine(buf))output.push(g);
}
function optimizeStream(emit,sink,options={}){
    const block=[],limit=options.block||128,window=options.window||24;
    let buffered=[];
    function flush(){
        if(block.length){optimizeBlock(block,buffered,window);block.length=0;}
        if(buffered.length>=65536){sink('packed',buffered);buffered=[];}
    }
    function put(g){block.push(g);if(block.length===limit)flush();}
    emit((kind,data)=>{
        if(kind==='packed'){for(const g of data)put(g);}
        else if(kind==='nct'){for(const g of data)put(record(g.length===1?N:g[0],g.length===3?g[1]:N,g.at(-1)));}
        else{
            flush();if(buffered.length){sink('packed',buffered);buffered=[];}
            sink(kind,data);
        }
    });
    flush();if(buffered.length)sink('packed',buffered);
}
module.exports={optimizeBlock,optimizeStream,record,N,BARRIER,commutes};
