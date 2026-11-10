'use strict';

const fs=require('fs');
const classes=['WordArithmetic','MixedArithmetic','UnitPreparation','UniversalGeneral','TruncatedGeneral',
    'AlignedGeneral','SingleAffineGeneral','EarlyUnit','EarlyGeneral','OddEstimateGeneral','UnguardedGeneral',
    'HornerSquare','BlockConstant','CoordinateArithmetic','ClassicalProgram'];
const skip=new Set(['constructor','put','zero','one','flip','when','alloc','drop','copyBit','loan','layout',
    'layouts','topDivisor','makeBand','bands','gatedSwap','tagEqual','raw','free']);
function decorate(constructors,record) {
    for(const ctor of constructors){
        for(const name of Object.getOwnPropertyNames(ctor.prototype)){
            if(skip.has(name))continue;
            const old=ctor.prototype[name];if(typeof old!=='function')continue;
            const label=ctor.name+'.'+name;
            ctor.prototype[name]=function(...args){
                const rev=args[args.length-1]===true;
                return record(label,rev,()=>old.apply(this,args));
            };
        }
    }
}
class SpanLog{
    constructor(path,position){
        this.fd=fs.openSync(path,'wx');this.position=position;this.next=1;this.parent=0;this.rows=[];this.written=0;
    }
    span(name,reverse,fn){
        const start=this.position(),id=this.next++,parent=this.parent;
        this.parent=id;
        try{return fn();}finally{
            this.parent=parent;
            const end=this.position();
            if(end-start>=32){
                this.rows.push([id,parent,start,end,name,Number(reverse)].join('\t')+'\n');
                if(this.rows.length===32768)this.flush();
                this.written++;
            }
        }
    }
    flush(){if(this.rows.length)fs.writeFileSync(this.fd,this.rows.join(''));this.rows=[];}
    close(){this.flush();fs.closeSync(this.fd);}
}
module.exports={classes,decorate,SpanLog};
