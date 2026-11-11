'use strict';

// The export path takes no point or simulator input. It reuses the checked
// arithmetic construction to emit registers, all classical control gates,
// measurement feedback, and quantum X/CX/CCX gates in declaration order.
const fs=require('fs'),path=require('path'),crypto=require('crypto'),Module=require('module');
const {emitRegenerate}=require('../field/forward.cjs');
const {emitMultiplyWithSign657,emitDivideWithSign657}=require('../../../../agents/midpoint-implicit-query-20261109/field656-clean-lease/index.cjs');
const NONE=1023, EMPTY=65535;
function replaceOnce(s,from,to){
    const at=s.indexOf(from);if(at<0||s.indexOf(from,at+from.length)>=0)throw Error('ambiguous construction site: '+from);
    return s.slice(0,at)+to+s.slice(at+from.length);
}
function arithmetic(spanLog){
    const name=path.join(__dirname,'centered-point.cjs');
    let src=fs.readFileSync(name,'utf8');
    const digest=crypto.createHash('sha256').update(src).digest('hex');
    if(digest!==SOURCE_SHA)throw Error('wrong centered construction '+digest);
    src=replaceOnce(src,'inverse=null,policy=\'random\',extraEnable=false){','inverse=null,policy=\'random\',extraEnable=false,stream=null){');
    src=replaceOnce(src,'controls=compileOffsetControls(m,BigInt(delta),rows.map(r=>r.B)),',
        'controls=compileOffsetControls(m,BigInt(delta),rows.map(r=>r.B),stream?stream.classic:null),');
    src=replaceOnce(src,'const tape=new CompleteTape(width,states,0x69b17,policy,mask),',
        'const tape=stream?stream.start(Tape,width,controls):new CompleteTape(width,states,0x69b17,policy,mask),');
    src=replaceOnce(src,'if(b===C1)tape.z(q);else for(let i=0;i<tape.batches.length;i++)',
        'if(b===C1)tape.z(q);else if(tape.cz)tape.cz(q,b);else for(let i=0;i<tape.batches.length;i++)');
    src=replaceOnce(src,'for(let i=0;i<states.length;i++)for(let j=0;j<width;j++)if(states[i][j]!==wants[i][j])',
        'if(stream){stream.finish(controls,tape);return;}\n for(let i=0;i<states.length;i++)for(let j=0;j<width;j++)if(states[i][j]!==wants[i][j])');
    const entry=new Module(name,module);entry.filename=name;entry.paths=module.paths;
    if(spanLog){
        const {classes,decorate}=require('./span-log.cjs');
        entry.traceSpan=(label,rev,fn)=>spanLog.span(label,rev,fn);
        entry.traceDecorate=ctors=>decorate(ctors,entry.traceSpan);
        src=replaceOnce(src,'return {pointReference,exceptionTable,',
            'module.traceDecorate(['+classes.join(',')+']);\nreturn {pointReference,exceptionTable,');
        src=replaceOnce(src,'ops=upperSteps(t,m,delta,l,logical);stepList(ops,false,fn=>fn(false));',
            'ops=upperSteps(t,m,delta,l,logical);module.traceSpan("upper.forward",false,()=>stepList(ops,false,fn=>fn(false)));');
        src=replaceOnce(src,'stepList(ops,true,fn=>fn(true));if(t.hist.size)',
            'module.traceSpan("upper.reverse",true,()=>stepList(ops,true,fn=>fn(true)));if(t.hist.size)');
        src=replaceOnce(src,'function nativeSink(tape,map){','function baseNativeSink(tape,map){');
        src=replaceOnce(src,'function rationalBackend(emitter,inverse,extraEnable=false)',
            'function nativeSink(tape,map){const send=baseNativeSink(tape,map);return(kind,data)=>kind==="packed"||kind==="nct"?module.traceSpan("field."+kind,false,()=>send(kind,data)):send(kind,data);}\nfunction rationalBackend(emitter,inverse,extraEnable=false)');
    }
    entry._compile(src,name);return entry.exports;
}
const SOURCE_SHA='10790de4c79338419f92a5a2fd72017c829fc94900fe053627884cddc568283a';
class GateWriter {
    constructor(filename,spanPath) {
        this.file=filename===null?null:fs.openSync(filename,'wx');this.buf=new Uint16Array(4*65536);this.n=0;this.total=0;
        if(spanPath){const {SpanLog}=require('./span-log.cjs');this.log=new SpanLog(spanPath,()=>this.total);this.hash=crypto.createHash('sha256');}
        this.kinds=Array(19).fill(0);this.classicalPeak=512;this.quantumWidth=657;
    }
    emit(kind,a=EMPTY,b=EMPTY,c=EMPTY) {
        const i=this.n;this.buf[i]=kind;this.buf[i+1]=a;this.buf[i+2]=b;this.buf[i+3]=c;
        this.n+=4;this.total++;this.kinds[kind]++;if(this.n===this.buf.length)this.flush();
    }
    flush() {
        const chunk=Buffer.from(this.buf.buffer,0,2*this.n);
        if(this.hash)this.hash.update(chunk);
        if(this.file!==null){let offset=0;while(offset<chunk.length)offset+=fs.writeSync(this.file,chunk,offset,chunk.length-offset);}
        this.n=0;
    }
    registers() {
        for(let r=0;r<4;r++){this.emit(1,r);for(let j=0;j<256;j++)this.emit(r<2?2:18,r,(r%2)*256+j);}
    }
    hooks(){
        const w=this;
        const classic=(op,t,c)=>{
            if(op===3) w.emit(15,c);
            else if(op===4) w.emit(16);
            else w.emit([4,5,3][op],t,c<0?EMPTY:c);
        };
        return {classic,start(Tape,width,controls){
            if(width!==657)throw Error('wrong native width');
            w.emit(15,controls.plan.finite);
            return new class extends Tape{
                constructor(){super(width,[],null,NONE);this.firstBit=controls.peak;this.nextBit=this.firstBit;}
                out(a,b,t){
                    if(t>=width||t===a||t===b||(a!==NONE&&(a>=width||a===b))||(b!==NONE&&b>=width))throw Error('bad quantum port');
                    if(a!==NONE)w.emit(13,a,b,t);else if(b!==NONE)w.emit(8,b,t);else w.emit(6,t);
                }
                classical(key,i,ctrl,t){const bit=controls.ports[key][i];
                    if(ctrl===null)w.emit(6,t,bit);else w.emit(8,ctrl,t,bit);}
                hmr(q){const b=this.nextBit++;if(b>=EMPTY)throw Error('measurement index overflow');w.emit(12,q,b);return b;}
                z(q){w.emit(7,q);}
                cz(q1,q2){w.emit(9,q1,q2);}
                cond(bit,fn){w.emit(15,bit);fn();w.emit(16);}
            };
        },finish(controls,tape){
            w.emit(16);
            for(let i=tape.firstBit;i<tape.nextBit;i++)w.emit(4,i);
            controls.release();w.classicalPeak=tape.nextBit;
        }};
    }
    produce(){
        this.registers();
        const wrap=(label,operator)=>!this.log?operator:(...args)=>this.log.span(label,false,()=>operator(...args));
        arithmetic(this.log).shellWithFieldOracles(256,(1n<<32n)+977n,[],false,
            {forward:wrap('short.multiply',emitMultiplyWithSign657),regenerate:wrap('history.regenerate',emitRegenerate)},
            wrap('short.divide',emitDivideWithSign657),'random',false,this.hooks());
        this.flush();if(this.file!==null)fs.closeSync(this.file);if(this.log)this.log.close();
        return {kind:'Input-independent Q657 gate export',wordsPerOp:4,opWordBits:16,width:this.quantumWidth,
            classicalBits:this.classicalPeak,counts:this.kinds,ops:this.total,
            ...(this.hash?{traceSha256:this.hash.digest('hex'),spans:this.log.written}:{})};
    }
}
if(require.main===module) {
    if(require('os').endianness()!=='LE'||!process.argv[2])throw Error('supply an unused binary output path on a little-endian host');
    const spans=process.argv[2]==='--spans';
    if(spans&&!process.argv[3])throw Error('specify sidecar output path');
    console.log(JSON.stringify(new GateWriter(spans?null:process.argv[2],spans?process.argv[3]:undefined).produce(),null,2));
}
module.exports={arithmetic,GateWriter};
