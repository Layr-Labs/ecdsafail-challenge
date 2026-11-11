'use strict';
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
const {implicitTopDigit}=require('./implicit-top.cjs');
function replace(s,a,b){if(s.split(a).length!==2)throw Error('hosted divider anchor '+a);return s.replace(a,()=>b);}
function hostedTypes(q,local){
    const code=fs.readFileSync(path.join(q,'multiply-nine.cjs'),'utf8');
    const reduced=local.D2Reduced(128,4).constructor;
    const originalMap=local.emitWalk.toString();
    const map=Function('return ('+replace(originalMap,'if(x===1023)return x;if(x===top)',
        'if(x===1023)return x;if(w.joinedHost&&x===w.tag.at(-2)){if(block.tagPort==null)throw Error("missing hosted tag");x=block.tagPort;}if(x===top)')+')')();
    function constantDigit(a,b,h,e){
        const pool=this.y;
        const tape={loan(used,n){const blocked=new Set(used);return pool.filter(q=>!blocked.has(q)).slice(0,n);},
            out:(a,b,t)=>a===1023?this.raw(b===1023?-1:b,-1,t):this.raw(a,b===1023?-1:b,t)};
        implicitTopDigit(tape,[...b,h],[...a,-1001],[e],false);
    }
    function addReducedTail(all){
        const n=this.n,l=this.L,r=this.R,active=[this.fire],push=fn=>all.push({fn,rev:false});
        for(let bits=1;bits<=n;bits++){
            const gap=n+1-bits,mark=()=>this.zer([r[n-bits+1]],r.slice(1,n-bits+1),this.fire);
            push(mark);push(()=>{for(let j=n;j>=gap;j--)this.swap(active,l[j],l[j+1]);});push(mark);
        }
        push(()=>{for(let j=n;j>=1;j--)this.swap([],r[j],r[j+1]);});
    }
    const start=code.indexOf('function hostWalk(pub,bits=6){'),stop=code.indexOf(';\n\nreturn module.exports;',start);
    if(start<0||stop<start)throw Error('hosted source boundaries');
    let s=code.slice(start,stop);
    s=replace(s,'const Base=pub.D2Canonical,flat=Object.getPrototypeOf(Base.prototype),unit=Object.getPrototypeOf(flat);',
        'const Base=isReduced?reduced:pub.D2Canonical,flat=Object.getPrototypeOf(Base.prototype),unit=isReduced?flat:Object.getPrototypeOf(flat);');
    s=replace(s,'constantDigit(a,b,h,e){eliminate(pub.dirtyDigit([...a,1001],b,h,e,this.y[0]),1001,(cs,z)=>this.op(cs,z));}',
        'constantDigit(a,b,h,e){return constantDigit.call(this,a,b,h,e);}');
    s=replace(s,'a.push(flat.plan.call(this).at(-1));return a;',
        'if(isReduced)addReducedTail.call(this,a);else if(appendCanonical)a.push(flat.plan.call(this).at(-1));return a;');
    s=replace(s,'if(this.tag.length<3)','this.joinedHost=true;if(this.tag.length<3)');
    const construct=(r,bits,append)=>Function('edit','isReduced','reduced','constantDigit','addReducedTail','appendCanonical','return ('+s+')')(replace,r,reduced,constantDigit,addReducedTail,append)(local,bits);
    return {canonical:construct(false,4,true),reduced:construct(true,5,false),signed:construct(false,5,false),map};
}
function build(q,mode='both',digitKind='alternating'){
    const published=require(path.join(q,'public-backend.cjs'));
    // The source transport is unchanged outside the two selected walks.
    const digit=digitKind==='shared'?require(path.join(q,'shared-digit.cjs')).sharedDigit:require(path.join(q,'alternating-digit.cjs')).alternatingDigit;
    const local=published.withDigit(digit);
    const T=hostedTypes(q,local);
    const merged={...local,emitWalk:T.map,
        D2Canonical:function(n,bits){return bits===12?new T.canonical(n):new local.D2Canonical(n,bits);},
        D2Reduced:function(n,bits){return bits===12?new T.reduced(n):new local.D2Reduced(n,bits);}};
    const base=path.join(q,'divide.cjs'),m=new Module(base,module);
    m.filename=base;m.paths=Module._nodeModulePaths(path.dirname(base));
    m.adjust=d=>{
        let s=require(path.join(q,'p-d5.cjs'))(d);
        if(mode!=='outer')s=replace(s,'emitWalk(new SectorCanonical(n,3),','emitWalk(new SectorCanonical(n,12),');
        if(mode!=='inner')s=replace(s,'emitWalk((()=>{const w=new Reduced(n,4);w.tag=w.tag.slice(0,4);return w;})(),','emitWalk(new Reduced(n,12),');
        return s;
    };
    const src=replace(fs.readFileSync(base,'utf8'),'const divide=Function(','d=module.adjust(d);const divide=Function(');
    m._compile(src,base);
    return m.exports.build(merged);
}
module.exports={build,hostedTypes};
