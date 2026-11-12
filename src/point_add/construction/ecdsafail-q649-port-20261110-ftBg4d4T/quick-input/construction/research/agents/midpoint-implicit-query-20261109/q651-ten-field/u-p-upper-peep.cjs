'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('upper peep anchor '+a);s=s.replace(a,()=>b);};
 one('class PointFoldTape extends FoldTape{',`const S1CreatePeep=${require('./u-peep.cjs').createPeep.toString()};\nclass PointFoldTape extends FoldTape{`);
 one('super(logical,[],l.g);this.ids=',`super(logical,[],l.g);
        const original=output,peep=S1CreatePeep((a,b,z)=>original.out(a,b,z),{mode:'commute',window:4096});
        output=Object.create(original);output.out=peep.gate;this.s1Flush=peep.flush;
        for(const name of ['hmr','z'])output[name]=(...args)=>{peep.flush();const r=original[name](...args);peep.flush();return r;};
        output.cond=(mask,fn)=>{peep.flush();return original.cond(mask,()=>{fn();peep.flush();});};
        this.ids=`);
 one('}return ops;\n}\nfunction bracketMap', '}return [()=>t.s1Flush&&t.s1Flush(),...ops,()=>t.s1Flush&&t.s1Flush()];\n}\nfunction bracketMap');
 return s;
};
