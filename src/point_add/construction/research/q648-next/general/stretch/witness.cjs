'use strict';
// U11's virtual top is write-only. Accumulate it on an arbitrary dirty
// passenger, then use the guarded difference of its two physical values.
function dirtyTopWitness(o,tape,B){
    const top=-1101,T=B.T.slice(0,-1).concat(top),flag=o.dv[0],ctrl=[o.g,o.take,-19];
    const phase=o.measureTarget===flag,target=phase?o.zword.at(-1):flag;
    const hidden=[...o.tag,...o.tags,flag,target,o.take,o.g],busy=new Set([...T,...B.D,...hidden]);
    const scratch=o.zword.find(q=>!busy.has(q)&&tape.ids.includes(q));
    if(scratch===undefined)throw Error('Q648 witness needs a dirty spectator');
    tape.q648StretchWitness?.(scratch,o,B,phase);
    const tp=Object.create(tape),flips=new Set(),tags=new Set(o.tag),guards=[];
    tp.loan=(used,n)=>tape.loan([...used,...hidden,scratch],n);
    if(o.inUpperHalf)guards.push({yes:[o.g,o.take],no:[]});
    guards.push({yes:[o.g,o.take],no:o.tag.slice(3)});
    if(o.packedShort)guards.push({yes:[o.g,o.take,o.tag[3]],no:o.tag.filter((q,i)=>i!==3)});
    const observe=()=>{
        for(const guard of guards){
            const yes=[scratch],no=[];
            for(const q of guard.yes)(flips.has(q)?no:yes).push(q);
            for(const q of guard.no)(flips.has(q)?yes:no).push(q);
            if(!yes.some(q=>no.includes(q)))o.toggle(tape,[...new Set(yes)],[...new Set(no)],target);
        }
    };
    tp.out=(a,b,t)=>{
        if(a===top||b===top)throw Error('Q648 witness top read');
        if(a===scratch||b===scratch||t===scratch)throw Error('Q648 witness scratch alias');
        if(t===top){tape.out(a,b,scratch);return;}
        if(tags.has(t)){
            if(a!==NONE||b!==NONE)throw Error('Q648 witness rank mutation');
            if(flips.has(t))flips.delete(t);else flips.add(t);
        }
        tape.out(a,b,t);
    };
    const pre=[rv=>o.inc(tp,T,[],rv),rv=>o.oddProduct(tp,T,B.D,[],rv),rv=>o.lowReflect(tp,T,B.w,[],rv)];
    o.toggle(tape,ctrl,[],target);observe();
    stepList(pre,false,f=>f(false));observe();
    if(phase){tape.z(target);observe();}
    stepList(pre,true,f=>f(true));
    if(phase){observe();o.toggle(tape,ctrl,[],target);tape.z(target);tape.z(flag);}
    if(flips.size)throw Error('Q648 witness guard frame not restored');
}
function patch(source){
    const entry='    u11Predicate(tape,B){',start=source.indexOf(entry),end=source.indexOf('\n    }',start);
    if(start<0||end<start||source.indexOf(entry,start+1)>=0||source.split('class Tape {').length!==2)throw Error('Q648 virtual top source');
    const method=source.slice(start,end);
    if(!method.includes("if(a===top||b===top)throw Error('U11 virtual high read');")||!method.includes('if(deposit)accumulate(a,b);'))throw Error('Q648 virtual top contract');
    return (source.slice(0,start)+entry+'\n      dirtyTopWitness(this,tape,B);'+source.slice(end))
        .replace('class Tape {',()=>dirtyTopWitness.toString()+'\nclass Tape {');
}
module.exports={patch,dirtyTopWitness};
