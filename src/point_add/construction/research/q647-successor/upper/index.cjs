'use strict';

// The reverse U43 product adds src into the equally wide suffix dst, enabled
// by a preceding digit. Its top is write-only. Use the existing ancilla-free
// controlled ripple for physical addends; the virtual-register compiler keeps
// ownership of the other terms and the virtual top's guarded deposits.
function patch(source){
    const first=source.indexOf('    u43HighWitness(tape,B,back){'),last=source.indexOf('\n    u42Add(',first);
    if(first<0||last<=first)throw Error('Q647 U43 witness source');
    let part=source.slice(first,last);
    function once(was,now){if(part.split(was).length!==2)throw Error('Q647 ripple source '+was);part=part.replace(was,()=>now);}
    const run='const run=(ops,rv)=>stepList(ops,rv,o=>apply(o.yes,o.no,o.t));';
    once(run,`const protectedWires=new Set([host,x,y,top,flag,target,H.g,H.take,642]);
      const ripple=(o,rv)=>{
        const {src,dst,bit}=o;
        const modified=dst.slice(0,-1),all=src.concat(modified,bit);
        // The virtual divisor expressions must have the same physical inputs
        // at the end. Source and enable are restored by the whole ripple.
        const valid=src.length===dst.length&&dst.at(-1)===topT&&
          all.every(q=>q>=0&&!protectedWires.has(q))&&new Set(all).size===all.length&&
          [...vals.values()].every(e=>support(e).every(q=>q!==target&&!modified.includes(q)));
        if(!valid){
          const slow=[];for(let j=0;j<src.length;j++)slow.push(...incOps(dst.slice(j),[bit,src[j]]));
          stepList(slow,rv,k=>apply(k.yes,k.no,k.t));return;
        }
        tape.q647ProductPrice?.(H.k,src.length,rv);
        const proxy=Object.create(tape);
        proxy.out=(a,b,z)=>{
          if(a===topT||b===topT)throw Error('U43 ripple reads virtual top');
          if(z!==topT){tape.out(a,b,z);return;}
          if(!deposit)return;
          const cs=[...new Set([H.g,H.take,host,a,b].filter(q=>q!==NONE))];
          H.toggle(raw,cs,[],target);
        };
        MixedArithmetic.prototype.nrAdder.call(H,proxy,src,dst,null,bit,rv);
      };
      const run=(ops,rv)=>stepList(ops,rv,o=>o.src?ripple(o,rv):apply(o.yes,o.no,o.t));`);
    once('for(let j=0;j<src.length;j++)pre.push(...incOps(dst.slice(j),[T[i],src[j]]));','pre.push({src,dst,bit:T[i]});');
    return source.slice(0,first)+part+source.slice(last);
}
function install(research){
    const path=require('node:path');
    require(path.join(research,'q648-frontier/grade/six-clean-trial.cjs'));
    const host=require(path.join(research,'q648-frontier/upper/six.cjs'));
    const before=host.patch;
    host.patch=(...args)=>patch(before(...args));
}
module.exports={patch,install};
