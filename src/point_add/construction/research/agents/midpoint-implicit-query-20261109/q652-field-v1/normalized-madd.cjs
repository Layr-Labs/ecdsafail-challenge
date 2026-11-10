'use strict';
const {SectorSigned}=require('../q653-next/parts.cjs');

// A and B are canonical, M is normalized. Its known leading one holds
// the carry until B is canonical again.
function normalizedMadd(M,A,B){
    const high=M.at(-1),m=M.slice(0,-1),b=B.slice(0,-1),top=B.at(-1),g=[];
    const used=new Set([...M,...A,...B]),dirty=[];
    for(let q=0;dirty.length<4;q++)if(!used.has(q))dirty.push(q);
    const frame={
        raw(a,b,q){g.push(a<0?[q]:b<0?[a,q]:[a,b,q]);},
        op(c,q){
            if(c.length<=2){g.push([...c,q]);return;}
            const w=dirty.find(x=>!c.includes(x)&&x!==q);
            const tail=c.at(-1),prefix=c.slice(0,-1);
            this.op(prefix,w);this.op([w,tail],q);this.op(prefix,w);this.op([w,tail],q);
        },
    };
    const add=(c,a,b,h)=>SectorSigned.prototype.add.call(frame,c,a,b,null,h);
    const lt=(c,a,b,h)=>SectorSigned.prototype.lt.call(frame,c,a,b,h);
    function addModulus(c,carry){
        add(c,m,b,null);
        if(carry!==null){
            frame.op(c.concat(top),carry);
            frame.op([],top);lt(c.concat(top),m,b,carry);frame.op([],top);
        }
        frame.op(c,top);lt(c,m,b,top);
    }
    frame.op([],high);
    add([],A,B,high);
    const from=g.length;addModulus([],high);
    const down=g.splice(from).reverse();g.push(...down);
    addModulus([high],null);
    frame.op([],high);lt([],A,B,high);frame.op([],high);
    return g;
}
module.exports={normalizedMadd};
