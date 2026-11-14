'use strict';
const fs=require('node:fs'),path=require('node:path'),Module=require('node:module');
const {hostedTypes}=require('./hosted-divide.cjs');
function edit(s,a,b){if(s.split(a).length!==2)throw Error('history host anchor '+a);return s.replace(a,()=>b);}
function build(q){
    const name=path.join(q,'regen.cjs'),src=fs.readFileSync(name,'utf8'),pub=require(path.join(q,'public-backend.cjs'));
    const local=pub.withDigit(require(path.join(q,'shared-digit.cjs')).sharedDigit),host=hostedTypes(q,local).signed;
    const m=new Module(name,module);m.filename=name;m.paths=Module._nodeModulePaths(q);
    m.patch=s=>{
        for(const [a,b] of require(path.join(q,'p-r650.js')))s=edit(s,a,b);
        s=edit(s,'walk=new Signed(n,4),walk6=new Signed(n,6)','walk=new Signed(n,5),walk6=new Signed(n,6)');
        s=edit(s,'walk.tag[3]=651;','walk.tag[3]=651;walk.tag[4]=652;');
        s=edit(s,'const port=q=>{if((g===walk||g===walk6)','const port=q=>{if(g===walk&&q===g.tag.at(-2)){if(block.tagPort==null)throw Error("missing hosted history tag");q=block.tagPort;}if((g===walk||g===walk6)');
        return s;
    };
    m.select=Walk=>class extends Walk{
        constructor(n,bits){if(bits===5)return new host(n);super(n,bits);}
    };
    let code=edit(src,'m.Walk=Walk;m.adjust=adjust;m._compile(text,material);','m.Walk=module.select(Walk);m.adjust=s=>module.patch(adjust(s));m._compile(text,material);');
    m._compile(code,name);return m.exports;
}
module.exports={build};
