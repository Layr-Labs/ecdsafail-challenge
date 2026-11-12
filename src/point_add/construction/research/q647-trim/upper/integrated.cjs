'use strict';
const path=require('node:path');
const sign=require('./index.cjs');
const affine=require('../../q648-trim/alternate/q647.cjs');
const {mixedKnownTop}=require('../../q649-record/upper/main.cjs');
const quick=path.resolve(__dirname,'../../../ecdsafail-q649-port-20261110-ftBg4d4T/quick-input');
const {portUpper}=require(path.join(quick,'port/port.cjs'));
const {leaseCoefficient}=require(path.join(quick,'port/materialize.cjs'));
function once(s,x,y,count=1){const a=s.split(x);if(a.length!==count+1)throw Error('Q647 integrated source '+x);return a.join(y);}
function otherAffine(owner,tape,layer,r,a,d,rv){
    const local=Object.create(layer);
    local.digit=(tp,z,v,on,back)=>{
        const target=owner.u12?owner.u12VirtualTape(tp):tp;
        cleanTop(target,z,v,on,owner.carry,back);
        if(owner.u12)target.u12Check();
    };
    return local.mixed(tape,r,a,d,[owner.take],rv);
}
function legacySign(s){
    const before='rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv)';
    const old='stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));';
    s=once(s,'class Tape {',leaseCoefficient.toString()+'\nclass Tape {');
    for(const method of ['u23Sign(inputTape,target){','u16Sign(inputTape,target){','u9ThreeSign(tape,target){','u6DoubleSign(tape,target){']){
        const begin=s.indexOf('    '+method),end=s.indexOf('\n    }',begin);
        if(begin<0||end<begin)throw Error('Q647 fallback probe '+method);
        let body=s.slice(begin,end);
        body=once(body,before,'rv=>leaseCoefficient(H,tape,a,1,tp=>tp.add(a,D,[],this.carry,rv))');
        const known='this.u5PhaseHost!==target&&target===this.dv[0]&&(this.measureTarget===target||!this.probeBack)&&!tag.includes(target)';
        body=once(body,old,`const known=${known};H.q649Loan=known?target:null;stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);H.q649Loan=known&&this.measureTarget===target?target:null;stepList(seq,true,fn=>fn(true));`);
        s=s.slice(0,begin)+body+s.slice(end);
    }
    const go='      super.mixed(this.u40Tag&&v[0]===this.u40Low?this.u40Tape(tape):tape,q,v,rem,controls,back);';
    return once(s,go,`      if(this.u6Code&&this.q649Loan!==undefined&&v[0]===this.u40Low&&!controls.length){leaseCoefficient(this,tape,v,1,tp=>super.mixed(tp,q,v,rem,controls,back));return;}\n`+go);
}
function patch(finalDonorUpper,compilerRoot=path.join(quick,'compiler'),mode='all'){
    if(!['all','joint','port','simple'].includes(mode))throw Error('Q647 integrated mode');
    let s=affine.patch(sign.patch(finalDonorUpper));
    if(mode==='joint')return s;
    const compiler=path.resolve(compilerRoot,'q650-joined-probes');
    for(const f of [require(path.join(compiler,'implicit-top.cjs')).implicitTopDigit,require(path.join(compiler,'wide.cjs')).sharedRippleTail]){
        if(!s.includes(f.toString()))throw Error('Q647 already-installed arithmetic mismatch for '+f.name);
    }
    for(const pattern of ['if(v.length>=8){implicitTopDigit(','function sharedControlledPermutation(',"throw Error('U37 omitted role '","throw Error('U37 strict647 first physical '"]){
        if(!s.includes(pattern))throw Error('Missing Q647 donor geometry '+pattern);
    }
    // A provisional helper can survive in the logical dirty pool even while
    // the physical allocator lends its site to role 646. Exclude the live
    // eviction in the base lender. Views that override loan still delegate
    // to this base, preserving both their own bans and the active frame.
    const blocked='const bad=new Set([...used,this.guard]);';
    s=once(s,blocked,"const bad=new Set([...used,this.guard]);if(this.u37Control)bad.add(this.u37Control.frame);");
    s=require(path.join(compiler,'increment.cjs')).patchIncrement(s);
    s=portUpper(s,compiler,new Set(['code','codetrans','prefix']));
    s=once(s,'tag.slice(exceptionalPrefix(free,bits))','tag.slice(exceptionalPrefix(free,tag.length))');
    const start='    tailDigit(tape,layer,z,S,back){';
    s=once(s,start,start+`\n      if(!this.u6Code){const cut=this.r.indexOf(z.at(-1))-this.ab+1;if(cut<1||cut>=S.length)throw Error('Q647 probe cropped divisor');z=z.slice(cut);S=S.slice(cut);}`);
    // Both affine tail branches in the public donor already slice the
    // arithmetic. Bypass its polynomial evaluator only after all virtual
    // coefficient bits have fallen outside the cropped native digit.
    const digit='rr=>layer.digit(tape,z.slice(cut),a.slice(cut),[t],!rr)';
    s=once(s,digit,`rr=>{const h=this.u36?1+this.u36Bits:this.u22?4:2,v=a.slice(cut),w=z.slice(cut);if(this.u12&&cut>=h){const plain=Object.create(layer);plain.u12=false;plain.digitTopOne(tape,w,v,[t],!rr);}else layer.digit(tape,w,v,[t],!rr);}`);
    if(mode==='simple')return s;
    s=once(s,'class Tape {',[otherAffine,mixedKnownTop].map(f=>f.toString()).join('\n')+'\nclass Tape {');
    s=once(s,'if(!owner.u36)return layer.mixed(t,r,a,d,[owner.take],back);','if(!owner.u36)return otherAffine(owner,t,layer,r,a,d,back);');
    s=once(s,'layer.mixed(tape,r,v,d,[this.take],!rr);','mixedKnownTop(this,tape,r,v,d,!rr);');
    if(mode==='port')return s;
    return legacySign(s);
}
module.exports={patch,quick};
