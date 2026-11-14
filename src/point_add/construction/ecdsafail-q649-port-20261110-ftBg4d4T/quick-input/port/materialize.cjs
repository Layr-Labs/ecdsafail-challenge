'use strict';

function leaseCoefficient(owner, tape, v, bit, run) {
    const carrier=owner.q649Loan===undefined?owner.pick:owner.q649Loan, source=v[bit];
    if(carrier===null){return run(owner.u6VirtualTape(tape));}
    if (source === undefined || owner.u40Tag.includes(carrier) || v.includes(carrier)) throw Error('Q649 coefficient lease collision');
    if (tape.q649Observe) tape.q649Observe(carrier,owner,'before');
    const cleanTape=Object.create(tape);
    cleanTape.ids=tape.ids.filter(q=>q!==carrier);
    const decoded=owner.u6VirtualTape(cleanTape), material=Object.create(decoded);
    const wire=q=>q===source?carrier:q;
    material.out=(a,b,t)=>decoded.out(wire(a),wire(b),wire(t));
    decoded.out(1023,source,carrier);
    run(material);
    decoded.out(1023,source,carrier);
    if (tape.q649Observe) tape.q649Observe(carrier,owner,'after');
}

function install(source, one, options) {
    const marker='class Tape {';
    source=one(source,marker,leaseCoefficient.toString()+'\n'+marker);
    const entry='    mixed(tape,q,v,rem,controls,back){\n      super.mixed(this.u40Tag';
    let bit=options.has('leasezero')?'0':'1';
    if(options.has('leasethree'))bit='(this.u9Three?2:1)';
    source=one(source,entry,'    mixed(tape,q,v,rem,controls,back){\n      if(this.u6Code&&v[0]===this.u40Low&&!controls.length){\n        leaseCoefficient(this,tape,v,'+bit+',tp=>super.mixed(tp,q,v,rem,controls,back));return;\n      }\n      super.mixed(this.u40Tag');
    if(options.has('leaseadd')){
        const line='rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv)';
        if(source.split(line).length!==3)throw Error('Q649 U6/U9 plain adder');
        source=source.split(line).join('rv=>leaseCoefficient(H,tape,a,'+bit.replace('this.u9Three','H.u9Three')+',tp=>tp.add(a,D,[],this.carry,rv)),rv=>H.alignedMix(tape,a,D,tag,rv)');
    }
    if(options.has('f1')){
        const seq='stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));\n      for(const tp of H.u6Tapes)tp.u6Check();';
        if(source.split(seq).length!==3)throw Error('Q649 U6/U9 sign boundary');
        source=source.split(seq).join('const known=this.u5PhaseHost!==target&&target===this.dv[0]&&(this.measureTarget===target||!this.probeBack);H.q649Loan=known?target:null;stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);H.q649Loan=known&&this.measureTarget===target?target:null;stepList(seq,true,fn=>fn(true));\n      for(const tp of H.u6Tapes)tp.u6Check();');
    }
    if(options.has('audit')){
        const marker='this.toGlobal=x=>map[x>l.g?x-1:x];';
        const observe=`this.q649Observe=(q,owner,side)=>{
          if(!original.batches||!original.batches.length)return;
          if(this.endUpper)this.endUpper();this.s1Flush();
          for(let i=0;i<original.batches.length;i++){
            let active=original.current===null?original.valid[i]:original.current[i]&original.valid[i];
            for(const control of owner.ctrl){
              if(control===owner.g)continue;
              if(control<0||this.toGlobal(control)===undefined)throw Error('Q649 unsupported probe guard '+control);
              active&=original.batches[i][this.toGlobal(control)];
            }
            if((original.batches[i][this.toGlobal(q)]&active)!==0)throw Error('Q649 enabled probe loan one '+[owner.k,side,q,i,active>>>0,original.batches[i][this.toGlobal(q)]]);
          }
          globalThis.q649LoanChecks=(globalThis.q649LoanChecks||0)+1;
        };`;
        source=one(source,marker,marker+observe);
    }
    return source;
}
module.exports={leaseCoefficient, install};
