'use strict';
exports.wholeStageFreed=false;
exports.select=w=>w.kind==='trial'&&w.args[0]===true&&w.k<=63?{evict:642,reason:'U38 original-band triple high rank'}:null;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U38 anchor '+a);s=s.replace(a,()=>b);};
 one('    trial(tape,witness,back){\n      if(witness&&this.k<=112&&!this.u35DirectionOnly){',`    trial(tape,witness,back){
      if(witness&&this.k<=63&&!this.u38Early){
        const H=Object.create(this),tp=Object.create(tape);H.u38Early=true;
        tp.ids=tape.ids.filter(q=>q!==642);tp.loan=(used,n)=>tape.loan([...used,642],n);
        tp.out=(a,b,t)=>{if([a,b,t].includes(642))throw Error('U38 pick operand '+[this.k,a,b,t]);tape.out(a,b,t);};
        H.trial(tp,witness,back);return;
      }
      if(witness&&this.k<=112&&!this.u35DirectionOnly){`);
 one('    u26Normalize(tape,back){','    u26Normalize(tape,back){\n      if(this.u38Early)return this.u38Normalize(tape,back);');
 one('    u26Bias(tape,back){','    u26Bias(tape,back){\n      if(this.u38Early)return this.u38Bias(tape,back);');
 one('    u26Tape(tape){','    u26Tape(tape){\n      if(this.u38Early)return this.u38Tape(tape);');
 one('low.u26Code=work.u26Code=code;rank[code.l]=-2605;rank[code.h]=-2606;',`low.u26Code=work.u26Code=code;rank[code.l]=-2605;rank[code.h]=-2606;
          if(H.u38Early){low.u38Code=work.u38Code={c:code.c,xyz:work.n.slice(8,11)};rank[3]=hi;rank[4]=-3804;rank[5]=-3805;rank[6]=-3806;}`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u38Normalize(tape,back){
      const C=this.u38Code,n=this.n,top=n.at(-1),q=this.tag[0],H=Object.create(this);
      H.tag=this.tag.slice();H.tag[6]=this.carry;H.tag[5]=C.c;H.tag[4]=q;H.tag[1]=q;
      const plain=(word,d,t,rv)=>this.permute(tape,word,word.slice(-d).concat(word.slice(0,-d)),[this.take,t],rv);
      const step=(j,rot,rv)=>{const d=1<<j,t=H.tag[j];stepList([()=>H.toggle(tape,[this.take],n.slice(-d),t),rr=>rot(n,d,t,rr)],rv,fn=>fn(rv));};
      const rotate=(word,d,t,rv)=>{
        const short=word.filter(w=>!C.xyz.includes(w));
        stepList([()=>tape.out(NONE,NONE,C.c),rr=>this.permute(tape,word,word.slice(-d).concat(word.slice(0,-d)),[this.take,t,C.c],rr),()=>tape.out(NONE,NONE,C.c),rr=>this.permute(tape,short,short.slice(-d).concat(short.slice(0,-d)),[this.take,t,C.c],rr)],rv,fn=>fn(rv));
      };
      const high=rv=>stepList([6,5,4],rv,j=>step(j,plain,rv));
      const compress=rv=>{
        const ports=[q,C.c,this.carry,...C.xyz],input=Array.from({length:7},(_,i)=>i+1),output=input.map(r=>2+8*(r-1)),pos=input.slice(),seq=[];
        for(let i=0;i<7;i++)if(pos[i]!==output[i]){const a=pos[i],b=output[i];seq.push([a,b]);for(let j=0;j<7;j++)pos[j]=pos[j]===a?b:pos[j]===b?a:pos[j];}
        stepList(seq,rv,([a,b])=>this.u6Transpose(tape,ports,a,b,[this.take],[],rv));
      };
      const lower=rv=>stepList([3,2,1],rv,j=>step(j,rotate,rv));
      const last=rv=>stepList([()=>tape.out(NONE,this.take,top),rr=>this.permute(tape,[top,q],[q,top],[this.take],rr),rr=>rotate(n.slice(0,-1),1,q,rr),()=>this.toggle(tape,[this.take,q],[],n[0])],rv,fn=>fn(rv));
      stepList([high,compress,lower,last],back,fn=>fn(back));
    }
    u38Bias(tape,back){
      const C=this.u38Code,low=this.tag.slice(0,4),ports=[C.c,...C.xyz];
      const high=rv=>stepList([1,3,5,7,9,11,13],rv,b=>this.u6Transpose(tape,ports,0,b,[this.take,...low],[],rv));
      stepList([high,rv=>this.inc(tape,low,[this.take],rv)],back,fn=>fn(back));
    }
    u38Tape(tape){
      const H=this,C=this.u38Code,code=[C.c,...C.xyz],virtual=[-3804,-3805,-3806],frames=new Set(),tp=Object.create(tape);
      tp.loan=(used,n)=>tape.loan([...used,...code,642,647],n);
      const expr=q=>{if(!virtual.includes(q))return [{yes:q===NONE?[]:[q],no:[]}];const bit=virtual.indexOf(q),[x,y,z]=C.xyz;
        // h=(xyz)+1: h0=!x, h1=x XOR y, h2=z XOR xy.
        // These are XOR polynomials, including overlapping terms.
        const out=bit===0?[{yes:[C.c],no:[x]}]:bit===1?[{yes:[C.c,x],no:[]},{yes:[C.c,y],no:[]}]:[{yes:[C.c,z],no:[]},{yes:[C.c,x,y],no:[]}];
        if(frames.has(q))out.push({yes:[],no:[]});return out;};
      tp.out=(a,b,t)=>{
        if(virtual.includes(t)){if(a!==NONE||b!==NONE)throw Error('U38 virtual nonlinear write');if(frames.has(t))frames.delete(t);else frames.add(t);return;}
        if(code.includes(t))throw Error('U38 original-band code collision '+[H.k,a,b,t]);
        if(!virtual.includes(a)&&!virtual.includes(b)){tape.out(a,b,t);return;}
        for(const A of expr(a))for(const B of expr(b)){const yes=[...new Set([...A.yes,...B.yes])],no=[...new Set([...A.no,...B.no])];if(!yes.some(q=>no.includes(q)))H.toggle(tape,yes,no,t);}
      };tp.u26Check=()=>{if(frames.size)throw Error('U38 unclosed rank frame');};return tp;
    }
`);
 return s;
};
