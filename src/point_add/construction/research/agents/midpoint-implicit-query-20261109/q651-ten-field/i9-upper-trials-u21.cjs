'use strict';
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U26 anchor '+a);s=s.replace(a,()=>b);};
 one(' return layer;\n    }\n    // r36 U2:',` if(witness&&this.k<=95)layer.u26=true;
 return layer;
    }
    // r36 U2:`);
 one('low.packedShort=true;low.n=[-23,...packed.slice(0,-1)];work.n=packed.slice(0,-1);if(H.u39Trial){rank[1]=work.n.at(-1);}',`low.packedShort=true;low.n=[-23,...packed.slice(0,-1)];work.n=packed.slice(0,-1);if(H.u39Trial){rank[1]=work.n.at(-1);}
        if(H.u26){const code={c:rank.at(-2),x:work.n[14],y:work.n[15],h:rank.length-1,l:rank.length-2};low.u26Code=work.u26Code=code;rank[code.l]=-2605;rank[code.h]=-2606;}`);
 one('const norm=rv=>work.normalize(tape,rv),bias=rv=>this.inc(tape,rank,[],rv);',`const norm=rv=>work.normalize(tape,rv),bias=rv=>H.u26?work.u26Bias(tape,rv):this.inc(tape,rank,[],rv);`);
 one('      const H=this.uTrialRank(witness);\n      const steps=',`      const H=this.uTrialRank(witness);
      if(H.u26){H.u26Code={c:H.tag.at(-2),x:H.n[14],y:H.n[15],h:H.tag.length-1,l:H.tag.length-2};H.tag[H.u26Code.l]=-2605;H.tag[H.u26Code.h]=-2606;}
      const steps=`);
 one('    u39Normalize(tape,back){',`    u39Normalize(tape,back){
      if(this.u26){this.u26Normalize(tape,back);return;}`);
 one('    u11Band(tape,B,back){',`    u11Band(tape,B,back){
      if(this.u26&&!this.u26Band){const H=Object.create(this);H.u26Band=true;const tp=H.u26Tape(tape);H.u11Band(tp,B,back);tp.u26Check();return;}`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u26Normalize(tape,back){
      const C=this.u26Code,n=this.n,top=n.at(-1),q=this.tag[0],H=Object.create(this);
      H.tag=this.tag.slice();H.tag[C.h]=this.carry;H.tag[C.l]=C.c;H.tag[1]=q;
      const high=rv=>stepList([C.h,C.l],rv,j=>{
        const d=1<<j,t=H.tag[j],orig=n.slice(-d).concat(n.slice(0,-d));
        const seq=[()=>H.toggle(tape,[this.take],n.slice(-d),t),rr=>H.permute(tape,n,orig,[this.take,t],rr)];stepList(seq,rv,fn=>fn(rv));
      });
      const compress=rv=>stepList([[1,6],[3,10]],rv,([a,b])=>this.u6Transpose(tape,[this.carry,C.c,C.x,C.y],a,b,[this.take],[],rv));
      const rotate=(word,d,bit,rv)=>{
        const short=word.filter(w=>w!==C.x&&w!==C.y);
        const seq=[()=>tape.out(NONE,NONE,C.c),rr=>this.permute(tape,word,word.slice(-d).concat(word.slice(0,-d)),[this.take,bit,C.c],rr),()=>tape.out(NONE,NONE,C.c),rr=>this.permute(tape,short,short.slice(-d).concat(short.slice(0,-d)),[this.take,bit,C.c],rr)];
        stepList(seq,rv,fn=>fn(rv));
      };
      const lower=rv=>stepList(split(1,C.l).reverse(),rv,j=>{
        const d=1<<j,t=H.tag[j];const seq=[()=>H.toggle(tape,[this.take],n.slice(-d),t),rr=>rotate(n,d,t,rr)];stepList(seq,rv,fn=>fn(rv));
      });
      const low=n.slice(0,-1),last=rv=>{
        const seq=[()=>tape.out(NONE,this.take,top),rr=>this.permute(tape,[top,q],[q,top],[this.take],rr),rr=>rotate(low,1,q,rr),()=>this.toggle(tape,[this.take,q],[],low[0])];stepList(seq,rv,fn=>fn(rv));
      };
      stepList([high,compress,lower,last],back,fn=>fn(back));
    }
    u26Bias(tape,back){
      const C=this.u26Code,low=this.tag.slice(0,C.l),ports=[C.c,C.x,C.y];
      const high=rv=>stepList([[0,1],[0,3],[0,5]],rv,([a,b])=>this.u6Transpose(tape,ports,a,b,[this.take,...low],[],rv));
      stepList([high,rv=>this.inc(tape,low,[this.take],rv)],back,fn=>fn(back));
    }
    u26Tape(tape){
      const H=this,C=this.u26Code,frames=new Set(),code=[C.c,C.x,C.y],virtual=[-2605,-2606];
      const root=Object.create(tape);root.loan=(used,n)=>tape.loan([...used,...code,647],n);
      const tp=Object.create(root);
      const expr=q=>{
        if(!virtual.includes(q))return [{yes:q===NONE?[]:[q],no:[]}];
        const out=q===-2605?[{yes:[C.c],no:[C.x]}]:[{yes:[C.c,C.x],no:[]},{yes:[C.c,C.y],no:[]}];
        if(frames.has(q))out.push({yes:[],no:[]});return out;
      };
      tp.out=(a,b,t)=>{
        if(virtual.includes(t)){if(a!==NONE||b!==NONE)throw Error('U26 virtual rank non-X');if(frames.has(t))frames.delete(t);else frames.add(t);return;}
        if(code.includes(t))throw Error('U26 code touched in band '+[a,b,t]);
        if(!virtual.includes(a)&&!virtual.includes(b)){root.out(a,b,t);return;}
        for(const A of expr(a))for(const B of expr(b)){
          const yes=[...new Set([...A.yes,...B.yes])],no=[...new Set([...A.no,...B.no])];if(yes.some(q=>no.includes(q)))continue;
          H.toggle(root,yes,no,t);
        }
      };
      tp.u26Check=()=>{if(frames.size)throw Error('U26 rank frame not restored');};return tp;
    }
`);
 return s;
};
