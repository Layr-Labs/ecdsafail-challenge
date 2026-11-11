'use strict';
exports.select=w=>w.kind==='trial'&&w.args[0]===true&&w.k>=64&&w.k<=95?{evict:642,reason:'U42 30-state prefix codec'}:null;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U42 anchor '+a);s=s.replace(a,()=>b);};
 if(!s.includes('    u35Direction(tape){'))s=require('./i9-upper-u35-direction.cjs').upper(s);
 one('      if(!witness&&this.k<=112&&!this.u30Trial){',`      if(witness&&this.k>=64&&this.k<=95&&!this.u42){
        const H=Object.create(this),tp=Object.create(tape);H.u42=true;H.u35DirectionOnly=true;
        tp.ids=tape.ids.filter(q=>q!==642);tp.loan=(used,n)=>tape.loan([...used,642],n);
        tp.out=(a,b,t)=>{if([a,b,t].includes(642))throw Error('U42 pick operand '+[this.k,a,b,t]);tape.out(a,b,t);};
        H.trial(tp,witness,back);return;
      }
      if(!witness&&this.k<=112&&!this.u30Trial){`);
 one('    u26Normalize(tape,back){','    u26Normalize(tape,back){\n      if(this.u42)return this.u42Normalize(tape,back);');
 one('    u26Tape(tape){','    u26Tape(tape){\n      if(this.u42)return this.u42Tape(tape);');
 one('H.tag[H.u26Code.l]=-2605;H.tag[H.u26Code.h]=-2606;',`H.tag[H.u26Code.l]=-2605;H.tag[H.u26Code.h]=-2606;
        if(H.u42){H.u42Code={c:H.u26Code.c,xyz:[H.n[7],H.n[8],H.n[14],H.n[15]]};H.tag[3]=-4203;H.tag[4]=-4204;H.tag[5]=-4205;}`);
 one('    u11Band(tape,B,back){','    u11Band(tape,B,back){\n      if(this.u42&&B.lo&&!this.u42High){const H=Object.create(this);H.u42High=true;H.u42Band=B;H.u11Band(tape,B,back);return;}');
 one('    roundedDivisor(tape,B,back){\n      if(this.u39LowOne===undefined)', '    roundedDivisor(tape,B,back){\n      if(this.u42High){const L=B.H.slice(0,-1);stepList([rv=>this.inc(tape,L,[],!rv),rv=>this.inc(tape,L.slice(1),[this.dv[1]],rv)],back,fn=>fn(back));return;}\n      if(this.u39LowOne===undefined)');
 one('    oddProduct(tape,T,D,ctrl,back){','    oddProduct(tape,T,D,ctrl,back){\n      if(this.u42High)return this.u42Product(tape,T,D,ctrl,back);');
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u42Add(tape,a,dest,base,back){
      const n=a.length,b=dest.slice(0,n),hi=dest.slice(n);
      if(!hi.length){tape.add(a,dest,base,this.pick,back);return;}
      if(hi.length===1){this.addTop(tape,a,dest,base,back);return;}
      if(hi.length!==2)throw Error('U42 add width');
      const d=tape.loan([...a,...dest,...base],1)[0],tp=Object.create(tape);tp.loan=(used,k)=>tape.loan([...used,d],k);
      const ops=[[NONE,a[n-1],d]];
      for(let i=1;i<n;i++)ops.push([NONE,a[i],b[i]]);
      for(let i=n-2;i>=1;i--)ops.push([NONE,a[i],a[i+1]]);
      for(let i=0;i<n-1;i++)ops.push([a[i],b[i],a[i+1]]);
      ops.push([a[n-1],b[n-1],d]);
      const mark=()=>{for(const op of ops)tp.out(...op);for(let i=ops.length-2;i>=1;i--)tp.out(...ops[i]);};
      const high=rv=>stepList([()=>this.toggle(tp,[...base,d,hi[0]],[],hi[1]),()=>this.toggle(tp,[...base,d],[],hi[0])],rv,body=>{body();mark();body();mark();});
      stepList([high,rv=>tp.add(a,b,base,this.pick,rv)],back,fn=>fn(back));
    }
    u42Product(tape,T,D,ctrl,back){
      const high=D.at(-1),L=D.slice(1,-1),w=D.length-1;
      stepList(split(0,T.length-1).reverse(),back,i=>{
        const body=rv=>this.uControl(tape,[...ctrl,T[i]],[],(tp,V)=>this.u42Add(tp,D.slice(1,Math.min(D.length-1,T.length-i)),T.slice(i+1),[V],rv));
        const overflow=rv=>{const tail=T.slice(i+w);if(!tail.length)return;const cs=[...ctrl,T[i],this.dv[1]];
          if(tail.length>2)throw Error('U42 overflow width');
          const seq=tail.length===2?[()=>this.toggle(tape,[...cs,tail[0]],L,tail[1]),()=>this.toggle(tape,cs,L,tail[0])]:[()=>this.toggle(tape,cs,L,tail[0])];stepList(seq,rv,fn=>fn());};
        stepList([body,overflow],back,fn=>fn(back));
      });
    }
    u42Normalize(tape,back){
      const C=this.u42Code,n=this.n,top=n.at(-1),q=this.tag[0],H=Object.create(this),[x,...rest]=C.xyz;
      H.tag=this.tag.slice();H.tag[5]=this.carry;H.tag[4]=C.c;H.tag[3]=q;H.tag[1]=q;
      const plain=(word,d,t,rv)=>this.permute(tape,word,word.slice(-d).concat(word.slice(0,-d)),[this.take,t],rv);
      const step=(j,rot,rv)=>{const d=1<<j,t=H.tag[j];stepList([()=>H.toggle(tape,[this.take],n.slice(-d),t),rr=>rot(n,d,t,rr)],rv,fn=>fn(rv));};
      const rotate=(word,d,t,rv)=>{
        const partial=word.filter(w=>w!==x),short=word.filter(w=>!C.xyz.includes(w));
        const rot=(ws,cs,rr)=>this.permute(tape,ws,ws.slice(-d).concat(ws.slice(0,-d)),cs,rr);
        stepList([()=>tape.out(NONE,NONE,C.c),rr=>rot(word,[this.take,t,C.c],rr),()=>tape.out(NONE,NONE,C.c),()=>tape.out(NONE,NONE,x),rr=>rot(partial,[this.take,t,C.c,x],rr),()=>tape.out(NONE,NONE,x),rr=>rot(short,[this.take,t,C.c,x],rr)],rv,fn=>fn(rv));
      };
      const high=rv=>stepList([5,4,3],rv,j=>step(j,plain,rv));
      const compress=rv=>{
        const ports=[q,C.c,this.carry,...C.xyz],input=[...Array.from({length:8},(_,a)=>1+16*a),2,3,4,5,6,7],output=[...Array.from({length:8},(_,a)=>2+16*a),...Array.from({length:6},(_,h)=>10+16*h)],pos=input.slice(),seq=[];
        for(let i=0;i<input.length;i++)if(pos[i]!==output[i]){const a=pos[i],b=output[i];seq.push([a,b]);for(let j=0;j<pos.length;j++)pos[j]=pos[j]===a?b:pos[j]===b?a:pos[j];}
        stepList(seq,rv,([a,b])=>this.u6Transpose(tape,ports,a,b,[this.take],[],rv));
      };
      const lower=rv=>stepList([2,1],rv,j=>step(j,rotate,rv));
      const last=rv=>stepList([()=>tape.out(NONE,this.take,top),rr=>this.permute(tape,[top,q],[q,top],[this.take],rr),rr=>rotate(n.slice(0,-1),1,q,rr),()=>this.toggle(tape,[this.take,q],[],n[0])],rv,fn=>fn(rv));
      stepList([high,compress,lower,last],back,fn=>fn(back));
    }
    u42Tape(tape){
      const H=this,C=this.u42Code,code=[C.c,...C.xyz],virtual=[-4203,-4204,-4205],frames=new Set(),tp=Object.create(tape);
      tp.loan=(used,n)=>tape.loan([...used,...code,642,647],n);
      const expr=q=>{if(!virtual.includes(q))return [{yes:q===NONE?[]:[q],no:[]}];const bit=virtual.indexOf(q),[x,y,z,w]=C.xyz,c=C.c;
        const out=bit===0?[{yes:[c],no:[x]},{yes:[c,x,y],no:[]}]:bit===1?[{yes:[c,x],no:[z]}]:[{yes:[c,x,w],no:[]},{yes:[c,x,z],no:[]}];
        if(frames.has(q))out.push({yes:[],no:[]});return out;};
      tp.out=(a,b,t)=>{
        if(virtual.includes(t)){if(a!==NONE||b!==NONE)throw Error('U42 virtual nonlinear write');if(frames.has(t))frames.delete(t);else frames.add(t);return;}
        if(code.includes(t))throw Error('U42 code collision '+[H.k,a,b,t]);
        if(!virtual.includes(a)&&!virtual.includes(b)){tape.out(a,b,t);return;}
        for(const A of expr(a))for(const B of expr(b)){const yes=[...new Set([...A.yes,...B.yes])],no=[...new Set([...A.no,...B.no])];if(!yes.some(q=>no.includes(q)))H.toggle(tape,yes,no,t);}
      };tp.u26Check=()=>{if(frames.size)throw Error('U42 unclosed rank frame');};return tp;
    }
`);
 return s;
};
