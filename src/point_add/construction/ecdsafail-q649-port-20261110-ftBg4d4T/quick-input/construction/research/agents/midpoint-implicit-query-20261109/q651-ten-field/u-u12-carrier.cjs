'use strict';
// Early affine only. Source overlay after U9; no emitted gate snapshots.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U12 anchor '+a);s=s.replace(a,()=>b);};
 one('H.u3Affine=true;H.u38Implicit=true;}','H.u3Affine=true;H.u38Implicit=true;H.u12=true;H.tag[0]=this.A[0];}');
 one('    normalizeTopLease(tape,a,back){','    normalizeTopLease(tape,a,back){\n        if(this.u12){this.u12Normalize(tape,a,back);return;}');
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u12Normalize(tape,a,back){
      const H=Object.create(this),carry=this.carry,top=a.at(-1),low=a[0],extra=a[1];
      H.tag=this.tag.slice();H.tag[1]=carry;
      const norm=rv=>stepList(split(1,H.tag.length).reverse(),rv,j=>{
        const k=1<<j,orig=a.slice(-k).concat(a.slice(0,-k)),bit=H.tag[j];
        const seq=[()=>H.toggle(tape,[H.take],a.slice(-k),bit),rr=>H.permute(tape,a,orig,[H.take,bit],rr)];stepList(seq,rv,fn=>fn(rv));
      });
      const last=rv=>{
        const lower=a.slice(0,-1),orig=lower.slice(-1).concat(lower.slice(0,-1));
        const seq=[rr=>this.permute(tape,[top,carry],[carry,top],[this.take],rr),()=>tape.out(NONE,this.take,carry),
          rr=>this.permute(tape,lower,orig,[this.take,carry],rr),()=>this.toggle(tape,[this.take,carry],[],low),
          rr=>this.permute(tape,[carry,low],[low,carry],[this.take],rr)];stepList(seq,rv,fn=>fn(rv));
      };
      const recode=rv=>{
        // Partial injection on [temporary,rank0,rank1,rank2,extra].
        // c0 -> extra1 + original low2; c1 -> extra1 + 4 + original low1.
        const map=new Map();
        for(let x=0;x<2;x++)for(let y=0;y<2;y++)map.set(x+16*y,16+2*x+4*y);
        for(let y=0;y<2;y++)map.set(2+16*y,16+8+2*y);
        for(let c=2;c<8;c++)map.set(2*c,2*c);
        // Close each open path to obtain a permutation, then decompose cycles.
        const incoming=new Set(map.values());
        for(const start of [...map.keys()])if(!incoming.has(start)){
          let at=start;while(map.has(at))at=map.get(at);map.set(at,start);
        }
        const seen=new Set(),swaps=[];
        for(const start of map.keys())if(!seen.has(start)){
          const cycle=[];let at=start;while(!seen.has(at)){seen.add(at);cycle.push(at);at=map.get(at);}
          for(let i=1;i<cycle.length;i++)swaps.push([cycle[0],cycle[i]]);
        }
        const ports=[carry,low,top,this.tag[2],extra];
        stepList(swaps,rv,([a,b])=>this.u6Transpose(tape,ports,a,b,[this.take],this.tag.slice(3),false));
      };
      stepList([norm,last,recode],back,fn=>fn(back));
    }
    indicator(tape,j,kind,controls,target){
      if(!this.u12){super.indicator(tape,j,kind,controls,target);return;}
      super.indicator(tape,j,kind,controls,target);
      const pred=c=>kind==='eq'?c===j:kind==='gt'?c>j:c<=j;
      for(let code=0;code<6;code++){
        const rank=code<4?0:1;if(pred(code)===pred(rank))continue;
        const yes=[...controls,this.A[1]],no=[];
        this.tag.forEach((q,i)=>((code>>i)&1?yes:no).push(q));this.toggle(tape,yes,no,target);
      }
    }
    guardedBarrel(tape,word,left,back){
      if(!this.u12){super.guardedBarrel(tape,word,left,back);return;}
      const extra=this.A[1];
      stepList(split(0,this.tag.length),back,j=>{
        const k=(1<<j)%word.length;if(!k)return;
        const origin=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
        const mark=()=>{
          if(j<3)this.toggle(tape,[...this.ctrl,this.tag[j]],[extra],this.carry);
          else this.toggle(tape,[...this.ctrl,this.tag[j]],[],this.carry);
          if(j===0)this.toggle(tape,[...this.ctrl,extra,this.tag[2]],[],this.carry);
        };
        mark();this.permute(tape,word,origin,[this.carry],back);mark();
      });
    }
    digitTopOne(tape,z,v,controls,back){
      if(!this.u12){super.digitTopOne(tape,z,v,controls,back);return;}
      const tp=this.u12VirtualTape(tape);super.digitTopOne(tp,z,v,controls,back);tp.u12Check();
    }
    u12VirtualTape(tape){
      const H=this,tag=this.tag,extra=this.A[1],host=this.A.slice(0,2),tp=Object.create(tape);
      tp.ids=tape.ids.filter(q=>!tag.includes(q)&&q!==extra);
      const cube=(yes=[],no=[])=>({yes:[...new Set(yes)].sort((a,b)=>a-b),no:[...new Set(no)].sort((a,b)=>a-b)});
      const key=c=>c.yes.join(',')+'!'+c.no.join(',');
      const norm=ts=>{const m=new Map();for(const c of ts){if(c.yes.some(q=>c.no.includes(q)))continue;const k=key(c);if(m.has(k))m.delete(k);else m.set(k,c);}return [...m.values()];};
      const base=[[cube([extra,tag[0]],[tag[2]])],[cube([extra,tag[1]],[tag[2]]),cube([extra,tag[2],tag[0]])]];
      let expressions=base.map(x=>x.slice()),dependencies=new Set();
      const deps=()=>{dependencies=new Set(expressions.flatMap(e=>e.flatMap(c=>c.yes.concat(c.no))));};deps();
      const expr=q=>q===NONE?[cube()]:host.includes(q)?expressions[host.indexOf(q)]:[cube([q])];
      const mul=(a,b)=>norm(a.flatMap(x=>b.map(y=>cube(x.yes.concat(y.yes),x.no.concat(y.no)))));
      tp.out=(a,b,t)=>{
        if(!host.includes(a)&&!host.includes(b)&&!host.includes(t)&&!dependencies.has(t)){tape.out(a,b,t);return;}
        const terms=mul(expr(a),expr(b));
        if(host.includes(t)){const i=host.indexOf(t);expressions[i]=norm(expressions[i].concat(terms));deps();return;}
        if(terms.some(c=>c.yes.includes(t)||c.no.includes(t)))throw Error('U12 implicit self target '+[H.k,a,b,t]);
        expressions=expressions.map(e=>norm(e.concat(mul(e.filter(c=>c.yes.includes(t)||c.no.includes(t)).map(c=>cube(c.yes.filter(q=>q!==t),c.no.filter(q=>q!==t))),terms))));deps();
        if(expressions.some(e=>e.length>10000))throw Error('U12 symbolic cap');
        for(const c of terms)H.toggle(tape,c.yes,c.no,t);
      };
      tp.u12Check=()=>{for(let i=0;i<2;i++)if(norm(expressions[i].concat(base[i])).length)throw Error('U12 virtual not restored '+H.k);};return tp;
    }
`);
 return s;
};
