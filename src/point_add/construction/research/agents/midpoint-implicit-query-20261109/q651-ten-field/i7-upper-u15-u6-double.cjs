'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U6 double anchor '+a);s=s.replace(a,()=>b);};
 one('u40Sign(tape,target){',`u40Sign(tape,target){
      if((this.k>=3&&this.k<=62||this.k>=68&&this.k<=95)&&this.u5PhaseHost===undefined){this.u6DoubleSign(tape,target);return;}`);
 one('u40Tape(tape){','u40Tape(tape){\n      if(this.u6Code)return this.u6VirtualTape(tape);');
 one('      if(this.u40FixedRank!==undefined&&word.length===0)',`      if(this.u6Code&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        MixedArithmetic.prototype.constBelow.call(this,tape,word,limit,controls,targets);
        if(limit>1n&&limit<=BigInt(this.u6Code[3])){for(const t of targets)this.toggle(tape,controls.concat(word.slice(2)),[],t);return;}
        if(limit===1n){for(const t of targets){this.toggle(tape,controls.concat(word.slice(2),word[0]),[],t);this.toggle(tape,controls.concat(word.slice(2),word[1]),[word[0]],t);}return;}
        this.u6Code.forEach((c,i)=>{if((BigInt(i===3?1:0)<limit)!==(BigInt(c)<limit))for(const t of targets){const yes=controls.slice(),no=[];word.forEach((q,j)=>((c>>j)&1?yes:no).push(q));this.toggle(tape,yes,no,t);}});return;
      }
      if(this.u40FixedRank!==undefined&&word.length===0)`);
 one('      if(this.u40FixedRank!==undefined){const k=',`      if(this.u6Code){
        const seq=[rv=>AlignedGeneral.prototype.barrel.call(this,tape,word,tag,left,rv)];
        this.u6Code.forEach((c,i)=>{const rank=i===3?1:0,k=((c-rank)%word.length+word.length)%word.length;
          const src=left?word.slice(k).concat(word.slice(0,k)):word.slice(-k).concat(word.slice(0,-k));
          const yes=[],no=[];tag.forEach((q,j)=>((c>>j)&1?yes:no).push(q));
          seq.push(rv=>{for(const q of no)tape.out(NONE,NONE,q);this.permute(tape,word,src,tag,rv);for(const q of no)tape.out(NONE,NONE,q);});
        });stepList(seq,back,fn=>fn(back));return;
      }
      if(this.u40FixedRank!==undefined){const k=`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u6RankBit(tape,j,target){
      const high=this.r.slice(this.ab),n=high.length,d=tape.loan([...high,target],n+1),coeff=Array(n+1).fill(0);
      for(let i=0;i<n;i++){coeff[i]^=(i+1)>>j&1;coeff[i+1]^=(i+1)>>j&1;}
      for(const q of high)tape.out(NONE,NONE,q);
      for(let e=0;e<2;e++){tape.out(NONE,NONE,d[n]);for(let i=n-1;i>=0;i--)tape.out(high[i],d[i+1],d[i]);for(let i=0;i<=n;i++)if(coeff[i])tape.out(NONE,d[i],target);for(let i=0;i<n;i++)tape.out(high[i],d[i+1],d[i]);}
      for(const q of high)tape.out(NONE,NONE,q);
    }
    u6Transpose(tape,tag,a,b,yes,no,back){
      const path=[],v=a;let at=v;
      for(let j=0;j<tag.length;j++)if(((a^b)>>j)&1){const p=yes.slice(),n=no.slice();tag.forEach((q,i)=>{if(i!==j)((at>>i)&1?p:n).push(q);});path.push(()=>this.toggle(tape,p,n,tag[j]));at^=1<<j;}
      const ops=path.concat(path.slice(0,-1).reverse());stepList(ops,back,fn=>fn());
    }
    u6DoubleSign(tape,target){
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const tag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q);
      const max=2**bits-1,codes=[max-2,max-1,max,max-3];if(codes[3]<=free)throw Error('U6 code capacity '+this.k);
      const H=Object.create(this);H.u40Low=S[0];H.u40Tag=tag;H.u6Code=codes;H.u6S=S;H.u6Tapes=[];
      const high=this.r.slice(base),low=high[0];
      const rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);});
      const recode=rv=>{const ops=[...codes.slice(0,3).map((c,i)=>rr=>this.u6Transpose(tape,tag,i+1,c,[],high,rr)),rr=>this.u6Transpose(tape,tag,0,codes[3],[low],high.slice(1),rr)];stepList(ops,rv,fn=>fn(rv));};
      const seq=[rotate,()=>this.rank(tape,tag),recode,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();
    }
    u6VirtualTape(tape){
      const H=this,tag=this.u40Tag,[q0,q1]=this.u6S,host=[q0,q1],tp=Object.create(tape);
      tp.ids=tape.ids.filter(q=>!tag.includes(q));
      const cube=(yes=[],no=[])=>({yes:[...new Set(yes)].sort((a,b)=>a-b),no:[...new Set(no)].sort((a,b)=>a-b)});
      const key=c=>c.yes.join(',')+'!'+c.no.join(',');
      const norm=ts=>{const m=new Map();for(const c of ts){if(c.yes.some(q=>c.no.includes(q)))continue;const k=key(c);if(m.has(k))m.delete(k);else m.set(k,c);}return [...m.values()];};
      const eq=c=>cube(tag.filter((q,j)=>c>>j&1),tag.filter((q,j)=>!(c>>j&1)));
      const base=[[cube(tag.slice(2).concat(tag[1]))],[cube(tag.slice(2).concat(tag[0])),eq(this.u6Code[3])]];let expressions=base.map(x=>x.slice());
      let dependencies=new Set();const deps=()=>{dependencies=new Set(expressions.flatMap(e=>e.flatMap(c=>c.yes.concat(c.no))));};deps();
      const expr=q=>q===NONE?[cube()]:host.includes(q)?expressions[host.indexOf(q)]:[cube([q])];
      const mul=(a,b)=>norm(a.flatMap(x=>b.map(y=>cube(x.yes.concat(y.yes),x.no.concat(y.no)))));
      tp.out=(a,b,t)=>{if(!host.includes(a)&&!host.includes(b)&&!host.includes(t)&&!dependencies.has(t)){tape.out(a,b,t);return;}
        const terms=mul(expr(a),expr(b));if(host.includes(t)){const i=host.indexOf(t);expressions[i]=norm(expressions[i].concat(terms));deps();return;}
        if(terms.some(c=>c.yes.includes(t)||c.no.includes(t)))throw Error('U6 implicit self target '+[H.k,a,b,t]);
        expressions=expressions.map(e=>norm(e.concat(mul(e.filter(c=>c.yes.includes(t)||c.no.includes(t)).map(c=>cube(c.yes.filter(q=>q!==t),c.no.filter(q=>q!==t))),terms))));
        deps();
        for(const c of terms)H.toggle(tape,c.yes,c.no,t);
      };
      tp.u6Check=()=>{for(let i=0;i<2;i++)if(norm(expressions[i].concat(base[i])).length)throw Error('U6 virtual not restored '+H.k);};
      H.u6Tapes.push(tp);return tp;
    }
`);
 return s;
};
