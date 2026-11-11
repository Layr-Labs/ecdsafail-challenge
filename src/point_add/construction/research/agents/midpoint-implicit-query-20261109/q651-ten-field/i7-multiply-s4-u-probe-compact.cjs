'use strict';
// Incremental source overlay after U15 sourceUpper, before its single sink.
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U16 anchor '+a);s=s.replace(a,()=>b);};
 one('this.ids=this.ids.filter(q=>q!==650&&q!==651);','this.ids=this.ids.filter(q=>q!==647&&q!==650&&q!==651);');
 one('u40Sign(tape,target){',`u40Sign(tape,target){
      if((this.k>=15&&this.k<=62||this.k>=80&&this.k<=95)){this.u16Sign(tape,target);return;}`);
 one('    u9Category(rank){',`    u9Category(rank){
      if(this.u16Code){const t=this.u40Tag,yes=t.slice(4),no=[];
        if(rank===0)no.push(t[3]);
        if(rank===1){yes.push(t[3]);no.push(t[2]);}
        if(rank===2)yes.push(t[3],t[2]);
        return {yes,no};}
`);
 one('      if(this.u9Three&&word.length===',`      if(this.u16Code&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        if(limit<0n||limit>BigInt(this.u16Start))throw Error('U16 comparator range '+limit);
        MixedArithmetic.prototype.constBelow.call(this,tape,word,limit,controls,targets);
        for(let rank=0;rank<3;rank++)if(BigInt(rank)<limit){const p=this.u9Category(rank);for(const t of targets)this.toggle(tape,controls.concat(p.yes),p.no,t);}return;
      }
      if(this.u9Three&&word.length===`);
 one('      if(this.u9Three){\n        const extra=tag.at(-1);',`      if(this.u16Code){
        stepList(split(0,tag.length),back,j=>{
          const k=(1<<j)%word.length,src=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
          const terms=[{yes:[tag[j]],no:[]},{yes:[...new Set([tag[j],...tag.slice(4)])],no:[]}];
          if(j<2)terms.push(this.u9Category(j===0?1:2));
          stepList(terms,back,p=>{for(const q of p.no)tape.out(NONE,NONE,q);this.u10ControlledPermutation(tape,word,src,p.yes.concat(p.no),back);for(const q of p.no)tape.out(NONE,NONE,q);});
        });return;
      }
      if(this.u9Three){
        const extra=tag.at(-1);`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u16Sign(inputTape,target){
      const tape=Object.create(inputTape);tape.ids=inputTape.ids.filter(q=>q!==647);
      tape.out=(a,b,z)=>{if(a===647||b===647||z===647)throw Error('U16 compact probe ban647');inputTape.out(a,b,z);};
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;
      const start=2**bits-16;
      if(bits<5||free>=start)throw Error('U16 capacity '+[this.k,free,start]);
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const tag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q);
      if(tag.at(-1)!==647)throw Error('U16 expected rank top '+[this.k,tag]);tag[tag.length-1]=S[2];
      if(new Set(tag).size!==tag.length)throw Error('U16 tag alias');
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u9Three:true,u16Code:true,u16Start:start});
      const high=this.r.slice(base);
      const rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);});
      const swaps=[];
      for(let rank=0;rank<3;rank++){
        const inputs=[],outputs=[];
        for(let low=0;low<2**(3-rank);low++){
          const coeff=low<<rank;
          inputs.push(rank^((coeff>>1&1)<<0)^((coeff&1)<<1)^((coeff>>2&1)*(2**(bits-1))));
          outputs.push(start+(rank===0?0:rank===1?8:12)+low);
        }
        const positions=inputs.slice(),seq=[];
        for(let i=0;i<inputs.length;i++)if(positions[i]!==outputs[i]){
          const from=positions[i],to=outputs[i];seq.push([from,to]);
          for(let j=0;j<positions.length;j++)positions[j]=positions[j]===from?to:positions[j]===to?from:positions[j];
        }
        const yes=rank?[high[rank-1]]:[],no=high.slice(rank);
        swaps.push(rv=>{const mark=()=>this.toggle(tape,yes,no,this.pick);mark();stepList(seq,rv,([from,to])=>this.u6Transpose(tape,tag,from,to,[this.pick],[],rv));mark();});
      }
      const recode=rv=>stepList(swaps,rv,fn=>fn(rv));
      const seq=[rotate,()=>this.rank(tape,tag),recode,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();
    }
`);
 return s;
};
