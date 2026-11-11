'use strict';
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U23 anchor '+a);s=s.replace(a,()=>b);};
 one('    u40Sign(tape,target){',`    u40Sign(tape,target){
      if(this.k<=9||this.k>=64&&this.k<=74){this.u23Sign(tape,target);return;}
      if(this.k===63||this.k===112){this.u9ThreeSign(tape,target);return;}`);
 one("layer.u40Probe=this.k<=95&&(this.k!==63||this.u5PhaseHost===undefined);",'layer.u40Probe=this.k<=95;');
 one('this.u5PhaseHost===undefined||this.k>=96&&this.k<=111','this.u5PhaseHost===undefined||this.k>=96&&this.k<=112');
 one('    u9Category(rank){',`    u9Category(rank){
      if(this.u23Four){const t=this.u40Tag,yes=[t.at(-1)],no=[t[4-rank]];for(let j=5-rank;j<5;j++)yes.push(t[j]);return {yes,no};}`);
 one('      if(this.u18Dense&&word.length===',`      if(this.u23Four&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        MixedArithmetic.prototype.constBelow.call(this,tape,word,limit,controls,targets);
        for(let rank=0;rank<4;rank++)if(BigInt(rank)<limit){const p=this.u9Category(rank);for(const target of targets)this.toggle(tape,controls.concat(p.yes),p.no,target);}return;
      }
      if(this.u18Dense&&word.length===`);
 one('      if(this.u18Dense){\n        stepList',`      if(this.u23Four){
        stepList(split(0,tag.length-1),back,j=>{
          const k=(1<<j)%word.length,src=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
          const terms=[{yes:[tag[j]],no:[tag.at(-1)]}];
          for(let rank=0;rank<4;rank++)if(rank>>j&1)terms.push(this.u9Category(rank));
          stepList(terms,back,p=>{for(const q of p.no)tape.out(NONE,NONE,q);this.u10ControlledPermutation(tape,word,src,p.yes.concat(p.no),back);for(const q of p.no)tape.out(NONE,NONE,q);});
        });return;
      }
      if(this.u18Dense){
        stepList`);
 one('host=this.u9Three?this.u6S.slice(0,3):[q0,q1]','host=this.u23Four?this.u6S.slice(0,4):this.u9Three?this.u6S.slice(0,3):[q0,q1]');
 one('[[0],[0,1],[0,1,2]].map((ranks,j)', '(this.u23Four?[[0],[0,1],[0,1,2],[0,1,2,3]]:[[0],[0,1],[0,1,2]]).map((ranks,j)');
 one('cut>=(this.u9Three?3:2)','cut>=(this.u23Four?4:this.u9Three?3:2)');
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u23Sign(inputTape,target){
      const tape=Object.create(inputTape);tape.ids=inputTape.ids.filter(q=>q!==647);
      tape.out=(a,b,z)=>{if(a===647||b===647||z===647)throw Error('U23 probe ban647 '+[this.k,a,b,z]);inputTape.out(a,b,z);};
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const tag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q);
      const slot=tag.indexOf(647);if(slot<0)throw Error('U23 expected647 '+[this.k,tag]);tag[slot]=S[2];tag.push(S[3]);
      if(new Set(tag).size!==tag.length)throw Error('U23 tag alias '+[this.k,tag]);
      const top=2**(tag.length-1);if(free>=top||top<32)throw Error('U23 four capacity '+[this.k,free,top]);
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u9Three:true,u23Four:true});
      const high=this.r.slice(base);
      const rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);});
      const swaps=[];
      for(let rank=0;rank<4;rank++){
        const inputs=[],outputs=[];
        for(let low=0;low<2**(4-rank);low++){
          const coeff=low<<rank;
          inputs.push(rank^((coeff>>1&1)<<0)^((coeff&1)<<1)^((coeff>>2&1)*(2**slot))^((coeff>>3&1)*top));
          outputs.push(top+(rank===0?0:rank===1?16:rank===2?24:28)+low);
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
