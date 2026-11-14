'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U9 three anchor '+a);s=s.replace(a,()=>b);};
 one('u40Sign(tape,target){',`u40Sign(tape,target){
      if((this.k<=2||this.k>=63&&this.k<=67)&&this.u5PhaseHost===undefined){this.u9ThreeSign(tape,target);return;}`);
 // Row63 previously bypassed U4; use the same complete remainder geometry.
 one('layer.u40Probe=this.k<=95&&this.k!==63;', 'layer.u40Probe=this.k<=95&&(this.k!==63||this.u5PhaseHost===undefined);');
 one('      if(this.u6Code&&word.length===',`      if(this.u9Three&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        MixedArithmetic.prototype.constBelow.call(this,tape,word,limit,controls,targets);
        for(let rank=0;rank<3;rank++)if(BigInt(rank)<limit){const p=this.u9Category(rank);for(const t of targets)this.toggle(tape,controls.concat(p.yes),p.no,t);}return;
      }
      if(this.u6Code&&word.length===`);
 one('      if(this.u6Code){\n        const seq=',`      if(this.u9Three){
        const extra=tag.at(-1);
        stepList(split(0,tag.length-1),back,j=>{
          const k=(1<<j)%word.length,src=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
          const terms=[{yes:[tag[j]],no:[extra]}];if(j<2)terms.push(this.u9Category(j===0?1:2));
          stepList(terms,back,p=>{for(const q of p.no)tape.out(NONE,NONE,q);this.permute(tape,word,src,p.yes.concat(p.no),back);for(const q of p.no)tape.out(NONE,NONE,q);});
        });return;
      }
      if(this.u6Code){
        const seq=`);
 one('const H=this,tag=this.u40Tag,[q0,q1]=this.u6S,host=[q0,q1],tp=Object.create(tape);',
     'const H=this,tag=this.u40Tag,[q0,q1]=this.u6S,host=this.u9Three?this.u6S.slice(0,3):[q0,q1],tp=Object.create(tape);');
 one('const base=[[cube(tag.slice(2).concat(tag[1]))],[cube(tag.slice(2).concat(tag[0])),eq(this.u6Code[3])]];let expressions=',
 `const base=this.u9Three?[[0],[0,1],[0,1,2]].map((ranks,j)=>ranks.map(rank=>{const p=this.u9Category(rank);return cube(p.yes.concat(tag[j-rank]),p.no);})): [[cube(tag.slice(2).concat(tag[1]))],[cube(tag.slice(2).concat(tag[0])),eq(this.u6Code[3])]];let expressions=`);
 one('for(let i=0;i<2;i++)if(norm(expressions[i].concat(base[i])).length)', 'for(let i=0;i<host.length;i++)if(norm(expressions[i].concat(base[i])).length)');
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u9Category(rank){
      const t=this.u40Tag,n=t.length-1,yes=[t[n]],no=[];
      if(rank===0)no.push(t[3]);
      if(rank===1){yes.push(t[3]);no.push(t[2]);}
      if(rank===2)yes.push(t[3],t[2]);
      return {yes,no};
    }
    u9ThreeSign(tape,target){
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;
      if(bits<4||free+12>=2**(bits+1))throw Error('U9 capacity '+this.k);
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const rankTag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:q),tag=rankTag.concat(S[2]);
      if(new Set(tag).size!==tag.length)throw Error('U9 tag collision');
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u9Three:true});
      const high=this.r.slice(base),top=2**bits;
      const rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);});
      // For each rank0/1/2 support, synthesize a permutation of the code word.
      // Input low bits are xor'd into rankTag0/1 and the additional high code bit.
      const swaps=[];
      for(let rank=0;rank<3;rank++){
        const inputs=[],outputs=[];
        for(let low=0;low<2**(3-rank);low++){
          const coeff=low<<rank;
          inputs.push(rank^((coeff>>1&1)<<0)^((coeff&1)<<1)^((coeff>>2&1)*top));
          outputs.push(top+(rank===0?0:rank===1?8:12)+low);
        }
        const positions=inputs.slice(),seq=[];
        for(let i=0;i<inputs.length;i++)if(positions[i]!==outputs[i]){
          const from=positions[i],to=outputs[i];seq.push([from,to]);
          for(let j=0;j<positions.length;j++)positions[j]=positions[j]===from?to:positions[j]===to?from:positions[j];
        }
        const yes=rank?[high[rank-1]]:[],no=high.slice(rank);
        for(const [from,to]of seq)swaps.push(rv=>this.u6Transpose(tape,tag,from,to,yes,no,rv));
      }
      const recode=rv=>stepList(swaps,rv,fn=>fn(rv));
      const seq=[rotate,()=>this.rank(tape,rankTag),recode,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();
    }
`);
 return s;
};
