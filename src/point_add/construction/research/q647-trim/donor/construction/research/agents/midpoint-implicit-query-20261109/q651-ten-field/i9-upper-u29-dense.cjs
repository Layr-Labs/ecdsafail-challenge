'use strict';
// Experimental four-coefficient-bit code. Frees rank/carry role 643 in
// selected compact probes; the source guard rejects any hidden use.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U29 dense anchor '+a);s=s.replace(a,()=>b);};
 one('    u16Sign(inputTape,target){',`    u16Sign(inputTape,target){
      {const free=this.r.length-this.ab,bits=Math.floor(Math.log2(free))+1;
       if(this.u5PhaseHost!==target&&bits>=5&&free<2**bits-30){this.u29DenseSign(inputTape,target);return;}}
`);
 one('    u9Category(rank){',`    u9Category(rank){
      if(this.u29Dense){const t=this.u40Tag,low=4-rank,code=2**t.length-(rank===0?16:rank===1?24:rank===2?28:30),yes=[],no=[];
        for(let j=low;j<t.length;j++)((code>>j)&1?yes:no).push(t[j]);return {yes,no};}
`);
 one('      if(this.u23Four){\n        stepList',`      if(this.u29Dense){
        stepList(split(0,tag.length),back,j=>{
          const shift=(1<<j)%word.length,src=left?word.slice(-shift).concat(word.slice(0,-shift)):word.slice(shift).concat(word.slice(0,shift));
          const terms=[{yes:[tag[j]],no:[]}];
          for(let rank=0;rank<4;rank++){
            const p=this.u9Category(rank),code=2**tag.length-(rank===0?16:rank===1?24:rank===2?28:30);
            if(j<4-rank){terms.push({yes:[...new Set([...p.yes,tag[j]])],no:p.no,inverse:true});if(rank>>j&1)terms.push(p);}
            else if(((code>>j)&1)^((rank>>j)&1))terms.push({...p,inverse:!!(code>>j&1)});
          }
          stepList(terms,back,p=>{for(const q of p.no)tape.out(NONE,NONE,q);this.u10ControlledPermutation(tape,word,src,p.yes.concat(p.no),back!==!!p.inverse);for(const q of p.no)tape.out(NONE,NONE,q);});
        });return;
      }
      if(this.u23Four){
        stepList`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u29DenseSign(inputTape,target){
      const tape=Object.create(inputTape);tape.ids=inputTape.ids.filter(q=>q!==643&&q!==647);
      tape.out=(a,b,z)=>{if([a,b,z].includes(643)||[a,b,z].includes(647))throw Error('U29 dense banned helper '+[this.k,a,b,z]);inputTape.out(a,b,z);};
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const tag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?S[3]:q),slot=tag.indexOf(647);
      if(slot<0||free>=2**bits-30)throw Error('U29 dense capacity');tag[slot]=S[2];
      if(new Set(tag).size!==tag.length)throw Error('U29 dense tag alias');
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u9Three:true,u23Four:true,u29Dense:true});
      const high=this.r.slice(base),rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const n=(1<<j)%S.length,src=S.slice(-n).concat(S.slice(0,-n));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);});
      const swaps=[];
      for(let rank=0;rank<4;rank++){
        const inputs=[],outputs=[];
        for(let low=0;low<2**(4-rank);low++){
          const coeff=low<<rank;
          inputs.push(rank^((coeff>>1&1)<<0)^((coeff&1)<<1)^((coeff>>2&1)*(2**slot))^((coeff>>3&1)*4));
          outputs.push(2**bits-(rank===0?16:rank===1?24:rank===2?28:30)+low);
        }
        const positions=inputs.slice(),seq=[];
        for(let i=0;i<inputs.length;i++)if(positions[i]!==outputs[i]){const from=positions[i],to=outputs[i];seq.push([from,to]);for(let j=0;j<positions.length;j++)positions[j]=positions[j]===from?to:positions[j]===to?from:positions[j];}
        const yes=rank?[high[rank-1]]:[],no=high.slice(rank);
        swaps.push(rv=>{const mark=()=>this.toggle(tape,yes,no,this.pick);mark();stepList(seq,rv,([from,to])=>this.u6Transpose(tape,tag,from,to,[this.pick],[],rv));mark();});
      }
      const recode=rv=>stepList(swaps,rv,fn=>fn(rv));
      const seq=[rotate,()=>this.rank(tape,tag),recode,rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();
    }
`);
 return s;
};
