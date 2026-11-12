'use strict';
// Incremental SOURCE overlay on U28 + U29. No sink or inter-family transport.
exports.wholeStageFreed=false;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U34 anchor '+a);s=s.replace(a,()=>b);};
 one('    u40Sign(tape,target){',`    u40Sign(tape,target){
      if(this.u5PhaseHost!==target&&this.k<=111&&!(this.k>=29&&this.k<=62||this.k===94||this.k===95)){
        const H=Object.create(this);if(this.k===111)Object.defineProperty(H,'ab',{value:this.half+1});
        H.u34Sign(tape,target);return;
      }
`);
 one('    u9Category(rank){',`    u9Category(rank){
      if(this.u34Low){const t=this.u40Tag,n=this.u34Low,yes=[...t.slice(n+1),...t.slice(0,rank)],no=[t[rank]];return {yes,no};}
`);
 one('host=this.u23Four?this.u6S.slice(0,4)', 'host=this.u34Low?this.u6S.slice(0,this.u34Low):this.u23Four?this.u6S.slice(0,4)');
 one('const base=this.u9Three?', 'const base=this.u34Low?Array.from({length:this.u34Low},(_,j)=>[cube([...tag.slice(this.u34Low+1),tag[j+1]]),cube([...tag.slice(this.u34Low+1),...tag.slice(0,j+2)])]):this.u9Three?');
 one('const tp=cut>=(this.u23Four?4:this.u9Three?3:2)?tape:', 'const tp=cut>=(this.u34Low|| (this.u23Four?4:this.u9Three?3:2))?tape:');
 one('    constBelow(tape,word,limit,controls,targets){',`    constBelow(tape,word,limit,controls,targets){
      if(this.u34Low&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        const n=this.u34Low,start=2**word.length-2**(n+1);
        if(limit<0n||limit>BigInt(start))throw Error('U34 compare range '+limit);
        MixedArithmetic.prototype.constBelow.call(this,tape,word,limit,controls,targets);
        for(let rank=0;rank<n;rank++)if(BigInt(rank)<limit){const p=this.u9Category(rank);for(const t of targets)this.toggle(tape,controls.concat(p.yes),p.no,t);}return;
      }
`);
 one('    barrel(tape,word,tag,left,back){\n      if(this.u29Dense){',`    barrel(tape,word,tag,left,back){
      if(this.u34Low){
        const n=this.u34Low;
        stepList(split(0,tag.length),back,j=>{
          const shift=(1<<j)%word.length,src=left?word.slice(-shift).concat(word.slice(0,-shift)):word.slice(shift).concat(word.slice(0,shift));
          const terms=[{yes:[tag[j]],no:[]}];
          for(let rank=0;rank<n;rank++){
            const p=this.u9Category(rank),code=2**tag.length-2**(n+1)+2**rank-1;
            if(j>rank&&j<=n){terms.push({yes:[...new Set([...p.yes,tag[j]])],no:p.no,inverse:true});if(rank>>j&1)terms.push(p);}
            else if(((code>>j)&1)^((rank>>j)&1))terms.push({...p,inverse:!!(code>>j&1)});
          }
          stepList(terms,back,p=>{for(const q of p.no)tape.out(NONE,NONE,q);this.u10ControlledPermutation(tape,word,src,p.yes.concat(p.no),back!==!!p.inverse);for(const q of p.no)tape.out(NONE,NONE,q);});
        });return;
      }
      if(this.u29Dense){`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u34Sign(inputTape,target){
      const tape=Object.create(inputTape);tape.ids=inputTape.ids.filter(q=>q!==643&&q!==647);
      tape.loan=(used,n)=>inputTape.loan([...used,643,647],n);
      tape.out=(a,b,z)=>{if([a,b,z].includes(643)||[a,b,z].includes(647))throw Error('U34 banned helper '+[this.k,a,b,z]);inputTape.out(a,b,z);};
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const tag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?S[3]:q),slot=tag.indexOf(647);
      let n;
      if(this.k>=96){if(!this.u38ProbeLease||slot<0)throw Error('U34 V lease');tag[slot]=this.v[this.k];tag.push(S[2]);n=4;}
      else if(slot>=0){tag[slot]=S[2];tag.push(S[4]);n=5;}
      else{tag.push(S[2]);n=4;}
      const start=2**tag.length-2**(n+1);
      if(new Set(tag).size!==tag.length||free>=start||tag.some(q=>q===643||q===647))throw Error('U34 capacity '+[this.k,free,start,tag]);
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u34Low:n});
      const high=this.r.slice(base),rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const shift=(1<<j)%S.length,src=S.slice(-shift).concat(S.slice(0,-shift));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);});
      const swaps=[];
      for(let rank=0;rank<n;rank++){
        const positions=[],outputs=[];
        for(let low=0;low<2**(n-rank);low++){
          const coeff=low*2**rank;let raw=rank;
          for(let j=0;j<n;j++)if(coeff>>j&1)raw^=2**tag.indexOf(S[j]);
          positions.push(raw);outputs.push(2**tag.length-2**(n+1)+2**rank-1+low*2**(rank+1));
        }
        const seq=[];
        for(let i=0;i<positions.length;i++)if(positions[i]!==outputs[i]){const from=positions[i],to=outputs[i];seq.push([from,to]);for(let j=0;j<positions.length;j++)positions[j]=positions[j]===from?to:positions[j]===to?from:positions[j];}
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
