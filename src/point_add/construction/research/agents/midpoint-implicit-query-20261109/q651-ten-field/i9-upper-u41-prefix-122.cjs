'use strict';
// Tight prefix code: rank r occupies prefix 1^r 0, with n-r low coefficient bits.
// Last two codewords encode ranks n and n+1. No extra clean helper is used.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U34 late anchor '+a);s=s.replace(a,()=>b);};
 one('    alignedSign(tape,target){\n        if(this.u40Probe)',`    alignedSign(tape,target){
        if(this.k===124){
          const H=Object.create(this),tp=Object.create(tape);H.u40Probe=true;
          tp.ids=tape.ids.filter(q=>q!==643&&q!==647);tp.loan=(used,n)=>tape.loan([...used,643,647],n);
          tp.out=(a,b,z)=>{if([a,b,z].includes(643)||[a,b,z].includes(647))throw Error('U34 late banned helper');tape.out(a,b,z);};
          H.u40Sign(tp,target);return;
        }
        if(this.u40Probe)`);
 one('H.u23LateCode=true;if(H.r.length-H.ab<=11)', 'H.u23LateCode=true;if(H.r.length-H.ab<=12){H.u34UnarySign(tape,target);return;}if(H.r.length-H.ab<=11)');
 one('const base=this.u34Low?', 'const base=this.u34Unary?Array.from({length:this.u34Low},(_,j)=>[cube([tag[j+1]]),cube(tag.slice(0,j+2))]):this.u34Low?');
 one('    u9Category(rank){',`    u9Category(rank){
      if(this.u34Unary){const t=this.u40Tag;return {yes:t.slice(0,rank),no:[t[rank]]};}
`);
 one('    constBelow(tape,word,limit,controls,targets){',`    constBelow(tape,word,limit,controls,targets){
      if(this.u34Unary&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        if(limit<=0n)return;for(const t of targets){this.toggle(tape,controls,[],t);if(limit<=BigInt(word.length))this.toggle(tape,controls.concat(word.slice(0,Number(limit))),[],t);}return;
      }
`);
 one('    barrel(tape,word,tag,left,back){\n      if(this.u34Low){',`    barrel(tape,word,tag,left,back){
      if(this.u34Unary){
        const src=left?word.slice(-1).concat(word.slice(0,-1)):word.slice(1).concat(word[0]);
        stepList(split(1,tag.length+1),back,j=>{const controls=tag.slice(0,j);if(j===1)this.permute(tape,word,src,controls,back);else this.u10ControlledPermutation(tape,word,src,controls,back);});return;
      }
      if(this.u34Low){`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u34UnarySign(inputTape,target){
      const tape=Object.create(inputTape);tape.ids=inputTape.ids.filter(q=>q!==643&&q!==647);tape.loan=(used,n)=>inputTape.loan([...used,643,647],n);
      tape.out=(a,b,z)=>{if([a,b,z].includes(643)||[a,b,z].includes(647))throw Error('U34 unary banned helper');inputTape.out(a,b,z);};
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1,n=Math.max(3,free-1);
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D],tag=[(this.k<=112?this.probeTag(base,this.tags.slice(0,Math.max(4,bits)),target)[3]:this.tags[3]),...S.slice(0,n)];
      if(free<1||free>15||new Set(tag).size!==n+1)throw Error('U34 unary capacity');
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u34Low:n,u34Unary:true});
      const high=this.r.slice(base),rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const shift=(1<<j)%S.length,src=S.slice(-shift).concat(S.slice(0,-shift));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);}),swaps=[];
      for(let j=0;j<free;j++)swaps.push(()=>{tape.out(NONE,NONE,tag[j]);this.toggle(tape,[],high.slice(j),tag[j]);});
      const recode=rv=>stepList(swaps,rv,fn=>fn(rv)),seq=[rotate,recode,rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));for(const tp of H.u6Tapes)tp.u6Check();
    }
`);
 return s;
};

