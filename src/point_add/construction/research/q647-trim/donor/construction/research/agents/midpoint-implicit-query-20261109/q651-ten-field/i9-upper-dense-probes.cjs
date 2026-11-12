'use strict';
// Dense extension to U16. Only ten public probe rows, no runtime dispatch.
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U18 anchor '+a);s=s.replace(a,()=>b);};
 one('if((this.k>=15&&this.k<=62||this.k>=80&&this.k<=95))','if((this.k>=10&&this.k<=62||this.k>=75&&this.k<=95))');
 one('const start=2**bits-16;\n      if(bits<5||free>=start)', 'const dense=this.k>=10&&this.k<=14||this.k>=75&&this.k<=79,start=2**bits-(dense?11:16);\n      if(bits<5||free>=start)');
 one('u16Code:true,u16Start:start','u16Code:true,u16Start:start,u18Dense:dense');
 s=s.replace('for(let rank=0;rank<3;rank++){\n        const inputs=', 'for(let rank=0;rank<(dense?4:3);rank++){\n        const inputs=');
 one('outputs.push(start+(rank===0?0:rank===1?8:12)+low);','outputs.push(dense?(rank===0?2**bits-8+low:rank===1?low:rank===2?2**bits-10+low:2**bits-11):start+(rank===0?0:rank===1?8:12)+low);');
 one('    u9Category(rank){','    u9Category(rank){\n      if(this.u18Dense)return this.u18Category(rank);');
 one('      if(this.u16Code&&word.length===',`      if(this.u18Dense&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])){
        MixedArithmetic.prototype.constBelow.call(this,tape,word,limit,controls,targets);
        for(let rank=0;rank<4;rank++)for(let low=0;low<2**Math.max(0,3-rank);low++){
          const code=this.u18Encode(rank,low);if((BigInt(code)<limit)===(BigInt(rank)<limit))continue;
          const yes=controls.slice(),no=[];word.forEach((q,j)=>((code>>j)&1?yes:no).push(q));for(const target of targets)this.toggle(tape,yes,no,target);
        }return;
      }
      if(this.u16Code&&word.length===`);
 one('      if(this.u16Code){\n        stepList',`      if(this.u18Dense){
        stepList(split(0,tag.length),back,j=>{
          const k=(1<<j)%word.length,src=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
          stepList(this.u18BitTerms(j),back,p=>{for(const q of p.no)tape.out(NONE,NONE,q);this.u10ControlledPermutation(tape,word,src,p.yes.concat(p.no),back);for(const q of p.no)tape.out(NONE,NONE,q);});
        });return;
      }
      if(this.u16Code){
        stepList`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u18Encode(rank,low){const C=2**this.u40Tag.length;return rank===0?C-8+low:rank===1?low:rank===2?C-10+low:rank===3?C-11:rank;}
    u18Category(rank){
      const t=this.u40Tag,yes=[],no=[];
      if(rank===0)return {yes:t.slice(3),no};
      if(rank===1)return {yes,no:t.slice(2)};
      const code=this.u18Encode(rank,0),begin=rank===2?1:0;
      for(let j=begin;j<t.length;j++)((code>>j)&1?yes:no).push(t[j]);return {yes,no};
    }
    u18BitTerms(j){
      const t=this.u40Tag,terms=[{yes:[t[j]],no:[]}];
      for(let rank=0;rank<4;rank++){
        const p=this.u18Category(rank),lowBits=Math.max(0,3-rank),code=this.u18Encode(rank,0);
        if(j<lowBits)terms.push({yes:[...new Set([...p.yes,t[j]])],no:p.no});
        if(((code>>j)&1)^((rank>>j)&1))terms.push(p);
      }
      return terms;
    }
`);
 return s;
};

