'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U10 anchor '+a);s=s.replace(a,()=>b);};
 one('      const rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);});',`      const rotate=rv=>{
        const partial=[this.pick,this.pick,...tag.slice(2)];
        // Higher rank bits fit their final helpers before the coefficient rotates.
        const hi=()=>this.u10RankHigh(tape,partial);
        hi();stepList(split(0,bits),rv,j=>{const q=j<2?this.pick:tag[j];if(j<2)this.u6RankBit(tape,j,q);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[q],rv);if(j<2)this.u6RankBit(tape,j,q);});hi();
      };`);
 one('      const recode=rv=>{const ops=[...codes.slice(0,3).map((c,i)=>rr=>this.u6Transpose(tape,tag,i+1,c,[],high,rr)),rr=>this.u6Transpose(tape,tag,0,codes[3],[low],high.slice(1),rr)];stepList(ops,rv,fn=>fn(rv));};',`      const recode=rv=>{
        const zero=rr=>{const mark=()=>this.toggle(tape,[],high,this.pick);mark();const ops=codes.slice(0,3).map((c,i)=>bb=>this.u6Transpose(tape,tag,i+1,c,[this.pick],[],bb));stepList(ops,rr,fn=>fn(rr));mark();};
        const unit=rr=>{const mark=()=>this.toggle(tape,[low],high.slice(1),this.pick);mark();this.u6Transpose(tape,tag,0,codes[3],[this.pick],[],rr);mark();};
        stepList([zero,unit],rv,fn=>fn(rv));
      };`);
 one('    u6RankBit(tape,j,target){',`    u10RankHigh(tape,tag){
      const high=this.r.slice(this.ab),n=high.length,d=tape.loan([...high,...tag],n+1),coeff=Array(n+1).fill(0);
      for(let i=0;i<n;i++){coeff[i]^=i+1;coeff[i+1]^=i+1;}
      for(const q of high)tape.out(NONE,NONE,q);
      for(let e=0;e<2;e++){tape.out(NONE,NONE,d[n]);for(let i=n-1;i>=0;i--)tape.out(high[i],d[i+1],d[i]);for(let i=0;i<=n;i++)for(let j=2;j<tag.length;j++)if(coeff[i]>>j&1)tape.out(NONE,d[i],tag[j]);for(let i=0;i<n;i++)tape.out(high[i],d[i+1],d[i]);}
      for(const q of high)tape.out(NONE,NONE,q);
    }
    u10ControlledPermutation(tape,word,src,controls,back){
      // Each permutation is two involutions. Dirty control echo is exact for each.
      const pos=new Map(word.map((q,i)=>[q,i])),p=src.map(q=>pos.get(q)),seen=new Set(),layers=[[],[]];
      for(let i=0;i<p.length;i++)if(!seen.has(i)){const cyc=[];let j=i;while(!seen.has(j)){seen.add(j);cyc.push(word[j]);j=p[j];}const n=cyc.length;
        for(let j=0;j<n;j++){const a=(n-j)%n;if(j<a)layers[0].push([cyc[j],cyc[a]]);const b=(n-1-j)%n;if(j<b)layers[1].push([cyc[j],cyc[b]]);}}
      const d=tape.loan([...word,...controls],1)[0],mark=()=>this.toggle(tape,controls,[],d);
      stepList(layers,back,pairs=>{const body=()=>{for(const [a,b]of pairs)this.gatedSwap(tape,a,b,[d],[]);};body();mark();body();mark();});
    }
    u6RankBit(tape,j,target){`);
 one('this.permute(tape,word,src,tag,rv);for(const q of no)', 'this.u10ControlledPermutation(tape,word,src,tag,rv);for(const q of no)');
 one('        for(const c of terms)H.toggle(tape,c.yes,c.no,t);',`        H.u10Terms(tape,terms,t);`);
 one('    u10RankHigh(tape,tag){',`    u10Terms(tape,terms,t){
      const cost=(p,n)=>2*n+(p+n<3?1:4*(p+n)-8);
      const raw=terms.reduce((v,c)=>v+cost(c.yes.length,c.no.length),0);
      const common={yes:terms.length?terms[0].yes.filter(q=>terms.every(c=>c.yes.includes(q))):[],no:terms.length?terms[0].no.filter(q=>terms.every(c=>c.no.includes(q))):[]};
      const rest=terms.map(c=>({yes:c.yes.filter(q=>!common.yes.includes(q)),no:c.no.filter(q=>!common.no.includes(q))}));
      const fact=2*cost(common.yes.length,common.no.length)+2*rest.reduce((v,c)=>v+cost(c.yes.length+1,c.no.length),0);
      if(fact<raw){const used=[t,...terms.flatMap(c=>c.yes.concat(c.no))],d=tape.loan(used,1)[0];const mark=()=>this.toggle(tape,common.yes,common.no,d),body=()=>{for(const c of rest)this.toggle(tape,[d,...c.yes],c.no,t);};mark();body();mark();body();}
      else for(const c of terms)this.toggle(tape,c.yes,c.no,t);
    }
    u10RankHigh(tape,tag){`);
 one('    tailDigit(tape,layer,z,S,back){',`    tailDigit(tape,layer,z,S,back){
      if(this.u6Code){
        // The tail enable is rank >= i-ab+1. Active digits therefore have
        // i-ab+1 zero low divisor bits. Disabled fused digits are identity.
        const i=this.r.indexOf(z.at(-1)),cut=i-this.ab+1;
        if(cut<1)throw Error('U10 tail threshold');
        const V=S.slice(cut),Z=z.slice(cut),loan=tape.loan([...z,...S,this.take],1)[0];
        const tp=cut>=2?tape:this.u6VirtualTape(tape);
        stepList(dirtyDigit(V,Z.slice(0,-1),Z.at(-1),this.take,loan),back,op=>tp.out(op.length===3?op[0]:NONE,op.length>=2?op[op.length-2]:NONE,op.at(-1)));
        return;
      }`);
 return s;
};
