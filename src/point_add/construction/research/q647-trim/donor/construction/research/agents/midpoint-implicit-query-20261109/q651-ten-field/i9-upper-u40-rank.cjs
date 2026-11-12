'use strict';
// On valid U34 codes, each signed rotation sum is a Boolean decoded rank bit.
// Compute that parity once per involution using a value-independent dirty echo.
exports.upper=s=>{
 const begin=s.indexOf('      if(this.u34Low){\n        const n=this.u34Low;\n        stepList(split(0,tag.length),back,j=>{');
 const end=s.indexOf('      if(this.u29Dense){',begin);
 if(begin<0||end<begin)throw Error('U40 rank barrel anchor');
 const block=s.slice(begin,end);
 const old='          stepList(terms,back,p=>{for(const q of p.no)tape.out(NONE,NONE,q);this.u10ControlledPermutation(tape,word,src,p.yes.concat(p.no),back!==!!p.inverse);for(const q of p.no)tape.out(NONE,NONE,q);});';
 if(block.split(old).length!==2)throw Error('U40 rank terms anchor');
 const replacement=`          const pos=new Map(word.map((q,i)=>[q,i])),perm=src.map(q=>pos.get(q)),seen=new Set(),layers=[[],[]];
          for(let i=0;i<perm.length;i++)if(!seen.has(i)){const cyc=[];let v=i;while(!seen.has(v)){seen.add(v);cyc.push(word[v]);v=perm[v];}const len=cyc.length;
            for(let h=0;h<len;h++){const a=(len-h)%len;if(h<a)layers[0].push([cyc[h],cyc[a]]);const b=(len-1-h)%len;if(h<b)layers[1].push([cyc[h],cyc[b]]);}}
          const d=tape.loan([...word,...tag],1)[0],mark=()=>this.u10Terms(tape,terms,d);
          stepList(layers,back,pairs=>{const body=()=>{for(const [a,b]of pairs)this.gatedSwap(tape,a,b,[d],[]);};body();mark();body();mark();});`;
 return s.slice(0,begin)+block.replace(old,replacement)+s.slice(end);
};
