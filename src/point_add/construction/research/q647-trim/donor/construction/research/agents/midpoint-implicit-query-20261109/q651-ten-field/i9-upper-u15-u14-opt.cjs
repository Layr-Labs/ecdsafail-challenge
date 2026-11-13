'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U14 anchor '+a);s=s.replace(a,()=>b);};
 // U9 has THREE encoded coefficient sites: cut=2 still needs virtual S2.
 one('const tp=cut>=2?tape:this.u6VirtualTape(tape);','const tp=cut>=(this.u9Three?3:2)?tape:this.u6VirtualTape(tape);');
 // U10 shared high-rank calculation, generalized to the three-site code.
 one('u10RankHigh(tape,tag){','u10RankHigh(tape,tag,first=2){');
 one('for(let j=2;j<tag.length;j++)if(coeff[i]>>j&1)','for(let j=first;j<tag.length;j++)if(coeff[i]>>j&1)');
 one('      const rotate=rv=>stepList(split(0,bits),rv,j=>{this.u6RankBit(tape,j,this.pick);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[this.pick],rv);this.u6RankBit(tape,j,this.pick);});',`      const rotate=rv=>{
        const partial=[this.pick,this.pick,this.pick,...rankTag.slice(3)];
        const hi=()=>this.u10RankHigh(tape,partial,3);
        hi();stepList(split(0,bits),rv,j=>{const q=j<3?this.pick:rankTag[j];if(j<3)this.u6RankBit(tape,j,q);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[q],rv);if(j<3)this.u6RankBit(tape,j,q);});hi();
      };`);
 // Recode before parkTail: pick is still clean. Cache each rank predicate.
 one('        for(const [from,to]of seq)swaps.push(rv=>this.u6Transpose(tape,tag,from,to,yes,no,rv));',`        swaps.push(rv=>{const mark=()=>this.toggle(tape,yes,no,this.pick);mark();stepList(seq,rv,([from,to])=>this.u6Transpose(tape,tag,from,to,[this.pick],[],rv));mark();});`);
 // Dirty echo remains valid after parkTail, when pick may carry data.
 one('this.permute(tape,word,src,p.yes.concat(p.no),back);','this.u10ControlledPermutation(tape,word,src,p.yes.concat(p.no),back);');
 return s;
};
