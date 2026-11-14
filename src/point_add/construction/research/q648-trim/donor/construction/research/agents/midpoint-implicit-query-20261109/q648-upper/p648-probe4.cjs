'use strict';
// q648 (papers): forward sign probe rows 0..63 without helper 256 (b256 = A[129], the probe rank's bit-3 host).
// u9ThreeSign generalised to FOUR coefficient hosts: rank tag = [S1,S0,carry,S3,rtop,v[k],f2] + code flag S2 (8 wires).
// Normal lanes have rank >= 4, so S0..S3 (the rotated-in top bits) are zero there and S3 holds rank bit 3 cleanly.
// Ranks 0..3 keep their low coefficient bits in the tag as codes 128 + off_r + low (off = 0,16,24,28; 30 codes),
// categories cat_r on (S2, rtop, S3, carry); the rotation computes rank bits 0..3 into pick (u6RankBit) and bits >= 4
// into their final hosts, as u9ThreeSign does for bits 0..2. Env Q648_P4=0 disables; Q648_P4ROWS=lo-hi limits rows.
const rep=(s,a,b)=>{if(s.split(a).length!==2)throw Error('q648 probe4 anchor '+a.slice(0,70));return s.replace(a,()=>b);};
module.exports.upper=s=>{
  if(process.env.Q648_P4==='0')return s;
  const [lo,hi]=(process.env.Q648_P4ROWS||'0-112').split('-').map(Number);
  // dispatch (forward probe: u5PhaseHost undefined)
  s=rep(s,"      if((this.k<=2||this.k>=63&&this.k<=67)&&this.u5PhaseHost===undefined){this.u9ThreeSign(tape,target);return;}",
   `      if(this.k>=${lo}&&this.k<=${hi}&&(this.u5PhaseHost===undefined||${process.env.Q648_P4RET!=='0'})&&!this.u648VkHost&&!(this.k>=113&&process.env.Q648_P4T113&&!(process.env.Q648_P4T113==='both'||(process.env.Q648_P4T113==='dv1')===(target===this.dv[1])))){this.u648FourSign(tape,target);return;}\n      if((this.k<=2||this.k>=63&&this.k<=67)&&this.u5PhaseHost===undefined){this.u9ThreeSign(tape,target);return;}`);
  if(process.env.Q648_P4F113==='1'||(process.env.Q648_F113==='1'&&process.env.Q648_P4F113!=='0')){
    s=rep(s,"      if((this.k<=2||this.k>=63&&this.k<=67)&&this.u5PhaseHost===undefined){this.u9ThreeSign(tape,target);return;}",
     "      if(this.k>=113&&this.k<=119&&!this.u648Narrow0&&typeof this.u648FourSign==='function'){this.u648FourSign(tape,target);return;}\n      if((this.k<=2||this.k>=63&&this.k<=67)&&this.u5PhaseHost===undefined){this.u9ThreeSign(tape,target);return;}");
    s=rep(s,"        if(this.u40Probe){this.u40Sign(tape,target);return;}\n        const base=this.ab,w=this.half+1;",
     "        if(this.u40Probe){this.u40Sign(tape,target);return;}\n        if(this.k>=119&&this.k<=122&&!this.u648Narrow0&&typeof this.u648FourSign==='function'){this.u648FourSign(tape,target);return;}\n        const base=this.ab,w=this.half+1;");
  }
  // retire probes that take the generic AlignedGeneral.alignedSign (rows 96..119 under u5PhaseHost: no u40Probe)
  if(process.env.Q648_P4RET!=='0')s=rep(s,"    alignedSign(tape,target){\n        if(this.u40Probe){this.u40Sign(tape,target);return;}",
   `    alignedSign(tape,target){\n        if(this.u5PhaseHost!==undefined&&this.k>=${lo}&&this.k<=${hi}&&!(${JSON.stringify((process.env.Q648_P4RSKIP||'').split(',').filter(Boolean).map(Number))}).includes(this.k)&&typeof this.u648FourSign==='function'){if(this.u648VkOk()){const H=Object.create(this);H.u40Probe=true;H.u648VkHost=true;H.u40Sign(tape,target);return;}this.u648FourSign(tape,target);return;}\n        if(this.u40Probe){this.u40Sign(tape,target);return;}`);
  s=rep(s,"        const out=tag.slice();out[3]=host;return out;\n    }\n    alignedSign(tape,target){",
   "        const out=tag.slice();out[3]=host;if(this.u648VkHost){if(out.includes(this.v[this.k])&&out.indexOf(this.v[this.k])!==1)throw Error('U648 vk twice');return out.map((q,i)=>q===f2&&i!==3?this.v[this.k]:q);}return out;\n    }\n    alignedSign(tape,target){");
  s=rep(s,"    u9ThreeSign(tape,target){","    u648VkOk(){if(process.env.Q648_P4R1==='0'||!this.u38ProbeLease||this.tags[1]!==this.v[this.k])return false;const free=this.r.length-this.ab,bits=Math.floor(Math.log2(free))+1;return free!==(1<<bits)-1;}\n    u9ThreeSign(tape,target){");
  // categories for h hosts: positions P=[h,h-1,..,2]; cat_r: yes = extra + P[0..r), no = P[r] (r < h-1)
  s=rep(s,"    u9Category(rank){\n      const t=this.u40Tag,n=t.length-1,yes=[t[n]],no=[];",
   "    u9Category(rank){\n      if(this.u648C){const t=this.u40Tag,f=t[t.length-1],R=this.u648C.Pr.map(i=>t[i]),yes=[f],no=[];R.forEach((q,b)=>((rank>>b)&1?yes:no).push(q));return {yes,no};}\n      if(this.u9H){const t=this.u40Tag,h=this.u9H,P=[];for(let x=h;x>=2;x--)P.push(t[x]);const yes=[t[t.length-1],...P.slice(0,rank)],no=rank<h-1?[P[rank]]:[];return {yes,no};}\n      const t=this.u40Tag,n=t.length-1,yes=[t[n]],no=[];");
  // virtual hosts
  s=rep(s,"host=this.u9Three?this.u6S.slice(0,3):[q0,q1],tp=Object.create(tape);","host=this.u9Three?this.u6S.slice(0,this.u9H||3):[q0,q1],tp=Object.create(tape);");
  s=rep(s,"const base=this.u9Three?[[0],[0,1],[0,1,2]].map(","const base=this.u648C?this.u648C.Pc.map(i=>[cube([tag[tag.length-1],tag[i]])]):this.u9Three?Array.from({length:this.u9H||3},(_,j)=>Array.from({length:j+1},(_,r)=>r)).map(");
  // constBelow correction
  s=rep(s,"for(let rank=0;rank<3;rank++)if(BigInt(rank)<limit){const p=this.u9Category(rank);","for(let rank=0;rank<(this.u9H||3);rank++)if(BigInt(rank)<limit){const p=this.u9Category(rank);");
  // barrel corrections: code lane of rank r rotates by r
  s=rep(s,"const terms=[{yes:[tag[j]],no:[extra]}];if(j<2)terms.push(this.u9Category(j===0?1:2));",
   "const terms=[{yes:[tag[j]],no:[extra]}];if(this.u648C){if(j<2)terms.push({yes:[extra,tag[this.u648C.Pr[j]]],no:[]});}else if(this.u9H){for(let r=1;r<this.u9H;r++)if((r>>j)&1)terms.push(this.u9Category(r));}else if(j<2)terms.push(this.u9Category(j===0?1:2));");
  // tail digit: host bits below cut
  s=rep(s,"const tp=cut>=(this.u9Three?3:2)?tape:this.u6VirtualTape(tape);","const tp=cut>=(this.u9Three?(this.u9H||3):2)?tape:this.u6VirtualTape(tape);");
  const NEW=`    u648FourSign(tape,target){
      const FREE=+(process.env.Q648_P4FREE||647);
      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1,h=bits>=4?4:3;
      const ext=(bits<6&&this.u38ProbeLease&&(this.tags[1]===this.v[this.k]||this.tags[0]===this.v[this.k])&&process.env.Q648_P4EXT!=='0')?[this.v[this.k]]:[];
      if(bits+ext.length<6&&this.u5PhaseHost===target&&this.tags[0]===target&&process.env.Q648_P4F1!=='0')ext.push(target);
      if(2**(h+1)-2>2**(bits+ext.length)||bits+ext.length<h||free>=2**bits)throw Error('U648 capacity '+[this.k,free,h]);
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const rankTag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:(i===3&&h===4)?S[3]:(FREE===647&&q===this.aux[3]&&i===bits-1)?this.A.at(-1):q).concat(ext),tag=rankTag.concat(S[2]),L=rankTag.length;
      if(new Set(tag).size!==tag.length)throw Error('U648 tag collision '+this.k);if(tag.includes(FREE))throw Error('U648 freed helper in tag '+[this.k,tag]);
      if(process.env.Q648_P4LOG&&!globalThis.__P4L?.has(this.k)){(globalThis.__P4L=globalThis.__P4L||new Set()).add(this.k);console.error('P4',this.k,free,JSON.stringify(tag));}
      const CMPX=process.env.Q648_P4C==='0'||L<6?null:{Pc:[1,0,4,3],Pr:L>=7?[5,6]:[5,2]};
      const H=Object.create(this);Object.assign(H,{u40Low:S[0],u40Tag:tag,u6Code:[],u6S:S,u6Tapes:[],u9Three:true,u9H:h,u648C:CMPX});
      const high=this.r.slice(base),top=2**L,off=h===4?[0,16,24,28]:[0,8,12];
      const rotate=rv=>{
        const partial=[...Array(h).fill(this.pick),...rankTag.slice(h)];
        const hiR=()=>this.u10RankHigh(tape,partial,h);
        hiR();stepList(split(0,bits),rv,j=>{const q=j<h?this.pick:rankTag[j];if(j<h)this.u6RankBit(tape,j,q);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[q],rv);if(j<h)this.u6RankBit(tape,j,q);});hiR();
      };
      const swaps=[];
      for(let rank=0;rank<h;rank++){
        const inputs=[],outputs=[];
        for(let low=0;low<2**(h-rank);low++){
          const c=low<<rank;
          inputs.push(rank^((c>>1&1)<<0)^((c&1)<<1)^((c>>2&1)*top)^((c>>3&1)<<3));
          outputs.push(CMPX?top+CMPX.Pc.reduce((v,p,j)=>v|((c>>j&1)<<p),0)+((rank&1)<<CMPX.Pr[0])+((rank>>1&1)<<CMPX.Pr[1]):top+off[rank]+low);
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
      const seq=[rotate,()=>this.rank(tape,rankTag),recode,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,tag,rv),rv=>H.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
      for(const tp of H.u6Tapes)tp.u6Check();
    }
    u9ThreeSign(tape,target){`;
  s=rep(s,"    u9ThreeSign(tape,target){",NEW);
  // Without the rows-113+ switches (Q648_F113 / Q648_P4F113 / Q648_P4T113) the emitted source is byte-identical to 7f183ea's:
  // the generalised S-host lines (h=3|4) are mapped back to their h=4 text (checked by diffing the transformed source).
  if(!(process.env.Q648_F113==='1'||process.env.Q648_P4F113==='1'||process.env.Q648_P4T113)){
    const LEG=[["      const base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1,h=bits>=4?4:3;", "      const h=4,base=this.ab,w=this.half+1,free=this.r.length-base,bits=Math.floor(Math.log2(free))+1;"], ["      const ext=(bits<6&&this.u38ProbeLease&&(this.tags[1]===this.v[this.k]||this.tags[0]===this.v[this.k])&&process.env.Q648_P4EXT!=='0')?[this.v[this.k]]:[];", "      const ext=(bits<6&&this.u38ProbeLease&&this.tags[1]===this.v[this.k]&&process.env.Q648_P4EXT!=='0')?[this.v[this.k]]:[];"], ["      if(2**(h+1)-2>2**(bits+ext.length)||bits+ext.length<h||free>=2**bits)throw Error('U648 capacity '+[this.k,free,h]);", "      if(bits+ext.length<5||free>=2**bits)throw Error('U648 capacity '+[this.k,free]);"], ["      const rankTag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:(i===3&&h===4)?S[3]:(FREE===647&&q===this.aux[3]&&i===bits-1)?this.A.at(-1):q).concat(ext),tag=rankTag.concat(S[2]),L=rankTag.length;", "      const rankTag=this.probeTag(base,this.tags.slice(0,bits),target).map((q,i)=>i===0?S[1]:i===1?S[0]:i===2?this.carry:i===3?S[3]:(FREE===647&&q===this.aux[3]&&i===bits-1)?this.A.at(-1):q).concat(ext),tag=rankTag.concat(S[2]),L=rankTag.length;"], ["      const high=this.r.slice(base),top=2**L,off=h===4?[0,16,24,28]:[0,8,12];", "      const high=this.r.slice(base),top=2**L,off=[0,16,24,28];"], ["        const partial=[...Array(h).fill(this.pick),...rankTag.slice(h)];", "        const partial=[this.pick,this.pick,this.pick,this.pick,...rankTag.slice(4)];"], ["        const hiR=()=>this.u10RankHigh(tape,partial,h);", "        const hiR=()=>this.u10RankHigh(tape,partial,4);"], ["        hiR();stepList(split(0,bits),rv,j=>{const q=j<h?this.pick:rankTag[j];if(j<h)this.u6RankBit(tape,j,q);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[q],rv);if(j<h)this.u6RankBit(tape,j,q);});hiR();", "        hiR();stepList(split(0,bits),rv,j=>{const q=j<4?this.pick:rankTag[j];if(j<4)this.u6RankBit(tape,j,q);const k=(1<<j)%S.length,src=S.slice(-k).concat(S.slice(0,-k));this.permute(tape,S,src,[q],rv);if(j<4)this.u6RankBit(tape,j,q);});hiR();"], ["      if(this.k>=0&&this.k<=112&&(this.u5PhaseHost===undefined||true)&&!this.u648VkHost&&!(this.k>=113&&process.env.Q648_P4T113&&!(process.env.Q648_P4T113==='both'||(process.env.Q648_P4T113==='dv1')===(target===this.dv[1])))){this.u648FourSign(tape,target);return;}", "      if(this.k>=0&&this.k<=112&&(this.u5PhaseHost===undefined||true)&&!this.u648VkHost){this.u648FourSign(tape,target);return;}"]];
    for(const [now,old] of LEG){if(s.split(now).length!==2)throw Error('q648 probe4 legacy map '+now.slice(0,60));s=s.replace(now,()=>old);}
  }
  return s;
};
