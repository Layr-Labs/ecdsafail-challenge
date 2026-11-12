'use strict';
// q648 (papers): flagProbe rows 113+ follow dv[1] instead of the fixed f2 wire (aux[3]).
// In rows 113..126 dv = [f1, f2]: f2 IS the row's second flag. flagProbe(i=0) already hosts a rank bit on dv[1] (zero then);
// the aligned probe's tag map names aux[3] explicitly at rows 119..122 for the dv[0] probe: that becomes dv[1], so a
// row-level re-home of dv[1] (ringhole's) carries the probes with it. Env Q648_FLAG=0 disables.
// Test hook: Q648_DV1=<wire> re-homes dv[1] for k >= Q648_DV1K (default 113) in the row constructor.
module.exports.upper=s=>{
  if(process.env.Q648_FLAG==='0')return s;
  const rep=(a,b)=>{if(s.split(a).length!==2)throw Error('q648 flag anchor '+a.slice(0,60));s=s.replace(a,()=>b);};
  rep("          if(this.k===119)return target===this.dv[0]?this.aux[3]:q;\n          if(this.k>=120&&this.k<=122)return target===this.dv[0]?this.aux[3]:this.A.at(-1);",
      "          if(this.k===119)return target===this.dv[0]?this.dv[1]:q;\n          if(this.k>=120&&this.k<=122)return target===this.dv[0]?this.dv[1]:this.A.at(-1);");
  // Q648_DV1MAP="113-118=256,119=650,..." re-homes dv[1] per row band (rows not listed keep f2).
  // Q648_F113=1 bundles the measured rows-113+ contract with ringhole's p648-u7 + p648-r113: dv[1] := X with X = 256 (113..124),
  // carry (125..127); probe 1 narrow at 119,123,124 (S-host routine at 119,123); probe 0 narrow (their code, rank on X) at 113..118,120..122.
  const B=process.env.Q648_F113==='1';
  const MAP=(process.env.Q648_DV1MAP||(B?'113-124=256,125-127=643':'')).split(',').filter(Boolean).map(x=>{const [r,w]=x.split('=');const [lo,hi]=r.split('-').map(Number);return [lo,hi===undefined?lo:hi,+w];});
  if(process.env.Q648_DV1)MAP.push([+(process.env.Q648_DV1K||113),127,+process.env.Q648_DV1]);
  if(MAP.length)rep("this.dv=[f1,f2];this.qtop=q1;",
      "this.dv=[f1,(("+JSON.stringify(MAP)+").find(([a,b])=>k>=a&&k<=b)||[0,0,f2])[2]];this.qtop=q1;");
  // Q648_FNARROW=k,..: flag probe 1 in these rows takes the narrow layer (base half+1, guard top [pick]) even where their
  // same-width rule keeps it wide, so 256 is free at the deposit; rows in Q648_FN4 (default 119,123) run papers' S-host
  // routine there (rank width = free+1 bits), the others keep their own tag.
  const NR=(process.env.Q648_FNARROW||(B?'119,123,124':'')).split(',').filter(Boolean).map(Number),N4=(process.env.Q648_FN4||'119,123').split(',').filter(Boolean).map(Number);
  // Q648_F0NARROW=k,..: flag probe 0 in these rows also takes the narrow layer, but keeps THEIR code (rank bit on dv[1]=X):
  // with base half+1 the guard top is [pick], so X=256 is free to be its rank host.
  const N0=(process.env.Q648_F0NARROW||(B?'113,114,115,116,117,118,120,121,122':'')).split(',').filter(Boolean).map(Number);
  if(N0.length)rep("    flagProbe(tape,flag,i,rv){\n","    flagProbe(tape,flag,i,rv){\n        if(i===0&&"+JSON.stringify(N0)+".includes(this.k)){const layer=Object.create(this);layer.tags=this.tags.slice();layer.tags[3]=this.dv[1];layer.narrowProbe=true;layer.u648Narrow=true;layer.u648Narrow0=true;if(layer.ab!==this.half+1)throw Error('q648 narrow0 '+this.k);layer.signProbe(tape,flag,rv);return;}\n");
  if(NR.length){
    rep("    flagProbe(tape,flag,i,rv){\n","    flagProbe(tape,flag,i,rv){\n        if(i===1&&"+JSON.stringify(NR)+".includes(this.k)){const layer=Object.create(this);layer.tags=this.tags.slice();layer.narrowProbe=true;layer.u648Narrow=true;layer.tags[2]=this.A.at(-1);if(layer.ab!==this.half+1)throw Error('q648 narrow '+this.k);layer.signProbe(tape,flag,rv);return;}\n");
    rep("    get ab(){\n      if(!this.r)return undefined;","    get ab(){\n      if(!this.r)return undefined;if(this.u648Narrow)return this.half+1;");
    rep("        const base=this.ab,w=this.half+1;\n        if(this.r.length<this.half+2){super.signProbe(tape,target,false);return;}",
        "        if(this.u648Narrow&&"+JSON.stringify(N4)+".includes(this.k)&&!this.u40Probe&&typeof this.u648FourSign==='function'){this.u648FourSign(tape,target);return;}\n        const base=this.ab,w=this.half+1;\n        if(this.r.length<this.half+2){super.signProbe(tape,target,false);return;}");
  }
  return s;
};
