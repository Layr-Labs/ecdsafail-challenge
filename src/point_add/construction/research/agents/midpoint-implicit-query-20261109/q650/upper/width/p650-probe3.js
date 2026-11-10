'use strict';
// q650 upper probe: 2-pass data probes in wideBand rows; f1-hosted retire probes in wideBand rows;
// v[k]-hosted rank bit 1 in all non-wideBand probe rows (96..124). See q650_upper.md.
module.exports=[
 [
  "this.permute(tape,word,src,[tag[j]],back);",
  "if(tag[j]===-301)return;this.permute(tape,word,src,tag[j]===-302?[]:[tag[j]],back);"
 ],
 [
  "mark=()=>this.constBelow(tape,tag,BigInt(i-base+1),[],[this.pick]);",
  "mark=()=>this.cmpTag(tape,tag,BigInt(i-base+1),[],[this.pick]);"
 ],
 [
  "const select=()=>{tape.out(NONE,NONE,this.take);this.constBelow(tape,tag,BigInt(i-base+1),[],[this.take]);};",
  "const select=()=>{tape.out(NONE,NONE,this.take);this.cmpTag(tape,tag,BigInt(i-base+1),[],[this.take]);};"
 ],
 [
  "const mark=()=>{tape.out(NONE,NONE,this.take);this.constBelow(tape,tag,BigInt(i-base+1),[],[this.take]);};",
  "const mark=()=>{tape.out(NONE,NONE,this.take);this.cmpTag(tape,tag,BigInt(i-base+1),[],[this.take]);};"
 ],
 [
  "    barrel(tape,word,tag,left,back){",
  "    cmpTag(tape,tag,limit,controls,targets){\n        if(!tag.some(q=>q===-301||q===-302)){this.constBelow(tape,tag,limit,controls,targets);return;}\n        const wires=[],pos=[];let K=0n;\n        tag.forEach((q,i)=>{if(q===-302)K+=1n<<BigInt(i);else if(q!==-301){wires.push(q);pos.push(i);}});\n        let cnt=0n;for(let y=0;y<(1<<wires.length);y++){let L=K;for(let b=0;b<pos.length;b++)if((y>>b)&1)L+=1n<<BigInt(pos[b]);if(L<limit)cnt++;}\n        this.constBelow(tape,wires,cnt,controls,targets);\n    }\n    rankG(tape,wires,G){\n        const high=this.r.slice(this.ab);\n        if(!high.length){for(let k=0;k<wires.length;k++)if((G[0]>>k)&1)tape.out(NONE,NONE,wires[k]);return;}\n        const n=high.length,d=tape.loan([...high,...wires],n+1),coeff=Array.from({length:n+1},(_,i)=>i<n?G[i]^G[i+1]:G[n]);\n        for(const x of high)tape.out(NONE,NONE,x);\n        for(let rep=0;rep<2;rep++){\n            tape.out(NONE,NONE,d[n]);\n            for(let i=n-1;i>=0;i--)tape.out(high[i],d[i+1],d[i]);\n            for(let i=0;i<=n;i++)for(let k=0;k<wires.length;k++)if((coeff[i]>>k)&1)tape.out(NONE,d[i],wires[k]);\n            for(let i=0;i<n;i++)tape.out(high[i],d[i+1],d[i]);\n        }\n        for(const x of high)tape.out(NONE,NONE,x);\n    }\n    q650Passes(tag,free){\n        const lg=tag.length;if(lg<2||tag[1]!==651)return null;\n        const out=[],classes=[],cap=1<<(lg-1);\n        for(const j of [0,1]){const S=[];for(let L=0;L<=free;L++)if(((L>>1)&1)===j)S.push(L);\n            const extra=[];while(S.length>=cap)extra.push(S.pop());\n            classes.push({S,konst:{1:j}});for(const m of extra)classes.push({S:[m],single:true});}\n        for(const c of classes){\n            if(!c.S.length)continue;\n            let tg,wires,enc;\n            if(c.single){const m=c.S[0];tg=tag.map((q,i)=>((m>>i)&1)?-302:-301);wires=[tag[0]];enc=L=>0;}\n            else{const pos=[];tg=tag.map((q,i)=>i===1?(c.konst[1]?-302:-301):q);wires=[];\n                tag.forEach((q,i)=>{if(i!==1){wires.push(q);pos.push(i);}});\n                enc=L=>{let y=0;pos.forEach((p,b)=>{if((L>>p)&1)y|=1<<b;});return y;};}\n            const used=new Set(c.S.map(enc));let sent=-1;for(let y=(1<<wires.length)-1;y>=0;y--)if(!used.has(y)){sent=y;break;}\n            if(sent<0)throw Error('q650 probe pass without sentinel '+[this.k,free,lg]);\n            const mem=new Set(c.S),G=[];for(let L=0;L<=free;L++)G.push(mem.has(L)?enc(L):sent);\n            const yes=wires.filter((q,b)=>(sent>>b)&1),no=wires.filter((q,b)=>!((sent>>b)&1));\n            out.push({tag:tg,wires,G,yes,no});\n        }\n        return out;\n    }\n    barrel(tape,word,tag,left,back){"
 ],
 [
  "        const seq=[\n            ()=>this.rank(tape,tag),rv=>this.barrel(tape,S,tag,true,rv),rv=>this.inc(tape,this.r,[],!rv),\n            rv=>this.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>tape.add(a,D,[],this.carry,rv),\n            rv=>this.alignedMix(tape,a,D,tag,rv),rv=>this.barrel(tape,this.r,tag,false,rv)\n        ];\n        stepList(seq,false,fn=>fn(false));\n        phaseDeposit(this,tape,target,()=>{this.toggle(tape,this.ctrl,[],target);tape.out(NONE,NONE,S.at(-1));this.constBelow(tape,word,this.centeredFree?this.p-(1n<<BigInt(this.k)):this.p,[...this.ctrl,S.at(-1)],[target]);tape.out(NONE,NONE,S.at(-1));});\n        stepList(seq,true,fn=>fn(true));\n    }\n    signProbe(tape,target,back){this.alignedSign(tape,target);}",
  "        const mk=(tg,rk)=>[\n            rk,rv=>this.barrel(tape,S,tg,true,rv),rv=>this.inc(tape,this.r,[],!rv),\n            rv=>this.parkTail(tape,D,tg,rv),()=>this.cnotList(tape,[],D),rv=>tape.add(a,D,[],this.carry,rv),\n            rv=>this.alignedMix(tape,a,D,tg,rv),rv=>this.barrel(tape,this.r,tg,false,rv)\n        ];\n        const lim=this.centeredFree?this.p-(1n<<BigInt(this.k)):this.p;\n        const write=(tgt,yes,no)=>{for(const q of no)tape.out(NONE,NONE,q);\n            this.toggle(tape,[...this.ctrl,...yes,...no],[],tgt);tape.out(NONE,NONE,S.at(-1));\n            this.constBelow(tape,word,lim,[...this.ctrl,...yes,...no,S.at(-1)],[tgt]);tape.out(NONE,NONE,S.at(-1));\n            for(const q of no)tape.out(NONE,NONE,q);};\n        const retire=this.measureTarget===target,vk=this.v[this.k],t1=tag.length>=2&&tag[1]===651;\n        // non-wideBand rows: v[k] (V's top, 1 on taken lanes) hosts rank bit 1; untaken lanes run a reversed garbage body\n        const vHost=t1&&!this.wideBand;\n        const passes=vHost||retire||globalThis.__Q650NOPASS?null:this.q650Passes(tag,free);\n        // retire probe: f1 was just reset by hmr; it hosts rank bit 1 and the phase deposit goes to a dirty y wire\n        const host=!vHost&&retire&&t1&&target===this.dv[0];\n        let tg=tag;if(host){tg=tag.slice();tg[1]=this.dv[0];}\n        if(vHost){tg=tag.slice();tg[1]=vk;tape.out(NONE,this.take,vk);this.noLease=true;}\n        if(!passes){\n            const seq=mk(tg,()=>this.rank(tape,tg));\n            const f1z=!host&&target===this.dv[0]&&(retire||!this.probeBack);\n            this.f1Clean=f1z;stepList(seq,false,fn=>fn(false));this.f1Clean=false;\n            if(host){const d=640;write(d,[],[]);tape.z(d);write(d,[],[]);tape.z(d);}\n            else phaseDeposit(this,tape,target,()=>write(target,[],[]));\n            this.f1Clean=f1z&&retire;stepList(seq,true,fn=>fn(true));this.f1Clean=false;\n            if(vHost){this.noLease=false;tape.out(NONE,this.take,vk);}return;\n        }\n        passes.forEach((ps,pi)=>{\n            const seq=mk(ps.tag,()=>this.rankG(tape,ps.wires,ps.G));\n            const f1z=pi===0&&target===this.dv[0]&&!this.probeBack;\n            this.f1Clean=f1z;stepList(seq,false,fn=>fn(false));this.f1Clean=false;\n            phaseDeposit(this,tape,target,()=>{write(target,[],[]);write(target,ps.yes,ps.no);});\n            stepList(seq,true,fn=>fn(true));\n        });\n    }\n    signProbe(tape,target,back){this.probeBack=back;this.alignedSign(tape,target);}"
 ],
 [
  "      const loan=tape.loan([...z,...S,this.take],1)[0];\n      const ops=dirtyDigit(S,z.slice(0,-1),z.at(-1),this.take,loan);",
  "      if(this.f1Clean){const L2=Object.create(layer);L2.pick=this.dv[0];MixedArithmetic.prototype.digit.call(L2,tape,z,S,[this.take],back);return;}\n      const loan=tape.loan([...z,...S,this.take],1)[0];\n      const ops=dirtyDigit(S,z.slice(0,-1),z.at(-1),this.take,loan);"
 ],
 [
  "const lease=()=>{if(this.useCoefficientDirection&&!this.wideBand)tape.out(NONE,this.take,this.v[this.k]);};",
  "const lease=()=>{if(this.useCoefficientDirection&&!this.wideBand&&!this.noLease)tape.out(NONE,this.take,this.v[this.k]);};"
 ],
 [
  "      if(!this.wideBand&&this.layouts()){layer.digit(tape,z,S,[this.take],back);return;}",
  "      if(!this.wideBand&&this.layouts()&&!this.noLease){layer.digit(tape,z,S,[this.take],back);return;}"
 ]
];
