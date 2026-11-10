'use strict';
// U3 complete upper logical652 eviction, after frozen q652 upper lists.
// Includes U2; apply this bundle alone, excluding logical652..656 from dirty loans.
module.exports=[
  [
    "    // r35: view of this row whose fourth rank bit lives on host; with host===pick every digit goes dirty.",
    "    // r36 U: emit a body with virtual control V equal to a stable predicate.\n    uControl(tape,yes,no,run){\n        const V=-1001,owner=this,proxy=Object.create(tape);\n        const hidden=[...yes,...no,...this.tag,...this.tags,this.take];\n        proxy.loan=(used,n)=>tape.loan([...used,...hidden],n);\n        proxy.out=(a,b,t)=>{\n            if(t===V)throw Error(\"virtual selector written\");\n            if(a!==V&&b!==V){tape.out(a,b,t);return;}\n            const more=[a,b].filter(w=>w!==V&&w!==NONE);\n            owner.toggle(tape,[...yes,...more],no,t);\n        };\n        run(proxy,V);\n    }\n    uEq(j){const yes=[],no=[];for(let i=0;i<this.tag.length;i++)((j>>i)&1?yes:no).push(this.tag[i]);return {yes,no};}\n    uTrialRank(witness){\n        const layer=this.hostRank(this.pick);layer.tag=layer.tag.slice();layer.tag[2]=witness?this.carry:this.dv[0];layer.uLift=witness;layer.uSpare=!witness;return layer;\n    }\n    // r35: view of this row whose fourth rank bit lives on host; with host===pick every digit goes dirty."
  ],
  [
    "const H=this.hostRank(this.pick);\n        const seq=[()=>this.direction(tape)",
    "const H=this.uTrialRank(witness);\n        const seq=[()=>this.direction(tape)"
  ],
  [
    "H=this.hostRank(this.pick),low=Object.create(H),work=Object.create(H);",
    "H=this.uTrialRank(witness),low=Object.create(H),work=Object.create(H);"
  ],
  [
    "      const H=this.hostRank(this.pick);\n      const steps=[dirs,",
    "      const H=this.uTrialRank(witness);\n      const steps=[dirs,"
  ],
  [
    "    onesBlock(tape,R,D,n,extra,ctrl,back){\n        const t=this.carry,",
    "    onesBlock(tape,R,D,n,extra,ctrl,back){\n        if(this.uLift){\n            this.uControl(tape,[...ctrl,...extra],[],(tp,V)=>{\n                const layer=Object.create(this);layer.carry=V;layer.uLift=false;\n                // The base method's two selector toggles become no-ops; V is supplied by uControl.\n                layer.toggle=function(t,yes,no,target){if(target===V)return;this.__proto__.toggle.call(this,t,yes,no,target);};\n                layer.onesBlock(tp,R,D,n,extra,ctrl,back);\n            });return;\n        }\n        const t=this.carry,"
  ],
  [
    "    lowReflect(tape,T,w,ctrl,back){\n        const seq=",
    "    lowReflect(tape,T,w,ctrl,back){\n        if(this.uLift){\n            const seq=[()=>this.cnotList(tape,ctrl,T)];\n            for(let j=0;j<T.length-w;j++)if(j<=this.maxShift)seq.push(rv=>{\n                const e=this.uEq(j);this.uControl(tape,[...ctrl,...e.yes],e.no,(tp,V)=>this.inc(tp,T.slice(w+j),[V],rv));\n            });stepList(seq,back,fn=>fn(back));return;\n        }\n        const seq="
  ],
  [
    "    oddProduct(tape,T,D,ctrl,back){\n        stepList",
    "    oddProduct(tape,T,D,ctrl,back){\n        if(this.uLift){\n            stepList(split(0,T.length-1).reverse(),back,i=>{\n                this.uControl(tape,[...ctrl,T[i]],[],(tp,V)=>{\n                    const src=D.slice(1,T.length-i),dst=T.slice(i+1);\n                    if(this.rankHost===this.pick&&dst.length>src.length)this.addTop(tp,src,dst,[V],back);\n                    else tp.add(src,dst,[V],this.pick,back);\n                });\n            });return;\n        }\n        stepList"
  ],
  [
    "    oddQuotient(tape,B,back){\n        this.withDivisor",
    "    oddQuotient(tape,B,back){\n        if(this.uSpare){\n            const layer=Object.create(this);layer.uSpare=false;layer.dv=[B.T.at(-1),this.dv[1]];\n            layer.oddQuotient(tape,B,back);return;\n        }\n        this.withDivisor"
  ],
  [
    "        if(this.tag.length<4)return this;\n        const layer=Object.create(this);layer.tag=this.tag.slice();layer.tag[3]=host;layer.rankHost=host;",
    "        if(this.tag.length<3)return this;\n        const layer=Object.create(this);layer.tag=this.tag.slice();layer.tag[this.tag.length===3?2:3]=host;layer.rankHost=host;"
  ],
  [
    "        const H=this.hostRank(this.dv[1]);\n        const D=this.topDivisor()",
    "        const H=Object.create(this.hostRank(this.dv[1]));H.tag=H.tag.slice();if(H.tag.length>=3)H.tag[2]=this.dv[0];\n        const D=this.topDivisor()"
  ],
  [
    "        if(this.k>112||tag.length<4)return tag;",
    "        if(this.k===63){const out=tag.slice();out[2]=this.aux[3];tag=out;}\n        if(this.k>112||tag.length<4)return tag;"
  ],
  [
    "        if(lg(a)<4||typeof this.alignedSign!==\"function\"){this.signProbe(tape,flag,rv);return;}",
    "        if(lg(a)===3 && (i===0 || this.k>=120)){\n            const layer=Object.create(this);layer.tags=this.tags.slice();\n            if(i===0)layer.tags[2]=this.dv[1];\n            else{layer.narrowProbe=true;layer.tags[2]=this.A.at(-1);if(layer.ab!==this.half+1)throw Error(\"U second probe split\");}\n            layer.signProbe(tape,flag,rv);return;\n        }\n        if(lg(a)<4||typeof this.alignedSign!==\"function\"){this.signProbe(tape,flag,rv);return;}"
  ],
  [
    "      const H=this.hostRank(this.useCoefficientDirection?this.pick:this.dv[1]);\n      if(!this.deep)",
    "      const H=Object.create(this.hostRank(this.useCoefficientDirection?this.pick:this.dv[1]));\n      if(this.k>=64&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.A[this.k<=95?this.half:this.half+1];}\n      if(!this.deep)"
  ],
  [
    "    // r35: view of this row whose fourth rank bit lives on host; with host===pick every digit goes dirty.",
    "    // r36 U2: expand a stable rank comparison as disjoint binary prefix cubes.\n    uLess(limit){\n        const n=this.tag.length,out=[];\n        if(limit<=0)return out;if(limit>=2**n)return [{yes:[],no:[]}];\n        for(let i=0;i<n;i++)if((limit>>i)&1){const yes=[],no=[this.tag[i]];\n            for(let j=i+1;j<n;j++)((limit>>j)&1?yes:no).push(this.tag[j]);out.push({yes,no});}\n        return out;\n    }\n    uSelect(tape,cubes,run){\n        const V=-1002,owner=this,tp=Object.create(tape),hidden=[...this.tag,...this.tags,this.take];\n        tp.loan=(used,n)=>tape.loan([...used,...hidden,...cubes.flatMap(p=>[...p.yes,...p.no])],n);\n        tp.out=(a,b,t)=>{if(t===V)throw Error('write virtual comparison');\n            if(a!==V&&b!==V){tape.out(a,b,t);return;}\n            const more=[a,b].filter(w=>w!==V&&w!==NONE);\n            for(const p of cubes)owner.toggle(tape,[...p.yes,...more],p.no,t);\n        };run(tp,V);\n    }\n    // r35: view of this row whose fourth rank bit lives on host; with host===pick every digit goes dirty."
  ],
  [
    "        const g=this.ctrl,Q=this.q,H=this.hostRank(this.pick);",
    "        const g=this.ctrl,Q=this.q,H=Object.create(this.hostRank(this.pick));\n        if(this.k>=113&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.carry;H.uDebt=true;}"
  ],
  [
    "    installZeros(tape,back){\n        const Q=this.q,sel=this.carry;",
    "    installZeros(tape,back){\n        if(this.uDebt){\n            const Q=this.q;stepList(split(0,this.maxShift),back,j=>this.uSelect(tape,this.uLess(j+1),(tp,V)=>this.permute(tp,[this.n[j],Q[j+2]],[Q[j+2],this.n[j]],[V],back)));\n            tape.out(NONE,NONE,this.n.at(-1));return;\n        }\n        const Q=this.q,sel=this.carry;"
  ],
  [
    "    mixedHead(tape,D,C,back) {\n        const Q=this.q,sel=this.carry;",
    "    mixedHead(tape,D,C,back) {\n        if(this.uDebt){\n            const Q=this.q,stages=[rv=>this.mixed(tape,Q.slice(0,2),D,C,[],rv)];\n            for(let i=2;i<Q.length;i++)stages.push(rv=>this.uSelect(tape,[{yes:[],no:[]},...this.uLess(i-1)],(tp,V)=>{\n                const z=[...C,Q[i]],origins=[...z.slice(1),z[0]],seq=[rr=>this.digit(tp,z,D,[V],!rr),rr=>this.permute(tp,z,origins,[V],rr)];\n                stepList(seq,rv,fn=>fn(rv));\n            }));stepList(stages,back,fn=>fn(back));return;\n        }\n        const Q=this.q,sel=this.carry;"
  ],
  [
    "      if(this.k>=64&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.A[this.k<=95?this.half:this.half+1];}",
    "      if(this.k>=64&&this.k<=119){H.tag=H.tag.slice();H.tag[2]=this.A[this.k<=95?this.half:this.half+1];}\n      if(this.k<64){H.tag=H.tag.slice();H.tag[2]=this.v[this.k];H.u3Affine=true;}"
  ],
  [
    "    affine(tape,back){\n        const a=this.A.slice(0,this.half),",
    "    affine(tape,back){\n        if(this.u3Affine){this.u3AffineBody(tape,back);return;}\n        const a=this.A.slice(0,this.half),"
  ],
  [
    "    layouts(){\n        const K=this.maxShift,out=[];",
    "    // U3: v[k] is the known active leading coefficient bit. Lease it as rank[2].\n    u3AffineBody(tape,back){\n        const a=this.A.slice(0,this.half),r=this.r,v=this.v,D=this.zword.slice(0,this.half),d=D.slice(0,this.h);\n        const base=this.half+1,word=[...r.slice(0,base),...D],tail=r.slice(base),g=this.ctrl;\n        const host=v.at(-1),carry=this.carry;\n        if(this.tag[2]!==host||this.rankHost!==this.pick)throw Error('U3 affine ports');\n        const canon=rv=>this.digit(tape,[...d,this.dv[0]],v,[],rv);\n        const leading=()=>tape.out(NONE,this.take,host);\n        // Carry is zero at these boundaries. Swapping makes the coefficient's top bit zero;\n        // X restores the known active one. During the body carry is arbitrary rank data.\n        const withV=(rv,body)=>{\n            this.permute(tape,[host,carry],[carry,host],[],false);tape.out(NONE,NONE,host);\n            body(rv);\n            tape.out(NONE,NONE,host);this.permute(tape,[host,carry],[carry,host],[],true);\n        };\n        const mixedV=rv=>withV(rv,rr=>{\n            const layer=Object.create(this);layer.digit=this.digitDirty;\n            layer.mixed(tape,r,v,d,[this.take],!rr);\n        });\n        const addV=rv=>withV(rv,rr=>tape.add(v,d,g,this.carry,rr));\n        const seq=[canon,leading,rv=>this.normalizeA(tape,a,rv),\n            rv=>this.guardedBarrel(tape,D,true,rv),rv=>this.parkAffine(tape,D,rv),\n            rv=>this.affineProduct(tape,a,D,rv),rv=>this.guardedBarrel(tape,r,false,rv),\n            rv=>this.reflect(tape,word,g,rv),rv=>this.inc(tape,word,g,!rv),\n            rv=>this.guardedPermutation(tape,[...tail,...D],[...D,...tail],[],rv),\n            mixedV,()=>this.cnotList(tape,g,d),addV,rv=>this.inc(tape,r,g,rv),\n            rv=>this.normalizeA(tape,a,!rv),leading,rv=>canon(!rv)];\n        stepList(seq,back,fn=>fn(back));\n    }\n    layouts(){\n        const K=this.maxShift,out=[];"
  ],
  [
    "      if(this.ab===this.half+2)return [all.b,all.p,all.c];\n      return \"pc\".split('').map(x=>all[x]);",
    "      if(this.ab===this.half+2)return [all.b,all.p];\n      return [all.p];"
  ],
  [
    "const free=this.r.length-base,tag=this.probeTag(base,this.tags.slice(0,free?Math.floor(Math.log2(free))+1:0),target),S=this.A.slice(0,w),D=this.zword.slice(0,w);",
    "const free=this.r.length-base,tag=this.probeTag(base,this.tags.slice(0,free?Math.floor(Math.log2(free))+1:0),target).map((q,i)=>i===2?this.carry:q),S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1);"
  ],
  [
    "rv=>this.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>tape.add(S,D,[],this.carry,rv),\n            rv=>this.alignedMix(tape,S,D,tag,rv),rv=>this.barrel(tape,this.r,tag,false,rv)",
    "rv=>this.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>tape.add(a,D,[],this.carry,rv),\n            rv=>this.alignedMix(tape,a,D,tag,rv),rv=>this.barrel(tape,this.r,tag,false,rv)"
  ],
  [
    "phaseDeposit(this,tape,target,()=>{this.toggle(tape,this.ctrl,[],target);this.constBelow(tape,word,this.centeredFree?this.p-(1n<<BigInt(this.k)):this.p,this.ctrl,[target]);});",
    "phaseDeposit(this,tape,target,()=>{this.toggle(tape,this.ctrl,[],target);tape.out(NONE,NONE,S.at(-1));this.constBelow(tape,word,this.centeredFree?this.p-(1n<<BigInt(this.k)):this.p,[...this.ctrl,S.at(-1)],[target]);tape.out(NONE,NONE,S.at(-1));});"
  ]
];
