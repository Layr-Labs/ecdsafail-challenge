'use strict';
// r35/upper WIP patch list (ours): [group, from, to] over the composed generator (pinned centered-point + centerfix + g129).
// Goal: no gate ever touches logical tags[3] (id 653 = physical 652). Each window re-hosts that rank bit on an idle wire.
const P=[];
const add=(group,from,to)=>P.push([group,from,to]);

// ---- shared helpers (injected into OddEstimateGeneral; visible to UnguardedGeneral rows) ----
add('helpers',
"    layouts(){\n        const K=this.maxShift,out=[];",
`    // r35: fused digit with one dirty loan instead of the clean pick ancilla (same map as digit()).
    digitDirty(tape,z,v,controls,back){
        if(!controls.length){MixedArithmetic.prototype.digit.call(this,tape,z,v,controls,back);return;}
        if(z.length!==v.length+1)throw Error("dirty digit width");
        const multi=controls.length>1,e=multi?this.carry:controls[0];
        if(multi)this.toggle(tape,controls,[],e);
        const loan=tape.loan([...z,...v,e],1)[0];
        stepList(dirtyDigit(v,z.slice(0,-1),z.at(-1),e,loan),back,op=>tape.out(op.length===3?op[0]:NONE,op.length>=2?op[op.length-2]:NONE,op.at(-1)));
        if(multi)this.toggle(tape,controls,[],e);
    }
    // r35: view of this row whose fourth rank bit lives on host; with host===pick every digit goes dirty.
    hostRank(host){
        if(this.tag.length<4)return this;
        const layer=Object.create(this);layer.tag=this.tag.slice();layer.tag[3]=host;layer.rankHost=host;
        if(host===this.pick)layer.digit=this.digitDirty;
        return layer;
    }
    // r35: dest = src + dest with a one-wire top and no carry ancilla (same map as tape.add with a clean carry wire).
    addTop(tape,src,dest,base,inverse){
        const k=src.length,a=src,b=dest.slice(0,k),hi=dest[k];
        if(dest.length!==k+1||k<2)throw Error("top add shape");
        const loans=tape.loan([...a,...dest,...base],4),list=[],cx=(x,y)=>list.push([[x],y]),cc=(x,y,z)=>list.push([[x,y],z]);
        list.push([[...base,a[k-1]],hi]);
        for(let i=1;i<k;i++)cx(a[i],b[i]);
        for(let i=k-2;i>=1;i--)cx(a[i],a[i+1]);
        for(let i=0;i<k-1;i++)cc(a[i],b[i],a[i+1]);
        list.push([[...base,a[k-1],b[k-1]],hi]);
        for(let i=k-1;i>=1;i--){list.push([[...base,a[i]],b[i]]);cc(a[i-1],b[i-1],a[i]);}
        for(let i=1;i<k-1;i++)cx(a[i],a[i+1]);
        list.push([[...base,a[0]],b[0]]);
        for(let i=1;i<k;i++)cx(a[i],b[i]);
        stepList(list,inverse,g=>tape.mc(g[0],g[1],loans));
    }
    // r35: controlled mixed product while pick holds a rank bit. g is the fixed enable of the fold tape, so take alone
    // drives the digits and the idle carry wire is the clean digit ancilla (carry is zero around every digit of mixed()).
    mixedHeld(tape,q,v,rem,controls,back){
        const live=controls.filter(c=>c!==tape.one);
        if(this.rankHost!==this.pick||live.length!==1){this.mixed(tape,q,v,rem,controls,back);return;}
        const layer=Object.create(this);layer.pick=this.carry;layer.digit=MixedArithmetic.prototype.digit;
        layer.mixed(tape,q,v,rem,live,back);
    }
    layouts(){
        const K=this.maxShift,out=[];`);

// ---- TRIAL: rank window normalize..~normalize, rows 0..112: fourth rank bit on pick ----
add('trial',
"            tape.add(D.slice(1,T.length-i),T.slice(i+1),[this.carry],this.pick,back);",
"            const src=D.slice(1,T.length-i),dst=T.slice(i+1);\n            if(this.rankHost===this.pick&&dst.length>src.length)this.addTop(tape,src,dst,[this.carry],back);else tape.add(src,dst,[this.carry],this.pick,back);");
// row 112 (OddEstimateGeneral.trial)
add('trial',
"        const seq=[()=>this.direction(tape),rv=>this.packNumber(tape,rv),rv=>this.normalize(tape,rv)];\n        for(const B of Bs)seq.push(rv=>witness?this.oddWitness(tape,B,rv):this.oddQuotient(tape,B,rv));\n        seq.push(rv=>this.normalize(tape,!rv),rv=>this.packNumber(tape,!rv),()=>this.direction(tape));",
"        const H=this.hostRank(this.pick);\n        const seq=[()=>this.direction(tape),rv=>this.packNumber(tape,rv),rv=>H.normalize(tape,rv)];\n        for(const B of Bs)seq.push(rv=>witness?H.oddWitness(tape,B,rv):H.oddQuotient(tape,B,rv));\n        seq.push(rv=>H.normalize(tape,!rv),rv=>this.packNumber(tape,!rv),()=>this.direction(tape));");
// deep rows (k<=63)
add('trial',
"low=Object.create(this),work=Object.create(this);\n        const rank=this.tag.slice();rank[4]=hi;rank[5]=free;low.tag=rank;work.tag=rank;",
"H=this.hostRank(this.pick),low=Object.create(H),work=Object.create(H);\n        const rank=H.tag.slice();rank[4]=hi;rank[5]=free;low.tag=rank;work.tag=rank;");
// rows 64..111
add('trial',
"      const steps=[dirs,rv=>this.packNumber(tape,rv),moved,rv=>this.normalize(tape,rv)];\n      for(const band of this.layouts())steps.push(rv=>witness?this.oddWitness(tape,band,rv):this.oddQuotient(tape,band,rv));\n      steps.push(rv=>this.normalize(tape,!rv),rv=>moved(!rv),rv=>this.packNumber(tape,!rv),dirs);",
"      const H=this.hostRank(this.pick);\n      const steps=[dirs,rv=>this.packNumber(tape,rv),moved,rv=>H.normalize(tape,rv)];\n      for(const band of H.layouts())steps.push(rv=>witness?H.oddWitness(tape,band,rv):H.oddQuotient(tape,band,rv));\n      steps.push(rv=>H.normalize(tape,!rv),rv=>moved(!rv),rv=>this.packNumber(tape,!rv),dirs);");

// ---- AFFINE: rank window normalizeA..~normalizeA. Rows 0..111: fourth rank bit on pick; rows 112..119: on f2 (idle there) ----
add('affine',
`      if(!this.deep){super.affine(tape,back);return;}
      const layer=Object.create(this);layer.tag=this.tag.slice();layer.tag[4]=this.A[this.half];super.affine.call(layer,tape,back);`,
`      const H=this.hostRank(this.useCoefficientDirection?this.pick:this.dv[1]);
      if(!this.deep){super.affine.call(H,tape,back);return;}
      const layer=Object.create(H);layer.tag=H.tag.slice();layer.tag[4]=this.A[this.half];super.affine.call(layer,tape,back);`);
add('affine',
"        const seq=[rv=>this.mixed(tape,this.r.slice(0,base),a,d,ctrl,rv),tail];",
"        const seq=[rv=>this.mixedHeld(tape,this.r.slice(0,base),a,d,ctrl,rv),tail];");
add('affine',
"            rv=>this.mixed(tape,r,v,d,g,!rv),()=>this.cnotList(tape,g,d),",
"            rv=>this.mixedHeld(tape,r,v,d,g,!rv),()=>this.cnotList(tape,g,d),");

// ---- PROBE2F: the two probes of the two-flag core, rows 113..118 (4-bit rank). Loop level only. ----
// Probe 1 (target f1): fourth rank bit on f2, still clear and not referenced by the probe.
// Probe 2 (target f2): after correction 1 the coefficient A'' = u + q1*v has q <= q1 <= q+1, so
//   r*A'' <= r*v' + r*v < 2p < 2^257, hence bits(r)+bits(A'') <= 258 and the 129-wire split (g129) applies:
//   guards are pick and carry only, and the top coefficient wire A[129] (zero, a guard of the 130 split) hosts the bit.
add('probe2f',
"        for(const flag of this.dv)seq.push(rv=>this.signProbe(tape,flag,rv),rv=>tape.add(v,this.A,[...ctrl,flag],this.carry,!rv));",
"        this.dv.forEach((flag,i)=>seq.push(rv=>this.flagProbe(tape,flag,i,rv),rv=>tape.add(v,this.A,[...ctrl,flag],this.carry,!rv)));");
add('probe2f',
"    select(tape){\n        const high=this.bank.slice(this.h),g=[this.g,this.bank[this.k]];",
`    flagProbe(tape,flag,i,rv){
        const lg=x=>x>0?Math.floor(Math.log2(x))+1:0,a=this.r.length-(this.half+2);
        if(lg(a)<4||typeof this.alignedSign!=="function"){this.signProbe(tape,flag,rv);return;}
        if(this.dv.length!==2||flag!==this.dv[i]||lg(a)!==4||lg(a+1)!==4||this.ab!==this.half+2)throw Error("unhosted two-flag probe");
        const layer=Object.create(this);layer.tags=this.tags.slice();
        if(i===0)layer.tags[3]=this.dv[1];
        else{layer.narrowProbe=true;layer.tags[3]=this.A.at(-1);if(layer.ab!==this.half+1)throw Error("narrow probe split");}
        layer.signProbe(tape,flag,rv);
    }
    select(tape){
        const high=this.bank.slice(this.h),g=[this.g,this.bank[this.k]];`);
add('probe2f',
"if(mode==='off'||a<0||!this.layouts())return wide;",
"if(mode==='off'||a<0||!(this.narrowProbe||this.layouts()))return wide;");

module.exports=P;
