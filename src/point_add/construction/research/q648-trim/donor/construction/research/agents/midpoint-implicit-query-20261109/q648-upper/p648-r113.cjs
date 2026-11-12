'use strict';
// ringhole (q648): rows 113..126, the second correction flag dv[1] (was logical 647) relayed so that no helper beyond the seven is needed
// outside the flag probes (whose deposit target / rank host is papers' probe code). Needs j648-u7.cjs (carry-free u7Threshold, u7Debt in 113..126).
// Structural (gate-list) touch map per row: after flag probe 1 the flag moves (take-gated swap) onto carry and stays there: add1 uses pick as
// its carry ancilla, coef^-1 runs mixed with the single control [take] (no carry selector), packNumber / inc Q / the carry-free u7Thresholds
// (rows 113..126) and row 127's threshold never touch carry; threshold(dv1) targets carry.
// The estimate's rank host dv[1] -> logical 256: after packNumber N = R*V+U < 2^256 (I(k)), so 256 is zero on taken lanes and the estimate body
// never touches it; the estimate's normalize writes it on all lanes and normalize^-1 restores it (body is take-gated).
// Test hook: R113_DV1=<wire> re-homes dv[1] for rows >= 113 (e.g. 650 with ban=651) so the probes keep a flag wire until papers' code lands.
const LO=+(process.env.R113_LO||113),HI=+(process.env.R113_HI||127),DV1=process.env.R113_DV1?+process.env.R113_DV1:null;
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('r113 anchor '+a.slice(0,60));s=s.replace(a,()=>b);};
 const inRows="(this.k>="+LO+"&&this.k<="+HI+")";
 // Production dv[1] map: rows 125..127 -> carry (both flag probes leave carry untouched there, structural touch map); rows 113..124 keep 647
 // until the probe owner frees a wire inside the flag probes (R113_DV1 overrides all rows for testing).
 const CARRYLO=+(process.env.R113_CARRYLO||125);
 // The production dv[1] map is papers' p648-flag (applied BEFORE this file): 256 on rows 113..124, carry on 125..127. The hooks below are for testing only.
 if(DV1!==null||process.env.R113_CARRY==='1')one("this.tags=port(Math.ceil(Math.log2(m/2)));this.dv=[f1,f2];this.qtop=q1;",
   "this.tags=port(Math.ceil(Math.log2(m/2)));this.dv=[f1,f2];this.qtop=q1;"+(DV1!==null?"if(k>="+LO+"&&k<="+HI+")this.dv=[f1,"+DV1+"];":"if(k>="+CARRYLO+"&&k<="+HI+")this.dv=[f1,this.carry];"));
 one("const H=Object.create(this.hostRank(this.dv[1]));H.tag=H.tag.slice();if(H.tag.length>=3)H.tag[2]=this.dv[0];if(this.k>=120&&this.k<=125)H.tag[1]=this.dv[1];",
   "const H=Object.create(this.hostRank("+inRows+"?this.A[this.half+1]:this.dv[1]));H.tag=H.tag.slice();if(H.tag.length>=3)H.tag[2]=this.dv[0];if(this.k>=120&&this.k<=125)H.tag[1]="+inRows+"?this.A[this.half+1]:this.dv[1];");
 one("        this.dv.forEach((flag,i)=>seq.push(rv=>this.flagProbe(tape,flag,i,rv),rv=>tape.add(v,this.A,[...ctrl,flag],this.carry,!rv)));",
 String.raw`        if(${inRows}&&process.env.R113_RELAY!=='0'){
          const f2=this.dv[1],P=this.pick,RT=this.r.at(-1),C=this.carry,T=this.take,twoPad=q.slice(-2);
          const sw=(a,b)=>()=>{if(a===b)return;this.toggle(tape,[T,a],[],b);this.toggle(tape,[T,b],[],a);this.toggle(tape,[T,a],[],b);};
          const D=Object.create(this);D.dv=[this.dv[0],C];
          // flag2 lives on carry from the end of flag probe 1 to threshold(dv1): add1 takes pick as its carry ancilla, and coef^-1 runs with
          // the single control [take] (g is the fixed enable), so mixed needs no carry selector.
          seq.push(rv=>this.flagProbe(tape,this.dv[0],0,rv),rv=>tape.add(v,this.A,[...ctrl,this.dv[0]],this.carry,!rv),
            rv=>this.flagProbe(tape,f2,1,rv),sw(f2,C),rv=>tape.add(v,this.A,[...ctrl,C],P,!rv),
            rv=>this.mixed(tape,q,v,u,[T],!rv),rv=>D.removeDebt(tape,rv),coef,rv=>this.affine(tape,rv),
            rv=>this.permute(tape,[...this.bank,...u,...twoPad],[...this.A.slice(0,this.half),...v,...this.A.slice(this.half)],ctrl,rv));
          stepList(seq,back,fn=>fn(back));return;
        }
        this.dv.forEach((flag,i)=>seq.push(rv=>this.flagProbe(tape,flag,i,rv),rv=>tape.add(v,this.A,[...ctrl,flag],this.carry,!rv)));`);
 return s;
};
