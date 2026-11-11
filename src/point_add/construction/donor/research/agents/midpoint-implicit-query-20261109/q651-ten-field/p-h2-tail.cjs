'use strict';
// h2 upper saving (idea credited to Akashneelesh's 650, 5909718a, q650/upper/p650-tail.js; re-derived for this upper).
// The probe tail digits fall back to dirtyDigit (one dirty loan, 4n+5 CCX) whenever the probe has no clean pick
// (wide band U4 probes, U38 leased probes). The clean fused digit (3n+4 CCX) needs one ancilla that is zero on entry
// and is returned to zero. The probe target wire is such an ancilla while it is provably zero:
//   * retire probes (measureTarget===target): the target was just reset by hmr, and phaseDeposit writes and then
//     unwrites it, so it is zero in both halves;
//   * the compute half of a non-retire probe whose target is zero on probe entry: the target is first written by the
//     deposit. Its uncompute half keeps dirtyDigit, which is the same map as the clean digit with a zero ancilla.
// Fail-closed checks, all at generation time:
//   * the target is not among the digit's wires (z, S, take);
//   * while a probe runs, every gate reaching the physical tape is inspected: outside the deposit and outside the
//     clean digits themselves, no gate may write the target. So the target keeps its probe-entry value up to the
//     deposit (and keeps zero after a retire deposit, whose write/unwrite pair restores it);
//   * zero on probe entry is tracked over the whole ladder: a wrapper on the shared physical tape records every
//     written wire and every hmr; a probe converts only if its target was reset by an hmr and not written since
//     (retire probes must satisfy this or the build throws). Only core flag (=dv[0]) probes are considered;
//   * replay mode (tape lanes present) also asserts the target is zero on every lane before and after each
//     converted digit.
// H2_TAIL=0 disables the rewrite.
const ON=process.env.H2_TAIL!=='0';
const FWD=process.env.H2_TAILFWD==='1';
const helper=`
let h2Probe=null;const TAILFWD="__TAILFWD__"==="1";
if(process.env.H2_STATS)process.on('exit',()=>console.error('h2stats tailConverted',h2ProbeRun.converted||0,JSON.stringify(h2ProbeRun.by),JSON.stringify(h2ProbeRun.probes),'coefRows',typeof h2CoefSkip==='function'?h2CoefSkip.rows:'-','coefGates',typeof h2CoefSkip==='function'?h2CoefSkip.gates:'-'));
// Whole-ladder tracker on the shared physical tape: which physical wires were written since their last hmr.
function h2Track(tape){
  const P=tape.physical;if(P.h2Track)return P.h2Track;
  const T={written:new Set(),reset:new Set()},old=P.out;
  P.out=function(a,b,t){T.written.add(t);return old.apply(this,arguments);};
  let base=tape;while(base&&!Object.prototype.hasOwnProperty.call(base,'hmr'))base=Object.getPrototypeOf(base);
  if(!base)throw Error('h2 tail: no hmr owner');
  const oh=base.hmr,one=tape.one;
  base.hmr=function(q){const p=(one!==undefined&&q>one)?q-1:q;T.written.delete(p);T.reset.add(p);return oh.apply(this,arguments);};
  P.h2Track=T;return T;
}
function h2ProbeRun(o,tape,target,body){
  if(h2Probe)throw Error('h2 tail: nested probe');
  const T=h2Track(tape);
  const retire=o.measureTarget===target,P=tape.physical,old=P.out;
  const ctx={target,retire,half:0,inDeposit:false,inDigit:false,o,tape,phys:null};
  // physical index of the logical target as FoldTape.out forwards it (enable wire removed, ids above it shift down)
  ctx.phys=(tape.one!==undefined&&target>tape.one)?target-1:target;
  // Zero on entry: retire probes run right after hmr(target); otherwise require an earlier hmr(target) and no write since.
  ctx.zeroEntry=T.reset.has(ctx.phys)&&!T.written.has(ctx.phys);
  // H2_TAILFWD=1 (separate, opt-in): forward-ladder core probes (tape.hist present, non-retire) are also treated as
  // zero on entry. Argument: the core defers this probe's predicate with hmr(flag) and replays the phase in the
  // reverse ladder as cond(ms, z(flag)) after recomputing the predicate on a flag that is zero there (the mirrored
  // state just after the forward hmr). The base circuit's phase is exact only if the forward flag held exactly the
  // predicate at the hmr, i.e. flag was zero at this probe's entry. So this holds on every input where the base
  // itself is exact; it is not proved independently here (the static tracker cannot see the U3 affine's
  // canon compute/uncompute of dv[0] cancel).
  if(!ctx.zeroEntry&&!retire&&TAILFWD&&tape.hist&&o.h2CoreProbe===target)ctx.zeroEntry=ctx.implied=true;
  if(retire&&!ctx.zeroEntry)throw Error('h2 tail: retire target not freshly reset');
  if(process.env.H2_STATS){const m=h2ProbeRun.probes||(h2ProbeRun.probes={}),key=(retire?'retire':'fwd')+(ctx.zeroEntry?'Z':'N');m[key]=(m[key]||0)+1;}
  P.out=function(a,b,t){if(!ctx.inDeposit&&!ctx.inDigit&&t===ctx.phys)throw Error('h2 tail: probe target written outside the deposit');return old.apply(this,arguments);};
  h2Probe=ctx;
  try{body();}finally{h2Probe=null;P.out=old;}
}
`;
module.exports=s=>{
  if(!ON)return s;
  const one=(a,b)=>{if(s.split(a).length!==2)throw Error('h2 tail anchor x'+(s.split(a).length-1)+': '+a.slice(0,80));s=s.replace(a,()=>b);};
  // Probe entry from the odd-estimate core: only the core's flag (=dv[0]) probes are converted.
  one('    signProbe(tape,target,back){this.alignedSign(tape,target);}',
      '    signProbe(tape,target,back){if(target!==this.dv[0]||!(tape.physical&&typeof tape.physical.out==="function")){this.alignedSign(tape,target);return;}const prev=this.h2CoreProbe;this.h2CoreProbe=target;try{h2ProbeRun(this,tape,target,()=>this.alignedSign(tape,target));}finally{this.h2CoreProbe=prev;}}');
  // Deposit boundary: writes to the target are allowed only inside it; afterwards a non-retire target is no longer zero.
  one('function phaseDeposit(o,tape,wire,write){write();if(o.measureTarget===wire){tape.z(wire);write();}}',
      'function phaseDeposit(o,tape,wire,write){const c=h2Probe&&h2Probe.target===wire?h2Probe:null;if(c){if(c.inDeposit)throw Error("h2 tail: nested deposit");c.inDeposit=true;}write();if(o.measureTarget===wire){tape.z(wire);write();}if(c){c.inDeposit=false;c.half++;}}');
  one('      if(!this.u38ProbeLease&&!this.wideBand&&this.layouts()){layer.digit(tape,z,S,[this.take],back);return;}\n      const loan=tape.loan([...z,...S,this.take],1)[0];',
      `      if(!this.u38ProbeLease&&!this.wideBand&&this.layouts()){layer.digit(tape,z,S,[this.take],back);return;}
      {const c=h2Probe;
       if(c&&c.zeroEntry&&!c.inDeposit&&(c.retire?c.half<=1:c.half===0)){
        const w=c.target;if(z.includes(w)||S.includes(w)||w===this.take)throw Error('h2 tail: target overlaps digit');
        if(c.half>1)throw Error('h2 tail: second deposit');
        const lanes=c.tape.physical&&c.tape.physical.batches;
        if(lanes){for(const r of lanes)if(r[c.phys]!==0)throw Error('h2 tail: target not zero at clean digit');}
        const L2=Object.create(layer);L2.pick=w;L2.carry=this.take;
        c.inDigit=true;try{MixedArithmetic.prototype.digit.call(L2,this.u40Tag?this.u40Tape(tape):tape,z,S,[this.take],back);}finally{c.inDigit=false;}
        if(lanes){for(const r of lanes)if(r[c.phys]!==0)throw Error('h2 tail: target not restored by clean digit');}
        h2ProbeRun.converted=(h2ProbeRun.converted||0)+1;if(process.env.H2_STATS){const m=h2ProbeRun.by||(h2ProbeRun.by={}),key=(c.retire?'retire':c.implied?'implied':'fwd')+c.half;m[key]=(m[key]||0)+1;}return;
       }}
      const loan=tape.loan([...z,...S,this.take],1)[0];`);
  one('\nclass UnguardedGeneral extends OddEstimateGeneral {',helper.replace('__TAILFWD__',FWD?'1':'0')+'\nclass UnguardedGeneral extends OddEstimateGeneral {');
  return s;
};
