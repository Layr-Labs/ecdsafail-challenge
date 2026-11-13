'use strict';
// Source-level window allocator. Diagnostic staging has a seventh slot647;
// strict mode rejects it at the first emitted operand. Sign is always646.
exports.wholeStageFreed=false;
exports.upper=(s,{strict=false,selectors=[]}={})=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U37 allocator anchor '+a);s=s.replace(a,()=>b);};
 // Canonicalize U31's private affine ABI without staging swaps. Its body
 // already computes the original logical semantics before its tape adapter.
 const begin=s.indexOf('    u31AffineFramed(tape,back){'),end=s.indexOf('    u31Digit(tape,z,v,controls,back){',begin);
 if(begin<0||end<begin)throw Error('U37 U31 canonical frame');
 const allAffine=s.includes('u36Normalize(tape,a,back){');
 s=s.slice(0,begin)+`    u31AffineFramed(tape,back){return this.affine(tape,back);}
    affine(tape,back){
      ${allAffine?'':'if(this.k<112)return this.u31AffineBody(tape,back);'}
      const tp=Object.create(tape),pick=this.pick;
      tp.ids=tape.ids.filter(q=>q!==pick&&q!==this.qtop);
      tp.out=(a,b,z)=>{if([a,b,z].includes(pick))throw Error('U37 U31 pick use');tape.out(a,b,z);};
      return this.u31AffineBody(tp,back);
    }
`+s.slice(end);
 one('class FoldTape extends Tape {',`
function u37Select(w){
 ${selectors.length?`for(const select of [${selectors.map(f=>f.toString()).join(',')}]){const r=select(w);if(r!==null&&r!==undefined)return r.evict;}`:''}
 if(w.kind==='unit'||w.kind==='boundary')return 646;
 if(['glue','estimate','removeDebt'].includes(w.kind))return 642;
 if(w.kind==='affine')return w.k>=112?642:null;
 if(w.kind==='trial')return w.args[0]===false&&w.k<=112?644:null;
 if(w.kind==='signProbe'){
   const target=w.args[0];
   if(w.k<=112&&w.measureTarget===target&&w.phaseHost===target)return 644;
   if(target===644&&((w.k===125||w.k===126)||(!w.back&&((w.k>=29&&w.k<=62)||w.k===94||w.k===95))))return 643;
 }
 return null;
}
for(const cls of [UnitPreparation,UniversalGeneral,TruncatedGeneral,AlignedGeneral,SingleAffineGeneral,EarlyUnit,EarlyGeneral,OddEstimateGeneral,UnguardedGeneral]){
 for(const name of ['emit','trial','signProbe','affine','estimate','removeDebt']){
  const d=Object.getOwnPropertyDescriptor(cls.prototype,name);if(typeof d?.value!=='function')continue;
  cls.prototype[name]=function(tape,...args){
   const ctl=tape.u37Control;if(!ctl||ctl.active)return d.value.call(this,tape,...args);
   if(name==='emit'&&cls!==EarlyUnit&&cls!==UnguardedGeneral)return d.value.call(this,tape,...args);
   const prev=ctl.window,wasActive=ctl.active;
   const w={kind:name==='emit'?(cls===EarlyUnit?'unit':'glue'):name,k:this.k,back:name==='emit'?args[0]:ctl.back,args,measureTarget:this.measureTarget??null,phaseHost:this.u5CleanPhase??null};
   if(name==='emit')ctl.back=args[0];
   ctl.active=name!=='emit'||cls===EarlyUnit;
   ctl.enter(w,u37Select(w));
   try{return d.value.call(this,tape,...args);}
   finally{ctl.active=wasActive;ctl.enter(prev,prev.evict);}
  };
 }
}
class FoldTape extends Tape {`);
 const prior='for(const q of [256,642,643,644,645,646,647,648,649,650,651]){const j=[256,642,643,644,645,646,648].indexOf(q);map[q>l.g?q-1:q]=q===649?647:j<0?undefined:[512,641,642,643,644,645,646][j];}';
 one(prior,'for(const q of [256,642,643,644,645,646,647,648,649,650,651]){const j=[256,642,643,644,645,648].indexOf(q);map[q>l.g?q-1:q]=q===649?646:q===646?647:j<0?undefined:[512,641,642,643,644,645][j];}');
 one('this.map=map;const wire=x=>{if(x===NONE)return NONE;if(map[x]===undefined)throw Error("upper unresolved logical site "+(x>=l.g?x+1:x));return map[x];};',`
        const slot={256:512,642:641,643:642,644:643,645:644,648:645},cv=q=>q>l.g?q-1:q;
        const ctl={active:false,back:false,window:{kind:'boundary',k:-1,back:false,args:[],evict:646},frame:646,serial:0,windows:[],handoffs:[]};
        this.u37Control=ctl;
        const set=evict=>{for(const q of [256,642,643,644,645,648])map[cv(q)]=q===evict?undefined:slot[q];map[cv(646)]=evict===646?undefined:evict===null?647:slot[evict];};
        const host=evict=>evict===646?null:evict===null?647:slot[evict];
        ctl.enter=(info,evict)=>{
          const old=ctl.frame,a=host(old),b=host(evict),oldWindow=ctl.window;
          const w={...info,evict,id:ctl.serial++,ops:0,ccx:0,firstOffendingGate:null,firstPhysical647:null};
          const boundary={from:oldWindow.id??'initial',to:w.id,oldFrame:old,newFrame:evict,fromKind:oldWindow.kind,toKind:w.kind,k:w.k,back:ctl.back,source:a,destination:b,ops:old===evict||a===null||b===null?0:2,ccx:0,covered:old!==null&&evict!==null};
          if(old!==evict){
            // Preserve explicit frame boundaries through the one final sink.
            // Flush only; never assert all helpers clean at an internal boundary.
            this.u37Flush?.();
            // This is a premise check hook only, never a state-dependent choice.
            globalThis.__u37Boundary?.({tape:this,output,map,old,evict,a,b,w,boundary});
            if(a!==null&&b!==null){output.out(NONE,a,b);output.out(NONE,b,a);}
          }
          ctl.handoffs.push(boundary);ctl.windows.push(w);ctl.frame=evict;ctl.window=w;set(evict);
        };
        set(646);this.map=map;
        const wire=x=>{if(x===NONE)return NONE;const q=x>=l.g?x+1:x,p=map[x];
          if(p===undefined)throw Error('U37 omitted role '+q+' in '+JSON.stringify(ctl.window));
          if(${strict}&&p>=647)throw Error('U37 strict647 first physical '+p+' logical '+q+' window '+JSON.stringify(ctl.window));
          return p;
        };`);
 one('this.physical={out:(a,b,t)=>output.out(wire(a),wire(b),wire(t))};',`
        const note=(kind,qs)=>{const w=ctl.window;w.ops++;if(kind==='gate'&&qs[0]!==NONE)w.ccx++;
          if(w.evict===null){
            if(!w.firstOffendingGate&&qs.includes(cv(642)))w.firstOffendingGate={index:w.ops,kind,logical:qs.map(q=>q===NONE?q:q>=l.g?q+1:q),attemptedEviction:642};
            if(!w.firstPhysical647&&qs.includes(cv(646)))w.firstPhysical647={index:w.ops,kind,logical:qs.map(q=>q===NONE?q:q>=l.g?q+1:q)};
          }
        };
        this.physical={out:(a,b,t)=>{note('gate',[a,b,t]);output.out(wire(a),wire(b),wire(t));}};`);
 one('this.z=q=>output.z(this.toGlobal(q));this.cond=(cond,fn)=>output.cond(cond,fn);this.hist=new Map();',`
        this.z=q=>{note('z',[cv(q)]);output.z(this.toGlobal(q));};
        this.cond=(cond,fn)=>output.cond(cond,fn);this.hist=new Map();`);
 // The symbolic pass must not assume the live sign is a clean helper.
 const clean='for(const q of [512,641,642,643,644,645,646])v.put(q,0);';
 if(s.includes(clean))one(clean,strict?'for(const q of [512,641,642,643,644,645])v.put(q,0);':'for(const q of [512,641,642,643,644,645,647])v.put(q,0);');
 if(s.includes('this.s1Flush=()=>{peep.flush();peep.stage?.();};'))one('this.s1Flush=()=>{peep.flush();peep.stage?.();};','this.s1Flush=()=>{peep.flush();peep.stage?.();};this.u37Flush=()=>peep.flush();');
 if(strict)one('if(a!==null&&b!==null){output.out(NONE,a,b);output.out(NONE,b,a);}',"if(a!==null&&b!==null){if(a>=647||b>=647)throw Error('U37 strict647 handoff to remaining window '+JSON.stringify({boundary,w,firstGate:[NONE,a,b]}));output.out(NONE,a,b);output.out(NONE,b,a);}");
 return s;
};
