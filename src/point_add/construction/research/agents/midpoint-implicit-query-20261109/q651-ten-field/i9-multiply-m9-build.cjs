'use strict';
const old={edit(s,a,b){if(s.split(a).length!==2)throw Error('M9 source anchor '+a);return s.replace(a,()=>b);}},{compactNormal}=require('./i9-multiply-m9-compact-normal.cjs'),{lowerer}=require('./i9-multiply-m9-encoded-lowerer.cjs'),{powerFactory}=require('./i9-multiply-m9-simple-power.cjs');
module.exports=function build(b,pub,wrapSparse){let f=require('./i9-multiply-m9-shifted-lift.cjs')(b.f);
 f=old.edit(f,'run(norm);',"sink('m9normal',[false,true]);");f=old.edit(f,'run(unn,true);',"sink('m9normal',[true,false]);");
 f=old.edit(f,'for(const [G,ops,rv,map] of all){const inv=rv!==!!reverse;',"for(const [G,ops,rv,map] of all){const inv=rv!==!!reverse;if(ops===nrm){M9N(inv);continue;}");
 f=old.edit(f,'function power(back){const parts=m6powerParts(128,T,H,S,en,L,kappa,extra);if(back)parts.reverse();for(const part of parts)run(part(),back);}','function power(back){M9P(back);}');
 const p=Function('module',f+';return {fr,MCX,negate,incReg,digit};')({exports:{}});
 function mul(sink){let enc=null,ops=0,buf=[],capture=null;const flush=()=>{if(buf.length){sink('packed',buf);buf=[];}};
 const emit=(a,b,t)=>{if([a,b,t].some(q=>q!==1023&&q>=646))throw Error('physical forbidden '+[a,b,t]);if(a===t||b===t||a===b&&a!==1023)throw Error('physical alias');const g=(a<<20)|(b<<10)|t;if(capture){capture.push(g);return;}ops++;buf.push(g);if(buf.length>=4096)flush();},raw=r=>emit(r.length>1?r[0]:1023,r.length>2?r[1]:1023,r.at(-1));
 const normal=(reverse,qmove=false)=>{flush();if(reverse){console.log('M9 LOWER CHECK',JSON.stringify(enc.stats()));enc.check();enc=null;}const T=Array.from({length:128},(_,i)=>i),H=T.map(i=>384+i),S=Array.from({length:6},(_,i)=>640+i),L=Array.from({length:256},(_,i)=>128+i),g=compactNormal(T,H,S,L,p,qmove);if(reverse)g.reverse();for(const r of g)raw(r);if(!reverse)enc=lowerer(emit,p);flush();};
 const gate=(a,b,t)=>enc?enc.gate(a,b,t):emit(a,b,t);
 const power=back=>{flush();enc.check();const pf=powerFactory(p,raw,r=>gate(r.length>1?r[0]:1023,r.length>2?r[1]:1023,r.at(-1)),()=>enc.check());pf.erase();for(let k=0;k<127;k++){const i=back?126-k:k;capture=[];pf.iteration(i);const g=capture;capture=null;if(back)g.reverse();for(const x of g)emit(x>>>20&1023,x>>>10&1023,x&1023);}pf.erase();flush();console.log('M9 POWER DONE',back,JSON.stringify(enc.stats()));};
 const sourceSink=(k,d)=>{if(k==='m9normal'){normal(...d);return;}if(k==='nct')for(const r of d)gate(r.length>1?r[0]:1023,r.length>2?r[1]:1023,r.at(-1));else if(k==='packed')for(const x of d)gate(x>>>20&1023,x>>>10&1023,x&1023);else{flush();sink(k,d);}};
 const fn=Function('module','Replacement','dirtyDigit','lowValuationSweep','plusOneMod','M9N','M9P',f+';return emitForward128;')({exports:{}},b.Walk,pub.dirtyDigit,pub.lowValuationSweep,pub.plusOneMod,normal,power);
 try{fn(sourceSink);flush();}catch(e){if(enc)console.log('M9 LOWER FAILURE',JSON.stringify(enc.stats()));throw e;}
 }
 const emitMultiplySparse=sink=>{const mapped=pub.mapped(sink,false),p=wrapSparse(mapped,{window:4096,mode:'commute'});mul(p.sink);p.flush();};
 return{mul,f,emitMultiplySparse};
};
