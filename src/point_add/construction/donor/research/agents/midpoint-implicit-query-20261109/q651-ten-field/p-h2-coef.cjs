'use strict';
// h2 upper saving (idea credited to Akashneelesh's 650, 5909718a, q650/upper/p650-coef.js; re-derived for this upper).
// In the forward ladder (PointFoldTape keeps tape.hist) the odd-estimate core runs
//   coef^-1 ; hmr(flag) ; coef
// with nothing else between them (the deferred-phase branch only measures flag). If coef never touches flag,
// coef^-1 and coef commute past the hmr and cancel exactly, so both are dropped.
// This is checked at generation time, fail closed, for every row where it is applied:
//   * both coef calls are recorded on a proxy tape (nothing reaches the real output; any escape throws),
//   * neither list contains an hmr, z, conditional or classical op (they throw),
//   * no recorded gate touches flag (logical wire), including dirty loans,
//   * the coef(false) list is exactly the reverse of the coef(true) list (X/CX/CCX are self-inverse).
// The reverse ladder (rv=true) is unchanged: there the probe sits between the two coef calls.
// H2_COEF=0 disables the rewrite (measurement only).
const ON=process.env.H2_COEF!=='0';
const helper=`
function h2CoefSkip(o,tape,flag,coef){
  const lists=[[],[]],deny=n=>()=>{throw Error('h2 coef: '+n+' inside coef');};
  const realPhys=tape.physical,realHmr=tape.hmr,realZ=tape.z,realCond=tape.cond;
  tape.physical={out:()=>{throw Error('h2 coef: gate escaped the recorder');}};tape.hmr=deny('hmr');tape.z=deny('z');tape.cond=deny('cond');
  try{
    for(const [j,rv] of [[0,true],[1,false]]){
      const rec=Object.create(tape);
      rec.out=(a,b,t)=>{lists[j].push(a+','+b+','+t);if(a===flag||b===flag||t===flag)throw Error('h2 coef: coef touches flag');};
      rec.hmr=deny('hmr');rec.z=deny('z');rec.cond=deny('cond');rec.classical=deny('classical');
      rec.physical={out:()=>{throw Error('h2 coef: direct physical gate');}};
      o.mixed(rec,o.q,o.v,o.u,o.ctrl,rv);
    }
  }finally{tape.physical=realPhys;tape.hmr=realHmr;tape.z=realZ;tape.cond=realCond;}
  const [a,b]=lists;
  if(a.length!==b.length)throw Error('h2 coef: unequal lists');
  for(let i=0;i<a.length;i++)if(a[i]!==b[a.length-1-i])throw Error('h2 coef: coef(false) is not the reverse of coef(true)');
  h2CoefSkip.rows=(h2CoefSkip.rows||0)+1;h2CoefSkip.gates=(h2CoefSkip.gates||0)+2*a.length;
  return true;
}
`;
module.exports=s=>{
  if(!ON)return s;
  const one=(a,b)=>{if(s.split(a).length!==2)throw Error('h2 coef anchor x'+(s.split(a).length-1)+': '+a.slice(0,80));s=s.replace(a,()=>b);};
  one('const v=this.v,q=this.q,g=this.ctrl,flag=this.dv[0],coef=rv=>this.mixed(tape,q,v,this.u,g,rv);',
      'const v=this.v,q=this.q,g=this.ctrl,flag=this.dv[0],coef=rv=>this.mixed(tape,q,v,this.u,g,rv);let h2Skip=false;');
  one('rv=>tape.add(v,this.A,[...g,flag],this.carry,!rv),rv=>coef(!rv),',
      'rv=>tape.add(v,this.A,[...g,flag],this.carry,!rv),rv=>{if(tape.hist&&!rv&&h2CoefSkip(this,tape,flag,coef)){h2Skip=true;return;}coef(!rv);},');
  one('},coef,rv=>this.affine(tape,rv),',
      '},rv=>{if(h2Skip&&!rv){h2Skip=false;return;}coef(rv);},rv=>this.affine(tape,rv),');
  one('\nclass UnguardedGeneral extends OddEstimateGeneral {',helper+'\nclass UnguardedGeneral extends OddEstimateGeneral {');
  return s;
};
