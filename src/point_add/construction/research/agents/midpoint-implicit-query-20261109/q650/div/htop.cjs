'use strict';
// q650 divide: route the top quotient bit (Htop, logical 640) through data hosts instead of logical 640.
// Stage A (this file so far): split .. alpha exit.
//   norm/high/split : the high digit is written to Q[6] (Q is zero at entry and idle there).
//   outer walk      : Q[6] (the walk uses Q[0..5],Q[124..127] only).
//   alpha entry     : Q[6] -> Q[125] (zero for every lane: alpha not yet written; c5,c6 on Q[126],Q[127]).
//   alpha, class t<=125 : Q[125] stays (alpha's slice is Q[0..t-1]).
//   alpha, class 126 : moved to class 126's U top u[125]=L[4] (U<V/2), class 126 now uses the special path
//                      that omits U's top; c5 stays on Q[126] (outside alpha's slice).
//   alpha, class 127 : XOR-hosted on L[1] (L[1]=1^Htop): g=gcd(Mn,r) in {2,3}, so L[1]=1 is known.
//   alpha, class 128 : g=1, V=Mn. V odd => s=0 => count bit c0 (641) is zero and untouched in alpha: host 641.
//                      V even => V[0]=0: host V[0] during the body with V[0] substituted as constant 0, then
//                      XOR-host on U[0]=L[129] (L[129]=1^Htop; U odd since gcd(U,V)=1), restoring V[0]=0 before the selector.
//   Two class-128 bodies run (V odd, then V even); each is selected by V[127] and V[0].
// Q650_HTOP_STAGE=A returns Htop to logical 640 at alpha exit (validation of stage A only).
module.exports=function(d){
  const rep=(a,b)=>{if(d.split(a).length!==2)throw Error('htop anchor x'+(d.split(a).length-1)+': '+a.slice(0,90));d=d.replace(a,()=>b);};
  // W0 / qsplit: separate high-digit lists for the split (h=Q[6]) and its qsplit uncompute (h=HR).
  rep("high=digit(n,M,H,Htop)","high=digit(n,M,H,Q[6]),HR=process.env.Q650_HTOP_STAGE==='A'?Htop:L[n+1],highR=digit(n,M,H,HR)");
  rep("put(rev(split));put(rev(high));","put(rev(split));put(rev(highR));");
  // outer walk -> alpha
  rep("put(rev(ss));tap('outer');","put(rev(ss));put([[Q[6],Q[n-3]],[Q[n-3],Q[6]]]);tap('outer');");
  // D2Alpha: substitution-aware put, class 126 into the special path, per-class hosts.
  rep("function D2Alpha(n,terms,L,R,J,sign,loan,ws,sink){const e=ws[0],v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink('nct',g);let added=0;",
      "function D2Alpha(n,terms,L,R,J,sign,loan,ws,sink){const e=ws[0],v=Array.from({length:n},(_,j)=>R[n+1-j]),u=Array.from({length:n},(_,j)=>L[n+1-j]);let SUB=-1;const put=g=>{if(SUB<0){sink('nct',g);return;}const o=[];for(const r of g){if(r[r.length-1]===SUB)throw Error('htop: substituted V0 is a target');if(!r.slice(0,-1).includes(SUB))o.push(r);}sink('nct',o);};let added=0;");
  rep("if(t< n-1){ // Preserve all lower classes literally.","if(t< n-2){ // Preserve all lower classes literally.");
  // Replace the special-path head and tail with per-pass hosting.
  rep("put(cls);put(D2F.fr(e,J[n-2],utop));\n if(t===n)put([[e,J[n-1],L[0]],[L[0]],[e,L[0],J[n-1]],[L[0]]]);",
      "const H6=J[n-3],c5=t>=n-1?D2F.fr(e,J[n-2],utop):[];\n"+
      " const passes=t===n-2?[{cls,pre:D2F.fr(e,H6,utop),post:[],sub:-1}]:t===n-1?[{cls,pre:[...c5,[e,H6,L[1]],[e,L[1],H6],[e,H6]],post:[],sub:-1}]:\n"+
      "  [{cls:[[v[n-1],v[0],e]],pre:[...c5,...D2F.fr(e,H6,641)],post:[],sub:-1},{cls:[[v[0]],[v[n-1],v[0],e],[v[0]]],pre:[...c5,...D2F.fr(e,H6,v[0])],post:[[e,v[0],L[n+1]],[e,L[n+1],v[0]],[e,v[0]]],sub:v[0]}];\n"+
      " for(const P of passes){put(P.cls);put(P.pre);SUB=P.sub;\n"+
      " if(t===n)put([[e,J[n-1],L[0]],[L[0]],[e,L[0],J[n-1]],[L[0]]]);");
  rep("put(D2F.plus(m,a,null,gap));};const cond=()=>put([[sign],[e,sign,gap],[sign]]);neg();cond();neg();cond();put([...cls].reverse());",
      "put(D2F.plus(m,a,null,gap));};const cond=()=>put([[sign],[e,sign,gap],[sign]]);neg();cond();neg();cond();SUB=-1;put(P.post);put([...P.cls].reverse());}");
  // F (field product) used logical 640 as its carry w0. During F, M is the original input and S its count
  // (preF rotates M back), so c0 = parity(128-height(M)) is a function of M: uncompute c0 into nothing,
  // run F with w0 on S[0], recompute c0. M and S are unchanged by F.
  rep("const ff=fieldprod(2*n,n,K),perm=w=>w===base+1?L[n]:w===base+2?e:w;put(rev(ff.g.map(a=>a.map(perm))));",
      "const ff=fieldprod(2*n,n,K),perm=w=>w===base?S[0]:w===base+1?L[n]:w===base+2?e:w;{const c0=[];for(let h=1;h<=n;h++)if((n-h)&1){const c=M.slice(h-1);c0.push(...mcN(c,c.map((_,i)=>i===0),S[0],loan));}put(c0);put(rev(ff.g.map(a=>a.map(perm))));put(c0);}");
  if(process.env.Q650_HTOP_STAGE==='full'){
    // inner walk: 3 tags frees 643 (Htop's host there; ledger's ipark ends with Htop on 643, unpark takes it).
    rep("emitWalk(new SectorCanonical(n,4),[...vt,R[1],R[1]]","emitWalk(new SectorCanonical(n,3),[...vt,R[1],R[1]]");
    // winding (TEMPORARY until winding hosts exist): ledger's unpark exit hosts -> 640 at winding entry.
    //   class<=127: Q127 (zero, Q<V) | 128 V odd: 641 | 128 V even: 650 (XOR on U0=1).
    const W="{const V=vt,V127=V[127],V0=V[0],mv=(c,b,a,z,aval)=>{const g=[];if(aval)g.push([a]);g.push(...mcN([...c,a],[...b,true],z,loan),...mcN([...c,z],[...b,true],a,loan));if(aval)g.push([a]);return g;};"+
      "put(mv([V127],[false],Q[n-1],Htop,0));put(mv([V127,V0],[true,true],641,Htop,0));put(mv([V127,V0],[true,false],L[n+1],Htop,1));}";
    rep("tap('unpark');\nD2Winding(n,L,R,Q,loan,sink);tap('winding');parkOuter(n,M,rm,Q,T6.slice(0,-1),p,bits,R[1],loan,sink);",
        "tap('unpark');\n"+(process.env.Q650_WIND_TEMP!=='1'?"":W)+"D2Winding(n,L,R,Q,loan,sink);tap('winding');parkOuter(n,M,rm,Q,T6.slice(0,-1),p,bits,R[1],loan,sink);"+
        (process.env.Q650_WIND_TEMP!=='1'?"":"put([[Htop,644],[644,Htop]]);"));
    // reverse walk: 4 tags (backend D2Reduced(n,-4)) frees 644; Htop rides 644, then 644 -> L[129] (zero after the walk).
    rep("emitWalk(new Reduced(n,4),L,R,{...ws,fire:S[4],tst:L[n+1],aux:-1},loan,true,sink);S[bits-2]=sig;",
        "emitWalk(new Reduced(n,-4),L,R,{...ws,fire:S[4],tst:L[n+1],aux:-1},loan,true,sink);put([[644,L[n+1]],[L[n+1],644]]);S[bits-2]=sig;");
  }
  if(process.env.Q650_HTOP_STAGE==='A'){
    // Temporary: return Htop to logical 640 at alpha exit (group selectors on V's top bits, ancilla R[1]).
    rep("D2Alpha(n,terms,L,R,Q,sig,loan,[rm[1],e,t,L[0]],sink);tap('alpha');",
     "D2Alpha(n,terms,L,R,Q,sig,loan,[rm[1],e,t,L[0]],sink);{const V=vt,E=R[1],grp=(c,b,g)=>{const s=mcN(c,b,E,loan);put(s);put(g);put(rev(s));};"+
     "grp([V[125],V[126],V[127]],[false,false,false],fr(E,Q[n-3],Htop));grp([V[125],V[126],V[127]],[true,false,false],fr(E,L[4],Htop));"+
     "grp([V[126],V[127]],[true,false],[[E,L[1]],...fr(E,L[1],Htop),[E,L[1]]]);grp([V[127],V[0]],[true,true],fr(E,641,Htop));grp([V[127],V[0]],[true,false],[[E,L[n+1]],...fr(E,L[n+1],Htop),[E,L[n+1]]]);}tap('alpha');");
  }
  return d;
};
