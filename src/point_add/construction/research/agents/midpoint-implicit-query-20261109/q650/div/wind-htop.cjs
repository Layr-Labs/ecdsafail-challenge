'use strict';
// From ledger (q650-divx e1d8f0f).
// Winding -> restore Htop routing for classes c<=127 via count / trailing-zero slack (ledger).
// Facts: Mn = g*V = M*2^s, so tz(g)+tz(V) >= s; after the winding body Q = g*Q_old, so tz(Q) >= tz(g).
// K = c5|c6 (s>=32). Code slots for (c5,c6), chosen by Pg = [g0..g6 all zero] (g = L[0..128-c], unwritten here):
//   Pg (tz(g)>=7): Q5,Q6, zero because tz(gQ)>=7 (parkOuter folds only Q0..Q4).
//   !Pg (tz(g)<=6): V0,V1, zero whenever K because tz(V)>=32-6.   Classes c>=122 (g shorter than 8 bits): always V0,V1.
// Winding own iteration (under sel): Htop Q127 -> V127 after cls (V127=0, unread by park/rot/body). After park^-1:
//   slot5^=c5, slot6^=c6; utop^=gap&!slot6 (utop=K); gap^=slot5&utop (gap=0); V127 -> gap.
// Restore loop1 own iteration (after hmr, 644 clean): gap -> 644, then the exact inverse; the original c5 move follows.
function one(d,a,b){if(d.split(a).length!==2)throw Error('wind anchor '+a.slice(0,70));return d.replace(a,()=>b);}
// Gate builder shared by both sites: returns nct gates. lit = [wire, positive?]. Dirty-ladder MCX on loan wires.
const LIB=`const WH=(()=>{
 const mc=(lits,t,loan)=>{const g=[],neg=lits.filter(([,p])=>!p).map(([w])=>w),c=lits.map(([w])=>w);for(const w of neg)g.push([w]);
  if(c.length<=2)g.push([...c,t]);else{const k=c.length,b=loan.filter(w=>w!==t&&!c.includes(w)).slice(0,k-2);
   for(let s=0;s<2;s++){if(s===0)g.push([c[0],c[1],b[0]]);for(let i=1;i<k-2;i++)g.push([c[i+1],b[i-1],b[i]]);g.push([c[k-1],b[k-3],t]);for(let i=k-3;i>=1;i--)g.push([c[i+1],b[i-1],b[i]]);if(s===0)g.push([c[0],c[1],b[0]]);}}
  for(const w of neg)g.push([w]);return g;};
 // encode for class c with selector wire sel: (Q,L,V arrays of this scope)
 const enc=(c,n,sel,Q,L,V,loan)=>{const size=n+1-c,gap=L[size],utop=L[size+1],V127=V[n-1],g=[];
  const usePg=c<=121,Pg=usePg?L.slice(0,7).map(w=>[w,false]):null,S=[sel,true];
  const slotMove=(src,qs,vs)=>{ // slot ^= src for the case-selected slot
   if(!usePg){g.push(...mc([S,[src,true]],vs,loan));return;}
   g.push(...mc([S,[src,true],...Pg],qs,loan));g.push(...mc([S,[src,true]],vs,loan));g.push(...mc([S,[src,true],...Pg],vs,loan));};
  slotMove(gap,Q[5],V[0]);slotMove(utop,Q[6],V[1]);
  // utop ^= sel & gap & !slot6
  if(!usePg)g.push(...mc([S,[gap,true],[V[1],false]],utop,loan));
  else{g.push(...mc([S,[gap,true],[Q[6],false],...Pg],utop,loan));g.push(...mc([S,[gap,true],[V[1],false]],utop,loan));g.push(...mc([S,[gap,true],[V[1],false],...Pg],utop,loan));}
  // gap ^= sel & slot5 & utop
  if(!usePg)g.push(...mc([S,[V[0],true],[utop,true]],gap,loan));
  else{g.push(...mc([S,[Q[5],true],[utop,true],...Pg],gap,loan));g.push(...mc([S,[V[0],true],[utop,true]],gap,loan));g.push(...mc([S,[V[0],true],[utop,true],...Pg],gap,loan));}
  g.push([sel,V127,gap],[sel,gap,V127]);return g;};
 return {mc,enc};})();`;
const CMIN=+(process.env.WCMIN||1);
function windHtop(d){
 d=one(d,"function D2Winding(n,L,R,Q,loan,sink){",LIB+"function D2Winding(n,L,R,Q,loan,sink){");
 d=one(d," const sel=R[1],V=Array.from({length:n},(_,i)=>R[n+1-i]);\n for(let c=1;c<n;c++){"," const sel=R[1],V=Array.from({length:n},(_,i)=>R[n+1-i]);\n if(process.env.W128!=='0')sink('nct',[...WH.mc([[V[n-1],true],[V[0],true],[641,true]],L[1],loan),...WH.mc([[V[n-1],true],[V[0],true],[L[1],true]],641,loan)]);\n for(let c=1;c<n;c++){");
 d=one(d,"  sink('nct',cls);sink('nct',park);sink('nct',rot);",
  "  const on=c>="+CMIN+";sink('nct',cls);if(on)sink('nct',[[sel,Q[n-1],V[n-1]],[sel,V[n-1],Q[n-1]]]);sink('nct',park);sink('nct',rot);");
 d=one(d,"  sink('nct',[...park].reverse());sink('nct',[...cls].reverse());",
  "  sink('nct',[...park].reverse());if(on)sink('nct',WH.enc(c,n,sel,Q,L,V,loan));sink('nct',[...cls].reverse());");
 d=one(d,"host=c<n?L[n+1-c]:L[2];put(sel);put(fr(R[1],T6[0],host));put(rev(sel));}put([[T6[0],Q[bits-2]]]);",
  "host=c<n?L[n+1-c]:L[2];put(sel);if(c>="+CMIN+"&&c<n){const gp=L[n+1-c];put([[R[1],gp,644],[R[1],644,gp]]);put([...WH.enc(c,n,R[1],Q,L,vt,loan)].reverse().filter((x,i)=>i>=2));}if(c===n&&process.env.W128!=='0'){put([...WH.mc([[R[1],true],[vt[0],true],[L[1],true]],644,loan),...WH.mc([[R[1],true],[vt[0],true],[644,true]],L[1],loan)]);put([...WH.mc([[R[1],true],[vt[0],false],[650,false]],644,loan),...WH.mc([[R[1],true],[vt[0],false],[644,true]],650,loan)]);}put(fr(R[1],T6[0],host));put(rev(sel));}"+(process.env.TAPW?"sink('tap','loop1');":"")+"put([[T6[0],Q[bits-2]]]);");
 return d;}
module.exports={windHtop};
