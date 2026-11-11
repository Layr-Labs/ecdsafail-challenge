'use strict';
// Q648_DIV part 'c2w' (ledger): count bit c2 (logical 643 = S[2]) evicted from wind.before through po.hmr.
// Entry contract: c2 on 643 at the start of D14BeforeWinding (or, with evict's part c2u2, already in the entry hosts Q127/U2). Exit: the po.hmr fold (Q2 ^= c2, hmr record bits+2 = 9)
// done from 641 (zero after hmr(T6[0], bits+4)); 643 untouched in between.
// Fact (evict, measured): c2 = 1 => tz(g) + tz(V) >= 4, where g = L[0..size-1] (size = n+1-height), V = R reversed.
// Hosts per class (k = tz(g)):
//   k >= 2 (L0 = L1 = 0): wind.before: c2 -> Q127 (Q[n-1] is zero for every height <= 127; height 128 has g = 1).
//       Inside winding iteration c (sel = [height == c]): Q127 -> V[h], h = min(c+2, n-1) (V[c..] = 0 at height c; D5Relay
//       uses V[c], D14Relay V[c+1], park V[c-1]), before park/rot; after the body (Q = g*J): k >= 3 -> Q2 (Q0..Q2 = 0), which
//       is already the fold state Q2_po ^ c2 with Q2_po = 0; k = 2 -> Q1 (Q0 = Q1 = 0; Q2_po = 1).
//       po.hmr: k >= 3: 641 ^= Q2 (copy; Q2 keeps Q2_po ^ c2). k = 2: Q2 ^= Q1, then Q1 -> 641.
//   k <= 1: c2 = 1 => 8 | V. wind.before: U2 ^= Q2 ^ Q1 ^ U1 (= 0 by U2 = J2 ^ J1 ^ U1 on 8|V lanes, J = Q before winding),
//       then c2 -> U2 (U2 = L[n-1] is untouched by winding for heights >= 3; 8|V forces height >= 4).
//       po.hmr: U2 -> 641, U2 ^= U1 ^ J2 ^ J1 with J = (Q >> k) * (g >> k)^-1 mod 8 (enumerated), then Q2 ^= 641.
//   Between winding and po.hmr nothing reads these hosts on these classes: parkOuter fwd writes Q0 only, D14ParkCount uses
//   Q[k+1..k+3] for k = tz(g) <= 3 with 16|V guards (k >= 2 there for Q1/Q2 hosts) and U1/U3, the sign lease uses
//   Q[k+qb], U[qb] (U2 only when k = 2, whose c2 is on Q1) and L[k+qb].
// Then hmr(641, bits+2). The original j = 2 fold is removed; j = 1 runs after it (Q1 is back to Q1_po on k = 2 lanes).
const {parts}=require('./d648-walks.cjs');
const HELP=`
function D648C2Mc(cs,ps,z,loan){const m=new Map();for(let i=0;i<cs.length;i++){if(m.has(cs[i])&&m.get(cs[i])!==ps[i])return [];m.set(cs[i],ps[i]);}
 if(m.has(z))throw Error('c2w alias '+z);const k=[...m.keys()];return mcN(k,k.map(w=>m.get(w)),z,loan.filter(w=>w!==z&&!m.has(w)));}
// C cubes (8|V, tz(g) <= 1): k = 0, k = 1 for heights <= 127 (height 128 excluded by ~V[n-1]: its g = 1 is implicit and L0 is
// data there), and height 128 itself (k = 0, g = 1).
function D648C2Cubes(V,L){const n=V.length,v8=[V[0],V[1],V[2]],f=[false,false,false];return [[[...v8,V[n-1],L[0]],[...f,false,true],0],[[...v8,V[n-1],L[0],L[1]],[...f,false,false,true],1],[[...v8,V[n-1]],[...f,true],-1]];}
function D648C2In(n,L,R,Q,loan,sink,c2){
 if(c2!==643)throw Error('c2w port '+c2);if(globalThis.__c2dbg)globalThis.__c2dbg('in0',{L,R,Q});
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink('nct',g),mc=D648C2Mc;
 for(const [cs,ps] of D648C2Cubes(V,L)){
  for(const w of [Q[2],Q[1],U[1]])put(mc([...cs,w],[...ps,true],U[2],loan));
  put(mc([...cs,c2],[...ps,true],U[2],loan));put(mc([...cs,U[2]],[...ps,true],c2,loan));
 }
 const t=[V[n-1],L[0],L[1]],tp=[false,false,false];
 put(mc([...t,c2],[...tp,true],Q[n-1],loan));put(mc([...t,Q[n-1]],[...tp,true],c2,loan));
 if(globalThis.__c2dbg)globalThis.__c2dbg('in1',{L,R,Q});
}
function D648C2WindIn(n,L,V,Q,sel,loan,c){
 if(c>n-2)return [];const h=V[Math.min(c+2,n-1)],cs=[sel,L[0],L[1]],ps=[true,false,false];
 return [...D648C2Mc([...cs,Q[n-1]],[...ps,true],h,loan),...D648C2Mc([...cs,h],[...ps,true],Q[n-1],loan)];
}
function D648C2J12(n,L,Q,k,size,cs,ps,dst,loan){ // dst ^= J1^J2 (J odd, J = (Q>>k)/(g>>k) mod 8; g bits >= size are 0)
 const rows=[],inv8=x=>{for(let y=1;y<8;y+=2)if((x*y)%8===1)return y;throw Error('inv8');};
 const gb=[1,2].filter(i=>k+i<size).map(i=>L[k+i]),qb=[Q[k+1],Q[k+2]];
 for(let gp=0;gp<(1<<gb.length);gp++){const gi=inv8(1|(gp<<1));
  for(let q=1;q<8;q+=2){const j=(q*gi)%8;if(!(((j>>1)^(j>>2))&1))continue;
   rows.push(...D648C2Mc([...cs,...gb,...qb],[...ps,...gb.map((_,i)=>!!((gp>>i)&1)),!!(q&2),!!(q&4)],dst,loan));}}
 return rows;
}
function D648C2WindOut(n,L,V,Q,sel,loan,c){
 const U2=L[n-1],U1=L[n],size=n+1-c,rows=[];
 // C, k = 1 (8|V, g = 2*odd): after the body Q1 = 1 (J odd); host c2 there as Q1 = 1^c2, restore U2 while Q is clean.
 if(c>=4&&c<=n-1){const cs=[sel,V[0],V[1],V[2],L[0],L[1]],ps=[true,false,false,false,false,true];
  rows.push(...D648C2Mc([...cs,U2],[...ps,true],Q[1],loan),...D648C2Mc([...cs,Q[1]],[...ps,false],U2,loan),
   ...D648C2Mc([...cs,U1],[...ps,true],U2,loan),...D648C2J12(n,L,Q,1,size,cs,ps,U2,loan));}
 if(c>n-2)return rows;const h=V[Math.min(c+2,n-1)];
 for(const [l2,dst] of [[false,Q[2]],[true,Q[1]]]){const cs=[sel,L[0],L[1],L[2]],ps=[true,false,false,l2];
  rows.push(...D648C2Mc([...cs,h],[...ps,true],dst,loan),...D648C2Mc([...cs,dst],[...ps,true],h,loan));}
 return rows;
}
function D648C2Out(n,L,R,Q,loan,sink,port){
 const V=Array.from({length:n},(_,j)=>R[n+1-j]),U=Array.from({length:n},(_,j)=>L[n+1-j]),put=g=>sink('nct',g),mc=D648C2Mc;
 if(globalThis.__c2dbg)globalThis.__c2dbg('out0',{L,R,Q});
 const inv8=x=>{for(let y=1;y<8;y+=2)if((x*y)%8===1)return y;throw Error('inv8');};
 // class groups: heights <= n-3 (all g bits present), n-2, n-1, n (size 3, 2, 1: missing g bits are zero)
 const groups=[[[V[n-3],V[n-2],V[n-1]],[false,false,false],99]];
 for(const c of [n-2,n-1,n]){const hc=V.slice(c-1);groups.push([hc,hc.map((_,i)=>i===0),n+1-c]);}
 const cubes=D648C2Cubes(V,L);
 for(const [cs0,ps0,kk] of [cubes[0],cubes[2]]){const grp=kk<0?[[[],[],1]]:groups;
  put(mc([...cs0,U[2]],[...ps0,true],port,loan));put(mc([...cs0,port],[...ps0,true],U[2],loan));
  put(mc([...cs0,U[1]],[...ps0,true],U[2],loan));
  for(const [hc,hp,size] of grp)put(D648C2J12(n,L,Q,0,size,[...cs0,...hc],[...ps0,...hp],U[2],loan));
 }
 {const [cs1,ps1]=cubes[1];put(mc([...cs1,Q[1]],[...ps1,true],port,loan));put(mc(cs1,ps1,port,loan));put(mc([...cs1,port],[...ps1,true],Q[1],loan));}
 put([[port,Q[2]]]);
 const A=[V[n-1],L[0],L[1],L[2]];put(mc([...A,Q[2]],[false,false,false,false,true],port,loan));
 const B=[V[n-1],L[0],L[1],L[2]],bp=[false,false,false,true];
 put(mc([...B,Q[1]],[...bp,true],Q[2],loan));put(mc([...B,Q[1]],[...bp,true],port,loan));put(mc([...B,port],[...bp,true],Q[1],loan));
 if(globalThis.__c2dbg)globalThis.__c2dbg('out1',{L,R,Q});
}
`;
module.exports=function(s){
 const on=parts();if(!on('c2w'))return s;
 const one=(a,b)=>{const k=s.split(a).length-1;if(k!==1)throw Error('c2w anchor x'+k+': '+a.slice(0,70));s=s.replace(a,()=>b);};
 one("D14BeforeWinding(n,L,R,Q,loan,sink);D2Winding(n,L,R,Q,loan,sink);tap('winding');",
     (on('c2u2')?'':'D648C2In(n,L,R,Q,loan,sink,S[2]);')+"D14BeforeWinding(n,L,R,Q,loan,sink);D2Winding(n,L,R,Q,loan,sink);tap('winding');");
 one("sink('nct',cls);sink('nct',D14Relay(n,L,V,Q,sel,loan,c,false));",
     "sink('nct',cls);sink('nct',D648C2WindIn(n,L,V,Q,sel,loan,c));sink('nct',D14Relay(n,L,V,Q,sel,loan,c,false));");
 one("sink('nct',D14Relay(n,L,V,Q,sel,loan,c,true));sink('nct',[...park].reverse());",
     "sink('nct',D14Relay(n,L,V,Q,sel,loan,c,true));sink('nct',D648C2WindOut(n,L,V,Q,sel,loan,c));sink('nct',[...park].reverse());");
 one("for(let j=1;j<3;j++){put([[T6[j],Q[j]]]);sink('hmr',[T6[j],bits+j]);}",
     "D648C2Out(n,L,R,Q,loan,sink,T6[0]);sink('hmr',[T6[0],bits+2]);put([[T6[1],Q[1]]]);sink('hmr',[T6[1],bits+1]);");
 s+=HELP;return s;
};
