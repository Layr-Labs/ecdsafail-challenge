 'use strict';
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D26 outer virtual anchor '+a);s=s.replace(a,()=>b);};
 one("D25WindConnect(n,L,R,Q,loan,base+1,sink);tap('d25.winding.connected');", "D25WindConnect(n,L,R,Q,loan,R[1],sink);T6[0]=R[1];tap('d25.winding.connected');");
 one("const D26count1Host=T6[0];put([[T6[1],D26count1Host],[D26count1Host,T6[1]]]);T6[0]=T6[1];tap('d26.outer.port642');", "tap('d26.outer.port129');");
 one("put([[D26count1Host,Q[1]]]);sink('hmr',[D26count1Host,bits+1]);", "put([[T6[1],Q[1]]]);sink('hmr',[T6[1],bits+1]);");
 let a=s.indexOf('function D14ParkCount('),b=s.indexOf('function D17Raw(',a),f=s.slice(a,b);
 const old="const pred=D14Raw(cs,ps,e,loan);put(pred);put(fr(e,Q[3],port));put([...pred].reverse());";
 if(f.split(old).length!==2)throw Error('D26 outer count3 predicate');
 f=f.replace(old,`for(const r of fr(1022,Q[3],port)){const controls=r.slice(0,-1);if(controls.includes(1022)){const rest=controls.filter(q=>q!==1022);put(D14Raw([...cs,...rest],[...ps,...rest.map(()=>true)],r.at(-1),loan));}else put([r]);}`);
 s=s.slice(0,a)+f+s.slice(b);
 a=s.indexOf('for(let c=1;c<=n;c++){',s.indexOf('parkOuter(n,M,rm,Q,T6.slice(0,1)'));
 b=s.indexOf("put([[T6[0],Q[4]]]);sink('hmr',[T6[0],bits+4]);",a);f=s.slice(a,b);
 const begin='const sel=flagHeight(vt,c,R[1],loan);put(sel);';if(f.split(begin).length!==2)throw Error('D26 count4 start');
 f=f.replace(begin,`const hc=vt.slice(c-1),hp=hc.map((_,j)=>j===0);const put=g=>{const rows=[];for(const r of g){if(r.at(-1)===1022)throw Error('D26 selector targeted');const cs=r.slice(0,-1);if(cs.includes(1022)){const rest=cs.filter(q=>q!==1022);rows.push(...D17Raw([...hc,...rest],[...hp,...rest.map(()=>true)],r.at(-1),loan));}else rows.push(r);}sink('nct',rows);};`);
 if(f.split('put(rev(sel));').length!==2)throw Error('D26 count4 end');f=f.replace('put(rev(sel));','').replaceAll('R[1]','1022');
 s=s.slice(0,a)+f+s.slice(b);return s;
};
