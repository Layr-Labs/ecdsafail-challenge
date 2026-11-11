 'use strict';
// D24 source layer. count6's redundant copy can be measured immediately after mask.
// Q126 then becomes the parking port; count0 host remains caller-parameterized.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D26 anchor '+a);s=s.replace(a,()=>b);};
 one('const c4=S[4],lowHost=Q[n-4];','const count0Host=S[0];const c4=S[4],lowHost=Q[n-4];');
 one('delta();bias(false);mark();mask();swap02();mask0Carrier();',
     "delta();bias(false);mark();mask();sink('hmr',[S[6],off+6]);put([[S[0],S[6]],[S[6],S[0]]]);S[0]=S[6];swap02();mask0Carrier();");
 one("for(let j=1;j<bits;j++)if(j!==2&&j!==3&&j!==4)sink('hmr',[S[j],off+j]);",
     "for(let j=1;j<bits;j++)if(j!==2&&j!==3&&j!==4&&j!==6)sink('hmr',[S[j],off+j]);");
 one('else{routeZeros(n,L,R,e,loan,put,true,null,c=>p3(c).reverse());extractBit(4,S[0]);',
     'else{routeZeros(n,L,R,e,loan,put,true,null,c=>p3(c).reverse());S[0]=S[6];extractBit(4,S[0]);');
 one("for(let j=5;j<bits;j++){extractBit(j,S[j]);sink('phase',[S[j],off+j]);}",
     "for(let j=5;j<bits;j++)if(j!==6){extractBit(j,S[j]);sink('phase',[S[j],off+j]);}");
 one('gather0(true);mask0Carrier();swap02();\n mask();mark();bias(true);delta();',
     "gather0(true);mask0Carrier();swap02();put([[S[0],count0Host],[count0Host,S[0]]]);S[0]=count0Host;extractBit(6,S[6]);sink('phase',[S[6],off+6]);\n mask();mark();bias(true);delta();");
 one('if(bit!==2||!rev)return raw(cs,ps,z);', 'if((bit!==2&&bit!==6)||!rev)return raw(cs,ps,z);');
 return s;
};
