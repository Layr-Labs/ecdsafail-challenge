'use strict';
const {replace}=require('./base.cjs');
function thinDivide(d) {
    const helpers=`
function terminalSign(n,L,R,wire,loan,put,swap) {
    const v=Array.from({length:n},(_,j)=>R[n+1-j]);
    for(let t=1;t<=n;t++){
        const place=L[n+2-t],test=v.slice(t-1),pol=test.map((_,j)=>j===0);
        if(swap)put([[place,wire]]);
        put(mcN(test.concat(swap?wire:place),pol.concat(true),swap?place:wire,loan));
        if(swap)put([[place,wire]]);
    }
}
`;
    d=replace(d,'function outerloadJ(n,terms',helpers+'\nfunction outerloadJ(n,terms');
    d=replace(d,'const e=ws[0],v=Array.from({length:n},(_,j)=>R[n+1-j]),u=',
        'const v=Array.from({length:n},(_,j)=>R[n+1-j]),u=');
    d=replace(d,'if(lo===undefined)continue;',
        'if(lo===undefined)continue;const e=t===n?L[0]:J[n-1];');
    d=replace(d,'put(cls);put(park);if(t===2)',
        'if(t===n){const top=J[n-1],vhi=v[n-1];put([[L[0],top],[top,L[0]],[L[0],top],[vhi,L[0]],[L[0],top]]);}else put(cls);put(park);if(t===2)');
    d=replace(d,'put(park.slice().reverse());put([...cls].reverse());',
        'put(park.slice().reverse());if(t===n){const top=J[n-1],vhi=v[n-1];put([[vhi],[top,L[0]],[vhi,L[0],top],[top,L[0]],[vhi]]);}else put([...cls].reverse());');

    d=replace(d,'ws={sign:sig,tag:S,fire:S[5]','ws={sign:S[4],tag:S,fire:S[5]');
    d=d.replaceAll('new Reduced(n)','new Reduced(n,5)');
    d=replace(d,'L,R,ws,loan,false,sink);put(rev(ss));tap(\'outer\');outerloadJ(n,terms,L,R,Q,sig,loan,[rm[1],e,t,L[0]],sink);tap(\'alpha\');',
        'L,R,ws,loan,false,sink);put(fr(null,S[4],R[1]).map(g=>g.filter(x=>x!==null)));put(rev(ss));tap(\'outer\');outerloadJ(n,terms,L,R,Q,R[1],loan,[rm[1],e,t,L[0]],sink);terminalSign(n,L,R,R[1],loan,put,true);tap(\'alpha\');');
    // An unconditional swap exchanges the clean sign target with the returned sign.
    d=replace(d,'put(fr(null,S[4],R[1]).map(g=>g.filter(x=>x!==null)));',
        'put([[S[4],R[1]],[R[1],S[4]],[S[4],R[1]]]);');
    d=replace(d,'new SectorCanonical(n,5)','new SectorCanonical(n,4)');
    d=replace(d,"sink('hmr',[S[j],off+j]);routeZeros(n,L,R,e,loan,put);",
        "sink('hmr',[S[j],off+j]);terminalSign(n,L,R,S[3],loan,put,true);routeZeros(n,L,R,e,loan,put);");
    d=replace(d,'routeZeros(n,L,R,e,loan,put,true);move();extract();',
        'routeZeros(n,L,R,e,loan,put,true);terminalSign(n,L,R,S[3],loan,put,true);move();extract();');
    d=replace(d,'bits,R[1],loan,sink);emitWalk(new Reduced(n,5),',
        'bits,R[1],loan,sink);terminalSign(n,L,R,S[4],loan,put,true);emitWalk(new Reduced(n,5),');

    const start=d.indexOf('function extract(){'),end=d.indexOf('\n',start);
    let extract=d.slice(start,end);
    const old=extract.indexOf('for(let raw=1;raw<m;raw+=2)'),last=extract.lastIndexOf('put([...a].reverse());}}');
    if(old<0||last<=old)throw Error('Changed inner tag extraction');
    const extra=`
        put([...a].reverse());}
        const scratch=Q[n-2];
        function contribution(difference){
            for(let j=0;j<bits;j++){
                const cs=[D,...V.slice(0,j+1)],mark=mcN(cs,cs.map(()=>false),e,loan);
                put(mark);const m=1<<(j+1);
                for(let raw=1;raw<m;raw+=2){
                    const sol=shortinv(BigInt(raw),BigInt(m)),v=kp*sol,high=1n<<BigInt(j);
                    const yes=((v%BigInt(m))&high)!==0n,no=((((-v)%BigInt(m)+BigInt(m))%BigInt(m))&high)!==0n;
                    if(difference?yes!==no:no){
                        const ctl=difference?[e,scratch]:[e];
                        put(mcN(ctl.concat(Q.slice(0,j+1)),ctl.map(()=>true).concat(eq_bits(Q,raw).slice(0,j+1)),S[j],loan));
                    }
                }
                put(mark.slice().reverse());
            }
        }
        contribution(false);contribution(true);terminalSign(n,L,R,scratch,loan,put,false);
        contribution(true);terminalSign(n,L,R,scratch,loan,put,false);
    }`;
    extract=extract.slice(0,old)+extra;
    return d.slice(0,start)+extract+d.slice(end);
}
module.exports={thinDivide};
