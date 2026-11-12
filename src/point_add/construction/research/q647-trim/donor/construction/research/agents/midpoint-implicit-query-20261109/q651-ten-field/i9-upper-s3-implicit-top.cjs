'use strict';
// The high divisor bit is 1 at both boundaries. Carry updates into that
// otherwise missing physical bit are accumulated on u, preserving its unknown
// original value. The two high target CNOTs are involutions: their dirty
// offsets cancel on opposite sides of the low-ripple descent.
function implicitTopDigit(tape,z,v,controls,back){
    if(z.length!==v.length+1||controls.length!==1)throw Error('implicit digit shape');
    const width=v.length,k=width-1,e=controls[0],h=z[width],top=z[k];
    if(!k){
        if(back){tape.out(e,h,top);tape.out(e,top,h);}
        else{tape.out(e,top,h);tape.out(e,h,top);}return;
    }
    const A=v.slice(0,k),B=z.slice(0,k),[u,d]=tape.loan([...z,...v,e],2);
    const ops=[],x=q=>ops.push([1023,1023,q]),cx=(a,b)=>ops.push([1023,a,b]),cc=(a,b,t)=>ops.push([a,b,t]);
    const conditional=(other,t)=>{cc(e,u,d);cc(d,other,t);cc(e,u,d);cc(d,other,t);};
    conditional(top,h);
    for(const q of B)x(q);
    for(let i=1;i<k;i++)cx(A[i],B[i]);
    x(u);if(k>=2)cx(A[k-1],u);
    for(let i=k-2;i>=1;i--)cx(A[i],A[i+1]);
    for(let i=0;i<k-1;i++)cc(B[i],A[i],A[i+1]);
    cc(B[k-1],A[k-1],u);
    // Apply both high CNOTs with the encoded predicate e*u and restore d.
    cc(d,top,h);cc(e,u,d);cc(d,top,h);cc(d,h,top);cc(e,u,d);cc(d,h,top);
    cc(B[k-1],A[k-1],u);
    for(let i=0;i<k;i++){cc(d,A[i],B[i]);if(i+1<k)cx(d,B[i]);}
    cc(e,h,d);cc(d,A[k-1],B[k-1]);
    for(let i=k-2;i>=0;i--){cc(B[i],A[i],A[i+1]);cc(d,A[i],B[i]);}
    cc(e,h,d);
    for(let i=0;i+1<k;i++)cx(d,B[i]);
    for(let i=1;i<k-1;i++)cx(A[i],A[i+1]);
    if(k>=2)cx(A[k-1],u);x(u);
    conditional(h,top);
    for(let i=1;i<k;i++)cx(A[i],B[i]);
    for(const q of B)x(q);
    if(back)ops.reverse();for(const gate of ops)tape.out(...gate);
}
function patchImplicit(source){
    const anchor='    digitTopOne(tape,z,v,controls,back){';
    if(source.split(anchor).length!==2)throw Error('implicit entry anchor');
    return source.replace('class Tape {',()=>implicitTopDigit.toString()+'\nclass Tape {')
        .replace(anchor,()=>anchor+'\n        if(v.length>=8){implicitTopDigit(tape,z,v,controls,back);return;}');
}
module.exports={implicitTopDigit,patchImplicit};
