'use strict';
// ledger (q648): U15 deep quotient TRIAL / WITNESS (rows 0..63) without logical 647 (f2 = rank bit 6).
// UEXTRA overlay for ringhole's h649 harness, after p648-affine.cjs and p648-trial96.cjs.
//
// Code. On taken lanes with rank >= 64 ("P lanes") the bit f is stored in the normalized numerator's known zeros:
//   copies c = n[P..P+2] := b3..b5, b3..b5 := 111, marker n[M] := 1, f := 0.
// Zero facts (deep rows, unbiased shift s = rank): n[0..s-1] = 0 after normalization. P lanes: n[0..63] = 0. Lanes with
// b3..b5 = 111 and f = 0: s >= 56, n[0..55] = 0, so the marker reads 0 there and P = take & b3 & b4 & b5 & n[M] exactly.
// More generally lanes with v = (b3..b5) >= 4 have s >= 32 > M, so n[M] = 0 on every non-P lane with v >= 4.
//   encode(F):  c ^= b [take,F]; b ^= c [take,F]; b ^= 111 [take,F]; n[M] ^= 1 [take,F]; F ^= take&b3&b4&b5&n[M].
// The bands see the 6-bit tag (rank.slice(0,6)): [b3..b5 == 0] == [rank < 8] on every lane; the low bits are unchanged;
// oddQuotient's onesBlock(2^j,[tag[j]]) value use is repaired on P lanes (+8(c+1) steps, positive controls).
// Bias (rank+1, the bands' convention) acts on the CODE (biasE, take-gated; ring: untaken lanes' rank is unread):
//   low3 += 1; on low==0 (carry) with b=111: P lanes c += 1, former rank-63 lanes become P (mk := 1, c = 0); then P lanes
//   park at 110 and b3..b5 += 1 on carry lanes (P back to 111, natural v<=6 to v+1). See biasOps.
// f hosts outside the code (measured free on taken lanes, stress 832, rows 0..63, every step of the window):
//   quotient pre-band : f on q0 (645) through norm, then encode.                    [no hook]
//   witness  post-band: f on f1 (644) through norm, then encode.                    [no hook; witness runs BACK]
//   quotient post-band: code survives biasE^-1, lease^-1, j0^-1 (re-stash inside j0), decode into qtop (646) before j1^-1.
//   witness  pre-band : code survives biasE^-1, u11 rest^-1 (re-stash), j1^-1 (re-stash), decode into qtop before j2^-1.
// Re-stash: a rotation by d controlled on x moves the code up by d on x lanes; inside the same normalization step (x still
// known) it is moved back: n[i] ^= n[i+d], n[i+d] ^= n[i] for the copies [take,x,b3,b4,b5,n[M+d]], then the marker
// [take,x,b3,b4,b5]. Non-P lanes with b3..b5 = 111 have zeros there, so the moves are identities.
// Result: logical 647 is never touched by rows 0..63's trial or witness.
const LO=+(process.env.T648_LO||0),HI=+(process.env.T648_HI||63),F2=647,P=+(process.env.T648_P||8),M=+(process.env.T648_M||11);
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('t648 anchor '+a.slice(0,70));s=s.replace(a,()=>b);};
 one("    trial(tape,witness,back){\n\n      if(this.k<=95&&!witness&&!this.u8Entered){",
 String.raw`    t648(tape,rank,nn,P,M,witness,work){
      if(this.k<${LO}||this.k>${HI})return null;
      if(rank.length!==7||rank[6]!==${F2})throw Error('t648 rank '+this.k+' '+JSON.stringify(rank));
      const take=this.take,l=rank.slice(0,3),b=rank.slice(3,6),c=nn.slice(P,P+3),mk=nn[M],X=q=>tape.out(NONE,NONE,q);
      const q0=this.q.at(-2),qt=this.qtop,f1=this.dv[0];
      if(q0!==645||qt!==646||f1!==644)throw Error('t648 hosts '+this.k+' '+[q0,qt,f1]);
      const cfg=witness?{pre:{F:qt,J:1},post:{F:f1,J:null}}:{pre:{F:q0,J:null},post:{F:qt,J:0}};
      for(const q of [...c,mk,nn[M+1],nn[M+2],nn[P-1]])if(!(q>=0)||rank.includes(q)||q===take)throw Error('t648 ports '+this.k);
      const run=(ops,rv)=>stepList(ops,rv,fn=>fn());
      const encOps=F=>{const o=[];
        for(let i=0;i<3;i++)o.push(()=>this.toggle(tape,[take,F,b[i]],[],c[i]));
        for(let i=0;i<3;i++)o.push(()=>this.toggle(tape,[take,F,c[i]],[],b[i]));
        for(let i=0;i<3;i++)o.push(()=>this.toggle(tape,[take,F],[],b[i]));
        o.push(()=>this.toggle(tape,[take,F],[],mk));
        o.push(()=>this.toggle(tape,[take,...b,mk],[],F));return o;};
      // copies (marker at M+d still in place as the P witness), then the marker itself.
      const restash=(d,x)=>{const o=[];
        for(let i=0;i<3;i++){const lo=nn[P+i],hi=nn[P+i+d],cs=[take,x,...b,nn[M+d]];
          o.push(()=>{if(nn[M+d]===lo||nn[M+d]===hi)throw Error('t648 restash overlap');this.toggle(tape,[...cs,hi],[],lo);},()=>this.toggle(tape,[...cs,lo],[],hi));}
        const cm=[take,x,...b];o.push(()=>this.toggle(tape,[...cm,nn[M+d]],[],mk),()=>this.toggle(tape,[...cm,mk],[],nn[M+d]));
        return o;};
      // biasE: rank+1 on the code. lz = low bits 000 after the low increment (the carry). On lz lanes with b=111: P lanes
      // (mk=1) c += 1; former rank-63 lanes (mk=0, c=000) get mk := 1 (now P with c=0; c=000 is the discriminator, P lanes
      // have c >= 1 after their increment). Then P lanes park b at 110 ([lz,b4,b5,mk]: natural v=6 lanes have mk=0) and one
      // 3-bit increment on lz lanes moves P lanes back to 111 and every natural v<=6 to v+1.
      const biasOps=[
        rr=>this.inc(tape,l,[take],rr),
        rr=>{l.forEach(X);this.inc(tape,c,[take,...l,...b,mk],rr);l.forEach(X);},
        ()=>{l.forEach(X);this.toggle(tape,[take,...l,...b],[...c],mk);l.forEach(X);},
        ()=>{l.forEach(X);this.toggle(tape,[take,...l,b[1],b[2],mk],[],b[0]);l.forEach(X);},
        rr=>{l.forEach(X);this.inc(tape,b,[take,...l],rr);l.forEach(X);}];
      const biasE=rv=>stepList(biasOps,rv,fn=>fn(rv));
      const side=({F,J})=>{const S=Object.create(work);S.tag=rank.slice();S.tag[6]=F;
        if(J!==null)S.__hk=(tp,phase,j,t,rr)=>{
          if(phase==='pre'&&j===J)run(encOps(F),rr);
          else if(phase==='post'&&j<=J)run(restash(1<<j,t),rr);
          else if(phase==='rest')run(restash(1,t),rr);};
        return S;};
      const SP=side(cfg.pre),SQ=side(cfg.post);
      const pre=[rv=>SP.normalize(tape,rv)];if(cfg.pre.J===null)pre.push(rv=>run(encOps(cfg.pre.F),rv));pre.push(rv=>biasE(rv));
      const post=[rv=>biasE(!rv)];if(cfg.post.J===null)post.push(rv=>run(encOps(cfg.post.F),!rv));post.push(rv=>SQ.normalize(tape,!rv));
      const view=o=>{const v=Object.create(o);v.tag=rank.slice(0,6);v.t648=true;
        // oddQuotient applies onesBlock(2^j,[tag[j]]) for 2^j <= B.hi (rank bits as VALUES). On P lanes bits 3..5 give 56
        // steps instead of 64 + 8c: add onesBlock(8,[P]) and onesBlock(8*2^i,[P,c_i]).
        v.oddQuotient=function(tp,B,back){const prev=v.__B648;v.__B648=B;try{return o.oddQuotient.call(this,tp,B,back);}finally{v.__B648=prev;}};
        v.onesBlock=function(tp,R,D,n,extra,ctrl,back){
          const B=v.__B648,fix=B&&B.hi>=64&&n===32&&extra.length===1&&extra[0]===b[2];
          const Pc=[...b,mk],seq=[rr=>o.onesBlock.call(this,tp,R,D,n,extra,ctrl,rr)];
          if(fix){seq.push(rr=>o.onesBlock.call(this,tp,R,D,8,Pc,ctrl,rr));for(let i=0;i<3;i++)seq.push(rr=>o.onesBlock.call(this,tp,R,D,8<<i,[...Pc,c[i]],ctrl,rr));}
          stepList(seq,back,fn=>fn(back));};
        return v;};
      return {pre,post,view};
    }
    trial(tape,witness,back){

      if(this.k<=95&&!witness&&!this.u8Entered){`);
 // The original deep block only (ringhole's p648-trial96 duplicates its text for rows 64..111): first match after its rank line.
 {const key="const rank=H.tag.slice();rank[4]=hi;rank[5]=free;low.tag=rank;work.tag=rank;";if(s.split(key).length!==2)throw Error('t648 deep key');
  const a="        const norm=rv=>work.normalize(tape,rv),bias=rv=>this.inc(tape,rank,[],rv);\n        const steps=[dirs,pack,moved,setOne,choose,norm,bias];\n        for(const band of low.layouts())steps.push(rv=>witness?low.oddWitness(tape,band,rv):low.oddQuotient(tape,band,rv));\n        steps.push(rv=>bias(!rv),rv=>norm(!rv),";
  const b="        const norm=rv=>work.normalize(tape,rv),bias=rv=>this.inc(tape,rank,[],rv);\n        const E648=this.t648(tape,rank,work.n,"+P+","+M+",witness,work),LB=E648?E648.view(low):low;\n        const steps=[dirs,pack,moved,setOne,choose];if(E648)steps.push(...E648.pre);else steps.push(norm,bias);\n        for(const band of low.layouts())steps.push(rv=>witness?LB.oddWitness(tape,band,rv):LB.oddQuotient(tape,band,rv));\n        if(E648)steps.push(...E648.post);else steps.push(rv=>bias(!rv),rv=>norm(!rv));steps.push(";
  const i=s.indexOf(key),j=s.indexOf(a,i);if(j<0||j-i>2000)throw Error('t648 deep anchor');s=s.slice(0,j)+b+s.slice(j+a.length);}
 // normalization hooks (only active on the side objects that carry __hk)
 one("        const seq=[()=>H.toggle(tape,[this.take],n.slice(-s),t),rr=>H.permute(tape,n,origins,[this.take,t],rr)];\n        stepList(seq,rv,fn=>fn(rv));",
     "        const hk=this.__hk,seq=[...(hk?[rr=>hk(tape,'pre',j,t,rr)]:[]),()=>H.toggle(tape,[this.take],n.slice(-s),t),rr=>H.permute(tape,n,origins,[this.take,t],rr),...(hk?[rr=>hk(tape,'post',j,t,rr)]:[])];\n        stepList(seq,rv,fn=>fn(rv));");
 one("        const seq=[()=>H.toggle(tape,[this.take],n.slice(-d),t),rr=>H.permute(tape,n,orig,[this.take,t],rr)];\n        stepList(seq,rv,fn=>fn(rv));",
     "        const hk=this.__hk,seq=[...(hk?[rr=>hk(tape,'pre',j,t,rr)]:[]),()=>H.toggle(tape,[this.take],n.slice(-d),t),rr=>H.permute(tape,n,orig,[this.take,t],rr),...(hk?[rr=>hk(tape,'post',j,t,rr)]:[])];\n        stepList(seq,rv,fn=>fn(rv));");
 one("rv=>this.permute(tape,low,low.slice(-1).concat(low.slice(0,-1)),[this.take,q],rv),",
     "rv=>this.permute(tape,low,low.slice(-1).concat(low.slice(0,-1)),[this.take,q],rv),...(this.__hk?[rv=>this.__hk(tape,'rest',0,q,rv)]:[]),");
 return s;
};
