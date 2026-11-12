'use strict';
// D21 exact tail simplification after D20's shared-enable tail.
// Direct threshold D17GTOracle is now a function of M only, and does not
// address t. Count3 toggles t, leaves M unchanged, and restores dirty C.
// Thus each A B A^-1 conjugation is just B, for both threshold directions.
module.exports=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('D21 echo anchor '+a);s=s.replace(a,b);};
 one('put(c3oracle);put(q);put(rev(c3oracle));','put(q);');
 one('put(c3oracle);put(rev(q));put(rev(c3oracle));','put(rev(q));');
 return s;
};
