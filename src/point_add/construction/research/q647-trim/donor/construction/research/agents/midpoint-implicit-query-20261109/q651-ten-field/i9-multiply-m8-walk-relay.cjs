'use strict';
module.exports=function(pub,bits=7){const Base=pub.D2Canonical;return class Relay extends Base {
 constructor(n){super(n,bits);require('./i9-multiply-walk-small.cjs').install(this,pub.dirtyDigit,{rot:false,pair:true,select:true});require('./i9-multiply-multi-relay.cjs').install(this,pub.dirtyDigit);}
};};
