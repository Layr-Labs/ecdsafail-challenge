'use strict';
// Apply AFTER n651a q651-ten-field/upper.cjs upper(raw).
// The caller must supply nine clean sites. Does not change other stages or global width.
module.exports=[
 ['if(ids[i]===undefined&&i!==654)ids[i]=clean[j++];',
  'if(ids[i]===undefined&&i!==654&&i!==650)ids[i]=clean[j++];'],
 ['if(j!==10||clean.length!==10)throw Error("Q651 history geometry");',
  'if(j!==9||clean.length!==9)throw Error("Q650 history geometry");'],
];
