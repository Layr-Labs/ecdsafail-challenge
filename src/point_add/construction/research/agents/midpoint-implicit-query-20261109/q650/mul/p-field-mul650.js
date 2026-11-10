'use strict';
// q650 short.multiply: the 651 field list with p-mul650.js appended (multiply no longer uses logical 650).
// p-mul650.js anchors on text produced by q651/mul/p-mul651.js and needs D2Canonical from q651/p-divide-d4.js,
// so it must come after the complete 651 list. Divide and stage-map entries are untouched.
module.exports=[...require('../../q651/p-field651.js'),...require('./p-mul650.js')];
