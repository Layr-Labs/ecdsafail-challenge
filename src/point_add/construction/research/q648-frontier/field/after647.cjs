'use strict';
const path=require('node:path');
const root=process.env.Q647_POINT_ADD||path.resolve(__dirname,'../../q647-trim/donor');
require('./buckets.cjs').install(root,647);
