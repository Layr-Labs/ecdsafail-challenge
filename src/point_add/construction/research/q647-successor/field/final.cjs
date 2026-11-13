'use strict';
require('./preload.cjs');
require('./sectors.cjs').install();
require('./hosted.cjs').install();
require('./clean.cjs').install();
require('./rotation.cjs').install();
