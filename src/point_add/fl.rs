//! q631 / fl (agent fl, 2026-11-19; local research, NOT part of any package; nothing in the builder calls it): the last records with no
//! free lane on the 632-lane list.  Each fix is its own submodule behind its own switch, all OFF:
//!   flwalk: the forward hybrid walk rows (segments 2 and 18).
//!   fli4:   ITEM 4 (segment 8): lane 2 free from the run-1 head through the alpha tail (encoding E2, replaces R1).
//!   fli12:  ITEM 12 (segment 25): lane 513 free from i12's R1 point through alpha row 127 (E2 transferred, replaces i12's R1).
//!   flseam: the transcoder E2 form -> i4b's E_A form used by fli4 and fli12 at the ipark Gtop window start.
//! Report: ~/Projects/ecdsafail/q631/fl/summary.py.
#[path = "flwalk.rs"]
#[allow(dead_code)]
pub mod flwalk;
#[path = "fli4.rs"]
#[allow(dead_code)]
pub mod fli4;
#[path = "fli12.rs"]
#[allow(dead_code)]
pub mod fli12;
#[path = "flseam.rs"]
#[allow(dead_code)]
pub mod flseam;
