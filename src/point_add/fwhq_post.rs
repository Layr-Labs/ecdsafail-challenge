use crate::circuit::Op;
// fwhq post stage (min-Toffoli points): one table of AND-cache holds and erase holds, generated on this build's own
// pre-tail gate list by the fwlead sigscan `svn` tool (each hold verified on 2,097,152 sampled shots, then placed on a
// verified idle-zero wire gap below the walk cap; no wire above the cap is used). The table refuses to run unless its
// input is the exact gate list it was generated on (length + SHA3-256), and every edit checks the op it replaces.
pub(super) fn run(v: Vec<Op>) -> Vec<Op> {
    super::source_edits::run(v, include_str!("fwhq_holds.txt"))
}
