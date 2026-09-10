//! First twenty scheduled templates; reserve tranche 2, prefix 20.
pub(crate) const ACTIVE_TEMPLATES:usize=20;
pub(super) fn selected(block:usize,entry_j:usize)->bool{selected_prefix(block,entry_j,ACTIVE_TEMPLATES)}
fn selected_prefix(block:usize,entry_j:usize,prefix:usize)->bool{
 assert!(block<26&&entry_j<4&&prefix<=104);
 block*4+(entry_j+1)%4<prefix
}
