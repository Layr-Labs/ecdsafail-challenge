//! First 30 scheduled templates; reserve tranche 3, prefix 30.
//!
//! The Q793 lifecycle retains the original 104-template space: 26 blocks of
//! 64 scheduled steps. Keep selection in that exact block/entry-clock basis.
//! Selection remains compile-time; it never depends on quantum data, a measurement or the nonce.
pub(crate) const RESERVE_BLOCK:usize=64;
pub(crate) const RESERVE_BLOCKS:usize=1616usize.div_ceil(RESERVE_BLOCK);
pub(crate) const RESERVE_TEMPLATES:usize=4*RESERVE_BLOCKS;
pub(crate) const ACTIVE_TEMPLATES:usize=104;
pub(super) fn selected(block:usize,entry_j:usize)->bool{selected_prefix(block,entry_j,ACTIVE_TEMPLATES)}
fn selected_prefix(block:usize,entry_j:usize,prefix:usize)->bool{
 let bs=crate::point_add::trailmix_port::inversion::shared_step::SCHEDULE_BLOCK;
 assert!(block<crate::point_add::trailmix_port::inversion::shared_step::SCHEDULE_BLOCKS&&entry_j<4&&prefix<=RESERVE_TEMPLATES);
 assert!(RESERVE_BLOCK%bs==0,"window blocks must subdivide the reserve block");
 let reserve_block=(block*bs)/RESERVE_BLOCK;
 reserve_block*4+(entry_j+1)%4<prefix
}
