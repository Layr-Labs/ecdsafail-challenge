//! The same buffered pass chain is used by the compact filter and the competition entry.
use super::{ladder::{self, Row}, post};

pub struct Passes {
    pub clean: ladder::clean::Clean,
    pub rotate: ladder::rotate::Rotation,
    pub group: ladder::group::Group,
    pub post: post::Post,
    pub output: u64,
}

impl Passes {
    pub fn new(width: usize, size: usize) -> Self {
        Self {
            clean: ladder::clean::Clean::new(width,size),
            rotate: ladder::rotate::Rotation::new(width,size),
            group: ladder::group::Group::new(width,size),
            post: post::Post::new(), output: 0,
        }
    }

    pub fn push(&mut self, r: Row, emit: &mut impl FnMut(Row)) {
        let Self {clean,rotate,group,post,output}=self;
        clean.push(r, &mut |r| rotate.push(r, &mut |r| group.push(r, &mut |r|
            post.push(r, &mut |r| { *output+=1; emit(r); }))));
    }

    pub fn finish(&mut self, emit: &mut impl FnMut(Row)) {
        let Self {clean,rotate,group,post,output}=self;
        let mut send=|r| { *output+=1; emit(r); };
        let mut after_group=|r| post.push(r,&mut send);
        let mut after_rotate=|r| group.push(r,&mut after_group);
        clean.finish(&mut |r|rotate.push(r,&mut after_rotate));
        rotate.finish(&mut after_rotate);
        group.finish(&mut after_group);
        post.finish(&mut send);
    }
}
