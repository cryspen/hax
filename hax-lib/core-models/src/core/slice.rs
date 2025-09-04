use super::primitives::array::*;

mod iter {
    #[hax_lib::replace("
unfold let t_Chunks a = t_Slice (t_Slice a)
unfold let t_ChunksExact a = t_Slice (t_Slice a)
unfold let t_Iter a = t_Slice a
    ")]
    struct Chunks<T>(Seq<Slice<T>>);
}

#[hax_lib::attributes]
impl<T: Clone> Slice<T> {
    fn len(&self) -> usize {
        super::primitives::array::slice_length(self)
    }
    #[hax_lib::opaque]
    fn chunks(&self, cs: usize) -> iter::Chunks {
        todo!()
    }
    #[hax_lib::opaque]
    fn chunks_exact(&self, cs: usize) -> iter::Chunks {
        todo!()
    }
    #[hax_lib::requires(self.len() == src.len())]
    fn copy_from_slice(&mut self, src: Slice<T>) {
        *self = src
    }
    #[hax_lib::requires(self.len() == src.len())]
    fn clone_from_slice(&mut self, src: Slice<T>) {
        *self = src
    }
    #[hax_lib::requires(_mid <= self.len())]
    #[hax_lib::opaque]
    fn split_at(&self, _mid: usize) -> (&[T], &[T]) {
        todo!()
    }
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    #[hax_lib::opaque]
    fn contains(&self, _v: T) -> bool {
        todo!()
    }
    #[hax_lib::opaque]
    fn copy_within<R>(&self, src: R, dest: usize) -> Slice<T> where T: Copy {
        todo!()
    }
    #[hax_lib::opaque]
    fn binary_search(&self, _x: &T) -> Result<usize, usize> /* where T: super::ops::Ord */ {
        todo!()
    }
}

