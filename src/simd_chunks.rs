use std::arch::x86_64 as arch;

#[allow(non_camel_case_types)]
pub type v128 = arch::__m128i;

#[allow(non_camel_case_types)]
pub type v256 = arch::__m256i;

pub trait SimdChunk {
    fn load_unaligned(ptr: *const u8) -> Self;
    fn store_unaligned(self, buf: &mut [u8]);

    fn blend(self, other: Self, start_at: u32) -> Self;
    fn blend_left_u8(self, filler: u8, remaining_len: u32) -> Self;

    fn swap_bytes(self) -> Self;

    // Rotate elements so that "offset" is the first element
    fn rotate(self, offset: u32) -> Self;
}

impl SimdChunk for v128 {
    #[inline(always)]
    fn load_unaligned(ptr: *const u8) -> Self {
        unsafe { arch::_mm_loadu_si128(ptr.cast()) }
    }

    #[inline(always)]
    fn store_unaligned(self, buf: &mut [u8]) {
        if buf.len() < 16 {
            panic!("buffer is too small");
        }

        unsafe {
            arch::_mm_storeu_si128(buf.as_mut_ptr().cast(), self);
        }
    }

    fn swap_bytes(self) -> Self {
        unsafe {
            let indexes = arch::_mm_setr_epi8(
                15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
            );

            arch::_mm_shuffle_epi8(self, indexes)
        }
    }

    #[inline(always)]
    fn blend(self, other: Self, start_at: u32) -> Self {
        unsafe {
            let indexes = arch::_mm_setr_epi8(
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            );
            let offset = arch::_mm_set1_epi8((15 - start_at) as i8);
            let mask = arch::_mm_cmpgt_epi8(indexes, offset);
            arch::_mm_blendv_epi8(self, other, mask)
        }
    }

    #[inline(always)]
    fn blend_left_u8(self, filler: u8, remaining_len: u32) -> Self {
        let filler = unsafe { arch::_mm_set1_epi8(filler as i8) };
        filler.blend(self, remaining_len)
    }

    #[inline(always)]
    fn rotate(self, offset: u32) -> Self {
        unsafe {
            let indexes = arch::_mm_setr_epi8(
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            );
            let offset = arch::_mm_set1_epi8(offset as i8);
            let lookup = arch::_mm_add_epi8(indexes, offset);

            arch::_mm_shuffle_epi8(self, lookup)
        }
    }
}

impl SimdChunk for v256 {
    #[inline(always)]
    fn load_unaligned(ptr: *const u8) -> Self {
        unsafe { arch::_mm256_loadu_si256(ptr.cast()) }
    }

    #[inline(always)]
    fn store_unaligned(self, buf: &mut [u8]) {
        if buf.len() < 32 {
            panic!("buffer is too small");
        }

        unsafe {
            arch::_mm256_storeu_si256(buf.as_mut_ptr().cast(), self);
        }
    }

    #[inline(always)]
    fn swap_bytes(self) -> Self {
        unsafe {
            let indexes = arch::_mm256_setr_epi8(
                31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
                15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
            );

            let swapped = arch::_mm256_permute2x128_si256(self, self, 0x01);
            arch::_mm256_shuffle_epi8(swapped, indexes)
        }
    }

    #[inline(always)]
    fn blend(self, other: Self, start_at: u32) -> Self {
        unsafe {
            let indexes = arch::_mm256_setr_epi8(
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
                18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
            );
            let offset = arch::_mm256_set1_epi8((31 - start_at) as i8);
            let mask = arch::_mm256_cmpgt_epi8(indexes, offset);
            arch::_mm256_blendv_epi8(self, other, mask)
        }
    }

    #[inline(always)]
    fn blend_left_u8(self, filler: u8, remaining_len: u32) -> Self {
        let filler = unsafe { arch::_mm256_set1_epi8(filler as i8) };
        filler.blend(self, remaining_len)
    }

    #[inline(always)]
    fn rotate(self, offset: u32) -> Self {
        // rotate within each lane
        // swap lanes of the rotated vec into a temp vec
        // blend temp vec with rotated vec

        unsafe {
            // Imagine each lane only has 4 bytes (for simplicity).
            // So entire vector is 8 bytes:
            //
            // [0, 1, 2, 3] | [4, 5, 6, 7]
            //
            // rotated by offset 2 within lanes:
            //
            // [2, 3, 0, 1] | [6, 7, 4, 5]
            //
            // swapped laned:
            //
            // [6, 7, 4, 5] | [2, 3, 0, 1]
            //
            // blend mask:
            //
            // [0xff, 0xff, 0, 0] | [0xff, 0xff, 0, 0]
            //
            // result = (rotated & blend) | (swapped & !blend)

            let indexes = arch::_mm256_setr_epi8(
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2,
                3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            );

            let lookup_offset = arch::_mm256_set1_epi8(offset as i8);
            let lookup = arch::_mm256_add_epi8(indexes, lookup_offset);

            // pshufb is fetching indexes with a "mod 16" semantics.
            let rotated = arch::_mm256_shuffle_epi8(self, lookup);
            let swapped =
                arch::_mm256_permute2x128_si256(rotated, rotated, 0x01);

            // set 7-th bit where lookup index is >= 16
            let mask = arch::_mm256_slli_epi32(lookup, 3);

            arch::_mm256_blendv_epi8(rotated, swapped, mask)
        }
    }
}

fn crosses_page_boundary<T>(ptr: *const T, alignment: usize) -> bool {
    let addr: usize = unsafe { std::mem::transmute(ptr) };
    let addr = addr as u32;

    // One false positive at 4096 - alignment
    (!addr & (4096 - alignment as u32)) == 0
}

pub struct SimdChunks<'a, T: SimdChunk> {
    ptr: *const T,
    len: usize,

    marker: std::marker::PhantomData<&'a u8>,
}

impl<'a, T: SimdChunk> SimdChunks<'a, T> {
    fn from(buf: &'a [u8]) -> Self {
        Self {
            ptr: buf.as_ptr().cast(),
            len: buf.len(),
            marker: Default::default(),
        }
    }

    pub fn remainder_len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn remainder(&self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        let (ptr, offset) = self.remainder_ptr_unaligned::<T>();
        let rem = T::load_unaligned(ptr);

        if offset == 0 {
            return Some(rem);
        }

        Some(rem.rotate(offset as u32))
    }

    pub fn remainder_as<U>(&self) -> Option<<U as std::ops::Shr<u32>>::Output>
    where
        U: Sized + std::ops::Shr<u32>,
    {
        if self.len == 0 {
            return None;
        }

        let (ptr, offset) = self.remainder_ptr_unaligned::<U>();

        let value = unsafe { ptr.cast::<U>().read_unaligned() };
        Some(value >> (offset as u32 * 8))
    }

    fn remainder_ptr_unaligned<U>(&self) -> (*const u8, usize) {
        let alignment = std::mem::size_of::<U>();

        if !crosses_page_boundary(self.ptr, alignment) {
            return (self.ptr.cast(), 0);
        }

        let offset = alignment - self.len;

        let byte_ptr = self.ptr.cast::<u8>();
        let aligned_right = unsafe { byte_ptr.sub(offset).cast() };

        (aligned_right, offset)
    }
}

impl<'a, T: SimdChunk> Iterator for SimdChunks<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let size = std::mem::size_of::<T>();
        if self.len >= size {
            let item = T::load_unaligned(self.ptr.cast());
            self.ptr = unsafe { self.ptr.add(1) };
            self.len -= size;

            Some(item)
        } else {
            None
        }
    }
}

impl<'a, T: SimdChunk> ExactSizeIterator for SimdChunks<'a, T> {
    fn len(&self) -> usize {
        self.len / std::mem::size_of::<T>()
    }
}

pub struct SimdRChunks<'a, T: SimdChunk> {
    ptr: *const T,
    len: usize,

    marker: std::marker::PhantomData<&'a u8>,
}

impl<'a, T: SimdChunk> SimdRChunks<'a, T> {
    fn from(buf: &'a [u8]) -> Self {
        Self {
            ptr: unsafe {
                buf.as_ptr().add(buf.len()).sub(std::mem::size_of::<T>())
            }
            .cast(),
            len: buf.len(),
            marker: Default::default(),
        }
    }

    pub fn remainder_len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn remainder(&self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        let (ptr, trailing) = self.remainder_ptr_unaligned::<T>();
        let rem = T::load_unaligned(ptr);

        if trailing == 0 {
            return Some(rem);
        }

        Some(rem.rotate((std::mem::size_of::<T>() - trailing) as u32))
    }

    pub fn remainder_as<U>(&self) -> Option<<U as std::ops::Shl<u32>>::Output>
    where
        U: Sized + std::ops::Shl<u32>,
    {
        if self.len == 0 {
            return None;
        }

        let (ptr, offset) = self.remainder_ptr_unaligned::<U>();

        let value = unsafe { ptr.cast::<U>().read_unaligned() };
        Some(value << (offset as u32 * 8))
    }

    fn remainder_ptr_unaligned<U>(&self) -> (*const u8, usize) {
        let alignment = std::mem::size_of::<U>();
        debug_assert!(self.len <= alignment);

        let ptr = unsafe {
            self.ptr
                .cast::<u8>()
                .add(std::mem::size_of::<T>() - alignment)
        };

        if !crosses_page_boundary(ptr, alignment) {
            return (ptr.cast(), 0);
        }

        let trailing = alignment - self.len;
        let aligned_left = unsafe { ptr.add(trailing).cast() };

        (aligned_left, trailing)
    }
}

impl<'a, T: SimdChunk> Iterator for SimdRChunks<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let size = std::mem::size_of::<T>();

        if self.len >= size {
            let item = T::load_unaligned(self.ptr.cast());
            self.ptr = unsafe { self.ptr.sub(1) };
            self.len -= size;

            Some(item)
        } else {
            None
        }
    }
}

impl<'a> ExactSizeIterator for SimdRChunks<'a, v128> {
    fn len(&self) -> usize {
        self.len / 16
    }
}

pub trait SimdChunksExt {
    fn simd_chunks<T: SimdChunk>(&self) -> SimdChunks<T>;
    fn simd_rchunks<T: SimdChunk>(&self) -> SimdRChunks<T>;
}

impl SimdChunksExt for [u8] {
    fn simd_chunks<T: SimdChunk>(&self) -> SimdChunks<T> {
        SimdChunks::from(&self)
    }

    fn simd_rchunks<T: SimdChunk>(&self) -> SimdRChunks<T> {
        SimdRChunks::from(&self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::Layout;

    #[test]
    fn v128_blend() {
        let data = (0_u8..16).collect::<Vec<u8>>();
        let mut bytes = [0; 16];

        let v = v128::load_unaligned(data.as_ptr());
        let r = v.blend_left_u8(20, 3);
        r.store_unaligned(&mut bytes);

        assert_eq!(
            bytes,
            [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 13, 14, 15]
        );
    }

    #[test]
    fn v128_rotate() {
        let data = (0_u8..16).collect::<Vec<u8>>();
        let mut bytes = [0; 16];

        let v = v128::load_unaligned(data.as_ptr());
        let r = v.rotate(5);
        r.store_unaligned(&mut bytes);

        assert_eq!(
            bytes,
            [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4]
        );

        println!("r = {:?}", bytes);
    }

    #[test]
    fn v256_blend() {
        let data = (0_u8..32).collect::<Vec<u8>>();
        let mut bytes = [0; 32];

        let v = v256::load_unaligned(data.as_ptr());
        let r = v.blend_left_u8(50, 3);
        r.store_unaligned(&mut bytes);

        let lane0 = &bytes[0..16];
        let lane1 = &bytes[16..32];

        assert_eq!(
            lane0,
            [50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50]
        );
        assert_eq!(
            lane1,
            [50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 29, 30, 31]
        );
    }

    #[test]
    fn v256_rotate_less_than_16() {
        let data = (0_u8..32).collect::<Vec<u8>>();
        let mut bytes = [0; 32];

        let v = v256::load_unaligned(data.as_ptr());
        let r = v.rotate(5);
        r.store_unaligned(&mut bytes);

        let lane0 = &bytes[0..16];
        let lane1 = &bytes[16..32];

        assert_eq!(
            lane0,
            [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
        );
        assert_eq!(
            lane1,
            [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4]
        );
    }

    #[test]
    fn v256_rotate_more_than_16() {
        let data = (0_u8..32).collect::<Vec<u8>>();
        let mut bytes = [0; 32];

        let v = v256::load_unaligned(data.as_ptr());
        let r = v.rotate(25);
        r.store_unaligned(&mut bytes);

        let lane0 = &bytes[0..16];
        let lane1 = &bytes[16..32];

        assert_eq!(
            lane0,
            [25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8]
        );
        assert_eq!(
            lane1,
            [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
        );
    }

    #[test]
    fn iterates_unaligned_data() {
        let layout = Layout::from_size_align(256, 16).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) };
        for i in 0..256 {
            unsafe { *ptr.add(i) = 0xff };
        }

        for offset in 0..15 {
            let ptr = unsafe { ptr.add(offset) };
            let bytes = unsafe { std::slice::from_raw_parts_mut(ptr, 20) };
            for i in 0..bytes.len() {
                bytes[i] = i as u8;
            }

            let mut chunks = bytes.simd_chunks();
            let chunk = chunks.next().unwrap();

            let mut bytes = [0_u8; 16];
            unsafe {
                arch::_mm_storeu_si128(bytes.as_mut_ptr().cast(), chunk);
            }
            assert_eq!(
                bytes,
                [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
            );

            let mut remainder = [0_u8; 16];
            unsafe {
                arch::_mm_storeu_si128(
                    remainder.as_mut_ptr().cast(),
                    chunks.remainder().unwrap(),
                );
            }
            assert_eq!(remainder[..4], [16, 17, 18, 19]);

            let r = chunks.remainder_as::<u64>().unwrap();
            assert_eq!(r as u32, u32::from_le_bytes([16, 17, 18, 19]));

            /*
            println!(
                "alignment_offset={}, chunk={:?}, remainder_len={:?}, remainder={:?}",
                alignment_offset,
                bytes,
                chunks.remainder_len(),
                &remainder[..chunks.remainder_len()]
            );*/
        }

        unsafe { std::alloc::dealloc(ptr, layout) };
    }

    #[test]
    fn iterates_unaligned_data_rev() {
        let layout = Layout::from_size_align(256, 16).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) };
        for i in 0..256 {
            unsafe { *ptr.add(i) = 0xff };
        }

        for offset in 0..15 {
            let ptr = unsafe { ptr.add(128 + offset) };
            let bytes = unsafe { std::slice::from_raw_parts_mut(ptr, 20) };
            for i in 0..bytes.len() {
                bytes[i] = i as u8;
            }

            let mut chunks = bytes.simd_rchunks();
            let chunk = chunks.next().unwrap();

            let mut bytes = [0_u8; 16];
            unsafe {
                arch::_mm_storeu_si128(bytes.as_mut_ptr().cast(), chunk);
            }
            assert_eq!(
                bytes,
                [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
            );

            let mut remainder = [0_u8; 16];
            unsafe {
                arch::_mm_storeu_si128(
                    remainder.as_mut_ptr().cast(),
                    chunks.remainder().unwrap(),
                );
            }
            assert_eq!(remainder[16 - 4..], [0, 1, 2, 3]);

            let r = chunks.remainder_as::<u64>().unwrap();
            assert_eq!((r >> 32) as u32, u32::from_le_bytes([0, 1, 2, 3]));

            /*
            println!(
                "alignment_offset={}, chunk={:?}, remainder_len={:?}, remainder={:?}",
                alignment_offset,
                bytes,
                chunks.remainder_len(),
                &remainder[16 - chunks.remainder_len()..]
            );*/
        }

        unsafe { std::alloc::dealloc(ptr, layout) };
    }
}
